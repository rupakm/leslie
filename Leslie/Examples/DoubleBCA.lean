import Leslie.Compose
import Leslie.Examples.BindingCrusaderAgreement

/-! # Double BCA — Proof-of-Concept for Protocol Composition

    A protocol that runs BCA twice in sequence:
    1. Round 1: processes use their original input of type `T`
    2. Round 2: processes use round 1's decision as input (type `Val T = Option T`)

    **Data dependency**: when a process decides `mv : Val T` in round 1,
    round 2's `input` field is set to `some mv`. This includes both
    binary decisions (`some (some b)`) and ⊥ decisions (`some none`).

    **Shared corruption**: a single `corrupted` list across both rounds.

    Both rounds are standard BCA instances. Round 1 is `bca T n f` and
    round 2 is `bca (Val T) n f` (operating over `Option T` values).
    We construct a `ProtocolCall` for each round and lift agreement and
    validity via `lift_invariant`. -/

open TLA
open BindingCrusaderAgreement

namespace DoubleBCA

variable (T : Type) [DecidableEq T] (n f : Nat)

/-! ## State -/

/-- Round 1 BCA fields (value type `T`). -/
structure R1State (n : Nat) where
  local_ : Fin n → LocalState T n
  buffer : Message T n → Bool
  boundValue : Option (Val T)

/-- Round 2 BCA fields (value type `Val T = Option T`). -/
structure R2State (n : Nat) where
  local_ : Fin n → LocalState (Val T) n
  buffer : Message (Val T) n → Bool
  boundValue : Option (Val (Val T))

/-- Reconstruct a full BCA state from round 1 fields + shared corruption. -/
def toR1State (rs : R1State T n) (corrupted : List (Fin n)) :
    BindingCrusaderAgreement.State T n where
  local_ := rs.local_
  buffer := rs.buffer
  corrupted := corrupted
  boundValue := rs.boundValue

/-- Reconstruct a full BCA state from round 2 fields + shared corruption. -/
def toR2State (rs : R2State T n) (corrupted : List (Fin n)) :
    BindingCrusaderAgreement.State (Val T) n where
  local_ := rs.local_
  buffer := rs.buffer
  corrupted := corrupted
  boundValue := rs.boundValue

/-- Composed state: shared corruption + two rounds. -/
structure State where
  corrupted : List (Fin n)
  r1 : R1State T n
  r2 : R2State T n

def proj_r1 (s : State T n) : BindingCrusaderAgreement.State T n :=
  toR1State T n s.r1 s.corrupted

def proj_r2 (s : State T n) : BindingCrusaderAgreement.State (Val T) n :=
  toR2State T n s.r2 s.corrupted

/-! ## Actions -/

inductive Action where
  | corrupt (i : Fin n)
  | r1 (a : BindingCrusaderAgreement.Action T n)
  | r2 (a : BindingCrusaderAgreement.Action (Val T) n)

/-! ## Specification -/

def spec : ActionSpec (State T n) (Action T n) where
  init := fun s =>
    (bca T n f).init (proj_r1 T n s) ∧
    (bca (Val T) n f).init (proj_r2 T n s)
  actions := fun
    --
    -- Shared corruption: applied to both rounds
    --
    | .corrupt i => {
        gate := fun s =>
          isCorrect T n (proj_r1 T n s) i ∧
          s.corrupted.length + 1 ≤ f
        transition := fun s s' =>
          ((bca T n f).actions (.corrupt i)).transition
            (proj_r1 T n s) (proj_r1 T n s') ∧
          ((bca (Val T) n f).actions (.corrupt i)).transition
            (proj_r2 T n s) (proj_r2 T n s')
      }
    --
    -- Round 1: forwarded to standard BCA.
    -- For decide actions, the decision feeds into round 2's input.
    --
    | .r1 a => {
        gate := fun s => match a with
          | .corrupt _ => False
          | .decide i _ =>
            ((bca T n f).actions a).gate (proj_r1 T n s) ∧
            (s.r2.local_ i).input = none
          | _ => ((bca T n f).actions a).gate (proj_r1 T n s)
        transition := fun s s' => match a with
          | .corrupt _ => False
          | .decide i mv =>
            ((bca T n f).actions a).transition
              (proj_r1 T n s) (proj_r1 T n s') ∧
            -- DATA DEPENDENCY: feed decision mv into round 2's input
            s'.r2 = { s.r2 with
              local_ := fun p => if p = i
                then { s.r2.local_ i with input := some mv }
                else s.r2.local_ p } ∧
            s'.corrupted = s.corrupted
          | _ =>
            ((bca T n f).actions a).transition
              (proj_r1 T n s) (proj_r1 T n s') ∧
            s'.r2 = s.r2 ∧ s'.corrupted = s.corrupted
      }
    --
    -- Round 2: standard BCA over Val T (init gate reads `input`, set by round 1)
    --
    | .r2 a => {
        gate := fun s => match a with
          | .corrupt _ => False
          | .set_input _ _ => False  -- r2 inputs come from the r1→r2 feed only
          | _ => ((bca (Val T) n f).actions a).gate (proj_r2 T n s)
        transition := fun s s' => match a with
          | .corrupt _ => False
          | .set_input _ _ => False
          | _ =>
            ((bca (Val T) n f).actions a).transition
              (proj_r2 T n s) (proj_r2 T n s') ∧
            s'.r1 = s.r1 ∧ s'.corrupted = s.corrupted
      }

/-! ## Protocol Call: Round 1 -/

def call_r1 :
    ProtocolCall (State T n) (BindingCrusaderAgreement.State T n)
      (Action T n) (BindingCrusaderAgreement.Action T n) where
  composed := spec T n f
  sub := bca T n f
  proj := proj_r1 T n
  init_proj := fun _ hinit => hinit.1
  step_proj := fun s s' ⟨i, hgate, htrans⟩ => by
    cases i with
    | corrupt i =>
      left ; refine ⟨.corrupt i, ?_, ?_⟩
      · exact ⟨by simp [proj_r1, toR1State] ; exact hgate.1,
               by simp [proj_r1, toR1State] ; exact hgate.2⟩
      · exact htrans.1
    | r1 a =>
      cases a with
      | corrupt _ => exact absurd hgate False.elim
      | set_input i v => left ; exact ⟨.set_input i v, hgate, htrans.1⟩
      | decide i mv =>
        left ; exact ⟨.decide i mv, hgate.1, htrans.1⟩
      | send src dst t v => left ; exact ⟨.send src dst t v, hgate, htrans.1⟩
      | recv src dst t v => left ; exact ⟨.recv src dst t v, hgate, htrans.1⟩
    | r2 a =>
      cases a with
      | corrupt _ => exact absurd hgate False.elim
      | set_input _ _ => exact absurd hgate False.elim
      | _ =>
        right ; show proj_r1 T n s = proj_r1 T n s'
        simp only [proj_r1, toR1State]
        rw [htrans.2.1.symm, htrans.2.2.symm]

/-! ## Protocol Call: Round 2

    Round 2 is `bca (Val T) n f`. The `.r1 (.decide i mv)` step
    feeds round 1's decision into round 2's `input` field — this maps
    to BCA's `set_input i mv` action on `proj_r2`. -/

def call_r2 :
    ProtocolCall (State T n) (BindingCrusaderAgreement.State (Val T) n)
      (Action T n) (BindingCrusaderAgreement.Action (Val T) n) where
  composed := spec T n f
  sub := bca (Val T) n f
  proj := proj_r2 T n
  init_proj := fun _ hinit => hinit.2
  step_proj := fun s s' ⟨i, hgate, htrans⟩ => by
    cases i with
    | corrupt i =>
      left ; refine ⟨.corrupt i, ?_, ?_⟩
      · exact ⟨by simp [proj_r2, toR2State] ; exact hgate.1,
               by simp [proj_r2, toR2State] ; exact hgate.2⟩
      · exact htrans.2
    | r1 a =>
      cases a with
      | corrupt _ => exact absurd hgate False.elim
      | set_input i v =>
        right ; show proj_r2 T n s = proj_r2 T n s'
        simp only [proj_r2, toR2State]
        rw [htrans.2.1.symm, htrans.2.2.symm]
      | decide i mv =>
        -- Maps to BCA's set_input i mv on proj_r2
        left
        obtain ⟨_, hr2eq, hcorr⟩ := htrans
        exact ⟨.set_input i mv, hgate.2, by
          show proj_r2 T n s' = { proj_r2 T n s with
            local_ := fun p => if p = i
              then { (proj_r2 T n s).local_ i with input := some mv }
              else (proj_r2 T n s).local_ p }
          simp only [proj_r2, toR2State, hcorr, hr2eq]⟩
      | send src dst t v =>
        right ; show proj_r2 T n s = proj_r2 T n s'
        simp only [proj_r2, toR2State]
        rw [htrans.2.1.symm, htrans.2.2.symm]
      | recv src dst t v =>
        right ; show proj_r2 T n s = proj_r2 T n s'
        simp only [proj_r2, toR2State]
        rw [htrans.2.1.symm, htrans.2.2.symm]
    | r2 a =>
      cases a with
      | corrupt _ => exact absurd hgate False.elim
      | set_input _ _ => exact absurd hgate False.elim
      | send src dst t v => left ; exact ⟨.send src dst t v, hgate, htrans.1⟩
      | recv src dst t v => left ; exact ⟨.recv src dst t v, hgate, htrans.1⟩
      | decide i v => left ; exact ⟨.decide i v, hgate, htrans.1⟩

/-! ## Lifted Properties -/

/-- **Round 1 agreement**. -/
theorem r1_agreement (hn : n > 3 * f) :
    pred_implies (spec T n f).safety
      [tlafml| □ ⌜ fun s => agreement T n (proj_r1 T n s) ⌝] :=
  (call_r1 T n f).lift_invariant (bca_agreement_stutter T n f hn)

/-- **Round 1 validity**. -/
theorem r1_validity (hn : n > 3 * f) (v : T) :
    pred_implies (spec T n f).safety
      [tlafml| □ ⌜ fun s => validity T n v (proj_r1 T n s) ⌝] :=
  (call_r1 T n f).lift_invariant (bca_validity_stutter T n f hn v)

/-- **Round 2 agreement**. -/
theorem r2_agreement (hn : n > 3 * f) :
    pred_implies (spec T n f).safety
      [tlafml| □ ⌜ fun s => agreement (Val T) n (proj_r2 T n s) ⌝] :=
  (call_r2 T n f).lift_invariant (bca_agreement_stutter (Val T) n f hn)

/-- **Round 2 validity**. -/
theorem r2_validity (hn : n > 3 * f) (v : Val T) :
    pred_implies (spec T n f).safety
      [tlafml| □ ⌜ fun s => validity (Val T) n v (proj_r2 T n s) ⌝] :=
  (call_r2 T n f).lift_invariant (bca_validity_stutter (Val T) n f hn v)

def feed_inv (s : State T n) : Prop :=
  ∀ p mv, (s.r2.local_ p).input = some mv → (s.r1.local_ p).decided = some mv

theorem feed_inv_init :
    ∀ s, (spec T n f).init s → feed_inv T n s := by
  intro s ⟨_, hinit2⟩ p mv hinp
  simp [proj_r2, toR2State] at hinit2
  have := hinit2.1 p
  simp [BindingCrusaderAgreement.LocalState.init] at this
  simp [this] at hinp

theorem feed_inv_step :
    ∀ s s', (∃ i, ((spec T n f).actions i).fires s s') →
    feed_inv T n s → feed_inv T n s' := by
  intro s s' ⟨action, hfire⟩ ih
  simp [spec, GatedAction.fires] at hfire
  obtain ⟨hgate, htrans⟩ := hfire
  intro p mv hinp
  cases action with
  | corrupt i =>
    -- corrupted/input/decided unchanged
    obtain ⟨hr1, hr2⟩ := htrans
    simp [bca, proj_r1, toR1State, proj_r2, toR2State] at hr1 hr2
    rw [hr2.1] at hinp ; rw [hr1.1] ; exact ih p mv hinp
  | r1 a =>
    cases a with
    | corrupt _ => exact absurd hgate False.elim
    | decide i mv' =>
      obtain ⟨hr1, hr2eq, _⟩ := htrans
      rw [hr2eq] at hinp ; simp at hinp
      simp [bca, proj_r1, toR1State] at hr1
      by_cases hpi : p = i
      · subst hpi ; simp at hinp ; subst hinp
        -- hr1.1 : s'.r1.local_ = fun p => if p = p then {... decided := some mv'} else ...
        have : s'.r1.local_ p = _ := congrFun hr1.1 p
        simp at this ; rw [this]
      · simp [hpi] at hinp
        have : s'.r1.local_ p = s.r1.local_ p := by
          have := congrFun hr1.1 p ; simp [hpi] at this ; exact this
        rw [this] ; exact ih p mv hinp
    | send _ _ _ _ | set_input _ _ =>
      -- r2 unchanged, r1 transition preserves decided
      obtain ⟨hr1, hr2eq, _⟩ := htrans
      rw [hr2eq] at hinp ; have hih := ih p mv hinp
      simp [bca, proj_r1, toR1State] at hr1
      have hloc := congrFun hr1.1 p
      split at hloc
      · subst_vars ; rw [hloc] ; exact hih
      · rw [hloc] ; exact hih
    | recv src dst t v =>
      -- r2 unchanged, r1 recv preserves decided (case split on t/mv for struct)
      obtain ⟨hr1, hr2eq, _⟩ := htrans
      rw [hr2eq] at hinp ; have hih := ih p mv hinp
      simp [bca, proj_r1, toR1State] at hr1
      have hloc := congrFun hr1.1 p
      split at hloc
      · subst_vars ; rw [hloc] ; cases t with
        | init => cases v with
          | none => exact hih
          | some bv =>
            by_cases hc : (s.r1.local_ dst).initRecv src bv = false
            · simp ; rw [if_pos hc] ; exact hih
            · simp ; rw [if_neg hc] ; exact hih
        | echo => cases v with
          | none => exact hih
          | some bv =>
            by_cases hc : (s.r1.local_ dst).echoRecv src bv = false
            · simp ; rw [if_pos hc] ; exact hih
            · simp ; rw [if_neg hc] ; exact hih
        | vote =>
          by_cases hc : (s.r1.local_ dst).voteRecv src v = false
          · rw [if_pos hc] ; exact hih
          · rw [if_neg hc] ; exact hih
      · rw [hloc] ; exact hih
  | r2 a =>
    cases a with
    | corrupt _ => exact absurd hgate False.elim
    | set_input _ _ => exact absurd hgate False.elim
    | send _ _ _ _ | decide _ _ =>
      -- r1 unchanged, r2 transition preserves input
      obtain ⟨hr2, hr1eq, _⟩ := htrans
      rw [hr1eq] ; have hih := ih p mv
      simp [bca, proj_r2, toR2State] at hr2
      have hloc := congrFun hr2.1 p
      split at hloc
      · subst_vars ; rw [hloc] at hinp ; exact hih hinp
      · rw [hloc] at hinp ; exact hih hinp
    | recv src dst t v =>
      -- r1 unchanged, r2 recv preserves input (case split on t/mv for struct)
      obtain ⟨hr2, hr1eq, _⟩ := htrans
      rw [hr1eq] ; have hih := ih p mv
      simp [bca, proj_r2, toR2State] at hr2
      have hloc := congrFun hr2.1 p
      split at hloc
      · subst_vars ; rw [hloc] at hinp ; cases t with
        | init => cases v with
          | none => exact hih hinp
          | some bv =>
            simp only [] at hinp
            by_cases hc : (s.r2.local_ dst).initRecv src bv = false
            · rw [if_pos hc] at hinp ; exact hih hinp
            · rw [if_neg hc] at hinp ; exact hih hinp
        | echo => cases v with
          | none => exact hih hinp
          | some bv =>
            simp only [] at hinp
            by_cases hc : (s.r2.local_ dst).echoRecv src bv = false
            · rw [if_pos hc] at hinp ; exact hih hinp
            · rw [if_neg hc] at hinp ; exact hih hinp
        | vote =>
          by_cases hc : (s.r2.local_ dst).voteRecv src v = false
          · rw [if_pos hc] at hinp ; exact hih hinp
          · rw [if_neg hc] at hinp ; exact hih hinp
      · rw [hloc] at hinp ; exact hih hinp

/-- **Data dependency**: r2 input for process p tracks r1 decision.
    Since `.r2 (.set_input)` is blocked, r2 input is ONLY set by the
    feed from r1 decisions. -/
theorem feed_invariant :
    pred_implies (spec T n f).safety
      [tlafml| □ ⌜ fun s =>
        ∀ p mv, (s.r2.local_ p).input = some mv →
                (s.r1.local_ p).decided = some mv ⌝] := by
  apply init_invariant (feed_inv_init T n f)
    (fun s s' hn' hi => feed_inv_step T n f s s' hn' hi)

/-- **Double BCA validity**: if all processes are either corrupted, have
    no r1 input, or have r1 input `b`, then every r2 decision is either
    `none` or `some (some b)`.

    Chains: r1 validity → feed invariant → r2 validity. -/
theorem double_validity (hn : n > 3 * f) (b : T) :
    pred_implies (spec T n f).safety
      [tlafml| □ ⌜ fun s =>
        (∀ p, ¬isCorrect T n (proj_r1 T n s) p ∨
              (s.r1.local_ p).input = none ∨
              (s.r1.local_ p).input = some b) →
        ∀ p, (s.r2.local_ p).decided = none ∨
             (s.r2.local_ p).decided = some (some (some b)) ⌝] := by
  intro e hsafety k hr1_inputs p
  -- Step 1: r1 validity at step k
  have hr1_val : validity T n b (proj_r1 T n (exec.drop k e 0)) :=
    r1_validity T n f hn b e hsafety k
  -- Apply r1 validity to get r1 decisions
  have hr1_dec := hr1_val hr1_inputs
  -- Step 2: r2 validity at step k
  have hr2_val : validity (Val T) n (some b) (proj_r2 T n (exec.drop k e 0)) :=
    r2_validity T n f hn (some b) e hsafety k
  -- Apply r2 validity — need its antecedent
  apply hr2_val
  · -- ∀ q, ¬isCorrect q ∨ r2.input = none ∨ r2.input = some (some b)
    intro q
    simp only [proj_r2, toR2State]
    cases hinp : ((exec.drop k e 0).r2.local_ q).input with
    | none => exact Or.inr (Or.inl rfl)
    | some mv =>
      have hfeed := feed_invariant T n f e hsafety k q mv hinp
      -- r1.decided q = some mv. By r1_dec: decided = none ∨ some (some b).
      rcases hr1_dec q with hdec_none | hdec_some
      · -- decided = none contradicts hfeed
        simp only [proj_r1, toR1State] at hdec_none
        rw [hdec_none] at hfeed ; exact absurd hfeed (by simp)
      · -- decided = some (some b). So mv = some b.
        simp only [proj_r1, toR1State] at hdec_some
        rw [hdec_some] at hfeed
        exact Or.inr (Or.inr (by simp only [Option.some.inj hfeed]))

end DoubleBCA
