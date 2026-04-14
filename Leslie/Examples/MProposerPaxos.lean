import Batteries.Data.List.Lemmas

/-! # m-Proposer Paxos: Bounded-Unrolling Feasibility Test

    Generalization of `TwoProposerPaxos.lean` to an arbitrary number of
    proposers `m`.  Single-decree, binary value space, `n` acceptors.

    The progress measure is a per-acceptor phase in `{0, ..., 2m + 1}`
    plus a per-proposer phase in `{0, 1}`.  The global sum is bounded
    by `(2 * m + 1) * n + m = 2 * m * n + n + m`, so any trace from
    `initialState` has length at most `2 * m * n + n + m`.

    Safety is proved using the same "defer gate" shortcut as in the
    two-proposer case, generalized: when a proposer acts, it must copy
    the value of *any* other proposer that has already proposed.  This
    makes `values_agree` trivially inductive.

    Core Lean 4 only; no Mathlib. -/

namespace MProposerPaxos

/-! ## Section 1: Model -/

/-- Binary value space. -/
abbrev Val : Type := Fin 2

/-- `m` proposer ids ordered by ballot. -/
abbrev Proposer (m : Nat) : Type := Fin m

/-- Per-acceptor local state. -/
structure AcceptorState (m : Nat) where
  promised : Option (Proposer m)
  accepted : Option (Proposer m × Val)

/-- Per-proposer state. -/
structure ProposerState where
  proposed : Option Val

/-- Global state. -/
structure PaxosState (n m : Nat) where
  locals    : Fin n → AcceptorState m
  proposers : Proposer m → ProposerState

inductive Action (n m : Nat) where
  | prepare : Proposer m → Fin n → Action n m
  | propose : Proposer m → Val → Action n m
  | accept  : Proposer m → Fin n → Action n m

/-- Does proposer `p` strictly outrank the current promise? -/
def outranks {m : Nat} (current : Option (Proposer m)) (p : Proposer m) : Prop :=
  match current with
  | none   => True
  | some q => q.val < p.val

/-- Functional update on `locals`. -/
def setLocal {n m : Nat} (f : Fin n → AcceptorState m) (i : Fin n)
    (a : AcceptorState m) : Fin n → AcceptorState m :=
  fun j => if j = i then a else f j

@[simp] theorem setLocal_self {n m : Nat} (f : Fin n → AcceptorState m)
    (i : Fin n) (a : AcceptorState m) : setLocal f i a i = a := by
  simp [setLocal]

@[simp] theorem setLocal_ne {n m : Nat} (f : Fin n → AcceptorState m)
    (i j : Fin n) (a : AcceptorState m) (h : j ≠ i) : setLocal f i a j = f j := by
  simp [setLocal, h]

/-- Functional update on `proposers`. -/
def setProp {m : Nat} (f : Proposer m → ProposerState) (p : Proposer m)
    (s : ProposerState) : Proposer m → ProposerState :=
  fun q => if q = p then s else f q

@[simp] theorem setProp_self {m : Nat} (f : Proposer m → ProposerState)
    (p : Proposer m) (s : ProposerState) : setProp f p s p = s := by
  simp [setProp]

@[simp] theorem setProp_ne {m : Nat} (f : Proposer m → ProposerState)
    (p q : Proposer m) (s : ProposerState) (h : q ≠ p) : setProp f p s q = f q := by
  simp [setProp, h]

def preparedAt {m : Nat} (a : AcceptorState m) (p : Proposer m) : AcceptorState m :=
  { a with promised := some p }

def acceptedAt {m : Nat} (a : AcceptorState m) (p : Proposer m) (v : Val) :
    AcceptorState m :=
  { a with accepted := some (p, v) }

def proposedAt (_s : ProposerState) (v : Val) : ProposerState :=
  { proposed := some v }

/-- One-step transition.  The `propose` step carries a defer gate: the
    proposing proposer must copy the value of any other proposer that
    has already proposed. -/
def step {n m : Nat} (s s' : PaxosState n m) (a : Action n m) : Prop :=
  match a with
  | .prepare p i =>
      outranks (s.locals i).promised p ∧
      s' = { s with locals := setLocal s.locals i (preparedAt (s.locals i) p) }
  | .propose p v =>
      (s.proposers p).proposed = none ∧
      (∀ (q : Proposer m) (w : Val),
          q ≠ p → (s.proposers q).proposed = some w → v = w) ∧
      s' = { s with proposers := setProp s.proposers p (proposedAt (s.proposers p) v) }
  | .accept p i =>
      (s.locals i).promised = some p ∧
      (s.locals i).accepted = none ∧
      (∃ v, (s.proposers p).proposed = some v ∧
            s' = { s with
              locals := setLocal s.locals i (acceptedAt (s.locals i) p v) })

def initialState (n m : Nat) : PaxosState n m where
  locals    := fun _ => { promised := none, accepted := none }
  proposers := fun _ => { proposed := none }

inductive Reachable {n m : Nat} : PaxosState n m → Prop where
  | init : Reachable (initialState n m)
  | step : ∀ {s s'} a, Reachable s → step s s' a → Reachable s'

/-! ## Section 2: List / Fin sum plumbing. -/

def listSum {α : Type _} (f : α → Nat) : List α → Nat
  | [] => 0
  | x :: xs => f x + listSum f xs

theorem listSum_le_const {α : Type _} (f : α → Nat) (k : Nat)
    (h : ∀ x, f x ≤ k) : ∀ (xs : List α), listSum f xs ≤ xs.length * k
  | [] => by simp [listSum]
  | x :: xs => by
      have hx := h x
      have hxs := listSum_le_const f k h xs
      simp [listSum, List.length_cons, Nat.succ_mul]
      omega

theorem listSum_update_not_mem {α : Type _} [DecidableEq α]
    (f : α → Nat) (i : α) (v : Nat) (xs : List α) (hni : i ∉ xs) :
    listSum (fun j => if j = i then v else f j) xs = listSum f xs := by
  induction xs with
  | nil => simp [listSum]
  | cons y ys ih =>
    have hy : y ≠ i := by intro h; exact hni (by simp [h])
    have hys : i ∉ ys := fun h => hni (by simp [h])
    simp [listSum, if_neg hy, ih hys]

theorem listSum_update_mem {α : Type _} [DecidableEq α]
    (f : α → Nat) (i : α) (v : Nat) (xs : List α)
    (hmem : i ∈ xs) (hnd : xs.Nodup) :
    listSum (fun j => if j = i then v else f j) xs + f i = listSum f xs + v := by
  induction xs with
  | nil => cases hmem
  | cons x xs ih =>
    by_cases hx : x = i
    · rw [hx] at hnd
      have hxni : i ∉ xs := (List.nodup_cons.mp hnd).1
      have hxs := listSum_update_not_mem f i v xs hxni
      show (if x = i then v else f x)
            + listSum (fun j => if j = i then v else f j) xs + f i
            = f x + listSum f xs + v
      rw [if_pos hx, hxs, hx]; omega
    · have hmem' : i ∈ xs := by
        cases hmem with
        | head => exact absurd rfl hx
        | tail _ h => exact h
      have hnd' : xs.Nodup := (List.nodup_cons.mp hnd).2
      have ih' := ih hmem' hnd'
      show (if x = i then v else f x)
            + listSum (fun j => if j = i then v else f j) xs + f i
            = f x + listSum f xs + v
      rw [if_neg hx]; omega

def finSum {n : Nat} (f : Fin n → Nat) : Nat :=
  listSum f (List.finRange n)

theorem finSum_le_const {n : Nat} (f : Fin n → Nat) (k : Nat)
    (h : ∀ i, f i ≤ k) : finSum f ≤ n * k := by
  unfold finSum
  have := listSum_le_const f k h (List.finRange n)
  rw [List.length_finRange] at this
  exact this

theorem finSum_update {n : Nat} (f : Fin n → Nat) (i : Fin n) (v : Nat) :
    finSum (fun j => if j = i then v else f j) + f i = finSum f + v := by
  unfold finSum
  exact listSum_update_mem f i v (List.finRange n)
    (List.mem_finRange i) (List.nodup_finRange n)

theorem listSum_zero {α : Type _} (f : α → Nat) (hf : ∀ x, f x = 0) :
    ∀ xs : List α, listSum f xs = 0
  | [] => by simp [listSum]
  | x :: xs => by simp [listSum, hf x, listSum_zero f hf xs]

/-! ## Section 3: Progress measure

    * `promiseLevel none = 0`, `promiseLevel (some p) = p.val + 1`.
      Bound: `≤ m`.
    * `acceptorPhase a = promiseLevel a.promised + (m+1) * [accepted]`.
      Bound: `≤ 2 * m + 1`.
    * `proposerPhase p = 1 iff proposed.isSome`.  Bound: `≤ 1`.
    * `phaseCounter s = finSum acceptorPhase + finSum proposerPhase`.
      Bound: `(2 * m + 1) * n + m = 2 * m * n + n + m`. -/

def promiseLevel {m : Nat} (o : Option (Proposer m)) : Nat :=
  match o with
  | none   => 0
  | some p => p.val + 1

@[simp] theorem promiseLevel_none {m : Nat} : promiseLevel (none : Option (Proposer m)) = 0 :=
  rfl

@[simp] theorem promiseLevel_some {m : Nat} (p : Proposer m) :
    promiseLevel (some p) = p.val + 1 := rfl

theorem promiseLevel_le {m : Nat} (o : Option (Proposer m)) : promiseLevel o ≤ m := by
  cases o with
  | none => simp
  | some p => have := p.isLt; simp; omega

def acceptorPhase {m : Nat} (a : AcceptorState m) : Nat :=
  promiseLevel a.promised + (if a.accepted.isSome then m + 1 else 0)

theorem acceptorPhase_le {m : Nat} (a : AcceptorState m) :
    acceptorPhase a ≤ 2 * m + 1 := by
  unfold acceptorPhase
  have := promiseLevel_le a.promised
  by_cases h : a.accepted.isSome <;> simp [h] <;> omega

def proposerPhase (p : ProposerState) : Nat :=
  if p.proposed.isSome then 1 else 0

theorem proposerPhase_le_one (p : ProposerState) : proposerPhase p ≤ 1 := by
  unfold proposerPhase; split <;> simp

/-- Global progress measure: acceptor sum plus proposer sum. -/
def phaseCounter {n m : Nat} (s : PaxosState n m) : Nat :=
  finSum (fun i => acceptorPhase (s.locals i))
    + finSum (fun p => proposerPhase (s.proposers p))

theorem phaseCounter_bounded {n m : Nat} (s : PaxosState n m) :
    phaseCounter s ≤ (2 * m + 1) * n + m := by
  unfold phaseCounter
  have ha := finSum_le_const (fun i => acceptorPhase (s.locals i)) (2 * m + 1)
    (fun i => acceptorPhase_le _)
  have hp := finSum_le_const (fun p => proposerPhase (s.proposers p)) 1
    (fun p => proposerPhase_le_one _)
  have hp' : finSum (fun p => proposerPhase (s.proposers p)) ≤ m := by
    have := hp; simpa [Nat.mul_one] using this
  have hcomm : n * (2 * m + 1) = (2 * m + 1) * n := Nat.mul_comm _ _
  omega

theorem phaseCounter_initialState (n m : Nat) :
    phaseCounter (initialState n m) = 0 := by
  unfold phaseCounter finSum
  have h0 : listSum (fun i => acceptorPhase ((initialState n m).locals i))
              (List.finRange n) = 0 := by
    apply listSum_zero
    intro i; simp [initialState, acceptorPhase]
  have h1 : listSum (fun p => proposerPhase ((initialState n m).proposers p))
              (List.finRange m) = 0 := by
    apply listSum_zero
    intro p; simp [initialState, proposerPhase]
  rw [h0, h1]

/-! ### Phase-increment lemmas -/

/-- If `p` outranks `o`, the new promise level is strictly greater. -/
theorem promiseLevel_upgrade {m : Nat} (o : Option (Proposer m)) (p : Proposer m)
    (h : outranks o p) :
    promiseLevel (some p) ≥ promiseLevel o + 1 := by
  unfold outranks at h
  cases o with
  | none => simp
  | some q =>
    have hq : q.val < p.val := h
    simp; omega

theorem acceptorPhase_prepare {m : Nat} (a : AcceptorState m) (p : Proposer m)
    (h : outranks a.promised p) :
    acceptorPhase (preparedAt a p) ≥ acceptorPhase a + 1 := by
  have hp := promiseLevel_upgrade a.promised p h
  have hacc : (preparedAt a p).accepted = a.accepted := rfl
  have hpro : (preparedAt a p).promised = some p := rfl
  unfold acceptorPhase
  rw [hacc, hpro]
  omega

theorem acceptorPhase_accept {m : Nat} (a : AcceptorState m) (p : Proposer m) (v : Val)
    (_hprom : a.promised = some p) (hacc : a.accepted = none) :
    acceptorPhase (acceptedAt a p v) = acceptorPhase a + (m + 1) := by
  unfold acceptorPhase acceptedAt
  have : a.accepted.isSome = false := by rw [hacc]; rfl
  simp [this]

theorem finSum_acceptor_update {n m : Nat} (f : Fin n → AcceptorState m)
    (i : Fin n) (a : AcceptorState m) :
    finSum (fun j => acceptorPhase ((setLocal f i a) j)) + acceptorPhase (f i)
      = finSum (fun j => acceptorPhase (f j)) + acceptorPhase a := by
  have hrw : (fun j => acceptorPhase ((setLocal f i a) j)) =
             (fun j => if j = i then acceptorPhase a else acceptorPhase (f j)) := by
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [setLocal, h]
  rw [hrw]
  exact finSum_update (fun j => acceptorPhase (f j)) i (acceptorPhase a)

theorem finSum_proposer_update {m : Nat} (f : Proposer m → ProposerState)
    (p : Proposer m) (s : ProposerState) :
    finSum (fun q => proposerPhase ((setProp f p s) q)) + proposerPhase (f p)
      = finSum (fun q => proposerPhase (f q)) + proposerPhase s := by
  have hrw : (fun q => proposerPhase ((setProp f p s) q)) =
             (fun q => if q = p then proposerPhase s else proposerPhase (f q)) := by
    funext q
    by_cases h : q = p
    · subst h; simp
    · simp [setProp, h]
  rw [hrw]
  exact finSum_update (fun q => proposerPhase (f q)) p (proposerPhase s)

theorem phaseCounter_prepare {n m : Nat} (s s' : PaxosState n m)
    (p : Proposer m) (i : Fin n)
    (hstep : step s s' (.prepare p i)) :
    phaseCounter s' ≥ phaseCounter s + 1 := by
  obtain ⟨hok, hs'⟩ := hstep
  subst hs'
  have hfu := finSum_acceptor_update s.locals i (preparedAt (s.locals i) p)
  have hge := acceptorPhase_prepare (s.locals i) p hok
  change finSum (fun j => acceptorPhase
      ((setLocal s.locals i (preparedAt (s.locals i) p)) j))
      + finSum (fun q => proposerPhase (s.proposers q))
    ≥ phaseCounter s + 1
  unfold phaseCounter
  omega

theorem phaseCounter_accept {n m : Nat} (s s' : PaxosState n m)
    (p : Proposer m) (i : Fin n)
    (hstep : step s s' (.accept p i)) :
    phaseCounter s' = phaseCounter s + (m + 1) := by
  obtain ⟨hprom, hacc, v, _hprop, hs'⟩ := hstep
  subst hs'
  have hfu := finSum_acceptor_update s.locals i (acceptedAt (s.locals i) p v)
  have heq := acceptorPhase_accept (s.locals i) p v hprom hacc
  change finSum (fun j => acceptorPhase
      ((setLocal s.locals i (acceptedAt (s.locals i) p v)) j))
      + finSum (fun q => proposerPhase (s.proposers q))
    = phaseCounter s + (m + 1)
  unfold phaseCounter
  omega

theorem phaseCounter_propose {n m : Nat} (s s' : PaxosState n m)
    (p : Proposer m) (v : Val)
    (hstep : step s s' (.propose p v)) :
    phaseCounter s' = phaseCounter s + 1 := by
  obtain ⟨hnone, _hdefer, hs'⟩ := hstep
  subst hs'
  have hfu := finSum_proposer_update s.proposers p (proposedAt (s.proposers p) v)
  have hold : proposerPhase (s.proposers p) = 0 := by
    unfold proposerPhase; rw [hnone]; rfl
  have hnew : proposerPhase (proposedAt (s.proposers p) v) = 1 := by
    unfold proposerPhase; simp [proposedAt]
  change finSum (fun j => acceptorPhase (s.locals j))
      + finSum (fun q => proposerPhase
          ((setProp s.proposers p (proposedAt (s.proposers p) v)) q))
    = phaseCounter s + 1
  unfold phaseCounter
  omega

theorem phaseCounter_monotone {n m : Nat} (s s' : PaxosState n m) (a : Action n m)
    (hstep : step s s' a) :
    phaseCounter s' ≥ phaseCounter s + 1 := by
  cases a with
  | prepare p i => exact phaseCounter_prepare s s' p i hstep
  | propose p v =>
      have h := phaseCounter_propose s s' p v hstep
      omega
  | accept  p i =>
      have h := phaseCounter_accept s s' p i hstep
      omega

/-! ## Section 4: Traces and diameter bound -/

inductive StepsFrom {n m : Nat} :
    PaxosState n m → List (Action n m) → PaxosState n m → Prop where
  | nil  : ∀ s, StepsFrom s [] s
  | cons : ∀ {s s' s'' : PaxosState n m} (a : Action n m) (acts : List (Action n m)),
             step s s' a → StepsFrom s' acts s'' → StepsFrom s (a :: acts) s''

theorem phaseCounter_after_steps {n m : Nat}
    {s s'' : PaxosState n m} {acts : List (Action n m)}
    (hs : StepsFrom s acts s'') :
    phaseCounter s'' ≥ phaseCounter s + acts.length := by
  induction hs with
  | nil s => simp
  | @cons s₁ s₂ s₃ a acts hstep _ ih =>
    have h1 := phaseCounter_monotone s₁ s₂ a hstep
    simp [List.length_cons]
    omega

theorem phaseCounter_fires_finitely_often {n m : Nat} (s s' : PaxosState n m)
    (acts : List (Action n m)) (hs : StepsFrom s acts s') :
    acts.length ≤ (2 * m + 1) * n + m - phaseCounter s := by
  have hafter := phaseCounter_after_steps hs
  have hbnd := phaseCounter_bounded s'
  omega

theorem StepsFrom.snoc {n m : Nat} {p q r : PaxosState n m} {as : List (Action n m)}
    (b : Action n m) (hpq : StepsFrom p as q) (hqr : step q r b) :
    StepsFrom p (as ++ [b]) r := by
  induction hpq with
  | nil s => exact StepsFrom.cons b [] hqr (StepsFrom.nil _)
  | @cons s₁ s₂ s₃ x xs hx _ ih => exact StepsFrom.cons x (xs ++ [b]) hx (ih hqr)

theorem stepsFrom_preserves_reachable {n m : Nat} {s₀ s : PaxosState n m}
    {acts : List (Action n m)} (h : StepsFrom s₀ acts s) (h₀ : Reachable s₀) :
    Reachable s := by
  induction h with
  | nil s => exact h₀
  | @cons s₁ s₂ s₃ a acts hstep _ ih =>
    exact ih (Reachable.step a h₀ hstep)

theorem stepsFrom_to_reachable {n m : Nat} {acts : List (Action n m)}
    {s : PaxosState n m} (h : StepsFrom (initialState n m) acts s) : Reachable s :=
  stepsFrom_preserves_reachable h Reachable.init

theorem reachable_iff_stepsFrom {n m : Nat} (s : PaxosState n m) :
    Reachable s ↔ ∃ acts, StepsFrom (initialState n m) acts s := by
  constructor
  · intro h
    induction h with
    | init => exact ⟨[], StepsFrom.nil _⟩
    | step a _ hstep ih =>
      obtain ⟨acts, hfrom⟩ := ih
      exact ⟨acts ++ [a], StepsFrom.snoc a hfrom hstep⟩
  · rintro ⟨acts, hfrom⟩
    exact stepsFrom_to_reachable hfrom

/-! ## Section 5: Safety (agreement) -/

def agreement {n m : Nat} (s : PaxosState n m) : Prop :=
  ∀ (i j : Fin n) (p q : Proposer m) (v w : Val),
    (s.locals i).accepted = some (p, v) →
    (s.locals j).accepted = some (q, w) →
    v = w

structure SafetyInv {n m : Nat} (s : PaxosState n m) : Prop where
  accept_matches_propose :
    ∀ (i : Fin n) (p : Proposer m) (v : Val),
      (s.locals i).accepted = some (p, v) →
      (s.proposers p).proposed = some v
  values_agree :
    ∀ (p q : Proposer m) (v w : Val),
      (s.proposers p).proposed = some v →
      (s.proposers q).proposed = some w →
      v = w

theorem agreement_of_safetyInv {n m : Nat} (s : PaxosState n m) (h : SafetyInv s) :
    agreement s := by
  intro i j p q v w hi hj
  have hpv := h.accept_matches_propose i p v hi
  have hqw := h.accept_matches_propose j q w hj
  exact h.values_agree p q v w hpv hqw

theorem safetyInv_initial {n m : Nat} : SafetyInv (initialState n m) := by
  refine ⟨?_, ?_⟩
  · intro i p v hi
    simp [initialState] at hi
  · intro p q v w h0 _
    simp [initialState] at h0

theorem safetyInv_preserved {n m : Nat} {s s' : PaxosState n m}
    (_hreach : Reachable s) (a : Action n m)
    (hstep : step s s' a) (hinv : SafetyInv s) : SafetyInv s' := by
  cases a with
  | prepare p i =>
    obtain ⟨_, hs'⟩ := hstep
    subst hs'
    refine ⟨?_, ?_⟩
    · intro j q v hj
      by_cases hji : j = i
      · subst hji
        simp [setLocal, preparedAt] at hj
        exact hinv.accept_matches_propose j q v hj
      · simp [setLocal, hji] at hj
        exact hinv.accept_matches_propose j q v hj
    · intro p' q' v' w' h0 h1
      exact hinv.values_agree p' q' v' w' h0 h1
  | accept p i =>
    obtain ⟨_hprom, _hacc, v, hprop, hs'⟩ := hstep
    subst hs'
    refine ⟨?_, ?_⟩
    · intro j q w hj
      by_cases hji : j = i
      · subst hji
        simp [setLocal, acceptedAt] at hj
        obtain ⟨rfl, rfl⟩ := hj
        exact hprop
      · simp [setLocal, hji] at hj
        exact hinv.accept_matches_propose j q w hj
    · intro p' q' v' w' h0 h1
      exact hinv.values_agree p' q' v' w' h0 h1
  | propose p v =>
    obtain ⟨hnone, hdefer, hs'⟩ := hstep
    subst hs'
    refine ⟨?_, ?_⟩
    · intro j q w hj
      have hj' : (s.locals j).accepted = some (q, w) := hj
      have hmatch := hinv.accept_matches_propose j q w hj'
      by_cases hqp : q = p
      · subst hqp
        rw [hnone] at hmatch; cases hmatch
      · show ((setProp s.proposers p (proposedAt (s.proposers p) v)) q).proposed
              = some w
        rw [setProp_ne _ _ _ _ hqp]
        exact hmatch
    · -- values_agree after propose
      intro p' q' v' w' h0 h1
      -- For each proposer pid ∈ {p', q'}, extract its "pre-step" state.
      by_cases hp'p : p' = p
      · -- p' = p: v' is the freshly-proposed value v.
        subst hp'p
        have hvv' : v' = v := by
          have hh : ((setProp s.proposers p' (proposedAt (s.proposers p') v)) p').proposed
                  = some v' := h0
          rw [setProp_self, proposedAt] at hh
          exact (Option.some.inj hh).symm
        by_cases hq'p : q' = p'
        · subst hq'p
          have hww' : w' = v := by
            have hh : ((setProp s.proposers q' (proposedAt (s.proposers q') v)) q').proposed
                    = some w' := h1
            rw [setProp_self, proposedAt] at hh
            exact (Option.some.inj hh).symm
          rw [hvv', hww']
        · -- q' ≠ p: q' was unchanged and already = some w'.
          have hq'old : (s.proposers q').proposed = some w' := by
            have hh : ((setProp s.proposers p' (proposedAt (s.proposers p') v)) q').proposed
                    = some w' := h1
            rwa [setProp_ne _ _ _ _ hq'p] at hh
          -- Defer gate: since q' ≠ p and q' already proposed w', v = w'.
          have hvw : v = w' := hdefer q' w' hq'p hq'old
          rw [hvv', hvw]
      · -- p' ≠ p: p' unchanged, so (s.proposers p').proposed = some v'
        have hp'old : (s.proposers p').proposed = some v' := by
          have hh : ((setProp s.proposers p (proposedAt (s.proposers p) v)) p').proposed
                  = some v' := h0
          rwa [setProp_ne _ _ _ _ hp'p] at hh
        by_cases hq'p : q' = p
        · subst hq'p
          have hww' : w' = v := by
            have hh : ((setProp s.proposers q' (proposedAt (s.proposers q') v)) q').proposed
                    = some w' := h1
            rw [setProp_self, proposedAt] at hh
            exact (Option.some.inj hh).symm
          have hvv' : v = v' := hdefer p' v' hp'p hp'old
          rw [hww', ← hvv']
        · have hq'old : (s.proposers q').proposed = some w' := by
            have hh : ((setProp s.proposers p (proposedAt (s.proposers p) v)) q').proposed
                    = some w' := h1
            rwa [setProp_ne _ _ _ _ hq'p] at hh
          exact hinv.values_agree p' q' v' w' hp'old hq'old

theorem agreement_reachable {n m : Nat} (s : PaxosState n m) (h : Reachable s) :
    agreement s := by
  have hinv : SafetyInv s := by
    induction h with
    | init => exact safetyInv_initial
    | step a hreach' hstep ih =>
        exact safetyInv_preserved hreach' a hstep ih
  exact agreement_of_safetyInv s hinv

/-! ## Section 6: Bounded-unrolling theorem -/

def safeUpTo (n m : Nat) (k : Nat) : Prop :=
  ∀ acts : List (Action n m), acts.length ≤ k →
    ∀ s', StepsFrom (initialState n m) acts s' → agreement s'

def safeAll (n m : Nat) : Prop :=
  ∀ s : PaxosState n m, Reachable s → agreement s

/-- **Main theorem: m-proposer Paxos bounded unrolling.** Safety of all
    reachable states is equivalent to safety of states reachable within
    `2 * m * n + n + m` steps from the initial state. -/
theorem m_proposer_bounded_unrolling (n m : Nat) :
    safeAll n m ↔ safeUpTo n m (2 * m * n + n + m) := by
  constructor
  · intro hall acts _ s' hfrom
    apply hall
    exact (reachable_iff_stepsFrom s').mpr ⟨acts, hfrom⟩
  · intro _ s hreach
    obtain ⟨acts, hfrom⟩ := (reachable_iff_stepsFrom s).mp hreach
    have hlen : acts.length ≤ 2 * m * n + n + m := by
      have h := phaseCounter_fires_finitely_often _ _ _ hfrom
      have h0 : phaseCounter (initialState n m) = 0 :=
        phaseCounter_initialState n m
      have hbnd : (2 * m + 1) * n + m = 2 * m * n + n + m := by
        rw [Nat.add_mul, Nat.one_mul]
      omega
    exact agreement_reachable s hreach

/-! ## Section 7: Sanity checks -/

example : phaseCounter (initialState 3 2) = 0 :=
  phaseCounter_initialState 3 2

example : ∀ (s : PaxosState 3 2), phaseCounter s ≤ 17 := by
  intro s
  have := phaseCounter_bounded (n := 3) (m := 2) s
  omega

end MProposerPaxos
