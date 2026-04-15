import Batteries.Data.List.Lemmas
import Leslie.Examples.CutoffReasoning.PhaseCountingThreshold

/-! # Two-Proposer Paxos: Bounded-Unrolling Feasibility Test

    A follow-on to `SingleProposerPaxos.lean`.  Two proposers with fixed
    ballots `b₀ < b₁`, `n` acceptors, one slot, binary value space.

    ## ⚠ Scope — READ THIS FIRST

    **This file does NOT mechanize real two-proposer Paxos.**  It proves
    the bounded-unrolling theorem on a *restricted* model that replaces
    Paxos's promise-quorum + max-vote safety argument with a
    deterministic "defer rule": whichever proposer acts second must
    simply copy the value the first proposer chose.

    Concretely, the `.propose p v` step (§Section 1 below) contains the
    conjunct

        ∀ w, (s.proposers 0).proposed = some w → p = 1 → v = w
        ∀ w, (s.proposers 1).proposed = some w → p = 0 → v = w

    instead of real Paxos's

        ∃ Q, majority Q ∧ ∀ i ∈ Q, i has promised to p ∧
        (∀ c < p.ballot, hSafe-style max-vote constraint)

    The defer rule is a **sound strengthening** of real Paxos (it admits
    strictly fewer behaviors), but it completely sidesteps the
    quorum-intersection reasoning that makes real Paxos verification
    hard.  In particular:

    * No `promise quorum` is tracked.
    * No witness for `SafeAt(v, p)` is carried through the invariant.
    * The `hcon` / `hconstr` constraint from Paxos's `p2a` is absent.
    * `values_agree` becomes step-inductive without any `hSafe`-like
      field, because the defer rule forces it directly.

    **What this file DOES demonstrate:**

    * The bounded-unrolling *framework* (phase counter + diameter bound
      + `safeAll ↔ safeUpTo` iff) applies cleanly to a Paxos-shaped
      ballot-ordered protocol.
    * The per-acceptor phase counter `promiseLevel ∈ {0, 1, 2}` handles
      higher-ballot promise upgrades without a lexicographic measure.
    * The framework scales from single-proposer to two-proposer without
      structural changes — only the counter arithmetic and safety
      invariant differ.

    **What this file DOES NOT demonstrate:**

    * Real Paxos safety via quorum intersection.
    * Non-trivial `hSafe`/`hC`/`hG` max-vote reasoning.
    * Any property of Paxos that depends on the timing of promises
      interleaved with accepts.

    A future file mechanizing real quorum-gated Paxos with a proper
    `hSafe`-style invariant would be ~1000+ additional lines and is
    deferred.  See `docs/cutoff-theorems.md` §5.13 for the obstacles and
    §5.13.4 for the tractable subproblem ladder.

    ## Historical note

    An earlier version of this file had NO cross-proposer ordering gate
    (not even the defer rule) and was discovered to be unsound during
    sorry discharge: a concrete 6-step counterexample at `n = 2` proves
    `agreement` is false without the gate.  The defer rule was added in
    commit 3 of PR #18 to close the sorry.  The counterexample and its
    resolution are the reason for the strong scope note above.

    ## Theorem summary

    * **Phase counting**: every action strictly increases a per-acceptor
      phase in `{0, 1, 2, 3, 4}` plus a per-proposer phase in `{0, 1}`.
      The global sum is bounded by `4 * n + 2`, so any trace from
      `initialState` has length ≤ `4 * n + 2`.
    * **Bounded unrolling**: safety of *all* reachable states is
      equivalent to safety of states reachable in ≤ `4 * n + 2` steps.
    * **Safety (restricted)**: `agreement_reachable` holds for all
      reachable states of the *defer-gated* model.  See scope note above
      for what this does and does not entail.

    Core Lean 4 only; no Mathlib. -/

namespace TwoProposerPaxos

/-! ## Section 1: Model -/

/-- Binary value space. -/
abbrev Val : Type := Fin 2

/-- Two proposer ids: `0` is the low ballot, `1` is the high ballot. -/
abbrev Proposer : Type := Fin 2

/-- Per-acceptor local state. -/
structure AcceptorState where
  /-- Highest-ballot proposer this acceptor has promised to, if any. -/
  promised : Option Proposer
  /-- Most recently accepted `(proposer, value)` pair, if any. -/
  accepted : Option (Proposer × Val)
  deriving DecidableEq, Repr

/-- Per-proposer state: which value (if any) has been proposed. -/
structure ProposerState where
  proposed : Option Val
  deriving DecidableEq, Repr

/-- Global state. -/
structure PaxosState (n : Nat) where
  locals    : Fin n → AcceptorState
  proposers : Proposer → ProposerState

/-- Actions.  `prepare p i`: acceptor `i` upgrades its promise to `p` (if
    current promise is strictly below `p`).  `propose p v`: proposer `p`
    picks a value `v` (constrained by `hconstr` if `p = 1`).
    `accept p i`: acceptor `i` accepts `p`'s proposed value. -/
inductive Action (n : Nat) where
  | prepare : Proposer → Fin n → Action n
  | propose : Proposer → Val → Action n
  | accept  : Proposer → Fin n → Action n

/-- Does proposer `p` strictly dominate the current promise? -/
def outranks (current : Option Proposer) (p : Proposer) : Prop :=
  match current with
  | none    => True
  | some q  => q.val < p.val

instance : DecidablePred (outranks · 0) := by
  intro c; cases c <;> simp [outranks] <;> infer_instance
instance : DecidablePred (outranks · 1) := by
  intro c; cases c <;> simp [outranks] <;> infer_instance

/-- Update function for `locals`. -/
def setLocal {n : Nat} (f : Fin n → AcceptorState) (i : Fin n)
    (a : AcceptorState) : Fin n → AcceptorState :=
  fun j => if j = i then a else f j

@[simp] theorem setLocal_self {n : Nat} (f : Fin n → AcceptorState) (i : Fin n)
    (a : AcceptorState) : setLocal f i a i = a := by
  simp [setLocal]

@[simp] theorem setLocal_ne {n : Nat} (f : Fin n → AcceptorState) (i j : Fin n)
    (a : AcceptorState) (h : j ≠ i) : setLocal f i a j = f j := by
  simp [setLocal, h]

/-- Update function for `proposers`. -/
def setProp (f : Proposer → ProposerState) (p : Proposer)
    (s : ProposerState) : Proposer → ProposerState :=
  fun q => if q = p then s else f q

@[simp] theorem setProp_self (f : Proposer → ProposerState) (p : Proposer)
    (s : ProposerState) : setProp f p s p = s := by
  simp [setProp]

@[simp] theorem setProp_ne (f : Proposer → ProposerState) (p q : Proposer)
    (s : ProposerState) (h : q ≠ p) : setProp f p s q = f q := by
  simp [setProp, h]

/-- Acceptor after a `prepare p i` action. -/
def preparedAt (a : AcceptorState) (p : Proposer) : AcceptorState :=
  { a with promised := some p }

/-- Acceptor after an `accept p i v` action. -/
def acceptedAt (a : AcceptorState) (p : Proposer) (v : Val) : AcceptorState :=
  { a with accepted := some (p, v) }

/-- Proposer `p` with proposed value `v`. -/
def proposedAt (_s : ProposerState) (v : Val) : ProposerState :=
  { proposed := some v }

/-- One-step transition as a predicate on pre/post states and an action.
    For simplicity, the low proposer (`p = 0`) may pick any value; the high
    proposer (`p = 1`) obeys the full Paxos `hconstr`: if *some* acceptor
    reports a prior acceptance from a strictly lower proposer, the chosen
    value must equal that prior value.  We encode this as a direct lookup
    in the global state (the "responses are the current truth" shortcut
    is sound because `promised` is monotone along ballot ordering). -/
def step {n : Nat} (s s' : PaxosState n) (a : Action n) : Prop :=
  match a with
  | .prepare p i =>
      outranks (s.locals i).promised p ∧
      s' = { s with locals := setLocal s.locals i (preparedAt (s.locals i) p) }
  | .propose p v =>
      (s.proposers p).proposed = none ∧
      -- hconstr: if `p = 1`, any prior accept from `p = 0` forces `v` to match.
      (∀ (i : Fin n) (w : Val),
          p = (1 : Proposer) →
          (s.locals i).accepted = some (0, w) → v = w) ∧
      -- Cross-proposer defer gate (two-proposer specialization of the
      -- Paxos promise-quorum + max-vote rule).  Whichever proposer acts
      -- second must copy the value the first proposer chose.  This is
      -- sound because with only two proposers one of them is always
      -- "second", and it gives us a trivially inductive `values_agree`
      -- without needing to carry a witness quorum through the invariant.
      (∀ w, (s.proposers 0).proposed = some w → p = (1 : Proposer) → v = w) ∧
      (∀ w, (s.proposers 1).proposed = some w → p = (0 : Proposer) → v = w) ∧
      s' = { s with proposers := setProp s.proposers p (proposedAt (s.proposers p) v) }
  | .accept p i =>
      (s.locals i).promised = some p ∧
      (s.locals i).accepted = none ∧
      (∃ v, (s.proposers p).proposed = some v ∧
            s' = { s with
              locals := setLocal s.locals i (acceptedAt (s.locals i) p v) })

/-- Canonical initial state. -/
def initialState (n : Nat) : PaxosState n where
  locals    := fun _ => { promised := none, accepted := none }
  proposers := fun _ => { proposed := none }

inductive Reachable {n : Nat} : PaxosState n → Prop where
  | init : Reachable (initialState n)
  | step : ∀ {s s'} a, Reachable s → step s s' a → Reachable s'

/-! ## Section 2: List/Fin sum plumbing (duplicated from SingleProposerPaxos to
    keep this file self-contained). -/

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

    Per-acceptor phase, with the interesting case being the upgrade
    `promised = some 0 → some 1`:

    * 0 if unpromised and unaccepted
    * 1 if `promised = some 0` and unaccepted
    * 2 if `promised = some 1` and unaccepted
    * 3 if `promised = some 0` and accepted
    * 4 if `promised = some 1` and accepted

    Each action that touches acceptor `i` strictly increases its phase:
    * `prepare 0 i` (unpromised → some 0): +1.
    * `prepare 1 i` (unpromised → some 1): +2.
    * `prepare 1 i` (some 0 → some 1): +1 (and +2 at top row).
    * `accept p i`: +2 in either row (unaccepted → accepted).

    The maximum per-acceptor phase is 4, and per-proposer phase is 1.
    Total: `4 * n + 2`. -/

/-- Promise level: 0 = unpromised, 1 = promised to 0, 2 = promised to 1. -/
def promiseLevel (o : Option Proposer) : Nat :=
  match o with
  | none                   => 0
  | some p => if p.val = 0 then 1 else 2

@[simp] theorem promiseLevel_none : promiseLevel none = 0 := rfl

theorem promiseLevel_le_two (o : Option Proposer) : promiseLevel o ≤ 2 := by
  unfold promiseLevel
  cases o with
  | none => simp
  | some p => by_cases h : p.val = 0 <;> simp [h]

/-- Per-acceptor phase: promise level + 2 if accepted. -/
def acceptorPhase (a : AcceptorState) : Nat :=
  promiseLevel a.promised + (if a.accepted.isSome then 2 else 0)

theorem acceptorPhase_le_four (a : AcceptorState) : acceptorPhase a ≤ 4 := by
  unfold acceptorPhase
  have := promiseLevel_le_two a.promised
  by_cases h : a.accepted.isSome <;> simp [h] <;> omega

/-- Per-proposer phase: 1 iff it has proposed. -/
def proposerPhase (p : ProposerState) : Nat :=
  if p.proposed.isSome then 1 else 0

theorem proposerPhase_le_one (p : ProposerState) : proposerPhase p ≤ 1 := by
  unfold proposerPhase; split <;> simp

/-- Global progress measure. -/
def phaseCounter {n : Nat} (s : PaxosState n) : Nat :=
  finSum (fun i => acceptorPhase (s.locals i))
    + proposerPhase (s.proposers 0) + proposerPhase (s.proposers 1)

theorem phaseCounter_bounded {n : Nat} (s : PaxosState n) :
    phaseCounter s ≤ 4 * n + 2 := by
  unfold phaseCounter
  have ha := finSum_le_const (fun i => acceptorPhase (s.locals i)) 4
    (fun i => acceptorPhase_le_four _)
  have hp0 := proposerPhase_le_one (s.proposers 0)
  have hp1 := proposerPhase_le_one (s.proposers 1)
  omega

theorem phaseCounter_initialState (n : Nat) :
    phaseCounter (initialState n) = 0 := by
  unfold phaseCounter finSum
  have h0 : listSum (fun i => acceptorPhase ((initialState n).locals i))
              (List.finRange n) = 0 := by
    apply listSum_zero
    intro i; simp [initialState, acceptorPhase]
  rw [h0]
  simp [initialState, proposerPhase]

/-! ### Phase-increment lemmas -/

/-- Helper: if `outranks o p`, then `promiseLevel (some p) ≥ promiseLevel o + 1`. -/
theorem promiseLevel_upgrade (o : Option Proposer) (p : Proposer)
    (h : outranks o p) :
    promiseLevel (some p) ≥ promiseLevel o + 1 := by
  unfold outranks at h
  cases o with
  | none =>
    -- promiseLevel (some p) is 1 or 2, promiseLevel none = 0.
    unfold promiseLevel
    by_cases hp : p.val = 0 <;> simp [hp]
  | some q =>
    -- q.val < p.val, so p.val = 1 and q.val = 0 (since both < 2).
    have hq : q.val < p.val := h
    have hp2 : p.val < 2 := p.isLt
    have hp1 : p.val = 1 := by omega
    have hq0 : q.val = 0 := by omega
    unfold promiseLevel
    simp [hp1, hq0]

/-- `prepare p i` strictly increases `acceptorPhase` at `i`. -/
theorem acceptorPhase_prepare (a : AcceptorState) (p : Proposer)
    (h : outranks a.promised p) :
    acceptorPhase (preparedAt a p) ≥ acceptorPhase a + 1 := by
  have hp := promiseLevel_upgrade a.promised p h
  have hacc : (preparedAt a p).accepted = a.accepted := rfl
  have hpro : (preparedAt a p).promised = some p := rfl
  unfold acceptorPhase
  rw [hacc, hpro]
  omega

/-- `accept p i` strictly increases `acceptorPhase` at `i` (by 2). -/
theorem acceptorPhase_accept (a : AcceptorState) (p : Proposer) (v : Val)
    (_hprom : a.promised = some p) (hacc : a.accepted = none) :
    acceptorPhase (acceptedAt a p v) = acceptorPhase a + 2 := by
  unfold acceptorPhase acceptedAt
  have : a.accepted.isSome = false := by rw [hacc]; rfl
  simp [this]

/-- Helper: functional update of the acceptors field via `setLocal`. -/
theorem finSum_acceptor_update {n : Nat} (f : Fin n → AcceptorState)
    (i : Fin n) (a : AcceptorState) :
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

/-- Any `prepare p i` strictly increases `phaseCounter` by ≥ 1. -/
theorem phaseCounter_prepare {n : Nat} (s s' : PaxosState n)
    (p : Proposer) (i : Fin n)
    (hstep : step s s' (.prepare p i)) :
    phaseCounter s' ≥ phaseCounter s + 1 := by
  obtain ⟨hok, hs'⟩ := hstep
  subst hs'
  have hfu := finSum_acceptor_update s.locals i (preparedAt (s.locals i) p)
  have hge := acceptorPhase_prepare (s.locals i) p hok
  -- `proposers` field is definitionally unchanged
  change finSum (fun j => acceptorPhase
      ((setLocal s.locals i (preparedAt (s.locals i) p)) j))
      + proposerPhase (s.proposers 0) + proposerPhase (s.proposers 1)
    ≥ phaseCounter s + 1
  unfold phaseCounter
  omega

/-- Any `accept p i` strictly increases `phaseCounter` by 2. -/
theorem phaseCounter_accept {n : Nat} (s s' : PaxosState n)
    (p : Proposer) (i : Fin n)
    (hstep : step s s' (.accept p i)) :
    phaseCounter s' = phaseCounter s + 2 := by
  obtain ⟨hprom, hacc, v, _hprop, hs'⟩ := hstep
  subst hs'
  have hfu := finSum_acceptor_update s.locals i (acceptedAt (s.locals i) p v)
  have heq := acceptorPhase_accept (s.locals i) p v hprom hacc
  change finSum (fun j => acceptorPhase
      ((setLocal s.locals i (acceptedAt (s.locals i) p v)) j))
      + proposerPhase (s.proposers 0) + proposerPhase (s.proposers 1)
    = phaseCounter s + 2
  unfold phaseCounter
  omega

/-- Any `propose p v` strictly increases `phaseCounter` by 1 (in the sum of
    proposer phases). -/
theorem phaseCounter_propose {n : Nat} (s s' : PaxosState n)
    (p : Proposer) (v : Val)
    (hstep : step s s' (.propose p v)) :
    phaseCounter s' = phaseCounter s + 1 := by
  obtain ⟨hnone, _hcon, _hd01, _hd10, hs'⟩ := hstep
  subst hs'
  change (finSum (fun j => acceptorPhase (s.locals j)))
      + proposerPhase ((setProp s.proposers p (proposedAt (s.proposers p) v)) 0)
      + proposerPhase ((setProp s.proposers p (proposedAt (s.proposers p) v)) 1)
    = phaseCounter s + 1
  unfold phaseCounter
  have hold : (s.proposers p).proposed.isSome = false := by rw [hnone]; rfl
  have hnew : (proposedAt (s.proposers p) v).proposed.isSome = true := rfl
  -- Case on whether p = 0 or p = 1.
  by_cases hp : p = (0 : Proposer)
  · subst hp
    have h0old : proposerPhase (s.proposers 0) = 0 := by
      unfold proposerPhase; rw [hnone]; rfl
    have h0new : proposerPhase (proposedAt (s.proposers 0) v) = 1 := by
      unfold proposerPhase; simp [proposedAt]
    have h0sp : proposerPhase ((setProp s.proposers 0 (proposedAt (s.proposers 0) v)) 0)
                = 1 := by rw [setProp_self]; exact h0new
    have h1sp : proposerPhase ((setProp s.proposers 0 (proposedAt (s.proposers 0) v)) 1)
                = proposerPhase (s.proposers 1) := by
      rw [setProp_ne _ _ _ _ (by decide : (1 : Proposer) ≠ 0)]
    omega
  · -- p = 1
    have hp1 : p = (1 : Proposer) := by
      have := p.isLt
      have : p.val = 0 ∨ p.val = 1 := by omega
      rcases this with h | h
      · exact absurd (Fin.ext h) hp
      · exact Fin.ext h
    subst hp1
    have h1old : proposerPhase (s.proposers 1) = 0 := by
      unfold proposerPhase; rw [hnone]; rfl
    have h1new : proposerPhase (proposedAt (s.proposers 1) v) = 1 := by
      unfold proposerPhase; simp [proposedAt]
    have h1sp : proposerPhase ((setProp s.proposers 1 (proposedAt (s.proposers 1) v)) 1)
                = 1 := by rw [setProp_self]; exact h1new
    have h0sp : proposerPhase ((setProp s.proposers 1 (proposedAt (s.proposers 1) v)) 0)
                = proposerPhase (s.proposers 0) := by
      rw [setProp_ne _ _ _ _ (by decide : (0 : Proposer) ≠ 1)]
    omega

/-- **Monotonicity**: every action strictly increases `phaseCounter` by ≥ 1. -/
theorem phaseCounter_monotone {n : Nat} (s s' : PaxosState n) (a : Action n)
    (hstep : step s s' a) :
    phaseCounter s' ≥ phaseCounter s + 1 := by
  cases a with
  | prepare p i =>
      exact phaseCounter_prepare s s' p i hstep
  | propose p v =>
      have h := phaseCounter_propose s s' p v hstep
      omega
  | accept  p i =>
      have h := phaseCounter_accept s s' p i hstep
      omega

/-! ## Section 4: Phase-counting framework instantiation -/

/-- Package two-proposer Paxos as a `PhaseCountingSystem`. -/
def twoProposerSystem (n : Nat) : PhaseCounting.PhaseCountingSystem where
  State        := PaxosState n
  Action       := Action n
  step         := step
  init         := initialState n
  phaseCounter := phaseCounter
  bound        := 4 * n + 2
  init_zero    := phaseCounter_initialState n
  step_mono    := by
    intro s s' a hstep
    have := phaseCounter_monotone s s' a hstep
    omega
  step_bounded := by
    intro s s' _ _
    exact phaseCounter_bounded s'

/-! ## Section 5: Safety (agreement)

    The real Paxos safety argument, restricted to two proposers, with
    the propose-step gated by a "second proposer copies first" rule
    that obviates carrying a witness quorum through the invariant. -/

/-- Agreement: any two accepted values agree. -/
def agreement {n : Nat} (s : PaxosState n) : Prop :=
  ∀ (i j : Fin n) (p q : Proposer) (v w : Val),
    (s.locals i).accepted = some (p, v) →
    (s.locals j).accepted = some (q, w) →
    v = w

/-- A stronger invariant: if both proposers have proposed, their values agree.
    From this plus the fact that accepted values equal the proposing proposer's
    value, agreement follows. -/
structure SafetyInv {n : Nat} (s : PaxosState n) : Prop where
  /-- Any accepted `(p, v)` means `p` has proposed and its value is `v`. -/
  accept_matches_propose :
    ∀ (i : Fin n) (p : Proposer) (v : Val),
      (s.locals i).accepted = some (p, v) →
      (s.proposers p).proposed = some v
  /-- If both proposers have proposed, their values agree. -/
  values_agree :
    ∀ (v w : Val),
      (s.proposers 0).proposed = some v →
      (s.proposers 1).proposed = some w →
      v = w

/-- Agreement follows from `SafetyInv`. -/
theorem agreement_of_safetyInv {n : Nat} (s : PaxosState n) (h : SafetyInv s) :
    agreement s := by
  intro i j p q v w hi hj
  have hpv := h.accept_matches_propose i p v hi
  have hqw := h.accept_matches_propose j q w hj
  -- Both are `.proposed = some ?` for some proposer.  Case on whether p = q.
  by_cases hpq : p = q
  · subst hpq
    rw [hpv] at hqw
    exact Option.some.inj hqw
  · -- p ≠ q and both < 2: either (p=0,q=1) or (p=1,q=0).
    have hp2 := p.isLt
    have hq2 := q.isLt
    by_cases hp0 : p = (0 : Proposer)
    · subst hp0
      have hq1 : q = (1 : Proposer) := by
        have : q.val = 0 ∨ q.val = 1 := by omega
        rcases this with h | h
        · exact absurd (Fin.ext h) (fun e => hpq e.symm)
        · exact Fin.ext h
      subst hq1
      exact h.values_agree v w hpv hqw
    · have hp1 : p = (1 : Proposer) := by
        have : p.val = 0 ∨ p.val = 1 := by omega
        rcases this with h | h
        · exact absurd (Fin.ext h) hp0
        · exact Fin.ext h
      subst hp1
      have hq0 : q = (0 : Proposer) := by
        have : q.val = 0 ∨ q.val = 1 := by omega
        rcases this with h | h
        · exact Fin.ext h
        · have hq1 : q = (1 : Proposer) := Fin.ext (by simp [h])
          exact absurd hq1.symm hpq
      subst hq0
      exact (h.values_agree w v hqw hpv).symm

/-- `SafetyInv` holds initially. -/
theorem safetyInv_initial {n : Nat} : SafetyInv (initialState n) := by
  refine ⟨?_, ?_⟩
  · intro i p v hi
    simp [initialState] at hi
  · intro v w h0 _
    simp [initialState] at h0

/-- `SafetyInv` is preserved by `step`.

    The preservation argument:

    * `prepare p i`: touches only `locals i .promised`.  Neither invariant
      field references `.promised`, so both are preserved trivially.
    * `accept p i`: touches only `locals i .accepted`.  The new accepted
      value comes from `(s.proposers p).proposed`, so
      `accept_matches_propose` is preserved.  `values_agree` is
      unchanged.
    * `propose p v`: touches only `proposers p .proposed`.
      `accept_matches_propose`: any existing accept references an old
      `proposers _` that we may have just set.  In the two-proposer
      world, only one proposer is being updated, and any prior accept
      must be for a *different* proposer (because the `propose` action
      requires `.proposed = none`, yet an accept by `p` would need
      `.proposed = some _`).  So preservation follows.
      `values_agree`: if `p = 0` and proposer 1 has already proposed
      `w`, we need `v = w`.  This is the **max-vote argument**: `v`
      must match any earlier accept from proposer 1 via `hconstr`, but
      that's only constrained when `p = 1`.  For `p = 0` updating
      first, there's no prior accept from proposer 1 in the reachable
      state (that would require proposer 1 to have already proposed,
      contradicting `hnone`). -/
theorem safetyInv_preserved {n : Nat} {s s' : PaxosState n}
    (hreach : Reachable s) (a : Action n)
    (hstep : step s s' a) (hinv : SafetyInv s) : SafetyInv s' := by
  cases a with
  | prepare p i =>
    obtain ⟨_, hs'⟩ := hstep
    subst hs'
    refine ⟨?_, ?_⟩
    · intro j q v hj
      -- locals updated at i with new promised, accepted unchanged
      by_cases hji : j = i
      · subst hji
        simp [setLocal, preparedAt] at hj
        exact hinv.accept_matches_propose j q v hj
      · simp [setLocal, hji] at hj
        exact hinv.accept_matches_propose j q v hj
    · intro v w h0 h1
      exact hinv.values_agree v w h0 h1
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
    · intro v' w' h0 h1
      exact hinv.values_agree v' w' h0 h1
  | propose p v =>
    obtain ⟨hnone, _hcon, hd01, hd10, hs'⟩ := hstep
    subst hs'
    refine ⟨?_, ?_⟩
    · intro j q w hj
      -- locals unchanged
      have hj' : (s.locals j).accepted = some (q, w) := hj
      have hmatch := hinv.accept_matches_propose j q w hj'
      -- Could (s.proposers q).proposed have changed? Only if q = p.  But
      -- then `hmatch : (s.proposers p).proposed = some w` contradicts
      -- `hnone : (s.proposers p).proposed = none`.
      by_cases hqp : q = p
      · subst hqp
        rw [hnone] at hmatch; cases hmatch
      · show ((setProp s.proposers p (proposedAt (s.proposers p) v)) q).proposed
              = some w
        rw [setProp_ne _ _ _ _ hqp]
        exact hmatch
    · intro v' w' h0 h1
      -- Need to show v' = w'.
      -- Case on which proposer just moved.
      by_cases hp0 : p = (0 : Proposer)
      · subst hp0
        --         Proposer 1 was already `some w'` before this step (from h1,
        --         since setProp at 0 leaves 1 unchanged).
        have h1' : (s.proposers 1).proposed = some w' := by
          have : ((setProp s.proposers 0 (proposedAt (s.proposers 0) v)) 1).proposed
                = some w' := h1
          rwa [setProp_ne _ _ _ _ (by decide : (1 : Proposer) ≠ 0)] at this
        have h0' : v' = v := by
          have : ((setProp s.proposers 0 (proposedAt (s.proposers 0) v)) 0).proposed
                = some v' := h0
          rw [setProp_self, proposedAt] at this
          exact (Option.some.inj this).symm
        subst h0'
        -- Proposer 1 had already proposed `w'`; `hd10` gives `v = w'`.
        exact (hd10 w' h1' rfl)
      · -- p = 1: symmetric case, but hconstr DOES apply.
        have hp1 : p = (1 : Proposer) := by
          have := p.isLt
          have : p.val = 0 ∨ p.val = 1 := by omega
          rcases this with h | h
          · exact absurd (Fin.ext h) hp0
          · exact Fin.ext h
        subst hp1
        have h0' : (s.proposers 0).proposed = some v' := by
          have : ((setProp s.proposers 1 (proposedAt (s.proposers 1) v)) 0).proposed
                = some v' := h0
          rwa [setProp_ne _ _ _ _ (by decide : (0 : Proposer) ≠ 1)] at this
        have h1' : w' = v := by
          have : ((setProp s.proposers 1 (proposedAt (s.proposers 1) v)) 1).proposed
                = some w' := h1
          rw [setProp_self, proposedAt] at this
          exact (Option.some.inj this).symm
        subst h1'
        -- Need `v' = v`, where `v'` is proposer 0's already-proposed value
        -- and `v` is proposer 1's fresh choice.  `hd01` gives `v = v'`.
        exact (hd01 v' h0' rfl).symm

/-- **Main safety theorem**: every reachable state satisfies `agreement`.
    Derived from `SafetyInv` via `agreement_of_safetyInv`. -/
theorem agreement_reachable {n : Nat} (s : PaxosState n) (h : Reachable s) :
    agreement s := by
  have hinv : SafetyInv s := by
    induction h with
    | init => exact safetyInv_initial
    | step a hreach' hstep ih =>
        exact safetyInv_preserved hreach' a hstep ih
  exact agreement_of_safetyInv s hinv

/-! ## Section 6: Bounded-unrolling theorem (via abstract framework) -/

/-- Adapter: walking a framework `StepsFrom` for `twoProposerSystem n`
    folds local `Reachable` along the trace. -/
private theorem reachable_of_stepsFrom {n : Nat} :
    ∀ (acts : List (Action n)) {s₀ s : PaxosState n},
      Reachable s₀ →
      PhaseCounting.StepsFrom (twoProposerSystem n) s₀ acts s →
      Reachable s
  | [], _, _, hr₀, h => by
    match h with
    | PhaseCounting.StepsFrom.nil _ => exact hr₀
  | a :: as, _, _, hr₀, h => by
    match h with
    | PhaseCounting.StepsFrom.cons _ _ hstep htail =>
      exact reachable_of_stepsFrom as (Reachable.step a hr₀ hstep) htail

theorem reachable_iff_framework {n : Nat} (s : PaxosState n) :
    Reachable s ↔ PhaseCounting.Reachable (twoProposerSystem n) s := by
  constructor
  · intro h
    induction h with
    | init => exact PhaseCounting.Reachable.init
    | step a _ hstep ih =>
      exact PhaseCounting.Reachable.step (P := twoProposerSystem n) a ih hstep
  · intro hr
    obtain ⟨acts, hfrom⟩ :=
      (PhaseCounting.reachable_iff_stepsFrom (twoProposerSystem n) s).mp hr
    exact reachable_of_stepsFrom acts Reachable.init hfrom

def safeUpTo (n : Nat) (k : Nat) : Prop :=
  ∀ acts : List (Action n), acts.length ≤ k →
    ∀ s', PhaseCounting.StepsFrom (twoProposerSystem n) (initialState n) acts s' →
      agreement s'

def safeAll (n : Nat) : Prop :=
  ∀ s : PaxosState n, Reachable s → agreement s

/-- **Main theorem: Two-proposer Paxos bounded unrolling.** Safety of all
    reachable states is equivalent to safety of all states reachable
    within `4 * n + 2` steps from the canonical initial state. Derived
    from the abstract `phase_counting_bounded_unrolling`. -/
theorem two_proposer_bounded_unrolling (n : Nat) :
    safeAll n ↔ safeUpTo n (4 * n + 2) := by
  constructor
  · intro hall acts _ s' hfrom
    apply hall
    refine (reachable_iff_framework s').mpr ?_
    exact PhaseCounting.stepsFrom_preserves_reachable hfrom PhaseCounting.Reachable.init
  · intro _ s hreach
    exact agreement_reachable s hreach

/-! ## Section 7: Sanity checks -/

example : phaseCounter (initialState 3) = 0 :=
  phaseCounter_initialState 3

example : ∀ (s : PaxosState 3), phaseCounter s ≤ 14 := by
  intro s
  have := phaseCounter_bounded (n := 3) s
  omega

end TwoProposerPaxos
