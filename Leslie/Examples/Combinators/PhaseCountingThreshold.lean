import Batteries.Data.List.Lemmas

/-! # Phase-Counting Threshold Protocols (abstract framework)

    A protocol-agnostic bounded-unrolling skeleton for **phase-counting**
    transition systems: systems carrying a `Nat`-valued phase counter that

      1. starts at `0` in the initial state,
      2. is strictly monotonic along every step, and
      3. is bounded by some `bound : Nat` (possibly depending on
         protocol parameters like `n`, `m`).

    From these three facts we get, for free, the "bounded unrolling"
    equivalence: safety of all reachable states is equivalent to safety
    of all traces of length `≤ bound` starting from the initial state.

    This is the phase-counting analogue of
    `Leslie/Examples/Combinators/PhaseAbsorbingThreshold.lean`, which
    handles phase-**absorbing** binary threshold protocols. Both modules
    share the "bounded depth suffices" pattern; they differ only in how
    the diameter bound is obtained (a safety-diameter fixpoint argument
    there, a monotone counter argument here).

    ### Concrete instances

    The three Paxos files on branch `feat/paxos-bounded-unrolling` are
    all phase-counting. Each instantiates this framework locally:

      * `SingleProposerPaxos.lean` — counter ≤ `2 * n`
      * `TwoProposerPaxos.lean`    — counter ≤ `4 * n + 2`
      * `MProposerPaxos.lean`      — counter ≤ `2 * m * n + n + m`

    Core Lean 4 + Batteries only; no Mathlib.
-/

namespace PhaseCounting

/-! ## Section 1: Abstract system -/

/-- A phase-counting transition system: carrier type `State`, action type
    `Action`, step relation, distinguished initial state, and a monotone
    bounded `phaseCounter`. The three side conditions are:

      * `init_zero`       — the counter starts at `0`,
      * `step_mono`       — every step strictly increases the counter
                            (in fact by at least one; we only need `<`),
      * `step_bounded`    — every step stays within `bound`; combined
                            with `init_zero` this gives reachability-wide
                            boundedness.

    The side conditions are quoted in "step-local" form (no reference to
    `Reachable`) so the structure is non-recursive. -/
structure PhaseCountingSystem where
  State        : Type
  Action       : Type
  step         : State → State → Action → Prop
  init         : State
  phaseCounter : State → Nat
  bound        : Nat
  init_zero    : phaseCounter init = 0
  step_mono    : ∀ s s' a, step s s' a → phaseCounter s < phaseCounter s'
  step_bounded : ∀ s s' a, step s s' a → phaseCounter s' ≤ bound

/-! ## Section 2: Reachability and stepped traces -/

variable (P : PhaseCountingSystem)

/-- Reachable states of `P`, built by transitive closure from `P.init`. -/
inductive Reachable : P.State → Prop where
  | init : Reachable P.init
  | step : ∀ {s s' : P.State} (a : P.Action),
             Reachable s → P.step s s' a → Reachable s'

/-- Multi-step traces with an explicit action list. `StepsFrom s₀ acts s`
    means the trace `s₀ —[acts]→ s` exists. -/
inductive StepsFrom : P.State → List P.Action → P.State → Prop where
  | nil  : ∀ s, StepsFrom s [] s
  | cons : ∀ {s s' s'' : P.State} (a : P.Action) (acts : List P.Action),
             P.step s s' a → StepsFrom s' acts s'' → StepsFrom s (a :: acts) s''

/-- `StepsFrom` is closed under right-append of a single step. -/
theorem StepsFrom.snoc {P : PhaseCountingSystem}
    {p q r : P.State} {as : List P.Action}
    (b : P.Action) (hpq : StepsFrom P p as q) (hqr : P.step q r b) :
    StepsFrom P p (as ++ [b]) r := by
  induction hpq with
  | nil s => exact StepsFrom.cons b [] hqr (StepsFrom.nil _)
  | @cons s₁ s₂ s₃ x xs hx _ ih =>
    exact StepsFrom.cons x (xs ++ [b]) hx (ih hqr)

/-- Reachability is closed under `StepsFrom`: if we reach `s₀` and there
    is a trace `s₀ —[acts]→ s`, then `s` is reachable too. -/
theorem stepsFrom_preserves_reachable {P : PhaseCountingSystem}
    {s₀ s : P.State} {acts : List P.Action}
    (h : StepsFrom P s₀ acts s) (h₀ : Reachable P s₀) : Reachable P s := by
  induction h with
  | nil s => exact h₀
  | @cons s₁ s₂ s₃ a acts hstep _ ih =>
    exact ih (Reachable.step a h₀ hstep)

/-- Equivalence: `s` is reachable iff there is a trace from the initial
    state reaching it. -/
theorem reachable_iff_stepsFrom (P : PhaseCountingSystem) (s : P.State) :
    Reachable P s ↔ ∃ acts, StepsFrom P P.init acts s := by
  constructor
  · intro h
    induction h with
    | init => exact ⟨[], StepsFrom.nil _⟩
    | step a _ hstep ih =>
      obtain ⟨acts, hfrom⟩ := ih
      exact ⟨acts ++ [a], StepsFrom.snoc a hfrom hstep⟩
  · rintro ⟨acts, hfrom⟩
    exact stepsFrom_preserves_reachable hfrom Reachable.init

/-! ## Section 3: Counter monotonicity along traces -/

/-- Along any trace, the phase counter increases by **at least** the
    trace length. Combined with the bound, this caps trace length. -/
theorem phaseCounter_after_steps {P : PhaseCountingSystem}
    {s s'' : P.State} {acts : List P.Action}
    (hs : StepsFrom P s acts s'') :
    P.phaseCounter s + acts.length ≤ P.phaseCounter s'' := by
  induction hs with
  | nil s => simp
  | @cons s₁ s₂ s₃ a acts hstep _ ih =>
    have h1 : P.phaseCounter s₁ < P.phaseCounter s₂ := P.step_mono _ _ _ hstep
    have h2 : P.phaseCounter s₁ + 1 ≤ P.phaseCounter s₂ := h1
    simp [List.length_cons]
    omega

/-- Auxiliary: if we start at a state whose counter is `≤ bound` and
    take any number of steps, the resulting state's counter stays `≤ bound`.
    (Trivially true for zero steps; for non-zero, use `step_bounded` on
    the first step and recurse.) -/
theorem stepsFrom_tail_bounded {P : PhaseCountingSystem}
    {s s' : P.State} {acts : List P.Action}
    (h : StepsFrom P s acts s') (hs : P.phaseCounter s ≤ P.bound) :
    P.phaseCounter s' ≤ P.bound := by
  induction h with
  | nil _ => exact hs
  | @cons s₁ s₂ s₃ _a _acts hstep _ ih =>
    exact ih (P.step_bounded _ _ _ hstep)

/-- Any trace reaching a state from the initial state has bounded length. -/
theorem stepsFrom_length_bounded {P : PhaseCountingSystem}
    {s : P.State} {acts : List P.Action}
    (h : StepsFrom P P.init acts s) : acts.length ≤ P.bound := by
  have hafter : P.phaseCounter P.init + acts.length ≤ P.phaseCounter s :=
    phaseCounter_after_steps h
  have h0 : P.phaseCounter P.init = 0 := P.init_zero
  have hsb : P.phaseCounter s ≤ P.bound :=
    stepsFrom_tail_bounded h (by rw [h0]; exact Nat.zero_le _)
  omega

/-! ## Section 4: The abstract bounded-unrolling theorem -/

/-- Safety of all reachable states. -/
def safeAll (P : PhaseCountingSystem) (Safe : P.State → Prop) : Prop :=
  ∀ s, Reachable P s → Safe s

/-- Safety of all traces of length `≤ k` from the initial state. -/
def safeUpTo (P : PhaseCountingSystem) (Safe : P.State → Prop) (k : Nat) : Prop :=
  ∀ acts : List P.Action, acts.length ≤ k →
    ∀ s, StepsFrom P P.init acts s → Safe s

/-- **Phase-counting bounded-unrolling theorem.** For any safety predicate
    `Safe`, `Safe` holds at every reachable state iff it holds along every
    trace of length `≤ P.bound` starting from the initial state.

    The `→` direction is immediate from `reachable_iff_stepsFrom`. The
    `←` direction uses `stepsFrom_length_bounded` to cap the trace. -/
theorem phase_counting_bounded_unrolling (P : PhaseCountingSystem)
    (Safe : P.State → Prop) :
    safeAll P Safe ↔ safeUpTo P Safe P.bound := by
  constructor
  · intro hall acts _ s hfrom
    exact hall s ((reachable_iff_stepsFrom P s).mpr ⟨acts, hfrom⟩)
  · intro hsmall s hreach
    obtain ⟨acts, hfrom⟩ := (reachable_iff_stepsFrom P s).mp hreach
    have hlen : acts.length ≤ P.bound := stepsFrom_length_bounded hfrom
    exact hsmall acts hlen s hfrom

end PhaseCounting
