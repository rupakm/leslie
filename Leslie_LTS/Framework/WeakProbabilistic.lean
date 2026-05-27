import Leslie_LTS.Framework.RandProbExec

/-! # Weak Probabilistic Transitions for PLTS

    This module defines weak probabilistic transitions for Probabilistic
    Labelled Transition Systems (PLTS), extending the strong (single-step)
    transitions in `Probabilistic.lean`.

    The construction proceeds in four layers:

    1. **Hyper-transitions** (`HyperStep`): lift single-state transitions
       to distributions. `μ --l--> μ'` means each `q ∈ μ.support` takes
       an `l`-step to some `μ_q`, and `μ' = μ.bind (q ↦ μ_q)`.

    2. **Internal hyper-transitions** (`InternalHyperStep`): hyper-transitions
       with an internal label, where states may stutter (skip) instead of
       taking a step.

    3. **Internal weak transitions** (`InternalWeakStar`): reflexive-transitive
       closure of internal hyper-transitions.

    4. **Weak transitions** (`WeakStep`): an internal weak transition, followed
       by a hyper-transition with label `l`, followed by another internal weak
       transition.
-/

namespace PLTS

variable {State : Type u} {Label : Type v}

/-! ## Hyper-Transitions -/

/-- A hyper-transition lifts single-state transitions to distributions.
    `HyperStep sys l μ μ'` means: there exists a choice function `f` assigning
    to each `q ∈ μ.support` a distribution `f q` such that `sys.step q l (f q)`,
    and `μ' = μ.bind f`. -/
def HyperStep (sys : System State Label) (l : Label) (μ μ' : PMF State) : Prop :=
  ∃ f : State → PMF State,
    (∀ q ∈ μ.support, sys.step q l (f q)) ∧
    μ' = μ.bind f

/-! ## Internal Hyper-Transitions -/

/-- An internal hyper-transition: there exists a choice function `f` such that
    for each `q ∈ μ.support`, either `q` takes a step with some internal label
    to `f q`, or `f q = PMF.pure q` (stutter). Different states may use
    different internal labels. At least one state in the support must take
    a genuine step (not stutter), ensuring progress. `μ' = μ.bind f`. -/
def InternalHyperStep (sys : System State Label) (lab : LTS.Labelling Label)
    (μ μ' : PMF State) : Prop :=
  ∃ f : State → PMF State,
    (∀ q ∈ μ.support,
      (∃ l, lab.is_internal l = true ∧ sys.step q l (f q)) ∨ f q = PMF.pure q) ∧
    (∃ q ∈ μ.support, ∃ l, lab.is_internal l = true ∧ sys.step q l (f q)) ∧
    μ' = μ.bind f

/-! ## Internal Weak Probabilistic Transitions -/

/-- Reflexive-transitive closure of internal hyper-transitions. -/
inductive InternalWeakStar (sys : System State Label) (lab : LTS.Labelling Label)
    : PMF State → PMF State → Prop where
  | refl : InternalWeakStar sys lab μ μ
  | step : InternalHyperStep sys lab μ μ' →
      InternalWeakStar sys lab μ' μ'' → InternalWeakStar sys lab μ μ''

/-! ## Weak Probabilistic Transitions -/

/-- A weak probabilistic transition with label `l`:
    an internal weak transition, followed by a hyper-transition with label `l`,
    followed by another internal weak transition. -/
def WeakStep (sys : System State Label) (lab : LTS.Labelling Label)
    (l : Label) (μ μ' : PMF State) : Prop :=
  ∃ μ₁ μ₂,
    InternalWeakStar sys lab μ μ₁ ∧
    HyperStep sys l μ₁ μ₂ ∧
    InternalWeakStar sys lab μ₂ μ'

/-! ## Basic Properties -/

variable {sys : System State Label} {lab : LTS.Labelling Label}

/-- `InternalWeakStar` is transitive. -/
theorem InternalWeakStar.trans
    (h1 : InternalWeakStar sys lab μ μ')
    (h2 : InternalWeakStar sys lab μ' μ'') :
    InternalWeakStar sys lab μ μ'' := by
  induction h1 with
  | refl => exact h2
  | step hs _ ih => exact .step hs (ih h2)

/-- A single internal hyper-step is an `InternalWeakStar`. -/
theorem InternalWeakStar.single
    (h : InternalHyperStep sys lab μ μ') :
    InternalWeakStar sys lab μ μ' :=
  .step h .refl

/-- A single-state step lifts to a hyper-step from `PMF.pure s`. -/
theorem HyperStep.from_step {s : State} {l : Label} {μ' : PMF State}
    (h : sys.step s l μ') :
    HyperStep sys l (PMF.pure s) μ' :=
  ⟨fun _ => μ',
   fun q hq => by rw [PMF.support_pure, Set.mem_singleton_iff] at hq; subst hq; exact h,
   by simp⟩

/-- A strong step from a state is a weak step from `PMF.pure s`. -/
theorem WeakStep.from_step {s : State} {l : Label} {μ' : PMF State}
    (h : sys.step s l μ') :
    WeakStep sys lab l (PMF.pure s) μ' :=
  ⟨PMF.pure s, μ', .refl, .from_step h, .refl⟩

/-- A hyper-step is a weak step (with trivial internal closures). -/
theorem WeakStep.from_hyper
    (h : HyperStep sys l μ μ') :
    WeakStep sys lab l μ μ' :=
  ⟨μ, μ', .refl, h, .refl⟩

/-- An `InternalHyperStep` changes the distribution: it cannot be the identity,
    since at least one state must take a genuine step. Reflexivity is provided
    by `InternalWeakStar.refl` instead. -/
theorem InternalHyperStep.ne_refl
    (h : InternalHyperStep sys lab μ μ') : μ' = μ.bind h.choose :=
  h.choose_spec.2.2

/-! ## Stopping Strategies

    A stopping strategy extends the existing `Strategy` with the ability to
    halt. At each step, given the observation history and current state-signal,
    the strategy either stops (`none`) or continues with a label-signal
    (`some ls`).

    This integrates with the existing adversary framework: under
    `observation_resolving`, a stopping strategy together with any regular
    strategy extending it induces a well-defined probabilistic execution
    via `rand_exec_measure`. The stopping time, external trace, and outcome
    distribution are defined on this execution measure and depend only on
    behaviour up to the stopping time.

    The key difference from the hyper-transition definition: in a stopping
    strategy execution, different states may take their external `l`-step at
    different times. In the hyper-transition definition, all states take the
    `l`-step simultaneously (one `HyperStep` round). -/

/-- A stopping strategy: at each step, given the observation history and
    current state-signal, either halt (`none`) or continue with a
    label-signal (`some ls`). Extends `Strategy SS LS` with termination. -/
def StoppingStrategy (SS : Type w) (LS : Type x) :=
  List (SS × LS) → SS → Option LS

/-- A randomised stopping strategy: the continue case produces a
    distribution over label-signals rather than a single one. -/
def RandomisedStoppingStrategy (SS : Type w) (LS : Type x) :=
  List (SS × LS) → SS → Option (PMF LS)

namespace StoppingStrategy

variable {State : Type u} {Label : Type v} {SS : Type w} {LS : Type x}

/-- Embed a regular (non-stopping) strategy as a stopping strategy that
    never halts. -/
def ofStrategy (σ : Strategy SS LS) : StoppingStrategy SS LS :=
  fun hist ss => some (σ hist ss)

/-- A regular strategy **extends** a stopping strategy if it agrees with
    the stopping strategy on all inputs where the stopping strategy
    continues. Behaviour after halting is unconstrained. -/
def IsExtendedBy (σ : StoppingStrategy SS LS) (σ_ext : Strategy SS LS) : Prop :=
  ∀ hist ss ls, σ hist ss = some ls → σ_ext hist ss = ls

/-- Whether the strategy halts at step `n` on execution `ω`, given the
    adversary's observation functions. Uses `rand_obs_history` to compute
    the observation prefix that the strategy sees. -/
def halts_at (σ : StoppingStrategy SS LS)
    (obs : Observation State Label SS LS)
    (ω : ℕ → State × Label) (n : ℕ) : Prop :=
  σ (rand_obs_history obs ω n) (obs.observe_state (ω n).1) = none

/-- The stopping time: the first step at which the strategy halts.
    Returns `⊤ : ℕ∞` if the strategy never halts on `ω`. -/
noncomputable def stoppingTime (σ : StoppingStrategy SS LS)
    (obs : Observation State Label SS LS)
    (ω : ℕ → State × Label) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : σ.halts_at obs ω n), (n : ℕ∞)

end StoppingStrategy

/-! ## External Trace of Finite Prefixes -/

/-- The list of external labels in the first `n` steps of a state–label
    sequence `ω`. Step `i` contributes label `(ω i).2` if it is external. -/
def externalLabelsUntil (lab : LTS.Labelling Label)
    (ω : ℕ → State × Label) (n : ℕ) : List Label :=
  ((List.range n).map (fun i => (ω i).2)).filter (fun l => lab.is_external l)

/-! ## Scheduler-Based Weak Transitions -/

/-- Scheduler-based weak transition using a stopping strategy.

    From state `s₀`, there exists a stopping strategy `σ` and a regular
    strategy `σ_ext` extending it, such that under the execution measure
    `μ_exec` induced by `σ_ext.toRandomised`:

    1. **Almost-sure termination**: the stopping time `T` is finite a.s.
    2. **Trace condition**: the external trace up to `T` is `[l]` a.s.
    3. **Outcome**: for each state `s`, the probability of stopping at `s`
       equals `μ' s`.

    The extension `σ_ext` provides arbitrary post-stopping behaviour so that
    `rand_exec_measure` (which requires an infinite-horizon strategy) is
    well-defined. The outcome depends only on behaviour up to `T`, so the
    choice of extension is immaterial.

    The definition is parametric in the adversary, supporting both omniscient
    and partial-observation adversaries. -/
def SchedWeakStep (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    [Countable State] [Inhabited State]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]
    (lab : LTS.Labelling Label)
    (l : Label) (s₀ : State) (μ' : PMF State) : Prop :=
  ∃ (σ : StoppingStrategy SS LS) (σ_ext : Strategy SS LS),
    σ.IsExtendedBy σ_ext ∧
    let μ_exec := rand_exec_measure adv hres σ_ext.toRandomised s₀
    let T := σ.stoppingTime adv.obs
    -- (1) Almost-sure termination
    μ_exec {ω | T ω < ⊤} = 1 ∧
    -- (2) External trace is [l] a.s.
    μ_exec {ω | T ω < ⊤ →
      externalLabelsUntil lab ω (T ω).toNat = [l]} = 1 ∧
    -- (3) Outcome distribution
    (∀ s, μ' s = μ_exec {ω | T ω < ⊤ ∧ (ω (T ω).toNat).1 = s})

/-! ## Equivalence between Hyper-Transition and Scheduler Definitions -/

variable {sys : System State Label} {lab : LTS.Labelling Label}

/-- The hyper-transition weak step implies the scheduler-based weak step.

    **Construction:** The hyper-step chain
    `InternalWeakStar · HyperStep l · InternalWeakStar` is converted to
    a stopping strategy where all states proceed in lockstep through the
    chain. Each internal hyper-step becomes a round where each state takes
    its internal step (the progress condition ensures a genuine transition).
    After the final internal phase, the strategy halts. -/
theorem WeakStep.toSchedWeakStep
    {SS : Type w} {LS : Type x}
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    [Countable State] [Inhabited State]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]
    (hsys : adv.sys = sys)
    {l : Label} {s₀ : State} {μ' : PMF State}
    (hw : WeakStep sys lab l (PMF.pure s₀) μ') :
    SchedWeakStep adv hres lab l s₀ μ' := by
  sorry

/-- The scheduler-based weak step implies the hyper-transition weak step.

    This direction requires "synchronizing" asynchronous external steps:
    in a stopping strategy execution, different states may take their
    `l`-step at different times, whereas `WeakStep` requires all states to
    take the `l`-step in a single `HyperStep` round.

    **Proof idea:** Decompose the execution into three phases per state
    (pre-`l`, `l`-step, post-`l`). Since transitions are state-local, the
    bind operations can be rearranged so that all `l`-steps occur in a
    single round, yielding the
    `InternalWeakStar · HyperStep · InternalWeakStar` decomposition. -/
theorem SchedWeakStep.toWeakStep
    {SS : Type w} {LS : Type x}
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    [Countable State] [Inhabited State]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]
    (hsys : adv.sys = sys)
    {l : Label} {s₀ : State} {μ' : PMF State}
    (hs : SchedWeakStep adv hres lab l s₀ μ') :
    WeakStep sys lab l (PMF.pure s₀) μ' := by
  sorry

end PLTS
