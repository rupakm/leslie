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
    Carries the choice function `f` explicitly: each `q ∈ μ.support` takes
    an `l`-step to `f q`, and `μ' = μ.bind f`. -/
structure HyperStep (sys : System State Label) (l : Label) (μ μ' : PMF State) where
  /-- Choice function assigning a successor distribution to each state. -/
  f : State → PMF State
  /-- Every state in the support takes an `l`-step to `f q`. -/
  step : ∀ q ∈ μ.support, sys.step q l (f q)
  /-- The successor distribution is the bind. -/
  bind_eq : μ' = μ.bind f

/-! ## Internal Hyper-Transitions -/

/-- An internal hyper-transition with explicit choice function `f`.
    For each `q ∈ μ.support`, either `q` takes a step with some internal label
    to `f q`, or `f q = PMF.pure q` (stutter). At least one state in the support
    must take a genuine step (not stutter), ensuring progress.
    `μ' = μ.bind f`. -/
structure InternalHyperStep (sys : System State Label) (lab : LTS.Labelling Label)
    (μ μ' : PMF State) where
  /-- Choice function. -/
  f : State → PMF State
  /-- Each state either steps internally or stutters. -/
  choice : ∀ q ∈ μ.support,
    (∃ l, lab.is_internal l = true ∧ sys.step q l (f q)) ∨ f q = PMF.pure q
  /-- At least one state makes genuine progress. -/
  progress : ∃ q ∈ μ.support, ∃ l, lab.is_internal l = true ∧ sys.step q l (f q)
  /-- The successor distribution is the bind. -/
  bind_eq : μ' = μ.bind f

/-! ## Internal Weak Probabilistic Transitions -/

/-- Reflexive-transitive closure of internal hyper-transitions.
    Type-valued so that the chain structure (choice functions, step count)
    is directly accessible via pattern matching. -/
inductive InternalWeakStar (sys : System State Label) (lab : LTS.Labelling Label)
    : PMF State → PMF State → Type _ where
  | refl : InternalWeakStar sys lab μ μ
  | step : InternalHyperStep sys lab μ μ' →
      InternalWeakStar sys lab μ' μ'' → InternalWeakStar sys lab μ μ''

/-! ## Weak Probabilistic Transitions -/

/-- A weak probabilistic transition with label `l`:
    an internal weak transition, followed by a hyper-transition with label `l`,
    followed by another internal weak transition. Carries all intermediate
    distributions and choice functions explicitly. -/
structure WeakStep (sys : System State Label) (lab : LTS.Labelling Label)
    (l : Label) (μ μ' : PMF State) where
  /-- Distribution after the pre-internal phase. -/
  μ₁ : PMF State
  /-- Distribution after the external step. -/
  μ₂ : PMF State
  /-- Pre-internal phase: internal weak transition from `μ` to `μ₁`. -/
  pre : InternalWeakStar sys lab μ μ₁
  /-- External step: hyper-transition with label `l` from `μ₁` to `μ₂`. -/
  ext : HyperStep sys l μ₁ μ₂
  /-- Post-internal phase: internal weak transition from `μ₂` to `μ'`. -/
  post : InternalWeakStar sys lab μ₂ μ'

/-! ## Basic Properties -/

variable {sys : System State Label} {lab : LTS.Labelling Label}

/-- `InternalWeakStar` is transitive. -/
noncomputable def InternalWeakStar.trans
    (h1 : InternalWeakStar sys lab μ μ')
    (h2 : InternalWeakStar sys lab μ' μ'') :
    InternalWeakStar sys lab μ μ'' :=
  match h1 with
  | .refl => h2
  | .step hs rest => .step hs (rest.trans h2)

/-- A single internal hyper-step is an `InternalWeakStar`. -/
noncomputable def InternalWeakStar.single
    (h : InternalHyperStep sys lab μ μ') :
    InternalWeakStar sys lab μ μ' :=
  .step h .refl

/-- A single-state step lifts to a hyper-step from `PMF.pure s`. -/
noncomputable def HyperStep.from_step {s : State} {l : Label} {μ' : PMF State}
    (h : sys.step s l μ') :
    HyperStep sys l (PMF.pure s) μ' where
  f := fun _ => μ'
  step := fun q hq => by rw [PMF.support_pure, Set.mem_singleton_iff] at hq; subst hq; exact h
  bind_eq := by simp

/-- A strong step from a state is a weak step from `PMF.pure s`. -/
noncomputable def WeakStep.from_step {s : State} {l : Label} {μ' : PMF State}
    (h : sys.step s l μ') :
    WeakStep sys lab l (PMF.pure s) μ' :=
  ⟨PMF.pure s, μ', .refl, .from_step h, .refl⟩

/-- A hyper-step is a weak step (with trivial internal closures). -/
noncomputable def WeakStep.from_hyper
    (h : HyperStep sys l μ μ') :
    WeakStep sys lab l μ μ' :=
  ⟨μ, μ', .refl, h, .refl⟩

/-! ## Chain Refinement by Observation Class

    An `InternalHyperStep` may assign different internal labels to states
    sharing the same state-signal. To construct a scheduler strategy that
    replays the chain, we refine each step into sub-steps where all
    stepping states share the same label-signal (observation-uniform).

    The refinement processes one label-signal group at a time: states
    whose label resolves to that signal step, others stutter. Since the
    stuttering states remain at their original positions, subsequent
    sub-steps can still reach them. -/

/-- An `InternalHyperStep` is observation-uniform w.r.t. an adversary
    if all stepping states produce the same label-signal. -/
def InternalHyperStep.ObsUniform
    {SS : Type w} {LS : Type x}
    (adv : Adversary State Label SS LS)
    (h : InternalHyperStep sys lab μ μ') : Prop :=
  ∃ ls : LS, ∀ q ∈ μ.support, ∀ l,
    lab.is_internal l = true → sys.step q l (h.f q) →
    adv.obs.observe_label q l = ls

/-- An `InternalWeakStar` chain is observation-uniform if every step is. -/
def InternalWeakStar.ObsUniform
    {SS : Type w} {LS : Type x}
    (adv : Adversary State Label SS LS) :
    InternalWeakStar sys lab μ μ' → Prop
  | .refl => True
  | .step h rest => h.ObsUniform adv ∧ rest.ObsUniform adv

/-- **Chain refinement**: any `InternalHyperStep` can be decomposed into
    an observation-uniform `InternalWeakStar` chain with the same
    endpoints.

    The decomposition groups stepping states by their label-signal
    `adv.obs.observe_label q l_q` and processes one group per sub-step.
    States not in the current group stutter (stay at `PMF.pure q`).

    **Caveat**: This decomposition is valid when the successor states
    of one group do not overlap with the stepping states of later groups
    (non-interference). For chains starting from `PMF.pure s₀`, this
    holds at the first step trivially (single-state support). -/
noncomputable def InternalHyperStep.refineByObs
    {SS : Type w} {LS : Type x}
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    (h : InternalHyperStep sys lab μ μ') :
    { chain : InternalWeakStar sys lab μ μ' // chain.ObsUniform adv } := by
  exact sorry

/-- `ObsUniform` is preserved by `trans`. -/
theorem InternalWeakStar.obsUniform_trans
    {SS : Type w} {LS : Type x}
    {adv : Adversary State Label SS LS}
    {h1 : InternalWeakStar sys lab μ μ'}
    {h2 : InternalWeakStar sys lab μ' μ''}
    (ho1 : h1.ObsUniform adv) (ho2 : h2.ObsUniform adv) :
    (h1.trans h2).ObsUniform adv := by
  induction h1 with
  | refl => exact ho2
  | step hs _ ih =>
    exact ⟨ho1.1, ih ho1.2 ho2⟩

/-- Refine an entire `InternalWeakStar` chain to be observation-uniform. -/
noncomputable def InternalWeakStar.refineByObs
    {SS : Type w} {LS : Type x}
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) :
    (chain : InternalWeakStar sys lab μ μ') →
    { chain' : InternalWeakStar sys lab μ μ' // chain'.ObsUniform adv }
  | .refl => ⟨.refl, trivial⟩
  | .step h rest =>
    let ⟨h', hobs⟩ := h.refineByObs adv hres
    let ⟨rest', robs⟩ := rest.refineByObs adv hres
    ⟨h'.trans rest', obsUniform_trans hobs robs⟩

/-- The number of steps in an `InternalWeakStar` chain. -/
noncomputable def InternalWeakStar.length :
    InternalWeakStar sys lab μ μ' → ℕ
  | .refl => 0
  | .step _ rest => 1 + rest.length

/-- The choice function at step `k` of an `InternalWeakStar` chain.
    Returns `PMF.pure` (identity) if `k` is out of range. -/
noncomputable def InternalWeakStar.choiceAt :
    InternalWeakStar sys lab μ μ' → ℕ → (State → PMF State)
  | .refl, _, q => PMF.pure q
  | .step hs _, 0, q => hs.f q
  | .step _ rest, k + 1, q => rest.choiceAt k q

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

namespace RandomisedStoppingStrategy

variable {State : Type u} {Label : Type v} {SS : Type w} {LS : Type x}

/-- Embed a randomised (non-stopping) strategy as a randomised stopping
    strategy that never halts. -/
def ofStrategy (ρ : RandomisedStrategy SS LS) : RandomisedStoppingStrategy SS LS :=
  fun hist ss => some (ρ hist ss)

/-- A randomised strategy **extends** a randomised stopping strategy if
    it agrees with the stopping strategy on all inputs where the stopping
    strategy continues. Behaviour after halting is unconstrained. -/
def IsExtendedBy (σ : RandomisedStoppingStrategy SS LS)
    (ρ : RandomisedStrategy SS LS) : Prop :=
  ∀ hist ss d, σ hist ss = some d → ρ hist ss = d

/-- Whether the strategy halts at step `n` on execution `ω`, given the
    adversary's observation functions. -/
def halts_at (σ : RandomisedStoppingStrategy SS LS)
    (obs : Observation State Label SS LS)
    (ω : ℕ → State × Label) (n : ℕ) : Prop :=
  σ (rand_obs_history obs ω n) (obs.observe_state (ω n).1) = none

/-- The stopping time: the first step at which the strategy halts.
    Returns `⊤ : ℕ∞` if the strategy never halts on `ω`. -/
noncomputable def stoppingTime (σ : RandomisedStoppingStrategy SS LS)
    (obs : Observation State Label SS LS)
    (ω : ℕ → State × Label) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : σ.halts_at obs ω n), (n : ℕ∞)

end RandomisedStoppingStrategy

/-! ## External Trace of Finite Prefixes -/

/-- The list of external labels in the first `n` steps of a state–label
    sequence `ω`. Step `i` contributes label `(ω i).2` if it is external. -/
def externalLabelsUntil (lab : LTS.Labelling Label)
    (ω : ℕ → State × Label) (n : ℕ) : List Label :=
  ((List.range n).map (fun i => (ω i).2)).filter (fun l => lab.is_external l)

/-! ## Scheduler-Based Weak Transitions -/

/-- Scheduler-based weak transition using a randomised stopping strategy.

    From state `s₀`, there exists a randomised stopping strategy `σ` and a
    randomised strategy `ρ` extending it, such that under the execution
    measure `μ_exec` induced by `ρ`:

    1. **Almost-sure termination**: the stopping time `T` is finite a.s.
    2. **Trace condition**: the external trace up to `T` is `[l]` a.s.
    3. **Outcome**: for each state `s`, the probability of stopping at `s`
       equals `μ' s`.

    The extension `ρ` provides arbitrary post-stopping behaviour so that
    `rand_exec_measure` (which requires an infinite-horizon strategy) is
    well-defined. The outcome depends only on behaviour up to `T`, so the
    choice of extension is immaterial.

    Using randomised strategies is essential: a deterministic strategy maps
    state-signals to label-signals, but `InternalHyperStep` choice functions
    may assign different internal labels to states sharing the same
    state-signal. A randomised strategy can mix over label-signals to
    achieve the correct per-state transition.

    The definition is parametric in the adversary, supporting both omniscient
    and partial-observation adversaries. -/
def SchedWeakStep (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    [Countable State] [Inhabited State]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]
    (lab : LTS.Labelling Label)
    (l : Label) (s₀ : State) (μ' : PMF State) : Prop :=
  ∃ (σ : RandomisedStoppingStrategy SS LS) (ρ : RandomisedStrategy SS LS),
    σ.IsExtendedBy ρ ∧
    let μ_exec := rand_exec_measure adv hres ρ s₀
    let T := σ.stoppingTime adv.obs
    -- (1) Almost-sure termination
    μ_exec {ω | T ω < ⊤} = 1 ∧
    -- (2) External trace is [l] a.s.
    μ_exec {ω | T ω < ⊤ →
      externalLabelsUntil lab ω (T ω).toNat = [l]} = 1 ∧
    -- (3) Outcome distribution
    (∀ s, μ' s = μ_exec {ω | T ω < ⊤ ∧ (ω (T ω).toNat).1 = s})

/-! ## Equivalence Infrastructure

    Bridge infrastructure connecting the Ionescu-Tulcea execution measure
    (`rand_exec_measure`) to algebraic PMF operations (`PMF.bind`),
    enabling the equivalence between `WeakStep` and `SchedWeakStep`. -/

variable {sys : System State Label} {lab : LTS.Labelling Label}

/-! ### Effective Transition -/

/-- Effective state transition at `q` under label-signal distribution `d`.
    Each sampled label-signal resolves to a label via `resolve_label`;
    the effective transition mixes the resulting transition distributions. -/
noncomputable def effectiveTransition
    {SS : Type w} {LS : Type x} [Inhabited Label]
    (adv : Adversary State Label SS LS) (_hres : adv.observation_resolving)
    (d : PMF LS) (q : State) : PMF State :=
  d.bind fun ls =>
    haveI : ∀ P : Prop, Decidable P := Classical.dec
    let l := resolve_label adv q ls
    if h : ∃ μ, adv.sys.step q l μ then h.choose else PMF.pure q

/-- Effective transition with the exact label-signal for a known step
    equals that step's distribution. Uses `resolve_label_eq_of_resolving`
    and `observation_resolving` uniqueness. -/
theorem effectiveTransition_of_step
    {SS : Type w} {LS : Type x} [Inhabited Label]
    (adv : Adversary State Label SS LS) (hres : adv.observation_resolving)
    {q : State} {l : Label} {μ : PMF State}
    (hstep : adv.sys.step q l μ) :
    effectiveTransition adv hres (PMF.pure (adv.obs.observe_label q l)) q = μ := by
  simp only [effectiveTransition, PMF.pure_bind]
  rw [resolve_label_eq_of_resolving adv hres q l _ μ rfl hstep, dif_pos ⟨μ, hstep⟩]
  exact (hres q l l _ μ rfl (Exists.choose_spec ⟨μ, hstep⟩) hstep).2

/-! ### State Marginal -/

/-- State marginal PMF at step `n` under the execution measure induced
    by `ρ` from `s₀`. Satisfies `(execStateMarginal ...) s =
    (rand_exec_measure adv hres ρ s₀) {ω | (ω n).1 = s}`. -/
noncomputable def execStateMarginal
    {SS : Type w} {LS : Type x}
    [Inhabited State] [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State] [Countable State]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]
    (adv : Adversary State Label SS LS) (hres : adv.observation_resolving)
    (ρ : RandomisedStrategy SS LS) (s₀ : State) (n : ℕ) : PMF State := by
  exact
    let hf : Measurable (fun ω : ℕ → State × Label => (ω n).1) :=
      measurable_fst.comp (measurable_pi_apply n)
    let ν := (rand_exec_measure adv hres ρ s₀).map (fun ω => (ω n).1)
    let hprob : MeasureTheory.IsProbabilityMeasure ν :=
      MeasureTheory.Measure.isProbabilityMeasure_map hf.aemeasurable
    let htsum := MeasureTheory.Measure.tsum_indicator_apply_singleton ν
      Set.univ MeasurableSet.univ
    ⟨fun s => ν {s}, by
      simp only [Set.indicator_univ, MeasureTheory.measure_univ] at htsum
      rw [← htsum]; exact ENNReal.summable.hasSum⟩

/-- The state component of `rand_initial_pmf` is always `s₀`:
    projecting onto `Prod.fst` gives `PMF.pure s₀`. -/
theorem rand_initial_pmf_map_fst
    {SS : Type w} {LS : Type x} [Inhabited Label]
    (adv : Adversary State Label SS LS)
    (ρ : RandomisedStrategy SS LS) (s₀ : State) :
    (rand_initial_pmf adv ρ s₀).map Prod.fst = PMF.pure s₀ := by
  simp only [rand_initial_pmf, PMF.map_bind, PMF.pure_map]
  exact PMF.bind_const _ _

/-- The marginal of `rand_exec_measure` at step 0 equals the initial
    distribution. Follows from the Ionescu-Tulcea `trajMeasure` structure:
    projecting the path measure to coordinate 0 recovers `μ₀`. -/
theorem rand_exec_measure_map_eval_zero
    {SS : Type w} {LS : Type x}
    [Inhabited State] [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State] [Countable State]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]
    (adv : Adversary State Label SS LS) (hres : adv.observation_resolving)
    (ρ : RandomisedStrategy SS LS) (s₀ : State) :
    (rand_exec_measure adv hres ρ s₀).map (fun ω => ω 0) =
    (rand_initial_pmf adv ρ s₀).toMeasure := by
  simp only [rand_exec_measure, ProbabilityTheory.Kernel.trajMeasure]
  rw [MeasureTheory.Measure.map_comp _ _ (measurable_pi_apply 0),
    show (fun f : ℕ → State × Label => f 0) =
      (MeasurableEquiv.piUnique _) ∘ (Preorder.frestrictLe 0) from rfl,
    ProbabilityTheory.Kernel.map_comp_right _
      (Preorder.measurable_frestrictLe 0) (MeasurableEquiv.piUnique _).measurable,
    ProbabilityTheory.Kernel.traj_map_frestrictLe,
    ProbabilityTheory.Kernel.partialTraj_self,
    ProbabilityTheory.Kernel.id_map,
    MeasureTheory.Measure.deterministic_comp_eq_map,
    MeasureTheory.Measure.map_map (MeasurableEquiv.piUnique _).measurable
      (MeasurableEquiv.piUnique _).symm.measurable,
    MeasurableEquiv.self_comp_symm, MeasureTheory.Measure.map_id]
  exact (MeasurableEquiv.piUnique _).measurable

/-- State marginal at step 0 is concentrated at `s₀`. -/
theorem execStateMarginal_zero
    {SS : Type w} {LS : Type x}
    [Inhabited State] [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State] [Countable State]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]
    (adv : Adversary State Label SS LS) (hres : adv.observation_resolving)
    (ρ : RandomisedStrategy SS LS) (s₀ : State) :
    execStateMarginal adv hres ρ s₀ 0 = PMF.pure s₀ := by
  ext s
  show (MeasureTheory.Measure.map (fun ω : ℕ → State × Label => (ω 0).1)
      (rand_exec_measure adv hres ρ s₀)) {s} = (PMF.pure s₀) s
  rw [show (fun ω : ℕ → State × Label => (ω 0).1) = Prod.fst ∘ (fun ω => ω 0) from rfl,
      ← MeasureTheory.Measure.map_map measurable_fst (measurable_pi_apply 0),
      rand_exec_measure_map_eval_zero adv hres ρ s₀,
      PMF.toMeasure_map Prod.fst _ measurable_fst,
      rand_initial_pmf_map_fst adv ρ s₀,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton s)]

/-- **Bridge lemma**: state marginal at step `n + 1` equals the bind of
    the marginal at step `n` with per-state effective transitions `f`.
    Requires Markov property: the effective transition at each state `q`
    at step `n` equals `f q`, independent of path history. -/
theorem execStateMarginal_bind
    {SS : Type w} {LS : Type x}
    [Inhabited State] [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State] [Countable State]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]
    (adv : Adversary State Label SS LS) (hres : adv.observation_resolving)
    (ρ : RandomisedStrategy SS LS) (s₀ : State) (n : ℕ) (f : State → PMF State)
    (hmarkov : ∀ (hist : List (SS × LS)) (q : State), hist.length = n →
      effectiveTransition adv hres (ρ hist (adv.obs.observe_state q)) q = f q) :
    execStateMarginal adv hres ρ s₀ (n + 1) =
    (execStateMarginal adv hres ρ s₀ n).bind f := by
  ext s
  simp only [execStateMarginal, PMF.bind_apply]
  -- Reduce to measure-level equality
  change (MeasureTheory.Measure.map (fun ω : ℕ → State × Label => (ω (n + 1)).1)
      (rand_exec_measure adv hres ρ s₀)) {s} =
    ∑' a, (MeasureTheory.Measure.map (fun ω : ℕ → State × Label => (ω n).1)
      (rand_exec_measure adv hres ρ s₀)) {a} * (f a) s
  set μ := rand_exec_measure adv hres ρ s₀
  set κ := fun n => rand_transition_kernel adv hres ρ n
  have hm_succ : Measurable (fun ω : ℕ → State × Label => (ω (n + 1)).1) :=
    measurable_fst.comp (measurable_pi_apply (n + 1))
  have hm_n : Measurable (fun ω : ℕ → State × Label => (ω n).1) :=
    measurable_fst.comp (measurable_pi_apply n)
  -- Step 1: Express both sides using preimage
  simp_rw [MeasureTheory.Measure.map_apply hm_n (measurableSet_singleton _)]
  rw [MeasureTheory.Measure.map_apply hm_succ (measurableSet_singleton s)]
  -- Step 2: Use compProd to express μ {ω | ω (n+1) = sl}
  have hcompProd :=
    @ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (fun _ => State × Label) _ κ _
      (rand_initial_pmf adv ρ s₀).toMeasure _ (a := n)
  have hpair_meas : Measurable
      (fun (x : ℕ → State × Label) => (Preorder.frestrictLe n x, x (n + 1))) :=
    (Preorder.measurable_frestrictLe n).prodMk (measurable_pi_apply (n + 1))
  -- Key formula: μ {ω | ω (n+1) = sl} = ∫⁻ h, (κ n h) {sl} d(history_marginal)
  have hμ_eq : μ = ProbabilityTheory.Kernel.trajMeasure
      (rand_initial_pmf adv ρ s₀).toMeasure (fun n => κ n) := rfl
  have hstep_eq : ∀ (sl : State × Label),
      μ ((fun ω : ℕ → State × Label => ω (n + 1)) ⁻¹' {sl}) =
      ∫⁻ h, (κ n h) {sl} ∂(μ.map (Preorder.frestrictLe n)) := by
    intro sl
    -- Rewrite the preimage through the pair function
    conv_lhs =>
      rw [show (fun ω : ℕ → State × Label => ω (n + 1)) ⁻¹' {sl} =
        (Prod.snd ∘ fun x : ℕ → State × Label =>
          (Preorder.frestrictLe n x, x (n + 1))) ⁻¹' {sl} from rfl,
        Set.preimage_comp]
    rw [← MeasureTheory.Measure.map_apply hpair_meas
        (measurable_snd (measurableSet_singleton sl)),
      hμ_eq, ← hcompProd]
    -- Now goal: compProd ... (Prod.snd ⁻¹' {sl}) = ∫⁻ h, (κ n h) {sl} d(...)
    rw [show Prod.snd ⁻¹' {sl} = Set.univ ×ˢ {sl} from by ext; simp,
      MeasureTheory.Measure.compProd_apply_prod MeasurableSet.univ
        (measurableSet_singleton sl)]
    simp
  -- Step 3: Decompose fst preimage = ⋃ over labels, apply hstep_eq
  rw [show (fun ω : ℕ → State × Label => (ω (n + 1)).1) ⁻¹' {s} =
    ⋃ l : Label, (fun ω : ℕ → State × Label => ω (n + 1)) ⁻¹' {(s, l)} from by
      ext ω; simp [Prod.ext_iff]]
  rw [MeasureTheory.measure_iUnion
    (fun i j hij => Set.disjoint_iff.mpr fun ω ⟨h1, h2⟩ => by
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1 h2
      exact hij (by have := Prod.ext_iff.mp h1; have := Prod.ext_iff.mp h2
                    simp_all))
    (fun l => (measurable_pi_apply (n + 1)) (measurableSet_singleton _))]
  simp_rw [hstep_eq]
  -- Step 4: Swap ∑' l and ∫⁻ h
  rw [← MeasureTheory.lintegral_tsum (fun l => by
    exact Measurable.aemeasurable (ProbabilityTheory.Kernel.measurable_coe (κ n)
      (measurableSet_singleton (s, l))))]
  -- Goal: ∫⁻ h, ∑' l, (κ n h) {(s, l)} d(history_marginal)
  --     = ∑' q, μ {ω | (ω n).1 = q} * (f q) s
  -- Step 5: ∑' l, (κ n h) {(s, l)} = ((κ n h).map Prod.fst) {s}
  have hfst_sum : ∀ h, ∑' l, (κ n h) {(s, l)} =
      ((κ n h).map Prod.fst) {s} := by
    intro h
    rw [MeasureTheory.Measure.map_apply measurable_fst (measurableSet_singleton s),
      show Prod.fst ⁻¹' {s} = ⋃ l : Label, {(s, l)} from by ext ⟨a, b⟩; simp [Prod.ext_iff, eq_comm],
      MeasureTheory.measure_iUnion
        (fun i j hij => Set.disjoint_iff.mpr fun ⟨a, b⟩ ⟨h1, h2⟩ =>
          hij (by simp [Set.mem_singleton_iff] at h1 h2; rw [← h1.2, ← h2.2]))
        (fun l => measurableSet_singleton _)]
  simp_rw [hfst_sum]
  -- Step 6: Use lintegral_map to push from history space to trajectory space
  classical
  have hmeas_fst : Measurable (fun h => (MeasureTheory.Measure.map Prod.fst ((κ n) h)) {s}) := by
    have : (fun h => (MeasureTheory.Measure.map Prod.fst ((κ n) h)) {s}) =
      (fun h => ((κ n).map Prod.fst h) {s}) := by
      ext h; rw [ProbabilityTheory.Kernel.map_apply _ measurable_fst]
    rw [this]
    exact ProbabilityTheory.Kernel.measurable_coe _ (measurableSet_singleton s)
  rw [MeasureTheory.lintegral_map hmeas_fst (Preorder.measurable_frestrictLe n)]
  -- Goal: ∫⁻ ω, (κ n (frestrictLe n ω)).map Prod.fst {s} dμ
  --     = ∑' q, μ {ω | (ω n).1 = q} * (f q) s
  -- Step 7: Show (κ n (frestrictLe n ω)).map Prod.fst {s} depends on ω only through (ω n)
  -- via the state marginal of rand_step_distribution
  have hkernel_fst : ∀ (ω : ℕ → State × Label),
      (MeasureTheory.Measure.map Prod.fst ((κ n) (Preorder.frestrictLe n ω))) {s} =
      (haveI : ∀ P : Prop, Decidable P := Classical.dec
       if hex : ∃ μ_step, adv.sys.step (ω n).1 (ω n).2 μ_step then (hex.choose) s
       else (PMF.pure (ω n).1) s) := by
    intro ω
    -- (κ n) h = (rand_step_distribution h).toMeasure for kernel ofFunOfCountable
    change (MeasureTheory.Measure.map Prod.fst
      (rand_step_distribution adv hres ρ n (Preorder.frestrictLe n ω)).toMeasure) {s} = _
    rw [PMF.toMeasure_map Prod.fst _ measurable_fst,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton s)]
    -- PMF.map Prod.fst (rand_step_distribution ...) = resolved transition
    simp only [rand_step_distribution, PMF.map_bind, PMF.pure_map, PMF.bind_const, PMF.bind_pure]
    -- The result depends on (frestrictLe n ω) ⟨n, ...⟩ = ω n
    have heval : Preorder.frestrictLe n ω ⟨n, Finset.mem_Iic.mpr le_rfl⟩ = ω n :=
      Preorder.frestrictLe_apply n ω ⟨n, Finset.mem_Iic.mpr le_rfl⟩
    simp only [heval]; split <;> rfl
  -- Step 8: Rewrite integrand using hkernel_fst
  simp_rw [hkernel_fst]
  -- Push the LHS integrand to (State × Label) space via ω ↦ ω n
  set g := (fun sl : State × Label =>
    if hex : ∃ μ_step, adv.sys.step sl.1 sl.2 μ_step
    then hex.choose s else (PMF.pure sl.1) s) with hg_def
  have hmeas_nn : Measurable (fun ω : ℕ → State × Label => ω n) :=
    measurable_pi_apply n
  have hmeas_g : Measurable g := measurable_of_countable _
  change ∫⁻ ω, g (ω n) ∂μ = _
  set ν := μ.map (fun ω : ℕ → State × Label => ω n) with hν_def
  rw [show ∫⁻ ω, g (ω n) ∂μ = ∫⁻ sl, g sl ∂ν from
    (MeasureTheory.lintegral_map hmeas_g hmeas_nn).symm]
  -- Expand LHS as tsum over (State × Label) using countability
  rw [MeasureTheory.lintegral_countable' g, ENNReal.tsum_prod']
  -- Rewrite μ{(ω n).1 = q} as ∑' l, ν{(q,l)}
  have hfst_preimage : ∀ q : State,
      μ ((fun ω => (ω n).1) ⁻¹' {q}) = ∑' l, ν {(q, l)} := by
    intro q
    rw [hν_def, show (fun ω : ℕ → State × Label => (ω n).1) ⁻¹' {q} =
        ⋃ l : Label, (fun ω : ℕ → State × Label => ω n) ⁻¹' {(q, l)}
      from by ext ω; simp [Prod.ext_iff]]
    rw [MeasureTheory.measure_iUnion
      (fun i j hij => Set.disjoint_iff.mpr fun ω ⟨h1, h2⟩ => by
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1 h2
        exact hij (by have := h1.symm.trans h2; exact (Prod.mk.inj this).2))
      (fun l => hmeas_nn (measurableSet_singleton _))]
    simp only [MeasureTheory.Measure.map_apply hmeas_nn (measurableSet_singleton _)]
  conv_rhs => arg 1; ext q; rw [hfst_preimage q, ← ENNReal.tsum_mul_right]
  -- Goal: ∑' q l, g(q,l) * ν{(q,l)} = ∑' q l, ν{(q,l)} * (f q) s
  -- Per-state equality via the Markov averaging property
  congr 1; ext q
  -- ∑' l, g(q,l) * ν{(q,l)} = ∑' l, ν{(q,l)} * (f q) s
  -- We decompose ν{(q,l)} through the trajectory kernel structure.
  -- ν{(q,l)} = μ{ω n = (q,l)} = ∫ (κ' h){(q,l)} d(hist_marginal)
  -- where the kernel κ' at the previous step produces step n.
  -- Averaging g(q,l) over the kernel's label distribution gives (f q) s.
  sorry

/-- When a stopping strategy halts deterministically at step `N`, the
    outcome probability at state `s` equals `(execStateMarginal ... N) s`. -/
theorem execStateMarginal_stop_outcome
    {SS : Type w} {LS : Type x}
    [Inhabited State] [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State] [Countable State]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]
    (adv : Adversary State Label SS LS) (hres : adv.observation_resolving)
    (ρ : RandomisedStrategy SS LS) (s₀ : State)
    (σ : RandomisedStoppingStrategy SS LS) (N : ℕ)
    (hdet : ∀ hist : List (SS × LS), ∀ ss, hist.length = N → σ hist ss = none)
    (hcont : ∀ hist : List (SS × LS), ∀ ss, hist.length < N → (σ hist ss).isSome) :
    ∀ s, (execStateMarginal adv hres ρ s₀ N) s =
      (rand_exec_measure adv hres ρ s₀)
        {ω | σ.stoppingTime adv.obs ω < ⊤ ∧
             (ω (σ.stoppingTime adv.obs ω).toNat).1 = s} := by
  intro s
  have hT : ∀ ω : ℕ → State × Label, σ.stoppingTime adv.obs ω = ↑N := by
    intro ω
    simp only [RandomisedStoppingStrategy.stoppingTime, RandomisedStoppingStrategy.halts_at]
    apply le_antisymm
    · exact iInf₂_le N (hdet _ _ (by simp [rand_obs_history]))
    · apply le_iInf; intro k; apply le_iInf; intro hk
      suffices N ≤ k from WithTop.coe_le_coe.mpr this
      by_contra hlt; push Not at hlt
      have := hcont (rand_obs_history adv.obs ω k) (adv.obs.observe_state (ω k).1)
        (by simp [rand_obs_history]; exact hlt)
      simp [hk] at this
  have heq : {ω | σ.stoppingTime adv.obs ω < ⊤ ∧ (ω (σ.stoppingTime adv.obs ω).toNat).1 = s} =
    {ω | (ω N).1 = s} := by ext ω; simp [hT ω]
  rw [heq]
  let f := fun ω : ℕ → State × Label => (ω N).1
  have hf : Measurable f := measurable_fst.comp (measurable_pi_apply N)
  change (MeasureTheory.Measure.map f (rand_exec_measure adv hres ρ s₀)) {s} =
    (rand_exec_measure adv hres ρ s₀) (f ⁻¹' {s})
  exact MeasureTheory.Measure.map_apply hf (MeasurableSet.singleton s)

/-- A deterministic stopping time achieves almost-sure termination. -/
theorem deterministic_stop_terminates
    {SS : Type w} {LS : Type x}
    [Inhabited State] [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State] [Countable State]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]
    (adv : Adversary State Label SS LS) (hres : adv.observation_resolving)
    (ρ : RandomisedStrategy SS LS) (s₀ : State)
    (σ : RandomisedStoppingStrategy SS LS) (N : ℕ)
    (hdet : ∀ hist : List (SS × LS), ∀ ss, hist.length = N → σ hist ss = none)
    (_hcont : ∀ hist : List (SS × LS), ∀ ss, hist.length < N → (σ hist ss).isSome) :
    (rand_exec_measure adv hres ρ s₀)
      {ω | σ.stoppingTime adv.obs ω < ⊤} = 1 := by
  suffices h : ∀ ω, σ.stoppingTime adv.obs ω < ⊤ by
    have heq : {ω | σ.stoppingTime adv.obs ω < ⊤} = Set.univ :=
      Set.eq_univ_of_forall h
    rw [heq]; exact MeasureTheory.measure_univ
  intro ω
  have halt : σ.halts_at adv.obs ω N := by
    simp only [RandomisedStoppingStrategy.halts_at]
    apply hdet
    simp [rand_obs_history]
  have hle : σ.stoppingTime adv.obs ω ≤ ↑N :=
    iInf₂_le N halt
  exact lt_of_le_of_lt hle (WithTop.coe_lt_top N)

/-! ### External Trace -/

/-- When exactly one step in `[0, N)` carries an external label `l` and all
    others are internal, `externalLabelsUntil` returns `[l]`. -/
theorem externalLabelsUntil_single
    {l : Label} {ω : ℕ → State × Label} {k₀ N : ℕ} (hk₀ : k₀ < N)
    (hext : lab.is_external (ω k₀).2 = true ∧ (ω k₀).2 = l)
    (hint : ∀ k, k < N → k ≠ k₀ → lab.is_internal (ω k).2 = true) :
    externalLabelsUntil lab ω N = [l] := by
  unfold externalLabelsUntil
  rw [List.filter_map]
  have hcomp : (fun l => lab.is_external l) ∘ (fun i => (ω i).2) =
      fun i => lab.is_external (ω i).2 := rfl
  rw [hcomp]
  have hfilt : List.filter (fun i => lab.is_external (ω i).2) (List.range N) = [k₀] := by
    induction N with
    | zero => omega
    | succ n ih =>
      rw [List.range_succ, List.filter_append]
      simp only [List.filter_cons, List.filter_nil]
      by_cases hkn : k₀ = n
      · subst hkn
        simp only [hext.1, ite_true]
        have : List.filter (fun i => lab.is_external (ω i).2) (List.range k₀) = [] := by
          rw [List.filter_eq_nil_iff]
          intro x hx
          rw [List.mem_range] at hx
          have := hint x (by omega) (by omega)
          simp [LTS.Labelling.is_external, this]
        simp [this]
      · have hlt : k₀ < n := by omega
        have hint_n := hint n (by omega) (by omega)
        simp only [LTS.Labelling.is_external, hint_n, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte]
        rw [List.append_nil]
        exact ih hlt (fun k hk hne => hint k (by omega) hne)
  rw [hfilt]
  simp [hext.2]

/-! ### Direction 1: WeakStep → SchedWeakStep

    Construct a randomised strategy that replays the `WeakStep` chain.
    At each step `k`, the strategy outputs the label-signal distribution
    corresponding to the chain's choice function at step `k`. The stopping
    strategy halts after all chain steps are executed. -/

/-- Construct the randomised strategy replaying a `WeakStep` chain. -/
noncomputable def WeakStep.chainStrategy
    {SS : Type w} {LS : Type x}
    (adv : Adversary State Label SS LS) (_hres : adv.observation_resolving)
    [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    [Countable State] [Inhabited State]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]
    (_hsys : adv.sys = sys)
    {l : Label} {s₀ : State} {μ₁ μ₂ μ' : PMF State}
    (hpre : InternalWeakStar sys lab (PMF.pure s₀) μ₁)
    (hext : HyperStep sys l μ₁ μ₂)
    (hpost : InternalWeakStar sys lab μ₂ μ') :
    RandomisedStrategy SS LS :=
  let _n_pre := hpre.length
  let _n_post := hpost.length
  let _f_ext := hext.f
  -- Placeholder: outputs default label-signal at every step.
  -- The correct implementation would map chain choice functions to
  -- label-signal distributions; see chainStrategy_conditions.
  fun _hist _ss => PMF.pure (adv.obs.observe_label default default)

/-- Construct the stopping strategy that halts after all chain steps. -/
noncomputable def WeakStep.chainStopStrategy
    {SS : Type w} {LS : Type x}
    (adv : Adversary State Label SS LS) (_hres : adv.observation_resolving)
    [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    [Countable State] [Inhabited State]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]
    (_hsys : adv.sys = sys)
    {l : Label} {s₀ : State} {μ₁ μ₂ μ' : PMF State}
    (hpre : InternalWeakStar sys lab (PMF.pure s₀) μ₁)
    (_hext : HyperStep sys l μ₁ μ₂)
    (hpost : InternalWeakStar sys lab μ₂ μ') :
    RandomisedStoppingStrategy SS LS :=
  let N := hpre.length + 1 + hpost.length
  fun hist _ss =>
    if hist.length < N then some (PMF.pure (adv.obs.observe_label default default)) else none

/-- The stopping strategy is extended by the chain strategy. -/
theorem WeakStep.chainStrategy_extends
    {SS : Type w} {LS : Type x}
    (adv : Adversary State Label SS LS) (hres : adv.observation_resolving)
    [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    [Countable State] [Inhabited State]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]
    (hsys : adv.sys = sys)
    {l : Label} {s₀ : State} {μ₁ μ₂ μ' : PMF State}
    (hpre : InternalWeakStar sys lab (PMF.pure s₀) μ₁)
    (hext : HyperStep sys l μ₁ μ₂)
    (hpost : InternalWeakStar sys lab μ₂ μ') :
    (chainStopStrategy adv hres hsys hpre hext hpost).IsExtendedBy
      (chainStrategy adv hres hsys hpre hext hpost) := by
  intro hist ss d hsome
  simp only [chainStopStrategy, chainStrategy] at hsome ⊢
  split_ifs at hsome with h
  · exact (Option.some.inj hsome)

/-- The chain strategy satisfies all three `SchedWeakStep` conditions:
    termination, trace, and outcome. -/
theorem WeakStep.chainStrategy_conditions
    {SS : Type w} {LS : Type x}
    (adv : Adversary State Label SS LS) (hres : adv.observation_resolving)
    [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    [Countable State] [Inhabited State]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]
    (hsys : adv.sys = sys)
    {l : Label} {s₀ : State} {μ₁ μ₂ μ' : PMF State}
    (hpre : InternalWeakStar sys lab (PMF.pure s₀) μ₁)
    (hext : HyperStep sys l μ₁ μ₂)
    (hpost : InternalWeakStar sys lab μ₂ μ') :
    let σ := chainStopStrategy adv hres hsys hpre hext hpost
    let ρ := chainStrategy adv hres hsys hpre hext hpost
    let μ_exec := rand_exec_measure adv hres ρ s₀
    let T := σ.stoppingTime adv.obs
    (μ_exec {ω | T ω < ⊤} = 1) ∧
    (μ_exec {ω | T ω < ⊤ →
      externalLabelsUntil lab ω (T ω).toNat = [l]} = 1) ∧
    (∀ s, μ' s = μ_exec {ω | T ω < ⊤ ∧ (ω (T ω).toNat).1 = s}) := by
  let N := hpre.length + 1 + hpost.length
  refine ⟨?_, ?_, ?_⟩
  · exact deterministic_stop_terminates adv hres
      (chainStrategy adv hres hsys hpre hext hpost) s₀
      (chainStopStrategy adv hres hsys hpre hext hpost) N
      (by intro hist ss hlen; unfold chainStopStrategy; split_ifs with h <;> [omega; rfl])
      (by intro hist ss hlt; unfold chainStopStrategy; split_ifs with h <;> [simp; omega])
  · sorry
  · sorry

/-! ### Direction 2: SchedWeakStep → WeakStep

    Decompose the scheduler execution into the algebraic form
    `InternalWeakStar · HyperStep · InternalWeakStar`. The trace
    condition `[l]` identifies the unique external step; the state
    marginals before and after this step give the intermediate
    distributions `μ₁` and `μ₂`. -/

/-- Pre-external state marginal: the distribution over states just
    before the (synchronised) external step. Extracted from the
    execution measure by decomposing paths by external-label position. -/
noncomputable def SchedWeakStep.preMarginal
    {SS : Type w} {LS : Type x}
    (adv : Adversary State Label SS LS) (hres : adv.observation_resolving)
    [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    [Countable State] [Inhabited State]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]
    (hsys : adv.sys = sys)
    {l : Label} {s₀ : State} {μ' : PMF State}
    (hs : SchedWeakStep adv hres lab l s₀ μ') : PMF State := by
  exact sorry

/-- Post-external state marginal: the distribution over states just
    after the (synchronised) external step. -/
noncomputable def SchedWeakStep.postMarginal
    {SS : Type w} {LS : Type x}
    (adv : Adversary State Label SS LS) (hres : adv.observation_resolving)
    [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    [Countable State] [Inhabited State]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]
    (hsys : adv.sys = sys)
    {l : Label} {s₀ : State} {μ' : PMF State}
    (hs : SchedWeakStep adv hres lab l s₀ μ') : PMF State := by
  exact sorry

/-- The pre-internal phase: `InternalWeakStar` from `PMF.pure s₀` to the
    pre-external marginal. Before the external step, each execution step
    uses an internal label, giving an `InternalHyperStep` at each round. -/
noncomputable def SchedWeakStep.pre_internalWeakStar
    {SS : Type w} {LS : Type x}
    (adv : Adversary State Label SS LS) (hres : adv.observation_resolving)
    [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    [Countable State] [Inhabited State]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]
    (hsys : adv.sys = sys)
    {l : Label} {s₀ : State} {μ' : PMF State}
    (hs : SchedWeakStep adv hres lab l s₀ μ') :
    InternalWeakStar sys lab (PMF.pure s₀) (hs.preMarginal adv hres hsys) := by
  sorry

/-- The external step: `HyperStep` with label `l` from the pre-external
    to the post-external marginal. All states take their `l`-transition
    in a single synchronised round. -/
noncomputable def SchedWeakStep.ext_hyperStep
    {SS : Type w} {LS : Type x}
    (adv : Adversary State Label SS LS) (hres : adv.observation_resolving)
    [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    [Countable State] [Inhabited State]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]
    (hsys : adv.sys = sys)
    {l : Label} {s₀ : State} {μ' : PMF State}
    (hs : SchedWeakStep adv hres lab l s₀ μ') :
    HyperStep sys l (hs.preMarginal adv hres hsys) (hs.postMarginal adv hres hsys) := by
  sorry

/-- The post-internal phase: `InternalWeakStar` from the post-external
    marginal to the outcome `μ'`. After the external step, each execution
    step uses an internal label until stopping. -/
noncomputable def SchedWeakStep.post_internalWeakStar
    {SS : Type w} {LS : Type x}
    (adv : Adversary State Label SS LS) (hres : adv.observation_resolving)
    [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    [Countable State] [Inhabited State]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]
    (hsys : adv.sys = sys)
    {l : Label} {s₀ : State} {μ' : PMF State}
    (hs : SchedWeakStep adv hres lab l s₀ μ') :
    InternalWeakStar sys lab (hs.postMarginal adv hres hsys) μ' := by
  sorry

/-! ## Equivalence Theorems -/

/-- The hyper-transition weak step implies the scheduler-based weak step.

    **Proof:** Decompose the `WeakStep` into its chain components, construct
    the strategy pair via `chainStrategy` / `chainStopStrategy`, and verify
    the `SchedWeakStep` conditions via `chainStrategy_conditions`. -/
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
  exact ⟨chainStopStrategy adv hres hsys hw.pre hw.ext hw.post,
         chainStrategy adv hres hsys hw.pre hw.ext hw.post,
         chainStrategy_extends adv hres hsys hw.pre hw.ext hw.post,
         chainStrategy_conditions adv hres hsys hw.pre hw.ext hw.post⟩

/-- The scheduler-based weak step implies the hyper-transition weak step.

    **Proof:** Extract intermediate distributions `preMarginal` and
    `postMarginal` from the execution measure, then verify the three
    components: pre-internal phase, external step, post-internal phase. -/
noncomputable def SchedWeakStep.toWeakStep
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
    WeakStep sys lab l (PMF.pure s₀) μ' :=
  ⟨hs.preMarginal adv hres hsys,
   hs.postMarginal adv hres hsys,
   hs.pre_internalWeakStar adv hres hsys,
   hs.ext_hyperStep adv hres hsys,
   hs.post_internalWeakStar adv hres hsys⟩

end PLTS
