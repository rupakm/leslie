import Leslie_LTS.Framework.Adversary
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-! # Randomised Probabilistic Executions

    Extension of the probabilistic execution framework from deterministic
    strategies to randomised strategies (`RandomisedStrategy`). Under
    `observation_resolving`, a randomised strategy induces two sources of
    randomness at each step:

    1. **Scheduler randomness**: the strategy samples a label-signal from a PMF
    2. **Transition randomness**: the PLTS samples the next state from the
       distribution determined by the chosen label (via the resolving condition)

    The execution measure lives on `ℕ → State × Label` — sequences of
    state–label pairs — because the label choices affect the observation
    history, which in turn affects future scheduler decisions. This contrasts
    with the deterministic case (`ProbExec.lean`), where the measure lives
    on `ℕ → State` because labels are deterministic functions of the state
    sequence.

    Using `State × Label` (rather than `State × LS`) keeps the measure space
    symmetric with the PLTS dynamics (`step : State → Label → PMF State → Prop`)
    and allows direct conversion to `LTS.Execution` via `rand_to_exec`.

    ## Structure

    1. **Observation history**: compute `(SS × LS)` from `(State × Label)` pairs
    2. **Label resolution**: convert a label-signal to a label (classical)
    3. **Step probability**: probability of each transition (state × scheduler)
    4. **Cone measure**: inductive probability of a finite prefix
    5. **Step distribution**: PMF at each step for the Ionescu-Tulcea construction
    6. **Transition kernel**: Markov kernel wrapping the step distribution
    7. **Execution measure**: probability measure via Ionescu-Tulcea
    8. **Execution well-formedness**: per-execution analogue of well-formedness
    9. **Relationship to deterministic strategies**: embedding via `toRandomised`
-/

namespace PLTS

variable {State : Type u} {Label : Type v}
variable {SS : Type w} {LS : Type x}

/-! ## Observation History from State–Label Sequences -/

/-- The observation history computed from a sequence of state–label pairs.
    At each position `i < k`, the observation is
    `(observe_state(s_i), observe_label(s_i, l_i))`. -/
def rand_obs_history (obs : Observation State Label SS LS)
    (ω : ℕ → State × Label) (k : ℕ) : List (SS × LS) :=
  List.ofFn fun i : Fin k =>
    (obs.observe_state (ω i.val).1, obs.observe_label (ω i.val).1 (ω i.val).2)

/-! ## Label Resolution -/

open Classical in
/-- Resolve a label-signal to a label at a given state: return the unique
    label `l` with `observe_label s l = ls` and an enabled transition, or
    `default` if no such label exists.

    Under `observation_resolving`, the result is unique (independent of
    classical choice) when a matching transition exists. -/
noncomputable def resolve_label (adv : Adversary State Label SS LS)
    [Inhabited Label]
    (s : State) (ls : LS) : Label :=
  if hex : ∃ l, ∃ μ, adv.obs.observe_label s l = ls ∧ adv.sys.step s l μ then
    hex.choose
  else
    default

/-- Under `observation_resolving`, `resolve_label` returns the actual label
    when one exists with the given signal. -/
theorem resolve_label_eq_of_resolving (adv : Adversary State Label SS LS)
    [Inhabited Label]
    (hres : adv.observation_resolving)
    (s : State) (l : Label) (ls : LS) (μ : PMF State)
    (hobs : adv.obs.observe_label s l = ls)
    (hstep : adv.sys.step s l μ) :
    resolve_label adv s ls = l := by
  classical
  have hex : ∃ l', ∃ μ', adv.obs.observe_label s l' = ls ∧ adv.sys.step s l' μ' :=
    ⟨l, μ, hobs, hstep⟩
  simp only [resolve_label, dif_pos hex]
  obtain ⟨μ', hobs', hstep'⟩ := hex.choose_spec
  exact (hres s hex.choose l μ' μ (hobs'.trans hobs.symm) hstep' hstep).1

/-! ## Randomised Step Probability -/

open Classical in
/-- The probability of the transition at step `k` of a state–label
    sequence under randomised strategy `ρ`. This is the product of:

    - The **state-transition probability**: `μ_k(s_{k+1})` where `μ_k` is the
      distribution for transition `(s_k, l_k)`, or the Dirac indicator if
      no transition exists from `(s_k, l_k)`.
    - The **scheduler probability**: `ρ(obs_history, ss_{k+1})(ls_{k+1})`,
      where `ls_{k+1} = observe_label(s_{k+1}, l_{k+1})` is the label-signal
      corresponding to the label at step `k+1`. -/
noncomputable def rand_step_prob (adv : Adversary State Label SS LS)
    (ρ : RandomisedStrategy SS LS)
    (ω : ℕ → State × Label) (k : ℕ) : ENNReal :=
  let s_k := (ω k).1
  let l_k := (ω k).2
  let state_prob : ENNReal :=
    if h : ∃ μ, adv.sys.step s_k l_k μ then
      h.choose ((ω (k + 1)).1)
    else
      if (ω (k + 1)).1 = s_k then 1 else 0
  let sched_prob : ENNReal :=
    ρ (rand_obs_history adv.obs ω (k + 1))
      (adv.obs.observe_state (ω (k + 1)).1)
      (adv.obs.observe_label (ω (k + 1)).1 (ω (k + 1)).2)
  state_prob * sched_prob

open Classical in
/-- Under `observation_resolving`, the state-transition component of
    `rand_step_prob` equals the PMF value for the actual transition
    distribution, independently of classical choice. -/
theorem rand_step_prob_state_eq_of_resolving (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    (ω : ℕ → State × Label) (k : ℕ)
    (μ : PMF State)
    (hstep : adv.sys.step (ω k).1 (ω k).2 μ) :
    (if h : ∃ μ', adv.sys.step (ω k).1 (ω k).2 μ' then
      h.choose ((ω (k + 1)).1)
    else
      if (ω (k + 1)).1 = (ω k).1 then 1 else 0) = μ ((ω (k + 1)).1) := by
  classical
  rw [dif_pos ⟨μ, hstep⟩]
  exact congr_fun (congr_arg DFunLike.coe
    (hres _ _ _ _ _ rfl (Exists.choose_spec ⟨μ, hstep⟩) hstep).2) _

/-! ## Randomised Cone Measure -/

open Classical in
/-- The **randomised cone measure**: probability that a state–label
    sequence matches the given prefix of length `n`, under randomised
    strategy `ρ` from initial state `s₀`.

    - At length 0: `ρ([], ss₀)(observe_label(s₀, l₀))` if the initial
      state matches, else 0. This accounts for the scheduler's initial
      label-signal choice.
    - At length `n + 1`: the cone measure at length `n` times the
      step probability at step `n`. -/
noncomputable def rand_cone_prob (adv : Adversary State Label SS LS)
    (ρ : RandomisedStrategy SS LS) (s₀ : State)
    (ω : ℕ → State × Label) : ℕ → ENNReal
  | 0 => if (ω 0).1 = s₀ then
           ρ [] (adv.obs.observe_state s₀)
             (adv.obs.observe_label s₀ (ω 0).2)
         else 0
  | n + 1 => rand_cone_prob adv ρ s₀ ω n * rand_step_prob adv ρ ω n

theorem rand_cone_prob_succ (adv : Adversary State Label SS LS)
    (ρ : RandomisedStrategy SS LS) (s₀ : State) (ω : ℕ → State × Label) (n : ℕ) :
    rand_cone_prob adv ρ s₀ ω (n + 1) =
    rand_cone_prob adv ρ s₀ ω n * rand_step_prob adv ρ ω n :=
  rfl

/-- The randomised cone measure is zero if the initial state doesn't match. -/
theorem rand_cone_prob_eq_zero_of_ne (adv : Adversary State Label SS LS)
    (ρ : RandomisedStrategy SS LS) (s₀ : State) (ω : ℕ → State × Label)
    (h : (ω 0).1 ≠ s₀) (n : ℕ) :
    rand_cone_prob adv ρ s₀ ω n = 0 := by
  induction n with
  | zero =>
    classical
    exact if_neg h
  | succ n ih => rw [rand_cone_prob_succ, ih, zero_mul]

/-! ## Step Distribution and Transition Kernels -/

variable [MeasurableSpace State] [MeasurableSingletonClass State] [Countable State]
         [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]

open Classical in
/-- The transition distribution for a randomised strategy at step `n`.
    Given a history of `(State × Label)` pairs up to step `n`:

    1. Get the distribution `μ_n` for transition `(s_n, l_n)`
       (or Dirac fallback if no transition exists)
    2. Sample `s_{n+1} ~ μ_n`
    3. Compute the observation history via `observe_state` and `observe_label`
    4. The scheduler samples `ls_{n+1} ~ ρ(obs_history, observe_state(s_{n+1}))`
    5. Resolve `ls_{n+1}` to `l_{n+1}` via `resolve_label`
    6. Return `(s_{n+1}, l_{n+1})` -/
noncomputable def rand_step_distribution [Inhabited State] [Inhabited Label]
    (adv : Adversary State Label SS LS)
    (_hres : adv.observation_resolving)
    (ρ : RandomisedStrategy SS LS)
    (n : ℕ) (h : (i : ↥(Finset.Iic n)) → State × Label) : PMF (State × Label) :=
  let s_n := (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1
  let l_n := (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2
  -- Resolve the current transition
  let μ_n : PMF State :=
    if hex : ∃ μ, adv.sys.step s_n l_n μ then
      hex.choose
    else
      PMF.pure s_n -- fallback: stay in current state
  -- Build observation history (steps 0 through n inclusive)
  let obs_hist : List (SS × LS) := List.ofFn fun i : Fin (n + 1) =>
    let idx : ↥(Finset.Iic n) := ⟨i.val, Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp i.isLt)⟩
    (adv.obs.observe_state (h idx).1, adv.obs.observe_label (h idx).1 (h idx).2)
  -- Sample next state, then scheduler samples label-signal, resolve to label
  μ_n.bind fun s' =>
    (ρ obs_hist (adv.obs.observe_state s')).bind fun ls' =>
      PMF.pure (s', resolve_label adv s' ls')

/-- The Markov kernel at step `n` for a randomised strategy: wraps
    `rand_step_distribution` as a measure-valued kernel. -/
noncomputable def rand_transition_kernel [Inhabited State] [Inhabited Label]
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    (ρ : RandomisedStrategy SS LS)
    (n : ℕ) : ProbabilityTheory.Kernel
      ((i : ↥(Finset.Iic n)) → State × Label) (State × Label) :=
  ProbabilityTheory.Kernel.ofFunOfCountable
    (fun h => (rand_step_distribution adv hres ρ n h).toMeasure)

/-- The transition kernel for a randomised strategy is a Markov kernel
    (produces probability measures). -/
instance rand_transition_kernel_markov [Inhabited State] [Inhabited Label]
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    (ρ : RandomisedStrategy SS LS) (n : ℕ) :
    ProbabilityTheory.IsMarkovKernel (rand_transition_kernel adv hres ρ n) :=
  ProbabilityTheory.IsMarkovKernel.mk (fun h => by
    show MeasureTheory.IsProbabilityMeasure ((rand_transition_kernel adv hres ρ n) h)
    simp only [rand_transition_kernel, ProbabilityTheory.Kernel.ofFunOfCountable]
    exact PMF.toMeasure.isProbabilityMeasure (rand_step_distribution adv hres ρ n h))

/-! ## Initial Distribution -/

/-- The initial distribution for a randomised execution: the state is fixed
    at `s₀`, the scheduler samples a label-signal `ls ~ ρ([], ss₀)`, and
    `resolve_label` converts it to a label.
    The resulting PMF at `(s, l)` is
    `[s = s₀] * ∑ {ls | resolve_label(s₀, ls) = l} ρ([], ss₀)(ls)`. -/
noncomputable def rand_initial_pmf [Inhabited Label]
    (adv : Adversary State Label SS LS)
    (ρ : RandomisedStrategy SS LS) (s₀ : State) : PMF (State × Label) :=
  (ρ [] (adv.obs.observe_state s₀)).bind fun ls =>
    PMF.pure (s₀, resolve_label adv s₀ ls)

/-! ## Execution Measure -/

/-- The probability measure on infinite state–label sequences induced
    by a randomised strategy from initial state `s₀`.

    Constructed via the Ionescu-Tulcea theorem from the initial distribution
    and the sequence of randomised transition kernels. The measure captures
    both the scheduler's coin flips (label-signal choices resolved to labels)
    and the PLTS's transition randomness. -/
noncomputable def rand_exec_measure [Inhabited State] [Inhabited Label]
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    (ρ : RandomisedStrategy SS LS) (s₀ : State) :
    MeasureTheory.Measure (ℕ → State × Label) :=
  ProbabilityTheory.Kernel.trajMeasure
    (rand_initial_pmf adv ρ s₀).toMeasure
    (fun n => rand_transition_kernel adv hres ρ n)

/-- The randomised execution measure is a probability measure. -/
noncomputable instance rand_exec_measure_prob [Inhabited State] [Inhabited Label]
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    (ρ : RandomisedStrategy SS LS) (s₀ : State) :
    MeasureTheory.IsProbabilityMeasure (rand_exec_measure adv hres ρ s₀) :=
  ProbabilityTheory.Kernel.instIsProbabilityMeasureForallTrajMeasure

/-! ## Conversion to LTS.Execution

    Since the measure space is `ℕ → State × Label`, we can directly extract
    an `LTS.Execution` — no label reconstruction needed. -/

/-- Convert a state–label sequence to an `LTS.Execution`. -/
def rand_to_exec (ω : ℕ → State × Label) : LTS.Execution State Label where
  states := fun n => (ω n).1
  labels := fun n => (ω n).2

/-! ## Execution Well-Formedness

    An execution is **well-formed** under a randomised strategy if, at each
    step along the execution, every label-signal in the support of the
    scheduler's output has a corresponding enabled transition. This is the
    per-execution analogue of global well-formedness, and is the probabilistic
    counterpart of `consistent + hstep` for deterministic strategies. -/

omit [MeasurableSpace State] [MeasurableSingletonClass State] [Countable State]
  [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label] in
/-- An execution `ω` is well-formed under randomised strategy `ρ` if, at
    each step `k`, every label-signal in the support of the scheduler's
    output corresponds to at least one enabled transition from `(ω k).1`. -/
def Adversary.rand_exec_well_formed (adv : Adversary State Label SS LS)
    (ρ : RandomisedStrategy SS LS) (ω : ℕ → State × Label) : Prop :=
  ∀ k ls, ls ∈ (ρ (rand_obs_history adv.obs ω k)
    (adv.obs.observe_state (ω k).1)).support →
    ∃ l μ, adv.obs.observe_label (ω k).1 l = ls ∧ adv.sys.step (ω k).1 l μ

/-! ## Relationship to Deterministic Strategies

    When the randomised strategy is a lifted deterministic strategy
    `σ.toRandomised`, the scheduler PMF becomes a Dirac distribution
    `PMF.pure (σ hist ss)`, so the only randomness comes from the PLTS
    transitions — matching the deterministic case. -/

omit [MeasurableSpace State] [MeasurableSingletonClass State] [Countable State]
  [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label] in
/-- The initial PMF for a lifted deterministic strategy is a Dirac
    at `(s₀, resolve_label adv s₀ (σ [] ss₀))`. -/
theorem rand_initial_pmf_toRandomised [Inhabited Label]
    (adv : Adversary State Label SS LS)
    (σ : Strategy SS LS) (s₀ : State) :
    rand_initial_pmf adv σ.toRandomised s₀ =
    PMF.pure (s₀, resolve_label adv s₀ (σ [] (adv.obs.observe_state s₀))) := by
  simp [rand_initial_pmf, Strategy.toRandomised, PMF.pure_bind]

/-! ## Projections -/

omit [MeasurableSpace State] [MeasurableSingletonClass State] [Countable State]
  [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label] in
/-- Project a state–label sequence to its state component. -/
def rand_proj_states (ω : ℕ → State × Label) : ℕ → State :=
  fun n => (ω n).1

/-- The state-marginal measure: pushforward of `rand_exec_measure` under
    the state projection. This is a probability measure on `ℕ → State`. -/
noncomputable def rand_exec_measure_states [Inhabited State] [Inhabited Label]
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    (ρ : RandomisedStrategy SS LS) (s₀ : State) :
    MeasureTheory.Measure (ℕ → State) :=
  MeasureTheory.Measure.map rand_proj_states (rand_exec_measure adv hres ρ s₀)

/-! ## Cylinder Sets -/

omit [MeasurableSpace State] [MeasurableSingletonClass State] [Countable State]
  [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label] in
/-- The cylinder set for a state–label sequence: all infinite sequences
    agreeing on positions `0, ..., n`. -/
def rand_state_cylinder (ω : ℕ → State × Label) (n : ℕ) :
    Set (ℕ → State × Label) :=
  {ω' | ∀ k, k ≤ n → ω' k = ω k}

/-! ## Cylinder Identification Theorems

    These theorems prove that `rand_exec_measure` applied to a cylinder
    set equals `rand_cone_prob`. This is the randomised analogue of
    `exec_measure_cylinder` from `ProbExec.lean`. -/

omit [MeasurableSpace State] [MeasurableSingletonClass State] [Countable State]
  [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label] in
/-- Helper: under well-formedness and resolving, the tsum over label-signals
    of `ρ(ls) * [resolve_label(s, ls) = l]` collapses to
    `ρ(observe_label(s, l))`. The key insight is that `observe_label s l`
    is the unique label-signal that resolves back to `l`. -/
theorem resolve_label_tsum_eq [Inhabited Label] [DecidableEq Label]
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    (ρ_val : PMF LS)
    (s : State)
    (hwf : ∀ ls, ls ∈ ρ_val.support →
      ∃ l μ, adv.obs.observe_label s l = ls ∧ adv.sys.step s l μ)
    (l : Label) (μ : PMF State)
    (hstep : adv.sys.step s l μ) :
    ∑' ls, ρ_val ls * (if resolve_label adv s ls = l then (1 : ENNReal) else 0) =
    ρ_val (adv.obs.observe_label s l) := by
  rw [tsum_eq_single (adv.obs.observe_label s l)]
  · simp only [resolve_label_eq_of_resolving adv hres s l _ μ rfl hstep, ite_true, mul_one]
  · intro ls hne
    by_cases hmem : ls ∈ ρ_val.support
    · obtain ⟨l', μ', hobs', hstep'⟩ := hwf ls hmem
      have hrl := resolve_label_eq_of_resolving adv hres s l' ls μ' hobs' hstep'
      have : resolve_label adv s ls ≠ l := by
        intro heq; rw [hrl] at heq; rw [heq] at hobs'
        exact hne hobs'.symm
      simp [this]
    · simp only [PMF.mem_support_iff, ne_eq, not_not] at hmem
      simp [hmem]

/-- The randomised transition kernel applied to a singleton equals the
    step distribution PMF value. Analogous to `transition_kernel_singleton`. -/
theorem rand_transition_kernel_singleton [Inhabited State] [Inhabited Label]
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    (ρ : RandomisedStrategy SS LS)
    (n : ℕ) (h : (i : ↥(Finset.Iic n)) → State × Label)
    (sl : State × Label) :
    (rand_transition_kernel adv hres ρ n) h {sl} =
    (rand_step_distribution adv hres ρ n h) sl := by
  simp [rand_transition_kernel, ProbabilityTheory.Kernel.ofFunOfCountable,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton sl)]

omit [MeasurableSpace State] [MeasurableSingletonClass State] [Countable State]
  [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label] in
/-- The step distribution evaluated at the next state–label pair equals
    `rand_step_prob` when the history matches the execution prefix.
    This requires `observation_resolving`, `rand_exec_well_formed`,
    and that transitions exist at each step. -/
theorem rand_step_distribution_eq_step_prob [Inhabited State] [Inhabited Label]
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    (ρ : RandomisedStrategy SS LS)
    (ω : ℕ → State × Label)
    (hewf : adv.rand_exec_well_formed ρ ω)
    (hstep : ∀ k, ∃ μ, adv.sys.step (ω k).1 (ω k).2 μ)
    (n : ℕ) (h : (i : ↥(Finset.Iic n)) → State × Label)
    (hh : ∀ (i : ↥(Finset.Iic n)), h i = ω ↑i) :
    (rand_step_distribution adv hres ρ n h) (ω (n + 1)) =
    rand_step_prob adv ρ ω n := by
  classical
  -- Unfold rand_step_distribution
  simp only [rand_step_distribution]
  -- The current state and label from the history
  have h_n_eq : h ⟨n, Finset.mem_Iic.mpr le_rfl⟩ = ω n :=
    hh ⟨n, Finset.mem_Iic.mpr le_rfl⟩
  -- The observation history from h agrees with obs_history from ω
  have hhist_eq : (List.ofFn fun i : Fin (n + 1) =>
      let idx : ↥(Finset.Iic n) :=
        ⟨i.val, Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp i.isLt)⟩
      (adv.obs.observe_state (h idx).1,
       adv.obs.observe_label (h idx).1 (h idx).2)) =
    rand_obs_history adv.obs ω (n + 1) := by
    simp only [rand_obs_history]
    congr 1; ext ⟨i, hi⟩ <;> {
      simp only [hh ⟨i, Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp hi)⟩]
    }
  -- Unfold bind at ω (n+1)
  rw [PMF.bind_apply]
  -- The state transition part
  obtain ⟨μn, hμn⟩ := hstep n
  -- Rewrite the state component using h_n_eq
  conv_lhs =>
    arg 1; ext s'
    rw [PMF.bind_apply]
  -- Unfold rand_step_prob
  unfold rand_step_prob
  -- Simplify PMF.pure_apply inside the inner tsum
  simp_rw [PMF.pure_apply]
  -- Rewrite ω(n+1) = (s', resolve(s', a)) as Prod.mk equality
  simp_rw [Prod.eq_iff_fst_eq_snd_eq]
  -- Now we have: if (ω(n+1)).1 = s' ∧ (ω(n+1)).2 = resolve(s', a) then 1 else 0
  -- Collapse the s' sum via tsum_eq_single
  rw [tsum_eq_single (ω (n + 1)).1]
  · -- s' = (ω(n+1)).1: the ∧ collapses to just the resolve condition
    simp only [true_and]
    -- Both sides involve step from (ω n); use h_n_eq to align
    -- First handle the observation history on the LHS
    simp_rw [hhist_eq]
    -- Key idea: rewrite h ⟨n,...⟩ to ω n everywhere using simp
    -- simp handles dependent type rewrites better than rw
    simp only [h_n_eq]
    -- Now both sides reference (ω n) directly
    -- The dif conditions are the same: ∃ μ, step (ω n).1 (ω n).2 μ
    rw [dif_pos ⟨μn, hμn⟩, dif_pos ⟨μn, hμn⟩]
    -- Both choose_spec give steps from (ω n), so by resolving they equal μn
    have hμ_eq1 : (⟨μn, hμn⟩ : ∃ μ, adv.sys.step (ω n).1 (ω n).2 μ).choose
        (ω (n + 1)).1 = μn (ω (n + 1)).1 :=
      congr_fun (congr_arg DFunLike.coe
        (hres _ _ _ _ _ rfl
          (⟨μn, hμn⟩ : ∃ μ, adv.sys.step (ω n).1 (ω n).2 μ).choose_spec
          hμn).2) _
    rw [hμ_eq1]
    -- Now collapse the tsum over label-signals
    congr 1
    simp_rw [eq_comm (a := (ω (n + 1)).2)]
    obtain ⟨μ_next, hμ_next⟩ := hstep (n + 1)
    exact resolve_label_tsum_eq adv hres
      (ρ (rand_obs_history adv.obs ω (n + 1))
        (adv.obs.observe_state (ω (n + 1)).1))
      (ω (n + 1)).1
      (fun ls hmem => hewf (n + 1) ls hmem)
      (ω (n + 1)).2 μ_next hμ_next
  · intro s' hne
    have : ∀ a, (ω (n + 1)).1 = s' ∧ (ω (n + 1)).2 = resolve_label adv s' a ↔ False := by
      intro a; exact ⟨fun ⟨h, _⟩ => hne h.symm, False.elim⟩
    simp [this]

/-- Base case: the execution measure of the 0-cylinder equals
    `rand_cone_prob ... 0`. -/
theorem rand_exec_measure_cylinder_zero [Inhabited State] [Inhabited Label]
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    (ρ : RandomisedStrategy SS LS)
    (s₀ : State) (ω : ℕ → State × Label)
    (hewf : adv.rand_exec_well_formed ρ ω)
    (hstep : ∀ k, ∃ μ, adv.sys.step (ω k).1 (ω k).2 μ) :
    rand_exec_measure adv hres ρ s₀ (rand_state_cylinder ω 0) =
    rand_cone_prob adv ρ s₀ ω 0 := by
  classical
  simp only [rand_exec_measure, rand_cone_prob, ProbabilityTheory.Kernel.trajMeasure]
  set κ := fun n => rand_transition_kernel adv hres ρ n with hκ_def
  set S : Set ((i : ↥(Finset.Iic 0)) → (fun _ => State × Label) ↑i) :=
    {h | h ⟨0, Finset.mem_Iic.mpr le_rfl⟩ = ω 0}
  have hms : MeasurableSet S :=
    (measurableSet_singleton _).preimage (measurable_pi_apply _)
  -- The 0-cylinder is cylinder (Iic 0) S
  have hset : rand_state_cylinder ω 0 = MeasureTheory.cylinder (Finset.Iic 0) S := by
    ext ω'; simp [rand_state_cylinder, MeasureTheory.cylinder, Finset.restrict, S]
  rw [MeasureTheory.Measure.bind_apply
    (hset ▸ hms.preimage (Finset.measurable_restrict _))
    (ProbabilityTheory.Kernel.measurable _).aemeasurable]
  -- Each integrand: (traj κ 0) x₀ (cylinder) = dirac indicator
  have htraj_eval : ∀ x₀ : (↥(Finset.Iic 0) → State × Label),
      ((ProbabilityTheory.Kernel.traj κ 0) x₀) (rand_state_cylinder ω 0) =
      S.indicator (fun _ => 1) x₀ := by
    intro x₀
    change (ProbabilityTheory.Kernel.trajFun κ 0 x₀) (rand_state_cylinder ω 0) = _
    rw [hset]
    -- trajFun = trajContent.measure, and cylinder ∈ measurableCylinders
    unfold ProbabilityTheory.Kernel.trajFun
    have hmem := MeasureTheory.cylinder_mem_measurableCylinders (α := fun _ => State × Label) (Finset.Iic 0) S hms
    rw [MeasureTheory.AddContent.measure_eq _
      MeasureTheory.isSetSemiring_measurableCylinders
      MeasureTheory.generateFrom_measurableCylinders.symm _ hmem]
    rw [@ProbabilityTheory.Kernel.trajContent_cylinder
      (fun _ => State × Label) _ κ _ (a := 0) (b := 0) _ hms x₀,
      ProbabilityTheory.Kernel.partialTraj_self,
      ProbabilityTheory.Kernel.id_apply,
      MeasureTheory.Measure.dirac_apply' _ hms]
    rfl
  rw [MeasureTheory.lintegral_congr htraj_eval,
    MeasureTheory.lintegral_indicator_const hms, one_mul]
  -- Goal: (map piUnique.symm μ₀) S = if (ω 0).1 = s₀ then ... else 0
  -- Compute map: (map piUnique.symm μ₀) S = μ₀ (piUnique.symm ⁻¹' S)
  rw [MeasureTheory.Measure.map_apply (MeasurableEquiv.piUnique _).symm.measurable hms]
  -- piUnique.symm ⁻¹' S = {ω 0}
  have hpreimage : (MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic 0) => State × Label)).symm ⁻¹' S =
      {ω 0} := by
    ext v; simp [S, MeasurableEquiv.piUnique]
  rw [hpreimage, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  -- Goal: (rand_initial_pmf adv ρ s₀) (ω 0) = if (ω 0).1 = s₀ then ... else 0
  simp only [rand_initial_pmf, PMF.bind_apply, PMF.pure_apply]
  -- Split on whether (ω 0).1 = s₀
  split_ifs with hs
  · -- Case (ω 0).1 = s₀
    -- Simplify ω 0 = (s₀, resolve ...) to (ω 0).2 = resolve ...
    simp_rw [show ∀ a, (ω 0 = (s₀, resolve_label adv s₀ a)) =
        (resolve_label adv s₀ a = (ω 0).2) from fun a => by
      rw [Prod.ext_iff]; simp [hs, eq_comm]]
    obtain ⟨μ₀, hμ₀⟩ := hstep 0
    have hewf_0 : ∀ ls, ls ∈ (ρ [] (adv.obs.observe_state s₀)).support →
        ∃ l μ, adv.obs.observe_label s₀ l = ls ∧ adv.sys.step s₀ l μ := by
      intro ls hmem
      have h0 : rand_obs_history adv.obs ω 0 = [] := by simp [rand_obs_history]
      have hmem' : ls ∈ (ρ (rand_obs_history adv.obs ω 0)
          (adv.obs.observe_state (ω 0).1)).support := by rwa [h0, hs]
      obtain ⟨l, μ, hobs, hstep'⟩ := hewf 0 ls hmem'
      exact ⟨l, μ, by rwa [hs] at hobs, by rwa [hs] at hstep'⟩
    exact resolve_label_tsum_eq adv hres
      (ρ [] (adv.obs.observe_state s₀)) s₀
      hewf_0 (ω 0).2 μ₀ (hs ▸ hμ₀)
  · -- Case (ω 0).1 ≠ s₀: every summand is 0
    apply ENNReal.tsum_eq_zero.mpr
    intro ls
    simp only [mul_ite, mul_one, mul_zero]
    refine if_neg (fun h => hs ?_)
    exact (Prod.ext_iff.mp h).1

/-- Decomposition: the measure of the `(n+1)`-cylinder equals the measure
    of the `n`-cylinder times the kernel's transition probability.
    Mechanical port of `exec_measure_cylinder_succ` from ProbExec.lean. -/
theorem rand_exec_measure_cylinder_succ [Inhabited State] [Inhabited Label]
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    (ρ : RandomisedStrategy SS LS)
    (s₀ : State) (ω : ℕ → State × Label)
    (n : ℕ) :
    rand_exec_measure adv hres ρ s₀ (rand_state_cylinder ω (n + 1)) =
    rand_exec_measure adv hres ρ s₀ (rand_state_cylinder ω n) *
      (rand_transition_kernel adv hres ρ n)
        (fun i => ω ↑i) {ω (n + 1)} := by
  classical
  let μ := rand_exec_measure adv hres ρ s₀
  let κ := fun n => rand_transition_kernel adv hres ρ n
  -- Use the Markov property
  have hmarkov :=
    @ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (fun _ => State × Label) _ κ _
      (rand_initial_pmf adv ρ s₀).toMeasure _ (a := n)
  -- Decompose the cylinder set
  set S_prefix :=
    {h : (i : ↥(Finset.Iic n)) → State × Label | ∀ i, h i = ω ↑i}
  set sl_next := ω (n + 1)
  have hcyl_decomp : rand_state_cylinder ω (n + 1) =
      (fun x : ℕ → State × Label =>
        (Preorder.frestrictLe n x, x (n + 1))) ⁻¹'
        (S_prefix ×ˢ {sl_next}) := by
    ext ω'
    simp only [rand_state_cylinder, Set.mem_setOf_eq, Set.mem_preimage,
      Set.mem_prod, Set.mem_singleton_iff, S_prefix, sl_next,
      Preorder.frestrictLe]
    constructor
    · intro h
      exact ⟨fun i => h ↑i (Nat.le_succ_of_le (Finset.mem_Iic.mp i.prop)),
        h (n + 1) le_rfl⟩
    · intro ⟨h1, h2⟩ k hk
      rcases Nat.eq_or_lt_of_le hk with rfl | hlt
      · exact h2
      · exact h1 ⟨k, Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp hlt)⟩
  have hcyl_n : rand_state_cylinder ω n =
      (Preorder.frestrictLe n) ⁻¹' S_prefix := by
    ext ω'
    simp only [rand_state_cylinder, Set.mem_setOf_eq, Set.mem_preimage,
      S_prefix, Preorder.frestrictLe]
    exact ⟨fun h i => h ↑i (Finset.mem_Iic.mp i.prop),
      fun h k hk => h ⟨k, Finset.mem_Iic.mpr hk⟩⟩
  rw [show rand_exec_measure adv hres ρ s₀ = μ from rfl, hcyl_decomp]
  rw [← MeasureTheory.Measure.map_apply (by measurability) (by measurability)]
  simp only [μ, rand_exec_measure]; rw [← hmarkov]
  rw [MeasureTheory.Measure.compProd_apply (by measurability)]
  rw [hcyl_n,
    ← MeasureTheory.Measure.map_apply (by measurability) (by measurability)]
  have hsection : ∀ a : (↥(Finset.Iic n) → State × Label),
      (κ n) a (Prod.mk a ⁻¹' (S_prefix ×ˢ {sl_next})) =
      S_prefix.indicator (fun a => (κ n) a {sl_next}) a := by
    intro a
    simp only [Set.indicator_apply]
    split
    · next h =>
        congr 1; ext s
        simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff]
        exact ⟨fun ⟨_, hs⟩ => hs, fun hs => ⟨h, hs⟩⟩
    · next h =>
        have : Prod.mk a ⁻¹' (S_prefix ×ˢ {sl_next}) = ∅ := by
          ext s
          simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff,
            Set.mem_empty_iff_false, iff_false]
          exact fun ⟨ha, _⟩ => h ha
        rw [this, MeasureTheory.measure_empty]
  simp_rw [hsection]
  have hsingleton : S_prefix =
      {fun i : ↥(Finset.Iic n) => ω ↑i} := by
    ext h; simp [S_prefix, funext_iff]
  simp_rw [hsingleton, Set.indicator_singleton, Pi.single_apply]
  set ω_prefix : (↥(Finset.Iic n) → State × Label) := fun i => ω ↑i
  set c := (κ n ω_prefix) {sl_next}
  have hind : ∀ a, (if a = ω_prefix then c else 0) =
      ({ω_prefix} : Set _).indicator (fun _ => c) a := by
    intro a; simp [Set.indicator_apply]
  simp_rw [hind]
  rw [MeasureTheory.lintegral_indicator_const (measurableSet_singleton _),
    mul_comm]

/-- **Main theorem**: the execution measure of a cylinder set equals
    the randomised cone measure. This identifies the inductively defined
    `rand_cone_prob` with the measure-theoretic cylinder set probability.

    Proof by induction on `n`:
    - **Base**: uses `rand_exec_measure_cylinder_zero`
    - **Step**: decomposes the `(n+1)`-cylinder and applies
      `rand_step_distribution_eq_step_prob` via `resolve_label_tsum_eq`. -/
theorem rand_exec_measure_cylinder [Inhabited State] [Inhabited Label]
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    (ρ : RandomisedStrategy SS LS)
    (s₀ : State) (ω : ℕ → State × Label)
    (hewf : adv.rand_exec_well_formed ρ ω)
    (hstep : ∀ k, ∃ μ, adv.sys.step (ω k).1 (ω k).2 μ)
    (n : ℕ) :
    rand_exec_measure adv hres ρ s₀ (rand_state_cylinder ω n) =
    rand_cone_prob adv ρ s₀ ω n := by
  induction n with
  | zero => exact rand_exec_measure_cylinder_zero adv hres ρ s₀ ω hewf hstep
  | succ n ih =>
    rw [rand_exec_measure_cylinder_succ adv hres ρ s₀ ω n, ih,
      rand_cone_prob_succ, rand_transition_kernel_singleton,
      rand_step_distribution_eq_step_prob adv hres ρ ω hewf hstep n _
        (fun i => rfl)]

/-! ## Probabilistic Traces for Randomised Strategies

    The **trace** of an execution is the subsequence of external labels.
    Since the measure space is `ℕ → State × Label`, labels are directly
    available — no reconstruction needed (unlike `ProbExec.lean` where
    `reconstruct_labels` recovers labels from the state sequence).

    The **randomised probabilistic trace** is the pushforward of
    `rand_exec_measure` under the trace extraction function. -/

omit [MeasurableSpace State] [MeasurableSingletonClass State] [Countable State]
  [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label] in
/-- Extract the label sequence from a state–label sequence. -/
def rand_proj_labels (ω : ℕ → State × Label) : ℕ → Label :=
  fun n => (ω n).2

/-- The trace function for randomised strategies: extract labels from
    the state–label sequence, then take the external subsequence.
    No label reconstruction is needed since labels are stored directly. -/
noncomputable def rand_trace_fn [Inhabited Label]
    (lab : LTS.Labelling Label)
    (ω : ℕ → State × Label) : ℕ → Label :=
  LTS.externalSubseq lab (rand_proj_labels ω)

omit [MeasurableSingletonClass State] [Countable State] [MeasurableSingletonClass Label]
  [Countable Label] in
/-- The label projection `ℕ → State × Label → ℕ → Label` is measurable. -/
theorem rand_proj_labels_measurable :
    Measurable (rand_proj_labels : (ℕ → State × Label) → (ℕ → Label)) :=
  measurable_pi_lambda _ fun n => measurable_snd.comp (measurable_pi_apply n)

omit [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label] in
/-- Each coordinate of `externalSubseq` is measurable: `fun labels => externalSubseq lab labels n`
    factors through the identity on `ℕ → Label` and produces a value in `Label` (countable).
    Since `Label` is countable + MSC, every set in `Label` is measurable, so it suffices
    to show preimages of singletons are measurable. These are countable unions of
    cylinder sets in `ℕ → Label`. -/
private theorem externalSubseq_measurable' [Inhabited Label]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]
    (lab : LTS.Labelling Label) :
    Measurable (LTS.externalSubseq lab) := by
  classical
  apply measurable_pi_lambda
  intro n s _
  -- s ⊆ Label, express preimage as countable union over l ∈ s
  have : (fun labels => LTS.externalSubseq lab labels n) ⁻¹' s =
      ⋃ l ∈ s, (fun labels => LTS.externalSubseq lab labels n) ⁻¹' {l} := by ext x; simp
  rw [this]
  -- Express preimage as countable union over positions m where labels m = l
  -- and m is the n-th external position
  refine MeasurableSet.biUnion s.to_countable fun l _ => ?_
  -- Helper: restriction to Fin (m+1) is measurable, and all subsets of the
  -- countable type Fin (m+1) → Label are measurable.
  have hfactor : ∀ (T : Set (ℕ → Label)),
      (∃ m, ∃ S : Set (Fin (m + 1) → Label),
        T = (fun f : ℕ → Label => fun i : Fin (m + 1) => f i.val) ⁻¹' S) →
      MeasurableSet T := by
    rintro T ⟨m, S, rfl⟩
    exact (S.to_countable.measurableSet).preimage
      (measurable_pi_lambda _ fun i => measurable_pi_apply i.val)
  -- Decompose {labels | externalSubseq lab labels n = l}
  -- using externalSubseq_eq and externalSubseq_default
  have hdecomp : (fun labels => LTS.externalSubseq lab labels n) ⁻¹' {l} =
      (⋃ m, {labels : ℕ → Label | LTS.externalCount lab labels m = n ∧
        lab.is_external (labels m) = true ∧ labels m = l}) ∪
      (if l = lab.tau
       then {labels | ¬∃ m, LTS.externalCount lab labels m = n ∧
              lab.is_external (labels m) = true}
       else ∅) := by
    ext labels
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union,
      Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · intro heq
      by_cases hex : ∃ m, LTS.externalCount lab labels m = n ∧
          lab.is_external (labels m) = true
      · left; obtain ⟨m, hm, hext⟩ := hex
        exact ⟨m, hm, hext, (LTS.externalSubseq_eq lab labels hm hext).symm.trans heq⟩
      · right; rw [LTS.externalSubseq_default lab labels n hex] at heq
        rw [if_pos heq.symm]; exact hex
    · intro h; rcases h with ⟨m, hm, hext, hlm⟩ | hneg
      · exact (LTS.externalSubseq_eq lab labels hm hext).trans hlm
      · split at hneg
        · rw [LTS.externalSubseq_default lab labels n hneg]; exact ‹l = lab.tau›.symm
        · simp at hneg
  rw [hdecomp]
  apply MeasurableSet.union
  · -- ⋃ m, {labels | externalCount ... m = n ∧ is_external (labels m) ∧ labels m = l}
    apply MeasurableSet.iUnion; intro m
    -- {labels | externalCount lab labels m = n ∧ is_external (labels m) ∧ labels m = l}
    -- = (fun labels =>
    -- (externalCount lab labels m, is_external (labels m), labels m)) ⁻¹' {(n,true,l)}
    -- This function is measurable: codomain ℕ × Bool × Label is countable
    show MeasurableSet {labels | LTS.externalCount lab labels m = n ∧ _}
    have : {labels : ℕ → Label | LTS.externalCount lab labels m = n ∧
        lab.is_external (labels m) = true ∧ labels m = l} =
        (fun labels : ℕ → Label =>
          (LTS.externalCount lab labels m, lab.is_external (labels m), labels m)) ⁻¹'
        {(n, true, l)} := by
      ext; simp [Set.mem_preimage, Set.mem_singleton_iff]
    rw [this]
    -- The set factors through Fin (m+1) → Label (depends on labels 0..m only)
    -- Factors through Fin (m+1) → Label: depends on labels 0..m
    -- externalCount lab labels m uses labels 0..m-1, is_external and labels m use labels m
    refine hfactor _ ⟨m, {h | LTS.externalCount lab (fun i =>
        if hi : i ≤ m then h ⟨i, Nat.lt_succ_of_le hi⟩ else default) m = n ∧
      lab.is_external (h ⟨m, Nat.lt_succ_iff.mpr le_rfl⟩) = true ∧
      h ⟨m, Nat.lt_succ_iff.mpr le_rfl⟩ = l}, ?_⟩
    ext labels; show _ ↔ _
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff, Prod.mk.injEq]
    -- Key: externalCount lab (pad (restrict labels)) m = externalCount lab labels m
    -- because externalCount only reads positions < m
    have hec : LTS.externalCount lab
        (fun i => if _ : i ≤ m then labels i else default) m =
        LTS.externalCount lab labels m := by
      unfold LTS.externalCount; congr 1; apply List.filter_congr
      intro i hi; simp only [List.mem_range] at hi
      congr 1; exact dif_pos hi.le
    simp only [hec];
  · -- if l = tau: complement of ⋃ m, {labels | externalCount ... m = n ∧ is_external ...}
    split
    · -- compl of ⋃ m, ...
      rw [show {labels : ℕ → Label | ¬∃ m, LTS.externalCount lab labels m = n ∧
          lab.is_external (labels m) = true} =
        (⋃ m, {labels : ℕ → Label | LTS.externalCount lab labels m = n ∧
          lab.is_external (labels m) = true})ᶜ from by ext; simp]
      exact (MeasurableSet.iUnion fun m =>
        hfactor _ ⟨m, {h | LTS.externalCount lab (fun i =>
            if hi : i ≤ m then h ⟨i, Nat.lt_succ_of_le hi⟩ else default) m = n ∧
          lab.is_external (h ⟨m, Nat.lt_succ_iff.mpr le_rfl⟩) = true}, by
          ext labels; show _ ↔ _
          simp only [Set.mem_preimage, Set.mem_setOf_eq]
          have hec : LTS.externalCount lab
              (fun i => if _ : i ≤ m then labels i else default) m =
              LTS.externalCount lab labels m := by
            unfold LTS.externalCount; congr 1; apply List.filter_congr
            intro i hi; simp only [List.mem_range] at hi
            congr 1; exact dif_pos hi.le
          simp only [hec]⟩).compl
    · exact MeasurableSet.empty

omit [MeasurableSingletonClass State] [Countable State] in
/-- The randomised trace function is measurable: it is the composition of
    the measurable label projection with the measurable `externalSubseq`. -/
theorem rand_trace_fn_measurable [Inhabited Label]
    (lab : LTS.Labelling Label) :
    Measurable (rand_trace_fn lab : (ℕ → State × Label) → (ℕ → Label)) :=
  (externalSubseq_measurable' lab).comp rand_proj_labels_measurable

/-- The probabilistic trace for a randomised strategy: the pushforward
    of `rand_exec_measure` under the trace function. This is a probability
    measure on `ℕ → Label` representing the distribution over external
    label sequences. -/
noncomputable def rand_trace_measure [Inhabited State] [Inhabited Label]
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    (ρ : RandomisedStrategy SS LS) (lab : LTS.Labelling Label)
    (s₀ : State) : MeasureTheory.Measure (ℕ → Label) :=
  MeasureTheory.Measure.map (rand_trace_fn lab)
    (rand_exec_measure adv hres ρ s₀)

/-- The randomised probabilistic trace is a well-defined probability measure. -/
noncomputable instance rand_trace_measure_prob [Inhabited State] [Inhabited Label]
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    (ρ : RandomisedStrategy SS LS) (lab : LTS.Labelling Label)
    (s₀ : State) :
    MeasureTheory.IsProbabilityMeasure (rand_trace_measure adv hres ρ lab s₀) := by
  unfold rand_trace_measure
  exact MeasureTheory.Measure.isProbabilityMeasure_map
    (rand_trace_fn_measurable lab).aemeasurable

/-! ## Deterministic Strategies as a Special Case

    When the randomised strategy is `σ.toRandomised`, the randomised
    framework reduces to the deterministic framework from `ProbExec.lean`. -/

omit [MeasurableSpace State] [MeasurableSingletonClass State] [Countable State]
  [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label] in
/-- The randomised observation history applied to a state-label sequence
    `(e.states, e.labels)` equals the deterministic observation history. -/
theorem rand_obs_history_eq_obs_history (obs : Observation State Label SS LS)
    (e : LTS.Execution State Label) (k : ℕ) :
    rand_obs_history obs (fun n => (e.states n, e.labels n)) k =
    obs_history obs e k := by
  simp [rand_obs_history, obs_history]

omit [MeasurableSpace State] [MeasurableSingletonClass State] [Countable State]
  [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label] in
/-- Under a deterministic strategy lifted to `toRandomised`, the randomised
    cone measure equals the deterministic cone measure. -/
theorem rand_cone_prob_eq_cone_prob [Inhabited Label]
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    (σ : Strategy SS LS) (s₀ : State)
    (e : LTS.Execution State Label)
    (hcons : adv.consistent σ e)
    (hstep : ∀ k, ∃ μ, adv.sys.step (e.states k) (e.labels k) μ)
    (n : ℕ) :
    rand_cone_prob adv σ.toRandomised s₀ (fun k => (e.states k, e.labels k)) n =
    cone_prob adv σ s₀ e n := by
  set ω : ℕ → State × Label := fun k => (e.states k, e.labels k) with hω_def
  induction n with
  | zero =>
    classical
    simp only [rand_cone_prob, cone_prob]
    split_ifs with hs
    · -- hs : e.states 0 = s₀
      -- Goal: (σ.toRandomised [] (obs s₀))(observe_label(s₀, e.labels 0)) = 1
      have hcons_0 := (consistent_iff_forall_consistent_at adv σ e).mp hcons 0
      simp only [consistent_at, prescribed_signal, obs_history, List.ofFn_zero] at hcons_0
      -- hcons_0 : observe_label(e.states 0, e.labels 0) = σ [] (obs(e.states 0))
      simp only [Strategy.toRandomised, PMF.pure_apply]
      -- Goal: if observe_label(s₀, e.labels 0) = σ [] (obs s₀) then 1 else 0 = 1
      -- Use hs to rewrite hcons_0 from e.states 0 to s₀
      have hs' : e.states 0 = s₀ := hs
      have : adv.obs.observe_label s₀ (e.labels 0) = σ [] (adv.obs.observe_state s₀) := by
        rwa [hs'] at hcons_0
      rw [if_pos this]
    · rfl
  | succ n ih =>
    rw [rand_cone_prob_succ, cone_prob_succ, ih]
    congr 1
    -- Need: rand_step_prob adv σ.toRandomised ω n = step_prob adv σ e n
    simp only [rand_step_prob, step_prob]
    -- Consistency at step n
    have hcons_n := (consistent_iff_forall_consistent_at adv σ e).mp hcons n
    rw [if_pos hcons_n]
    -- Both have the same dif condition
    obtain ⟨μn, hμn⟩ := hstep n
    rw [dif_pos ⟨μn, hμn⟩, dif_pos ⟨μn, hμn⟩]
    -- The choose values are the same existential, so by resolving both equal μn
    have hμ_eq : (⟨μn, hμn⟩ : ∃ μ, adv.sys.step (e.states n) (e.labels n) μ).choose
        (e.states (n + 1)) = μn (e.states (n + 1)) :=
      congr_fun (congr_arg DFunLike.coe
        (hres _ _ _ _ _ rfl (⟨μn, hμn⟩ : ∃ μ, adv.sys.step (e.states n) (e.labels n) μ).choose_spec
          hμn).2) _
    rw [hμ_eq]
    -- Scheduler factor: (PMF.pure (σ hist ss))(ls) where ls = σ hist ss by consistency
    simp only [Strategy.toRandomised, PMF.pure_apply]
    -- The scheduler factor evaluates to 1 because the label-signal matches
    have hcons_succ := (consistent_iff_forall_consistent_at adv σ e).mp hcons (n + 1)
    simp only [consistent_at, prescribed_signal] at hcons_succ
    rw [rand_obs_history_eq_obs_history]
    rw [if_pos hcons_succ]
    simp [mul_one]

/- The theorem `rand_exec_measure_cylinder_eq_exec_measure_cylinder` has been
   moved to ProbExec.lean where it can reference both `exec_measure` and
   `rand_exec_measure`. -/

omit [MeasurableSpace State] [MeasurableSingletonClass State] [Countable State]
  [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label] in
/-- Consistency and step existence for a deterministic strategy imply
    per-execution well-formedness for the lifted randomised strategy. -/
theorem rand_exec_well_formed_of_consistent [Inhabited Label]
    (adv : Adversary State Label SS LS)
    (σ : Strategy SS LS)
    (e : LTS.Execution State Label)
    (hcons : adv.consistent σ e)
    (hstep : ∀ k, ∃ μ, adv.sys.step (e.states k) (e.labels k) μ) :
    adv.rand_exec_well_formed σ.toRandomised (fun k => (e.states k, e.labels k)) := by
  intro k ls hmem
  simp only [Strategy.toRandomised, PMF.mem_support_pure_iff] at hmem
  have hcons_k := (consistent_iff_forall_consistent_at adv σ e).mp hcons k
  rw [rand_obs_history_eq_obs_history] at hmem
  simp only [consistent_at, prescribed_signal] at hcons_k
  rw [← hcons_k] at hmem
  obtain ⟨μk, hμk⟩ := hstep k
  exact ⟨e.labels k, μk, hmem.symm, hμk⟩

end PLTS
