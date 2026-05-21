import Leslie_LTS.Framework.Adversary
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-! # Probabilistic Executions

    Given a PLTS, an initial state, and a strategy that resolves all
    nondeterminism (`strategy_resolving`), we define the **cone measure**:
    the probability of a finite execution prefix (cylinder set).

    The cone measure is defined inductively on the prefix length:

    - **Base**: `cone_prob ... 0 = if e.states 0 = s₀ then 1 else 0`
    - **Step**: `cone_prob ... (n+1) = cone_prob ... n * step_prob ... n`

    where `step_prob` gives the probability of the transition at step `n`:
    the PMF value `μ(e.states (n+1))` when the label matches the scheduler's
    prescription and a valid transition exists, or 0 otherwise.

    After resolving all nondeterminism, the only remaining randomness is
    the sampling from distributions — the system behaves as a Markov chain.

    ## Extension to a Probability Measure

    We construct a `MeasureTheory.Measure` on infinite state sequences
    `ℕ → State` via the Ionescu-Tulcea theorem (`Kernel.trajMeasure`).
    The key steps are:

    1. **Reconstruct labels**: Under a resolving strategy, labels are
       deterministic functions of the state history.
    2. **Build Markov kernels**: At each step, the resolving condition
       gives a unique distribution, yielding a kernel from state histories
       to next states.
    3. **Apply Ionescu-Tulcea**: `Kernel.trajMeasure` produces the measure.
    4. **Identify with `cone_prob`**: The cylinder set measure equals
       `cone_prob` via `Kernel.trajContent_cylinder`.
-/

namespace PLTS

variable {State : Type u} {Label : Type v}
variable {SS : Type w} {LS : Type x}

/-! ## Observation History -/

/-- The observation history of the first `k` steps of an execution:
    the list of `(state-signal, label-signal)` pairs seen so far.
    This is the information available to the strategy at step `k`. -/
def obs_history (obs : Observation State Label SS LS)
    (e : LTS.Execution State Label) (k : ℕ) : List (SS × LS) :=
  List.ofFn fun i : Fin k =>
    (obs.observe_state (e.states i.val),
     obs.observe_label (e.states i.val) (e.labels i.val))

/-- The label-signal prescribed by a strategy at step `k`. -/
def prescribed_signal (adv : Adversary State Label SS LS)
    (σ : Strategy SS LS) (e : LTS.Execution State Label) (k : ℕ) : LS :=
  σ (obs_history adv.obs e k) (adv.obs.observe_state (e.states k))

/-- An execution is consistent with a strategy at step `k` iff the
    observed label-signal equals the prescribed one.
    This is the pointwise version of `Adversary.consistent`. -/
def consistent_at (adv : Adversary State Label SS LS)
    (σ : Strategy SS LS) (e : LTS.Execution State Label) (k : ℕ) : Prop :=
  adv.obs.observe_label (e.states k) (e.labels k) = prescribed_signal adv σ e k

theorem consistent_iff_forall_consistent_at (adv : Adversary State Label SS LS)
    (σ : Strategy SS LS) (e : LTS.Execution State Label) :
    adv.consistent σ e ↔ ∀ k, consistent_at adv σ e k := by
  simp only [Adversary.consistent, consistent_at, prescribed_signal, obs_history]

/-! ## Step Probability -/

open Classical in
/-- The probability of the transition at step `k` of an execution under
    strategy `σ`. Returns `μ(e.states (k+1))` where `μ` is a distribution
    for the transition at `(e.states k, e.labels k)`, if the label matches
    the scheduler's prescription and a valid transition exists.
    Returns 0 otherwise.

    Under `observation_resolving`, the distribution `μ` is unique,
    so the result is independent of classical choice. -/
noncomputable def step_prob (adv : Adversary State Label SS LS)
    (σ : Strategy SS LS) (e : LTS.Execution State Label) (k : ℕ) : ENNReal :=
  if consistent_at adv σ e k then
    if h : ∃ μ, adv.sys.step (e.states k) (e.labels k) μ then
      h.choose (e.states (k + 1))
    else 0
  else 0

/-- Under the resolving condition, `step_prob` equals the PMF value for
    the actual transition distribution, independently of classical choice. -/
theorem step_prob_eq_of_resolving (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    (σ : Strategy SS LS) (e : LTS.Execution State Label) (k : ℕ)
    (μ : PMF State)
    (hstep : adv.sys.step (e.states k) (e.labels k) μ)
    (hcons : consistent_at adv σ e k) :
    step_prob adv σ e k = μ (e.states (k + 1)) := by
  classical
  unfold step_prob
  rw [if_pos hcons, dif_pos ⟨μ, hstep⟩]
  exact congr_fun (congr_arg DFunLike.coe
    (hres _ _ _ _ _ rfl (Exists.choose_spec ⟨μ, hstep⟩) hstep).2) _

/-- `step_prob` is zero when the label is inconsistent with the strategy. -/
theorem step_prob_eq_zero_of_inconsistent (adv : Adversary State Label SS LS)
    (σ : Strategy SS LS) (e : LTS.Execution State Label) (k : ℕ)
    (hinc : ¬consistent_at adv σ e k) :
    step_prob adv σ e k = 0 := by
  classical
  unfold step_prob
  rw [if_neg hinc]

/-- `step_prob` is zero when no transition exists. -/
theorem step_prob_eq_zero_of_no_step (adv : Adversary State Label SS LS)
    (σ : Strategy SS LS) (e : LTS.Execution State Label) (k : ℕ)
    (hno : ¬∃ μ, adv.sys.step (e.states k) (e.labels k) μ) :
    step_prob adv σ e k = 0 := by
  classical
  unfold step_prob
  simp [dif_neg hno]

/-! ## Cone Measure -/

open Classical in
/-- The **cone measure**: probability that an execution matches the given
    prefix of length `n`, under strategy `σ` from initial state `s₀`.

    - At length 0: 1 if the initial state is `s₀`, else 0.
    - At length `n + 1`: the cone measure at length `n` times the
      step probability at step `n`. -/
noncomputable def cone_prob (adv : Adversary State Label SS LS)
    (σ : Strategy SS LS) (s₀ : State)
    (e : LTS.Execution State Label) : ℕ → ENNReal
  | 0 => if e.states 0 = s₀ then 1 else 0
  | n + 1 => cone_prob adv σ s₀ e n * step_prob adv σ e n

theorem cone_prob_succ (adv : Adversary State Label SS LS)
    (σ : Strategy SS LS) (s₀ : State) (e : LTS.Execution State Label) (n : ℕ) :
    cone_prob adv σ s₀ e (n + 1) = cone_prob adv σ s₀ e n * step_prob adv σ e n :=
  rfl

/-- The cone measure is zero if the initial state doesn't match. -/
theorem cone_prob_eq_zero_of_ne (adv : Adversary State Label SS LS)
    (σ : Strategy SS LS) (s₀ : State) (e : LTS.Execution State Label)
    (h : e.states 0 ≠ s₀) (n : ℕ) :
    cone_prob adv σ s₀ e n = 0 := by
  induction n with
  | zero =>
    classical
    exact if_neg h
  | succ n ih => rw [cone_prob_succ, ih, zero_mul]

/-- The cone measure is zero if the execution is inconsistent with
    the strategy at any step before `n`. -/
theorem cone_prob_eq_zero_of_inconsistent (adv : Adversary State Label SS LS)
    (σ : Strategy SS LS) (s₀ : State) (e : LTS.Execution State Label)
    (n : ℕ) {k : ℕ} (hk : k < n) (hinc : ¬consistent_at adv σ e k) :
    cone_prob adv σ s₀ e n = 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [cone_prob_succ]
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hk) with rfl | hlt
    · rw [step_prob_eq_zero_of_inconsistent _ _ _ _ hinc, mul_zero]
    · rw [ih hlt, zero_mul]

/-! ## Phase 1: Reconstruct Labels from State Histories

    Under a resolving strategy, the label at each step is a deterministic
    function of the state prefix. Given an infinite state sequence
    `states : ℕ → State`, we reconstruct `labels : ℕ → Label` inductively:
    at step `k`, the scheduler prescribes a label-signal from the observation
    of the prefix and the previously reconstructed labels, and the resolving
    condition gives a unique label. -/

open Classical in
/-- Given a resolving adversary, a strategy, and an infinite state sequence,
    reconstruct the unique label at each step that the strategy would schedule.
    Defined by well-founded recursion: the label at step `k` depends only
    on the labels at steps `< k`.

    Returns an arbitrary label if no matching transition exists at a step. -/
noncomputable def reconstruct_labels (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) [Inhabited Label]
    (σ : Strategy SS LS) (states : ℕ → State) (k : ℕ) : Label :=
  let labels_lt : Fin k → Label := fun ⟨i, _⟩ =>
    reconstruct_labels adv hres σ states i
  let hist : List (SS × LS) := List.ofFn fun i : Fin k =>
    (adv.obs.observe_state (states i.val),
     adv.obs.observe_label (states i.val) (labels_lt i))
  let ls := σ hist (adv.obs.observe_state (states k))
  if hex : ∃ l, ∃ μ, adv.obs.observe_label (states k) l = ls ∧
      adv.sys.step (states k) l μ then
    hex.choose
  else
    default
termination_by k

/-- The execution built from a state sequence and reconstructed labels. -/
noncomputable def reconstructed_exec (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) [Inhabited Label]
    (σ : Strategy SS LS) (states : ℕ → State) : LTS.Execution State Label where
  states := states
  labels := reconstruct_labels adv hres σ states

/-- `reconstruct_labels` on a padded history that agrees with an execution's
    states produces the same labels as the execution, under resolving + consistency.
    This combines locality (only states ≤ k matter) with correctness
    (`reconstruct_labels_eq`), avoiding the need to compare `Exists.choose`
    on propositionally-equal-but-distinct existentials. -/
theorem reconstruct_labels_pad (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) [Inhabited Label]
    (σ : Strategy SS LS)
    (e : LTS.Execution State Label)
    (hcons : adv.consistent σ e)
    (hstep : ∀ k, ∃ μ, adv.sys.step (e.states k) (e.labels k) μ)
    (states : ℕ → State) (m : ℕ)
    (hagree : ∀ j, j ≤ m → states j = e.states j)
    (k : ℕ) (hk : k ≤ m) :
    reconstruct_labels adv hres σ states k = e.labels k := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    have ih' : ∀ (i : Fin k), reconstruct_labels adv hres σ states ↑i = e.labels ↑i :=
      fun ⟨i, hi⟩ => ih i hi (le_trans hi.le hk)
    have hk_eq : states k = e.states k := hagree k hk
    have hi_eq : ∀ (i : Fin k), states (↑i : ℕ) = e.states ↑i :=
      fun ⟨i, hi⟩ => hagree i (le_trans hi.le hk)
    -- The observation history from `states` matches that from `e`
    have hhist : (List.ofFn fun i : Fin k =>
        (adv.obs.observe_state (states ↑i),
         adv.obs.observe_label (states ↑i) (reconstruct_labels adv hres σ states ↑i))) =
        obs_history adv.obs e k := by
      simp only [obs_history]; congr 1; ext ⟨i, hi'⟩
      · dsimp; rw [hi_eq ⟨i, hi'⟩]
      · dsimp; rw [hi_eq ⟨i, hi'⟩, ih' ⟨i, hi'⟩]
    -- The prescribed signal matches
    have hls : σ (List.ofFn fun i : Fin k =>
        (adv.obs.observe_state (states ↑i),
         adv.obs.observe_label (states ↑i) (reconstruct_labels adv hres σ states ↑i)))
        (adv.obs.observe_state (states k)) =
      prescribed_signal adv σ e k := by
      simp only [prescribed_signal, hhist, hk_eq]
    -- Unfold and use the resolving condition
    unfold reconstruct_labels
    dsimp only []
    have hcons_k := (consistent_iff_forall_consistent_at adv σ e).mp hcons k
    obtain ⟨μ, hμ⟩ := hstep k
    -- e.labels k is a witness: same signal (by hls + hcons_k) and valid step (by hk_eq + hμ)
    have hμ' : adv.sys.step (states k) (e.labels k) μ := hk_eq ▸ hμ
    have hsig_e : adv.obs.observe_label (states k) (e.labels k) =
        σ (List.ofFn fun i : Fin k =>
          (adv.obs.observe_state (states ↑i),
           adv.obs.observe_label (states ↑i) (reconstruct_labels adv hres σ states ↑i)))
          (adv.obs.observe_state (states k)) := by
      have h1 : adv.obs.observe_label (e.states k) (e.labels k) =
          prescribed_signal adv σ e k := hcons_k
      rw [← hk_eq] at h1; rw [h1, ← hls]
    have hex : ∃ l, ∃ μ, adv.obs.observe_label (states k) l =
        σ (List.ofFn fun i : Fin k =>
          (adv.obs.observe_state (states ↑i),
           adv.obs.observe_label (states ↑i) (reconstruct_labels adv hres σ states ↑i)))
          (adv.obs.observe_state (states k)) ∧
        adv.sys.step (states k) l μ :=
      ⟨e.labels k, μ, hsig_e, hμ'⟩
    rw [dif_pos hex]
    -- hex.choose has the same signal as e.labels k, and both have valid steps
    obtain ⟨μ'', hobs', hstep'⟩ := hex.choose_spec
    have hsig : adv.obs.observe_label (states k) hex.choose =
        adv.obs.observe_label (states k) (e.labels k) :=
      hobs'.trans hsig_e.symm
    exact (hres (states k) hex.choose (e.labels k) μ'' μ hsig hstep' hμ').1

/-- **Key lemma**: Under a resolving strategy, reconstructing labels from an
    execution's state sequence recovers the original labels.

    Proof by strong induction on `k`:
    - By IH, the reconstructed labels at all steps `< k` equal `e.labels`.
    - So the observation history in `reconstruct_labels` matches `obs_history adv.obs e k`.
    - The prescribed label-signal matches `prescribed_signal adv σ e k`.
    - By consistency, `e.labels k` matches this signal, and by `hstep`, a
      transition exists. So `reconstruct_labels` chooses some label `l'` with
      the same signal. By the resolving condition, `l' = e.labels k`. -/
theorem reconstruct_labels_eq (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) [Inhabited Label]
    (σ : Strategy SS LS)
    (e : LTS.Execution State Label)
    (hcons : adv.consistent σ e)
    (hstep : ∀ k, ∃ μ, adv.sys.step (e.states k) (e.labels k) μ)
    (k : ℕ) :
    reconstruct_labels adv hres σ e.states k = e.labels k := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    unfold reconstruct_labels
    -- By IH, the inner labels_lt matches e.labels
    have hlabels : ∀ (i : Fin k), reconstruct_labels adv hres σ e.states i.val = e.labels i.val :=
      fun ⟨i, hi⟩ => ih i hi
    -- So the observation history matches
    have hhist : (List.ofFn fun i : Fin k =>
        (adv.obs.observe_state (e.states i.val),
         adv.obs.observe_label (e.states i.val)
           (reconstruct_labels adv hres σ e.states i.val))) =
        (List.ofFn fun i : Fin k =>
          (adv.obs.observe_state (e.states i.val),
           adv.obs.observe_label (e.states i.val) (e.labels i.val))) := by
      congr 1; ext ⟨i, hi⟩
      · rfl
      · dsimp; rw [hlabels ⟨i, hi⟩]
    -- The prescribed signal matches
    have hls : σ (List.ofFn fun i : Fin k =>
        (adv.obs.observe_state (e.states i.val),
         adv.obs.observe_label (e.states i.val)
           (reconstruct_labels adv hres σ e.states i.val)))
        (adv.obs.observe_state (e.states k)) =
      prescribed_signal adv σ e k := by
      simp only [prescribed_signal, obs_history, hhist]
    -- e.labels k is a valid witness for the existential
    have hcons_k := (consistent_iff_forall_consistent_at adv σ e).mp hcons k
    obtain ⟨μ, hμ⟩ := hstep k
    -- The existential is satisfied
    have hex : ∃ l, ∃ μ, adv.obs.observe_label (e.states k) l =
        σ (List.ofFn fun i : Fin k =>
          (adv.obs.observe_state (e.states i.val),
           adv.obs.observe_label (e.states i.val)
             (reconstruct_labels adv hres σ e.states i.val)))
          (adv.obs.observe_state (e.states k)) ∧
        adv.sys.step (e.states k) l μ := by
      refine ⟨e.labels k, μ, ?_, hμ⟩
      rw [hls]; exact hcons_k
    rw [dif_pos hex]
    -- hex.choose is some l' with the same signal and a valid step
    obtain ⟨μ', hobs', hstep'⟩ := hex.choose_spec
    -- By resolving: l' and e.labels k have the same signal → l' = e.labels k
    have hsame_signal : adv.obs.observe_label (e.states k) hex.choose =
        adv.obs.observe_label (e.states k) (e.labels k) := by
      rw [hobs', hls]; exact hcons_k.symm
    exact (hres (e.states k) hex.choose (e.labels k) μ' μ hsame_signal hstep' hμ).1

/-! ## Phase 2: Build Markov Kernels

    At each step `n`, we build a Markov kernel from state histories
    `(i : Finset.Iic n) → State` to next states `State`. The kernel
    maps a history to the distribution determined by the scheduler
    and the resolving condition. -/

variable [MeasurableSpace State] [MeasurableSingletonClass State]
         [Countable State] [Inhabited Label]

/-- Extract an infinite state sequence from a finite history by padding
    with a default value. -/
noncomputable def pad_history [Inhabited State]
    (n : ℕ) (h : (i : ↥(Finset.Iic n)) → State) : ℕ → State :=
  fun k => if hk : k ≤ n then h ⟨k, Finset.mem_Iic.mpr hk⟩ else default

open Classical in
/-- The distribution at step `n` given a state history: reconstruct
    the labels, compute the scheduler's output, extract the unique
    distribution via the resolving condition. -/
noncomputable def step_distribution [Inhabited State]
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    (σ : Strategy SS LS)
    (n : ℕ) (h : (i : ↥(Finset.Iic n)) → State) : PMF State :=
  let states := pad_history n h
  let labels := reconstruct_labels adv hres σ states
  let e : LTS.Execution State Label := ⟨states, labels⟩
  let ls := prescribed_signal adv σ e n
  if hex : ∃ μ, ∃ l, adv.obs.observe_label (states n) l = ls ∧
      adv.sys.step (states n) l μ then
    hex.choose
  else
    PMF.pure (states n) -- fallback: Dirac at current state

/-- The Markov kernel at step `n`: given a state history of length `n+1`,
    return the distribution for the next state. -/
noncomputable def transition_kernel [Inhabited State]
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    (σ : Strategy SS LS)
    (n : ℕ) : ProbabilityTheory.Kernel ((i : ↥(Finset.Iic n)) → State) State :=
  ProbabilityTheory.Kernel.ofFunOfCountable
    (fun h => (step_distribution adv hres σ n h).toMeasure)

/-- The transition kernel is a Markov kernel (produces probability measures). -/
instance transition_kernel_markov [Inhabited State]
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    (σ : Strategy SS LS) (n : ℕ) :
    ProbabilityTheory.IsMarkovKernel (transition_kernel adv hres σ n) :=
  ProbabilityTheory.IsMarkovKernel.mk (fun h => by
    show MeasureTheory.IsProbabilityMeasure ((transition_kernel adv hres σ n) h)
    simp only [transition_kernel, ProbabilityTheory.Kernel.ofFunOfCountable]
    exact PMF.toMeasure.isProbabilityMeasure (step_distribution adv hres σ n h))

/-! ## Phase 3: Apply Ionescu-Tulcea

    Combine the initial Dirac measure at `s₀` with the transition kernels
    to produce a probability measure on infinite state sequences `ℕ → State`
    via `ProbabilityTheory.Kernel.trajMeasure`. -/

/-- The probability measure on infinite state sequences induced by a
    resolving strategy from initial state `s₀`. -/
noncomputable def exec_measure [Inhabited State]
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    (σ : Strategy SS LS) (s₀ : State) :
    MeasureTheory.Measure (ℕ → State) :=
  ProbabilityTheory.Kernel.trajMeasure
    (PMF.toMeasure (PMF.pure s₀))
    (fun n => transition_kernel adv hres σ n)

/-- The execution measure is a probability measure. -/
noncomputable instance exec_measure_prob [Inhabited State]
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    (σ : Strategy SS LS) (s₀ : State) :
    MeasureTheory.IsProbabilityMeasure (exec_measure adv hres σ s₀) :=
  ProbabilityTheory.Kernel.instIsProbabilityMeasureForallTrajMeasure

/-! ## Phase 4: Identify `cone_prob` with Cylinder Set Measure

    The cylinder set for a finite state prefix `(s₀, ..., sₙ)` is
    `{ω : ℕ → State | ω 0 = s₀ ∧ ... ∧ ω n = sₙ}`. We show that
    `exec_measure` applied to this cylinder equals `cone_prob`. -/

/-- The cylinder set determined by the first `n+1` states of an execution:
    all infinite state sequences agreeing on positions `0, ..., n`. -/
def state_cylinder (e : LTS.Execution State Label) (n : ℕ) :
    Set (ℕ → State) :=
  {ω | ∀ k, k ≤ n → ω k = e.states k}

omit [MeasurableSpace State] [MeasurableSingletonClass State] [Countable State]
  [Inhabited Label] in
/-- The cylinder set can be expressed as `MeasureTheory.cylinder`. -/
theorem state_cylinder_eq_cylinder (e : LTS.Execution State Label) (n : ℕ) :
    state_cylinder e n =
    MeasureTheory.cylinder (Finset.Iic n)
      {h | ∀ (i : ↥(Finset.Iic n)), h i = e.states ↑i} := by
  ext ω
  simp only [state_cylinder, MeasureTheory.cylinder, Set.mem_setOf_eq, Set.mem_preimage]
  constructor
  · intro h i
    exact h ↑i (Finset.mem_Iic.mp i.prop)
  · intro h k hk
    exact h ⟨k, Finset.mem_Iic.mpr hk⟩

/-- The transition kernel applied to a singleton equals the step distribution
    PMF value. This follows from `ofFunOfCountable` + `PMF.toMeasure`. -/
theorem transition_kernel_singleton [Inhabited State]
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    (σ : Strategy SS LS) (n : ℕ)
    (h : (i : ↥(Finset.Iic n)) → State) (s : State) :
    (transition_kernel adv hres σ n) h {s} =
    (step_distribution adv hres σ n h) s := by
  simp [transition_kernel, ProbabilityTheory.Kernel.ofFunOfCountable,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton s)]

omit [MeasurableSpace State] [MeasurableSingletonClass State] [Countable State] in
/-- The step distribution relates to step_prob for consistent executions
    when the history matches the execution prefix. -/
theorem step_distribution_eq_step_prob [Inhabited State]
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    (σ : Strategy SS LS)
    (e : LTS.Execution State Label)
    (hcons : adv.consistent σ e)
    (hstep : ∀ k, ∃ μ, adv.sys.step (e.states k) (e.labels k) μ)
    (n : ℕ) (h : (i : ↥(Finset.Iic n)) → State)
    (hh : ∀ (i : ↥(Finset.Iic n)), h i = e.states ↑i) :
    (step_distribution adv hres σ n h) (e.states (n + 1)) =
    step_prob adv σ e n := by
  classical
  -- Key: pad_history n h agrees with e.states on [0..n]
  have hpad : ∀ k, k ≤ n → pad_history n h k = e.states k := by
    intro k hk; simp [pad_history, hk, hh]
  -- reconstruct_labels on pad_history agrees with e.labels for k < n,
  -- because reconstruct_labels at step k only reads states at positions ≤ k
  have hrl : ∀ k, k < n →
      reconstruct_labels adv hres σ (pad_history n h) k = e.labels k := by
    intro k hk
    exact reconstruct_labels_pad adv hres σ e hcons hstep _ n hpad k hk.le
  -- The observation history from the padded execution matches e's
  have hhist_eq : obs_history adv.obs
      ⟨pad_history n h, reconstruct_labels adv hres σ (pad_history n h)⟩ n =
      obs_history adv.obs e n := by
    simp only [obs_history]
    congr 1; ext ⟨i, hi⟩
    · dsimp; rw [hpad i hi.le]
    · dsimp; rw [hpad i hi.le, hrl i hi]
  -- The prescribed signal matches
  have hprescribed : prescribed_signal adv σ
      ⟨pad_history n h, reconstruct_labels adv hres σ (pad_history n h)⟩ n =
      prescribed_signal adv σ e n := by
    simp only [prescribed_signal, hhist_eq, hpad n le_rfl]
  -- Now unfold both definitions and use hprescribed to align them
  unfold step_distribution step_prob
  simp only [hprescribed, hpad n le_rfl]
  -- The consistent_at condition for e determines both branches
  have hcons_n := (consistent_iff_forall_consistent_at adv σ e).mp hcons n
  simp only [hcons_n, ite_true]
  -- Both existentials hold
  obtain ⟨μe, hμe⟩ := hstep n
  have hex_lhs : ∃ μ l, adv.obs.observe_label (e.states n) l =
      prescribed_signal adv σ e n ∧ adv.sys.step (e.states n) l μ :=
    ⟨μe, e.labels n, hcons_n, hμe⟩
  rw [dif_pos hex_lhs, dif_pos ⟨μe, hμe⟩]
  -- LHS chose some (μ', l') with same signal; RHS chose some μ''
  -- By resolving: l' has same signal as e.labels n, both have steps → μ' = μ''
  obtain ⟨l', hobs', hstep'⟩ := hex_lhs.choose_spec
  have hsig : adv.obs.observe_label (e.states n) l' =
      adv.obs.observe_label (e.states n) (e.labels n) :=
    hobs'.trans hcons_n.symm
  have ⟨_, hμ_eq⟩ := hres _ _ _ _ _ hsig hstep' hμe
  have ⟨_, hμ_eq'⟩ := hres _ _ _ _ _ rfl (Exists.choose_spec ⟨μe, hμe⟩) hμe
  exact congr_arg (· (e.states (n + 1))) (hμ_eq.trans hμ_eq'.symm)

/-- The execution measure of a cylinder set containing only the initial
    state equals the initial indicator. -/
theorem exec_measure_cylinder_zero [Inhabited State]
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    (σ : Strategy SS LS) (s₀ : State)
    (e : LTS.Execution State Label) :
    exec_measure adv hres σ s₀ (state_cylinder e 0) =
    cone_prob adv σ s₀ e 0 := by
  classical
  let κ := fun n => transition_kernel adv hres σ n
  set x₀ := (MeasurableEquiv.piUnique fun _ : ↥(Finset.Iic (0 : ℕ)) => State).symm s₀
  have hset : state_cylinder e 0 =
    (Finset.Iic 0).restrict ⁻¹'
      {h : ↥(Finset.Iic 0) → State |
        h ⟨0, Finset.mem_Iic.mpr le_rfl⟩ = e.states 0} := by
    ext ω; simp [state_cylinder, Finset.restrict]
  have hms : MeasurableSet
      {h : ↥(Finset.Iic 0) → State | h ⟨0, Finset.mem_Iic.mpr le_rfl⟩ = e.states 0} :=
    (measurableSet_singleton _).preimage (measurable_pi_apply _)
  -- Step 1-2: Unfold exec_measure to (trajFun κ 0 x₀) via Dirac + bind
  simp only [exec_measure, ProbabilityTheory.Kernel.trajMeasure, PMF.toMeasure_pure]
  rw [MeasureTheory.Measure.map_dirac,
    MeasureTheory.Measure.bind_apply (hset ▸ hms.preimage (Finset.measurable_restrict _))
      (ProbabilityTheory.Kernel.measurable _).aemeasurable,
    MeasureTheory.lintegral_dirac]
  -- Step 3: traj = trajFun definitionally
  change ProbabilityTheory.Kernel.trajFun κ 0 x₀ (state_cylinder e 0) = _
  rw [hset]
  -- Step 4: trajContent_cylinder + partialTraj_self + id_apply give us hcyl
  have hcyl := @ProbabilityTheory.Kernel.trajContent_cylinder
    (fun _ => State) _ κ _ (a := 0) (b := 0) _ hms x₀
  rw [ProbabilityTheory.Kernel.partialTraj_self, ProbabilityTheory.Kernel.id_apply] at hcyl
  -- hcyl: trajContent κ x₀ (cylinder (Iic 0) S) = dirac x₀ S
  -- Step 5: Connect trajFun to trajContent on this cylinder set.
  -- trajFun definitionally equals trajContent.measure
  unfold ProbabilityTheory.Kernel.trajFun
  -- cylinder (Iic 0) S ∈ measurableCylinders
  have hmem : (Finset.Iic 0).restrict ⁻¹'
      {h : ↥(Finset.Iic 0) → State | h ⟨0, Finset.mem_Iic.mpr le_rfl⟩ = e.states 0} ∈
      MeasureTheory.measurableCylinders (fun _ : ℕ => State) :=
    MeasureTheory.cylinder_mem_measurableCylinders _ _ hms
  rw [MeasureTheory.AddContent.measure_eq _
    MeasureTheory.isSetSemiring_measurableCylinders
    MeasureTheory.generateFrom_measurableCylinders.symm _ hmem]
  -- Goal: (trajContent κ x₀) ((Iic 0).restrict ⁻¹' S) = cone_prob ... 0
  -- hcyl uses cylinder (Iic 0) S which is definitionally (Iic 0).restrict ⁻¹' S
  refine hcyl.trans ?_
  rw [MeasureTheory.Measure.dirac_apply' _ hms, Set.indicator_apply, Pi.one_apply]
  simp only [Set.mem_setOf_eq, cone_prob]
  simp [show x₀ ⟨0, Finset.mem_Iic.mpr le_rfl⟩ = s₀ from by
    simp [x₀], eq_comm]

/-- Decomposition: the measure of the `(n+1)`-cylinder equals the measure
    of the `n`-cylinder times the kernel's transition probability. -/
theorem exec_measure_cylinder_succ [Inhabited State]
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    (σ : Strategy SS LS) (s₀ : State)
    (e : LTS.Execution State Label)
    (n : ℕ) :
    exec_measure adv hres σ s₀ (state_cylinder e (n + 1)) =
    exec_measure adv hres σ s₀ (state_cylinder e n) *
      (transition_kernel adv hres σ n)
        (fun i => e.states ↑i) {e.states (n + 1)} := by
  classical
  let μ := exec_measure adv hres σ s₀
  let κ := fun n => transition_kernel adv hres σ n
  -- Use the Markov property: (μ.map frestrictLe n) ⊗ₘ κ n = μ.map (frestrictLe n, eval (n+1))
  have hmarkov := @ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (fun _ => State) _ κ _ (PMF.toMeasure (PMF.pure s₀)) _ (a := n)
  -- state_cylinder e (n+1) = {ω | ∀ k ≤ n, ω k = e.states k} ∩ {ω | ω (n+1) = e.states (n+1)}
  -- = (frestrictLe n, eval (n+1)) ⁻¹' (prefix_set × {e.states (n+1)})
  -- Define the prefix set and singleton
  set S_prefix := {h : (i : ↥(Finset.Iic n)) → State | ∀ i, h i = e.states ↑i}
  set s_next := e.states (n + 1)
  -- state_cylinder e (n+1) = (fun x => (frestrictLe n x, x (n+1))) ⁻¹' (S_prefix ×ˢ {s_next})
  have hcyl_decomp : state_cylinder e (n + 1) =
      (fun x : ℕ → State => (Preorder.frestrictLe n x, x (n + 1))) ⁻¹'
        (S_prefix ×ˢ {s_next}) := by
    ext ω
    simp only [state_cylinder, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod,
      Set.mem_singleton_iff, S_prefix, s_next, Preorder.frestrictLe]
    constructor
    · intro h
      exact ⟨fun i => h ↑i (Nat.le_succ_of_le (Finset.mem_Iic.mp i.prop)),
        h (n + 1) le_rfl⟩
    · intro ⟨h1, h2⟩ k hk
      rcases Nat.eq_or_lt_of_le hk with rfl | hlt
      · exact h2
      · exact h1 ⟨k, Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp hlt)⟩
  -- state_cylinder e n = (frestrictLe n) ⁻¹' S_prefix
  have hcyl_n : state_cylinder e n =
      (Preorder.frestrictLe n) ⁻¹' S_prefix := by
    ext ω
    simp only [state_cylinder, Set.mem_setOf_eq, Set.mem_preimage, S_prefix,
      Preorder.frestrictLe]
    exact ⟨fun h i => h ↑i (Finset.mem_Iic.mp i.prop),
      fun h k hk => h ⟨k, Finset.mem_Iic.mpr hk⟩⟩
  -- Rewrite LHS using the decomposition
  rw [show exec_measure adv hres σ s₀ = μ from rfl, hcyl_decomp]
  -- LHS = μ ((fun x => (frestrictLe n x, x (n+1))) ⁻¹' (S_prefix ×ˢ {s_next}))
  -- = (μ.map (fun x => (frestrictLe n x, x (n+1)))) (S_prefix ×ˢ {s_next})
  rw [← MeasureTheory.Measure.map_apply (by measurability) (by measurability)]
  -- = ((μ.map frestrictLe n) ⊗ₘ κ n) (S_prefix ×ˢ {s_next})  [by hmarkov]
  simp only [μ, exec_measure]; rw [← hmarkov]
  -- Use compProd_apply on the product set
  rw [MeasureTheory.Measure.compProd_apply (by measurability)]
  -- = ∫ h, (κ n h) ({s_next}) d(μ.map frestrictLe n) restricted to S_prefix
  -- For the singleton S_prefix (one matching function), the integral collapses
  -- Rewrite RHS similarly
  rw [hcyl_n, ← MeasureTheory.Measure.map_apply (by measurability) (by measurability)]
  -- The section of the product set: Prod.mk a ⁻¹' (S_prefix ×ˢ {s_next})
  -- = if a ∈ S_prefix then {s_next} else ∅
  have hsection : ∀ a : (↥(Finset.Iic n) → State),
      (κ n) a (Prod.mk a ⁻¹' (S_prefix ×ˢ {s_next})) =
      S_prefix.indicator (fun a => (κ n) a {s_next}) a := by
    intro a
    simp only [Set.indicator_apply]
    split
    · next h =>
        congr 1; ext s
        simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff]
        exact ⟨fun ⟨_, hs⟩ => hs, fun hs => ⟨h, hs⟩⟩
    · next h =>
        have : Prod.mk a ⁻¹' (S_prefix ×ˢ {s_next}) = ∅ := by
          ext s
          simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff,
            Set.mem_empty_iff_false, iff_false]
          exact fun ⟨ha, _⟩ => h ha
        rw [this, MeasureTheory.measure_empty]
  simp_rw [hsection]
  -- S_prefix is a singleton {e_prefix}
  have hsingleton : S_prefix = {fun i : ↥(Finset.Iic n) => e.states ↑i} := by
    ext h; simp [S_prefix, funext_iff]
  -- ∫ indicator_{S_prefix} f dν = ∫ indicator_{{e_prefix}} f dν = f(e_prefix) * ν({e_prefix})
  simp_rw [hsingleton, Set.indicator_singleton, Pi.single_apply]
  -- Goal: ∫ a, (if a = e_prefix then c else 0) dν = ν({e_prefix}) * c
  set e_prefix : (↥(Finset.Iic n) → State) := fun i => e.states ↑i
  set c := (κ n e_prefix) {s_next}
  -- Convert: if a = e_prefix then c else 0 = indicator {e_prefix} (fun _ => c) a
  have hind : ∀ a, (if a = e_prefix then c else 0) =
      ({e_prefix} : Set _).indicator (fun _ => c) a := by
    intro a; simp [Set.indicator_apply]
  simp_rw [hind]
  rw [MeasureTheory.lintegral_indicator_const (measurableSet_singleton _), mul_comm]

/-- **Main theorem**: the execution measure of a cylinder set equals
    the cone measure. This identifies the inductively defined `cone_prob`
    with the measure-theoretic cylinder set probability.

    Proof by induction on `n`:
    - **Base**: the Dirac initial measure gives 1 on `{s₀}` and 0 elsewhere.
    - **Step**: the `(n+1)`-cylinder decomposes as the `n`-cylinder times the
      transition kernel, which equals `step_prob` by the resolving condition. -/
theorem exec_measure_cylinder [Inhabited State]
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    (σ : Strategy SS LS) (s₀ : State)
    (e : LTS.Execution State Label)
    (hcons : adv.consistent σ e)
    (hstep : ∀ k, ∃ μ, adv.sys.step (e.states k) (e.labels k) μ)
    (n : ℕ) :
    exec_measure adv hres σ s₀ (state_cylinder e n) =
    cone_prob adv σ s₀ e n := by
  induction n with
  | zero => exact exec_measure_cylinder_zero adv hres σ s₀ e
  | succ n ih =>
    rw [exec_measure_cylinder_succ adv hres σ s₀ e n, ih,
      cone_prob_succ, transition_kernel_singleton,
      step_distribution_eq_step_prob adv hres σ e hcons hstep n _ (fun i => rfl)]

/-! ## Probabilistic Traces

    The **trace** of an execution is the subsequence of external labels.
    Under a resolving strategy, labels are deterministic functions of the
    state sequence (via `reconstruct_labels`), so the trace is a
    deterministic function of the state sequence.

    The **probabilistic trace** is the pushforward (image measure) of
    `exec_measure` under this trace function. Since the trace function
    is measurable (it maps `ℕ → State` to `ℕ → Label` via pointwise
    operations on a countable/discrete space), the pushforward is a
    well-defined probability measure on `ℕ → Label`. -/

/-- The trace function: maps a state sequence to the external label
    subsequence. First reconstructs labels from the state sequence
    (under a resolving strategy), then extracts the external subsequence. -/
noncomputable def trace_fn [Inhabited Label]
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    (σ : Strategy SS LS) (lab : LTS.Labelling Label)
    (states : ℕ → State) : ℕ → Label :=
  LTS.externalSubseq lab (reconstruct_labels adv hres σ states)

/-- The probabilistic trace: the pushforward of `exec_measure` under the
    trace function. This is a probability measure on `ℕ → Label`
    representing the distribution over external label sequences. -/
noncomputable def trace_measure [Inhabited State] [Inhabited Label]
    [MeasurableSpace Label]
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    (σ : Strategy SS LS) (lab : LTS.Labelling Label)
    (s₀ : State) : MeasureTheory.Measure (ℕ → Label) :=
  MeasureTheory.Measure.map (trace_fn adv hres σ lab)
    (exec_measure adv hres σ s₀)

omit [Inhabited Label] in
/-- Each coordinate of `reconstruct_labels` is measurable: it factors
    through the finite restriction `(ℕ → State) → (Fin (k+1) → State)`
    (measurable) followed by a function on a countable type (measurable
    by `measurable_of_countable`). -/
theorem reconstruct_labels_measurable [Inhabited Label] [Inhabited State]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    (σ : Strategy SS LS) :
    Measurable (fun ω : ℕ → State => reconstruct_labels adv hres σ ω) := by
  apply measurable_pi_lambda
  intro k
  -- fun ω => reconstruct_labels ... ω k depends on ω 0, ..., ω k
  -- Factor through the finite restriction to Fin (k+1) → State
  let restrict_k : (ℕ → State) → (Fin (k + 1) → State) :=
    fun ω i => ω i.val
  -- The restriction is measurable (composition of coordinate projections)
  have h_restrict : Measurable restrict_k :=
    measurable_pi_lambda _ fun i => measurable_pi_apply i.val
  -- The function from Fin (k+1) → State to Label is measurable
  -- because the domain is countable
  have h_label : Measurable (fun h : Fin (k + 1) → State =>
      reconstruct_labels adv hres σ (fun n => if hn : n ≤ k
        then h ⟨n, Nat.lt_succ_of_le hn⟩ else default) k) :=
    measurable_of_countable _
  -- The composition gives the desired measurability
  -- reconstruct_labels ... ω k = F_k (restrict_k ω) where F_k is on Fin(k+1) → State
  -- F_k is measurable by measurable_of_countable (countable domain)
  -- restrict_k is measurable (coordinate projections)
  suffices heq : (fun ω => reconstruct_labels adv hres σ ω k) =
      (fun h : Fin (k + 1) → State =>
        reconstruct_labels adv hres σ (fun n => if hn : n ≤ k
          then h ⟨n, Nat.lt_succ_of_le hn⟩ else default) k) ∘ restrict_k by
    rw [heq]; exact h_label.comp h_restrict
  -- Prove the factoring: both sides agree because reconstruct_labels
  -- at step k only uses states at positions ≤ k.
  -- pad ω = fun n => if n ≤ k then ω n else default agrees with ω on [0..k].
  ext ω; simp only [restrict_k, Function.comp]
  -- The padded function, after Lean's simplification:
  set pad := fun n => if hn : n ≤ k then ω n else (default : State)
  -- pad and ω agree on [0..k]
  have hagree : ∀ j, j ≤ k → pad j = ω j := fun j hj => dif_pos hj
  -- By strong induction: reconstruct_labels agrees on both for j ≤ k
  suffices ∀ j, j ≤ k →
      reconstruct_labels adv hres σ pad j = reconstruct_labels adv hres σ ω j from
    (this k le_rfl).symm
  intro j hj
  induction j using Nat.strongRecOn with
  | _ j ih =>
    have ih' : ∀ (i : Fin j), reconstruct_labels adv hres σ pad ↑i =
        reconstruct_labels adv hres σ ω ↑i :=
      fun ⟨i, hi⟩ => ih i hi (le_trans hi.le hj)
    unfold reconstruct_labels; dsimp only []
    -- Observation histories match (states agree on [0..j-1] ⊆ [0..k], labels by IH)
    have hhist : (List.ofFn fun i : Fin j =>
        (adv.obs.observe_state (pad ↑i),
         adv.obs.observe_label (pad ↑i) (reconstruct_labels adv hres σ pad ↑i))) =
        (List.ofFn fun i : Fin j =>
        (adv.obs.observe_state (ω ↑i),
         adv.obs.observe_label (ω ↑i) (reconstruct_labels adv hres σ ω ↑i))) := by
      congr 1; ext ⟨i, hi⟩
      · dsimp; rw [hagree i (le_trans hi.le hj)]
      · dsimp; rw [hagree i (le_trans hi.le hj), ih' ⟨i, hi⟩]
    -- Case split on whether a matching transition exists from ω j
    -- (equivalent to pad j by hagree)
    by_cases hex_ω : ∃ l μ, adv.obs.observe_label (ω j) l =
        σ (List.ofFn fun i : Fin j =>
          (adv.obs.observe_state (ω ↑i),
           adv.obs.observe_label (ω ↑i) (reconstruct_labels adv hres σ ω ↑i)))
          (adv.obs.observe_state (ω j)) ∧ adv.sys.step (ω j) l μ
    · -- Both difs are positive
      have hex_pad : ∃ l μ, adv.obs.observe_label (pad j) l =
          σ (List.ofFn fun i : Fin j =>
            (adv.obs.observe_state (pad ↑i),
             adv.obs.observe_label (pad ↑i) (reconstruct_labels adv hres σ pad ↑i)))
            (adv.obs.observe_state (pad j)) ∧ adv.sys.step (pad j) l μ := by
        rwa [hagree j hj, hhist]
      rw [dif_pos hex_pad, dif_pos hex_ω]
      -- Both choose labels with the same signal from the same state
      -- By resolving: they must be the same label
      obtain ⟨μ₁, hobs₁, hstep₁⟩ := hex_pad.choose_spec
      obtain ⟨μ₂, hobs₂, hstep₂⟩ := hex_ω.choose_spec
      have hpj := hagree j hj  -- pad j = ω j
      -- Transport step from pad j to ω j (rewrite goal, not hypothesis)
      have hstep₁' : adv.sys.step (ω j) hex_pad.choose μ₁ := by
        rw [← hpj]; exact hstep₁
      -- Both labels have the same signal from ω j
      have hsig : adv.obs.observe_label (ω j) hex_pad.choose =
          adv.obs.observe_label (ω j) hex_ω.choose := by
        calc adv.obs.observe_label (ω j) hex_pad.choose
            = adv.obs.observe_label (pad j) hex_pad.choose :=
              congrArg (adv.obs.observe_label · hex_pad.choose) hpj.symm
          _ = σ _ (adv.obs.observe_state (pad j)) := hobs₁
          _ = σ _ (adv.obs.observe_state (ω j)) := by rw [hhist, hpj]
          _ = adv.obs.observe_label (ω j) hex_ω.choose := hobs₂.symm
      exact (hres (ω j) hex_pad.choose hex_ω.choose μ₁ μ₂ hsig hstep₁' hstep₂).1
    · -- Both difs are negative
      have hex_pad : ¬∃ l μ, adv.obs.observe_label (pad j) l =
          σ (List.ofFn fun i : Fin j =>
            (adv.obs.observe_state (pad ↑i),
             adv.obs.observe_label (pad ↑i) (reconstruct_labels adv hres σ pad ↑i)))
            (adv.obs.observe_state (pad j)) ∧ adv.sys.step (pad j) l μ := by
        rwa [hagree j hj, hhist]
      rw [dif_neg hex_pad, dif_neg hex_ω]

/-- Each coordinate of `externalSubseq` is measurable: `fun labels => externalSubseq lab labels n`
    factors through the identity on `ℕ → Label` and produces a value in `Label` (countable).
    Since `Label` is countable + MSC, every set in `Label` is measurable, so it suffices
    to show preimages of singletons are measurable. These are countable unions of
    cylinder sets in `ℕ → Label`. -/
theorem externalSubseq_measurable
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

omit [Inhabited Label] in
theorem trace_fn_measurable [Inhabited Label] [Inhabited State]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    (σ : Strategy SS LS) (lab : LTS.Labelling Label) :
    Measurable (trace_fn adv hres σ lab) :=
  (externalSubseq_measurable lab).comp (reconstruct_labels_measurable adv hres σ)

/-- The probabilistic trace is a well-defined probability measure. -/
noncomputable instance trace_measure_prob [Inhabited State] [Inhabited Label]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving)
    (σ : Strategy SS LS) (lab : LTS.Labelling Label)
    (s₀ : State) :
    MeasureTheory.IsProbabilityMeasure (trace_measure adv hres σ lab s₀) := by
  unfold trace_measure
  exact MeasureTheory.Measure.isProbabilityMeasure_map
    (trace_fn_measurable adv hres σ lab).aemeasurable

end PLTS
