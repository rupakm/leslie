import Leslie_LTS.Framework.Probabilistic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! # Adversary Models for PLTS

    By default, a property holds for a protocol if it holds for *all* executions
    of its LTS. This implicitly gives the scheduler (adversary) full knowledge of
    the system state — an **omniscient adversary**.

    Omniscient adversaries are the strongest model: proving correctness against them
    gives the strongest guarantees. However, some protocols cannot be correct against
    omniscient adversaries. For example, secret-sharing protocols must guarantee that
    an outsider cannot learn the secret, but an omniscient adversary can read the
    local memory of all processes.

    This module defines adversaries via **observation functions**: an adversary is
    characterized by what it can observe from states and labels. The observation
    function maps each state to a state-signal and each label to a label-signal,
    representing what the adversary sees when the system is in that state or
    executes that transition. These are distinct types to clarify the two kinds
    of observation. The observation naturally lifts to executions, producing a
    sequence of signals.

    Adversaries are defined natively on PLTS. An LTS adversary is recovered by
    constructing a PLTS adversary over `fromLTS sys` via `Adversary.ofLTS`.
-/

/-! ## Observation / Signals

    An adversary is defined by two signal types and two observation functions:
    - `StateSignal`: what the adversary sees from a state
    - `LabelSignal`: what the adversary sees from a transition label

    This separation makes the model clearer: state observations and label
    observations are conceptually different (one is about configuration,
    the other about actions). -/

/-- An observation function defines what an adversary can see.
    It maps each state to a state-signal and each (state, label) pair to a
    label-signal. The label observation may depend on the current state
    (e.g., to reveal more information about actions of corrupted processes). -/
structure Observation (State : Type u) (Label : Type v)
    (StateSignal : Type w) (LabelSignal : Type x) where
  /-- What the adversary observes when the system is in a given state. -/
  observe_state : State → StateSignal
  /-- What the adversary observes when a transition fires from a given state
      with a given label. -/
  observe_label : State → Label → LabelSignal

/-- The full observation of an execution: the state-signal sequence and
    the label-signal sequence that the adversary sees. -/
structure Observation.ExecView (StateSignal : Type w) (LabelSignal : Type x) where
  /-- Observed state signals at each time step. -/
  state_signals : Nat → StateSignal
  /-- Observed label signals at each time step. -/
  label_signals : Nat → LabelSignal

/-- An adversary **strategy** is a function from the observation of a prefix
    of an execution ending with a state — i.e., past (state-signal, label-signal)
    pairs followed by the current state-signal — and outputs a label-signal.
    This is what the adversary "requests" as the next action, expressed in its
    own observation space. -/
def Strategy (StateSignal : Type w) (LabelSignal : Type x) :=
  List (StateSignal × LabelSignal) → StateSignal → LabelSignal

/-- A **randomised strategy**: at each step, the adversary observes the
    signal history and current state-signal, and produces a probability
    distribution over label-signals (rather than a single label-signal).
    This generalises `Strategy` by allowing the adversary to flip coins. -/
def RandomisedStrategy (StateSignal : Type w) (LabelSignal : Type x) :=
  List (StateSignal × LabelSignal) → StateSignal → PMF LabelSignal

/-- Embed a deterministic strategy as a randomised strategy via `PMF.pure`:
    at each step, the distribution is concentrated on the single label-signal
    that the deterministic strategy would choose. -/
noncomputable def Strategy.toRandomised {SS : Type w} {LS : Type x}
    (σ : Strategy SS LS) : RandomisedStrategy SS LS :=
  fun hist ss => PMF.pure (σ hist ss)

/-! ## Lifting Observations to Executions

    An observation function naturally extends to executions: from an execution,
    the adversary sees a sequence of state-signals and label-signals. -/

section ObservationMethods

variable {State : Type u} {Label : Type v} {SS : Type w} {LS : Type x}

/-- The state-signal sequence observed by the adversary along an execution. -/
def Observation.exec_states (obs : Observation State Label SS LS)
    (e : LTS.Execution State Label) : Nat → SS :=
  obs.observe_state ∘ e.states

/-- The label-signal sequence observed by the adversary along an execution. -/
def Observation.exec_labels (obs : Observation State Label SS LS)
    (e : LTS.Execution State Label) : Nat → LS :=
  fun k => obs.observe_label (e.states k) (e.labels k)

/-- Lift an observation function to a full execution, producing the adversary's
    view of that execution. -/
def Observation.view (obs : Observation State Label SS LS)
    (e : LTS.Execution State Label) : Observation.ExecView SS LS where
  state_signals := obs.observe_state ∘ e.states
  label_signals := fun k => obs.observe_label (e.states k) (e.labels k)

/-- The adversary's view of an execution up to time `k`: the state signals
    `0..k` and label signals `0..k-1`. This represents the adversary's
    knowledge after `k` steps have been observed. -/
def Observation.view_prefix (obs : Observation State Label SS LS)
    (e : LTS.Execution State Label) (k : Nat) :
    (Fin (k + 1) → SS) × (Fin k → LS) :=
  (fun i => obs.observe_state (e.states i.val),
   fun i => obs.observe_label (e.states i.val) (e.labels i.val))

end ObservationMethods

/-! ## Adversary Definition -/

namespace PLTS

variable {State : Type u} {Label : Type v}
variable {SS : Type w} {LS : Type x}

/-- An adversary for a PLTS, defined by its observation function.
    The adversary observes state-signals from states and label-signals from
    labels, and can only base its scheduling decisions on these signals. -/
structure Adversary (State : Type u) (Label : Type v)
    (StateSignal : Type w) (LabelSignal : Type x) where
  /-- The underlying PLTS. -/
  sys : System State Label
  /-- The observation function defining what the adversary can see. -/
  obs : Observation State Label StateSignal LabelSignal

/-- Two executions are **indistinguishable** to an adversary if they produce
    the same observation sequences — same state-signals and same label-signals
    at every step. -/
def Adversary.indistinguishable (adv : Adversary State Label SS LS)
    (e₁ e₂ : LTS.Execution State Label) : Prop :=
  (∀ k, adv.obs.observe_state (e₁.states k) = adv.obs.observe_state (e₂.states k)) ∧
  (∀ k, adv.obs.observe_label (e₁.states k) (e₁.labels k) =
        adv.obs.observe_label (e₂.states k) (e₂.labels k))

/-- An execution is **consistent** with a strategy if at each step, the
    label-signal observed from the actual label matches what the strategy
    prescribed given the observation prefix so far. -/
def Adversary.consistent (adv : Adversary State Label SS LS)
    (σ : Strategy SS LS) (e : LTS.Execution State Label) : Prop :=
  ∀ k, adv.obs.observe_label (e.states k) (e.labels k) =
    σ (List.ofFn fun i : Fin k =>
      (adv.obs.observe_state (e.states i.val),
       adv.obs.observe_label (e.states i.val) (e.labels i.val)))
    (adv.obs.observe_state (e.states k))

/-- An execution is **admissible** for an adversary if there exists some strategy
    (depending only on observations) that is consistent with the execution. -/
def Adversary.admissible (adv : Adversary State Label SS LS)
    (e : LTS.Execution State Label) : Prop :=
  ∃ σ : Strategy SS LS, adv.consistent σ e

/-- An execution is valid under an adversary: it is a valid execution of the
    underlying PLTS (via `toLTS`) and is admissible (consistent with some
    observation-based strategy). -/
def Adversary.valid_exec (adv : Adversary State Label SS LS)
    (e : LTS.Execution State Label) : Prop :=
  (toLTS adv.sys).valid_exec e ∧ adv.admissible e

/-- A trace property holds under an adversary if it holds for all valid
    admissible executions. -/
def Adversary.satisfies (adv : Adversary State Label SS LS)
    (φ : LTS.Execution State Label → Prop) : Prop :=
  ∀ e, adv.valid_exec e → φ e

/-- A state predicate is an invariant under an adversary if it holds at every
    position of every admissible execution. -/
def Adversary.invariant (adv : Adversary State Label SS LS)
    (P : State → Prop) : Prop :=
  ∀ e, adv.valid_exec e → ∀ k, P (e.states k)

/-! ### The Omniscient Adversary

    The omniscient adversary observes the full state and the full label.
    Its state-signal type is `State` and its label-signal type is `Label`.
    Every execution is trivially admissible since the adversary can see
    everything and thus any schedule is realizable. -/

/-- The omniscient adversary: observes the full state and full label. -/
def omniscient (sys : System State Label) : Adversary State Label State Label where
  sys := sys
  obs := {
    observe_state := id
    observe_label := fun _ l => l
  }

/-- Under the omniscient adversary, every execution is admissible:
    the adversary sees everything, so any schedule is realizable. -/
theorem omniscient_all_admissible (sys : System State Label)
    (e : LTS.Execution State Label) :
    (omniscient sys).admissible e := by
  refine ⟨fun history _ => e.labels history.length, fun k => ?_⟩
  simp [omniscient]

/-- A property holds under the omniscient adversary iff it holds for all
    valid PLTS executions. -/
theorem omniscient_satisfies (sys : System State Label)
    (φ : LTS.Execution State Label → Prop) :
    (omniscient sys).satisfies φ ↔ ∀ e, (toLTS sys).valid_exec e → φ e := by
  constructor
  · intro h e hv
    exact h e ⟨hv, omniscient_all_admissible sys e⟩
  · intro h e ⟨hv, _⟩
    exact h e hv

/-! ### Adversary Ordering

    An adversary `A` is *weaker* than `B` if `A` observes less — i.e., `B`'s
    observations can be recovered from `A`'s. A weaker adversary sees less,
    so it has fewer admissible strategies, making properties easier to satisfy. -/

/-- Adversary `a` observes at most what `b` observes if `b`'s observations
    factor through `a`'s — anything `b` can distinguish, `a` can too.
    This means `a` is at least as strong as `b`. -/
def Adversary.observes_more
    {SS₁ : Type _} {LS₁ : Type _} {SS₂ : Type _} {LS₂ : Type _}
    (a : Adversary State Label SS₁ LS₁)
    (b : Adversary State Label SS₂ LS₂) : Prop :=
  a.sys = b.sys ∧
  ∃ (fs : SS₁ → SS₂) (fl : LS₁ → LS₂),
    (∀ s, b.obs.observe_state s = fs (a.obs.observe_state s)) ∧
    (∀ s l, b.obs.observe_label s l = fl (a.obs.observe_label s l))

/-! ### Indistinguishability Properties

    Two executions are indistinguishable to an adversary if they produce
    identical observation sequences. This is the foundation for defining
    security: a protocol hides information from the adversary if executions
    with different secrets are indistinguishable. -/

/-- Indistinguishability is reflexive. -/
theorem Adversary.indistinguishable_refl (adv : Adversary State Label SS LS)
    (e : LTS.Execution State Label) : adv.indistinguishable e e :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-- Indistinguishability is symmetric. -/
theorem Adversary.indistinguishable_symm (adv : Adversary State Label SS LS)
    {e₁ e₂ : LTS.Execution State Label}
    (h : adv.indistinguishable e₁ e₂) : adv.indistinguishable e₂ e₁ :=
  ⟨fun k => (h.1 k).symm, fun k => (h.2 k).symm⟩

/-- Indistinguishability is transitive. -/
theorem Adversary.indistinguishable_trans (adv : Adversary State Label SS LS)
    {e₁ e₂ e₃ : LTS.Execution State Label}
    (h₁ : adv.indistinguishable e₁ e₂) (h₂ : adv.indistinguishable e₂ e₃) :
    adv.indistinguishable e₁ e₃ :=
  ⟨fun k => (h₁.1 k).trans (h₂.1 k), fun k => (h₁.2 k).trans (h₂.2 k)⟩

/-- If two executions are indistinguishable and one is admissible via some
    strategy, then the other is admissible via the same strategy. -/
theorem Adversary.admissible_of_indistinguishable (adv : Adversary State Label SS LS)
    {e₁ e₂ : LTS.Execution State Label}
    (h : adv.indistinguishable e₁ e₂)
    (hadm : adv.admissible e₁) :
    adv.admissible e₂ := by
  obtain ⟨σ, hσ⟩ := hadm
  refine ⟨σ, fun k => ?_⟩
  have hobs : (List.ofFn fun i : Fin k =>
      (adv.obs.observe_state (e₁.states i.val),
       adv.obs.observe_label (e₁.states i.val) (e₁.labels i.val))) =
    (List.ofFn fun i : Fin k =>
      (adv.obs.observe_state (e₂.states i.val),
       adv.obs.observe_label (e₂.states i.val) (e₂.labels i.val))) := by
    congr 1; ext ⟨i, hi⟩
    · dsimp; exact h.1 i
    · dsimp; exact h.2 i
  rw [← h.2 k, ← hobs, ← h.1 k]
  exact hσ k

/-! ## Nondeterminism Resolution

    In a PLTS, multiple transitions may be enabled from the same state: different
    labels, or different distributions for the same label. A strategy prescribes
    a label-signal at each step, but multiple `(label, distribution)` pairs may
    match that signal — leaving residual nondeterminism.

    A strategy **resolves all nondeterminism** if its prescribed label-signal
    uniquely determines the transition `(label, distribution)` at each step.
    After resolution, the only remaining source of randomness is the sampling
    from the chosen distribution — the system behaves as a Markov chain.

    A structural condition **`observation_resolving`** on the `(PLTS, Observation)`
    pair guarantees that ALL strategies resolve all nondeterminism. -/

/-- A strategy **resolves all nondeterminism** for an adversary if, at any
    state, the prescribed label-signal uniquely determines the transition.
    That is: for any state `s` and any observation history, if two transitions
    `(l₁, μ₁)` and `(l₂, μ₂)` both match the signal prescribed by `σ`,
    they must be identical. -/
def Adversary.strategy_resolving (adv : Adversary State Label SS LS)
    (σ : Strategy SS LS) : Prop :=
  ∀ (s : State) (hist : List (SS × LS)) (l₁ l₂ : Label) (μ₁ μ₂ : PMF State),
    adv.obs.observe_label s l₁ = σ hist (adv.obs.observe_state s) →
    adv.obs.observe_label s l₂ = σ hist (adv.obs.observe_state s) →
    adv.sys.step s l₁ μ₁ → adv.sys.step s l₂ μ₂ →
    l₁ = l₂ ∧ μ₁ = μ₂

/-- The observation is **resolving**: at each state, the label-signal uniquely
    determines the transition. If two enabled transitions from the same state
    produce the same label-signal, they must have the same label and the same
    distribution. This is a structural property of the `(PLTS, Observation)`
    pair, independent of any particular strategy. -/
def Adversary.observation_resolving (adv : Adversary State Label SS LS) : Prop :=
  ∀ (s : State) (l₁ l₂ : Label) (μ₁ μ₂ : PMF State),
    adv.obs.observe_label s l₁ = adv.obs.observe_label s l₂ →
    adv.sys.step s l₁ μ₁ → adv.sys.step s l₂ μ₂ →
    l₁ = l₂ ∧ μ₁ = μ₂

/-- If the observation is resolving, then every strategy resolves all
    nondeterminism. The structural condition on `(PLTS, Observation)` is
    sufficient for universal nondeterminism resolution. -/
theorem Adversary.observation_resolving_implies_strategy_resolving
    (adv : Adversary State Label SS LS)
    (h : adv.observation_resolving) (σ : Strategy SS LS) :
    adv.strategy_resolving σ := by
  intro s hist l₁ l₂ μ₁ μ₂ hobs₁ hobs₂ hstep₁ hstep₂
  exact h s l₁ l₂ μ₁ μ₂ (hobs₁.trans hobs₂.symm) hstep₁ hstep₂

/-! ## LTS Adversary via fromLTS -/

/-- Construct a PLTS adversary from an LTS system by embedding via `fromLTS`. -/
def Adversary.ofLTS (sys : LTS.System State Label)
    (obs : Observation State Label SS LS) : Adversary State Label SS LS where
  sys := fromLTS sys
  obs := obs

/-- Execution validity for an `ofLTS` adversary reduces to LTS validity. -/
theorem Adversary.ofLTS_valid_exec (sys : LTS.System State Label)
    (obs : Observation State Label SS LS) (e : LTS.Execution State Label) :
    (Adversary.ofLTS sys obs).valid_exec e ↔
    sys.valid_exec e ∧ (Adversary.ofLTS sys obs).admissible e := by
  simp only [Adversary.valid_exec, Adversary.ofLTS, toLTS_fromLTS_valid_exec]

/-- The omniscient adversary for an LTS, constructed via PLTS. -/
def omniscientLTS (sys : LTS.System State Label) :
    Adversary State Label State Label :=
  omniscient (fromLTS sys)

/-- A property holds under the omniscient LTS adversary iff it holds for all
    valid LTS executions. -/
theorem omniscientLTS_satisfies (sys : LTS.System State Label)
    (φ : LTS.Execution State Label → Prop) :
    (omniscientLTS sys).satisfies φ ↔ ∀ e, sys.valid_exec e → φ e := by
  simp only [omniscientLTS, omniscient_satisfies, toLTS_fromLTS_valid_exec]

/-! ## Randomised Strategies

    A randomised strategy generalises a deterministic strategy by allowing
    the adversary to flip coins: at each step, instead of prescribing a
    single label-signal, it prescribes a probability distribution over
    label-signals. An execution is randomised-consistent if the observed
    label-signal at each step lies in the support of the prescribed
    distribution.

    The key structural property is that randomised consistency depends
    only on the adversary's view (observation sequences). This enables
    lifting results from deterministic to randomised strategies. -/

/-- An execution is **randomised-consistent** with a randomised strategy `ρ`
    if at each step, the observed label-signal is in the support of the
    distribution prescribed by `ρ` given the observation prefix. -/
def Adversary.randomised_consistent (adv : Adversary State Label SS LS)
    (ρ : RandomisedStrategy SS LS) (e : LTS.Execution State Label) : Prop :=
  ∀ k, adv.obs.observe_label (e.states k) (e.labels k) ∈
    (ρ (List.ofFn fun i : Fin k =>
      (adv.obs.observe_state (e.states i.val),
       adv.obs.observe_label (e.states i.val) (e.labels i.val)))
    (adv.obs.observe_state (e.states k))).support

/-- An execution is **randomised-admissible** for an adversary if there exists
    some randomised strategy consistent with the execution. -/
def Adversary.randomised_admissible (adv : Adversary State Label SS LS)
    (e : LTS.Execution State Label) : Prop :=
  ∃ ρ : RandomisedStrategy SS LS, adv.randomised_consistent ρ e

/-- Deterministic consistency implies randomised consistency with the
    lifted strategy: if `e` is consistent with `σ`, then `e` is
    randomised-consistent with `σ.toRandomised`. -/
theorem Adversary.consistent_toRandomised (adv : Adversary State Label SS LS)
    (σ : Strategy SS LS) (e : LTS.Execution State Label)
    (h : adv.consistent σ e) :
    adv.randomised_consistent σ.toRandomised e := by
  intro k
  simp only [Strategy.toRandomised, PMF.mem_support_pure_iff]
  exact h k

/-- Every deterministic-admissible execution is randomised-admissible. -/
theorem Adversary.randomised_admissible_of_admissible (adv : Adversary State Label SS LS)
    (e : LTS.Execution State Label) (h : adv.admissible e) :
    adv.randomised_admissible e := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨σ.toRandomised, adv.consistent_toRandomised σ e hσ⟩

/-- Randomised consistency depends only on the adversary's view:
    if two executions are indistinguishable (same state-signals and
    label-signals at every step), then one is randomised-consistent
    with `ρ` iff the other is. -/
theorem Adversary.randomised_consistent_of_indistinguishable
    (adv : Adversary State Label SS LS)
    (ρ : RandomisedStrategy SS LS)
    {e₁ e₂ : LTS.Execution State Label}
    (h : adv.indistinguishable e₁ e₂)
    (hcons : adv.randomised_consistent ρ e₁) :
    adv.randomised_consistent ρ e₂ := by
  intro k
  have hhist : (List.ofFn fun i : Fin k =>
      (adv.obs.observe_state (e₁.states i.val),
       adv.obs.observe_label (e₁.states i.val) (e₁.labels i.val))) =
    (List.ofFn fun i : Fin k =>
      (adv.obs.observe_state (e₂.states i.val),
       adv.obs.observe_label (e₂.states i.val) (e₂.labels i.val))) := by
    congr 1; ext ⟨i, hi⟩ <;> simp [h.1 i, h.2 i]
  rw [← h.2 k, ← h.1 k, ← hhist]
  exact hcons k

/-- From a randomised-consistent execution, extract a deterministic
    strategy that the execution is (deterministic-)consistent with.
    The extracted strategy simply replays the execution's actual
    label-signals at each step. -/
theorem Adversary.consistent_of_randomised_consistent
    (adv : Adversary State Label SS LS)
    (ρ : RandomisedStrategy SS LS)
    (e : LTS.Execution State Label)
    (_h : adv.randomised_consistent ρ e) :
    ∃ σ : Strategy SS LS, adv.consistent σ e := by
  refine ⟨fun hist _ => adv.obs.observe_label (e.states hist.length) (e.labels hist.length),
    fun k => ?_⟩
  simp only [List.length_ofFn]

/-! ## Observation History and Cone Measures -/

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

/-! ## Belief-State PLTS (Possible Worlds)

    Given an adversary with `observation_resolving`, the **belief-state PLTS**
    tracks the adversary's probabilistic knowledge about the system state.

    States are pairs `(ss : SS, μ : PMF State)` where `μ` is a distribution
    over original states, all having signal `ss`. This is the adversary's
    **belief**: a probability distribution over which state the system is in,
    given the observation history.

    Under `observation_resolving`, each `(state, label-signal)` pair determines
    a unique transition distribution. The belief update follows the Bayesian
    rule: execute the resolved transition from each possible state, then
    condition on the observed successor signal.

    The internal/external classification lifts to signals via a compatibility
    condition: internal labels produce internal signals and external labels
    produce external signals. -/

/-- A belief state: a state-signal paired with a distribution over original
    states consistent with that signal. -/
structure Adversary.BeliefState (State : Type u) (SS : Type w) where
  /-- The state-signal observed by the adversary. -/
  signal : SS
  /-- Distribution over original states consistent with this signal. -/
  belief : PMF State

open Classical in
/-- The joint distribution over successor states: mix the per-state
    transition distributions according to the current belief.
    Under resolving, each `(s, ls)` determines a unique `(l, ν)`.
    If `s` has no matching transition, fall back to `PMF.pure s`. -/
noncomputable def Adversary.beliefJoint (adv : Adversary State Label SS LS)
    [Inhabited Label]
    (_hres : adv.observation_resolving)
    (μ : PMF State) (ls : LS) : PMF State :=
  μ.bind fun s =>
    if h : ∃ l ν, adv.obs.observe_label s l = ls ∧ adv.sys.step s l ν then
      h.choose_spec.choose
    else
      PMF.pure s

/-- The belief-state PLTS induced by an adversary under `observation_resolving`.

    - **States**: `BeliefState State SS` — (signal, belief distribution)
    - **Labels**: `LS` — label signals
    - **Init**: `(ss, μ)` where all states in `μ.support` are initial with
      signal `ss`
    - **Step**: `(ss, μ) →[ls] ν_bs` where `ν_bs : PMF (BeliefState State SS)` is
      the Bayesian-updated distribution over successor belief states.
      Each `(ss', μ')` in `ν_bs.support` satisfies:
      - `μ'` is `beliefJoint μ ls` conditioned on `{s' | observe_state s' = ss'}`
      - `ν_bs(ss', μ')` is the marginal probability of observing `ss'` -/
noncomputable def Adversary.beliefPLTS (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) [Inhabited Label] :
    System (Adversary.BeliefState State SS) LS where
  init := fun bs =>
    (∀ s ∈ bs.belief.support, adv.sys.init s ∧
      adv.obs.observe_state s = bs.signal)
  step := fun bs ls ν_bs =>
    let joint := adv.beliefJoint hres bs.belief ls
    -- Every successor belief state in ν_bs's support is the posterior
    -- of joint conditioned on the corresponding signal
    ∀ bs' ∈ ν_bs.support,
      -- All states in the posterior have the right signal
      (∀ s' ∈ bs'.belief.support,
        adv.obs.observe_state s' = bs'.signal) ∧
      -- The posterior is joint conditioned on {s' | signal = ss'}
      (∃ h : ∃ a ∈ {s' | adv.obs.observe_state s' = bs'.signal},
          a ∈ joint.support,
        bs'.belief = PMF.filter joint
          {s' | adv.obs.observe_state s' = bs'.signal} h)

/-- Signal-level labelling compatibility: the observation preserves the
    internal/external classification of labels. -/
structure Adversary.SignalLabelling (adv : Adversary State Label SS LS)
    (lab : LTS.Labelling Label) where
  /-- The induced labelling on label-signals. -/
  sig_lab : LTS.Labelling LS
  /-- Internal labels produce internal signals. -/
  internal_preserved : ∀ s l,
    lab.is_internal l = true →
    sig_lab.is_internal (adv.obs.observe_label s l) = true
  /-- External labels produce external signals. -/
  external_preserved : ∀ s l,
    lab.is_external l = true →
    sig_lab.is_external (adv.obs.observe_label s l) = true

/-- Project an execution to its observation: apply the observation at each step. -/
def Adversary.projectExec (adv : Adversary State Label SS LS)
    (e : LTS.Execution State Label) : LTS.Execution SS LS where
  states := fun k => adv.obs.observe_state (e.states k)
  labels := fun k => adv.obs.observe_label (e.states k) (e.labels k)

/-- The projected execution's view agrees with the original execution's view.
    Projection to signals IS the adversary's observation. -/
theorem Adversary.projectExec_view (adv : Adversary State Label SS LS)
    (e : LTS.Execution State Label) :
    (adv.projectExec e).states = (adv.obs.view e).state_signals ∧
    (adv.projectExec e).labels = (adv.obs.view e).label_signals :=
  ⟨rfl, rfl⟩

/-- The naive quotient LTS on signals. May have spurious executions but is
    useful as a target for forward simulations between observation spaces. -/
def Adversary.quotientLTS (adv : Adversary State Label SS LS) :
    LTS.System SS LS where
  init := fun ss => ∃ s, adv.sys.init s ∧ adv.obs.observe_state s = ss
  step := fun ss ls ss' => ∃ s l s',
    (toLTS adv.sys).step s l s' ∧
    adv.obs.observe_state s = ss ∧
    adv.obs.observe_label s l = ls ∧
    adv.obs.observe_state s' = ss'

/-- Every valid execution projects to a valid quotient execution. -/
theorem Adversary.quotientLTS_project (adv : Adversary State Label SS LS)
    (e : LTS.Execution State Label)
    (hval : (toLTS adv.sys).valid_exec e) :
    adv.quotientLTS.valid_exec (adv.projectExec e) := by
  constructor
  · exact ⟨e.states 0, hval.1, rfl⟩
  · intro k
    exact ⟨e.states k, e.labels k, e.states (k + 1), hval.2 k, rfl, rfl, rfl⟩

/-! ## Backward-Compatible LTS Aliases -/

end PLTS

namespace LTS

/-- An LTS observation (alias for the top-level `Observation`). -/
abbrev Observation := _root_.Observation

namespace Observation

/-- Alias for `Observation.ExecView`. -/
abbrev ExecView := _root_.Observation.ExecView

end Observation

/-- An LTS strategy (alias for the top-level `Strategy`). -/
abbrev Strategy := _root_.Strategy

/-- An LTS randomised strategy (alias for the top-level `RandomisedStrategy`). -/
abbrev RandomisedStrategy := _root_.RandomisedStrategy

/-- An LTS adversary is a PLTS adversary. -/
abbrev Adversary := PLTS.Adversary

end LTS
