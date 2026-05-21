import Leslie_LTS.Framework.ProbExec

/-! # Secrecy Properties for PLTS Adversaries

    This module defines secrecy notions for PLTS adversaries: inferability,
    secrets, possibilistic secrecy (non-deducibility), and isomorphic secrecy
    (bijective remapping). These build on the adversary model defined in
    `Leslie_LTS.Framework.Adversary`.
-/

namespace PLTS

variable {State : Type u} {Label : Type v}
variable {SS : Type w} {LS : Type x}

/-! ## Inferable Properties

    Given a trace property `P`, an adversary, and an observation (what the
    adversary actually sees), we classify whether the adversary can infer
    whether `P` holds or not.

    An execution is **consistent with an observation** if the adversary's
    view of that execution matches the given observation.

    - `P` is **positively inferable** from an observation if all valid
      executions consistent with that observation satisfy `P`.
    - `P` is **negatively inferable** from an observation if all valid
      executions consistent with that observation do *not* satisfy `P`.
    - `P` is **not inferable** if it is neither positively nor negatively
      inferable — the adversary cannot determine from its observation
      whether `P` holds. -/

/-- An execution is consistent with an observation `v` if the adversary's
    view of the execution equals `v`. -/
def Adversary.consistent_with_view (adv : Adversary State Label SS LS)
    (e : LTS.Execution State Label) (v : Observation.ExecView SS LS) : Prop :=
  adv.obs.view e = v

/-- A trace property `P` is **positively inferable** from observation `v`
    under strategy `σ`: every system-valid execution that is consistent with
    strategy `σ` and produces observation `v` satisfies `P`. -/
def Adversary.positively_inferable (adv : Adversary State Label SS LS)
    (σ : Strategy SS LS)
    (P : LTS.Execution State Label → Prop)
    (v : Observation.ExecView SS LS) : Prop :=
  ∀ e, (toLTS adv.sys).valid_exec e → adv.consistent σ e →
    adv.consistent_with_view e v → P e

/-- A trace property `P` is **negatively inferable** from observation `v`
    under strategy `σ`: every system-valid execution consistent with `σ`
    that produces observation `v` does *not* satisfy `P`. -/
def Adversary.negatively_inferable (adv : Adversary State Label SS LS)
    (σ : Strategy SS LS)
    (P : LTS.Execution State Label → Prop)
    (v : Observation.ExecView SS LS) : Prop :=
  ∀ e, (toLTS adv.sys).valid_exec e → adv.consistent σ e →
    adv.consistent_with_view e v → ¬P e

/-- A trace property `P` is **not inferable** from observation `v`
    under strategy `σ`: the adversary cannot determine from `v` and `σ`
    whether `P` holds. -/
def Adversary.not_inferable (adv : Adversary State Label SS LS)
    (σ : Strategy SS LS)
    (P : LTS.Execution State Label → Prop)
    (v : Observation.ExecView SS LS) : Prop :=
  ¬adv.positively_inferable σ P v ∧ ¬adv.negatively_inferable σ P v

/-- If a property is not inferable under a strategy, there exist two
    system-valid executions consistent with the strategy and observation
    such that one satisfies `P` and the other does not. -/
theorem Adversary.not_inferable_witnesses (adv : Adversary State Label SS LS)
    (σ : Strategy SS LS)
    (P : LTS.Execution State Label → Prop)
    (v : Observation.ExecView SS LS)
    (h : adv.not_inferable σ P v) :
    (∃ e, (toLTS adv.sys).valid_exec e ∧ adv.consistent σ e ∧
      adv.consistent_with_view e v ∧ P e) ∧
    (∃ e, (toLTS adv.sys).valid_exec e ∧ adv.consistent σ e ∧
      adv.consistent_with_view e v ∧ ¬P e) := by
  obtain ⟨hnpos, hnneg⟩ := h
  constructor
  · exact Classical.byContradiction fun hc =>
      hnneg (fun e hv hσ hobs hp => hc ⟨e, hv, hσ, hobs, hp⟩)
  · exact Classical.byContradiction fun hc =>
      hnpos (fun e hv hσ hobs =>
        Classical.byContradiction (fun hnp => hc ⟨e, hv, hσ, hobs, hnp⟩))

/-- Positive and negative inferability are mutually exclusive
    (assuming some execution is consistent with the strategy and observation). -/
theorem Adversary.not_both_inferable (adv : Adversary State Label SS LS)
    (σ : Strategy SS LS)
    (P : LTS.Execution State Label → Prop)
    (v : Observation.ExecView SS LS)
    (e : LTS.Execution State Label)
    (hv : (toLTS adv.sys).valid_exec e) (hσ : adv.consistent σ e)
    (hobs : adv.consistent_with_view e v) :
    ¬(adv.positively_inferable σ P v ∧ adv.negatively_inferable σ P v) := by
  intro ⟨hpos, hneg⟩
  exact hneg e hv hσ hobs (hpos e hv hσ hobs)

/-! ## Secrets -/

/-- A trace property `P` is a **secret** under observation property `P'`:
    for every strategy `σ` and every observation `v` satisfying `P'`,
    the property `P` is not inferable from `v` under `σ`. -/
def Adversary.secret (adv : Adversary State Label SS LS)
    (P : LTS.Execution State Label → Prop)
    (P' : Observation.ExecView SS LS → Prop) : Prop :=
  ∀ σ v, P' v → adv.not_inferable σ P v

/-- If `P` is a secret under `P'`, then for every strategy and observation
    satisfying `P'`, there exist two system-valid executions consistent with
    the strategy and observation: one satisfying `P` and one not. -/
theorem Adversary.secret_witnesses (adv : Adversary State Label SS LS)
    (P : LTS.Execution State Label → Prop)
    (P' : Observation.ExecView SS LS → Prop)
    (hsec : adv.secret P P')
    (σ : Strategy SS LS) (v : Observation.ExecView SS LS) (hv : P' v) :
    (∃ e, (toLTS adv.sys).valid_exec e ∧ adv.consistent σ e ∧
      adv.consistent_with_view e v ∧ P e) ∧
    (∃ e, (toLTS adv.sys).valid_exec e ∧ adv.consistent σ e ∧
      adv.consistent_with_view e v ∧ ¬P e) :=
  adv.not_inferable_witnesses σ P v (hsec σ v hv)

/-! ## Possibilistic Secrecy

    Possibilistic secrecy (non-deducibility): the adversary cannot determine
    whether a property holds from its observation — both outcomes are possible. -/

/-- Possibilistic secrecy: a trace property `P` is a **possibilistic secret**
    under execution condition `P'` if, for every strategy and view realizable
    by a `P'`-satisfying execution, there exist `P'`-satisfying executions
    with that same view where `P` holds and where `P` doesn't hold.
    The adversary cannot determine `P` from its view — both outcomes
    are *possible*. This is also known as non-deducibility. -/
def Adversary.possibilistic_secret (adv : Adversary State Label SS LS)
    (P : LTS.Execution State Label → Prop)
    (P' : LTS.Execution State Label → Prop) : Prop :=
  ∀ σ v,
    (∃ e, (toLTS adv.sys).valid_exec e ∧ adv.consistent σ e ∧
      adv.obs.view e = v ∧ P' e) →
    (∃ e, (toLTS adv.sys).valid_exec e ∧ adv.consistent σ e ∧
      adv.obs.view e = v ∧ P' e ∧ P e) ∧
    (∃ e, (toLTS adv.sys).valid_exec e ∧ adv.consistent σ e ∧
      adv.obs.view e = v ∧ P' e ∧ ¬P e)

/-! ### Possibilistic Secrecy Proof Rule

    A general proof rule for establishing `possibilistic_secret` via a **remap**
    argument. -/

/-- **Possibilistic secrecy by remap**. -/
theorem Adversary.possibilistic_secret_by_remap (adv : Adversary State Label SS LS)
    {V : Type _}
    (secret : V → LTS.Execution State Label → Prop)
    (C : LTS.Execution State Label → Prop)
    (hhas_secret : ∀ e, (toLTS adv.sys).valid_exec e → C e → ∃ v, secret v e)
    (hremap : ∀ v₁ v₂ e (σ : Strategy SS LS),
      (toLTS adv.sys).valid_exec e → adv.consistent σ e → C e → secret v₁ e →
      ∃ e', (toLTS adv.sys).valid_exec e' ∧ adv.consistent σ e' ∧
        adv.obs.view e = adv.obs.view e' ∧ C e' ∧ secret v₂ e')
    (hexcl : ∀ v₁ v₂ e, (toLTS adv.sys).valid_exec e → C e →
      v₁ ≠ v₂ → secret v₁ e → ¬secret v₂ e)
    (s : V) (hne : ∃ s', s' ≠ s) :
    adv.possibilistic_secret (secret s) C := by
  intro σ v ⟨e₀, hvalid₀, hcons₀, hview₀, hC₀⟩
  obtain ⟨v₀, hv₀⟩ := hhas_secret e₀ hvalid₀ hC₀
  obtain ⟨s', hs'⟩ := hne
  constructor
  · -- Positive witness: remap v₀ → s
    obtain ⟨e', hv', hc', hw', hC', hsec_s⟩ :=
      hremap v₀ s e₀ σ hvalid₀ hcons₀ hC₀ hv₀
    exact ⟨e', hv', hc', hw' ▸ hview₀, hC', hsec_s⟩
  · -- Negative witness: remap v₀ → s' where s' ≠ s
    obtain ⟨e', hv', hc', hw', hC', hsec'⟩ :=
      hremap v₀ s' e₀ σ hvalid₀ hcons₀ hC₀ hv₀
    exact ⟨e', hv', hc', hw' ▸ hview₀, hC', hexcl s' s e' hv' hC' hs' hsec'⟩

/-! ## Isomorphic Secrecy

    A stronger notion of secrecy based on **bijective remapping**. Rather than
    just asserting that alternative secret values are *possible* (as
    `possibilistic_secret` does), we require an invertible, view-preserving
    transformation between executions with different secret values. -/

/-- Isomorphic secrecy: there exists an invertible remap between
    executions with different secret values that preserves everything the
    adversary can observe. -/
def Adversary.isomorphic_secret (adv : Adversary State Label SS LS)
    {V : Type _}
    (secret : V → LTS.Execution State Label → Prop)
    (C : LTS.Execution State Label → Prop) : Prop :=
  ∃ remap : V → V → LTS.Execution State Label → LTS.Execution State Label,
    -- (1) Remap preserves validity, consistency, view, condition, and secret
    (∀ v₁ v₂ e (σ : Strategy SS LS),
      (toLTS adv.sys).valid_exec e → adv.consistent σ e → C e → secret v₁ e →
      (toLTS adv.sys).valid_exec (remap v₁ v₂ e) ∧
      adv.consistent σ (remap v₁ v₂ e) ∧
      adv.obs.view e = adv.obs.view (remap v₁ v₂ e) ∧
      C (remap v₁ v₂ e) ∧
      secret v₂ (remap v₁ v₂ e)) ∧
    -- (2) Remap is invertible: bijection between fibers
    (∀ v₁ v₂ e, (toLTS adv.sys).valid_exec e → C e → secret v₁ e →
      remap v₂ v₁ (remap v₁ v₂ e) = e)

/-- Isomorphic secrecy implies possibilistic secrecy for every value. -/
theorem Adversary.isomorphic_secret.to_possibilistic_secret
    (adv : Adversary State Label SS LS)
    {V : Type _}
    (secret : V → LTS.Execution State Label → Prop)
    (C : LTS.Execution State Label → Prop)
    (hits : adv.isomorphic_secret secret C)
    (hhas_secret : ∀ e, (toLTS adv.sys).valid_exec e → C e → ∃ v, secret v e)
    (hexcl : ∀ v₁ v₂ e, (toLTS adv.sys).valid_exec e → C e →
      v₁ ≠ v₂ → secret v₁ e → ¬secret v₂ e)
    (s : V) (hne : ∃ s', s' ≠ s) :
    adv.possibilistic_secret (secret s) C := by
  obtain ⟨remap, hpres, _hinv⟩ := hits
  exact adv.possibilistic_secret_by_remap secret C hhas_secret
    (fun v₁ v₂ e σ hval hcons hC hsec =>
      let ⟨hval', hcons', hview', hC', hsec'⟩ := hpres v₁ v₂ e σ hval hcons hC hsec
      ⟨remap v₁ v₂ e, hval', hcons', hview', hC', hsec'⟩)
    hexcl s hne

/-- Establish isomorphic secrecy from a concrete remap with
    an invertibility certificate. -/
theorem Adversary.isomorphic_secret_by_remap (adv : Adversary State Label SS LS)
    {V : Type _}
    (secret : V → LTS.Execution State Label → Prop)
    (C : LTS.Execution State Label → Prop)
    (remap : V → V → LTS.Execution State Label → LTS.Execution State Label)
    (hpres : ∀ v₁ v₂ e (σ : Strategy SS LS),
      (toLTS adv.sys).valid_exec e → adv.consistent σ e → C e → secret v₁ e →
      (toLTS adv.sys).valid_exec (remap v₁ v₂ e) ∧
      adv.consistent σ (remap v₁ v₂ e) ∧
      adv.obs.view e = adv.obs.view (remap v₁ v₂ e) ∧
      C (remap v₁ v₂ e) ∧
      secret v₂ (remap v₁ v₂ e))
    (hinv : ∀ v₁ v₂ e, (toLTS adv.sys).valid_exec e → C e → secret v₁ e →
      remap v₂ v₁ (remap v₁ v₂ e) = e) :
    adv.isomorphic_secret secret C :=
  ⟨remap, hpres, hinv⟩

/-! ## Probabilistic Possibilistic Secrecy

    In an LTS, possibilistic secrecy relies on the scheduler *not* resolving
    all nondeterminism: if it did, there would be a single execution per view,
    and both outcomes could not coexist.

    In a PLTS, even when the scheduler resolves all nondeterminism (fixing a
    unique `(label, distribution)` at each step), multiple executions remain
    possible because the distribution is *sampled*. The probabilistic outcomes
    create uncertainty that the adversary cannot eliminate.

    `prob_possibilistic_secret` uses `exec_measure` — the probability measure
    on infinite state sequences induced by a resolving strategy via the
    Ionescu-Tulcea theorem. Under `observation_resolving`, labels are
    deterministic functions of the state sequence (via `reconstruct_labels`),
    so an execution property `P` lifts to a set of state sequences via
    `reconstructed_exec`. The definition asks that both `P` and `¬P` have
    positive measure — a genuine probabilistic statement that handles both
    finite-prefix properties and infinite-trace properties (e.g., "a label
    appears infinitely often"). -/

/-- Lift an execution property to a set of state sequences via
    `reconstructed_exec`: the execution built by pairing the state sequence
    with the labels uniquely determined by the resolving strategy. -/
def Adversary.lift_to_states (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) [Inhabited Label]
    (σ : Strategy SS LS) (P : LTS.Execution State Label → Prop) :
    Set (ℕ → State) :=
  {ω | P (reconstructed_exec adv hres σ ω)}

/-- Probabilistic possibilistic secrecy: for every resolving strategy,
    every initial state, and every realizable observation, the property `P`
    holds with positive probability but not surely under the induced
    execution measure.

    The condition `C` restricts attention to a subset of executions (e.g.,
    "at most `f` processes are corrupted"). The definition conditions on
    observation `v`: whenever `C`-executions producing observation `v` have
    positive measure, both `C ∧ P` and `C ∧ ¬P` have positive measure
    among executions producing the same observation. The adversary cannot
    determine `P` even knowing `C` and its observation.

    Since `exec_measure` is a probability measure on infinite state sequences
    (via Ionescu-Tulcea), this captures genuine probabilistic uncertainty —
    including for infinite-trace properties like "a label appears infinitely
    often." -/
def Adversary.prob_possibilistic_secret (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    [Countable State] [Inhabited State]
    (P : LTS.Execution State Label → Prop)
    (C : LTS.Execution State Label → Prop) : Prop :=
  ∀ σ s₀ v, adv.sys.init s₀ →
    exec_measure adv hres σ s₀
      (adv.lift_to_states hres σ (fun e => C e ∧ adv.obs.view e = v)) > 0 →
    exec_measure adv hres σ s₀
      (adv.lift_to_states hres σ (fun e => C e ∧ P e ∧ adv.obs.view e = v)) > 0 ∧
    exec_measure adv hres σ s₀
      (adv.lift_to_states hres σ (fun e => C e ∧ ¬P e ∧ adv.obs.view e = v)) > 0

/-- `prob_possibilistic_secret` implies `possibilistic_secret`: positive
    measure implies the set is non-empty (since `μ(∅) = 0`), giving
    witness executions with the same observation.

    The reconstructed execution from any state sequence `ω` is valid and
    consistent by construction (`hrecon`). The side condition `hC_pos`
    ensures that a valid consistent execution with `C` and observation `v`
    implies positive measure for the set `C ∧ view = v`. -/
theorem Adversary.prob_possibilistic_secret.to_possibilistic_secret
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    [Countable State] [Inhabited State]
    (P : LTS.Execution State Label → Prop)
    (C : LTS.Execution State Label → Prop)
    (hprob : adv.prob_possibilistic_secret hres P C)
    (hrecon : ∀ (σ : Strategy SS LS) (ω : ℕ → State),
      (toLTS adv.sys).valid_exec (reconstructed_exec adv hres σ ω) ∧
      adv.consistent σ (reconstructed_exec adv hres σ ω))
    (hC_pos : ∀ (σ : Strategy SS LS) (e : LTS.Execution State Label),
      (toLTS adv.sys).valid_exec e → adv.consistent σ e → C e →
      exec_measure adv hres σ (e.states 0)
        (adv.lift_to_states hres σ
          (fun e' => C e' ∧ adv.obs.view e' = adv.obs.view e)) > 0) :
    adv.possibilistic_secret P C := by
  intro σ v ⟨e, hval, hcons, hview, hC⟩
  have hinit : adv.sys.init (e.states 0) := hval.1
  have hCv_pos := hC_pos σ e hval hcons hC
  rw [hview] at hCv_pos
  obtain ⟨hP_pos, hNP_pos⟩ := hprob σ (e.states 0) v hinit hCv_pos
  -- Positive measure → non-empty: μ(S) > 0 implies S ≠ ∅
  have hne₁ := MeasureTheory.nonempty_of_measure_ne_zero hP_pos.ne'
  have hne₂ := MeasureTheory.nonempty_of_measure_ne_zero hNP_pos.ne'
  obtain ⟨ω₁, hC₁, hp₁, hw₁⟩ := hne₁
  obtain ⟨ω₂, hC₂, hp₂, hw₂⟩ := hne₂
  have ⟨hval₁, hcons₁⟩ := hrecon σ ω₁
  have ⟨hval₂, hcons₂⟩ := hrecon σ ω₂
  exact ⟨⟨_, hval₁, hcons₁, hw₁, hC₁, hp₁⟩, ⟨_, hval₂, hcons₂, hw₂, hC₂, hp₂⟩⟩

/-- **Probabilistic possibilistic secrecy by remap**: if whenever
    `C ∧ view = v` has positive measure under a resolving strategy, every
    secret fiber `C ∧ secret sv ∧ view = v` also has positive measure,
    then `secret sv` is a probabilistic possibilistic secret. -/
theorem Adversary.prob_possibilistic_secret_by_remap (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    [Countable State] [Inhabited State]
    {V : Type _}
    (secret : V → LTS.Execution State Label → Prop)
    (C : LTS.Execution State Label → Prop)
    (hfiber_pos : ∀ w (σ : Strategy SS LS) (s₀ : State)
      (v : Observation.ExecView SS LS),
      adv.sys.init s₀ →
      exec_measure adv hres σ s₀
        (adv.lift_to_states hres σ (fun e => C e ∧ adv.obs.view e = v)) > 0 →
      exec_measure adv hres σ s₀
        (adv.lift_to_states hres σ
          (fun e => C e ∧ secret w e ∧ adv.obs.view e = v)) > 0)
    (hexcl : ∀ v₁ v₂ e, C e → v₁ ≠ v₂ → secret v₁ e → ¬secret v₂ e)
    (sv : V) (hne : ∃ sv', sv' ≠ sv) :
    adv.prob_possibilistic_secret hres (secret sv) C := by
  intro σ s₀ v hinit hCv_pos
  obtain ⟨sv', hsv'⟩ := hne
  constructor
  · exact hfiber_pos sv σ s₀ v hinit hCv_pos
  · have hsv'_pos := hfiber_pos sv' σ s₀ v hinit hCv_pos
    exact lt_of_lt_of_le hsv'_pos (MeasureTheory.measure_mono (fun ω hω => by
      exact ⟨hω.1, hexcl sv' sv _ hω.1 hsv' hω.2.1, hω.2.2⟩))

/-! ## Probabilistic Isomorphic Secrecy

    The probabilistic analogue of `isomorphic_secret`. Instead of a remap
    on executions preserving validity and consistency, the remap operates
    on state sequences `ℕ → State` (since `exec_measure` is a measure on
    state sequences). The invertibility condition of the non-probabilistic
    version (bijection between fibers) becomes **measure preservation**:
    the remap is a measurable bijection whose pushforward preserves the
    execution measure. This ensures that the remap not only swaps secret
    values but does so without distorting probabilities — the adversary
    cannot distinguish secret values even by analyzing the probability
    distribution over executions. -/

/-- Probabilistic isomorphic secrecy: there exists a measurable,
    measure-preserving, invertible remap on state sequences that swaps
    secret values while preserving the condition `C` and the adversary's
    observation.

    Properties of the remap `f v₁ v₂`:
    - **Secret swap**: maps `C ∧ secret v₁` to `C ∧ secret v₂`
    - **View preservation**: the adversary's observation is unchanged
    - **Invertibility**: `f v₂ v₁ ∘ f v₁ v₂ = id` on `C ∧ secret v₁`
    - **Measure preservation**: the pushforward of `exec_measure` under
      `f v₁ v₂` equals `exec_measure`, so probabilities are undistorted -/
def Adversary.prob_isomorphic_secret (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    [Countable State] [Inhabited State]
    {V : Type _}
    (secret : V → LTS.Execution State Label → Prop)
    (C : LTS.Execution State Label → Prop) : Prop :=
  ∃ f : V → V → (ℕ → State) → (ℕ → State),
    -- (1) Remap preserves condition, secret value, and view
    (∀ v₁ v₂ ω σ,
      C (reconstructed_exec adv hres σ ω) →
      secret v₁ (reconstructed_exec adv hres σ ω) →
      C (reconstructed_exec adv hres σ (f v₁ v₂ ω)) ∧
      secret v₂ (reconstructed_exec adv hres σ (f v₁ v₂ ω)) ∧
      adv.obs.view (reconstructed_exec adv hres σ ω) =
        adv.obs.view (reconstructed_exec adv hres σ (f v₁ v₂ ω))) ∧
    -- (2) Remap is invertible on fibers
    (∀ v₁ v₂ ω σ,
      C (reconstructed_exec adv hres σ ω) →
      secret v₁ (reconstructed_exec adv hres σ ω) →
      f v₂ v₁ (f v₁ v₂ ω) = ω) ∧
    -- (3) Remap is measure-preserving
    (∀ v₁ v₂ σ s₀,
      adv.sys.init s₀ →
      MeasureTheory.Measure.map (f v₁ v₂) (exec_measure adv hres σ s₀) =
        exec_measure adv hres σ s₀)

/-- Core transfer lemma: the measure-preserving remap shows that every
    secret fiber has at least as much measure as any other fiber. -/
private theorem fiber_measure_transfer
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    [Countable State] [Inhabited State]
    {V : Type _}
    (secret : V → LTS.Execution State Label → Prop)
    (C : LTS.Execution State Label → Prop)
    (f : V → V → (ℕ → State) → (ℕ → State))
    (hpres : ∀ v₁ v₂ ω σ,
      C (reconstructed_exec adv hres σ ω) →
      secret v₁ (reconstructed_exec adv hres σ ω) →
      C (reconstructed_exec adv hres σ (f v₁ v₂ ω)) ∧
      secret v₂ (reconstructed_exec adv hres σ (f v₁ v₂ ω)) ∧
      adv.obs.view (reconstructed_exec adv hres σ ω) =
        adv.obs.view (reconstructed_exec adv hres σ (f v₁ v₂ ω)))
    (hmp : ∀ v₁ v₂ σ s₀, adv.sys.init s₀ →
      MeasureTheory.Measure.map (f v₁ v₂) (exec_measure adv hres σ s₀) =
        exec_measure adv hres σ s₀)
    (hmeas_f : ∀ v₁ v₂, Measurable (f v₁ v₂))
    (hmeas_set : ∀ v σ (v' : Observation.ExecView SS LS),
      MeasurableSet (adv.lift_to_states hres σ
        (fun e => C e ∧ secret v e ∧ adv.obs.view e = v')))
    (w₁ w₂ : V) (σ : Strategy SS LS) (s₀ : State) (hinit : adv.sys.init s₀)
    (v' : Observation.ExecView SS LS) :
    exec_measure adv hres σ s₀
      (adv.lift_to_states hres σ (fun e => C e ∧ secret w₁ e ∧ adv.obs.view e = v')) ≤
    exec_measure adv hres σ s₀
      (adv.lift_to_states hres σ (fun e => C e ∧ secret w₂ e ∧ adv.obs.view e = v')) := by
  -- map (f w₁ w₂) μ = μ, so μ((f w₁ w₂)⁻¹ S) = μ(S) for measurable S
  -- fiber w₁ ⊆ (f w₁ w₂)⁻¹(fiber w₂), so μ(fiber w₂) = μ((f w₁ w₂)⁻¹(fiber w₂)) ≥ μ(fiber w₁)
  set μ := exec_measure adv hres σ s₀
  set S := adv.lift_to_states hres σ
    (fun e => C e ∧ secret w₂ e ∧ adv.obs.view e = v')
  have hmap := hmp w₁ w₂ σ s₀ hinit
  -- μ(S) = (map (f w₁ w₂) μ)(S) = μ((f w₁ w₂)⁻¹' S)
  have hpreimage : μ ((f w₁ w₂) ⁻¹' S) = μ S := by
    rw [← MeasureTheory.Measure.map_apply (hmeas_f w₁ w₂) (hmeas_set w₂ σ v'), hmap]
  -- fiber w₁ ⊆ (f w₁ w₂)⁻¹' S
  have hsub : adv.lift_to_states hres σ
      (fun e => C e ∧ secret w₁ e ∧ adv.obs.view e = v') ⊆
      (f w₁ w₂) ⁻¹' S := by
    intro ω ⟨hC, hsec, hview⟩
    obtain ⟨hC', hsec', hview'⟩ := hpres w₁ w₂ ω σ hC hsec
    exact ⟨hC', hsec', hview ▸ hview'.symm⟩
  calc μ (adv.lift_to_states hres σ
        (fun e => C e ∧ secret w₁ e ∧ adv.obs.view e = v'))
      ≤ μ ((f w₁ w₂) ⁻¹' S) := MeasureTheory.measure_mono hsub
    _ = μ S := hpreimage

/-- Probabilistic isomorphic secrecy implies probabilistic possibilistic
    secrecy: the measure-preserving remap bijects `C ∧ secret v₁ ∧ view = v`
    onto `C ∧ secret v₂ ∧ view = v`, preserving measure. So if one fiber
    has positive measure, all fibers do. -/
theorem Adversary.prob_isomorphic_secret.to_prob_possibilistic_secret
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    [Countable State] [Inhabited State]
    {V : Type _} [Countable V]
    (secret : V → LTS.Execution State Label → Prop)
    (C : LTS.Execution State Label → Prop)
    (hits : adv.prob_isomorphic_secret hres secret C)
    (hexcl : ∀ v₁ v₂ e, C e → v₁ ≠ v₂ → secret v₁ e → ¬secret v₂ e)
    (hhas_secret : ∀ e, C e → ∃ v, secret v e)
    (sv : V) (hne : ∃ sv', sv' ≠ sv)
    (hmeas_f : ∀ (v₁ v₂ : V), Measurable (hits.choose v₁ v₂))
    (hmeas : ∀ v σ (v' : Observation.ExecView SS LS),
      MeasurableSet (adv.lift_to_states hres σ
        (fun e => C e ∧ secret v e ∧ adv.obs.view e = v')))
    :
    adv.prob_possibilistic_secret hres (secret sv) C := by
  set f := hits.choose with hf_def
  have hpres := hits.choose_spec.1
  have hinv := hits.choose_spec.2.1
  have hmp := hits.choose_spec.2.2
  obtain ⟨sv', hsv'⟩ := hne
  -- Use the by_remap proof rule: need every fiber to have positive measure
  apply adv.prob_possibilistic_secret_by_remap hres secret C _ hexcl sv ⟨sv', hsv'⟩
  -- Goal: hfiber_pos — ∀ w σ s₀ v, ... → μ(C ∧ secret w ∧ view = v) > 0
  intro w σ s₀ v hinit hCv_pos
  -- Step 1: C ∧ view = v ⊆ ⋃_w₀, (C ∧ secret w₀ ∧ view = v)
  have hcover : adv.lift_to_states hres σ (fun e => C e ∧ adv.obs.view e = v) ⊆
      ⋃ w₀ : V, adv.lift_to_states hres σ
        (fun e => C e ∧ secret w₀ e ∧ adv.obs.view e = v) := by
    intro ω ⟨hC, hview⟩
    obtain ⟨w₀, hw₀⟩ := hhas_secret _ hC
    exact Set.mem_iUnion.mpr ⟨w₀, hC, hw₀, hview⟩
  -- Step 2: Some fiber has positive measure (countable subadditivity)
  have hsome_pos : ∃ w₀ : V, exec_measure adv hres σ s₀
      (adv.lift_to_states hres σ
        (fun e => C e ∧ secret w₀ e ∧ adv.obs.view e = v)) > 0 := by
    by_contra hall
    push Not at hall
    have hall' : ∀ w₀, exec_measure adv hres σ s₀
        (adv.lift_to_states hres σ
          (fun e => C e ∧ secret w₀ e ∧ adv.obs.view e = v)) = 0 :=
      fun w₀ => le_antisymm (hall w₀) (zero_le _)
    have hle := (MeasureTheory.measure_mono hcover).trans
      (MeasureTheory.measure_iUnion_le
        (s := fun w₀ => adv.lift_to_states hres σ
          (fun e => C e ∧ secret w₀ e ∧ adv.obs.view e = v))
        (μ := exec_measure adv hres σ s₀))
    simp only [hall'] at hle
    rw [tsum_zero] at hle
    exact absurd (le_antisymm hle (zero_le _)) hCv_pos.ne'
  -- Step 3: Transfer to target fiber w
  obtain ⟨w₀, hw₀_pos⟩ := hsome_pos
  exact lt_of_lt_of_le hw₀_pos
    (fiber_measure_transfer adv hres secret C f hpres hmp hmeas_f hmeas
      w₀ w σ s₀ hinit v)

end PLTS
