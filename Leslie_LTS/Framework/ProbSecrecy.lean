import Leslie_LTS.Framework.Secrecy
import Leslie_LTS.Framework.RandProbExec

/-! # Probabilistic Secrecy Properties for PLTS Adversaries

    This module defines probabilistic secrecy notions that build on the
    possibilistic secrecy framework in `Leslie_LTS.Framework.Secrecy`.
    These use `rand_exec_measure` — the probability measure on infinite
    state–label sequences induced by a resolving randomised strategy via
    the Ionescu-Tulcea theorem.
-/

namespace PLTS

variable {State : Type u} {Label : Type v}
variable {SS : Type w} {LS : Type x}

/-! ## Probabilistic Inferability

    Probabilistic analogues of the inferability notions in `Secrecy.lean`.
    Where possibilistic inferability asks whether *all* executions satisfy `P`,
    probabilistic inferability asks whether `P` holds *almost surely* under
    the execution measure.

    The definitions use `rand_exec_measure` — the probability measure on
    infinite state–label sequences induced by a resolving strategy via the
    Ionescu-Tulcea theorem. An execution property `P` lifts to a set of
    state–label sequences via `rand_to_exec`. -/

/-- Lift an execution property to a set of state–label sequences via
    `rand_to_exec`: the execution built by extracting the state and label
    components from each pair. -/
def Adversary.lift_to_exec (_adv : Adversary State Label SS LS)
    (P : LTS.Execution State Label → Prop) :
    Set (ℕ → State × Label) :=
  {ω | P (rand_to_exec ω)}

/-- `P` is **probabilistically positively inferable** from observation `v`
    under resolving strategy `σ` and initial state `s₀`: among all
    executions with view `v`, `P` holds almost surely — the set of
    state–label sequences producing view `v` and `¬P` has measure zero. -/
def Adversary.prob_positively_inferable (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    [Countable State] [Inhabited State]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]
    (σ : Strategy SS LS) (s₀ : State)
    (P : LTS.Execution State Label → Prop)
    (v : Observation.ExecView SS LS) : Prop :=
  rand_exec_measure adv hres σ.toRandomised s₀
    (adv.lift_to_exec (fun e => adv.obs.view e = v ∧ ¬P e)) = 0

/-- `P` is **probabilistically negatively inferable** from observation `v`
    under resolving strategy `σ` and initial state `s₀`: among all
    executions with view `v`, `¬P` holds almost surely — the set of
    state–label sequences producing view `v` and `P` has measure zero. -/
def Adversary.prob_negatively_inferable (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    [Countable State] [Inhabited State]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]
    (σ : Strategy SS LS) (s₀ : State)
    (P : LTS.Execution State Label → Prop)
    (v : Observation.ExecView SS LS) : Prop :=
  rand_exec_measure adv hres σ.toRandomised s₀
    (adv.lift_to_exec (fun e => adv.obs.view e = v ∧ P e)) = 0

/-- `P` is **probabilistically not inferable** from observation `v`
    under resolving strategy `σ` and initial state `s₀`: if the observation
    is realizable (has positive measure), then `P` is neither almost surely
    true nor almost surely false — both `P` and `¬P` have positive
    probability among executions with view `v`.

    The realizability guard (positive measure of `{view = v}`) mirrors
    the possibilistic realizability guard (∃ execution with view v). -/
def Adversary.prob_not_inferable (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    [Countable State] [Inhabited State]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]
    (σ : Strategy SS LS) (s₀ : State)
    (P : LTS.Execution State Label → Prop)
    (v : Observation.ExecView SS LS) : Prop :=
  rand_exec_measure adv hres σ.toRandomised s₀
    (adv.lift_to_exec (fun e => adv.obs.view e = v)) > 0 →
  ¬adv.prob_positively_inferable hres σ s₀ P v ∧
  ¬adv.prob_negatively_inferable hres σ s₀ P v

/-! ## Probabilistic Possibilistic Secrecy

    The probabilistic analogue of `possibilistic_secret`: for every resolving
    strategy, initial state, and `C`-satisfying view, `P` is probabilistically
    not inferable.

    Since `rand_exec_measure` with `σ.toRandomised` requires a resolving
    strategy (deterministic), this quantifies over deterministic strategies
    `σ : Strategy SS LS`. -/

/-- Probabilistic possibilistic secrecy: for every resolving strategy `σ`,
    initial state `s₀`, and `C`-satisfying view `v`, the property `P` is
    probabilistically not inferable — both `P` and `¬P` have positive
    probability among executions with view `v`. -/
def Adversary.prob_possibilistic_secret (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    [Countable State] [Inhabited State]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]
    (P : LTS.Execution State Label → Prop)
    (C : Observation.ExecView SS LS → Prop) : Prop :=
  ∀ σ s₀, adv.sys.init s₀ →
    ∀ v, C v → adv.prob_not_inferable hres σ s₀ P v

/-- `prob_possibilistic_secret` implies `possibilistic_secret`: positive
    measure implies non-empty support, giving witness executions.

    The hypothesis `hrecon` ensures that each `ω` in the support encodes
    a valid, consistent execution via `rand_to_exec`. -/
theorem Adversary.prob_possibilistic_secret.to_possibilistic_secret
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    [Countable State] [Inhabited State]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]
    (P : LTS.Execution State Label → Prop)
    (C : Observation.ExecView SS LS → Prop)
    (hprob : adv.prob_possibilistic_secret hres P C)
    (hrecon : ∀ (σ : Strategy SS LS) (ω : ℕ → State × Label),
      (toLTS adv.sys).valid_exec (rand_to_exec ω) ∧
      adv.consistent σ (rand_to_exec ω))
    (hview_pos : ∀ σ s₀ v, adv.sys.init s₀ →
      (∃ e, (toLTS adv.sys).valid_exec e ∧ adv.consistent σ e ∧
        adv.obs.view e = v ∧ e.states 0 = s₀) →
      rand_exec_measure adv hres σ.toRandomised s₀
        (adv.lift_to_exec (fun e => adv.obs.view e = v)) > 0) :
    adv.possibilistic_secret P C := by
  intro ρ v hCv ⟨e₀, hval₀, hcons_r₀, hview₀⟩
  -- Extract deterministic strategy from e₀
  obtain ⟨σ, hcons₀⟩ := adv.consistent_of_randomised_consistent ρ e₀ hcons_r₀
  have hinit : adv.sys.init (e₀.states 0) := hval₀.1
  -- Get positive measure for {view = v} under σ
  have hμ_pos := hview_pos σ (e₀.states 0) v hinit ⟨e₀, hval₀, hcons₀, hview₀, rfl⟩
  -- Apply prob_not_inferable
  obtain ⟨hnpos, hnneg⟩ := hprob σ (e₀.states 0) hinit v hCv hμ_pos
  -- ¬prob_positively_inferable means μ({view=v ∧ ¬P}) ≠ 0
  -- ¬prob_negatively_inferable means μ({view=v ∧ P}) ≠ 0
  simp only [prob_positively_inferable] at hnpos
  simp only [prob_negatively_inferable] at hnneg
  -- Positive measure → non-empty
  have hne₁ := MeasureTheory.nonempty_of_measure_ne_zero hnneg
  have hne₂ := MeasureTheory.nonempty_of_measure_ne_zero hnpos
  obtain ⟨ω₁, hview₁, hp₁⟩ := hne₁
  obtain ⟨ω₂, hview₂, hp₂⟩ := hne₂
  -- Reconstructed executions are valid
  have ⟨hval₁, _⟩ := hrecon σ ω₁
  have ⟨hval₂, _⟩ := hrecon σ ω₂
  -- Transfer ρ-consistency from e₀ via same view
  have transfer : ∀ e', adv.obs.view e₀ = adv.obs.view e' →
      adv.randomised_consistent ρ e' := by
    intro e' hveq
    exact adv.randomised_consistent_of_indistinguishable ρ
      ⟨congr_fun (congr_arg Observation.ExecView.state_signals hveq),
       congr_fun (congr_arg Observation.ExecView.label_signals hveq)⟩ hcons_r₀
  exact ⟨fun hpos => hp₂ (hpos _ hval₂
          (transfer _ (hview₀.trans hview₂.symm)) hview₂),
         fun hneg => hneg _ hval₁
          (transfer _ (hview₀.trans hview₁.symm)) hview₁ hp₁⟩

/-! ## Probabilistic Isomorphic Secrecy

    The probabilistic analogue of `isomorphic_secret`. Instead of a remap
    on executions preserving validity and consistency, the remap operates
    on state–label sequences `ℕ → State × Label` (since `rand_exec_measure`
    is a measure on state–label sequences). The invertibility condition of
    the non-probabilistic version (bijection between fibers) becomes
    **measure preservation**: the remap is a measurable bijection whose
    pushforward preserves the execution measure. This ensures that the
    remap not only swaps secret values but does so without distorting
    probabilities — the adversary cannot distinguish secret values even
    by analyzing the probability distribution over executions. -/

/-- Probabilistic isomorphic secrecy: there exists a measurable,
    measure-preserving, invertible remap on state–label sequences that
    swaps secret values while preserving the condition `C` and the
    adversary's observation.

    Properties of the remap `f v₁ v₂`:
    - **Secret swap**: maps `C ∧ secret v₁` to `C ∧ secret v₂`
    - **View preservation**: the adversary's observation is unchanged
    - **Invertibility**: `f v₂ v₁ ∘ f v₁ v₂ = id` on `C ∧ secret v₁`
    - **Measure preservation**: the pushforward of `rand_exec_measure` under
      `f v₁ v₂` equals `rand_exec_measure`, so probabilities are undistorted -/
def Adversary.prob_isomorphic_secret (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    [Countable State] [Inhabited State]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]
    {V : Type _}
    (secret : V → LTS.Execution State Label → Prop)
    (C : LTS.Execution State Label → Prop) : Prop :=
  ∃ f : V → V → (ℕ → State × Label) → (ℕ → State × Label),
    -- (1) Remap preserves condition, secret value, and view
    (∀ v₁ v₂ ω,
      C (rand_to_exec ω) →
      secret v₁ (rand_to_exec ω) →
      C (rand_to_exec (f v₁ v₂ ω)) ∧
      secret v₂ (rand_to_exec (f v₁ v₂ ω)) ∧
      adv.obs.view (rand_to_exec ω) =
        adv.obs.view (rand_to_exec (f v₁ v₂ ω))) ∧
    -- (2) Remap is invertible on fibers
    (∀ v₁ v₂ ω,
      C (rand_to_exec ω) →
      secret v₁ (rand_to_exec ω) →
      f v₂ v₁ (f v₁ v₂ ω) = ω) ∧
    -- (3) Remap is measure-preserving
    (∀ v₁ v₂ (σ : Strategy SS LS) s₀,
      adv.sys.init s₀ →
      MeasureTheory.Measure.map (f v₁ v₂) (rand_exec_measure adv hres σ.toRandomised s₀) =
        rand_exec_measure adv hres σ.toRandomised s₀)

/-- Core transfer lemma: the measure-preserving remap shows that every
    secret fiber has at least as much measure as any other fiber. -/
private theorem fiber_measure_transfer
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    [Countable State] [Inhabited State]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]
    {V : Type _}
    (secret : V → LTS.Execution State Label → Prop)
    (C : LTS.Execution State Label → Prop)
    (f : V → V → (ℕ → State × Label) → (ℕ → State × Label))
    (hpres : ∀ v₁ v₂ ω,
      C (rand_to_exec ω) →
      secret v₁ (rand_to_exec ω) →
      C (rand_to_exec (f v₁ v₂ ω)) ∧
      secret v₂ (rand_to_exec (f v₁ v₂ ω)) ∧
      adv.obs.view (rand_to_exec ω) =
        adv.obs.view (rand_to_exec (f v₁ v₂ ω)))
    (hmp : ∀ v₁ v₂ (σ : Strategy SS LS) s₀, adv.sys.init s₀ →
      MeasureTheory.Measure.map (f v₁ v₂) (rand_exec_measure adv hres σ.toRandomised s₀) =
        rand_exec_measure adv hres σ.toRandomised s₀)
    (hmeas_f : ∀ v₁ v₂, Measurable (f v₁ v₂))
    (hmeas_set : ∀ v (v' : Observation.ExecView SS LS),
      MeasurableSet (adv.lift_to_exec
        (fun e => C e ∧ secret v e ∧ adv.obs.view e = v')))
    (w₁ w₂ : V) (σ : Strategy SS LS) (s₀ : State) (hinit : adv.sys.init s₀)
    (v' : Observation.ExecView SS LS) :
    rand_exec_measure adv hres σ.toRandomised s₀
      (adv.lift_to_exec (fun e => C e ∧ secret w₁ e ∧ adv.obs.view e = v')) ≤
    rand_exec_measure adv hres σ.toRandomised s₀
      (adv.lift_to_exec (fun e => C e ∧ secret w₂ e ∧ adv.obs.view e = v')) := by
  -- map (f w₁ w₂) μ = μ, so μ((f w₁ w₂)⁻¹ S) = μ(S) for measurable S
  -- fiber w₁ ⊆ (f w₁ w₂)⁻¹(fiber w₂), so μ(fiber w₂) = μ((f w₁ w₂)⁻¹(fiber w₂)) ≥ μ(fiber w₁)
  set μ := rand_exec_measure adv hres σ.toRandomised s₀
  set S := adv.lift_to_exec
    (fun e => C e ∧ secret w₂ e ∧ adv.obs.view e = v')
  have hmap := hmp w₁ w₂ σ s₀ hinit
  -- μ(S) = (map (f w₁ w₂) μ)(S) = μ((f w₁ w₂)⁻¹' S)
  have hpreimage : μ ((f w₁ w₂) ⁻¹' S) = μ S := by
    rw [← MeasureTheory.Measure.map_apply (hmeas_f w₁ w₂) (hmeas_set w₂ v'), hmap]
  -- fiber w₁ ⊆ (f w₁ w₂)⁻¹' S
  have hsub : adv.lift_to_exec
      (fun e => C e ∧ secret w₁ e ∧ adv.obs.view e = v') ⊆
      (f w₁ w₂) ⁻¹' S := by
    intro ω ⟨hC, hsec, hview⟩
    obtain ⟨hC', hsec', hview'⟩ := hpres w₁ w₂ ω hC hsec
    exact ⟨hC', hsec', hview ▸ hview'.symm⟩
  calc μ (adv.lift_to_exec
        (fun e => C e ∧ secret w₁ e ∧ adv.obs.view e = v'))
      ≤ μ ((f w₁ w₂) ⁻¹' S) := MeasureTheory.measure_mono hsub
    _ = μ S := hpreimage

/-! ## Information-Theoretic Secrecy

    Information-theoretic secrecy (Shannon secrecy): the adversary's observation
    is statistically independent of the secret value. Formally, for every pair
    of secret values `v₁, v₂`, every deterministic strategy `σ`, every initial
    state `s₀`, and every observation `o`, the execution measure assigns equal
    weight to the fibers `{C ∧ secret v₁ ∧ view = o}` and
    `{C ∧ secret v₂ ∧ view = o}`.

    This is the **likelihood equality** form of perfect secrecy:
      `μ(secret = v₁ ∧ view = o) = μ(secret = v₂ ∧ view = o)`
    which (after dividing by the marginal `μ(secret = v)`) is equivalent to
      `Pr[view = o | secret = v]` being constant in `v`. -/

/-- Information-theoretic secrecy: the measure of each (secret, view) fiber
    is independent of the secret value. For all `v₁, v₂`, strategies, initial
    states, and observations:
      `μ({C ∧ secret v₁ ∧ view = o}) = μ({C ∧ secret v₂ ∧ view = o})` -/
def Adversary.info_theoretic_secret (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    [Countable State] [Inhabited State]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]
    {V : Type _}
    (secret : V → LTS.Execution State Label → Prop)
    (C : LTS.Execution State Label → Prop) : Prop :=
  ∀ v₁ v₂ (σ : Strategy SS LS) s₀,
    adv.sys.init s₀ →
    ∀ o : Observation.ExecView SS LS,
      rand_exec_measure adv hres σ.toRandomised s₀
        (adv.lift_to_exec (fun e => C e ∧ secret v₁ e ∧ adv.obs.view e = o)) =
      rand_exec_measure adv hres σ.toRandomised s₀
        (adv.lift_to_exec (fun e => C e ∧ secret v₂ e ∧ adv.obs.view e = o))

/-- Probabilistic isomorphic secrecy implies information-theoretic secrecy:
    the measure-preserving remap gives `μ(fiber v₁) ≤ μ(fiber v₂)` via
    `fiber_measure_transfer`; applying in both directions yields equality. -/
theorem Adversary.prob_isomorphic_secret.to_info_theoretic_secret
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) [Inhabited Label]
    [MeasurableSpace State] [MeasurableSingletonClass State]
    [Countable State] [Inhabited State]
    [MeasurableSpace Label] [MeasurableSingletonClass Label] [Countable Label]
    {V : Type _}
    (secret : V → LTS.Execution State Label → Prop)
    (C : LTS.Execution State Label → Prop)
    (hits : adv.prob_isomorphic_secret hres secret C)
    (hmeas_f : ∀ (v₁ v₂ : V), Measurable (hits.choose v₁ v₂))
    (hmeas_set : ∀ v (o : Observation.ExecView SS LS),
      MeasurableSet (adv.lift_to_exec
        (fun e => C e ∧ secret v e ∧ adv.obs.view e = o))) :
    adv.info_theoretic_secret hres secret C := by
  intro v₁ v₂ σ s₀ hinit o
  have ⟨hpres, _, hmp⟩ := hits.choose_spec
  exact le_antisymm
    (fiber_measure_transfer adv hres secret C hits.choose hpres hmp
      hmeas_f hmeas_set v₁ v₂ σ s₀ hinit o)
    (fiber_measure_transfer adv hres secret C hits.choose hpres hmp
      hmeas_f hmeas_set v₂ v₁ σ s₀ hinit o)

end PLTS
