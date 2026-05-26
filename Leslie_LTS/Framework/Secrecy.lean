import Leslie_LTS.Framework.Adversary

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

    The definitions use **randomised strategies** as the primary scheduling
    model. Deterministic strategies are a special case via `Strategy.toRandomised`.

    - `P` is **positively inferable** from an observation if all valid
      randomised-consistent executions with that observation satisfy `P`.
    - `P` is **negatively inferable** if all such executions do not satisfy `P`.
    - `P` is **not inferable** if (given realizability) it is neither
      positively nor negatively inferable. -/

/-- An execution is consistent with an observation `v` if the adversary's
    view of the execution equals `v`. -/
def Adversary.consistent_with_view (adv : Adversary State Label SS LS)
    (e : LTS.Execution State Label) (v : Observation.ExecView SS LS) : Prop :=
  adv.obs.view e = v

/-- `P` is **positively inferable** from observation `v` under randomised
    strategy `ρ`: every valid randomised-consistent execution with view `v`
    satisfies `P`. -/
def Adversary.positively_inferable (adv : Adversary State Label SS LS)
    (ρ : RandomisedStrategy SS LS)
    (P : LTS.Execution State Label → Prop)
    (v : Observation.ExecView SS LS) : Prop :=
  ∀ e, (toLTS adv.sys).valid_exec e → adv.randomised_consistent ρ e →
    adv.consistent_with_view e v → P e

/-- `P` is **negatively inferable** from observation `v` under randomised
    strategy `ρ`: every valid randomised-consistent execution with view `v`
    does *not* satisfy `P`. -/
def Adversary.negatively_inferable (adv : Adversary State Label SS LS)
    (ρ : RandomisedStrategy SS LS)
    (P : LTS.Execution State Label → Prop)
    (v : Observation.ExecView SS LS) : Prop :=
  ∀ e, (toLTS adv.sys).valid_exec e → adv.randomised_consistent ρ e →
    adv.consistent_with_view e v → ¬P e

/-- `P` is **not inferable** from observation `v` under randomised
    strategy `ρ`: if the observation is realizable, then neither positive
    nor negative inferability holds.

    The realizability guard ensures vacuous truth for unrealizable
    observations. -/
def Adversary.not_inferable (adv : Adversary State Label SS LS)
    (ρ : RandomisedStrategy SS LS)
    (P : LTS.Execution State Label → Prop)
    (v : Observation.ExecView SS LS) : Prop :=
  (∃ e, (toLTS adv.sys).valid_exec e ∧ adv.randomised_consistent ρ e ∧
    adv.consistent_with_view e v) →
  ¬adv.positively_inferable ρ P v ∧ ¬adv.negatively_inferable ρ P v

/-- If a property is not inferable and the observation is realizable,
    there exist two valid randomised-consistent executions with that
    observation: one satisfying `P` and one not. -/
theorem Adversary.not_inferable_witnesses (adv : Adversary State Label SS LS)
    (ρ : RandomisedStrategy SS LS)
    (P : LTS.Execution State Label → Prop)
    (v : Observation.ExecView SS LS)
    (h : adv.not_inferable ρ P v)
    (hreal : ∃ e, (toLTS adv.sys).valid_exec e ∧ adv.randomised_consistent ρ e ∧
      adv.consistent_with_view e v) :
    (∃ e, (toLTS adv.sys).valid_exec e ∧ adv.randomised_consistent ρ e ∧
      adv.consistent_with_view e v ∧ P e) ∧
    (∃ e, (toLTS adv.sys).valid_exec e ∧ adv.randomised_consistent ρ e ∧
      adv.consistent_with_view e v ∧ ¬P e) := by
  obtain ⟨hnpos, hnneg⟩ := h hreal
  constructor
  · exact Classical.byContradiction fun hc =>
      hnneg (fun e hv hρ hobs hp => hc ⟨e, hv, hρ, hobs, hp⟩)
  · exact Classical.byContradiction fun hc =>
      hnpos (fun e hv hρ hobs =>
        Classical.byContradiction (fun hnp => hc ⟨e, hv, hρ, hobs, hnp⟩))

/-- Positive and negative inferability are mutually exclusive
    (assuming some execution is consistent and produces the observation). -/
theorem Adversary.not_both_inferable (adv : Adversary State Label SS LS)
    (ρ : RandomisedStrategy SS LS)
    (P : LTS.Execution State Label → Prop)
    (v : Observation.ExecView SS LS)
    (e : LTS.Execution State Label)
    (hv : (toLTS adv.sys).valid_exec e) (hρ : adv.randomised_consistent ρ e)
    (hobs : adv.consistent_with_view e v) :
    ¬(adv.positively_inferable ρ P v ∧ adv.negatively_inferable ρ P v) := by
  intro ⟨hpos, hneg⟩
  exact hneg e hv hρ hobs (hpos e hv hρ hobs)

/-! ## Possibilistic Secrecy

    Possibilistic secrecy (non-deducibility): the adversary cannot determine
    whether a property holds from its observation — both outcomes are possible.

    The definition quantifies over all **randomised strategies**. Deterministic
    strategies are a special case via `Strategy.toRandomised`. -/

/-- Possibilistic secrecy: a trace property `P` is a **possibilistic secret**
    under observation condition `C` if, for every randomised strategy `ρ` and
    every view `v` satisfying `C`, the property `P` is not inferable from `v` —
    both `P` and `¬P` are compatible with the observation.
    This is also known as non-deducibility. -/
def Adversary.possibilistic_secret (adv : Adversary State Label SS LS)
    (P : LTS.Execution State Label → Prop)
    (C : Observation.ExecView SS LS → Prop) : Prop :=
  ∀ ρ : RandomisedStrategy SS LS, ∀ v, C v → adv.not_inferable ρ P v

/-- Possibilistic secrecy against deterministic strategies only.
    This is weaker than `possibilistic_secret` (which quantifies over all
    randomised strategies), but is often easier to prove directly.
    Use `possibilistic_secret_of_det` to lift to the full definition. -/
def Adversary.det_possibilistic_secret (adv : Adversary State Label SS LS)
    (P : LTS.Execution State Label → Prop)
    (C : Observation.ExecView SS LS → Prop) : Prop :=
  ∀ σ : Strategy SS LS, ∀ v, C v → adv.not_inferable σ.toRandomised P v

/-- **Lifting theorem**: possibilistic secrecy against deterministic
    strategies implies possibilistic secrecy against all (randomised)
    strategies.

    Given a randomised-consistent execution `e₀`, we extract a deterministic
    `σ` consistent with `e₀`, lift to `σ.toRandomised`-consistency, apply
    `det_possibilistic_secret` to obtain witnesses sharing the same view,
    then transfer randomised consistency from `e₀` to the witnesses via
    `randomised_consistent_of_indistinguishable`. -/
theorem Adversary.possibilistic_secret_of_det
    (adv : Adversary State Label SS LS)
    (P : LTS.Execution State Label → Prop)
    (C : Observation.ExecView SS LS → Prop)
    (h : adv.det_possibilistic_secret P C) :
    adv.possibilistic_secret P C := by
  intro ρ v hCv ⟨e₀, hval₀, hcons_r₀, hview₀⟩
  -- Extract a deterministic strategy and lift to randomised
  obtain ⟨σ, hcons₀⟩ := adv.consistent_of_randomised_consistent ρ e₀ hcons_r₀
  have hcons_r₀' := adv.consistent_toRandomised σ e₀ hcons₀
  -- Get witnesses from deterministic possibilistic secrecy
  obtain ⟨⟨e₁, hval₁, _, hview₁, hp₁⟩, ⟨e₂, hval₂, _, hview₂, hp₂⟩⟩ :=
    adv.not_inferable_witnesses σ.toRandomised P v (h σ v hCv)
      ⟨e₀, hval₀, hcons_r₀', hview₀⟩
  -- Same view → indistinguishable → transfer ρ-consistency from e₀
  have mk_indist : ∀ e, adv.consistent_with_view e v →
      adv.indistinguishable e₀ e := by
    intro e hview
    have hveq : adv.obs.view e₀ = adv.obs.view e := hview₀.trans hview.symm
    exact ⟨congr_fun (congr_arg Observation.ExecView.state_signals hveq),
           congr_fun (congr_arg Observation.ExecView.label_signals hveq)⟩
  have hρ₁ := adv.randomised_consistent_of_indistinguishable ρ (mk_indist e₁ hview₁) hcons_r₀
  have hρ₂ := adv.randomised_consistent_of_indistinguishable ρ (mk_indist e₂ hview₂) hcons_r₀
  exact ⟨fun hpos => hp₂ (hpos e₂ hval₂ hρ₂ hview₂),
         fun hneg => hneg e₁ hval₁ hρ₁ hview₁ hp₁⟩

/-! ### Possibilistic Secrecy Proof Rule

    A general proof rule for establishing `possibilistic_secret` via a **remap**
    argument. -/

/-- **Possibilistic secrecy by remap**: given a family of secret predicates
    indexed by `V`, an observation condition `C`, if every valid execution
    whose view satisfies `C` has some secret value, the secret value can be
    remapped while preserving validity and view, and distinct values are
    exclusive, then `secret s` is a possibilistic secret under `C`.

    The remap hypotheses are scheduling-model-independent: they only require
    validity and view preservation. Randomised consistency of the remap
    witnesses is obtained automatically via `randomised_consistent_of_indistinguishable`
    (same view ⟹ indistinguishable ⟹ consistency transfers). -/
theorem Adversary.possibilistic_secret_by_remap (adv : Adversary State Label SS LS)
    {V : Type _}
    (secret : V → LTS.Execution State Label → Prop)
    (C : Observation.ExecView SS LS → Prop)
    (hhas_secret : ∀ e, (toLTS adv.sys).valid_exec e →
      C (adv.obs.view e) → ∃ v, secret v e)
    (hremap : ∀ v₁ v₂ e,
      (toLTS adv.sys).valid_exec e → C (adv.obs.view e) → secret v₁ e →
      ∃ e', (toLTS adv.sys).valid_exec e' ∧
        adv.obs.view e = adv.obs.view e' ∧ secret v₂ e')
    (hexcl : ∀ v₁ v₂ e, (toLTS adv.sys).valid_exec e →
      C (adv.obs.view e) → v₁ ≠ v₂ → secret v₁ e → ¬secret v₂ e)
    (s : V) (hne : ∃ s', s' ≠ s) :
    adv.possibilistic_secret (secret s) C := by
  intro ρ v hCv ⟨e₀, hvalid₀, hcons_r₀, hview₀⟩
  have hCe₀ : C (adv.obs.view e₀) := hview₀ ▸ hCv
  obtain ⟨v₀, hv₀⟩ := hhas_secret e₀ hvalid₀ hCe₀
  obtain ⟨s', hs'⟩ := hne
  -- Helper: same view as e₀ → indistinguishable → randomised-consistent with ρ
  have transfer : ∀ e', adv.obs.view e₀ = adv.obs.view e' →
      adv.randomised_consistent ρ e' := by
    intro e' hveq
    exact adv.randomised_consistent_of_indistinguishable ρ
      ⟨congr_fun (congr_arg Observation.ExecView.state_signals hveq),
       congr_fun (congr_arg Observation.ExecView.label_signals hveq)⟩ hcons_r₀
  have view_eq : ∀ e', adv.obs.view e₀ = adv.obs.view e' →
      adv.consistent_with_view e' v := fun e' hw' => hw'.symm.trans hview₀
  constructor
  · -- ¬positively_inferable: exhibit execution with ¬(secret s)
    obtain ⟨e', hv', hw', hsec'⟩ := hremap v₀ s' e₀ hvalid₀ hCe₀ hv₀
    intro hpos
    have hCe' : C (adv.obs.view e') := hw' ▸ hCe₀
    exact hexcl s' s e' hv' hCe' hs' hsec'
      (hpos e' hv' (transfer e' hw') (view_eq e' hw'))
  · -- ¬negatively_inferable: exhibit execution with secret s
    obtain ⟨e', hv', hw', hsec_s⟩ := hremap v₀ s e₀ hvalid₀ hCe₀ hv₀
    intro hneg
    exact hneg e' hv' (transfer e' hw') (view_eq e' hw') hsec_s

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
    (C : Observation.ExecView SS LS → Prop)
    (hhas_secret : ∀ e, (toLTS adv.sys).valid_exec e →
      C (adv.obs.view e) → ∃ v, secret v e)
    (hremap : ∀ v₁ v₂ e,
      (toLTS adv.sys).valid_exec e → C (adv.obs.view e) → secret v₁ e →
      ∃ e', (toLTS adv.sys).valid_exec e' ∧
        adv.obs.view e = adv.obs.view e' ∧ secret v₂ e')
    (hexcl : ∀ v₁ v₂ e, (toLTS adv.sys).valid_exec e →
      C (adv.obs.view e) → v₁ ≠ v₂ → secret v₁ e → ¬secret v₂ e)
    (s : V) (hne : ∃ s', s' ≠ s) :
    adv.possibilistic_secret (secret s) C :=
  adv.possibilistic_secret_by_remap secret C hhas_secret hremap hexcl s hne

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

end PLTS
