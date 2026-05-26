import Leslie_LTS.Framework.Secrecy
import Leslie_LTS.Framework.Simulation

/-! # Secrecy Transfer via Belief-State Forward Simulations

    Transfer possibilistic secrecy between PLTS adversaries using
    `LTS.ForwardSim` between their belief-state PLTS systems.

    The belief-state PLTS (`Adversary.beliefPLTS`) tracks the adversary's
    probabilistic knowledge. Forward simulations between these systems
    (via `toLTS`) establish behavioral correspondence. Projection and
    lifting connect original executions to belief-state executions.
-/

namespace PLTS

/-! ## Bijective Signal Mapping -/

/-- A bijective mapping between two observation signal spaces. -/
structure SignalMap (SS_A LS_A SS_B LS_B : Type*) where
  map_ss : SS_A ≃ SS_B
  map_ls : LS_A ≃ LS_B

variable {SS_A LS_A SS_B LS_B : Type*}

/-- Apply a signal mapping pointwise to an execution view. -/
def SignalMap.mapView (φ : SignalMap SS_A LS_A SS_B LS_B)
    (v : Observation.ExecView SS_A LS_A) : Observation.ExecView SS_B LS_B where
  state_signals := φ.map_ss ∘ v.state_signals
  label_signals := φ.map_ls ∘ v.label_signals

/-- The inverse signal mapping. -/
def SignalMap.symm (φ : SignalMap SS_A LS_A SS_B LS_B) : SignalMap SS_B LS_B SS_A LS_A where
  map_ss := φ.map_ss.symm
  map_ls := φ.map_ls.symm

/-! ## Projection and Lifting for Belief-State PLTS

    **Projection**: every original execution induces a valid belief-state
    execution (by computing the Bayesian posterior at each step).

    **Lifting**: every valid belief-state execution can be realized by
    an original execution. Each state in a belief's support is backward-
    reachable; extending to infinite executions requires compactness. -/

/-- Projection: an original execution induces a valid execution of
    `toLTS (beliefPLTS adv hres)`.

    The belief at step `k` is the posterior distribution over states
    consistent with the observation history up to step `k`.

    **SORRY**: constructing the explicit belief sequence requires
    Bayesian update computations with `PMF.filter`. -/
theorem beliefPLTS_project
    {State : Type*} {Label : Type*} {SS : Type*} {LS : Type*}
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) [Inhabited Label]
    (e : LTS.Execution State Label)
    (hval : (toLTS adv.sys).valid_exec e) :
    ∃ be : LTS.Execution (Adversary.BeliefState State SS) LS,
      (toLTS (adv.beliefPLTS hres)).valid_exec be ∧
      (∀ k, (be.states k).signal = adv.obs.observe_state (e.states k)) ∧
      (∀ k, be.labels k = adv.obs.observe_label (e.states k) (e.labels k)) ∧
      (∀ k, e.states k ∈ (be.states k).belief.support) := by
  sorry

/-- Lifting: every valid belief-state execution can be realized by
    an original execution.

    **COMPACTNESS NEEDED**: each state in the belief's support at step `k`
    has a valid original execution of length `k` reaching it (by backward
    induction). Extending to an infinite execution requires König's lemma
    or dependent choice. -/
theorem beliefPLTS_lift
    {State : Type*} {Label : Type*} {SS : Type*} {LS : Type*}
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) [Inhabited Label]
    (be : LTS.Execution (Adversary.BeliefState State SS) LS)
    (hval : (toLTS (adv.beliefPLTS hres)).valid_exec be) :
    ∃ e : LTS.Execution State Label,
      (toLTS adv.sys).valid_exec e ∧
      (∀ k, adv.obs.observe_state (e.states k) = (be.states k).signal) ∧
      (∀ k, adv.obs.observe_label (e.states k) (e.labels k) = be.labels k) := by
  sorry

/-! ## View Correspondence -/

/-- If two original executions have belief-state executions whose signals
    are related via φ, then the original views are φ-related. -/
theorem view_correspondence_belief
    {State_A : Type*} {Label_A : Type*} {SS_A : Type*} {LS_A : Type*}
    {State_B : Type*} {Label_B : Type*} {SS_B : Type*} {LS_B : Type*}
    (adv_A : Adversary State_A Label_A SS_A LS_A)
    (adv_B : Adversary State_B Label_B SS_B LS_B)
    (φ : SignalMap SS_A LS_A SS_B LS_B)
    (e_A : LTS.Execution State_A Label_A)
    (e_B : LTS.Execution State_B Label_B)
    (hobs_s : ∀ k, φ.map_ss (adv_A.obs.observe_state (e_A.states k)) =
      adv_B.obs.observe_state (e_B.states k))
    (hobs_l : ∀ k, φ.map_ls (adv_A.obs.observe_label (e_A.states k) (e_A.labels k)) =
      adv_B.obs.observe_label (e_B.states k) (e_B.labels k)) :
    φ.mapView (adv_A.obs.view e_A) = adv_B.obs.view e_B := by
  simp only [SignalMap.mapView, Observation.view, Observation.ExecView.mk.injEq]
  exact ⟨funext hobs_s, funext hobs_l⟩

/-! ## Possibilistic Secrecy Transfer -/

/-- **Possibilistic secrecy transfer** via `LTS.ForwardSim` between
    belief-state PLTS systems.

    Two forward simulations between `toLTS (beliefPLTS)` systems (in both
    directions via the bijective signal map φ) transfer possibilistic
    secrecy from system A to system B.

    The proof composes: project → simulate → lift in both directions.
    Projection and lifting use `beliefPLTS_project` and `beliefPLTS_lift`. -/
theorem possibilistic_secret_transfer
    {State_A : Type*} {Label_A : Type*} {SS_A : Type*} {LS_A : Type*}
    {State_B : Type*} {Label_B : Type*} {SS_B : Type*} {LS_B : Type*}
    (adv_A : Adversary State_A Label_A SS_A LS_A)
    (adv_B : Adversary State_B Label_B SS_B LS_B)
    (hres_A : adv_A.observation_resolving)
    (hres_B : adv_B.observation_resolving)
    [Inhabited Label_A] [Inhabited Label_B]
    (φ : SignalMap SS_A LS_A SS_B LS_B)
    (P_A : LTS.Execution State_A Label_A → Prop)
    (P_B : LTS.Execution State_B Label_B → Prop)
    (C_A : Observation.ExecView SS_A LS_A → Prop)
    (C_B : Observation.ExecView SS_B LS_B → Prop)
    (h_sec_A : adv_A.possibilistic_secret P_A C_A)
    -- Signal-level labellings
    (sig_lab_A : LTS.Labelling LS_A)
    (sig_lab_B : LTS.Labelling LS_B)
    -- Forward simulations between belief-state PLTS systems
    (sim_ab : LTS.ForwardSim
      (toLTS (adv_A.beliefPLTS hres_A)) sig_lab_A
      (toLTS (adv_B.beliefPLTS hres_B)) sig_lab_B)
    (sim_ba : LTS.ForwardSim
      (toLTS (adv_B.beliefPLTS hres_B)) sig_lab_B
      (toLTS (adv_A.beliefPLTS hres_A)) sig_lab_A)
    -- Compatibility: simulations preserve signal correspondence via φ
    (hab_label : sim_ab.label_map = φ.map_ls)
    (hab_R : ∀ bs_a bs_b, sim_ab.R bs_a bs_b →
      φ.map_ss bs_a.signal = bs_b.signal)
    (hba_label : sim_ba.label_map = φ.map_ls.symm)
    (hba_R : ∀ bs_b bs_a, sim_ba.R bs_b bs_a →
      φ.map_ss bs_a.signal = bs_b.signal)
    -- Property and condition transfer
    (h_prop : ∀ e_A e_B, (toLTS adv_A.sys).valid_exec e_A →
      (toLTS adv_B.sys).valid_exec e_B →
      φ.mapView (adv_A.obs.view e_A) = adv_B.obs.view e_B →
      (P_A e_A ↔ P_B e_B))
    (h_cond : ∀ v_A, C_B (φ.mapView v_A) → C_A v_A) :
    adv_B.possibilistic_secret P_B C_B := by
  -- The chain: original → belief-state → (ForwardSim) → belief-state → original
  -- Derive execution-level correspondence:
  -- B-original → B-belief → (sim_ba) → A-belief → A-original
  -- with φ-related views
  have chain_BA : ∀ e_B, (toLTS adv_B.sys).valid_exec e_B →
      ∃ e_A, (toLTS adv_A.sys).valid_exec e_A ∧
        φ.mapView (adv_A.obs.view e_A) = adv_B.obs.view e_B := by
    sorry -- project e_B → sim_ba → lift to e_A; use hab/hba compatibility
  -- A-original → A-belief → (sim_ab) → B-belief → B-original
  have chain_AB : ∀ e_A, (toLTS adv_A.sys).valid_exec e_A →
      ∃ e_B, (toLTS adv_B.sys).valid_exec e_B ∧
        φ.mapView (adv_A.obs.view e_A) = adv_B.obs.view e_B := by
    sorry -- project e_A → sim_ab → lift to e_B; use hab compatibility
  -- Main secrecy transfer proof
  intro ρ_B v_B hC_B ⟨e_B, hval_B, hcons_B, hview_B⟩
  -- Step 1: B → A with φ-related view
  obtain ⟨e_A, hval_A, hview_rel⟩ := chain_BA e_B hval_B
  have hview_map : φ.mapView (adv_A.obs.view e_A) = v_B :=
    hview_rel.trans hview_B
  -- Step 2: Condition transfer + A's secrecy
  have hC_A : C_A (adv_A.obs.view e_A) := h_cond _ (by rwa [hview_map])
  let σ_A : Strategy SS_A LS_A := fun hist _ =>
    adv_A.obs.observe_label (e_A.states hist.length) (e_A.labels hist.length)
  have hcons_σ : adv_A.consistent σ_A e_A := fun k => by
    simp only [σ_A, List.length_ofFn]
  obtain ⟨⟨e_A_pos, hval_pos, _, hview_pos, hP_pos⟩,
          ⟨e_A_neg, hval_neg, _, hview_neg, hP_neg⟩⟩ :=
    adv_A.not_inferable_witnesses σ_A.toRandomised P_A (adv_A.obs.view e_A)
      (h_sec_A σ_A.toRandomised (adv_A.obs.view e_A) hC_A)
      ⟨e_A, hval_A, adv_A.consistent_toRandomised σ_A e_A hcons_σ, rfl⟩
  -- Step 3: A-witnesses → B via chain_AB
  obtain ⟨e_B_pos, hval_B_pos, hview_B_pos⟩ := chain_AB e_A_pos hval_pos
  obtain ⟨e_B_neg, hval_B_neg, hview_B_neg⟩ := chain_AB e_A_neg hval_neg
  -- Property transfer
  have hP_iff_pos := h_prop e_A_pos e_B_pos hval_pos hval_B_pos hview_B_pos
  have hP_iff_neg := h_prop e_A_neg e_B_neg hval_neg hval_B_neg hview_B_neg
  -- B-witnesses have view v_B → indistinguishable → ρ_B-consistent
  have hview_B_pos' : adv_B.consistent_with_view e_B_pos v_B :=
    ((hview_B_pos.symm).trans (congr_arg φ.mapView hview_pos)).trans hview_map
  have hview_B_neg' : adv_B.consistent_with_view e_B_neg v_B :=
    ((hview_B_neg.symm).trans (congr_arg φ.mapView hview_neg)).trans hview_map
  have hcons_B_pos := adv_B.randomised_consistent_of_indistinguishable ρ_B
    ⟨congr_fun (congr_arg Observation.ExecView.state_signals (hview_B.trans hview_B_pos'.symm)),
     congr_fun (congr_arg Observation.ExecView.label_signals (hview_B.trans hview_B_pos'.symm))⟩
    hcons_B
  have hcons_B_neg := adv_B.randomised_consistent_of_indistinguishable ρ_B
    ⟨congr_fun (congr_arg Observation.ExecView.state_signals (hview_B.trans hview_B_neg'.symm)),
     congr_fun (congr_arg Observation.ExecView.label_signals (hview_B.trans hview_B_neg'.symm))⟩
    hcons_B
  exact ⟨fun hpos => hP_neg (hP_iff_neg.mpr (hpos e_B_neg hval_B_neg hcons_B_neg hview_B_neg')),
         fun hneg => hneg e_B_pos hval_B_pos hcons_B_pos hview_B_pos' (hP_iff_pos.mp hP_pos)⟩

end PLTS
