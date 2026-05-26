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
  classical
  -- Key lemma: successor state is in beliefJoint support
  have joint_mem : ∀ k (μ : PMF State),
      e.states k ∈ μ.support →
      e.states (k + 1) ∈ (adv.beliefJoint hres μ
        (adv.obs.observe_label (e.states k) (e.labels k))).support := by
    intro k μ hk_mem
    unfold Adversary.beliefJoint
    rw [PMF.mem_support_bind_iff]
    refine ⟨e.states k, hk_mem, ?_⟩
    obtain ⟨μ_step, hstep_μ, hmem_succ⟩ := hval.2 k
    have hex : ∃ l ν, adv.obs.observe_label (e.states k) l =
        adv.obs.observe_label (e.states k) (e.labels k) ∧
        adv.sys.step (e.states k) l ν :=
      ⟨e.labels k, μ_step, rfl, hstep_μ⟩
    rw [dif_pos hex]
    exact (hres (e.states k) hex.choose (e.labels k)
      hex.choose_spec.choose μ_step
      hex.choose_spec.choose_spec.1
      hex.choose_spec.choose_spec.2 hstep_μ).2 ▸ hmem_succ
  -- Build beliefs recursively: belief k is a PMF with e.states k in support
  -- and all support states having signal observe_state (e.states k)
  let mkBelief : (k : ℕ) → { μ : PMF State //
      e.states k ∈ μ.support ∧
      (∀ s ∈ μ.support, adv.obs.observe_state s =
        adv.obs.observe_state (e.states k)) } :=
    @Nat.rec (fun k => { μ : PMF State //
        e.states k ∈ μ.support ∧
        (∀ s ∈ μ.support, adv.obs.observe_state s =
          adv.obs.observe_state (e.states k)) })
      ⟨PMF.pure (e.states 0),
        by simp [PMF.support_pure],
        fun s hs => by rw [PMF.support_pure, Set.mem_singleton_iff] at hs; rw [hs]⟩
      (fun k prev =>
        have h_in := joint_mem k prev.val prev.property.1
        have h_fc : ∃ a ∈
            {s' | adv.obs.observe_state s' =
              adv.obs.observe_state (e.states (k + 1))},
            a ∈ (adv.beliefJoint hres prev.val
              (adv.obs.observe_label (e.states k) (e.labels k))).support :=
          ⟨e.states (k + 1), rfl, h_in⟩
        ⟨PMF.filter (adv.beliefJoint hres prev.val
            (adv.obs.observe_label (e.states k) (e.labels k))) _ h_fc,
          (PMF.mem_support_filter_iff h_fc).mpr ⟨rfl, h_in⟩,
          fun s hs => ((PMF.mem_support_filter_iff h_fc).mp hs).1⟩)
  -- Construct the belief-state execution
  let be : LTS.Execution (Adversary.BeliefState State SS) LS :=
    { states := fun k => ⟨adv.obs.observe_state (e.states k), (mkBelief k).val⟩
      labels := fun k => adv.obs.observe_label (e.states k) (e.labels k) }
  refine ⟨be, ⟨?_, ?_⟩, fun k => rfl, fun k => rfl,
    fun k => (mkBelief k).property.1⟩
  · -- Init: all states in belief 0's support are initial with correct signal
    intro s hs
    -- mkBelief 0 reduces to PMF.pure (e.states 0)
    change s ∈ (PMF.pure (e.states 0)).support at hs
    rw [PMF.support_pure, Set.mem_singleton_iff] at hs
    subst hs
    exact ⟨hval.1, rfl⟩
  · -- Steps: each step is a valid belief-state transition
    intro k
    let bs_next : Adversary.BeliefState State SS :=
      ⟨adv.obs.observe_state (e.states (k + 1)), (mkBelief (k + 1)).val⟩
    refine ⟨PMF.pure bs_next, ?_, (PMF.mem_support_pure_iff _ _).mpr rfl⟩
    intro bs' hbs'
    rw [PMF.support_pure, Set.mem_singleton_iff] at hbs'
    subst hbs'
    exact ⟨(mkBelief (k + 1)).property.2,
      ⟨e.states (k + 1), rfl,
        joint_mem k (mkBelief k).val (mkBelief k).property.1⟩,
      rfl⟩

/-- Lifting: a sequence of belief states with backward reachability
    through the original system can be realized by an original execution.

    **COMPACTNESS NEEDED**: each state in the belief's support at step `k`
    is backward-reachable (via `Star`) from some initial state. Extending
    finite backward-reachable prefixes to an infinite execution requires
    König's lemma or dependent choice. -/
theorem beliefPLTS_lift
    {State : Type*} {Label : Type*} {SS : Type*} {LS : Type*}
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) [Inhabited Label]
    (beliefs : ℕ → Adversary.BeliefState State SS)
    (labels : ℕ → LS)
    -- Signal condition: all support states have the declared signal
    (hsig : ∀ k s, s ∈ (beliefs k).belief.support →
      adv.obs.observe_state s = (beliefs k).signal)
    -- Init condition: initial belief states are valid initial states
    (hinit : ∀ s ∈ (beliefs 0).belief.support, adv.sys.init s)
    -- Backward reachability: each successor state is reachable from
    -- some predecessor state via the original system's transitive closure
    (hback : ∀ k (s' : State),
      s' ∈ (beliefs (k + 1)).belief.support →
      ∃ s ∈ (beliefs k).belief.support,
        LTS.Star (toLTS adv.sys) s s') :
    ∃ e : LTS.Execution State Label,
      (toLTS adv.sys).valid_exec e ∧
      (∀ k, adv.obs.observe_state (e.states k) = (beliefs k).signal) ∧
      (∀ k, adv.obs.observe_label (e.states k) (e.labels k) = labels k) := by
  -- SORRY: infinite path extraction from the backward-reachability tree
  -- + label selection at each step to match the label signal sequence.
  sorry

/-- A single belief-LTS step gives backward `Star` reachability at the
    original system level: each state in the successor belief is reachable
    (via `Star (toLTS adv.sys)`) from some state in the predecessor belief. -/
theorem beliefPLTS_step_backward
    {State : Type*} {Label : Type*} {SS : Type*} {LS : Type*}
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) [Inhabited Label]
    (bs bs' : Adversary.BeliefState State SS)
    (l : LS) (hstep : (toLTS (adv.beliefPLTS hres)).step bs l bs') :
    ∀ s' ∈ bs'.belief.support,
      ∃ s ∈ bs.belief.support,
        LTS.Star (toLTS adv.sys) s s' := by
  intro s' hs'
  obtain ⟨ν_bs, hstep_bs, hmem⟩ := hstep
  have hbs := hstep_bs bs' hmem
  obtain ⟨h_fc, h_eq⟩ := hbs.2
  have hs'_joint : s' ∈
      (adv.beliefJoint hres bs.belief l).support := by
    rw [h_eq, PMF.support_filter] at hs'; exact hs'.2
  rw [Adversary.beliefJoint, PMF.mem_support_bind_iff] at hs'_joint
  obtain ⟨s, hs_mem, hs'_fs⟩ := hs'_joint
  refine ⟨s, hs_mem, ?_⟩
  by_cases h : ∃ l' ν, adv.obs.observe_label s l' = l ∧ adv.sys.step s l' ν
  · rw [dif_pos h] at hs'_fs
    exact .step ⟨h.choose_spec.choose, h.choose_spec.choose_spec.2, hs'_fs⟩ .refl
  · rw [dif_neg h] at hs'_fs
    rw [PMF.support_pure, Set.mem_singleton_iff] at hs'_fs
    subst hs'_fs; exact .refl

/-- Composing backward `Star` reachability through an `InternalStar` path
    of belief-LTS steps. -/
theorem beliefPLTS_internalStar_backward
    {State : Type*} {Label : Type*} {SS : Type*} {LS : Type*}
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) [Inhabited Label]
    {lab : LTS.Labelling LS}
    {bs bs' : Adversary.BeliefState State SS}
    (hstar : LTS.InternalStar (toLTS (adv.beliefPLTS hres)) lab bs bs') :
    ∀ s' ∈ bs'.belief.support,
      ∃ s ∈ bs.belief.support,
        LTS.Star (toLTS adv.sys) s s' := by
  induction hstar with
  | refl => intro s' hs'; exact ⟨s', hs', .refl⟩
  | step _hint hstep _rest ih =>
    intro s' hs'
    obtain ⟨s_mid, hs_mid, hstar_mid⟩ := ih s' hs'
    obtain ⟨s, hs, hstar_s⟩ :=
      beliefPLTS_step_backward adv hres _ _ _ hstep s_mid hs_mid
    exact ⟨s, hs, hstar_s.trans hstar_mid⟩

/-- A single belief-LTS step preserves the signal condition: the successor
    belief state's support states all have the declared signal. -/
theorem beliefPLTS_step_sig
    {State : Type*} {Label : Type*} {SS : Type*} {LS : Type*}
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) [Inhabited Label]
    {bs bs' : Adversary.BeliefState State SS} {l : LS}
    (hstep : (toLTS (adv.beliefPLTS hres)).step bs l bs') :
    ∀ s ∈ bs'.belief.support, adv.obs.observe_state s = bs'.signal := by
  obtain ⟨ν, hstep_ν, hmem⟩ := hstep
  exact (hstep_ν bs' hmem).1

/-- An `InternalStar` of belief-LTS steps propagates the signal condition
    from the start state. -/
theorem beliefPLTS_internalStar_sig
    {State : Type*} {Label : Type*} {SS : Type*} {LS : Type*}
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) [Inhabited Label]
    {lab : LTS.Labelling LS}
    {bs bs' : Adversary.BeliefState State SS}
    (hbs : ∀ s ∈ bs.belief.support, adv.obs.observe_state s = bs.signal)
    (hstar : LTS.InternalStar (toLTS (adv.beliefPLTS hres)) lab bs bs') :
    ∀ s ∈ bs'.belief.support, adv.obs.observe_state s = bs'.signal := by
  induction hstar with
  | refl => exact hbs
  | step _hint hstep _rest ih => exact ih (beliefPLTS_step_sig adv hres hstep)

/-- Reachable belief-LTS states satisfy the signal condition. -/
theorem beliefPLTS_reachable_sig
    {State : Type*} {Label : Type*} {SS : Type*} {LS : Type*}
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) [Inhabited Label]
    {bs : Adversary.BeliefState State SS}
    (hreach : LTS.Reachable (toLTS (adv.beliefPLTS hres)) bs) :
    ∀ s ∈ bs.belief.support, adv.obs.observe_state s = bs.signal := by
  induction hreach with
  | init hinit => intro s hs; exact (hinit s hs).2
  | step _ hstep _ => exact beliefPLTS_step_sig adv hres hstep

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
    intro e_B hval_B
    -- Step 1: Project e_B to belief-state execution of B
    obtain ⟨be_B, hval_beB, hsig_B, hlab_B, _⟩ :=
      beliefPLTS_project adv_B hres_B e_B hval_B
    -- Step 2: Build ForwardSim witnesses carrying R, reachability,
    -- and backward Star (stored as a pair: current + previous belief)
    have hreach_B := LTS.System.valid_exec_reachable hval_beB
    -- The witness at each step k carries: (current_bs, prev_bs) where
    -- prev_bs is the witness at step k-1 (or current_bs for k=0).
    -- Backward Star from prev_bs to current_bs is bundled.
    let buildWit : (k : ℕ) →
        { p : Adversary.BeliefState State_A SS_A ×
              Adversary.BeliefState State_A SS_A //
          sim_ba.R (be_B.states k) p.1 ∧
          LTS.Reachable (toLTS (adv_A.beliefPLTS hres_A)) p.1 ∧
          (∀ s' ∈ p.1.belief.support,
            ∃ s ∈ p.2.belief.support,
              LTS.Star (toLTS adv_A.sys) s s') } :=
      @Nat.rec
        (fun k => { p : Adversary.BeliefState State_A SS_A ×
              Adversary.BeliefState State_A SS_A //
          sim_ba.R (be_B.states k) p.1 ∧
          LTS.Reachable (toLTS (adv_A.beliefPLTS hres_A)) p.1 ∧
          (∀ s' ∈ p.1.belief.support,
            ∃ s ∈ p.2.belief.support,
              LTS.Star (toLTS adv_A.sys) s s') })
        -- Base: prev = self (backward Star via refl)
        (let bs₀ := (sim_ba.init_sim (be_B.states 0) hval_beB.1).1
         ⟨(bs₀, bs₀),
          (sim_ba.init_sim (be_B.states 0) hval_beB.1).2.2,
          .init (sim_ba.init_sim (be_B.states 0) hval_beB.1).2.1,
          fun s' hs' => ⟨s', hs', .refl⟩⟩)
        -- Step: compose backward Star over ForwardSim path
        (fun k prev =>
          if hint : sig_lab_B.is_internal (be_B.labels k) = true then
            let w := sim_ba.step_internal (be_B.states k) (be_B.labels k)
              (be_B.states (k + 1)) prev.1.1 (hreach_B k) prev.2.1
              hint (hval_beB.2 k)
            ⟨(w.1, prev.1.1), w.2.2, w.2.1.toStar.reachable prev.2.2.1,
             fun s' hs' =>
               let ⟨s, hs, hstar⟩ :=
                 beliefPLTS_internalStar_backward adv_A hres_A w.2.1 s' hs'
               ⟨s, hs, hstar⟩⟩
          else
            let hext : sig_lab_B.is_external (be_B.labels k) = true :=
              show _ = true by simp [LTS.Labelling.is_external, hint]
            let w := sim_ba.step_external (be_B.states k) (be_B.labels k)
              (be_B.states (k + 1)) prev.1.1 (hreach_B k) prev.2.1
              hext (hval_beB.2 k)
            ⟨(w.2.2.1, prev.1.1), w.2.2.2.2.2.2,
             w.2.2.2.2.2.1.toStar.reachable
               (.step (w.2.2.2.1.toStar.reachable prev.2.2.1) w.2.2.2.2.1),
             fun s' hs' => by
               obtain ⟨s₃, hs₃, hstar₃⟩ :=
                 beliefPLTS_internalStar_backward adv_A hres_A
                   w.2.2.2.2.2.1 s' hs'
               obtain ⟨s₂, hs₂, hstar₂⟩ :=
                 beliefPLTS_step_backward adv_A hres_A _ _ _
                   w.2.2.2.2.1 s₃ hs₃
               obtain ⟨s₁, hs₁, hstar₁⟩ :=
                 beliefPLTS_internalStar_backward adv_A hres_A
                   w.2.2.2.1 s₂ hs₂
               exact ⟨s₁, hs₁, hstar₁.trans (hstar₂.trans hstar₃)⟩⟩)
    -- Step 3: Lift via beliefPLTS_lift with witness beliefs
    let wit_beliefs : ℕ → Adversary.BeliefState State_A SS_A :=
      fun k => (buildWit k).1.1
    let wit_labels : ℕ → LS_A :=
      fun k => sim_ba.label_map (be_B.labels k)
    -- Signal condition from reachability (carried in buildWit)
    have wit_sig : ∀ k s, s ∈ (wit_beliefs k).belief.support →
        adv_A.obs.observe_state s = (wit_beliefs k).signal :=
      fun k => beliefPLTS_reachable_sig adv_A hres_A (buildWit k).2.2.1
    -- Init condition
    have wit_init : ∀ s ∈ (wit_beliefs 0).belief.support,
        adv_A.sys.init s := by
      intro s hs
      exact (((sim_ba.init_sim (be_B.states 0) hval_beB.1).2.1) s hs).1
    -- Backward Star: the pair's .2 is always prev.1.1 in both dite branches.
    -- Use apply_ite to push Prod.snd through the dite.
    have wit_back : ∀ k (s' : State_A),
        s' ∈ (wit_beliefs (k + 1)).belief.support →
        ∃ s ∈ (wit_beliefs k).belief.support,
          LTS.Star (toLTS adv_A.sys) s s' := by
      intro k s' hs'
      have h := (buildWit (k + 1)).2.2.2 s' hs'
      -- Push Prod.snd through the dite in buildWit to show
      -- (buildWit (k+1)).val.2 = (buildWit k).val.1
      convert h using 2
      simp only [wit_beliefs, buildWit, apply_dite Prod.snd, apply_dite Subtype.val]
      split <;> rfl
    obtain ⟨e_A, hval_A, hsig_A, hlab_A⟩ :=
      beliefPLTS_lift adv_A hres_A wit_beliefs wit_labels
        wit_sig wit_init wit_back
    -- Step 4: Assemble view correspondence
    have hsig_AB : ∀ k, φ.map_ss (wit_beliefs k).signal =
        (be_B.states k).signal :=
      fun k => hba_R (be_B.states k) (buildWit k).1.1 (buildWit k).2.1
    have hlab_AB : ∀ k, φ.map_ls (wit_labels k) = be_B.labels k := by
      intro k
      show φ.map_ls (sim_ba.label_map (be_B.labels k)) = be_B.labels k
      rw [show sim_ba.label_map (be_B.labels k) = φ.map_ls.symm (be_B.labels k) from
        congr_fun hba_label (be_B.labels k)]
      exact Equiv.apply_symm_apply φ.map_ls (be_B.labels k)
    exact ⟨e_A, hval_A, view_correspondence_belief adv_A adv_B φ e_A e_B
      (fun k => by rw [hsig_A k, hsig_AB k, hsig_B k])
      (fun k => by rw [hlab_A k, hlab_AB k, hlab_B k])⟩
  -- A-original → A-belief → (sim_ab) → B-belief → B-original
  have chain_AB : ∀ e_A, (toLTS adv_A.sys).valid_exec e_A →
      ∃ e_B, (toLTS adv_B.sys).valid_exec e_B ∧
        φ.mapView (adv_A.obs.view e_A) = adv_B.obs.view e_B := by
    intro e_A hval_A
    -- Step 1: Project e_A to belief-state execution of A
    obtain ⟨be_A, hval_beA, hsig_A, hlab_A, _⟩ :=
      beliefPLTS_project adv_A hres_A e_A hval_A
    -- Step 2: Build ForwardSim witnesses for belief-LTS-B
    have hreach_A := LTS.System.valid_exec_reachable hval_beA
    let buildWit : (k : ℕ) →
        { p : Adversary.BeliefState State_B SS_B ×
              Adversary.BeliefState State_B SS_B //
          sim_ab.R (be_A.states k) p.1 ∧
          LTS.Reachable (toLTS (adv_B.beliefPLTS hres_B)) p.1 ∧
          (∀ s' ∈ p.1.belief.support,
            ∃ s ∈ p.2.belief.support,
              LTS.Star (toLTS adv_B.sys) s s') } :=
      @Nat.rec
        (fun k => { p : Adversary.BeliefState State_B SS_B ×
              Adversary.BeliefState State_B SS_B //
          sim_ab.R (be_A.states k) p.1 ∧
          LTS.Reachable (toLTS (adv_B.beliefPLTS hres_B)) p.1 ∧
          (∀ s' ∈ p.1.belief.support,
            ∃ s ∈ p.2.belief.support,
              LTS.Star (toLTS adv_B.sys) s s') })
        (let bs₀ := (sim_ab.init_sim (be_A.states 0) hval_beA.1).1
         ⟨(bs₀, bs₀),
          (sim_ab.init_sim (be_A.states 0) hval_beA.1).2.2,
          .init (sim_ab.init_sim (be_A.states 0) hval_beA.1).2.1,
          fun s' hs' => ⟨s', hs', .refl⟩⟩)
        (fun k prev =>
          if hint : sig_lab_A.is_internal (be_A.labels k) = true then
            let w := sim_ab.step_internal (be_A.states k) (be_A.labels k)
              (be_A.states (k + 1)) prev.1.1 (hreach_A k) prev.2.1
              hint (hval_beA.2 k)
            ⟨(w.1, prev.1.1), w.2.2, w.2.1.toStar.reachable prev.2.2.1,
             fun s' hs' =>
               beliefPLTS_internalStar_backward adv_B hres_B w.2.1 s' hs'⟩
          else
            let hext : sig_lab_A.is_external (be_A.labels k) = true :=
              show _ = true by simp [LTS.Labelling.is_external, hint]
            let w := sim_ab.step_external (be_A.states k) (be_A.labels k)
              (be_A.states (k + 1)) prev.1.1 (hreach_A k) prev.2.1
              hext (hval_beA.2 k)
            ⟨(w.2.2.1, prev.1.1), w.2.2.2.2.2.2,
             w.2.2.2.2.2.1.toStar.reachable
               (.step (w.2.2.2.1.toStar.reachable prev.2.2.1) w.2.2.2.2.1),
             fun s' hs' => by
               obtain ⟨s₃, hs₃, hstar₃⟩ :=
                 beliefPLTS_internalStar_backward adv_B hres_B
                   w.2.2.2.2.2.1 s' hs'
               obtain ⟨s₂, hs₂, hstar₂⟩ :=
                 beliefPLTS_step_backward adv_B hres_B _ _ _
                   w.2.2.2.2.1 s₃ hs₃
               obtain ⟨s₁, hs₁, hstar₁⟩ :=
                 beliefPLTS_internalStar_backward adv_B hres_B
                   w.2.2.2.1 s₂ hs₂
               exact ⟨s₁, hs₁, hstar₁.trans (hstar₂.trans hstar₃)⟩⟩)
    -- Step 3: Lift via beliefPLTS_lift with witness beliefs
    let wit_beliefs : ℕ → Adversary.BeliefState State_B SS_B :=
      fun k => (buildWit k).1.1
    let wit_labels : ℕ → LS_B :=
      fun k => sim_ab.label_map (be_A.labels k)
    have wit_sig : ∀ k s, s ∈ (wit_beliefs k).belief.support →
        adv_B.obs.observe_state s = (wit_beliefs k).signal :=
      fun k => beliefPLTS_reachable_sig adv_B hres_B (buildWit k).2.2.1
    have wit_init : ∀ s ∈ (wit_beliefs 0).belief.support,
        adv_B.sys.init s := by
      intro s hs
      exact (((sim_ab.init_sim (be_A.states 0) hval_beA.1).2.1) s hs).1
    have wit_back : ∀ k (s' : State_B),
        s' ∈ (wit_beliefs (k + 1)).belief.support →
        ∃ s ∈ (wit_beliefs k).belief.support,
          LTS.Star (toLTS adv_B.sys) s s' := by
      intro k s' hs'
      have h := (buildWit (k + 1)).2.2.2 s' hs'
      convert h using 2
      simp only [wit_beliefs, buildWit, apply_dite Prod.snd, apply_dite Subtype.val]
      split <;> rfl
    obtain ⟨e_B, hval_B, hsig_B, hlab_B⟩ :=
      beliefPLTS_lift adv_B hres_B wit_beliefs wit_labels
        wit_sig wit_init wit_back
    -- Step 4: Assemble view correspondence
    have hsig_AB : ∀ k, (wit_beliefs k).signal =
        φ.map_ss (be_A.states k).signal :=
      fun k => (hab_R (be_A.states k) (buildWit k).1.1 (buildWit k).2.1).symm
    have hlab_AB : ∀ k, wit_labels k = φ.map_ls (be_A.labels k) := by
      intro k
      show sim_ab.label_map (be_A.labels k) = φ.map_ls (be_A.labels k)
      exact congr_fun hab_label (be_A.labels k)
    exact ⟨e_B, hval_B, view_correspondence_belief adv_A adv_B φ e_A e_B
      (fun k => by rw [← hsig_A k, ← hsig_AB k, hsig_B k])
      (fun k => by rw [← hlab_A k, ← hlab_AB k, hlab_B k])⟩
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
