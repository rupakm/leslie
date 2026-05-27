import Leslie_LTS.Framework.ProbSecrecy
import Leslie_LTS.Framework.ProbSimulation
import Leslie_LTS.Framework.SecrecyTransfer

/-! # Probabilistic Secrecy Transfer via Probabilistic Forward Simulations

    Transfer `prob_possibilistic_secret` between PLTS adversaries using
    `ProbForwardSim` between their belief-state PLTS systems.

    This is the probabilistic analogue of `possibilistic_secret_transfer`
    in `SecrecyTransfer.lean`. Where the possibilistic version uses
    `LTS.ForwardSim` between `toLTS (beliefPLTS)` and builds individual
    execution correspondences, this version uses `ProbForwardSim` between
    `beliefPLTS` systems and establishes measure-level correspondences
    via **simulation absolute continuity**.

    ## Architecture

    The file has four layers, each building on the previous:

    1. **Distributional backward reachability** (§1): helper lemmas showing
       that `InternalWeakStar` and `WeakStep` on PLTS distributions give
       `LTS.Star` backward reachability on `toLTS`.

    2. **Possibilistic chains** (§2): `prob_chain_BA` and `prob_chain_AB`
       build execution-level correspondences between the two systems using
       the **flattening technique** — second-order belief distributions
       from `ProbForwardSim` are flattened to single belief states via
       `flattenBeliefs`, then lifted to original executions via
       `beliefPLTS_lift`.

    3. **Simulation absolute continuity** (§3): the measure-theoretic core.
       A `ProbForwardSim` induces a coupling between execution measures
       (`exec_measure_coupling`, the single sorry) from which absolute
       continuity follows (`coupling_absolute_continuity`, fully proved):
       zero-measure view-conditional sets in the abstract system are
       zero-measure in the concrete system.

    4. **Main theorem** (§4): `prob_possibilistic_secret_transfer` applies
       `simulation_absolute_continuity` twice — with `sim_ba` for view
       realizability transfer (contrapositive), and with `sim_ab` for
       property transfer — to derive B's probabilistic secrecy from A's.

    ## Sorry status

    One sorry remains: `exec_measure_coupling`, which constructs a joint
    Ionescu-Tulcea measure from the `ProbForwardSim` step-level couplings.
    This requires new measure-theoretic infrastructure for composing
    coupled transition kernels into a joint trajectory measure.
-/

namespace PLTS

/-! ## §1: Distributional Backward Reachability

    Every state in the successor distribution's support has a predecessor
    in the initial distribution's support, connected by `LTS.Star` on
    `toLTS`. These are the distributional analogues of the point-to-point
    backward reachability lemmas in `SecrecyTransfer.lean`. -/

/-- Backward reachability through an `InternalHyperStep`: every state in
    `μ'.support` has a predecessor in `μ.support` connected by at most
    one `toLTS` step. -/
theorem InternalHyperStep_support_backward
    {State : Type*} {Label : Type*}
    {sys : System State Label} {lab : LTS.Labelling Label}
    {μ μ' : PMF State}
    (h : InternalHyperStep sys lab μ μ') :
    ∀ s' ∈ μ'.support, ∃ s ∈ μ.support,
      LTS.Star (toLTS sys) s s' := by
  intro s' hs'
  obtain ⟨f, hf_choice, _, hμ'⟩ := h
  rw [hμ', PMF.mem_support_bind_iff] at hs'
  obtain ⟨q, hq_mem, hs'_fq⟩ := hs'
  refine ⟨q, hq_mem, ?_⟩
  rcases hf_choice q hq_mem with ⟨l, _hint, hstep⟩ | hpure
  · exact .step ⟨f q, hstep, hs'_fq⟩ .refl
  · rw [hpure, PMF.support_pure, Set.mem_singleton_iff] at hs'_fq
    exact hs'_fq ▸ .refl

/-- Backward reachability through `InternalWeakStar`: every state in
    `μ'.support` has a predecessor in `μ.support` connected by
    `LTS.Star (toLTS sys)`. -/
theorem InternalWeakStar_support_backward
    {State : Type*} {Label : Type*}
    {sys : System State Label} {lab : LTS.Labelling Label}
    {μ μ' : PMF State}
    (h : InternalWeakStar sys lab μ μ') :
    ∀ s' ∈ μ'.support, ∃ s ∈ μ.support,
      LTS.Star (toLTS sys) s s' := by
  induction h with
  | refl => intro s' hs'; exact ⟨s', hs', .refl⟩
  | step hstep _rest ih =>
    intro s' hs'
    obtain ⟨s_mid, hs_mid, hstar_mid⟩ := ih s' hs'
    obtain ⟨s, hs, hstar_s⟩ :=
      InternalHyperStep_support_backward hstep s_mid hs_mid
    exact ⟨s, hs, hstar_s.trans hstar_mid⟩

/-- Backward reachability through a `HyperStep`: every state in
    `μ'.support` has a predecessor in `μ.support` connected by
    a single `toLTS` step. -/
theorem HyperStep_support_backward
    {State : Type*} {Label : Type*}
    {sys : System State Label}
    {l : Label} {μ μ' : PMF State}
    (h : HyperStep sys l μ μ') :
    ∀ s' ∈ μ'.support, ∃ s ∈ μ.support,
      LTS.Star (toLTS sys) s s' := by
  intro s' hs'
  obtain ⟨f, hf, hμ'⟩ := h
  rw [hμ', PMF.mem_support_bind_iff] at hs'
  obtain ⟨q, hq_mem, hs'_fq⟩ := hs'
  exact ⟨q, hq_mem, .step ⟨f q, hf q hq_mem, hs'_fq⟩ .refl⟩

/-- Backward reachability through a `WeakStep`: every state in
    `μ'.support` has a predecessor in `μ.support` connected by
    `LTS.Star (toLTS sys)`. Composes through the three phases:
    internal → external → internal. -/
theorem WeakStep_support_backward
    {State : Type*} {Label : Type*}
    {sys : System State Label} {lab : LTS.Labelling Label}
    {l : Label} {μ μ' : PMF State}
    (h : WeakStep sys lab l μ μ') :
    ∀ s' ∈ μ'.support, ∃ s ∈ μ.support,
      LTS.Star (toLTS sys) s s' := by
  obtain ⟨μ₁, μ₂, hpre, hext, hpost⟩ := h
  intro s' hs'
  obtain ⟨s₂, hs₂, hstar₃⟩ :=
    InternalWeakStar_support_backward hpost s' hs'
  obtain ⟨s₁, hs₁, hstar₂⟩ :=
    HyperStep_support_backward hext s₂ hs₂
  obtain ⟨s, hs, hstar₁⟩ :=
    InternalWeakStar_support_backward hpre s₁ hs₁
  exact ⟨s, hs, hstar₁.trans (hstar₂.trans hstar₃)⟩

/-! Generalise `beliefPLTS_internalStar_backward` from `InternalStar`
    to `Star`: a `LTS.Star` path through the belief PLTS gives backward
    reachability in the original system. -/

/-- A `LTS.Star` of belief-PLTS steps gives backward `LTS.Star`
    reachability at the original system level. Generalises
    `beliefPLTS_internalStar_backward` by dropping the internal-label
    restriction. -/
theorem beliefPLTS_star_backward
    {State : Type*} {Label : Type*} {SS : Type*} {LS : Type*}
    (adv : Adversary State Label SS LS)
    (hres : adv.observation_resolving) [Inhabited Label]
    {bs bs' : Adversary.BeliefState State SS}
    (hstar : LTS.Star (toLTS (adv.beliefPLTS hres)) bs bs') :
    ∀ s' ∈ bs'.belief.support,
      ∃ s ∈ bs.belief.support,
        LTS.Star (toLTS adv.sys) s s' := by
  induction hstar with
  | refl => intro s' hs'; exact ⟨s', hs', .refl⟩
  | step hstep _rest ih =>
    intro s' hs'
    obtain ⟨s_mid, hs_mid, hstar_mid⟩ := ih s' hs'
    obtain ⟨s, hs, hstar_s⟩ :=
      beliefPLTS_step_backward adv hres _ _ _ hstep s_mid hs_mid
    exact ⟨s, hs, hstar_s.trans hstar_mid⟩

/-! ## §2: Possibilistic Chains via Flattening

    The `ProbForwardSim` gives distributions `ν : PMF (BeliefState State SS)`
    — a second-order distribution (distribution over distributions). To use
    `beliefPLTS_lift`, we flatten each `ν` to a single `BeliefState` by
    mixing all the component beliefs via `bind`. -/

/-- Flatten a second-order distribution `ν : PMF (BeliefState State SS)`
    into a single belief state by mixing component beliefs via `bind`.
    The signal `sig` must be the common signal of all `bs ∈ ν.support`
    (ensured by the `ProbForwardSim` signal compatibility conditions). -/
noncomputable def flattenBeliefs {State : Type*} {SS : Type*}
    (ν : PMF (Adversary.BeliefState State SS)) (sig : SS) :
    Adversary.BeliefState State SS where
  signal := sig
  belief := ν.bind (fun bs => bs.belief)

/-- A state in the flattened belief's support comes from some component
    belief state in the distribution's support. -/
theorem flattenBeliefs_mem_support {State : Type*} {SS : Type*}
    {ν : PMF (Adversary.BeliefState State SS)} {sig : SS} {s : State}
    (hs : s ∈ (flattenBeliefs ν sig).belief.support) :
    ∃ bs ∈ ν.support, s ∈ bs.belief.support := by
  simp only [flattenBeliefs, PMF.mem_support_bind_iff] at hs
  exact hs

/-- If `s ∈ bs.belief.support` and `bs ∈ ν.support`, then `s` is in the
    flattened belief's support. -/
theorem flattenBeliefs_mem_support_of {State : Type*} {SS : Type*}
    {ν : PMF (Adversary.BeliefState State SS)} {sig : SS} {s : State}
    {bs : Adversary.BeliefState State SS}
    (hbs : bs ∈ ν.support) (hs : s ∈ bs.belief.support) :
    s ∈ (flattenBeliefs ν sig).belief.support := by
  simp only [flattenBeliefs, PMF.mem_support_bind_iff]
  exact ⟨bs, hbs, hs⟩

/-! The possibilistic consequence of `ProbForwardSim`: for every valid
    concrete execution, there exists a valid abstract execution with
    φ-related views. The proof builds witness distributions by induction,
    flattens them to individual belief states, and lifts via
    `beliefPLTS_lift`. -/

/-- Execution-level chain BA: for every valid B-execution, there exists
    a valid A-execution with φ-related views.

    Uses the flattening technique: build witness distributions by
    induction from the `ProbForwardSim` step conditions, flatten each
    to a single belief state, and lift via `beliefPLTS_lift`. -/
theorem prob_chain_BA
    {State_A : Type*} {Label_A : Type*} {SS_A : Type*} {LS_A : Type*}
    {State_B : Type*} {Label_B : Type*} {SS_B : Type*} {LS_B : Type*}
    (adv_A : Adversary State_A Label_A SS_A LS_A)
    (adv_B : Adversary State_B Label_B SS_B LS_B)
    (hres_A : adv_A.observation_resolving)
    (hres_B : adv_B.observation_resolving)
    [Inhabited Label_A] [Inhabited Label_B]
    (φ : SignalMap SS_A LS_A SS_B LS_B)
    (sig_lab_A : LTS.Labelling LS_A)
    (sig_lab_B : LTS.Labelling LS_B)
    (sim_ba : ProbForwardSim (adv_B.beliefPLTS hres_B) sig_lab_B
                              (adv_A.beliefPLTS hres_A) sig_lab_A)
    (hba_label : sim_ba.label_map = φ.map_ls.symm)
    (hba_R : ∀ bs_b (ν : PMF (Adversary.BeliefState State_A SS_A)),
      sim_ba.R bs_b ν →
      ∀ bs_a ∈ ν.support, φ.map_ss bs_a.signal = bs_b.signal)
    (e_B : LTS.Execution State_B Label_B)
    (hval_B : (toLTS adv_B.sys).valid_exec e_B) :
    ∃ e_A : LTS.Execution State_A Label_A,
      (toLTS adv_A.sys).valid_exec e_A ∧
      φ.mapView (adv_A.obs.view e_A) = adv_B.obs.view e_B := by
  -- Step 1: Project e_B to belief-state execution of B
  obtain ⟨be_B, hval_beB, hsig_B, hlab_B, _⟩ :=
    beliefPLTS_project adv_B hres_B e_B hval_B
  have hreach_B := LTS.System.valid_exec_reachable hval_beB
  -- Step 2: Build witness distributions by Nat.rec
  -- Pair (ν_k, ν_{k-1}) tracking R, reachability, backward reachability
  -- Helper: weak transition backward + belief-PLTS backward → original Star
  have backward_chain :
      ∀ (ν_prev ν' : PMF (Adversary.BeliefState State_A SS_A)),
      (∀ bs ∈ ν'.support, ∃ bs_prev ∈ ν_prev.support,
        LTS.Star (toLTS (adv_A.beliefPLTS hres_A)) bs_prev bs) →
      ∀ (ν_next : PMF (Adversary.BeliefState State_A SS_A)),
      (∀ bs ∈ ν_next.support, bs ∈ ν'.support) →
      ∀ s' ∈ (ν_next.bind (·.belief)).support,
        ∃ s ∈ (ν_prev.bind (·.belief)).support,
          LTS.Star (toLTS adv_A.sys) s s' := by
    intro ν_prev ν' hback ν_next hsub s' hs'
    obtain ⟨bs', hbs', hs'_bs'⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs'
    obtain ⟨bs, hbs, hstar_belief⟩ := hback bs' (hsub bs' hbs')
    obtain ⟨s, hs, hstar_sys⟩ :=
      beliefPLTS_star_backward adv_A hres_A hstar_belief s' hs'_bs'
    exact ⟨s, (PMF.mem_support_bind_iff _ _ _).mpr ⟨bs, hbs, hs⟩, hstar_sys⟩
  -- Build witness sequence
  let buildWit : (k : ℕ) →
      { p : PMF (Adversary.BeliefState State_A SS_A) ×
            PMF (Adversary.BeliefState State_A SS_A) //
        sim_ba.R (be_B.states k) p.1 ∧
        (∀ bs_a ∈ p.1.support,
          LTS.Reachable (toLTS (adv_A.beliefPLTS hres_A)) bs_a) ∧
        (∀ s' ∈ (p.1.bind (·.belief)).support,
          ∃ s ∈ (p.2.bind (·.belief)).support,
            LTS.Star (toLTS adv_A.sys) s s') } :=
    @Nat.rec
      (fun k => { p : PMF (Adversary.BeliefState State_A SS_A) ×
            PMF (Adversary.BeliefState State_A SS_A) //
        sim_ba.R (be_B.states k) p.1 ∧
        (∀ bs_a ∈ p.1.support,
          LTS.Reachable (toLTS (adv_A.beliefPLTS hres_A)) bs_a) ∧
        (∀ s' ∈ (p.1.bind (·.belief)).support,
          ∃ s ∈ (p.2.bind (·.belief)).support,
            LTS.Star (toLTS adv_A.sys) s s') })
      -- Base: k = 0, prev = self
      (let w := sim_ba.init_sim (be_B.states 0) hval_beB.1
       ⟨(w.1, w.1),
        w.2.1,
        fun bs hbs => .init (w.2.2 bs hbs),
        fun s' hs' => ⟨s', hs', .refl⟩⟩)
      -- Step: k → k+1
      (fun k prev =>
        -- Extract PLTS step from valid_exec
        let μ_B := (hval_beB.2 k).choose
        let hstep_B := (hval_beB.2 k).choose_spec.1
        let hmem_B := (hval_beB.2 k).choose_spec.2
        -- DistLiftR component support ⊆ mixture support
        have comp_sub : ∀ {ν' : PMF (Adversary.BeliefState State_A SS_A)}
            (hlift : DistLiftR sim_ba.R μ_B ν'),
            ∀ bs ∈ (hlift.witness hmem_B).1.support, bs ∈ ν'.support :=
          fun hlift bs hbs => by
            rw [hlift.2.2, PMF.mem_support_bind_iff]
            exact ⟨be_B.states (k + 1), hmem_B, hbs⟩
        if hint : sig_lab_B.is_internal (be_B.labels k) = true then
          let w := sim_ba.step_internal (be_B.states k) (be_B.labels k)
            μ_B prev.1.1 (hreach_B k) prev.2.1 hint hstep_B
          let wit := w.2.2.witness hmem_B
          ⟨(wit.1, prev.1.1), wit.2,
           fun bs_a hbs_a => by
             obtain ⟨bs_prev, hbs_prev, hstar⟩ :=
               InternalWeakStar_support_backward w.2.1 bs_a
                 (comp_sub w.2.2 bs_a hbs_a)
             exact hstar.reachable (prev.2.2.1 bs_prev hbs_prev),
           backward_chain prev.1.1 w.1
             (InternalWeakStar_support_backward w.2.1)
             wit.1 (comp_sub w.2.2)⟩
        else
          let hext : sig_lab_B.is_external (be_B.labels k) = true :=
            show _ = true by simp [LTS.Labelling.is_external, hint]
          let w := sim_ba.step_external (be_B.states k) (be_B.labels k)
            μ_B prev.1.1 (hreach_B k) prev.2.1 hext hstep_B
          let wit := w.2.2.witness hmem_B
          ⟨(wit.1, prev.1.1), wit.2,
           fun bs_a hbs_a => by
             obtain ⟨bs_prev, hbs_prev, hstar⟩ :=
               WeakStep_support_backward w.2.1 bs_a
                 (comp_sub w.2.2 bs_a hbs_a)
             exact hstar.reachable (prev.2.2.1 bs_prev hbs_prev),
           backward_chain prev.1.1 w.1
             (WeakStep_support_backward w.2.1)
             wit.1 (comp_sub w.2.2)⟩)
  -- Step 3: Define flattened beliefs and labels
  let wit_beliefs : ℕ → Adversary.BeliefState State_A SS_A :=
    fun k => flattenBeliefs (buildWit k).1.1
      (φ.map_ss.symm ((be_B.states k).signal))
  let wit_labels : ℕ → LS_A :=
    fun k => sim_ba.label_map (be_B.labels k)
  -- Step 4: Verify beliefPLTS_lift conditions
  -- Signal condition
  have wit_sig : ∀ k s, s ∈ (wit_beliefs k).belief.support →
      adv_A.obs.observe_state s = (wit_beliefs k).signal := by
    intro k s hs
    obtain ⟨bs_a, hbs_a, hs_bs⟩ := flattenBeliefs_mem_support hs
    have hreach_a := (buildWit k).2.2.1 bs_a hbs_a
    have hsig_a := beliefPLTS_reachable_sig adv_A hres_A hreach_a s hs_bs
    have hφ := hba_R (be_B.states k) (buildWit k).1.1 (buildWit k).2.1 bs_a hbs_a
    simp only [wit_beliefs, flattenBeliefs]
    rw [hsig_a, ← hφ, Equiv.symm_apply_apply]
  -- Init condition
  have wit_init : ∀ s ∈ (wit_beliefs 0).belief.support,
      adv_A.sys.init s := by
    intro s hs
    obtain ⟨bs_a, hbs_a, hs_bs⟩ := flattenBeliefs_mem_support hs
    exact ((sim_ba.init_sim (be_B.states 0) hval_beB.1).2.2 bs_a hbs_a s hs_bs).1
  -- Backward reachability
  have wit_back : ∀ k (s' : State_A),
      s' ∈ (wit_beliefs (k + 1)).belief.support →
      ∃ s ∈ (wit_beliefs k).belief.support,
        LTS.Star (toLTS adv_A.sys) s s' := by
    intro k s' hs'
    -- (buildWit (k+1)).val.2 = (buildWit k).val.1 by construction
    have h := (buildWit (k + 1)).2.2.2 s' hs'
    -- Push Prod.snd through the dite in buildWit to show equality
    convert h using 2
    simp only [wit_beliefs, flattenBeliefs, buildWit, apply_dite Prod.snd, apply_dite Subtype.val]
    split <;> rfl
  -- Step 5: Lift via beliefPLTS_lift
  obtain ⟨e_A, hval_A, hsig_A, hlab_A⟩ :=
    beliefPLTS_lift adv_A hres_A wit_beliefs wit_labels
      wit_sig wit_init wit_back
  -- Step 6: Assemble view correspondence
  have hsig_AB : ∀ k, φ.map_ss (wit_beliefs k).signal =
      (be_B.states k).signal := by
    intro k; simp only [wit_beliefs, flattenBeliefs, Equiv.apply_symm_apply]
  have hlab_AB : ∀ k, φ.map_ls (wit_labels k) = be_B.labels k := by
    intro k
    show φ.map_ls (sim_ba.label_map (be_B.labels k)) = be_B.labels k
    rw [show sim_ba.label_map (be_B.labels k) = φ.map_ls.symm (be_B.labels k) from
      congr_fun hba_label (be_B.labels k)]
    exact Equiv.apply_symm_apply φ.map_ls (be_B.labels k)
  exact ⟨e_A, hval_A, view_correspondence_belief adv_A adv_B φ e_A e_B
    (fun k => by
      conv_lhs => rw [hsig_A k]
      rw [hsig_AB k, hsig_B k])
    (fun k => by
      conv_lhs => rw [hlab_A k]
      rw [hlab_AB k, hlab_B k])⟩

/-- Execution-level chain AB: for every valid A-execution, there exists
    a valid B-execution with φ-related views. Symmetric to `prob_chain_BA`. -/
theorem prob_chain_AB
    {State_A : Type*} {Label_A : Type*} {SS_A : Type*} {LS_A : Type*}
    {State_B : Type*} {Label_B : Type*} {SS_B : Type*} {LS_B : Type*}
    (adv_A : Adversary State_A Label_A SS_A LS_A)
    (adv_B : Adversary State_B Label_B SS_B LS_B)
    (hres_A : adv_A.observation_resolving)
    (hres_B : adv_B.observation_resolving)
    [Inhabited Label_A] [Inhabited Label_B]
    (φ : SignalMap SS_A LS_A SS_B LS_B)
    (sig_lab_A : LTS.Labelling LS_A)
    (sig_lab_B : LTS.Labelling LS_B)
    (sim_ab : ProbForwardSim (adv_A.beliefPLTS hres_A) sig_lab_A
                              (adv_B.beliefPLTS hres_B) sig_lab_B)
    (hab_label : sim_ab.label_map = φ.map_ls)
    (hab_R : ∀ bs_a (ν : PMF (Adversary.BeliefState State_B SS_B)),
      sim_ab.R bs_a ν →
      ∀ bs_b ∈ ν.support, φ.map_ss bs_a.signal = bs_b.signal)
    (e_A : LTS.Execution State_A Label_A)
    (hval_A : (toLTS adv_A.sys).valid_exec e_A) :
    ∃ e_B : LTS.Execution State_B Label_B,
      (toLTS adv_B.sys).valid_exec e_B ∧
      φ.mapView (adv_A.obs.view e_A) = adv_B.obs.view e_B := by
  -- Step 1: Project e_A to belief-state execution of A
  obtain ⟨be_A, hval_beA, hsig_A, hlab_A, _⟩ :=
    beliefPLTS_project adv_A hres_A e_A hval_A
  have hreach_A := LTS.System.valid_exec_reachable hval_beA
  -- Helper: weak transition backward + belief-PLTS backward → original Star
  have backward_chain :
      ∀ (ν_prev ν' : PMF (Adversary.BeliefState State_B SS_B)),
      (∀ bs ∈ ν'.support, ∃ bs_prev ∈ ν_prev.support,
        LTS.Star (toLTS (adv_B.beliefPLTS hres_B)) bs_prev bs) →
      ∀ (ν_next : PMF (Adversary.BeliefState State_B SS_B)),
      (∀ bs ∈ ν_next.support, bs ∈ ν'.support) →
      ∀ s' ∈ (ν_next.bind (·.belief)).support,
        ∃ s ∈ (ν_prev.bind (·.belief)).support,
          LTS.Star (toLTS adv_B.sys) s s' := by
    intro ν_prev ν' hback ν_next hsub s' hs'
    obtain ⟨bs', hbs', hs'_bs'⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs'
    obtain ⟨bs, hbs, hstar_belief⟩ := hback bs' (hsub bs' hbs')
    obtain ⟨s, hs, hstar_sys⟩ :=
      beliefPLTS_star_backward adv_B hres_B hstar_belief s' hs'_bs'
    exact ⟨s, (PMF.mem_support_bind_iff _ _ _).mpr ⟨bs, hbs, hs⟩, hstar_sys⟩
  -- Build witness sequence of B-belief distributions
  let buildWit : (k : ℕ) →
      { p : PMF (Adversary.BeliefState State_B SS_B) ×
            PMF (Adversary.BeliefState State_B SS_B) //
        sim_ab.R (be_A.states k) p.1 ∧
        (∀ bs_b ∈ p.1.support,
          LTS.Reachable (toLTS (adv_B.beliefPLTS hres_B)) bs_b) ∧
        (∀ s' ∈ (p.1.bind (·.belief)).support,
          ∃ s ∈ (p.2.bind (·.belief)).support,
            LTS.Star (toLTS adv_B.sys) s s') } :=
    @Nat.rec
      (fun k => { p : PMF (Adversary.BeliefState State_B SS_B) ×
            PMF (Adversary.BeliefState State_B SS_B) //
        sim_ab.R (be_A.states k) p.1 ∧
        (∀ bs_b ∈ p.1.support,
          LTS.Reachable (toLTS (adv_B.beliefPLTS hres_B)) bs_b) ∧
        (∀ s' ∈ (p.1.bind (·.belief)).support,
          ∃ s ∈ (p.2.bind (·.belief)).support,
            LTS.Star (toLTS adv_B.sys) s s') })
      -- Base: k = 0, prev = self
      (let w := sim_ab.init_sim (be_A.states 0) hval_beA.1
       ⟨(w.1, w.1),
        w.2.1,
        fun bs hbs => .init (w.2.2 bs hbs),
        fun s' hs' => ⟨s', hs', .refl⟩⟩)
      -- Step: k → k+1
      (fun k prev =>
        let μ_A := (hval_beA.2 k).choose
        let hstep_A := (hval_beA.2 k).choose_spec.1
        let hmem_A := (hval_beA.2 k).choose_spec.2
        have comp_sub : ∀ {ν' : PMF (Adversary.BeliefState State_B SS_B)}
            (hlift : DistLiftR sim_ab.R μ_A ν'),
            ∀ bs ∈ (hlift.witness hmem_A).1.support, bs ∈ ν'.support :=
          fun hlift bs hbs => by
            rw [hlift.2.2, PMF.mem_support_bind_iff]
            exact ⟨be_A.states (k + 1), hmem_A, hbs⟩
        if hint : sig_lab_A.is_internal (be_A.labels k) = true then
          let w := sim_ab.step_internal (be_A.states k) (be_A.labels k)
            μ_A prev.1.1 (hreach_A k) prev.2.1 hint hstep_A
          let wit := w.2.2.witness hmem_A
          ⟨(wit.1, prev.1.1), wit.2,
           fun bs_b hbs_b => by
             obtain ⟨bs_prev, hbs_prev, hstar⟩ :=
               InternalWeakStar_support_backward w.2.1 bs_b
                 (comp_sub w.2.2 bs_b hbs_b)
             exact hstar.reachable (prev.2.2.1 bs_prev hbs_prev),
           backward_chain prev.1.1 w.1
             (InternalWeakStar_support_backward w.2.1)
             wit.1 (comp_sub w.2.2)⟩
        else
          let hext : sig_lab_A.is_external (be_A.labels k) = true :=
            show _ = true by simp [LTS.Labelling.is_external, hint]
          let w := sim_ab.step_external (be_A.states k) (be_A.labels k)
            μ_A prev.1.1 (hreach_A k) prev.2.1 hext hstep_A
          let wit := w.2.2.witness hmem_A
          ⟨(wit.1, prev.1.1), wit.2,
           fun bs_b hbs_b => by
             obtain ⟨bs_prev, hbs_prev, hstar⟩ :=
               WeakStep_support_backward w.2.1 bs_b
                 (comp_sub w.2.2 bs_b hbs_b)
             exact hstar.reachable (prev.2.2.1 bs_prev hbs_prev),
           backward_chain prev.1.1 w.1
             (WeakStep_support_backward w.2.1)
             wit.1 (comp_sub w.2.2)⟩)
  -- Step 3: Define flattened beliefs and labels
  let wit_beliefs : ℕ → Adversary.BeliefState State_B SS_B :=
    fun k => flattenBeliefs (buildWit k).1.1
      (φ.map_ss ((be_A.states k).signal))
  let wit_labels : ℕ → LS_B :=
    fun k => sim_ab.label_map (be_A.labels k)
  -- Step 4: Verify beliefPLTS_lift conditions
  -- Signal condition
  have wit_sig : ∀ k s, s ∈ (wit_beliefs k).belief.support →
      adv_B.obs.observe_state s = (wit_beliefs k).signal := by
    intro k s hs
    obtain ⟨bs_b, hbs_b, hs_bs⟩ := flattenBeliefs_mem_support hs
    have hreach_b := (buildWit k).2.2.1 bs_b hbs_b
    have hsig_b := beliefPLTS_reachable_sig adv_B hres_B hreach_b s hs_bs
    have hφ := hab_R (be_A.states k) (buildWit k).1.1 (buildWit k).2.1 bs_b hbs_b
    simp only [wit_beliefs, flattenBeliefs]
    rw [hsig_b, ← hφ]
  -- Init condition
  have wit_init : ∀ s ∈ (wit_beliefs 0).belief.support,
      adv_B.sys.init s := by
    intro s hs
    obtain ⟨bs_b, hbs_b, hs_bs⟩ := flattenBeliefs_mem_support hs
    exact ((sim_ab.init_sim (be_A.states 0) hval_beA.1).2.2 bs_b hbs_b s hs_bs).1
  -- Backward reachability
  have wit_back : ∀ k (s' : State_B),
      s' ∈ (wit_beliefs (k + 1)).belief.support →
      ∃ s ∈ (wit_beliefs k).belief.support,
        LTS.Star (toLTS adv_B.sys) s s' := by
    intro k s' hs'
    have h := (buildWit (k + 1)).2.2.2 s' hs'
    convert h using 2
    simp only [wit_beliefs, flattenBeliefs, buildWit, apply_dite Prod.snd, apply_dite Subtype.val]
    split <;> rfl
  -- Step 5: Lift via beliefPLTS_lift
  obtain ⟨e_B, hval_B, hsig_B, hlab_B⟩ :=
    beliefPLTS_lift adv_B hres_B wit_beliefs wit_labels
      wit_sig wit_init wit_back
  -- Step 6: Assemble view correspondence
  have hsig_AB : ∀ k, (wit_beliefs k).signal =
      φ.map_ss ((be_A.states k).signal) := by
    intro k; simp only [wit_beliefs, flattenBeliefs]
  have hlab_AB : ∀ k, wit_labels k = φ.map_ls (be_A.labels k) := by
    intro k
    show sim_ab.label_map (be_A.labels k) = φ.map_ls (be_A.labels k)
    exact congr_fun hab_label (be_A.labels k)
  exact ⟨e_B, hval_B, view_correspondence_belief adv_A adv_B φ e_A e_B
    (fun k => by rw [← hsig_A k, ← hsig_AB k, ← hsig_B k])
    (fun k => by rw [← hlab_A k, ← hlab_AB k, ← hlab_B k])⟩


/-! ## §3: Simulation Absolute Continuity

    A `ProbForwardSim` from concrete to abstract belief PLTSes induces
    **absolute continuity** between the execution measures: zero-measure
    view-conditional sets in the abstract system are also zero-measure
    in the concrete system.

    The proof decomposes into two steps:
    - `exec_measure_coupling` (sorry): build a joint Ionescu-Tulcea
      measure from the `ProbForwardSim` step-level couplings
    - `coupling_absolute_continuity` (proved): derive zero-set transfer
      from the coupling's marginal and concentration properties -/

/-- **Execution measure coupling** (the single sorry).

    The `ProbForwardSim` relates belief-PLTS transition kernels step by
    step via `DistLiftR`. Composing these step-level couplings via the
    Ionescu-Tulcea theorem gives a joint measure on paired execution
    sequences whose marginals are the two execution measures and which
    concentrates on signal-related, valid pairs.

    **SORRY**: requires new measure-theoretic infrastructure for
    composing coupled Markov kernels into a joint trajectory measure. -/
theorem exec_measure_coupling
    {S₁ : Type*} {L₁ : Type*} {SS₁ : Type*} {LS₁ : Type*}
    {S₂ : Type*} {L₂ : Type*} {SS₂ : Type*} {LS₂ : Type*}
    (adv₁ : Adversary S₁ L₁ SS₁ LS₁)
    (adv₂ : Adversary S₂ L₂ SS₂ LS₂)
    (hres₁ : adv₁.observation_resolving)
    (hres₂ : adv₂.observation_resolving)
    [Inhabited L₁] [Inhabited L₂]
    [MeasurableSpace S₁] [MeasurableSingletonClass S₁] [Countable S₁] [Inhabited S₁]
    [MeasurableSpace L₁] [MeasurableSingletonClass L₁] [Countable L₁]
    [MeasurableSpace S₂] [MeasurableSingletonClass S₂] [Countable S₂] [Inhabited S₂]
    [MeasurableSpace L₂] [MeasurableSingletonClass L₂] [Countable L₂]
    (φ : SignalMap SS₁ LS₁ SS₂ LS₂)
    (sig_lab₁ : LTS.Labelling LS₁)
    (sig_lab₂ : LTS.Labelling LS₂)
    (sim : ProbForwardSim (adv₁.beliefPLTS hres₁) sig_lab₁
                           (adv₂.beliefPLTS hres₂) sig_lab₂)
    (h_label : sim.label_map = φ.map_ls)
    (h_R : ∀ bs₁ (ν : PMF (Adversary.BeliefState S₂ SS₂)),
      sim.R bs₁ ν → ∀ bs₂ ∈ ν.support, φ.map_ss bs₁.signal = bs₂.signal)
    (σ₁ : Strategy SS₁ LS₁) (s₀₁ : S₁) (hinit₁ : adv₁.sys.init s₀₁)
    (σ₂ : Strategy SS₂ LS₂) (s₀₂ : S₂) (hinit₂ : adv₂.sys.init s₀₂) :
    -- There exists a joint measure (coupling) on paired execution sequences
    ∃ γ : MeasureTheory.Measure ((ℕ → S₁ × L₁) × (ℕ → S₂ × L₂)),
      -- Marginal 1 is the concrete execution measure
      γ.map Prod.fst = rand_exec_measure adv₁ hres₁ σ₁.toRandomised s₀₁ ∧
      -- Marginal 2 is the abstract execution measure
      γ.map Prod.snd = rand_exec_measure adv₂ hres₂ σ₂.toRandomised s₀₂ ∧
      -- The coupling concentrates on signal-related, valid pairs:
      -- the complement has measure zero
      γ {p | φ.mapView (adv₁.obs.view (rand_to_exec p.1)) =
             adv₂.obs.view (rand_to_exec p.2) ∧
             (toLTS adv₁.sys).valid_exec (rand_to_exec p.1) ∧
             (toLTS adv₂.sys).valid_exec (rand_to_exec p.2)}ᶜ = 0 := by
  sorry

/-- **Coupling implies absolute continuity** (fully proved).

    Given a coupling `γ` with marginals `μ₁`, `μ₂` that concentrates on
    signal-related valid pairs, if `μ₂({view = v₂ ∧ Q₂}) = 0` then
    `μ₁({view = v₁ ∧ Q₁}) = 0`, provided Q₁ ↔ Q₂ on valid related pairs.

    Proof: `μ₂(S₂) = 0` implies `γ(snd⁻¹(S₂)) = 0` (marginal).
    The subset inclusion `fst⁻¹(S₁) ∩ C ⊆ snd⁻¹(S₂)` (from Q₁→Q₂ on C)
    gives `γ(fst⁻¹(S₁) ∩ C) = 0`. Since `γ(Cᶜ) = 0`, decomposing
    `fst⁻¹(S₁) = (fst⁻¹(S₁) ∩ C) ∪ (fst⁻¹(S₁) \ C)` gives
    `γ(fst⁻¹(S₁)) = 0`, hence `μ₁(S₁) = 0`. -/
theorem coupling_absolute_continuity
    {S₁ : Type*} {L₁ : Type*} {SS₁ : Type*} {LS₁ : Type*}
    {S₂ : Type*} {L₂ : Type*} {SS₂ : Type*} {LS₂ : Type*}
    (adv₁ : Adversary S₁ L₁ SS₁ LS₁)
    (adv₂ : Adversary S₂ L₂ SS₂ LS₂)
    [MeasurableSpace S₁] [MeasurableSingletonClass S₁] [Countable S₁] [Inhabited S₁]
    [MeasurableSpace L₁] [MeasurableSingletonClass L₁] [Countable L₁]
    [MeasurableSpace S₂] [MeasurableSingletonClass S₂] [Countable S₂] [Inhabited S₂]
    [MeasurableSpace L₂] [MeasurableSingletonClass L₂] [Countable L₂]
    (φ : SignalMap SS₁ LS₁ SS₂ LS₂)
    (μ₁ : MeasureTheory.Measure (ℕ → S₁ × L₁))
    (μ₂ : MeasureTheory.Measure (ℕ → S₂ × L₂))
    -- The coupling
    (γ : MeasureTheory.Measure ((ℕ → S₁ × L₁) × (ℕ → S₂ × L₂)))
    (hmarg₁ : γ.map Prod.fst = μ₁)
    (hmarg₂ : γ.map Prod.snd = μ₂)
    -- The coupling concentrates on signal-related valid pairs
    (hCc_zero : γ {p | φ.mapView (adv₁.obs.view (rand_to_exec p.1)) =
                       adv₂.obs.view (rand_to_exec p.2) ∧
                       (toLTS adv₁.sys).valid_exec (rand_to_exec p.1) ∧
                       (toLTS adv₂.sys).valid_exec (rand_to_exec p.2)}ᶜ = 0)
    -- Views and properties
    (v₁ : Observation.ExecView SS₁ LS₁) (v₂ : Observation.ExecView SS₂ LS₂)
    (hv : φ.mapView v₁ = v₂)
    (Q₁ : LTS.Execution S₁ L₁ → Prop) (Q₂ : LTS.Execution S₂ L₂ → Prop)
    -- Q₁ → Q₂ on valid, view-related pairs
    (hQ : ∀ e₁ e₂, (toLTS adv₁.sys).valid_exec e₁ →
      (toLTS adv₂.sys).valid_exec e₂ →
      φ.mapView (adv₁.obs.view e₁) = adv₂.obs.view e₂ →
      (Q₁ e₁ ↔ Q₂ e₂))
    -- Measurability of the view-property sets
    (hmeas₁ : MeasurableSet (adv₁.lift_to_exec (fun e => adv₁.obs.view e = v₁ ∧ Q₁ e)))
    (hmeas₂ : MeasurableSet (adv₂.lift_to_exec (fun e => adv₂.obs.view e = v₂ ∧ Q₂ e))) :
    μ₂ (adv₂.lift_to_exec (fun e => adv₂.obs.view e = v₂ ∧ Q₂ e)) = 0 →
    μ₁ (adv₁.lift_to_exec (fun e => adv₁.obs.view e = v₁ ∧ Q₁ e)) = 0 := by
  intro hμ₂_zero
  set C := {p : (ℕ → S₁ × L₁) × (ℕ → S₂ × L₂) |
    φ.mapView (adv₁.obs.view (rand_to_exec p.1)) =
      adv₂.obs.view (rand_to_exec p.2) ∧
    (toLTS adv₁.sys).valid_exec (rand_to_exec p.1) ∧
    (toLTS adv₂.sys).valid_exec (rand_to_exec p.2)}
  set S₁_set := adv₁.lift_to_exec (fun e => adv₁.obs.view e = v₁ ∧ Q₁ e)
  set S₂_set := adv₂.lift_to_exec (fun e => adv₂.obs.view e = v₂ ∧ Q₂ e)
  -- Key subset: fst⁻¹(S₁) ∩ C ⊆ snd⁻¹(S₂)
  have hsub : Prod.fst ⁻¹' S₁_set ∩ C ⊆ Prod.snd ⁻¹' S₂_set := by
    intro ⟨ω₁, ω₂⟩ ⟨⟨hv₁, hQ₁⟩, hrel, hval₁, hval₂⟩
    constructor
    · show adv₂.obs.view (rand_to_exec ω₂) = v₂
      rw [← hrel, hv₁, hv]
    · exact (hQ _ _ hval₁ hval₂ hrel).mp hQ₁
  -- γ(snd⁻¹(S₂)) = 0: from hmarg₂ and hμ₂_zero
  have hsnd_zero : γ (Prod.snd ⁻¹' S₂_set) = 0 := by
    rw [← MeasureTheory.Measure.map_apply measurable_snd hmeas₂, hmarg₂, hμ₂_zero]
  -- γ(fst⁻¹(S₁) ∩ C) = 0: by subset inclusion
  have hfst_C_zero : γ (Prod.fst ⁻¹' S₁_set ∩ C) = 0 :=
    le_antisymm (le_trans (MeasureTheory.measure_mono hsub) (le_of_eq hsnd_zero))
      (zero_le _)
  -- γ(fst⁻¹(S₁)) = 0: split into C and Cᶜ parts
  have hfst_zero : γ (Prod.fst ⁻¹' S₁_set) = 0 := by
    have h := MeasureTheory.measure_le_inter_add_diff γ (Prod.fst ⁻¹' S₁_set) C
    have hdiff_zero : γ (Prod.fst ⁻¹' S₁_set \ C) = 0 :=
      le_antisymm (le_trans (MeasureTheory.measure_mono
        (Set.diff_subset_compl _ _)) (le_of_eq hCc_zero)) (zero_le _)
    rw [hfst_C_zero, hdiff_zero, add_zero] at h
    exact le_antisymm h (zero_le _)
  -- μ₁(S₁) = 0: from hmarg₁
  rw [← hmarg₁, MeasureTheory.Measure.map_apply measurable_fst hmeas₁, hfst_zero]

/-- **Simulation absolute continuity**: `ProbForwardSim concrete abstract`
    implies zero-measure view-conditional sets in the abstract system are
    also zero-measure in the concrete system.

    Proved by composing `exec_measure_coupling` (builds coupling γ) with
    `coupling_absolute_continuity` (derives zero-set transfer from γ). -/
theorem simulation_absolute_continuity
    {S₁ : Type*} {L₁ : Type*} {SS₁ : Type*} {LS₁ : Type*}
    {S₂ : Type*} {L₂ : Type*} {SS₂ : Type*} {LS₂ : Type*}
    (adv₁ : Adversary S₁ L₁ SS₁ LS₁)
    (adv₂ : Adversary S₂ L₂ SS₂ LS₂)
    (hres₁ : adv₁.observation_resolving)
    (hres₂ : adv₂.observation_resolving)
    [Inhabited L₁] [Inhabited L₂]
    [MeasurableSpace S₁] [MeasurableSingletonClass S₁] [Countable S₁] [Inhabited S₁]
    [MeasurableSpace L₁] [MeasurableSingletonClass L₁] [Countable L₁]
    [MeasurableSpace S₂] [MeasurableSingletonClass S₂] [Countable S₂] [Inhabited S₂]
    [MeasurableSpace L₂] [MeasurableSingletonClass L₂] [Countable L₂]
    (φ : SignalMap SS₁ LS₁ SS₂ LS₂)
    (sig_lab₁ : LTS.Labelling LS₁)
    (sig_lab₂ : LTS.Labelling LS₂)
    (sim : ProbForwardSim (adv₁.beliefPLTS hres₁) sig_lab₁
                           (adv₂.beliefPLTS hres₂) sig_lab₂)
    (h_label : sim.label_map = φ.map_ls)
    (h_R : ∀ bs₁ (ν : PMF (Adversary.BeliefState S₂ SS₂)),
      sim.R bs₁ ν → ∀ bs₂ ∈ ν.support, φ.map_ss bs₁.signal = bs₂.signal)
    (σ₁ : Strategy SS₁ LS₁) (s₀₁ : S₁) (hinit₁ : adv₁.sys.init s₀₁)
    (σ₂ : Strategy SS₂ LS₂) (s₀₂ : S₂) (hinit₂ : adv₂.sys.init s₀₂)
    (v₁ : Observation.ExecView SS₁ LS₁) (v₂ : Observation.ExecView SS₂ LS₂)
    (hv : φ.mapView v₁ = v₂)
    (Q₁ : LTS.Execution S₁ L₁ → Prop) (Q₂ : LTS.Execution S₂ L₂ → Prop)
    (hQ : ∀ e₁ e₂, (toLTS adv₁.sys).valid_exec e₁ →
      (toLTS adv₂.sys).valid_exec e₂ →
      φ.mapView (adv₁.obs.view e₁) = adv₂.obs.view e₂ → (Q₁ e₁ ↔ Q₂ e₂))
    (hmeas₁ : MeasurableSet (adv₁.lift_to_exec (fun e => adv₁.obs.view e = v₁ ∧ Q₁ e)))
    (hmeas₂ : MeasurableSet (adv₂.lift_to_exec (fun e => adv₂.obs.view e = v₂ ∧ Q₂ e))) :
    rand_exec_measure adv₂ hres₂ σ₂.toRandomised s₀₂
      (adv₂.lift_to_exec (fun e => adv₂.obs.view e = v₂ ∧ Q₂ e)) = 0 →
    rand_exec_measure adv₁ hres₁ σ₁.toRandomised s₀₁
      (adv₁.lift_to_exec (fun e => adv₁.obs.view e = v₁ ∧ Q₁ e)) = 0 := by
  -- Step 1: Build the coupling
  obtain ⟨γ, hmarg₁, hmarg₂, hCc_zero⟩ :=
    exec_measure_coupling adv₁ adv₂ hres₁ hres₂ φ sig_lab₁ sig_lab₂
      sim h_label h_R σ₁ s₀₁ hinit₁ σ₂ s₀₂ hinit₂
  -- Step 2: Coupling implies absolute continuity
  exact coupling_absolute_continuity adv₁ adv₂ φ
    (rand_exec_measure adv₁ hres₁ σ₁.toRandomised s₀₁)
    (rand_exec_measure adv₂ hres₂ σ₂.toRandomised s₀₂)
    γ hmarg₁ hmarg₂ hCc_zero v₁ v₂ hv Q₁ Q₂ hQ hmeas₁ hmeas₂

/-! ## §4: Main Theorem -/

/-- **Probabilistic possibilistic secrecy transfer** via `ProbForwardSim`.

    Bidirectional `ProbForwardSim` between belief PLTSes transfers
    `prob_possibilistic_secret` from system A to system B.

    The proof applies `simulation_absolute_continuity` twice:
    - With `sim_ba` (B concrete, A abstract): contrapositive of
      `μ_A({view}) = 0 → μ_B({view}) = 0` gives view realizability transfer
    - With `sim_ab` (A concrete, B abstract): `μ_B({view ∧ Q_B}) = 0 →
      μ_A({view ∧ Q_A}) = 0` transfers inferability from B to A,
      contradicting A's secrecy -/
theorem prob_possibilistic_secret_transfer
    {State_A : Type*} {Label_A : Type*} {SS_A : Type*} {LS_A : Type*}
    {State_B : Type*} {Label_B : Type*} {SS_B : Type*} {LS_B : Type*}
    (adv_A : Adversary State_A Label_A SS_A LS_A)
    (adv_B : Adversary State_B Label_B SS_B LS_B)
    (hres_A : adv_A.observation_resolving)
    (hres_B : adv_B.observation_resolving)
    [Inhabited Label_A] [Inhabited Label_B]
    [MeasurableSpace State_A] [MeasurableSingletonClass State_A]
    [Countable State_A] [Inhabited State_A]
    [MeasurableSpace Label_A] [MeasurableSingletonClass Label_A] [Countable Label_A]
    [MeasurableSpace State_B] [MeasurableSingletonClass State_B]
    [Countable State_B] [Inhabited State_B]
    [MeasurableSpace Label_B] [MeasurableSingletonClass Label_B] [Countable Label_B]
    (φ : SignalMap SS_A LS_A SS_B LS_B)
    (P_A : LTS.Execution State_A Label_A → Prop)
    (P_B : LTS.Execution State_B Label_B → Prop)
    (C_A : Observation.ExecView SS_A LS_A → Prop)
    (C_B : Observation.ExecView SS_B LS_B → Prop)
    (h_sec_A : adv_A.prob_possibilistic_secret hres_A P_A C_A)
    (sig_lab_A : LTS.Labelling LS_A)
    (sig_lab_B : LTS.Labelling LS_B)
    (sim_ab : ProbForwardSim (adv_A.beliefPLTS hres_A) sig_lab_A
                              (adv_B.beliefPLTS hres_B) sig_lab_B)
    (sim_ba : ProbForwardSim (adv_B.beliefPLTS hres_B) sig_lab_B
                              (adv_A.beliefPLTS hres_A) sig_lab_A)
    (hab_label : sim_ab.label_map = φ.map_ls)
    (hab_R : ∀ bs_a (ν : PMF (Adversary.BeliefState State_B SS_B)),
      sim_ab.R bs_a ν →
      ∀ bs_b ∈ ν.support, φ.map_ss bs_a.signal = bs_b.signal)
    (hba_label : sim_ba.label_map = φ.map_ls.symm)
    (hba_R : ∀ bs_b (ν : PMF (Adversary.BeliefState State_A SS_A)),
      sim_ba.R bs_b ν →
      ∀ bs_a ∈ ν.support, φ.map_ss bs_a.signal = bs_b.signal)
    (h_prop : ∀ e_A e_B, (toLTS adv_A.sys).valid_exec e_A →
      (toLTS adv_B.sys).valid_exec e_B →
      φ.mapView (adv_A.obs.view e_A) = adv_B.obs.view e_B →
      (P_A e_A ↔ P_B e_B))
    (h_cond : ∀ v_A, C_B (φ.mapView v_A) → C_A v_A)
    -- Measurability of the property predicates on execution sequences
    (hmeas_P_A : ∀ v, MeasurableSet (adv_A.lift_to_exec (fun e => adv_A.obs.view e = v ∧ P_A e)))
    (hmeas_P_B : ∀ v, MeasurableSet (adv_B.lift_to_exec (fun e => adv_B.obs.view e = v ∧ P_B e)))
    (hmeas_nP_A : ∀ v, MeasurableSet (adv_A.lift_to_exec (fun e => adv_A.obs.view e = v ∧ ¬P_A e)))
    (hmeas_nP_B : ∀ v, MeasurableSet (adv_B.lift_to_exec (fun e => adv_B.obs.view e = v ∧ ¬P_B e))) :
    adv_B.prob_possibilistic_secret hres_B P_B C_B := by
  intro σ_B s₀_B hinit_B v_B hC_B hμ_B_pos
  -- Construct v_A from v_B via φ⁻¹
  let v_A : Observation.ExecView SS_A LS_A :=
    { state_signals := φ.map_ss.symm ∘ v_B.state_signals
      label_signals := φ.map_ls.symm ∘ v_B.label_signals }
  have hv_rel : φ.mapView v_A = v_B := by
    show Observation.ExecView.mk _ _ = v_B
    congr 1 <;> ext k <;> simp [v_A, Function.comp_def,
      Equiv.apply_symm_apply]
  have hC_A : C_A v_A := h_cond v_A (hv_rel ▸ hC_B)
  -- Step 1: View transfer B→A via sim_ba absolute continuity
  -- sim_ba gives: μ_A({view=v_A ∧ True}) = 0 → μ_B({view=v_B ∧ True}) = 0
  -- Contrapositive: μ_B({view=v_B}) > 0 → μ_A({view=v_A}) > 0
  -- (with Q = True and φ.symm signal map)
  -- Derive an A-initial state from sim_ba and hinit_B
  have ⟨s₀_A, hinit_A⟩ : ∃ s₀, adv_A.sys.init s₀ := by
    let bs_b : Adversary.BeliefState State_B SS_B :=
      ⟨adv_B.obs.observe_state s₀_B, PMF.pure s₀_B⟩
    have hbs_b_init : (adv_B.beliefPLTS hres_B).init bs_b :=
      fun s hs => by
        rw [PMF.mem_support_pure_iff] at hs; rw [hs]; exact ⟨hinit_B, rfl⟩
    obtain ⟨ν_A, _, hinit_ν⟩ := sim_ba.init_sim bs_b hbs_b_init
    obtain ⟨bs_a, hbs_a⟩ := ν_A.support_nonempty
    obtain ⟨s, hs⟩ := bs_a.belief.support_nonempty
    exact ⟨s, (hinit_ν bs_a hbs_a s hs).1⟩
  -- Pick any strategy for A
  let σ_A : Strategy SS_A LS_A := fun _ _ => sig_lab_A.tau
  -- Step 1: View transfer B→A via sim_ba absolute continuity (contrapositive)
  -- simulation_absolute_continuity with sim_ba (B concrete, A abstract, φ.symm):
  --   μ_A({view ∧ Q_A}) = 0 → μ_B({view ∧ Q_B}) = 0
  -- With Q = True: μ_A({view}) = 0 → μ_B({view}) = 0
  -- Contrapositive: μ_B > 0 → μ_A > 0
  have hba_R' : ∀ bs_b (ν : PMF (Adversary.BeliefState State_A SS_A)),
      sim_ba.R bs_b ν → ∀ bs_a ∈ ν.support,
        φ.symm.map_ss bs_b.signal = bs_a.signal :=
    fun bs_b ν hR bs_a hbs_a => by
      have := hba_R bs_b ν hR bs_a hbs_a
      simp [SignalMap.symm, Equiv.symm_apply_eq]; exact this.symm
  have hv_rel' : φ.symm.mapView v_B = v_A := by
    show Observation.ExecView.mk _ _ = v_A
    congr 1
  have hμ_A_pos : rand_exec_measure adv_A hres_A σ_A.toRandomised s₀_A
      (adv_A.lift_to_exec (fun e => adv_A.obs.view e = v_A)) > 0 := by
    by_contra h
    simp only [not_lt] at h
    have hμ_A_zero : rand_exec_measure adv_A hres_A σ_A.toRandomised s₀_A
        (adv_A.lift_to_exec (fun e => adv_A.obs.view e = v_A ∧ True)) = 0 := by
      apply le_antisymm _ (zero_le _)
      calc rand_exec_measure adv_A hres_A σ_A.toRandomised s₀_A
              (adv_A.lift_to_exec (fun e => adv_A.obs.view e = v_A ∧ True))
          ≤ rand_exec_measure adv_A hres_A σ_A.toRandomised s₀_A
              (adv_A.lift_to_exec (fun e => adv_A.obs.view e = v_A)) :=
            MeasureTheory.measure_mono (fun ω ⟨hv, _⟩ => hv)
        _ ≤ 0 := h
    have hμ_B_zero := simulation_absolute_continuity adv_B adv_A hres_B hres_A
      φ.symm sig_lab_B sig_lab_A sim_ba hba_label hba_R'
      σ_B s₀_B hinit_B σ_A s₀_A hinit_A v_B v_A hv_rel'
      (fun _ => True) (fun _ => True)
      (fun _ _ _ _ _ => Iff.rfl)
      -- MeasurableSet {view = v_B ∧ True}: decompose via excluded middle on P_B
      (show MeasurableSet (adv_B.lift_to_exec
          (fun e => adv_B.obs.view e = v_B ∧ (fun _ => True) e)) from by
        have : adv_B.lift_to_exec (fun e => adv_B.obs.view e = v_B ∧ (fun _ => True) e) =
               adv_B.lift_to_exec (fun e => adv_B.obs.view e = v_B ∧ P_B e) ∪
               adv_B.lift_to_exec (fun e => adv_B.obs.view e = v_B ∧ ¬P_B e) := by
          ext ω; simp [Adversary.lift_to_exec]; tauto
        rw [this]; exact (hmeas_P_B v_B).union (hmeas_nP_B v_B))
      -- MeasurableSet {view = v_A ∧ True}: same for A
      (show MeasurableSet (adv_A.lift_to_exec
          (fun e => adv_A.obs.view e = v_A ∧ (fun _ => True) e)) from by
        have : adv_A.lift_to_exec (fun e => adv_A.obs.view e = v_A ∧ (fun _ => True) e) =
               adv_A.lift_to_exec (fun e => adv_A.obs.view e = v_A ∧ P_A e) ∪
               adv_A.lift_to_exec (fun e => adv_A.obs.view e = v_A ∧ ¬P_A e) := by
          ext ω; simp [Adversary.lift_to_exec]; tauto
        rw [this]; exact (hmeas_P_A v_A).union (hmeas_nP_A v_A))
      hμ_A_zero
    have hμ_B_le : rand_exec_measure adv_B hres_B σ_B.toRandomised s₀_B
        (adv_B.lift_to_exec (fun e => adv_B.obs.view e = v_B)) ≤ 0 :=
      le_trans (MeasureTheory.measure_mono
        (show adv_B.lift_to_exec (fun e => adv_B.obs.view e = v_B) ⊆
              adv_B.lift_to_exec (fun e => adv_B.obs.view e = v_B ∧ True) from
          fun ω hv => ⟨hv, trivial⟩))
        (le_of_eq hμ_B_zero)
    exact absurd hμ_B_pos (not_lt.mpr hμ_B_le)
  -- Step 2: Apply A's probabilistic secrecy
  obtain ⟨hnot_pos_A, hnot_neg_A⟩ := h_sec_A σ_A s₀_A hinit_A v_A hC_A hμ_A_pos
  -- Step 3: Property transfer via sim_ab absolute continuity
  -- sim_ab gives: μ_B({view ∧ Q_B}) = 0 → μ_A({view ∧ Q_A}) = 0
  constructor
  · -- ¬ prob_positively_inferable for B
    intro hpos_B
    apply hnot_pos_A
    exact simulation_absolute_continuity adv_A adv_B hres_A hres_B
      φ sig_lab_A sig_lab_B sim_ab hab_label hab_R
      σ_A s₀_A hinit_A σ_B s₀_B hinit_B v_A v_B hv_rel
      (fun e => ¬P_A e) (fun e => ¬P_B e)
      (fun e_A e_B hv_A hv_B hview => (h_prop e_A e_B hv_A hv_B hview).not)
      (hmeas_nP_A v_A) (hmeas_nP_B v_B) hpos_B
  · -- ¬ prob_negatively_inferable for B
    intro hneg_B
    apply hnot_neg_A
    exact simulation_absolute_continuity adv_A adv_B hres_A hres_B
      φ sig_lab_A sig_lab_B sim_ab hab_label hab_R
      σ_A s₀_A hinit_A σ_B s₀_B hinit_B v_A v_B hv_rel
      P_A P_B h_prop (hmeas_P_A v_A) (hmeas_P_B v_B) hneg_B

end PLTS
