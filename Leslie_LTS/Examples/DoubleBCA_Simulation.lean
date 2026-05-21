import Leslie_LTS.Examples.DoubleBCA
import Leslie_LTS.Examples.DoubleIdealBCA
import Leslie_LTS.Examples.BCA_Simulation

/-! # Forward Simulation: Double BCA → Double Ideal BCA

    Constructs a `ForwardSim` from `doubleBCA` to `doubleIdealBCA` by
    composing the per-round forward simulations from `BCA_Simulation`.

    - `.par` steps: delegate to the per-round simulations
    - `.output` steps: matched one-to-one (external on both sides)
-/

open LTS

namespace DoubleBCA_Simulation


variable (T : Type) [DecidableEq T] (n f : Nat)

/-! ## FinalVal Mapping -/

/-- Map concrete FinalVal to ideal FinalVal. -/
def map_fv : DoubleBCA_LTS.FinalVal T → DoubleIdealBCA.FinalVal T
  | .bot => .bot
  | .valA v => .valA v
  | .valB v => .valB v

/-! ## Simulation Relation -/

/-- Product simulation relation on the round states, plus final outputs agree
    (up to the FinalVal mapping), plus abstract rounds are reachable. -/
def sim_rel (s_c : DoubleBCA_LTS.State T n)
    (s_a : DoubleIdealBCA.State T n) : Prop :=
  BCA_Simulation.sim_rel T n f s_c.r1 s_a.r1 ∧
  BCA_Simulation.sim_rel (BCA_LTS.Val T) n f s_c.r2 s_a.r2 ∧
  (∀ p, s_a.final p = (s_c.final p).map (map_fv T)) ∧
  Reachable (IdealBCA.ideal_bca T n f) s_a.r1 ∧
  Reachable (IdealBCA.ideal_bca (IdealBCA.Val T) n f) s_a.r2

/-! ## Label Map -/

/-- Label map from double BCA labels to double ideal BCA labels. -/
def label_map [Inhabited T] :
    DoubleBCA_LTS.Label T n → DoubleIdealBCA.Label T n
  | .par cl =>
    .par (match cl with
      | .left l₁ => .left (BCA_Simulation.label_map T n l₁)
      | .right l₂ => .right (BCA_Simulation.label_map (BCA_LTS.Val T) n l₂)
      | .sync l₁ l₂ => .sync (BCA_Simulation.label_map T n l₁)
                              (BCA_Simulation.label_map (BCA_LTS.Val T) n l₂))
  | .output i v => .output i (map_fv T v)

/-! ## Infrastructure -/

/-- Project reachability from the double system to round 1. -/
private theorem reachable_r1 (s : DoubleBCA_LTS.State T n)
    (h : Reachable (DoubleBCA_LTS.doubleBCA T n f) s) :
    Reachable (BCA_LTS.bca T n f) s.r1 := by
  induction h with
  | init hinit => exact .init hinit.1.1
  | @step s l s' _ hstep ih =>
    match l with
    | .par cl =>
      have ⟨hpar_step, _⟩ := hstep
      simp only [DoubleBCA_LTS.par_system, parallel] at hpar_step
      match cl with
      | .left l₁ =>
        obtain ⟨_, hs₁, _⟩ := hpar_step; exact .step ih hs₁
      | .right _ =>
        obtain ⟨_, _, heq⟩ := hpar_step; rw [heq]; exact ih
      | .sync l₁ _ =>
        obtain ⟨_, hs₁, _⟩ := hpar_step; exact .step ih hs₁
    | .output _ _ =>
      have ⟨_, _, _, heq, _, _⟩ := hstep; rw [heq]; exact ih

/-- Project reachability from the double system to round 2. -/
private theorem reachable_r2 (s : DoubleBCA_LTS.State T n)
    (h : Reachable (DoubleBCA_LTS.doubleBCA T n f) s) :
    Reachable (BCA_LTS.bca (BCA_LTS.Val T) n f) s.r2 := by
  induction h with
  | init hinit => exact .init hinit.1.2
  | @step s l s' _ hstep ih =>
    match l with
    | .par cl =>
      have ⟨hpar_step, _⟩ := hstep
      simp only [DoubleBCA_LTS.par_system, parallel] at hpar_step
      match cl with
      | .left _ =>
        obtain ⟨_, _, heq⟩ := hpar_step; rw [heq]; exact ih
      | .right l₂ =>
        obtain ⟨_, hs₂, _⟩ := hpar_step; exact .step ih hs₂
      | .sync _ l₂ =>
        obtain ⟨_, _, hs₂⟩ := hpar_step; exact .step ih hs₂
    | .output _ _ =>
      have ⟨_, _, _, _, heq, _⟩ := hstep; rw [heq]; exact ih

/-- A single internal IdealBCA round 1 step lifts to the double system. -/
private theorem lift_r1_step [Inhabited T] [Inhabited (Fin n)]
    (r1 : IdealBCA.State T n) (r2 : IdealBCA.State (IdealBCA.Val T) n)
    (fin : Fin n → Option (DoubleIdealBCA.FinalVal T))
    (l : IdealBCA.Label T n) (r1' : IdealBCA.State T n)
    (hint : (IdealBCA.ideal_labelling T n).is_internal l = true)
    (hstep : (IdealBCA.ideal_bca T n f).step r1 l r1') :
    (DoubleIdealBCA.doubleIdealBCA T n f).step ⟨r1, r2, fin⟩ (.par (.left l)) ⟨r1', r2, fin⟩ ∧
    (DoubleIdealBCA.labelling T n).is_internal (.par (.left l)) = true := by
  constructor
  · constructor
    · simp only [DoubleIdealBCA.par_system, parallel]
      refine ⟨?_, hstep, trivial⟩
      intro l₂; match l with
      | .bind _ => simp [DoubleIdealBCA.sync_pred]
      | .input _ _ => simp [IdealBCA.ideal_labelling] at hint
      | .corrupt _ => simp [IdealBCA.ideal_labelling] at hint
      | .output _ _ => simp [IdealBCA.ideal_labelling] at hint
    · rfl
  · match l with
    | .bind _ => rfl
    | .input _ _ => simp [IdealBCA.ideal_labelling] at hint
    | .corrupt _ => simp [IdealBCA.ideal_labelling] at hint
    | .output _ _ => simp [IdealBCA.ideal_labelling] at hint

/-- Lift an InternalStar of round 1 IdealBCA steps to the double system. -/
private def lift_r1_internal_star_aux [Inhabited T] [Inhabited (Fin n)]
    {r1 : IdealBCA.State T n} {t₁' : IdealBCA.State T n}
    (hstar : InternalStar (IdealBCA.ideal_bca T n f)
      (IdealBCA.ideal_labelling T n) r1 t₁')
    (s_a : DoubleIdealBCA.State T n) (hr1 : s_a.r1 = r1) :
    Σ' s_a', InternalStar (DoubleIdealBCA.doubleIdealBCA T n f)
      (DoubleIdealBCA.labelling T n) s_a s_a' ×'
      (s_a'.r1 = t₁' ∧ s_a'.r2 = s_a.r2 ∧ s_a'.final = s_a.final) :=
  match hr1, hstar with
  | rfl, .refl => ⟨s_a, .refl, rfl, rfl, rfl⟩
  | rfl, .step hint' hstep' rest =>
    let ⟨hstep_d, hint_d⟩ := lift_r1_step T n f _ s_a.r2 s_a.final _ _ hint' hstep'
    let ⟨s_a', hstar', heq_r1, heq_r2, heq_fin⟩ :=
      lift_r1_internal_star_aux rest ⟨_, s_a.r2, s_a.final⟩ rfl
    ⟨s_a', .step hint_d hstep_d hstar',
           heq_r1, by rw [heq_r2], by rw [heq_fin]⟩

private def lift_r1_internal_star [Inhabited T] [Inhabited (Fin n)]
    (s_a : DoubleIdealBCA.State T n)
    (t₁' : IdealBCA.State T n)
    (hstar : InternalStar (IdealBCA.ideal_bca T n f)
      (IdealBCA.ideal_labelling T n) s_a.r1 t₁') :
    Σ' s_a', InternalStar (DoubleIdealBCA.doubleIdealBCA T n f)
      (DoubleIdealBCA.labelling T n) s_a s_a' ×'
      (s_a'.r1 = t₁' ∧ s_a'.r2 = s_a.r2 ∧ s_a'.final = s_a.final) :=
  lift_r1_internal_star_aux T n f hstar s_a rfl

/-- A single internal IdealBCA round 2 step lifts to the double system. -/
private theorem lift_r2_step [Inhabited T] [Inhabited (Fin n)]
    (r1 : IdealBCA.State T n) (r2 : IdealBCA.State (IdealBCA.Val T) n)
    (fin : Fin n → Option (DoubleIdealBCA.FinalVal T))
    (l : IdealBCA.Label (IdealBCA.Val T) n) (r2' : IdealBCA.State (IdealBCA.Val T) n)
    (hint : (IdealBCA.ideal_labelling (IdealBCA.Val T) n).is_internal l = true)
    (hstep : (IdealBCA.ideal_bca (IdealBCA.Val T) n f).step r2 l r2') :
    (DoubleIdealBCA.doubleIdealBCA T n f).step ⟨r1, r2, fin⟩ (.par (.right l)) ⟨r1, r2', fin⟩ ∧
    (DoubleIdealBCA.labelling T n).is_internal (.par (.right l)) = true := by
  constructor
  · constructor
    · simp only [DoubleIdealBCA.par_system, parallel]
      refine ⟨?_, hstep, trivial⟩
      intro l₁; match l with
      | .bind _ => simp [DoubleIdealBCA.sync_pred]
      | .input _ _ => simp [IdealBCA.ideal_labelling] at hint
      | .corrupt _ => simp [IdealBCA.ideal_labelling] at hint
      | .output _ _ => simp [DoubleIdealBCA.sync_pred]
    · rfl
  · simp [DoubleIdealBCA.labelling]

/-- Lift an InternalStar of round 2 IdealBCA steps to the double system. -/
private def lift_r2_internal_star_aux [Inhabited T] [Inhabited (Fin n)]
    {r2 : IdealBCA.State (IdealBCA.Val T) n} {t₂' : IdealBCA.State (IdealBCA.Val T) n}
    (hstar : InternalStar (IdealBCA.ideal_bca (IdealBCA.Val T) n f)
      (IdealBCA.ideal_labelling (IdealBCA.Val T) n) r2 t₂')
    (s_a : DoubleIdealBCA.State T n) (hr2 : s_a.r2 = r2) :
    Σ' s_a', InternalStar (DoubleIdealBCA.doubleIdealBCA T n f)
      (DoubleIdealBCA.labelling T n) s_a s_a' ×'
      (s_a'.r1 = s_a.r1 ∧ s_a'.r2 = t₂' ∧ s_a'.final = s_a.final) :=
  match hr2, hstar with
  | rfl, .refl => ⟨s_a, .refl, rfl, rfl, rfl⟩
  | rfl, .step hint' hstep' rest =>
    let ⟨hstep_d, hint_d⟩ := lift_r2_step T n f s_a.r1 _ s_a.final _ _ hint' hstep'
    let ⟨s_a', hstar', heq_r1, heq_r2, heq_fin⟩ :=
      lift_r2_internal_star_aux rest ⟨s_a.r1, _, s_a.final⟩ rfl
    ⟨s_a', .step hint_d hstep_d hstar',
           by rw [heq_r1], heq_r2, by rw [heq_fin]⟩

private def lift_r2_internal_star [Inhabited T] [Inhabited (Fin n)]
    (s_a : DoubleIdealBCA.State T n)
    (t₂' : IdealBCA.State (IdealBCA.Val T) n)
    (hstar : InternalStar (IdealBCA.ideal_bca (IdealBCA.Val T) n f)
      (IdealBCA.ideal_labelling (IdealBCA.Val T) n) s_a.r2 t₂') :
    Σ' s_a', InternalStar (DoubleIdealBCA.doubleIdealBCA T n f)
      (DoubleIdealBCA.labelling T n) s_a s_a' ×'
      (s_a'.r1 = s_a.r1 ∧ s_a'.r2 = t₂' ∧ s_a'.final = s_a.final) :=
  lift_r2_internal_star_aux T n f hstar s_a rfl

/-! ## Cross-Round Invariant -/

/-- Concrete feed invariant: round 2 input tracks round 1 decision. -/
private theorem concrete_feed_inv
    (s : DoubleBCA_LTS.State T n)
    (hreach : Reachable (DoubleBCA_LTS.doubleBCA T n f) s) :
    DoubleBCA_LTS.feed_inv T n s := by
  induction hreach with
  | init hinit =>
    intro q mv hinp
    simp only at hinit
    have := hinit.1.2.1 q
    simp only [BCA_LTS.LocalState.init] at this
    rw [this] at hinp; simp at hinp
  | @step s l s' _ hstep ih =>
    intro q mv hinp
    match l with
    | .par cl =>
      have ⟨hps, _⟩ := hstep
      simp only [DoubleBCA_LTS.par_system, parallel] at hps
      match cl with
      | .left l₁ =>
        obtain ⟨hnosync, hs₁, heq2⟩ := hps
        have hinp' : (s.r2.local_ q).input = some mv := by rw [heq2] at hinp; exact hinp
        have hdec := ih q mv hinp'
        match l₁ with
        | .send .. => rw [BCA_LTS.send_decided hs₁]; exact hdec
        | .recv src dst t v =>
          have : (s'.r1.local_ q).decided = (s.r1.local_ q).decided := by
            cases t with
            | init => exact BCA_LTS.recv_init_decided hs₁ q
            | echo => exact BCA_LTS.recv_echo_decided hs₁ q
            | vote => exact BCA_LTS.recv_vote_decided hs₁ q
          rw [this]; exact hdec
        | .input .. => rw [BCA_LTS.input_decided hs₁]; exact hdec
        | .corrupt _ => exfalso; exact hnosync (.corrupt _) rfl
        | .output _ _ => exfalso; exact hnosync (.input _ _) ⟨rfl, rfl⟩
      | .right l₂ =>
        obtain ⟨hnosync, hs₂, heq1⟩ := hps
        rw [heq1]
        match l₂ with
        | .send .. => rw [BCA_LTS.send_input hs₂] at hinp; exact ih q mv hinp
        | .recv src dst t v =>
          have : (s'.r2.local_ q).input = (s.r2.local_ q).input := by
            cases t with
            | init => exact BCA_LTS.recv_init_input hs₂ q
            | echo => exact BCA_LTS.recv_echo_input hs₂ q
            | vote => exact BCA_LTS.recv_vote_input hs₂ q
          rw [this] at hinp; exact ih q mv hinp
        | .output .. => rw [BCA_LTS.output_input hs₂] at hinp; exact ih q mv hinp
        | .corrupt _ => exfalso; exact hnosync (.corrupt _) rfl
        | .input _ _ => exfalso; exact hnosync (.output _ _) ⟨rfl, rfl⟩
      | .sync l₁ l₂ =>
        obtain ⟨hsync, hs₁, hs₂⟩ := hps
        match l₁, l₂ with
        | .corrupt _, .corrupt _ =>
          obtain ⟨_, _, heq1⟩ := hs₁
          obtain ⟨_, _, heq2⟩ := hs₂
          have h1 : (s'.r1.local_ q).decided = (s.r1.local_ q).decided := by simp [heq1]
          have h2 : (s'.r2.local_ q).input = (s.r2.local_ q).input := by simp [heq2]
          rw [h1]; exact ih q mv (h2 ▸ hinp)
        | .output i₁ mv', .input i₂ _ =>
          obtain ⟨rfl, rfl⟩ := hsync
          by_cases hq : q = i₁
          · subst hq
            rw [BCA_LTS.input_input_self hs₂] at hinp
            rw [BCA_LTS.output_decided_self hs₁]; exact hinp
          · rw [BCA_LTS.input_input_other hs₂ q hq] at hinp
            rw [BCA_LTS.output_decided_other hs₁ q hq]; exact ih q mv hinp
        | .corrupt _, .send .. | .corrupt _, .recv ..
        | .corrupt _, .output .. | .corrupt _, .input ..
        | .send .., _ | .recv .., _ | .input .., _
        | .output _ _, .corrupt .. | .output _ _, .send ..
        | .output _ _, .recv .. | .output _ _, .output .. =>
          simp [DoubleBCA_LTS.sync_pred] at hsync
    | .output _ _ =>
      have ⟨_, _, _, heq1, heq2, _⟩ := hstep
      have h1 : (s'.r1.local_ q).decided = (s.r1.local_ q).decided := by rw [heq1]
      have h2 : (s'.r2.local_ q).input = (s.r2.local_ q).input := by rw [heq2]
      rw [h1]; exact ih q mv (h2 ▸ hinp)

/-- Corrupted lists agree between rounds at reachable states. -/
private theorem corrupted_eq
    (s : DoubleBCA_LTS.State T n)
    (hreach : Reachable (DoubleBCA_LTS.doubleBCA T n f) s) :
    s.r1.corrupted = s.r2.corrupted := by
  induction hreach with
  | init hinit =>
    simp only at hinit
    rw [hinit.1.1.2.2, hinit.1.2.2.2]
  | @step s l s' _ hstep ih =>
    match l with
    | .par cl =>
      have ⟨hps, _⟩ := hstep
      simp only [DoubleBCA_LTS.par_system, parallel] at hps
      match cl with
      | .left l₁ =>
        obtain ⟨hnosync, hs₁, heq2⟩ := hps
        match l₁ with
        | .send .. => rw [BCA_LTS.send_corrupted hs₁, heq2]; exact ih
        | .recv .. => rw [BCA_LTS.recv_corrupted hs₁, heq2]; exact ih
        | .input .. => rw [BCA_LTS.input_corrupted hs₁, heq2]; exact ih
        | .corrupt _ => exfalso; exact hnosync (.corrupt _) rfl
        | .output _ _ => exfalso; exact hnosync (.input _ _) ⟨rfl, rfl⟩
      | .right l₂ =>
        obtain ⟨hnosync, hs₂, heq1⟩ := hps
        match l₂ with
        | .send .. => rw [heq1, BCA_LTS.send_corrupted hs₂]; exact ih
        | .recv .. => rw [heq1, BCA_LTS.recv_corrupted hs₂]; exact ih
        | .output .. => rw [heq1, BCA_LTS.output_corrupted hs₂]; exact ih
        | .corrupt _ => exfalso; exact hnosync (.corrupt _) rfl
        | .input _ _ => exfalso; exact hnosync (.output _ _) ⟨rfl, rfl⟩
      | .sync l₁ l₂ =>
        obtain ⟨hsync, hs₁, hs₂⟩ := hps
        match l₁, l₂ with
        | .corrupt _, .corrupt _ =>
          rw [BCA_LTS.corrupt_eq hs₁, BCA_LTS.corrupt_eq hs₂]
          simp only [List.cons.injEq]; exact ⟨hsync, ih⟩
        | .output _ _, .input _ _ =>
          rw [BCA_LTS.output_corrupted hs₁, BCA_LTS.input_corrupted hs₂]; exact ih
        | .corrupt _, .send .. | .corrupt _, .recv ..
        | .corrupt _, .output .. | .corrupt _, .input ..
        | .send .., _ | .recv .., _ | .input .., _
        | .output _ _, .corrupt .. | .output _ _, .send ..
        | .output _ _, .recv .. | .output _ _, .output .. =>
          simp [DoubleBCA_LTS.sync_pred] at hsync
    | .output _ _ =>
      have ⟨_, _, _, heq1, heq2, _⟩ := hstep
      have h1 : s'.r1.corrupted = s.r1.corrupted := by rw [heq1]
      have h2 : s'.r2.corrupted = s.r2.corrupted := by rw [heq2]
      rw [h1, h2]; exact ih

/-- At reachable states, if decided q = some (some w), then echoSupport w ≥ threshold.
    Proof by induction on Reachable:
    - decided only changes on output steps
    - at the output step, countVoteRecv ≥ n-f → ∃ correct voter →
      voted_some_implies_echoSupport → echoSupport ≥ threshold
    - echoSupport is monotone across all steps (step_echoSupport_mono) -/
private theorem decided_implies_echoSupport
    (hn : n > 3 * f)
    (s : BCA_LTS.State T n)
    (hreach : Reachable (BCA_LTS.bca T n f) s)
    (q : Fin n) (w : T)
    (hdec : (s.local_ q).decided = some (some w)) :
    BCA_Simulation.echoSupport T n s w ≥ BCA_LTS.echoThreshold n f := by
  induction hreach with
  | init hinit =>
    obtain ⟨hlocal, _, _⟩ := hinit
    simp [hlocal q, BCA_LTS.LocalState.init] at hdec
  | @step s0 l s1 hreach0 hstep ih =>
    -- If decided q was already set in s0, use IH + monotonicity
    by_cases hdec0 : (s0.local_ q).decided = some (some w)
    · exact Nat.le_trans (ih hdec0)
        (BCA_Simulation.step_echoSupport_mono T n f hstep w)
    · -- decided q was NOT some (some w) in s0, so this step set it
      -- Only .output can change decided
      match l with
      | .send .. =>
        rw [BCA_LTS.send_decided hstep] at hdec; exact absurd hdec hdec0
      | .recv src dst t v =>
        have : (s1.local_ q).decided = (s0.local_ q).decided := by
          cases t with
          | init => exact BCA_LTS.recv_init_decided hstep q
          | echo => exact BCA_LTS.recv_echo_decided hstep q
          | vote => exact BCA_LTS.recv_vote_decided hstep q
        rw [this] at hdec; exact absurd hdec hdec0
      | .input .. =>
        rw [BCA_LTS.input_decided hstep] at hdec; exact absurd hdec hdec0
      | .corrupt _ =>
        obtain ⟨_, _, rfl⟩ := hstep; exact absurd hdec hdec0
      | .output i mv =>
        -- Must be q = i (other processes' decided unchanged)
        by_cases hqi : q = i
        · subst hqi
          -- mv = some w (from output_decided_self)
          have : mv = some w := by
            rw [BCA_LTS.output_decided_self hstep] at hdec
            exact Option.some.inj hdec
          subst this
          -- countVoteRecv (some w) ≥ returnThreshold in s0
          have hvotes : BCA_LTS.countVoteRecv T n (s0.local_ q) (some w) ≥
              BCA_LTS.returnThreshold n f := hstep.2.2.1
          -- Extract a correct voter via pigeonhole
          have hbudget := BCA_Simulation.corrupted_budget T n f hreach0
          have hlt : s0.corrupted.length <
              ((List.finRange n).filter
                (fun j => (s0.local_ q).voteRecv j (some w))).length := by
            simp only [BCA_LTS.countVoteRecv, BCA_LTS.returnThreshold] at hvotes
            omega
          obtain ⟨j, hj_recv, hj_corr⟩ :=
            pigeonhole_filter (fun j => (s0.local_ q).voteRecv j (some w))
              s0.corrupted hlt
          -- j is correct and q received vote(some w) from j
          -- By vote_trace: j actually voted (some w)
          have hj_voted := BCA_Simulation.vote_trace T n f hreach0 q j w
            (by simp only [BCA_LTS.isCorrect]; exact hj_corr) hj_recv
          -- By voted_some_implies_echoSupport: echoSupport w ≥ threshold at s0
          have hecho0 := BCA_Simulation.voted_some_implies_echoSupport T n f
            hreach0 j w (by simp only [BCA_LTS.isCorrect]; exact hj_corr) hj_voted
          -- By monotonicity: echoSupport w ≥ threshold at s1
          exact Nat.le_trans hecho0
            (BCA_Simulation.step_echoSupport_mono T n f hstep w)
        · -- q ≠ i: decided q unchanged
          rw [BCA_LTS.output_decided_other hstep q hqi] at hdec
          exact absurd hdec hdec0

private theorem decided_implies_bound
    (s_r : BCA_LTS.State T n) (s_i : IdealBCA.State T n)
    (hR : BCA_Simulation.sim_rel T n f s_r s_i)
    (hreach_i : Reachable (IdealBCA.ideal_bca T n f) s_i)
    (q : Fin n) (w : T)
    (hdec : (s_r.local_ q).decided = some (some w)) :
    s_i.bound_value = some w := by
  have hinv := IdealBCA.inv_reachable T n f s_i hreach_i
  have hdec_i := (hR.2.2.1 q).trans hdec
  exact hinv.1 q w hdec_i

private theorem approved_implies_r1_bound [Inhabited T] [Inhabited (Fin n)]
    (hn : n > 3 * f)
    (s_c : DoubleBCA_LTS.State T n) (s_a : DoubleIdealBCA.State T n)
    (hreach : Reachable (DoubleBCA_LTS.doubleBCA T n f) s_c)
    (hR₁ : BCA_Simulation.sim_rel T n f s_c.r1 s_a.r1)
    (hreach_a1 : Reachable (IdealBCA.ideal_bca T n f) s_a.r1)
    (i : Fin n)
    (hcorr : BCA_LTS.isCorrect T n s_c.r1 i)
    (w : T)
    (happroved : (s_c.r2.local_ i).approved (some w) = true) :
    s_a.r1.bound_value = some w := by
  -- Step 1: approved (some w) in round 2 → at least one correct process q
  -- has input (some (some w)) in round 2
  have hreach_r2 := reachable_r2 T n f s_c hreach
  -- Corrupted sets agree between rounds (from sim_rel)
  have hceq := corrupted_eq T n f s_c hreach
  have hcorr_r2 : BCA_LTS.isCorrect (BCA_LTS.Val T) n s_c.r2 i := by
    simp only [BCA_LTS.isCorrect] at hcorr ⊢
    rw [← hceq]; exact hcorr
  have hsup := BCA_Simulation.approval_implies_inputSupport (BCA_LTS.Val T) n f
    hreach_r2 hn i (some w) hcorr_r2 happroved
  have hbudget := BCA_Simulation.corrupted_budget (BCA_LTS.Val T) n f hreach_r2
  -- At least one correct process q has round 2 input = some (some w)
  have hpos : ((List.finRange n).filter (fun q =>
      decide (q ∉ s_c.r2.corrupted) &&
      decide ((s_c.r2.local_ q).input = some (some w)))).length > 0 := by omega
  obtain ⟨q, hq⟩ := List.exists_mem_of_length_pos hpos
  simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hq
  obtain ⟨_, hq_corr, hq_inp⟩ := hq
  -- Step 2: concrete feed invariant → round 1 decided q = some (some w)
  have hfeed := concrete_feed_inv T n f s_c hreach
  have hq_dec := hfeed q (some w) hq_inp
  -- Step 3: sim_rel + decided → bound_value = some w
  have hq_corr_r1 : BCA_LTS.isCorrect T n s_c.r1 q := by
    simp only [BCA_LTS.isCorrect] at hq_corr ⊢
    rw [hceq]; exact hq_corr
  exact decided_implies_bound T n f s_c.r1 s_a.r1 hR₁ hreach_a1 q w hq_dec

/-! ## Forward Simulation -/

/-- Forward simulation from the double concrete BCA to the double ideal BCA. -/
def double_forward_sim [Inhabited T] [Inhabited (Fin n)]
    (hn : n > 3 * f) :
    ForwardSim
      (DoubleBCA_LTS.doubleBCA T n f) (DoubleBCA_LTS.labelling T n)
      (DoubleIdealBCA.doubleIdealBCA T n f) (DoubleIdealBCA.labelling T n) where
  R := sim_rel T n f
  label_map := label_map T n
  init_sim := by
    intro s_c ⟨hpar, hfin⟩
    have ⟨t₁, ht₁_init, hR₁⟩ :=
      (BCA_Simulation.bca_forward_sim T n f hn).init_sim s_c.r1 hpar.1
    have ⟨t₂, ht₂_init, hR₂⟩ :=
      (BCA_Simulation.bca_forward_sim (BCA_LTS.Val T) n f hn).init_sim s_c.r2 hpar.2
    refine ⟨⟨t₁, t₂, fun _ => none⟩,
            ⟨⟨ht₁_init, ht₂_init⟩, fun p => rfl⟩,
            hR₁, hR₂, fun p => by simp [hfin p],
            .init ht₁_init, .init ht₂_init⟩
  step_internal := by
    intro s_c l s_c' s_a hreach ⟨hR₁, hR₂, hfin, hreach_a1, hreach_a2⟩ hint hstep
    simp only [DoubleBCA_LTS.labelling] at hint
    match l with
    | .par cl =>
      have ⟨hpar_step, hfeq⟩ := hstep
      simp only [DoubleBCA_LTS.par_system, parallel] at hpar_step
      match cl with
      -- Round 1 send/recv: BCA-internal → use round 1's step_internal + lift
      | .left (.send ..) | .left (.recv ..) =>
        have ⟨_, hs₁, heq2⟩ := hpar_step
        have ⟨t₁', hstar₁, hR₁'⟩ :=
          (BCA_Simulation.bca_forward_sim T n f hn).step_internal
            s_c.r1 _ s_c'.r1 s_a.r1 (reachable_r1 T n f s_c hreach) hR₁ rfl hs₁
        have ⟨s_a', hstar', heq_r1, heq_r2, heq_fin⟩ :=
          lift_r1_internal_star T n f s_a t₁' hstar₁
        exact ⟨s_a', hstar',
               heq_r1 ▸ hR₁', heq_r2 ▸ heq2 ▸ hR₂,
               ⟨fun p => by rw [hfeq, heq_fin]; exact hfin p,
                heq_r1 ▸ hstar₁.toStar.reachable hreach_a1,
                heq_r2 ▸ hreach_a2⟩⟩
      -- Round 2 send/recv: BCA-internal → use round 2's step_internal + lift
      | .right (.send ..) | .right (.recv ..) =>
        have ⟨_, hs₂, heq1⟩ := hpar_step
        have ⟨t₂', hstar₂, hR₂'⟩ :=
          (BCA_Simulation.bca_forward_sim (BCA_LTS.Val T) n f hn).step_internal
            s_c.r2 _ s_c'.r2 s_a.r2 (reachable_r2 T n f s_c hreach) hR₂ rfl hs₂
        have ⟨s_a', hstar', heq_r1, heq_r2, heq_fin⟩ :=
          lift_r2_internal_star T n f s_a t₂' hstar₂
        exact ⟨s_a', hstar',
               heq_r1 ▸ heq1 ▸ hR₁, heq_r2 ▸ hR₂',
               ⟨fun p => by rw [hfeq, heq_fin]; exact hfin p,
                heq_r1 ▸ hreach_a1,
                heq_r2 ▸ hstar₂.toStar.reachable hreach_a2⟩⟩
      -- Impossible .left cases: corrupt and output must sync
      | .left (.corrupt i) =>
        exfalso; exact hpar_step.1 (.corrupt i) rfl
      | .left (.output i mv) =>
        exfalso; exact hpar_step.1 (.input i mv) ⟨rfl, rfl⟩
      -- Impossible .right cases: corrupt and input must sync
      | .right (.corrupt j) =>
        exfalso; exact hpar_step.1 (.corrupt j) rfl
      | .right (.input j v) =>
        exfalso; exact hpar_step.1 (.output j v) ⟨rfl, rfl⟩
      -- Round 2 output: BCA-external but double-internal, use step_external + lift
      | .right (.output i₂ v₂) =>
        have ⟨_, hs₂, heq1⟩ := hpar_step
        -- Use round 2's step_external
        have ⟨t_mid, t_mid', t₂', hstar1, hstep_a, hstar2, hR₂'⟩ :=
          (BCA_Simulation.bca_forward_sim (BCA_LTS.Val T) n f hn).step_external
            s_c.r2 _ s_c'.r2 s_a.r2 (reachable_r2 T n f s_c hreach) hR₂ rfl hs₂
        -- Lift pre-internal star
        have ⟨s₁, hstar₁', _, heq_r2_1, heq_fin_1⟩ :=
          lift_r2_internal_star T n f s_a t_mid hstar1
        -- The abstract external step (.right (.output ...)) is internal in double labelling
        -- Wrap it as a single internal step in the double system
        let s₂ : DoubleIdealBCA.State T n := ⟨s₁.r1, t_mid', s₁.final⟩
        have hstep_d : (DoubleIdealBCA.doubleIdealBCA T n f).step
            s₁ (.par (.right (BCA_Simulation.label_map _ n (.output i₂ v₂)))) s₂ := by
          constructor
          · simp only [DoubleIdealBCA.par_system, parallel]
            refine ⟨?_, by rw [heq_r2_1]; exact hstep_a, rfl⟩
            intro l₁; simp [BCA_Simulation.label_map, DoubleIdealBCA.sync_pred]
          · rfl
        have hint_d : (DoubleIdealBCA.labelling T n).is_internal
            (.par (.right (BCA_Simulation.label_map _ n (.output i₂ v₂)))) = true := by
          simp [DoubleIdealBCA.labelling]
        -- Lift post-internal star
        have ⟨s₃, hstar₃', heq_r1_3, heq_r2_3, heq_fin_3⟩ :=
          lift_r2_internal_star T n f s₂ t₂' hstar2
        -- Concatenate: hstar₁' → hstep_d → hstar₃'
        have hstar_all : InternalStar (DoubleIdealBCA.doubleIdealBCA T n f)
            (DoubleIdealBCA.labelling T n) s_a s₃ := by
          exact InternalStar.trans hstar₁' (.step hint_d hstep_d hstar₃')
        have heq_r1_1 : s₁.r1 = s_a.r1 := by assumption
        have hreach_t₂' : Reachable (IdealBCA.ideal_bca (IdealBCA.Val T) n f) t₂' :=
          hstar2.toStar.reachable (.step (hstar1.toStar.reachable hreach_a2) hstep_a)
        exact ⟨s₃, hstar_all,
               heq_r1_3 ▸ heq_r1_1 ▸ heq1 ▸ hR₁, heq_r2_3 ▸ hR₂',
               ⟨fun p => by rw [hfeq, heq_fin_3, heq_fin_1]; exact hfin p,
                heq_r1_3 ▸ heq_r1_1 ▸ hreach_a1,
                heq_r2_3 ▸ hreach_t₂'⟩⟩
      -- Non-corrupt sync (output/input): double-internal
      | .sync (.output i₁ mv) (.input i₂ v₂) =>
        obtain ⟨hsync, hs₁, hs₂⟩ := hpar_step
        -- Call per-round step_external
        have ⟨t1m, t1m', t1', hstar1_pre, hstep1, hstar1_post, hR₁'⟩ :=
          (BCA_Simulation.bca_forward_sim T n f hn).step_external
            s_c.r1 _ s_c'.r1 s_a.r1 (reachable_r1 T n f s_c hreach) hR₁ rfl hs₁
        have ⟨t2m, t2m', t2', hstar2_pre, hstep2, hstar2_post, hR₂'⟩ :=
          (BCA_Simulation.bca_forward_sim (BCA_LTS.Val T) n f hn).step_external
            s_c.r2 _ s_c'.r2 s_a.r2 (reachable_r2 T n f s_c hreach) hR₂ rfl hs₂
        -- 1. Lift round 1 pre-internal*
        have ⟨sa₁, hpre₁, heq_r1_1, heq_r2_1, heq_fin_1⟩ :=
          lift_r1_internal_star T n f s_a t1m hstar1_pre
        -- 2. Lift round 2 pre-internal*
        have ⟨sa₂, hpre₂, heq_r1_2, heq_r2_2, heq_fin_2⟩ :=
          lift_r2_internal_star T n f sa₁ t2m (heq_r2_1 ▸ hstar2_pre)
        -- 3. Sync step (internal in double labelling)
        let sa₃ : DoubleIdealBCA.State T n := ⟨t1m', t2m', sa₂.final⟩
        have hstep1' : (IdealBCA.ideal_bca T n f).step sa₂.r1
            (BCA_Simulation.label_map T n (.output i₁ mv)) t1m' := by
          rw [heq_r1_2, heq_r1_1]; exact hstep1
        have hstep2' : (IdealBCA.ideal_bca (IdealBCA.Val T) n f).step sa₂.r2
            (BCA_Simulation.label_map (BCA_LTS.Val T) n (.input i₂ v₂)) t2m' := by
          rw [heq_r2_2]; exact hstep2
        have hsync' : DoubleIdealBCA.sync_pred T n
            (BCA_Simulation.label_map T n (.output i₁ mv))
            (BCA_Simulation.label_map (BCA_LTS.Val T) n (.input i₂ v₂)) := by
          simp only [DoubleIdealBCA.sync_pred, BCA_Simulation.label_map]; exact hsync
        have hstep_sync : (DoubleIdealBCA.doubleIdealBCA T n f).step sa₂
            (.par (.sync (BCA_Simulation.label_map T n (.output i₁ mv))
                         (BCA_Simulation.label_map (BCA_LTS.Val T) n (.input i₂ v₂)))) sa₃ := by
          constructor
          · simp only [DoubleIdealBCA.par_system, parallel]
            exact ⟨hsync', hstep1', hstep2'⟩
          · rfl
        have hint_sync : (DoubleIdealBCA.labelling T n).is_internal
            (.par (.sync (BCA_Simulation.label_map T n (.output i₁ mv))
                         (BCA_Simulation.label_map (BCA_LTS.Val T) n (.input i₂ v₂)))) = true := by
          simp [DoubleIdealBCA.labelling, BCA_Simulation.label_map]
        -- 4. Lift round 1 post-internal*
        have ⟨sa₄, hpost₁, heq_r1_4, heq_r2_4, heq_fin_4⟩ :=
          lift_r1_internal_star T n f sa₃ t1' hstar1_post
        -- 5. Lift round 2 post-internal*
        have ⟨sa₅, hpost₂, heq_r1_5, heq_r2_5, heq_fin_5⟩ :=
          lift_r2_internal_star T n f sa₄ t2' (heq_r2_4 ▸ hstar2_post)
        -- Concatenate into one InternalStar
        have hstar_all : InternalStar (DoubleIdealBCA.doubleIdealBCA T n f)
            (DoubleIdealBCA.labelling T n) s_a sa₅ :=
          (hpre₁.trans hpre₂).trans (.step hint_sync hstep_sync (hpost₁.trans hpost₂))
        have hreach_t1' : Reachable (IdealBCA.ideal_bca T n f) t1' :=
          hstar1_post.toStar.reachable (.step (hstar1_pre.toStar.reachable hreach_a1) hstep1)
        have hreach_t2' : Reachable (IdealBCA.ideal_bca (IdealBCA.Val T) n f) t2' :=
          hstar2_post.toStar.reachable (.step (hstar2_pre.toStar.reachable hreach_a2) hstep2)
        exact ⟨sa₅, hstar_all,
               heq_r1_5 ▸ heq_r1_4 ▸ hR₁', heq_r2_5 ▸ hR₂',
               ⟨fun p => by rw [hfeq, heq_fin_5, heq_fin_4, heq_fin_2, heq_fin_1]; exact hfin p,
                heq_r1_5 ▸ heq_r1_4 ▸ hreach_t1',
                heq_r2_5 ▸ hreach_t2'⟩⟩
      -- Impossible sync combinations (sync_pred = False)
      | .sync (.corrupt _) (.send ..) | .sync (.corrupt _) (.recv ..)
      | .sync (.corrupt _) (.output ..) | .sync (.corrupt _) (.input ..)
      | .sync (.send ..) _ | .sync (.recv ..) _ | .sync (.input ..) _
      | .sync (.output _ _) (.corrupt ..) | .sync (.output _ _) (.send ..)
      | .sync (.output _ _) (.recv ..) | .sync (.output _ _) (.output ..) =>
        exfalso; simp [DoubleBCA_LTS.sync_pred] at hpar_step
      -- Corrupt sync is external, contradiction
      | .sync (.corrupt _) (.corrupt _) =>
        exact absurd hint (by simp)
    | .output _ _ =>
      -- .output is external in DoubleBCA, contradiction
      exact absurd hint (by simp)
  step_external := by
    intro s_c l s_c' s_a hreach ⟨hR₁, hR₂, hfin, hreach_a1, hreach_a2⟩ hext hstep
    simp only [DoubleBCA_LTS.labelling, Labelling.is_external] at hext
    match l with
    | .par cl =>
      match cl with
      | .left (.input i v) =>
        -- Round 1 input: BCA-external, use round 1's step_external + lift
        have ⟨hpar_step, hfeq⟩ := hstep
        simp only [DoubleBCA_LTS.par_system, parallel] at hpar_step
        obtain ⟨_, hs₁, heq2⟩ := hpar_step
        have ⟨t_mid, t_mid', t₁', hstar1, hstep_a, hstar2, hR₁'⟩ :=
          (BCA_Simulation.bca_forward_sim T n f hn).step_external
            s_c.r1 _ s_c'.r1 s_a.r1 (reachable_r1 T n f s_c hreach) hR₁ rfl hs₁
        -- Lift pre-internal star (round 1)
        have ⟨sa₁, hstar₁', _, heq_r2_1, heq_fin_1⟩ :=
          lift_r1_internal_star T n f s_a t_mid hstar1
        -- The external step: .par (.left (.input ...)) which maps to .par (.left (.input ...))
        have heq_r1_1 : sa₁.r1 = t_mid := by assumption
        let sa₂ : DoubleIdealBCA.State T n := ⟨t_mid', sa₁.r2, sa₁.final⟩
        have hstep_d : (DoubleIdealBCA.doubleIdealBCA T n f).step
            sa₁ (.par (.left (BCA_Simulation.label_map T n (.input i v)))) sa₂ := by
          constructor
          · simp only [DoubleIdealBCA.par_system, parallel]
            refine ⟨?_, by rw [heq_r1_1]; exact hstep_a, rfl⟩
            intro l₂; simp [BCA_Simulation.label_map, DoubleIdealBCA.sync_pred]
          · rfl
        -- Lift post-internal star (round 1)
        have ⟨sa₃, hstar₃', heq_r1_3, heq_r2_3, heq_fin_3⟩ :=
          lift_r1_internal_star T n f sa₂ t₁' hstar2
        have hreach_t₁' : Reachable (IdealBCA.ideal_bca T n f) t₁' :=
          hstar2.toStar.reachable (.step (hstar1.toStar.reachable hreach_a1) hstep_a)
        exact ⟨sa₁, sa₂, sa₃,
               hstar₁', hstep_d, hstar₃',
               heq_r1_3 ▸ hR₁',
               heq_r2_3 ▸ heq_r2_1 ▸ heq2 ▸ hR₂,
               ⟨fun p => by rw [hfeq, heq_fin_3, heq_fin_1]; exact hfin p,
                heq_r1_3 ▸ hreach_t₁',
                heq_r2_3 ▸ heq_r2_1 ▸ hreach_a2⟩⟩
      | .sync (.corrupt i₁) (.corrupt i₂) =>
        -- Corruption sync: external, use both rounds' step_external
        have ⟨hpar_step, hfeq⟩ := hstep
        simp only [DoubleBCA_LTS.par_system, parallel] at hpar_step
        obtain ⟨hsync, hs₁, hs₂⟩ := hpar_step
        -- Call per-round step_external
        have ⟨t1m, t1m', t1', hstar1_pre, hstep1, hstar1_post, hR₁'⟩ :=
          (BCA_Simulation.bca_forward_sim T n f hn).step_external
            s_c.r1 _ s_c'.r1 s_a.r1 (reachable_r1 T n f s_c hreach) hR₁ rfl hs₁
        have ⟨t2m, t2m', t2', hstar2_pre, hstep2, hstar2_post, hR₂'⟩ :=
          (BCA_Simulation.bca_forward_sim (BCA_LTS.Val T) n f hn).step_external
            s_c.r2 _ s_c'.r2 s_a.r2 (reachable_r2 T n f s_c hreach) hR₂ rfl hs₂
        -- Pre-internal*: lift round 1, then round 2
        have ⟨sa₁, hpre₁, heq_r1_1, heq_r2_1, heq_fin_1⟩ :=
          lift_r1_internal_star T n f s_a t1m hstar1_pre
        have ⟨sa₂, hpre₂, heq_r1_2, heq_r2_2, heq_fin_2⟩ :=
          lift_r2_internal_star T n f sa₁ t2m (heq_r2_1 ▸ hstar2_pre)
        -- External sync step at (t1m, t2m)
        let sa₃ : DoubleIdealBCA.State T n := ⟨t1m', t2m', sa₂.final⟩
        have heq_r1_sa1 : sa₁.r1 = t1m := by assumption
        have hstep1' : (IdealBCA.ideal_bca T n f).step sa₂.r1 (.corrupt i₁) t1m' := by
          rw [heq_r1_2, heq_r1_sa1]
          exact hstep1
        have hstep2' : (IdealBCA.ideal_bca (IdealBCA.Val T) n f).step sa₂.r2
          (.corrupt i₂) t2m' := by
          rw [heq_r2_2]
          exact hstep2
        have hstep_d : (DoubleIdealBCA.doubleIdealBCA T n f).step sa₂
            (.par (.sync (.corrupt i₁) (.corrupt i₂))) sa₃ := by
          constructor
          · simp only [DoubleIdealBCA.par_system, parallel]
            exact ⟨hsync, hstep1', hstep2'⟩
          · rfl
        -- Post-internal*: lift round 1, then round 2
        have ⟨sa₄, hpost₁, heq_r1_4, heq_r2_4, heq_fin_4⟩ :=
          lift_r1_internal_star T n f sa₃ t1' hstar1_post
        have ⟨sa₅, hpost₂, heq_r1_5, heq_r2_5, heq_fin_5⟩ :=
          lift_r2_internal_star T n f sa₄ t2' (heq_r2_4 ▸ hstar2_post)
        -- Assemble: pre* → sync → post*
        exact ⟨sa₂, sa₃, sa₅,
               hpre₁.trans hpre₂,
               hstep_d,
               hpost₁.trans hpost₂,
               heq_r1_5 ▸ heq_r1_4 ▸ hR₁',
               heq_r2_5 ▸ hR₂',
               ⟨fun p => by
                rw [hfeq, heq_fin_5, heq_fin_4, heq_fin_2, heq_fin_1]
                exact hfin p,
                heq_r1_5 ▸ heq_r1_4 ▸
                  (hstar1_post.toStar.reachable
                  (.step (hstar1_pre.toStar.reachable hreach_a1) hstep1)),
                heq_r2_5 ▸
                  (hstar2_post.toStar.reachable
                  (.step (hstar2_pre.toStar.reachable hreach_a2) hstep2))⟩⟩
      | .left (.send ..) | .left (.recv ..) | .left (.corrupt _)
      | .left (.output _ _)
      | .right _
      | .sync (.output _ _) (.input _ _) =>
        -- Internal in double system, contradiction
        exact absurd hext (by simp)
      -- Impossible sync combinations
      | .sync (.corrupt _) (.send ..) | .sync (.corrupt _) (.recv ..)
      | .sync (.corrupt _) (.output ..) | .sync (.corrupt _) (.input ..)
      | .sync (.send ..) _ | .sync (.recv ..) _ | .sync (.input ..) _
      | .sync (.output _ _) (.corrupt ..) | .sync (.output _ _) (.send ..)
      | .sync (.output _ _) (.recv ..) | .sync (.output _ _) (.output ..) =>
        exact absurd hext (by simp)
    | .output i v =>
      -- Composite output: match one-to-one with abstract output
      have ⟨hcorr_c, hfin_none, hguard, heq1, heq2, hfeq⟩ := hstep
      -- Abstract side: construct the matching output step
      -- sim_rel gives us: s_a.r2.decided i = (s_c.r2.local_ i).decided
      have hdec_eq := hR₂.2.2.1 i
      -- s_a correctness from sim_rel (corrupted lists agree)
      have hcorr_a : IdealBCA.isCorrect T n s_a.r1 i := by
        simp only [IdealBCA.isCorrect, BCA_LTS.isCorrect] at hcorr_c ⊢
        rw [hR₁.1]; exact hcorr_c
      -- s_a.final i = none (from sim_rel + concrete final = none)
      have hfin_a_none : s_a.final i = none := by
        rw [hfin i, hfin_none]; rfl
      -- Case split on the concrete output value
      match v with
      | .valA w =>
        -- r2.decided i = some (some (some w)) in concrete
        -- sim_rel gives same in abstract
        have hd : (s_c.r2.local_ i).decided = some (some (some w)) := by
          match hd : (s_c.r2.local_ i).decided with
          | some (some (some w')) =>
            simp only [hd, DoubleBCA_LTS.FinalVal.valA.injEq] at hguard; subst hguard; rfl
          | some (some none) => simp [hd] at hguard
          | some none => simp [hd] at hguard
          | none => simp [hd] at hguard
        let s_a' : DoubleIdealBCA.State T n :=
          ⟨s_a.r1, s_a.r2, fun p => if p = i then some (.valA w) else s_a.final p⟩
        refine ⟨s_a, s_a', s_a', InternalStar.refl, ?_, InternalStar.refl, ?_⟩
        · -- Abstract step
          refine ⟨hcorr_a, hfin_a_none, ?_, rfl, rfl, rfl⟩
          rw [hdec_eq, hd]; rfl
        · -- sim_rel preserved
          refine ⟨by rw [heq1]; exact hR₁, by rw [heq2]; exact hR₂, ?_, hreach_a1, hreach_a2⟩
          intro p
          change (if p = i then some (.valA w) else s_a.final p) = _
          rw [hfeq]
          by_cases hp : p = i
          · subst hp; simp [map_fv]
          · simp [hp, hfin p]
      | .bot =>
        have hd : (s_c.r2.local_ i).decided = some (some none) := by
          match hd : (s_c.r2.local_ i).decided with
          | some (some none) => rfl
          | some (some (some _)) => simp [hd] at hguard
          | some none => simp [hd] at hguard
          | none => simp [hd] at hguard
        let s_a' : DoubleIdealBCA.State T n :=
          ⟨s_a.r1, s_a.r2, fun p => if p = i then some .bot else s_a.final p⟩
        refine ⟨s_a, s_a', s_a', InternalStar.refl, ?_, InternalStar.refl, ?_⟩
        · change IdealBCA.isCorrect T n s_a.r1 i ∧ _
          refine ⟨hcorr_a, hfin_a_none, ?_, rfl, rfl, rfl⟩
          rw [hdec_eq, hd]; rfl
        · refine ⟨by rw [heq1]; exact hR₁, by rw [heq2]; exact hR₂, ?_, hreach_a1, hreach_a2⟩
          intro p
          change (if p = i then some .bot else s_a.final p) = _
          rw [hfeq]
          by_cases hp : p = i
          · subst hp; simp [map_fv]
          · simp [hp, hfin p]
      | .valB w =>
        -- Round 2 decided ⊥, process approved (some w) in round 2
        have hd : (s_c.r2.local_ i).decided = some none := by
          match hd : (s_c.r2.local_ i).decided with
          | some none => rfl
          | some (some (some _)) => simp [hd] at hguard
          | some (some none) => simp [hd] at hguard
          | none => simp [hd] at hguard
        have happr : (s_c.r2.local_ i).approved (some w) = true := by
          have hguard' := hguard; rw [hd] at hguard'
          obtain ⟨w', happr, hveq⟩ := hguard'
          injection hveq with hveq; subst hveq; exact happr
        -- Use cross-round invariant to get r1.bound_value = some w
        have hbv := approved_implies_r1_bound T n f hn s_c s_a hreach hR₁
          hreach_a1 i hcorr_c w happr
        let s_a' : DoubleIdealBCA.State T n :=
          ⟨s_a.r1, s_a.r2, fun p => if p = i then some (.valB w) else s_a.final p⟩
        refine ⟨s_a, s_a', s_a', InternalStar.refl, ?_, InternalStar.refl, ?_⟩
        · -- Abstract output step
          refine ⟨hcorr_a, hfin_a_none, ?_, rfl, rfl, rfl⟩
          rw [hdec_eq, hd]
          exact ⟨w, hbv, rfl⟩
        · -- sim_rel preserved
          refine ⟨by rw [heq1]; exact hR₁, by rw [heq2]; exact hR₂, ?_, hreach_a1, hreach_a2⟩
          intro p
          change (if p = i then some (.valB w) else s_a.final p) = _
          rw [hfeq]
          by_cases hp : p = i
          · subst hp; simp [map_fv]
          · simp [hp, hfin p]

/-! ## Lifted Properties -/

/-- From `binding_inv`, derive `graded_agreement` at the abstract state. -/
private theorem abstract_graded_agreement
    (s_a : DoubleIdealBCA.State T n)
    (hinv : DoubleIdealBCA.binding_inv T n f s_a) :
    DoubleIdealBCA.graded_agreement T n s_a := by
  obtain ⟨hcons, hinv1, hinv2, hfeed⟩ := hinv
  -- Helpers (same as in graded_agreement_invariant)
  have valA_dec := fun p v (hfp : s_a.final p = some (.valA v)) =>
    by have hoc := hcons p; simp only [hfp] at hoc; exact hoc
  have bot_dec := fun p (hfp : s_a.final p = some .bot) =>
    by have hoc := hcons p; simp only [hfp] at hoc; exact hoc
  have valB_dec := fun p w (hfp : s_a.final p = some (.valB w)) => by
    have hoc := hcons p; simp only [hfp] at hoc
    exact (hoc : s_a.r2.decided p = some none ∧ s_a.r1.bound_value = some w)
  have valA_bound := fun p v (hfp : s_a.final p = some (.valA v)) =>
    hinv2.1 p (some v) (valA_dec p v hfp)
  have bot_bound := fun p (hfp : s_a.final p = some .bot) =>
    hinv2.1 p none (bot_dec p hfp)
  have valA_valB_agree : ∀ p q v w,
      s_a.final p = some (.valA v) → s_a.final q = some (.valB w) → v = w := by
    intro p q v w hfp hfq
    have hbv2 := valA_bound p v hfp
    have hsup := hinv2.2.2.1 (some v) hbv2
    have hpos : IdealBCA.inputSupport (IdealBCA.Val T) n s_a.r2 (some v) > 0 := by
      have := hinv2.2.2.2.1; omega
    simp only [IdealBCA.inputSupport] at hpos
    obtain ⟨r, hr⟩ := List.exists_mem_of_length_pos hpos
    simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hr
    have hbv1 := hinv1.1 r v (hfeed r (some v) hr.2.2)
    have hbv1' := (valB_dec q w hfq).2
    rw [hbv1] at hbv1'; exact Option.some.inj hbv1'
  refine ⟨?_, ?_, ?_⟩
  · intro p q v w _ _ hfpv hfqw
    rcases hfpv with hfp | hfp <;> rcases hfqw with hfq | hfq
    · have hbv := valA_bound p v hfp; have hbw := valA_bound q w hfq
      rw [hbv] at hbw; simp only [Option.some.injEq] at hbw; exact hbw
    · exact valA_valB_agree p q v w hfp hfq
    · exact (valA_valB_agree q p w v hfq hfp).symm
    · have h1 := (valB_dec p v hfp).2; have h2 := (valB_dec q w hfq).2
      rw [h1] at h2; simp only [Option.some.injEq] at h2; exact h2
  · intro p q v _ _ hfp hfq
    have hbv := valA_bound p v hfp; have hbot := bot_bound q hfq
    rw [hbv] at hbot; simp at hbot
  · intro p q v _ _ hfp hfq
    have hbot := bot_bound p hfp; have hbv := valA_bound q v hfq
    rw [hbot] at hbv; simp at hbv

/-- From `binding_inv`, derive `double_validity` at the abstract state. -/
private theorem abstract_double_validity (v : T)
    (s_a : DoubleIdealBCA.State T n)
    (hinv : DoubleIdealBCA.binding_inv T n f s_a) :
    DoubleIdealBCA.double_validity T n v s_a := by
  obtain ⟨hcons, hinv1, hinv2, hfeed⟩ := hinv
  have hval1 := IdealBCA.inv_implies_validity T n f v s_a.r1 hinv1
  have hval2 := IdealBCA.inv_implies_validity _ n f (some v) s_a.r2 hinv2
  intro hpre p hcorr
  have hr2_pre : ∀ q, ¬IdealBCA.isCorrect (IdealBCA.Val T) n s_a.r2 q ∨
      s_a.r2.input_ q = none ∨ s_a.r2.input_ q = some (some v) := by
    intro q
    match hinq : s_a.r2.input_ q with
    | none => right; left; rfl
    | some mv =>
      have hdec := hfeed q mv hinq
      rcases hval1 hpre q with h | h
      · rw [h] at hdec; simp at hdec
      · right; right; rw [← hdec]; exact h
  rcases hval2 hr2_pre p with h | h
  · have hoc := hcons p
    match hfp : s_a.final p with
    | none => left; rfl
    | some (.valA w) => simp only [hfp] at hoc; rw [h] at hoc; simp at hoc
    | some .bot => simp only [hfp] at hoc; rw [h] at hoc; simp at hoc
    | some (.valB w) => simp only [hfp] at hoc; rw [h] at hoc; simp at hoc
  · have hoc := hcons p
    match hfp : s_a.final p with
    | none => left; rfl
    | some (.valA w) =>
      right; simp only [hfp] at hoc; rw [h] at hoc; simp at hoc
      congr 1; congr 1; exact hoc.symm
    | some .bot => simp only [hfp] at hoc; rw [h] at hoc; simp at hoc
    | some (.valB w) => simp only [hfp] at hoc; rw [h] at hoc; simp at hoc

omit [DecidableEq T] in
/-- Helper: map concrete final to abstract final. -/
theorem map_final
    {s_c : DoubleBCA_LTS.State T n} {s_a : DoubleIdealBCA.State T n}
    (hfin : ∀ p, s_a.final p = (s_c.final p).map (map_fv T))
    (p : Fin n) (fv : DoubleBCA_LTS.FinalVal T) (h : s_c.final p = some fv) :
    s_a.final p = some (map_fv T fv) := by rw [hfin, h]; rfl

/-- Transfer sim_rel + abstract graded_agreement → concrete graded_agreement. -/
private theorem transfer_graded_agreement
    (s_c : DoubleBCA_LTS.State T n) (s_a : DoubleIdealBCA.State T n)
    (hR₁ : BCA_Simulation.sim_rel T n f s_c.r1 s_a.r1)
    (hfin : ∀ p, s_a.final p = (s_c.final p).map (map_fv T))
    (ha : DoubleIdealBCA.graded_agreement T n s_a) :
    DoubleBCA_LTS.graded_agreement T n s_c := by
  obtain ⟨hagree, hcompat1, hcompat2⟩ := ha
  have hcorr_iff : ∀ p, BCA_LTS.isCorrect T n s_c.r1 p ↔
      IdealBCA.isCorrect T n s_a.r1 p := by
    intro p; simp [BCA_LTS.isCorrect, IdealBCA.isCorrect, hR₁.1]
  refine ⟨?_, ?_, ?_⟩
  · intro p q v w hcp hcq hfpv hfqw
    have hfpv_a : s_a.final p = some (.valA v) ∨ s_a.final p = some (.valB v) :=
      hfpv.imp (map_final T n hfin p _) (map_final T n hfin p _)
    have hfqw_a : s_a.final q = some (.valA w) ∨ s_a.final q = some (.valB w) :=
      hfqw.imp (map_final T n hfin q _) (map_final T n hfin q _)
    exact hagree p q v w ((hcorr_iff p).mp hcp) ((hcorr_iff q).mp hcq) hfpv_a hfqw_a
  · intro p q v hcp hcq hfp hfq
    exact absurd (map_final T n hfin q _ hfq)
      (hcompat1 p q v ((hcorr_iff p).mp hcp) ((hcorr_iff q).mp hcq) (map_final T n hfin p _ hfp))
  · intro p q v hcp hcq hfp hfq
    exact absurd (map_final T n hfin q _ hfq)
      (hcompat2 p q v ((hcorr_iff p).mp hcp) ((hcorr_iff q).mp hcq) (map_final T n hfin p _ hfp))

/-- Transfer sim_rel + abstract double_validity → concrete double_validity. -/
private theorem transfer_double_validity (v : T)
    (s_c : DoubleBCA_LTS.State T n) (s_a : DoubleIdealBCA.State T n)
    (hR₁ : BCA_Simulation.sim_rel T n f s_c.r1 s_a.r1)
    (hfin : ∀ p, s_a.final p = (s_c.final p).map (map_fv T))
    (ha : DoubleIdealBCA.double_validity T n v s_a) :
    DoubleBCA_LTS.double_validity T n v s_c := by
  intro hpre p hcp
  have hpre_a : ∀ q, ¬IdealBCA.isCorrect T n s_a.r1 q ∨
      s_a.r1.input_ q = none ∨ s_a.r1.input_ q = some v := by
    intro q
    rcases hpre q with h | h | h
    · left; simp only [BCA_LTS.isCorrect, Decidable.not_not, IdealBCA.isCorrect, hR₁.1] at h ⊢
      exact h
    · right; left; rw [hR₁.2.1]; exact h
    · right; right; rw [hR₁.2.1]; exact h
  have hcp_a : IdealBCA.isCorrect T n s_a.r1 p := by
    simp only [BCA_LTS.isCorrect, IdealBCA.isCorrect, hR₁.1] at hcp ⊢; exact hcp
  rcases ha hpre_a p hcp_a with h | h
  · -- abstract final = none → concrete final = none
    left; have := hfin p; rw [h] at this
    cases hf : s_c.final p with
    | none => rfl
    | some _ => simp [hf] at this
  · -- abstract final = valA v → concrete final = valA v
    right
    have := hfin p; rw [h] at this
    cases hf : s_c.final p with
    | none => simp [hf] at this
    | some fv =>
      simp only [hf, Option.map_some, map_fv, Option.some.injEq] at this
      match fv with
      | .valA w => simp only [DoubleIdealBCA.FinalVal.valA.injEq] at this; rw [this]
      | .bot => simp at this
      | .valB _ => simp at this

theorem real_graded_agreement [Inhabited T] [Inhabited (Fin n)] (hn : n > 3 * f) :
    (DoubleBCA_LTS.doubleBCA T n f).satisfies
      [ltl| □ ⌜ DoubleBCA_LTS.graded_agreement T n ⌝] :=
  (double_forward_sim T n f hn).preserves_invariant
    (DoubleIdealBCA.binding_inv T n f)
    (DoubleIdealBCA.binding_inv_init T n f)
    (DoubleIdealBCA.binding_inv_step T n f)
    (DoubleBCA_LTS.graded_agreement T n)
    (fun s_c s_a ⟨hR₁, _, hfin, _, _⟩ hinv =>
      transfer_graded_agreement T n f s_c s_a hR₁ hfin
        (abstract_graded_agreement T n f s_a hinv))

theorem real_double_validity [Inhabited T] [Inhabited (Fin n)] (hn : n > 3 * f) (v : T) :
    (DoubleBCA_LTS.doubleBCA T n f).satisfies
      [ltl| □ ⌜ DoubleBCA_LTS.double_validity T n v ⌝] :=
  (double_forward_sim T n f hn).preserves_invariant
    (DoubleIdealBCA.binding_inv T n f)
    (DoubleIdealBCA.binding_inv_init T n f)
    (DoubleIdealBCA.binding_inv_step T n f)
    (DoubleBCA_LTS.double_validity T n v)
    (fun s_c s_a ⟨hR₁, _, hfin, _, _⟩ hinv =>
      transfer_double_validity T n f v s_c s_a hR₁ hfin
        (abstract_double_validity T n f v s_a hinv))

theorem real_double_binding [Inhabited T] [Inhabited (Fin n)] (hn : n > 3 * f) :
    DoubleBCA_LTS.double_binding T n f :=
  (double_forward_sim T n f hn).preserves_branching
    (W := T)
    (P_guard := fun s_a => ∃ p fv, IdealBCA.isCorrect T n s_a.r1 p ∧
      s_a.final p = some fv)
    (P_concl := fun v s_a => ∀ q fv, IdealBCA.isCorrect T n s_a.r1 q →
      s_a.final q = some fv →
      fv = .bot ∨ fv = .valA v ∨ fv = .valB v)
    (Q_guard := fun s_c => ∃ p fv, BCA_LTS.isCorrect T n s_c.r1 p ∧
      s_c.final p = some fv)
    (Q_concl := fun v s_c => ∀ q fv, BCA_LTS.isCorrect T n s_c.r1 q →
      s_c.final q = some fv →
      fv = .bot ∨ fv = .valA v ∨ fv = .valB v)
    (DoubleIdealBCA.double_binding_holds T n f)
    (by -- guard transfer: Q_guard s_c → P_guard s_a
      intro s_c s_a ⟨hR₁, _, hfin, _, _⟩ ⟨p, fv, hcp, hfp⟩
      exact ⟨p, map_fv T fv,
        by simp only [BCA_LTS.isCorrect, IdealBCA.isCorrect, hR₁.1] at hcp ⊢; exact hcp,
        map_final T n hfin p fv hfp⟩)
    (by -- conclusion transfer: P_concl v s_a → Q_concl v s_c
      intro v s_c s_a ⟨hR₁, _, hfin, _, _⟩ hconcl q fv hcq hfq
      have hcq_a : IdealBCA.isCorrect T n s_a.r1 q := by
        simp only [BCA_LTS.isCorrect, IdealBCA.isCorrect, hR₁.1] at hcq ⊢; exact hcq
      have hfq_a := map_final T n hfin q fv hfq
      have habst := hconcl q (map_fv T fv) hcq_a hfq_a
      match fv with
      | .bot => left; rfl
      | .valA w => simp only [map_fv, reduceCtorEq, DoubleIdealBCA.FinalVal.valA.injEq, or_false,
        false_or] at habst; right; left; rw [habst]
      | .valB w => simp only [map_fv, reduceCtorEq, DoubleIdealBCA.FinalVal.valB.injEq,
        false_or] at habst; right; right; rw [habst])

end DoubleBCA_Simulation
