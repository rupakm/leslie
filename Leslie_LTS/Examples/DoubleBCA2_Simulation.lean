import Leslie_LTS.Examples.DoubleBCA2
import Leslie_LTS.Examples.DoubleIdealBCA2
import Leslie_LTS.Examples.BCA_Simulation

/-! # Forward Simulation: DoubleBCA2 → DoubleIdealBCA2

    Uses `parallel_forward_sim` at two levels:

    1. **Inner level**: `parallel_forward_sim bca_sim₁ bca_sim₂` lifts
       per-round BCA simulations to `par_bca ≲ par_ideal`

    2. **Inner wrapper**: extend the inner simulation to handle the
       `readyToOutput` stutter label (via sim_rel on the wrapper)

    3. **Outer level**: `parallel_forward_sim inner_sim id_sim` composes
       the inner simulation with identity on `outputCtrl`

    Side conditions (sync compatibility, label map properties) are
    straightforward case analyses on the sync predicates and label maps.
-/

open LTS

namespace DoubleBCA2_Simulation

variable (T : Type) [DecidableEq T] (n f : Nat)

/-! ## FinalVal Mapping -/

def map_fv : DoubleBCA2.FinalVal T → DoubleIdealBCA2.FinalVal T
  | .bot => .bot
  | .valA v => .valA v
  | .valB v => .valB v

/-! ## Step 1: Inner Parallel Simulation (raw parallel)

    `parallel bca₁ bca₂ ≲ parallel ideal₁ ideal₂`
    via `parallel_forward_sim`. -/

def inner_par_sim [Inhabited T] [Inhabited (Fin n)] (hn : n > 3 * f) :
    ForwardSim
      (DoubleBCA2.par_bca T n f)
      (parallel_labelling (BCA_LTS.bca_labelling T n)
        (BCA_LTS.bca_labelling (BCA_LTS.Val T) n))
      (DoubleIdealBCA2.par_ideal T n f)
      (parallel_labelling (IdealBCA.ideal_labelling T n)
        (IdealBCA.ideal_labelling (IdealBCA.Val T) n)) :=
  parallel_forward_sim
    (BCA_Simulation.bca_forward_sim T n f hn)
    (BCA_Simulation.bca_forward_sim (BCA_LTS.Val T) n f hn)
    (hsync := by
      intro la lb hsyn
      match la, lb, hsyn with
      | .corrupt _, .corrupt _, h => exact h
      | .output _ _, .input _ _, h => exact h)
    (hnosync_left := by
      intro la hnosyn lb₂
      match la with
      | .corrupt i => exact absurd rfl (hnosyn (.corrupt i))
      | .output i v => exact absurd ⟨rfl, rfl⟩ (hnosyn (.input i v))
      | .input _ _ | .send .. | .recv .. =>
        match lb₂ with | .corrupt _ | .input _ _ | .output _ _ | .bind _ => exact id)
    (hnosync_right := by
      intro lb hnosyn la₂
      match lb with
      | .corrupt i => exact absurd rfl (hnosyn (.corrupt i))
      | .input i v => exact absurd ⟨rfl, rfl⟩ (hnosyn (.output i v))
      | .output _ _ | .send .. | .recv .. =>
        match la₂ with | .corrupt _ | .input _ _ | .output _ _ | .bind _ => exact id)
    (hsync_ext := by
      intro la lb hsyn
      match la, lb, hsyn with
      | .corrupt _, .corrupt _, _ => exact ⟨rfl, rfl⟩
      | .output _ _, .input _ _, _ => exact ⟨rfl, rfl⟩)
    (hmap_int_a := by
      intro la hint
      match la, hint with
      | .send .., _ => rfl
      | .recv .., _ => rfl)
    (hmap_int_b := by
      intro lb hint
      match lb, hint with
      | .send .., _ => rfl
      | .recv .., _ => rfl)

/-! ## Step 2: Inner Wrapper Simulation

    Extend `inner_par_sim` to handle the `readyToOutput` stutter label.
    The wrapper `innerSys` adds stutters on top of `par_bca`.
    The simulation relation includes the per-round sim_rels plus a
    cross-round consistency condition for `readyToOutput`. -/

/-! ## Cross-Round Invariant

    If process `i` is correct in round 1, round 2 has `approved (some w)`,
    and the sim_rels hold, then `s₂.1.bound_value = some w`. -/

-- Helper: project reachability from innerSys to par_bca
private theorem reachable_inner'
    {s : BCA_LTS.State T n × BCA_LTS.State (BCA_LTS.Val T) n}
    (h : Reachable (DoubleBCA2.innerSys T n f) s) :
    Reachable (DoubleBCA2.par_bca T n f) s := by
  induction h with
  | init hi => exact .init hi
  | @step s l s' _ hs ih =>
    match l with
    | .par _ => exact .step ih hs
    | .readyToOutput _ _ => rw [hs.2.2]; exact ih

-- All three helpers first project to par_bca reachability, then induct on that.
-- The key pattern: match on `l` BEFORE unfolding `par_bca`/`parallel`.

private theorem reachable_r2'
    {s : BCA_LTS.State T n × BCA_LTS.State (BCA_LTS.Val T) n}
    (h : Reachable (DoubleBCA2.innerSys T n f) s) :
    Reachable (BCA_LTS.bca (BCA_LTS.Val T) n f) s.2 := by
  have hp := reachable_inner' T n f h; clear h
  induction hp with
  | init hi => exact .init hi.2
  | @step s l s' _ hs ih =>
    match l with
    | .left _ =>
      have := hs; simp only [DoubleBCA2.par_bca, parallel] at this
      rw [this.2.2]; exact ih
    | .right _ =>
      have := hs; simp only [DoubleBCA2.par_bca, parallel] at this
      exact .step ih this.2.1
    | .sync _ _ =>
      have := hs; simp only [DoubleBCA2.par_bca, parallel] at this
      exact .step ih this.2.2

private theorem corrupted_eq'
    {s : BCA_LTS.State T n × BCA_LTS.State (BCA_LTS.Val T) n}
    (h : Reachable (DoubleBCA2.innerSys T n f) s) :
    s.1.corrupted = s.2.corrupted := by
  have hp := reachable_inner' T n f h; clear h
  induction hp with
  | init hi =>
    rw [hi.1.2.2, hi.2.2.2]
  | @step s l s' _ hs ih =>
    match l with
    | .left l₁ =>
      have := hs; simp only [DoubleBCA2.par_bca, parallel] at this
      obtain ⟨hnosync, hs₁, heq2⟩ := this
      match l₁ with
      | .send .. => rw [BCA_LTS.send_corrupted hs₁, heq2]; exact ih
      | .recv .. => rw [BCA_LTS.recv_corrupted hs₁, heq2]; exact ih
      | .input .. => rw [BCA_LTS.input_corrupted hs₁, heq2]; exact ih
      | .corrupt _ => exfalso; exact hnosync (.corrupt _) rfl
      | .output _ _ => exfalso; exact hnosync (.input _ _) ⟨rfl, rfl⟩
    | .right l₂ =>
      have := hs; simp only [DoubleBCA2.par_bca, parallel] at this
      obtain ⟨hnosync, hs₂, heq1⟩ := this
      match l₂ with
      | .send .. => rw [heq1, BCA_LTS.send_corrupted hs₂]; exact ih
      | .recv .. => rw [heq1, BCA_LTS.recv_corrupted hs₂]; exact ih
      | .output .. => rw [heq1, BCA_LTS.output_corrupted hs₂]; exact ih
      | .corrupt _ => exfalso; exact hnosync (.corrupt _) rfl
      | .input _ _ => exfalso; exact hnosync (.output _ _) ⟨rfl, rfl⟩
    | .sync l₁ l₂ =>
      have := hs; simp only [DoubleBCA2.par_bca, parallel] at this
      obtain ⟨hsync, hs₁, hs₂⟩ := this
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
        simp [DoubleBCA2.bca_sync] at hsync

private theorem feed_inv'
    {s : BCA_LTS.State T n × BCA_LTS.State (BCA_LTS.Val T) n}
    (h : Reachable (DoubleBCA2.innerSys T n f) s) :
    ∀ q mv, (s.2.local_ q).input = some mv → (s.1.local_ q).decided = some mv := by
  have hp := reachable_inner' T n f h; clear h
  induction hp with
  | init hi =>
    intro q mv hinp
    have := hi.2.1 q
    simp only [BCA_LTS.LocalState.init] at this
    rw [this] at hinp; simp at hinp
  | @step s l s' _ hs ih =>
    intro q mv hinp
    match l with
    | .left l₁ =>
      have := hs; simp only [DoubleBCA2.par_bca, parallel] at this
      obtain ⟨hnosync, hs₁, heq2⟩ := this
      have hinp' : (s.2.local_ q).input = some mv := by rw [heq2] at hinp; exact hinp
      have hdec := ih q mv hinp'
      match l₁ with
      | .send .. => rw [BCA_LTS.send_decided hs₁]; exact hdec
      | .recv src dst t v =>
        have : (s'.1.local_ q).decided = (s.1.local_ q).decided := by
          cases t with
          | init => exact BCA_LTS.recv_init_decided hs₁ q
          | echo => exact BCA_LTS.recv_echo_decided hs₁ q
          | vote => exact BCA_LTS.recv_vote_decided hs₁ q
        rw [this]; exact hdec
      | .input .. => rw [BCA_LTS.input_decided hs₁]; exact hdec
      | .corrupt _ => exfalso; exact hnosync (.corrupt _) rfl
      | .output _ _ => exfalso; exact hnosync (.input _ _) ⟨rfl, rfl⟩
    | .right l₂ =>
      have := hs; simp only [DoubleBCA2.par_bca, parallel] at this
      obtain ⟨hnosync, hs₂, heq1⟩ := this
      rw [heq1]
      match l₂ with
      | .send .. => rw [BCA_LTS.send_input hs₂] at hinp; exact ih q mv hinp
      | .recv src dst t v =>
        have : (s'.2.local_ q).input = (s.2.local_ q).input := by
          cases t with
          | init => exact BCA_LTS.recv_init_input hs₂ q
          | echo => exact BCA_LTS.recv_echo_input hs₂ q
          | vote => exact BCA_LTS.recv_vote_input hs₂ q
        rw [this] at hinp; exact ih q mv hinp
      | .output .. => rw [BCA_LTS.output_input hs₂] at hinp; exact ih q mv hinp
      | .corrupt _ => exfalso; exact hnosync (.corrupt _) rfl
      | .input _ _ => exfalso; exact hnosync (.output _ _) ⟨rfl, rfl⟩
    | .sync l₁ l₂ =>
      have := hs; simp only [DoubleBCA2.par_bca, parallel] at this
      obtain ⟨hsync, hs₁, hs₂⟩ := this
      match l₁, l₂ with
      | .corrupt _, .corrupt _ =>
        obtain ⟨_, _, heq1⟩ := hs₁
        obtain ⟨_, _, heq2⟩ := hs₂
        have h1 : (s'.1.local_ q).decided = (s.1.local_ q).decided := by simp [heq1]
        have h2 : (s'.2.local_ q).input = (s.2.local_ q).input := by simp [heq2]
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
        simp [DoubleBCA2.bca_sync] at hsync

/-- Cross-round invariant: if `approved (some w)` in concrete round 2,
    then `bound_value = some w` in abstract round 1.

    Proof sketch (same as `DoubleBCA_Simulation.approved_implies_r1_bound`):
    1. `approved (some w)` → `inputSupport (some w) ≥ f+1` in round 2
       (from `BCA_Simulation.approval_implies_inputSupport`)
    2. Extract a correct process `q` with round 2 input `some w`
       (pigeonhole on `inputSupport`)
    3. Feed invariant: `(s₁.2.local_ q).input = some (some w)`
       → `(s₁.1.local_ q).decided = some (some w)` (round 2 input = round 1 decision,
       invariant of the double composition maintained by sync)
    4. `s₂.1.decided q = (s₁.1.local_ q).decided = some (some w)` (from sim_rel)
    5. `decided (some w)` → `echoSupport w ≥ threshold` → `bound_value = some w`
       (from round 1 BCA invariant via sim_rel)

    Requires: feed invariant for `DoubleBCA2.innerSys`, corruption agreement
    between rounds, and BCA quorum invariants from `BCA_Simulation`. -/
private theorem approved_implies_r1_bound [Inhabited T] [Inhabited (Fin n)]
    (hn : n > 3 * f)
    {s₁ : BCA_LTS.State T n × BCA_LTS.State (BCA_LTS.Val T) n}
    {s₂ : IdealBCA.State T n × IdealBCA.State (IdealBCA.Val T) n}
    (hreach : Reachable (DoubleBCA2.innerSys T n f) s₁)
    (hR1 : BCA_Simulation.sim_rel T n f s₁.1 s₂.1)
    (_hR2 : BCA_Simulation.sim_rel (BCA_LTS.Val T) n f s₁.2 s₂.2)
    (hreach_a1 : Reachable (IdealBCA.ideal_bca T n f) s₂.1)
    (idx : Fin n)
    (hcorr : BCA_LTS.isCorrect T n s₁.1 idx)
    (w : T)
    (happroved : (s₁.2.local_ idx).approved (some w) = true) :
    s₂.1.bound_value = some w := by
  have hreach_r2 := reachable_r2' T n f hreach
  have hcorr_eq := corrupted_eq' T n f hreach
  have hfeed := feed_inv' T n f hreach
  have hcorr_r2 : BCA_LTS.isCorrect (BCA_LTS.Val T) n s₁.2 idx := by
    simp only [BCA_LTS.isCorrect] at hcorr ⊢; rw [← hcorr_eq]; exact hcorr
  have hsup := BCA_Simulation.approval_implies_inputSupport (BCA_LTS.Val T) n f
    hreach_r2 hn idx (some w) hcorr_r2 happroved
  have hbudget := BCA_Simulation.corrupted_budget (BCA_LTS.Val T) n f hreach_r2
  have hpos : ((List.finRange n).filter (fun q =>
      decide (q ∉ s₁.2.corrupted) &&
      decide ((s₁.2.local_ q).input = some (some w)))).length > 0 := by omega
  obtain ⟨q, hq⟩ := List.exists_mem_of_length_pos hpos
  simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hq
  have hq_dec := hfeed q (some w) hq.2.2
  have hinv := IdealBCA.inv_reachable T n f s₂.1 hreach_a1
  exact hinv.1 q w ((hR1.2.2.1 q).trans hq_dec)

-- Helper: lift InternalStar from par_ideal to innerSys (abstract side)
-- Internal labels in parallel_labelling are internal in innerLabelling.
private def lift_par_istar [Inhabited T] [Inhabited (Fin n)]
    {a b : IdealBCA.State T n × IdealBCA.State (IdealBCA.Val T) n}
    (h : InternalStar (DoubleIdealBCA2.par_ideal T n f)
      (parallel_labelling (IdealBCA.ideal_labelling T n)
        (IdealBCA.ideal_labelling (IdealBCA.Val T) n)) a b) :
    InternalStar (DoubleIdealBCA2.innerSys T n f)
      (DoubleIdealBCA2.innerLabelling T n) a b :=
  match h with
  | .refl => .refl
  | .step (l := l) hint hstep rest =>
    have hint' : (DoubleIdealBCA2.innerLabelling T n).is_internal (.par l) = true := by
      revert hint; simp only [parallel_labelling, IdealBCA.ideal_labelling,
        DoubleIdealBCA2.innerLabelling]
      split <;> (intro h; split <;> (split at h <;> simp at *))
    .step hint' (show (DoubleIdealBCA2.innerSys T n f).step _ (.par _) _ from hstep)
      (lift_par_istar rest)

-- Helper: label_map preserves internality across labellings.
-- Proof is case analysis on BCA/IdealBCA label constructors, verifying that
-- BCA_Simulation.label_map maps each internal BCA label to an internal IdealBCA label.
private theorem inner_par_sim_label_map_eq [Inhabited T] [Inhabited (Fin n)] (hn : n > 3 * f) :
    (inner_par_sim T n f hn).label_map =
      parallel_label_map (BCA_Simulation.label_map T n)
        (BCA_Simulation.label_map (BCA_LTS.Val T) n) := rfl

private theorem inner_label_map_int [Inhabited T] [Inhabited (Fin n)] (hn : n > 3 * f)
    (cl : CompLabel (BCA_LTS.Label T n) (BCA_LTS.Label (BCA_LTS.Val T) n))
    (hint : (DoubleBCA2.innerLabelling T n).is_internal
      (DoubleBCA2.InnerLabel.par cl) = true) :
    (DoubleIdealBCA2.innerLabelling T n).is_internal
      (.par ((inner_par_sim T n f hn).label_map cl)) = true := by
  rw [inner_par_sim_label_map_eq]
  revert hint
  simp only [DoubleBCA2.innerLabelling, DoubleIdealBCA2.innerLabelling,
    parallel_label_map, BCA_Simulation.label_map]
  match cl with
  | .left la => match la with
    | .send .. | .recv .. | .output _ _ | .corrupt _ | .input _ _ => simp
  | .right lb => match lb with
    | .send .. | .recv .. | .input _ _ | .output _ _ | .corrupt _ => simp
  | .sync la lb => match la, lb with
    | .corrupt _, .corrupt _ | .output _ _, _ => simp
    | .corrupt _, .input .. | .corrupt _, .output ..
    | .corrupt _, .send .. | .corrupt _, .recv ..
    | .input .., _ | .send .., _ | .recv .., _ => exact id

-- Helper: external in innerLabelling → external in parallel_labelling
omit [DecidableEq T] in
private theorem inner_ext_implies_par_ext [Inhabited T] [Inhabited (Fin n)]
    (cl : CompLabel (BCA_LTS.Label T n) (BCA_LTS.Label (BCA_LTS.Val T) n))
    (hext : (DoubleBCA2.innerLabelling T n).is_internal
      (DoubleBCA2.InnerLabel.par cl) = false) :
    (parallel_labelling (BCA_LTS.bca_labelling T n)
      (BCA_LTS.bca_labelling (BCA_LTS.Val T) n)).is_external cl = true := by
  simp only [DoubleBCA2.innerLabelling, Labelling.is_external, parallel_labelling,
    BCA_LTS.bca_labelling, Bool.not_eq_eq_eq_not, Bool.not_true] at hext ⊢
  revert hext; split <;> (try (subst_eqs; simp)) ; (try simp at *)

-- Helper: a step of par_ideal preserves reachability of component 1
private theorem par_ideal_step_reachable_fst [Inhabited T] [Inhabited (Fin n)]
    {s s' : IdealBCA.State T n × IdealBCA.State (IdealBCA.Val T) n}
    {cl : CompLabel (IdealBCA.Label T n) (IdealBCA.Label (IdealBCA.Val T) n)}
    (hra : Reachable (IdealBCA.ideal_bca T n f) s.1)
    (hstep : (DoubleIdealBCA2.par_ideal T n f).step s cl s') :
    Reachable (IdealBCA.ideal_bca T n f) s'.1 := by
  simp only [DoubleIdealBCA2.par_ideal, parallel] at hstep
  match cl with
  | .left l₁ => exact .step hra hstep.2.1
  | .right _ => rw [hstep.2.2]; exact hra
  | .sync l₁ _ => exact .step hra hstep.2.1

-- Helper: a step of par_ideal preserves reachability of component 2
private theorem par_ideal_step_reachable_snd [Inhabited T] [Inhabited (Fin n)]
    {s s' : IdealBCA.State T n × IdealBCA.State (IdealBCA.Val T) n}
    {cl : CompLabel (IdealBCA.Label T n) (IdealBCA.Label (IdealBCA.Val T) n)}
    (hra : Reachable (IdealBCA.ideal_bca (IdealBCA.Val T) n f) s.2)
    (hstep : (DoubleIdealBCA2.par_ideal T n f).step s cl s') :
    Reachable (IdealBCA.ideal_bca (IdealBCA.Val T) n f) s'.2 := by
  simp only [DoubleIdealBCA2.par_ideal, parallel] at hstep
  match cl with
  | .left _ => rw [hstep.2.2]; exact hra
  | .right l₂ => exact .step hra hstep.2.1
  | .sync _ l₂ => exact .step hra hstep.2.2

-- Helper: InternalStar of par_ideal preserves reachability of component 1
private theorem istar_reachable_fst [Inhabited T] [Inhabited (Fin n)]
    {a b : IdealBCA.State T n × IdealBCA.State (IdealBCA.Val T) n}
    (hra : Reachable (IdealBCA.ideal_bca T n f) a.1)
    (h : InternalStar (DoubleIdealBCA2.par_ideal T n f)
      (parallel_labelling (IdealBCA.ideal_labelling T n)
        (IdealBCA.ideal_labelling (IdealBCA.Val T) n)) a b) :
    Reachable (IdealBCA.ideal_bca T n f) b.1 := by
  induction h with
  | refl => exact hra
  | step _ hstep _ ih => exact ih (par_ideal_step_reachable_fst T n f hra hstep)

-- Helper: InternalStar of par_ideal preserves reachability of component 2
private theorem istar_reachable_snd [Inhabited T] [Inhabited (Fin n)]
    {a b : IdealBCA.State T n × IdealBCA.State (IdealBCA.Val T) n}
    (hra : Reachable (IdealBCA.ideal_bca (IdealBCA.Val T) n f) a.2)
    (h : InternalStar (DoubleIdealBCA2.par_ideal T n f)
      (parallel_labelling (IdealBCA.ideal_labelling T n)
        (IdealBCA.ideal_labelling (IdealBCA.Val T) n)) a b) :
    Reachable (IdealBCA.ideal_bca (IdealBCA.Val T) n f) b.2 := by
  induction h with
  | refl => exact hra
  | step _ hstep _ ih => exact ih (par_ideal_step_reachable_snd T n f hra hstep)

def inner_sim [Inhabited T] [Inhabited (Fin n)] (hn : n > 3 * f) :
    ForwardSim
      (DoubleBCA2.innerSys T n f)
      (DoubleBCA2.innerLabelling T n)
      (DoubleIdealBCA2.innerSys T n f)
      (DoubleIdealBCA2.innerLabelling T n) where
  R := fun s₁ s₂ => (inner_par_sim T n f hn).R s₁ s₂ ∧
    Reachable (IdealBCA.ideal_bca T n f) s₂.1 ∧
    Reachable (IdealBCA.ideal_bca (IdealBCA.Val T) n f) s₂.2
  label_map := fun l =>
    match l with
    | .par cl => .par ((inner_par_sim T n f hn).label_map cl)
    | .readyToOutput i v => .readyToOutput i (map_fv T v)
  init_sim := by
    intro s₁ hinit
    obtain ⟨s₂, hinit₂, hR⟩ := (inner_par_sim T n f hn).init_sim s₁ hinit
    exact ⟨s₂, hinit₂, hR, .init hinit₂.1, .init hinit₂.2⟩
  step_internal := by
    intro s₁ l₁ s₁' s₂ hreach ⟨hR_par, hra1, hra2⟩ hint hstep
    match l₁ with
    | .par cl =>
      simp only [DoubleBCA2.innerSys] at hstep
      by_cases hcl : (parallel_labelling (BCA_LTS.bca_labelling T n)
          (BCA_LTS.bca_labelling (BCA_LTS.Val T) n)).is_internal cl = true
      · obtain ⟨s₂', hstar, hR'⟩ := (inner_par_sim T n f hn).step_internal
          s₁ cl s₁' s₂ (reachable_inner' T n f hreach) hR_par hcl hstep
        exact ⟨s₂', lift_par_istar T n f hstar, hR',
          istar_reachable_fst T n f hra1 hstar,
          istar_reachable_snd T n f hra2 hstar⟩
      · have hext_par : (parallel_labelling (BCA_LTS.bca_labelling T n)
            (BCA_LTS.bca_labelling (BCA_LTS.Val T) n)).is_external cl = true := by
          simp [Labelling.is_external, hcl]
        obtain ⟨s₂m, s₂m', s₂', hpre, hstep₂, hpost, hR'⟩ :=
          (inner_par_sim T n f hn).step_external
            s₁ cl s₁' s₂ (reachable_inner' T n f hreach) hR_par hext_par hstep
        have hmid : (DoubleIdealBCA2.innerLabelling T n).is_internal
            (.par ((inner_par_sim T n f hn).label_map cl)) = true := by
          simp only [DoubleBCA2.innerLabelling] at hint
          exact inner_label_map_int T n f hn cl hint
        have hra1' := istar_reachable_fst T n f hra1 hpre
        have hra2' := istar_reachable_snd T n f hra2 hpre
        have hra1'' := par_ideal_step_reachable_fst T n f hra1' hstep₂
        have hra2'' := par_ideal_step_reachable_snd T n f hra2' hstep₂
        exact ⟨s₂', (lift_par_istar T n f hpre).trans
          (.step hmid hstep₂ (lift_par_istar T n f hpost)), hR',
          istar_reachable_fst T n f hra1'' hpost,
          istar_reachable_snd T n f hra2'' hpost⟩
  step_external := by
    intro s₁ l₁ s₁' s₂ hreach ⟨hR_par, hra1, hra2⟩ hext hstep
    match l₁ with
    | .par cl =>
      simp only [DoubleBCA2.innerSys] at hstep
      simp only [Labelling.is_external, DoubleBCA2.innerLabelling, Bool.not_eq_eq_eq_not,
        Bool.not_true] at hext
      have hext_par : (parallel_labelling (BCA_LTS.bca_labelling T n)
          (BCA_LTS.bca_labelling (BCA_LTS.Val T) n)).is_external cl = true :=
        inner_ext_implies_par_ext T n cl hext
      obtain ⟨s₂m, s₂m', s₂', hpre, hstep₂, hpost, hR'⟩ :=
        (inner_par_sim T n f hn).step_external
          s₁ cl s₁' s₂ (reachable_inner' T n f hreach) hR_par hext_par hstep
      have hra1' := istar_reachable_fst T n f hra1 hpre
      have hra2' := istar_reachable_snd T n f hra2 hpre
      have hra1'' := par_ideal_step_reachable_fst T n f hra1' hstep₂
      have hra2'' := par_ideal_step_reachable_snd T n f hra2' hstep₂
      exact ⟨s₂m, s₂m', s₂',
        lift_par_istar T n f hpre, hstep₂, lift_par_istar T n f hpost,
        hR',
        istar_reachable_fst T n f hra1'' hpost,
        istar_reachable_snd T n f hra2'' hpost⟩
    | .readyToOutput i v =>
      simp only [DoubleBCA2.innerSys] at hstep
      obtain ⟨hcorr, hguard, hstutter⟩ := hstep
      have hdec_eq := hR_par.2.2.2.1 i
      have hcorr_ideal : IdealBCA.isCorrect T n s₂.1 i := by
        simp only [BCA_LTS.isCorrect, IdealBCA.isCorrect] at hcorr ⊢
        rw [hR_par.1.1]; exact hcorr
      have hguard_abs : match s₂.2.decided i with
          | some (some (some w)) => map_fv T v = DoubleIdealBCA2.FinalVal.valA w
          | some (some none) => map_fv T v = DoubleIdealBCA2.FinalVal.bot
          | some none => ∃ w, s₂.1.bound_value = some w ∧
              map_fv T v = DoubleIdealBCA2.FinalVal.valB w
          | none => False := by
        rw [hdec_eq]
        match hd : (s₁.2.local_ i).decided, hguard with
        | some (some (some w)), hg => subst hg; rfl
        | some (some none), hg => subst hg; rfl
        | some none, ⟨w, happroved, hv⟩ =>
          subst hv
          exact ⟨w,
          approved_implies_r1_bound T n f hn hreach hR_par.1 hR_par.2 hra1 i hcorr w happroved, rfl⟩
        | none, hg => exact hg.elim
      -- Stutter on both sides
      subst hstutter
      exact ⟨s₂, s₂, s₂, .refl, ⟨hcorr_ideal, hguard_abs, rfl⟩, .refl, hR_par, hra1, hra2⟩

/-! ## Step 3: Output Controller Identity Simulation

    The output controller is identical on both sides, so the simulation
    is the identity. -/

def output_id_sim [Inhabited T] [Inhabited (Fin n)] :
    ForwardSim
      (DoubleBCA2.outputCtrl T n)
      (DoubleBCA2.outputLabelling T n)
      (DoubleIdealBCA2.outputCtrl T n)
      (DoubleIdealBCA2.outputLabelling T n) where
  R := fun s₁ s₂ => ∀ p, s₂ p = (s₁ p).map (map_fv T)
  label_map := fun l =>
    match l with
    | .doOutput i v => .doOutput i (map_fv T v)
    | .idle => .idle
  init_sim := by
    intro s₁ hinit
    exact ⟨fun _ => none, fun _ => rfl, fun p => by simp [hinit p]⟩
  step_internal := by
    intro s₁ l s₁' s₂ _ hR hint hstep
    match l, hint with
    | .idle, _ =>
      simp only [DoubleBCA2.outputCtrl] at hstep
      subst hstep; exact ⟨s₂, .refl, hR⟩
  step_external := by
    intro s₁ l s₁' s₂ _ hR hext hstep
    match l, hext with
    | .doOutput i v, _ =>
      simp only [DoubleBCA2.outputCtrl] at hstep
      obtain ⟨hnone, rfl⟩ := hstep
      let s₂' := fun p => if p = i then some (map_fv T v) else s₂ p
      refine ⟨s₂, s₂', s₂', .refl, ?_, .refl, ?_⟩
      · simp only [DoubleIdealBCA2.outputCtrl]
        refine ⟨?_, rfl⟩
        rw [hR i, hnone]; rfl
      · intro p
        simp only [s₂']
        split
        · next h => subst h; simp
        · next h => simp [hR p]

/-! ## Step 4: Full Composed Simulation

    `parallel_forward_sim inner_sim output_id_sim` at the outer level. -/

def double_forward_sim [Inhabited T] [Inhabited (Fin n)]
    (hn : n > 3 * f) :
    ForwardSim
      (DoubleBCA2.doubleBCA T n f)
      (DoubleBCA2.labelling T n)
      (DoubleIdealBCA2.doubleIdealBCA T n f)
      (DoubleIdealBCA2.labelling T n) :=
  parallel_forward_sim
    (inner_sim T n f hn)
    (output_id_sim T n)
    (hsync := by
      intro la lb hsyn
      match la, lb, hsyn with
      | .readyToOutput _ v, .doOutput _ _, ⟨rfl, rfl⟩ => exact ⟨rfl, rfl⟩)
    (hnosync_left := by
      intro la hnosyn lb₂
      match la with
      | .par _ =>
        change ¬DoubleIdealBCA2.output_sync T n (.par _) lb₂
        match lb₂ with | .doOutput _ _ | .idle => exact id
      | .readyToOutput i v => exact absurd ⟨rfl, rfl⟩ (hnosyn (.doOutput i v)))
    (hnosync_right := by
      intro lb hnosyn la₂
      match lb with
      | .idle =>
        change ¬DoubleIdealBCA2.output_sync T n la₂ .idle
        match la₂ with | .par _ | .readyToOutput _ _ => exact id
      | .doOutput i v => exact absurd ⟨rfl, rfl⟩ (hnosyn (.readyToOutput i v)))
    (hsync_ext := by
      intro la lb hsyn
      match la, lb, hsyn with
      | .readyToOutput _ _, .doOutput _ _, ⟨_, _⟩ =>
        exact ⟨by simp [Labelling.is_external, DoubleIdealBCA2.innerLabelling],
               by simp [Labelling.is_external, DoubleIdealBCA2.outputLabelling]⟩)
    (hmap_int_a := by
      intro la hint
      match la with
      | .readyToOutput _ _ => simp [DoubleBCA2.innerLabelling] at hint
      | .par cl => exact inner_label_map_int T n f hn cl hint)
    (hmap_int_b := by
      intro lb hint
      match lb with
      | .doOutput _ _ => simp [DoubleBCA2.outputLabelling] at hint
      | .idle => rfl)

/-! ## Protocol Properties for DoubleBCA2

    Transfer validity, graded agreement, and binding from the ideal system
    through the forward simulation. -/

omit [DecidableEq T] in
private theorem map_fv_injective : ∀ a b : DoubleBCA2.FinalVal T,
    map_fv T a = map_fv T b → a = b := by
  intro a b h; cases a <;> cases b <;>
    simp only [map_fv, DoubleIdealBCA2.FinalVal.valA.injEq,
      DoubleIdealBCA2.FinalVal.valB.injEq, reduceCtorEq] at h <;>
    (try rfl) <;> exact congrArg _ h

/-- Helper: extract the simulation relation components. -/
private theorem sim_components [Inhabited T] [Inhabited (Fin n)] (hn : n > 3 * f)
    {s₁ : (BCA_LTS.State T n × BCA_LTS.State (BCA_LTS.Val T) n) ×
    (Fin n → Option (DoubleBCA2.FinalVal T))}
    {s₂ : (IdealBCA.State T n × IdealBCA.State (IdealBCA.Val T) n) ×
    (Fin n → Option (DoubleIdealBCA2.FinalVal T))}
    (hR : (double_forward_sim T n f hn).R s₁ s₂) :
    s₂.1.1.corrupted = s₁.1.1.corrupted ∧
    (∀ p, s₂.1.1.input_ p = (s₁.1.1.local_ p).input) ∧
    (∀ p, s₂.2 p = (s₁.2 p).map (map_fv T)) :=
  ⟨hR.1.1.1.1, hR.1.1.1.2.1, hR.2⟩

omit [DecidableEq T] in
private theorem transfer_graded_agreement
    (s₁ : (BCA_LTS.State T n × BCA_LTS.State (BCA_LTS.Val T) n) ×
    (Fin n → Option (DoubleBCA2.FinalVal T)))
    (s₂ : (IdealBCA.State T n × IdealBCA.State (IdealBCA.Val T) n) ×
    (Fin n → Option (DoubleIdealBCA2.FinalVal T)))
    (hcorr_eq : s₂.1.1.corrupted = s₁.1.1.corrupted)
    (hfinal_eq : ∀ p, s₂.2 p = (s₁.2 p).map (map_fv T))
    (hagr : DoubleIdealBCA2.graded_agreement T n s₂) :
    DoubleBCA2.graded_agreement T n s₁ := by
  have corr : ∀ p, BCA_LTS.isCorrect T n s₁.1.1 p → IdealBCA.isCorrect T n s₂.1.1 p := by
    intro p h; simp only [BCA_LTS.isCorrect, IdealBCA.isCorrect] at h ⊢; rw [hcorr_eq]; exact h
  have lift : ∀ p fv, s₁.2 p = some fv → s₂.2 p = some (map_fv T fv) :=
    fun p _ h => by rw [hfinal_eq, h]; rfl
  refine ⟨?_, ?_, ?_⟩
  · intro p q v w hcp hcq hfpv hfqw
    exact hagr.1 p q v w (corr p hcp) (corr q hcq)
      (hfpv.elim (fun h => .inl (lift p _ h)) (fun h => .inr (lift p _ h)))
      (hfqw.elim (fun h => .inl (lift q _ h)) (fun h => .inr (lift q _ h)))
  · intro p q v hcp hcq hfp hfq
    exact hagr.2.1 p q v (corr p hcp) (corr q hcq) (lift p _ hfp) (lift q _ hfq)
  · intro p q v hcp hcq hfp hfq
    exact hagr.2.2 p q v (corr p hcp) (corr q hcq) (lift p _ hfp) (lift q _ hfq)

omit [DecidableEq T] in
private theorem transfer_double_validity (v : T)
    (s₁ : (BCA_LTS.State T n × BCA_LTS.State (BCA_LTS.Val T) n) ×
      (Fin n → Option (DoubleBCA2.FinalVal T)))
    (s₂ : (IdealBCA.State T n × IdealBCA.State (IdealBCA.Val T) n) ×
      (Fin n → Option (DoubleIdealBCA2.FinalVal T)))
    (hcorr_eq : s₂.1.1.corrupted = s₁.1.1.corrupted)
    (hinp_eq : ∀ p, s₂.1.1.input_ p = (s₁.1.1.local_ p).input)
    (hfinal_eq : ∀ p, s₂.2 p = (s₁.2 p).map (map_fv T))
    (hval : DoubleIdealBCA2.double_validity T n v s₂) :
    DoubleBCA2.double_validity T n v s₁ := by
  intro hpre p hcorr
  have hcorr₂ : IdealBCA.isCorrect T n s₂.1.1 p := by
    simp only [BCA_LTS.isCorrect, IdealBCA.isCorrect] at hcorr ⊢; rw [hcorr_eq]; exact hcorr
  have hpre₂ : ∀ q, ¬IdealBCA.isCorrect T n s₂.1.1 q ∨
      s₂.1.1.input_ q = none ∨ s₂.1.1.input_ q = some v := by
    intro q; rcases hpre q with h | h | h
    · left; simp only [BCA_LTS.isCorrect, Decidable.not_not, IdealBCA.isCorrect] at h ⊢
      rw [hcorr_eq]; exact h
    · right; left; rw [hinp_eq]; exact h
    · right; right; rw [hinp_eq]; exact h
  change s₁.2 p = none ∨ s₁.2 p = some (.valA v)
  rcases hval hpre₂ p hcorr₂ with h | h
  · have h : s₂.2 p = none := h
    rw [hfinal_eq] at h; simp only [Option.map_eq_none_iff] at h; left; exact h
  · have h : s₂.2 p = some (.valA v) := h
    match hout : s₁.2 p with
    | none => left; rfl
    | some fv =>
      rw [hfinal_eq, hout] at h; simp only [Option.map_some, map_fv, Option.some.injEq] at h
      cases fv with
      | valA w => right; simp only [DoubleIdealBCA2.FinalVal.valA.injEq] at h; rw [h]
      | valB w => simp at h
      | bot => simp at h

theorem real_graded_agreement [Inhabited T] [Inhabited (Fin n)] (hn : n > 3 * f) :
    (DoubleBCA2.doubleBCA T n f).satisfies
      [ltl| □ ⌜ DoubleBCA2.graded_agreement T n ⌝] :=
  (double_forward_sim T n f hn).preserves_invariant
    (DoubleIdealBCA2.binding_inv T n f)
    (DoubleIdealBCA2.binding_inv_init T n f)
    (DoubleIdealBCA2.binding_inv_step T n f)
    (DoubleBCA2.graded_agreement T n)
    (fun s₁ s₂ hR hinv => by
      obtain ⟨hcorr_eq, _, hfinal_eq⟩ := sim_components T n f hn hR
      obtain ⟨hcons, hinv1, hinv2, hfeed⟩ := hinv
      exact transfer_graded_agreement T n s₁ s₂ hcorr_eq hfinal_eq
        (DoubleIdealBCA2.graded_agreement_from_inv T n f s₂ hcons hinv1 hinv2 hfeed))

theorem real_double_validity [Inhabited T] [Inhabited (Fin n)] (hn : n > 3 * f) (v : T) :
    (DoubleBCA2.doubleBCA T n f).satisfies
      [ltl| □ ⌜ DoubleBCA2.double_validity T n v ⌝] :=
  (double_forward_sim T n f hn).preserves_invariant
    (DoubleIdealBCA2.binding_inv T n f)
    (DoubleIdealBCA2.binding_inv_init T n f)
    (DoubleIdealBCA2.binding_inv_step T n f)
    (DoubleBCA2.double_validity T n v)
    (fun s₁ s₂ hR hinv => by
      obtain ⟨hcorr_eq, hinp_eq, hfinal_eq⟩ := sim_components T n f hn hR
      obtain ⟨hcons, hinv1, hinv2, hfeed⟩ := hinv
      exact transfer_double_validity T n v s₁ s₂ hcorr_eq hinp_eq hfinal_eq
        (DoubleIdealBCA2.double_validity_from_inv T n f v s₂ hcons hinv1 hinv2 hfeed))

theorem real_double_binding [Inhabited T] [Inhabited (Fin n)] (hn : n > 3 * f) :
    DoubleBCA2.double_binding T n f :=
  (double_forward_sim T n f hn).preserves_branching
    (P_guard := fun s₂ => ∃ p fv, IdealBCA.isCorrect T n s₂.1.1 p ∧ s₂.2 p = some fv)
    (P_concl := fun v s₂ => ∀ q fv, IdealBCA.isCorrect T n s₂.1.1 q → s₂.2 q = some fv →
      fv = .bot ∨ fv = .valA v ∨ fv = .valB v)
    (DoubleIdealBCA2.double_binding_holds T n f)
    (fun s₁ s₂ hR ⟨p, fv, hcorr, (hfp : s₁.2 p = _)⟩ => by
      obtain ⟨hcorr_eq, _, hfinal_eq⟩ := sim_components T n f hn hR
      exact ⟨p, map_fv T fv,
        by simp only [BCA_LTS.isCorrect, IdealBCA.isCorrect] at hcorr ⊢; rw [hcorr_eq]; exact hcorr,
        by rw [hfinal_eq, hfp]; simp⟩)
    (fun v s₁ s₂ hR hconcl q fv hcorr (hfq : s₁.2 q = _) => by
      obtain ⟨hcorr_eq, _, hfinal_eq⟩ := sim_components T n f hn hR
      have hcorr₂ : IdealBCA.isCorrect T n s₂.1.1 q := by
        simp only [BCA_LTS.isCorrect, IdealBCA.isCorrect] at hcorr ⊢; rw [hcorr_eq]; exact hcorr
      have hfq₂ : s₂.2 q = some (map_fv T fv) := by rw [hfinal_eq, hfq]; simp
      rcases hconcl q (map_fv T fv) hcorr₂ hfq₂ with h | h | h
      · left; exact map_fv_injective T fv .bot h
      · right; left; exact map_fv_injective T fv (.valA v) h
      · right; right; exact map_fv_injective T fv (.valB v) h)

end DoubleBCA2_Simulation
