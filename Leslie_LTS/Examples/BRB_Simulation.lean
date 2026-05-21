import Leslie_LTS.Framework
import Leslie_LTS.Examples.BrachaBRB
import Leslie_LTS.Examples.IdealBRB
import Leslie_LTS.Examples.UtilityByzantine
import Leslie_LTS.Examples.CorruptionInvariants

/-! # Forward Simulation: Real BRB → Ideal BRB

  Forward simulation from the real Bracha BRB to the ideal BRB specification.
  Lifts safety properties (validity, agreement) from ideal to real.
-/

open LTS

namespace BRB_Simulation

variable (n f : Nat) (Value : Type) [DecidableEq Value]
variable (sender : Fin n)

/-! ### Label Map -/

/-- Map real BRB labels to ideal BRB labels. -/
def label_map : BRB_LTS.Label n Value → IdealBRB.Label n Value
  | .corrupt i => .corrupt i
  | .input i v => .input i v
  | .output i v => .output i v
  | .send _ _ _ v => .commit v
  | .recv _ _ _ v => .commit v

/-! ### Simulation Relation -/

/-- `|corrupted| + |{correct p : sendRecv(p) = some v}|`. -/
def initSupport (s_r : BRB_LTS.State n Value) (v : Value) : Nat :=
  s_r.corrupted.length +
  ((List.finRange n).filter (fun p =>
    p ∉ s_r.corrupted ∧ (s_r.local_ p).sendRecv = some v)).length

/-- If `initSupport` for `v` exceeds the corrupted count, then some process
    has `sendRecv = some v`, so `v` appears in the candidate list. -/
private theorem initSupport_in_candidates {n : Nat} {Value : Type} [DecidableEq Value]
    (s_r : BRB_LTS.State n Value) (v : Value)
    (h : initSupport n Value s_r v > s_r.corrupted.length) :
    v ∈ (List.finRange n).filterMap (fun p => (s_r.local_ p).sendRecv) := by
  unfold initSupport at h
  have hpos : ((List.finRange n).filter (fun p =>
    p ∉ s_r.corrupted ∧ (s_r.local_ p).sendRecv = some v)).length > 0 := by omega
  obtain ⟨p, hp⟩ := List.exists_mem_of_length_pos hpos
  simp only [Bool.decide_and, decide_not, List.mem_filter, List.mem_finRange, Bool.and_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, decide_eq_true_eq,
    true_and] at hp
  exact List.mem_filterMap.mpr ⟨p, List.mem_finRange p, hp.2⟩

/-- Find a value that newly crosses the echo threshold, if any.
    Returns `some ⟨v, proof⟩` with the crossing value, or `none`. -/
private def findNewCrossing {n : Nat} (f : Nat) {Value : Type} [DecidableEq Value]
    (s_r s_r' : BRB_LTS.State n Value) :
    Option { v : Value //
      initSupport n Value s_r' v ≥ BRB_LTS.echoThreshold n f ∧
      ¬ initSupport n Value s_r v ≥ BRB_LTS.echoThreshold n f } :=
  let candidates := (List.finRange n).filterMap (fun p => (s_r.local_ p).sendRecv)
  let pred := fun v => decide (initSupport n Value s_r' v ≥ BRB_LTS.echoThreshold n f) &&
                       !decide (initSupport n Value s_r v ≥ BRB_LTS.echoThreshold n f)
  match hfind : candidates.find? pred with
  | some v =>
    have hpred : pred v = true := List.find?_some hfind
    have hge : initSupport n Value s_r' v ≥ BRB_LTS.echoThreshold n f := by
      simp only [pred, Bool.and_eq_true, decide_eq_true_eq] at hpred; exact hpred.1
    have hlt : ¬ initSupport n Value s_r v ≥ BRB_LTS.echoThreshold n f := by
      simp only [pred, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        Nat.not_le] at hpred
      exact Nat.not_le.mpr hpred.2
    some ⟨v, hge, hlt⟩
  | none => none

/-- If any value crosses the threshold, `findNewCrossing` finds one. -/
private theorem findNewCrossing_complete {n : Nat} {f : Nat} {Value : Type} [DecidableEq Value]
    {s_r s_r' : BRB_LTS.State n Value}
    (hn : n > 3 * f)
    (hbudget : s_r'.corrupted.length ≤ f)
    (hcl : ∀ p : Fin n, s_r'.local_ p = s_r.local_ p)
    (hex : ∃ v, initSupport n Value s_r' v ≥ BRB_LTS.echoThreshold n f ∧
               ¬ initSupport n Value s_r v ≥ BRB_LTS.echoThreshold n f) :
    (findNewCrossing f s_r s_r').isSome = true := by
  obtain ⟨v, hge, hlt⟩ := hex
  have hgt : initSupport n Value s_r' v > s_r'.corrupted.length := by
    unfold BRB_LTS.echoThreshold at hge; omega
  have hmem_sr' := initSupport_in_candidates s_r' v hgt
  have hmem_sr : v ∈ (List.finRange n).filterMap (fun p => (s_r.local_ p).sendRecv) := by
    obtain ⟨p, _, hp⟩ := List.mem_filterMap.mp hmem_sr'
    exact List.mem_filterMap.mpr ⟨p, List.mem_finRange p, by rw [← hcl p]; exact hp⟩
  unfold findNewCrossing
  simp only
  split
  · rfl
  · next hfind =>
    have hnone := List.find?_eq_none.mp hfind v hmem_sr
    simp [hge, hlt] at hnone

/-- Simulation relation connecting real and ideal BRB states. -/
def sim_rel (s_r : BRB_LTS.State n Value) (s_i : IdealBRB.State n Value) : Prop :=
  s_i.corrupted = s_r.corrupted ∧
  s_i.broadcastVal = (s_r.local_ sender).broadcastVal ∧
  (∀ p, BRB_LTS.isCorrect n Value s_r p →
    s_i.returned p = (s_r.local_ p).returned) ∧
  (∀ v, s_i.set_up = some v ↔
    initSupport n Value s_r v ≥ BRB_LTS.echoThreshold n f)

/-! ### Helper Lemmas -/

/-- At most one value can have `initSupport ≥ n-f` when `n > 3f`. -/
theorem initSupport_unique {n f : Nat} {Value : Type} [DecidableEq Value]
    (hn : n > 3 * f) (s : BRB_LTS.State n Value)
    (hbudget : s.corrupted.length ≤ f)
    (hnodup : s.corrupted.Nodup)
    (v w : Value)
    (hv : initSupport n Value s v ≥ BRB_LTS.echoThreshold n f)
    (hw : initSupport n Value s w ≥ BRB_LTS.echoThreshold n f) :
    v = w := by
  if hvw : v = w then exact hvw else
  exfalso
  unfold initSupport BRB_LTS.echoThreshold at hv hw
  have hnf : n ≥ f := by omega
  have hfv : ((List.finRange n).filter (fun p =>
      p ∉ s.corrupted ∧ (s.local_ p).sendRecv = some v)).length + f + s.corrupted.length ≥ n := by
      omega
  have hfw : ((List.finRange n).filter (fun p =>
      p ∉ s.corrupted ∧ (s.local_ p).sendRecv = some w)).length + f + s.corrupted.length ≥ n := by
      omega
  clear hv hw
  have h3 : ∀ (l : List (Fin n)),
      (l.filter (fun p => decide (p ∉ s.corrupted ∧ (s.local_ p).sendRecv = some v))).length +
      (l.filter (fun p => decide (p ∉ s.corrupted ∧ (s.local_ p).sendRecv = some w))).length +
      (l.filter (fun p => decide (p ∈ s.corrupted))).length
      ≤ l.length := by
    intro l
    exact three_way_filter_le
      (fun p => decide (p ∉ s.corrupted ∧ (s.local_ p).sendRecv = some v))
      (fun p => decide (p ∉ s.corrupted ∧ (s.local_ p).sendRecv = some w))
      (fun p => decide (p ∈ s.corrupted)) l
      (fun x => by
        by_contra h
        simp only [Bool.and_eq_true, Bool.not_eq_false, decide_eq_true_eq] at h
        exact hvw (Option.some.inj (h.1.2.symm.trans h.2.2)))
      (fun x => by
        by_contra h
        simp only [Bool.and_eq_true, Bool.not_eq_false, decide_eq_true_eq] at h
        exact h.1.1 h.2)
      (fun x => by
        by_contra h
        simp only [Bool.and_eq_true, Bool.not_eq_false, decide_eq_true_eq] at h
        exact h.1.1 h.2)
  have h3way := h3 (List.finRange n)
  simp only [List.length_finRange] at h3way
  have hcc : ((List.finRange n).filter (fun p => decide (p ∈ s.corrupted))).length
      ≤ s.corrupted.length :=
    nodup_sub_length ((finRange_nodup n).sublist List.filter_sublist)
      (fun x hx => by simp only [List.mem_filter, List.mem_finRange, decide_eq_true_eq,
        true_and] at hx; exact hx)
  have hcc_eq : ((List.finRange n).filter (fun p => decide (p ∈ s.corrupted))).length
      = s.corrupted.length := by
    rw [Nat.le_antisymm hcc ?_]
    exact nodup_sub_length hnodup (fun x hx => by
      simp only [List.mem_filter, List.mem_finRange,
      decide_eq_true_eq, true_and]; exact hx)
  omega

/-- `initSupport` depends only on `corrupted` and `sendRecv`. -/
theorem initSupport_congr {n : Nat} {Value : Type} [DecidableEq Value]
    {s₁ s₂ : BRB_LTS.State n Value}
    (hcorr : s₁.corrupted = s₂.corrupted)
    (hrecv : ∀ p, (s₁.local_ p).sendRecv = (s₂.local_ p).sendRecv) :
    ∀ v, initSupport n Value s₁ v = initSupport n Value s₂ v := by
  intro v; unfold initSupport; rw [hcorr]; congr 1
  exact congrArg List.length (List.filter_congr (fun p _ => by rw [hrecv p]))

/-- After a corrupt step, `initSupport` is monotone. -/
theorem initSupport_corrupt_mono {n f : Nat} {Value : Type} [DecidableEq Value]
    {s s' : BRB_LTS.State n Value} {i} {sender : Fin n}
    (h : (BRB_LTS.brb n f Value sender).step s (.corrupt i) s') :
    ∀ w, initSupport n Value s w ≤ initSupport n Value s' w := by
  intro w
  have hcc := BRB_LTS.corrupt_corrupted h
  have hcl := BRB_LTS.corrupt_local h
  unfold initSupport; rw [hcc]; simp [List.length_cons]
  simp only [show ∀ p, s'.local_ p = s.local_ p from hcl]
  have hdec : (List.filter (fun p =>
      !decide (p ∈ s.corrupted) && decide ((s.local_ p).sendRecv = some w))
      (List.finRange n)).length ≤
    (List.filter (fun p =>
    !decide (p = i) && !decide (p ∈ s.corrupted) && decide ((s.local_ p).sendRecv = some w))
      (List.finRange n)).length + 1 := by
    have hsplit := filter_split
      (fun p => !decide (p ∈ s.corrupted) && decide ((s.local_ p).sendRecv = some w))
      (fun p : Fin n => !decide (p = i))
      (List.finRange n)
    have hone : (List.filter (fun x =>
        !decide (x ∈ s.corrupted) && decide ((s.local_ x).sendRecv = some w) && !!decide (x = i))
        (List.finRange n)).length ≤ 1 := by
      apply Nat.le_trans (filter_and_le _ _ _)
      simp only [Bool.not_not]
      have : ∀ x : Fin n, decide (x = i) = decide (x ∈ ([i] : List (Fin n))) := by intro x; simp
      simp only [this]; exact Nat.le_trans (filter_mem_le [i]) (by simp)
    have hcomm : (List.filter (fun x =>
        !decide (x ∈ s.corrupted) && decide ((s.local_ x).sendRecv = some w) && !decide (x = i))
        (List.finRange n)).length =
      (List.filter (fun p =>
      !decide (p = i) && !decide (p ∈ s.corrupted) && decide ((s.local_ p).sendRecv = some w))
        (List.finRange n)).length := by
      apply congrArg List.length; apply List.filter_congr
      intro p _; simp [Bool.and_comm, Bool.and_assoc]
    omega
  omega

/-- `initSupport` is monotone across steps. -/
theorem step_initSupport_mono {n f : Nat} {Value : Type} [DecidableEq Value]
    {s s' : BRB_LTS.State n Value} {l : BRB_LTS.Label n Value} {sender : Fin n}
    (h : (BRB_LTS.brb n f Value sender).step s l s') :
    ∀ w, initSupport n Value s w ≤ initSupport n Value s' w := by
  match l with
  | .corrupt _ => exact initSupport_corrupt_mono h
  | .send .. =>
    intro w; rw [initSupport_congr (BRB_LTS.send_corrupted h) (BRB_LTS.send_sendRecv h)]
  | .recv _ _ .init _ =>
    intro w
    have hc := BRB_LTS.recv_init_corrupted h
    unfold initSupport; rw [hc]
    apply Nat.add_le_add_left
    apply filter_length_mono
    intro p hp; simp only [Bool.decide_and, decide_not, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_false_iff_not, decide_eq_true_eq] at hp ⊢
    exact ⟨hp.1, BRB_LTS.recv_init_sendRecv_some h p w hp.2⟩
  | .recv _ _ .echo _ =>
    intro w; rw [initSupport_congr (BRB_LTS.recv_echo_corrupted h) (BRB_LTS.recv_echo_sendRecv h)]
  | .recv _ _ .vote _ =>
    intro w; rw [initSupport_congr (BRB_LTS.recv_vote_corrupted h) (BRB_LTS.recv_vote_sendRecv h)]
  | .output .. =>
    intro w; rw [initSupport_congr (BRB_LTS.output_corrupted h) (BRB_LTS.output_sendRecv h)]
  | .input .. =>
    intro w; rw [initSupport_congr (BRB_LTS.input_corrupted h) (BRB_LTS.input_sendRecv h)]

/-- `initSupport` is monotone after `recv init`. -/
theorem initSupport_recv_init_mono {n f : Nat} {Value : Type} [DecidableEq Value]
    {s s' : BRB_LTS.State n Value} {src dst v} {sender : Fin n}
    (h : (BRB_LTS.brb n f Value sender).step s (.recv src dst .init v) s') :
    ∀ w, initSupport n Value s w ≤ initSupport n Value s' w :=
  step_initSupport_mono h

/-- `initSupport w` is unchanged by `recv init v` when `w ≠ v`. -/
theorem initSupport_recv_init_other {n f : Nat} {Value : Type} [DecidableEq Value]
    {s s' : BRB_LTS.State n Value} {src dst v} {sender : Fin n}
    (h : (BRB_LTS.brb n f Value sender).step s (.recv src dst .init v) s')
    (w : Value) (hw : w ≠ v) :
    initSupport n Value s' w = initSupport n Value s w := by
  apply Nat.le_antisymm
  · have hc := BRB_LTS.recv_init_corrupted h
    unfold initSupport; rw [hc]
    apply Nat.add_le_add_left
    apply filter_length_mono
    intro p hp; simp only [Bool.decide_and, decide_not, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_false_iff_not, decide_eq_true_eq] at hp ⊢
    exact ⟨hp.1, BRB_LTS.recv_init_sendRecv_other h p w hw hp.2⟩
  · exact step_initSupport_mono h w

/-- sim_rel preserved when all relevant fields are unchanged. -/
def sim_rel_preserved_trivial
    {n f : Nat} {Value : Type} [DecidableEq Value] [Inhabited Value] {sender : Fin n}
    {s_r s_r' : BRB_LTS.State n Value} {s_i : IdealBRB.State n Value}
    (hR : sim_rel n f Value sender s_r s_i)
    (hc : s_r'.corrupted = s_r.corrupted)
    (hs : ∀ p, (s_r'.local_ p).sendRecv = (s_r.local_ p).sendRecv)
    (hb : ∀ p, (s_r'.local_ p).broadcastVal = (s_r.local_ p).broadcastVal)
    (hr : ∀ p, (s_r'.local_ p).returned = (s_r.local_ p).returned) :
    Σ' s₂', InternalStar (IdealBRB.ideal_brb n f Value sender)
      (IdealBRB.ideal_labelling n Value) s_i s₂' ×'
      sim_rel n f Value sender s_r' s₂' :=
  let ⟨h1, h2, h3, h4⟩ := hR
  ⟨s_i, .refl, h1.trans hc.symm, h2.trans (hb sender).symm,
   fun p hp => by
     have hp' : BRB_LTS.isCorrect n Value s_r p := by
       simp only [BRB_LTS.isCorrect, hc] at hp; exact hp
     rw [h3 p hp', hr],
   fun w => by rw [initSupport_congr hc hs]; exact h4 w⟩


/-! ### Invariants of the Real BRB -/

private def brb_corruption_spec {n f : Nat} {Value : Type} [DecidableEq Value]
    (sender : Fin n) : CorruptionInvariants.CorruptionSpec
    (BRB_LTS.brb n f Value sender) (fun s => s.corrupted) f where
  init_empty := fun _ ⟨_, _, hc⟩ => hc
  step_corrupted := fun s l s' h => by
    match l with
    | .corrupt i => obtain ⟨hci, hb, rfl⟩ := h; right; exact ⟨i, rfl, hci, hb⟩
    | .send .. => left; exact BRB_LTS.send_corrupted h
    | .recv _ _ .init _ => left; exact BRB_LTS.recv_init_corrupted h
    | .recv _ _ .echo _ => left; exact BRB_LTS.recv_echo_corrupted h
    | .recv _ _ .vote _ => left; exact BRB_LTS.recv_vote_corrupted h
    | .output .. => left; exact BRB_LTS.output_corrupted h
    | .input .. => left; exact BRB_LTS.input_corrupted h

theorem corrupted_budget {n f : Nat} {Value : Type} [DecidableEq Value]
    {sender : Fin n} {s : BRB_LTS.State n Value}
    (hreach : LTS.Reachable (BRB_LTS.brb n f Value sender) s) :
    s.corrupted.length ≤ f :=
  CorruptionInvariants.corrupted_budget (brb_corruption_spec sender) hreach

theorem corrupted_nodup {n f : Nat} {Value : Type} [DecidableEq Value]
    {sender : Fin n} {s : BRB_LTS.State n Value}
    (hreach : LTS.Reachable (BRB_LTS.brb n f Value sender) s) :
    s.corrupted.Nodup :=
  CorruptionInvariants.corrupted_nodup (brb_corruption_spec sender) hreach

/-- Buffer init from correct sender implies `sender.broadcastVal = some v`. -/
theorem buffer_init_consistent {n f : Nat} {Value : Type} [DecidableEq Value]
    {sender : Fin n} {s : BRB_LTS.State n Value}
    (hreach : LTS.Reachable (BRB_LTS.brb n f Value sender) s)
    (hcorr_s : BRB_LTS.isCorrect n Value s sender)
    (dst : Fin n) (v : Value)
    (hbuf : s.buffer ⟨sender, dst, .init, v⟩ = true) :
    (s.local_ sender).broadcastVal = some v := by
  induction hreach with
  | init hinit =>
    obtain ⟨_, hbuf_empty, _⟩ := hinit
    simp [hbuf_empty] at hbuf
  | step _ hstep ih =>
    have hcp := BRB_LTS.step_correct_prev hstep sender hcorr_s
    rename_i _ l _ _
    match l with
    | BRB_LTS.Label.corrupt _ =>
      rw [BRB_LTS.corrupt_buffer hstep] at hbuf
      rw [BRB_LTS.corrupt_local hstep sender]
      exact ih hcp hbuf
    | BRB_LTS.Label.send src dst' t mv =>
      rw [BRB_LTS.send_broadcastVal hstep]
      rcases BRB_LTS.send_buffer hstep ⟨sender, dst, .init, v⟩ hbuf with hmsg | hold
      · simp only [BRB_LTS.Message.mk.injEq] at hmsg
        obtain ⟨rfl, _, rfl, rfl⟩ := hmsg
        obtain ⟨hgate, _⟩ := hstep
        rcases hgate with hbyz | ⟨_, _, _, hbv⟩
        · exact absurd hbyz hcp
        · exact hbv
      · exact ih hcp hold
    | BRB_LTS.Label.recv _ _ .init _ =>
      rw [BRB_LTS.recv_init_broadcastVal hstep sender]
      exact ih hcp (BRB_LTS.recv_init_buffer hstep _ hbuf).2
    | BRB_LTS.Label.recv _ _ .echo _ =>
      rw [BRB_LTS.recv_echo_broadcastVal hstep sender]
      exact ih hcp (BRB_LTS.recv_echo_buffer hstep _ hbuf).2
    | BRB_LTS.Label.recv _ _ .vote _ =>
      rw [BRB_LTS.recv_vote_broadcastVal hstep sender]
      exact ih hcp (BRB_LTS.recv_vote_buffer hstep _ hbuf).2
    | BRB_LTS.Label.output _ _ =>
      rw [BRB_LTS.output_buffer hstep] at hbuf
      rw [BRB_LTS.output_broadcastVal hstep sender]
      exact ih hcp hbuf
    | BRB_LTS.Label.input _ _ =>
      rw [BRB_LTS.input_buffer hstep] at hbuf
      have := ih hcp hbuf
      rw [BRB_LTS.input_broadcastVal hstep]
      obtain ⟨rfl, hbn, _⟩ := hstep; rw [hbn] at this; contradiction

/-- Buffer echo(v) from correct src implies `src.echoed = some v`. -/
theorem buffer_echo_consistent {n f : Nat} {Value : Type} [DecidableEq Value]
    {sender : Fin n} {s : BRB_LTS.State n Value}
    (hreach : LTS.Reachable (BRB_LTS.brb n f Value sender) s)
    (src dst : Fin n) (v : Value)
    (hcorr_src : BRB_LTS.isCorrect n Value s src)
    (hbuf : s.buffer ⟨src, dst, .echo, v⟩ = true) :
    (s.local_ src).echoed = some v := by
  induction hreach with
  | init hinit => obtain ⟨_, hbe, _⟩ := hinit; simp [hbe] at hbuf
  | step _ hstep ih =>
    have hcp := BRB_LTS.step_correct_prev hstep src hcorr_src
    rename_i _ l _ _
    match l with
    | BRB_LTS.Label.corrupt _ =>
      rw [BRB_LTS.corrupt_buffer hstep] at hbuf
      rw [BRB_LTS.corrupt_local hstep src]
      exact ih hcp hbuf
    | BRB_LTS.Label.send src' dst' t mv =>
      rcases BRB_LTS.send_buffer hstep ⟨src, dst, .echo, v⟩ hbuf with hmsg | hold
      · simp only [BRB_LTS.Message.mk.injEq] at hmsg
        obtain ⟨rfl, _, rfl, rfl⟩ := hmsg
        exact BRB_LTS.send_echo_sets_echoed hstep hcp
      · exact BRB_LTS.step_echoed hstep src v (ih hcp hold)
    | BRB_LTS.Label.recv _ _ .init _ =>
      exact BRB_LTS.step_echoed hstep src v (ih hcp (BRB_LTS.recv_init_buffer hstep _ hbuf).2)
    | BRB_LTS.Label.recv _ _ .echo _ =>
      exact BRB_LTS.step_echoed hstep src v (ih hcp (BRB_LTS.recv_echo_buffer hstep _ hbuf).2)
    | BRB_LTS.Label.recv _ _ .vote _ =>
      exact BRB_LTS.step_echoed hstep src v (ih hcp (BRB_LTS.recv_vote_buffer hstep _ hbuf).2)
    | BRB_LTS.Label.output _ _ =>
      rw [BRB_LTS.output_buffer hstep] at hbuf
      exact BRB_LTS.step_echoed hstep src v (ih hcp hbuf)
    | BRB_LTS.Label.input _ _ =>
      rw [BRB_LTS.input_buffer hstep] at hbuf
      exact BRB_LTS.step_echoed hstep src v (ih hcp hbuf)

/-- Buffer vote(v) from correct src implies `src.voted v`. -/
theorem buffer_vote_consistent {n f : Nat} {Value : Type} [DecidableEq Value]
    {sender : Fin n} {s : BRB_LTS.State n Value}
    (hreach : LTS.Reachable (BRB_LTS.brb n f Value sender) s)
    (src dst : Fin n) (v : Value)
    (hcorr_src : BRB_LTS.isCorrect n Value s src)
    (hbuf : s.buffer ⟨src, dst, .vote, v⟩ = true) :
    (s.local_ src).voted v = true := by
  induction hreach with
  | init hinit => obtain ⟨_, hbe, _⟩ := hinit; simp [hbe] at hbuf
  | step _ hstep ih =>
    have hcp := BRB_LTS.step_correct_prev hstep src hcorr_src
    rename_i _ l _ _
    match l with
    | BRB_LTS.Label.corrupt _ =>
      rw [BRB_LTS.corrupt_buffer hstep] at hbuf
      rw [BRB_LTS.corrupt_local hstep src]; exact ih hcp hbuf
    | BRB_LTS.Label.send src' dst' t mv =>
      rcases BRB_LTS.send_buffer hstep ⟨src, dst, .vote, v⟩ hbuf with hmsg | hold
      · simp only [BRB_LTS.Message.mk.injEq] at hmsg
        obtain ⟨rfl, _, rfl, rfl⟩ := hmsg
        exact BRB_LTS.send_vote_sets_voted hstep hcp
      · exact BRB_LTS.step_voted hstep src v (ih hcp hold)
    | BRB_LTS.Label.recv _ _ .init _ =>
      exact BRB_LTS.step_voted hstep src v (ih hcp (BRB_LTS.recv_init_buffer hstep _ hbuf).2)
    | BRB_LTS.Label.recv _ _ .echo _ =>
      exact BRB_LTS.step_voted hstep src v (ih hcp (BRB_LTS.recv_echo_buffer hstep _ hbuf).2)
    | BRB_LTS.Label.recv _ _ .vote _ =>
      exact BRB_LTS.step_voted hstep src v (ih hcp (BRB_LTS.recv_vote_buffer hstep _ hbuf).2)
    | BRB_LTS.Label.output _ _ =>
      rw [BRB_LTS.output_buffer hstep] at hbuf
      exact BRB_LTS.step_voted hstep src v (ih hcp hbuf)
    | BRB_LTS.Label.input _ _ =>
      rw [BRB_LTS.input_buffer hstep] at hbuf
      exact BRB_LTS.step_voted hstep src v (ih hcp hbuf)

/-- Correct `sendRecv = some v` implies `sender.broadcastVal = some v`. -/
theorem init_trace {n f : Nat} {Value : Type} [DecidableEq Value]
    {sender : Fin n} {s : BRB_LTS.State n Value}
    (hreach : LTS.Reachable (BRB_LTS.brb n f Value sender) s)
    (hcorr_s : BRB_LTS.isCorrect n Value s sender)
    (p : Fin n) (v : Value)
    (hcorr_p : BRB_LTS.isCorrect n Value s p)
    (hrecv : (s.local_ p).sendRecv = some v) :
    (s.local_ sender).broadcastVal = some v := by
  induction hreach with
  | init hinit =>
    obtain ⟨hlocal, _, _⟩ := hinit
    simp [hlocal p, BRB_LTS.LocalState.init] at hrecv
  | step hreach_prev hstep ih =>
    have hcp_s := BRB_LTS.step_correct_prev hstep sender hcorr_s
    have hcp_p := BRB_LTS.step_correct_prev hstep p hcorr_p
    rename_i s' l _
    match l with
    | BRB_LTS.Label.corrupt _ =>
      rw [BRB_LTS.corrupt_local hstep] at hrecv ⊢; exact ih hcp_s hcp_p hrecv
    | BRB_LTS.Label.send _ _ _ _ =>
      rw [BRB_LTS.send_broadcastVal hstep, BRB_LTS.send_sendRecv hstep] at *
      exact ih hcp_s hcp_p hrecv
    | BRB_LTS.Label.recv src dst .init mv =>
      rw [BRB_LTS.recv_init_broadcastVal hstep sender]
      by_cases hvm : v = mv
      · -- v = mv: sendRecv p may have been set by this step
        subst hvm
        obtain ⟨hbuf_old, hs'⟩ := hstep
        subst hs'
        simp only at hrecv
        by_cases heq : p = dst
        · subst heq
          simp only [↓reduceIte] at hrecv
          by_cases hcond : src = sender ∧ (s'.local_ p).sendRecv = none
          · -- sendRecv was none, set to some v. src = sender.
            rw [hcond.1] at hbuf_old
            exact buffer_init_consistent hreach_prev hcp_s p v hbuf_old
          · -- sendRecv unchanged (condition not met)
            simp only [hcond] at hrecv
            exact ih hcp_s hcp_p hrecv
        · -- p ≠ dst: sendRecv unchanged
          simp only [heq] at hrecv
          exact ih hcp_s hcp_p hrecv
      · -- v ≠ mv: sendRecv for value v is unchanged
        have := BRB_LTS.recv_init_sendRecv_other hstep p v hvm hrecv
        exact ih hcp_s hcp_p this
    | BRB_LTS.Label.recv _ _ .echo _ =>
      rw [BRB_LTS.recv_echo_broadcastVal hstep, BRB_LTS.recv_echo_sendRecv hstep] at *
      exact ih hcp_s hcp_p hrecv
    | BRB_LTS.Label.recv _ _ .vote _ =>
      rw [BRB_LTS.recv_vote_broadcastVal hstep, BRB_LTS.recv_vote_sendRecv hstep] at *
      exact ih hcp_s hcp_p hrecv
    | BRB_LTS.Label.output _ _ =>
      rw [BRB_LTS.output_broadcastVal hstep, BRB_LTS.output_sendRecv hstep] at *
      exact ih hcp_s hcp_p hrecv
    | BRB_LTS.Label.input _ _ =>
      rw [BRB_LTS.input_sendRecv hstep] at hrecv
      rw [BRB_LTS.input_broadcastVal hstep]
      have := ih hcp_s hcp_p hrecv
      obtain ⟨rfl, hbn, _⟩ := hstep; rw [hbn] at this; contradiction

/-- `echoRecv p q v` and q correct implies `q.echoed = some v`. -/
theorem echo_trace {n f : Nat} {Value : Type} [DecidableEq Value]
    {sender : Fin n} {s : BRB_LTS.State n Value}
    (hreach : LTS.Reachable (BRB_LTS.brb n f Value sender) s)
    (p q : Fin n) (v : Value)
    (hcorr_q : BRB_LTS.isCorrect n Value s q)
    (hrecv : (s.local_ p).echoRecv q v = true) :
    (s.local_ q).echoed = some v := by
  induction hreach with
  | init hinit =>
    obtain ⟨hlocal, _, _⟩ := hinit
    simp [hlocal p, BRB_LTS.LocalState.init] at hrecv
  | step hreach_prev hstep ih =>
    have hcpq := BRB_LTS.step_correct_prev hstep q hcorr_q
    rename_i s_prev l _
    match l with
    | BRB_LTS.Label.recv src dst .echo mv =>
      by_cases hentry : p = dst ∧ q = src ∧ v = mv
      · obtain ⟨rfl, rfl, rfl⟩ := hentry
        have hstep' := hstep
        obtain ⟨hbuf_old, _⟩ := hstep
        exact BRB_LTS.step_echoed hstep' q v
          (buffer_echo_consistent hreach_prev q p v hcpq hbuf_old)
      · have hprev := BRB_LTS.step_echoRecv_prev hstep p q v hrecv
          (by intro src' dst' mv' h; simp only [BRB_LTS.Label.recv.injEq] at h
              obtain ⟨rfl, rfl, _, rfl⟩ := h; exact hentry)
        exact BRB_LTS.step_echoed hstep q v (ih hcpq hprev)
    | BRB_LTS.Label.corrupt _ | BRB_LTS.Label.send ..
    | BRB_LTS.Label.recv _ _ .init _ | BRB_LTS.Label.recv _ _ .vote _
    | BRB_LTS.Label.output .. | BRB_LTS.Label.input .. =>
      have hprev := BRB_LTS.step_echoRecv_prev hstep p q v hrecv
        (by intro src dst mv h; simp at h)
      exact BRB_LTS.step_echoed hstep q v (ih hcpq hprev)

/-- `voteRecv p q v` and q correct implies `q.voted v`. -/
theorem vote_trace {n f : Nat} {Value : Type} [DecidableEq Value]
    {sender : Fin n} {s : BRB_LTS.State n Value}
    (hreach : LTS.Reachable (BRB_LTS.brb n f Value sender) s)
    (p q : Fin n) (v : Value)
    (hcorr_q : BRB_LTS.isCorrect n Value s q)
    (hrecv : (s.local_ p).voteRecv q v = true) :
    (s.local_ q).voted v = true := by
  induction hreach with
  | init hinit =>
    obtain ⟨hlocal, _, _⟩ := hinit
    simp [hlocal p, BRB_LTS.LocalState.init] at hrecv
  | step hreach_prev hstep ih =>
    have hcpq := BRB_LTS.step_correct_prev hstep q hcorr_q
    rename_i s_prev l _
    match l with
    | BRB_LTS.Label.recv src dst .vote mv =>
      by_cases hentry : p = dst ∧ q = src ∧ v = mv
      · obtain ⟨rfl, rfl, rfl⟩ := hentry
        have hstep' := hstep
        obtain ⟨hbuf_old, _⟩ := hstep
        exact BRB_LTS.step_voted hstep' q v
          (buffer_vote_consistent hreach_prev q p v hcpq hbuf_old)
      · have hprev := BRB_LTS.step_voteRecv_prev hstep p q v hrecv
          (by intro src' dst' mv' h; simp only [BRB_LTS.Label.recv.injEq] at h
              obtain ⟨rfl, rfl, _, rfl⟩ := h; exact hentry)
        exact BRB_LTS.step_voted hstep q v (ih hcpq hprev)
    | BRB_LTS.Label.corrupt _ | BRB_LTS.Label.send ..
    | BRB_LTS.Label.recv _ _ .init _ | BRB_LTS.Label.recv _ _ .echo _
    | BRB_LTS.Label.output .. | BRB_LTS.Label.input .. =>
      have hprev := BRB_LTS.step_voteRecv_prev hstep p q v hrecv
        (by intro src dst mv h; simp at h)
      exact BRB_LTS.step_voted hstep q v (ih hcpq hprev)

/-- `echoed = some v` implies `sendRecv = some v` for correct processes. -/
theorem echoed_implies_sendRecv {n f : Nat} {Value : Type} [DecidableEq Value]
    {sender : Fin n} {s : BRB_LTS.State n Value}
    (hreach : LTS.Reachable (BRB_LTS.brb n f Value sender) s)
    (p : Fin n) (v : Value)
    (hcorr_p : BRB_LTS.isCorrect n Value s p)
    (hechoed : (s.local_ p).echoed = some v) :
    (s.local_ p).sendRecv = some v := by
  induction hreach with
  | init hinit =>
    obtain ⟨hlocal, _, _⟩ := hinit
    simp [hlocal p, BRB_LTS.LocalState.init] at hechoed
  | step hreach_prev hstep ih =>
    have hcp := BRB_LTS.step_correct_prev hstep p hcorr_p
    rename_i s_prev l _
    match l with
    | BRB_LTS.Label.send src _ .echo mv =>
      by_cases hentry : p = src ∧ v = mv
      · -- p just echoed v. The gate requires echoed = some v OR (echoed = none ∧ sendRecv = some v)
        obtain ⟨rfl, rfl⟩ := hentry
        have hstep' := hstep
        obtain ⟨hgate, _⟩ := hstep
        rcases hgate with hbyz | ⟨_, _, hecho_reason⟩
        · exact absurd hbyz hcp
        · rcases hecho_reason with hev | ⟨_, hsrecv⟩
          · -- echoed was already some v → ih gives sendRecv = some v in pre → preserved
            rw [BRB_LTS.send_sendRecv hstep' p]; exact ih hcp hev
          · -- sendRecv = some v already in pre → preserved
            rw [BRB_LTS.send_sendRecv hstep' p]; exact hsrecv
      · -- p didn't echo this step. echoed unchanged. sendRecv unchanged by send.
        have hprev := BRB_LTS.step_echoed_prev hstep p v hechoed (by
          intro d h; simp only [BRB_LTS.Label.send.injEq] at h;
          exact hentry ⟨h.1.symm, h.2.2.2.symm⟩)
        rw [BRB_LTS.send_sendRecv hstep p]; exact ih hcp hprev
    | BRB_LTS.Label.corrupt _ | BRB_LTS.Label.send _ _ .init _
    | BRB_LTS.Label.send _ _ .vote _ | BRB_LTS.Label.recv ..
    | BRB_LTS.Label.output .. | BRB_LTS.Label.input .. =>
      have hprev := BRB_LTS.step_echoed_prev hstep p v hechoed
        (by intro d h; simp at h)
      exact BRB_LTS.step_sendRecv_mono hstep p v (ih hcp hprev)

/-- If any correct process voted for `v`, some process has echo quorum for `v`. -/
theorem echo_witness {n f : Nat} {Value : Type} [DecidableEq Value]
    {sender : Fin n} {s : BRB_LTS.State n Value}
    (hreach : LTS.Reachable (BRB_LTS.brb n f Value sender) s)
    (v : Value)
    (hvoted : ∃ p, BRB_LTS.isCorrect n Value s p ∧ (s.local_ p).voted v = true) :
    ∃ q, BRB_LTS.countEchoRecv n Value (s.local_ q) v ≥ BRB_LTS.echoThreshold n f := by
  induction hreach with
  | init hinit =>
    obtain ⟨p, _, hvp⟩ := hvoted
    obtain ⟨hlocal, _, _⟩ := hinit
    simp [hlocal p, BRB_LTS.LocalState.init] at hvp
  | step hreach_prev hstep ih =>
    obtain ⟨p, hcorr_p, hvp⟩ := hvoted
    have hcp := BRB_LTS.step_correct_prev hstep p hcorr_p
    rename_i s_prev l _
    match l with
    | BRB_LTS.Label.send src _ .vote mv =>
      by_cases hsrc : p = src ∧ v = mv
      · -- p = src, v = mv: p may have just voted.
        obtain ⟨rfl, rfl⟩ := hsrc
        have hstep' := hstep
        obtain ⟨hgate, _⟩ := hstep
        rcases hgate with hbyz | ⟨_, _, hvote_reason⟩
        · -- src is byzantine — but hcp says p is correct in pre-state, contradiction
          exact absurd hbyz hcp
        · -- src is correct. Why did it vote?
          rcases hvote_reason with hvoted_already | hecho_quorum | hvote_amp
          · -- already voted: use ih
            obtain ⟨q, hq⟩ := ih ⟨p, hcp, hvoted_already⟩
            exact ⟨q, Nat.le_trans hq (BRB_LTS.step_countEchoRecv_mono hstep' q v)⟩
          · -- countEchoRecv ≥ n-f: witness is p itself
            exact ⟨p, Nat.le_trans hecho_quorum (BRB_LTS.step_countEchoRecv_mono hstep' p v)⟩
          · -- vote amplification: countVoteRecv ≥ f+1.
            have hbudget := corrupted_budget hreach_prev
            have hvlt : s_prev.corrupted.length <
              ((List.finRange n).filter ((s_prev.local_ p).voteRecv · v)).length := by
              unfold BRB_LTS.countVoteRecv BRB_LTS.voteThreshold at hvote_amp; omega
            obtain ⟨q, hqvote, hqcorr⟩ := pigeonhole_filter _ s_prev.corrupted hvlt
            have hqvoted := vote_trace hreach_prev p q v hqcorr hqvote
            obtain ⟨w, hw⟩ := ih ⟨q, hqcorr, hqvoted⟩
            exact ⟨w, Nat.le_trans hw (BRB_LTS.step_countEchoRecv_mono hstep' w v)⟩
      · -- p ≠ src or v ≠ mv: voted p v was already true in pre-state
        have hvp_prev := BRB_LTS.step_voted_prev hstep p v hvp (by
          intro dst h; simp only [BRB_LTS.Label.send.injEq] at h;
          exact hsrc ⟨h.1.symm, h.2.2.2.symm⟩)
        obtain ⟨q, hq⟩ := ih ⟨p, hcp, hvp_prev⟩
        exact ⟨q, Nat.le_trans hq (BRB_LTS.step_countEchoRecv_mono hstep q v)⟩
    | BRB_LTS.Label.corrupt _ | BRB_LTS.Label.send _ _ .init _
    | BRB_LTS.Label.send _ _ .echo _ | BRB_LTS.Label.recv ..
    | BRB_LTS.Label.output .. | BRB_LTS.Label.input .. =>
      have hvp_prev := BRB_LTS.step_voted_prev hstep p v hvp (by intro dst h; simp at h)
      obtain ⟨q, hq⟩ := ih ⟨p, hcp, hvp_prev⟩
      exact ⟨q, Nat.le_trans hq (BRB_LTS.step_countEchoRecv_mono hstep q v)⟩

/-- `voted v` implies `initSupport(v) ≥ n-f`. -/
theorem voted_implies_initSupport {n f : Nat} {Value : Type} [DecidableEq Value]
    {sender : Fin n} {s : BRB_LTS.State n Value}
    (hreach : LTS.Reachable (BRB_LTS.brb n f Value sender) s)
    (p : Fin n) (v : Value)
    (hcorr_p : BRB_LTS.isCorrect n Value s p)
    (hvoted : (s.local_ p).voted v = true) :
    initSupport n Value s v ≥ BRB_LTS.echoThreshold n f := by
  obtain ⟨q, hecho_q⟩ := echo_witness hreach v ⟨p, hcorr_p, hvoted⟩
  unfold initSupport
  unfold BRB_LTS.countEchoRecv BRB_LTS.echoThreshold at hecho_q
  apply Nat.le_trans hecho_q
  apply Nat.le_trans (filter_length_mono
    (fun r => (s.local_ q).echoRecv r v)
    (fun r => decide (r ∈ s.corrupted) || decide (r ∉ s.corrupted ∧ (s.local_ r).sendRecv = some v))
    (List.finRange n)
    (fun r hr => by
      simp only [Bool.decide_and, decide_not, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
        Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hr ⊢
      by_cases hcr : r ∈ s.corrupted
      · left; exact hcr
      · right;
        exact ⟨hcr, echoed_implies_sendRecv hreach r v hcr (echo_trace hreach q r v hcr hr)⟩))
  have hor := filter_or_le
    (fun r => decide (r ∈ s.corrupted))
    (fun r => decide (r ∉ s.corrupted ∧ (s.local_ r).sendRecv = some v))
    (List.finRange n)
  exact Nat.le_trans hor (Nat.add_le_add_right (filter_mem_le s.corrupted) _)

/-- `returned = some v` implies `initSupport(v) ≥ n-f`. -/
theorem output_implies_initSupport {n f : Nat} {Value : Type} [DecidableEq Value]
    {sender : Fin n} {s : BRB_LTS.State n Value}
    (hreach : LTS.Reachable (BRB_LTS.brb n f Value sender) s)
    (hn : n > 3 * f)
    (p : Fin n) (v : Value)
    (hcorr_p : BRB_LTS.isCorrect n Value s p)
    (hret : (s.local_ p).returned = some v) :
    initSupport n Value s v ≥ BRB_LTS.echoThreshold n f := by
  induction hreach with
  | init hinit =>
    obtain ⟨hlocal, _, _⟩ := hinit
    simp [hlocal p, BRB_LTS.LocalState.init] at hret
  | step hreach_prev hstep ih =>
    have hcp := BRB_LTS.step_correct_prev hstep p hcorr_p
    have hmono := step_initSupport_mono hstep
    rename_i s' l _
    match l with
    | BRB_LTS.Label.output i w =>
      by_cases heq : p = i
      · -- p = i: just returned. Extract vote count from output guard.
        subst heq
        have hstep' := hstep
        obtain ⟨_, _, hvotes, _⟩ := hstep
        rw [initSupport_congr (BRB_LTS.output_corrupted hstep') (BRB_LTS.output_sendRecv hstep')]
        have hbudget := corrupted_budget hreach_prev
        have hlt : s'.corrupted.length <
          ((List.finRange n).filter ((s'.local_ p).voteRecv · w)).length := by
          unfold BRB_LTS.countVoteRecv BRB_LTS.returnThreshold at hvotes
          have : n > 3 * f := hn; omega
        obtain ⟨q, hqvote, hqcorr⟩ := pigeonhole_filter _ s'.corrupted hlt
        have hqvoted := vote_trace hreach_prev p q w hqcorr hqvote
        have hinit_w := voted_implies_initSupport hreach_prev q w hqcorr hqvoted
        have hvw : v = w := by
          rw [BRB_LTS.output_returned hstep' p] at hret; simp at hret; exact hret.symm
        rw [hvw]; exact hinit_w
      · -- p ≠ i: returned p unchanged, use ih + monotonicity
        have hret' : (s'.local_ p).returned = some v := by
          rw [BRB_LTS.output_returned hstep p] at hret
          simp only [heq] at hret; exact hret
        exact Nat.le_trans (ih hcp hret') (hmono v)
    | BRB_LTS.Label.corrupt _ | BRB_LTS.Label.send ..
    | BRB_LTS.Label.recv .. | BRB_LTS.Label.input _ _ =>
      rw [BRB_LTS.step_returned hstep p (by intro _ _ h; simp at h)] at hret
      exact Nat.le_trans (ih hcp hret) (hmono v)

/-- If `initSupport v` newly crosses the threshold and uniqueness holds,
    then `set_up` was `none` before. -/
private theorem setup_none_of_new_crossing
    {n f : Nat} {Value : Type} [DecidableEq Value]
    {s_r' : BRB_LTS.State n Value} {s_i : IdealBRB.State n Value}
    (hn : n > 3 * f) (v : Value)
    (hbudget' : s_r'.corrupted.length ≤ f) (hnodup' : s_r'.corrupted.Nodup)
    (hcross : initSupport n Value s_r' v ≥ BRB_LTS.echoThreshold n f)
    (hold_v : s_i.set_up = some v → False)
    (hmono : ∀ w, s_i.set_up = some w → initSupport n Value s_r' w ≥ BRB_LTS.echoThreshold n f)
    : s_i.set_up = none := by
  match hsu : s_i.set_up with
  | none => rfl
  | some w =>
    have hwne : w ≠ v := fun heq => hold_v (heq ▸ hsu)
    exact absurd (initSupport_unique hn s_r' hbudget' hnodup' v w hcross (hmono w hsu)).symm hwne

/-! ### Forward Simulation -/

/-- The forward simulation from real BRB to ideal BRB. -/
def brb_forward_sim [Inhabited Value] [Inhabited (Fin n)] (hn : n > 3 * f) :
    ForwardSim
      (BRB_LTS.brb n f Value sender) (BRB_LTS.brb_labelling n Value)
      (IdealBRB.ideal_brb n f Value sender) (IdealBRB.ideal_labelling n Value) where
  R := sim_rel n f Value sender
  label_map := label_map n Value
  init_sim := by
    intro s_r ⟨hlocal, _, hcorr⟩
    refine ⟨⟨[], none, none, fun _ => none⟩, ⟨rfl, rfl, rfl, fun _ => rfl⟩, ?_⟩
    simp only [sim_rel]
    refine ⟨hcorr.symm, ?_, ?_, ?_⟩
    · -- broadcastVal agrees
      simp only [hlocal sender, BRB_LTS.LocalState.init]
    · -- returned agrees
      intro p _; simp only [hlocal p, BRB_LTS.LocalState.init]
    · -- set_up iff
      intro v; constructor
      · intro h; contradiction
      · intro h
        exfalso
        simp only [initSupport, hcorr, BRB_LTS.echoThreshold] at h
        have : ∀ p, (s_r.local_ p).sendRecv ≠ some v := by
          intro p; simp [hlocal p, BRB_LTS.LocalState.init]
        have : (List.finRange n).filter (fun p =>
          (s_r.local_ p).sendRecv = some v) = [] :=
          List.filter_eq_nil_iff.mpr (fun p _ => by simp [this p])
        simp [this] at h
        omega
  step_internal := by
    intro s_r l s_r' s_i hreach hR hint hstep
    simp only [BRB_LTS.brb_labelling] at hint
    rcases l with _ | ⟨src, dst, t, v⟩ | ⟨src, dst, t, v⟩ | _ | _
    · -- corrupt: not internal
      exact absurd hint (by simp)
    · -- send: nothing relevant changes, ideal stays put.
      exact sim_rel_preserved_trivial hR
        (BRB_LTS.send_corrupted hstep)
        (BRB_LTS.send_sendRecv hstep)
        (BRB_LTS.send_broadcastVal hstep)
        (BRB_LTS.send_returned hstep)
    · -- recv
      rcases t with _ | _ | _
      · -- recv init: may change sendRecv of dst from none to some v.
        have hc := BRB_LTS.recv_init_corrupted hstep
        have hr := BRB_LTS.recv_init_returned hstep
        have hb := BRB_LTS.recv_init_broadcastVal hstep
        have hmono := initSupport_recv_init_mono hstep
        obtain ⟨h1, h2, h3, h4⟩ := hR
        by_cases hold : initSupport n Value s_r v ≥ BRB_LTS.echoThreshold n f
        · -- Already crossed: set_up = some v already, ideal stays put
          have hsetup_v : s_i.set_up = some v := (h4 v).mpr hold
          refine ⟨s_i, .refl, h1.trans hc.symm, h2.trans (hb sender).symm, ?_, ?_⟩
          · intro p hp
            have hp' : BRB_LTS.isCorrect n Value s_r p := by
              simp only [BRB_LTS.isCorrect] at hp ⊢; rwa [← hc]
            rw [h3 p hp', hr]
          · intro w; constructor
            · intro hw; exact Nat.le_trans ((h4 w).mp hw) (hmono w)
            · intro hw
              by_cases heq : w = v
              · exact heq ▸ hsetup_v
              · rw [initSupport_recv_init_other hstep w heq] at hw
                exact (h4 w).mpr hw
        · -- Not yet crossed for v in old state.
          by_cases hcross : initSupport n Value s_r' v ≥ BRB_LTS.echoThreshold n f
          · have hbudget : s_r'.corrupted.length ≤ f := by
              rw [hc]; exact corrupted_budget hreach
            have hnodup : s_r'.corrupted.Nodup := by
              rw [hc]; exact corrupted_nodup hreach
            have hsetup_none := setup_none_of_new_crossing hn v hbudget hnodup hcross
              (fun hw => hold ((h4 v).mp hw))
              (fun w hw => Nat.le_trans ((h4 w).mp hw) (hmono w))
            have hcommit_step : (IdealBRB.ideal_brb n f Value sender).step
                s_i (.commit v) { s_i with set_up := some v } := by
              simp only [IdealBRB.ideal_brb, Order.add_one_le_iff, hsetup_none, and_true, true_and]
              by_cases hcorr_s : BRB_LTS.isCorrect n Value s_r sender
              · -- sender correct: need broadcastVal = some v
                left
                exact ⟨by simp only [IdealBRB.isCorrect, h1]; exact hcorr_s,
                       by -- Need: s_i.broadcastVal = some v
                          rw [h2, ← hb sender]
                          have hreach' : LTS.Reachable (BRB_LTS.brb n f Value sender) s_r' :=
                            .step hreach hstep
                          have hcorr_s' : BRB_LTS.isCorrect n Value s_r' sender := by
                            simp only [BRB_LTS.isCorrect, hc]; exact hcorr_s
                          have hbudget' := corrupted_budget hreach'
                          unfold initSupport BRB_LTS.echoThreshold at hcross
                          have hfilt_pos : ((List.finRange n).filter (fun p => p ∉ s_r'.corrupted
                            ∧ (s_r'.local_ p).sendRecv = some v)).length > 0 := by
                            omega
                          obtain ⟨p, hp⟩ := List.exists_mem_of_length_pos hfilt_pos
                          simp only [Bool.decide_and, decide_not, List.mem_filter,
                            List.mem_finRange, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
                            Bool.not_true, decide_eq_false_iff_not, decide_eq_true_eq,
                            true_and] at hp
                          exact init_trace hreach' hcorr_s' p v hp.1 hp.2⟩
              · -- sender corrupt
                right
                simp only [IdealBRB.isCorrect, h1, BRB_LTS.isCorrect] at hcorr_s ⊢; exact hcorr_s
            refine ⟨{ s_i with set_up := some v },
                    InternalStar.single (by simp only [IdealBRB.ideal_labelling]) hcommit_step, ?_⟩
            · -- sim_rel preserved
              refine ⟨h1.trans hc.symm, h2.trans (hb sender).symm, ?_, ?_⟩
              · intro p hp
                have hp' : BRB_LTS.isCorrect n Value s_r p := by
                  simp only [BRB_LTS.isCorrect] at hp ⊢; rwa [← hc]
                rw [h3 p hp', hr]
              · intro w; simp only [Option.some.injEq, ge_iff_le]; constructor
                · intro hw; subst hw; exact hcross
                · intro hw
                  exact initSupport_unique hn s_r' hbudget hnodup v w hcross hw
          · -- Not crossed in s_r' either: stay put.
            refine ⟨s_i, .refl, h1.trans hc.symm, h2.trans (hb sender).symm, ?_, ?_⟩
            · intro p hp
              have hp' : BRB_LTS.isCorrect n Value s_r p := by
                simp only [BRB_LTS.isCorrect] at hp ⊢; rwa [← hc]
              rw [h3 p hp', hr]
            · intro w; constructor
              · intro hw; exact Nat.le_trans ((h4 w).mp hw) (hmono w)
              · intro hw
                by_cases heq : w = v
                · subst heq; exact absurd hw hcross
                · rw [initSupport_recv_init_other hstep w heq] at hw
                  exact (h4 w).mpr hw
      · -- recv echo: nothing relevant changes.
        exact sim_rel_preserved_trivial hR
          (BRB_LTS.recv_echo_corrupted hstep)
          (BRB_LTS.recv_echo_sendRecv hstep)
          (BRB_LTS.recv_echo_broadcastVal hstep)
          (BRB_LTS.recv_echo_returned hstep)
      · -- recv vote: nothing relevant changes.
        exact sim_rel_preserved_trivial hR
          (BRB_LTS.recv_vote_corrupted hstep)
          (BRB_LTS.recv_vote_sendRecv hstep)
          (BRB_LTS.recv_vote_broadcastVal hstep)
          (BRB_LTS.recv_vote_returned hstep)
    · -- output: not internal
      exact absurd hint (by simp)
    · -- input: not internal
      exact absurd hint (by simp)
  step_external := by
    intro s_r l s_r' s_i hreach hR hext hstep
    simp only [BRB_LTS.brb_labelling, Labelling.is_external] at hext
    rcases l with ⟨i⟩ | _ | _ | ⟨i, v⟩ | ⟨i, v⟩
    · -- corrupt i: corrupted grows by i.
      have hcl_dec := BRB_LTS.corrupt_local hstep
      have hbudget_dec : s_r'.corrupted.length ≤ f := by
        rw [BRB_LTS.corrupt_corrupted hstep]; simp only [List.length_cons]
        exact Nat.lt_of_lt_of_le (BRB_LTS.corrupt_budget hstep) (Nat.le_refl _)
      match hfnc : findNewCrossing f s_r s_r' with
      | some ⟨v, hcross_v, hold_v⟩ =>
        obtain ⟨h1, h2, h3, h4⟩ := hR
        have hcl := BRB_LTS.corrupt_local hstep
        have hcc := BRB_LTS.corrupt_corrupted hstep
        have hci := BRB_LTS.corrupt_isCorrect hstep
        have hcb := BRB_LTS.corrupt_budget hstep
        have hmono := initSupport_corrupt_mono hstep
        have hbudget := corrupted_budget hreach
        have hnodup := corrupted_nodup hreach
        have hbudget' : s_r'.corrupted.length ≤ f := by
          rw [hcc]; simp only [List.length_cons]; omega
        have hnodup' : s_r'.corrupted.Nodup := by rw [hcc]; exact List.nodup_cons.mpr ⟨hci, hnodup⟩
        have hsetup_none := setup_none_of_new_crossing hn v hbudget' hnodup' hcross_v
          (fun hw => hold_v ((h4 v).mp hw))
          (fun w hw => Nat.le_trans ((h4 w).mp hw) (hmono w))
        let s_i_mid := { s_i with set_up := some v }
        let s_i' := { s_i_mid with corrupted := i :: s_i_mid.corrupted }
        have hcommit_step : (IdealBRB.ideal_brb n f Value sender).step
            s_i (.commit v) s_i_mid := by
          simp only [IdealBRB.ideal_brb, Order.add_one_le_iff, hsetup_none, and_true, true_and,
            s_i_mid]
          by_cases hcorr_s : BRB_LTS.isCorrect n Value s_r sender
          · left
            refine ⟨by simp only [IdealBRB.isCorrect, h1]; exact hcorr_s, ?_⟩
            rw [h2]
            have hfilt_pos : ((List.finRange n).filter (fun p =>
              p ∉ s_r'.corrupted ∧ (s_r'.local_ p).sendRecv = some v)).length > 0 := by
              have hcross_v' : initSupport n Value s_r' v ≥ BRB_LTS.echoThreshold n f := hcross_v
              unfold initSupport BRB_LTS.echoThreshold at hcross_v'; omega
            obtain ⟨p, hp⟩ := List.exists_mem_of_length_pos hfilt_pos
            simp only [Bool.decide_and, decide_not, List.mem_filter, List.mem_finRange,
              Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
              decide_eq_true_eq, true_and] at hp
            have hp_corr : BRB_LTS.isCorrect n Value s_r p := by
              simp only [hcc, List.mem_cons, not_or] at hp; exact hp.1.2
            have hp_recv : (s_r.local_ p).sendRecv = some v := by
              rw [← hcl]; exact hp.2
            exact init_trace hreach hcorr_s p v hp_corr hp_recv
          · right
            simp only [IdealBRB.isCorrect, h1, BRB_LTS.isCorrect] at hcorr_s ⊢; exact hcorr_s
        have hcorrupt_step : (IdealBRB.ideal_brb n f Value sender).step
            s_i_mid (label_map n Value (.corrupt i)) s_i' := by
          simp only [IdealBRB.ideal_brb, IdealBRB.isCorrect, Order.add_one_le_iff,
            Decidable.not_not, h1, label_map, and_true, s_i_mid, s_i']
          exact ⟨hci, hcb⟩
        refine ⟨s_i_mid, s_i', s_i',
                InternalStar.single (by simp only [IdealBRB.ideal_labelling]) hcommit_step,
                hcorrupt_step, .refl, ?_⟩
        refine ⟨by simp only [s_i', s_i_mid, hcc, h1], ?_, ?_, ?_⟩
        · simp only [s_i', s_i_mid, h2, hcl sender]
        · intro p hp
          have hp' : BRB_LTS.isCorrect n Value s_r p := by
            simp only [BRB_LTS.isCorrect, hcc, List.mem_cons, not_or] at hp; exact hp.2
          rw [show s_i'.returned p = s_i.returned p from rfl, h3 p hp', hcl]
        · intro w; simp only [Option.some.injEq, ge_iff_le, s_i_mid, s_i']; constructor
          · intro hw; subst hw; exact hcross_v
          · intro hw
            exact initSupport_unique hn s_r' hbudget' hnodup' v w hcross_v hw
      | none =>
        -- No threshold crossed: both InternalStar are refl. [Easy]
        have hcross : ∀ w, initSupport n Value s_r' w ≥ BRB_LTS.echoThreshold n f →
            ¬¬ initSupport n Value s_r w ≥ BRB_LTS.echoThreshold n f := by
          intro w hw hlt
          have := findNewCrossing_complete hn hbudget_dec hcl_dec ⟨w, hw, hlt⟩
          simp [hfnc] at this
        have hcl := BRB_LTS.corrupt_local hstep
        have hcc := BRB_LTS.corrupt_corrupted hstep
        have hci := BRB_LTS.corrupt_isCorrect hstep
        have hcb := BRB_LTS.corrupt_budget hstep
        have hmono := initSupport_corrupt_mono hstep
        obtain ⟨h1, h2, h3, h4⟩ := hR
        refine ⟨s_i, { s_i with corrupted := i :: s_i.corrupted },
                { s_i with corrupted := i :: s_i.corrupted }, .refl, ?_, .refl, ?_⟩
        · -- ideal corrupt step
          simp only [IdealBRB.ideal_brb, label_map, IdealBRB.isCorrect]
          simp only [h1, Order.add_one_le_iff, and_true]
          exact ⟨hci, hcb⟩
        · -- sim_rel preserved
          refine ⟨by simp only [hcc, h1], ?_, ?_, ?_⟩
          · simp only [h2, hcl sender]
          · intro p hp
            have hp' : BRB_LTS.isCorrect n Value s_r p := by
              simp only [BRB_LTS.isCorrect, hcc, List.mem_cons, not_or] at hp
              exact hp.2
            rw [h3 p hp', hcl]
          · intro w; constructor
            · intro hw; exact Nat.le_trans ((h4 w).mp hw) (hmono w)
            · intro hw
              exact (h4 w).mpr (Decidable.not_not.mp (hcross w hw))
    · -- send: not external
      exact absurd hext (by simp)
    · -- recv: not external
      exact absurd hext (by simp)
    · -- output i v: correct process i returns v.
      obtain ⟨h1, h2, h3, h4⟩ := hR
      have hreach' := LTS.Reachable.step hreach hstep
      have hcorr_i' : BRB_LTS.isCorrect n Value s_r' i := by
        obtain ⟨hci, _, _, rfl⟩ := hstep; exact hci
      have hret_i' : (s_r'.local_ i).returned = some v := by
        obtain ⟨_, _, _, rfl⟩ := hstep; simp
      have hinit := output_implies_initSupport hreach' hn i v hcorr_i' hret_i'
      have hisup : ∀ w, initSupport n Value s_r w = initSupport n Value s_r' w :=
        fun w =>
        (initSupport_congr (BRB_LTS.output_corrupted hstep) (BRB_LTS.output_sendRecv hstep) w).symm
      have hsetup_v : s_i.set_up = some v := (h4 v).mpr (by rw [hisup]; exact hinit)
      refine ⟨s_i, { s_i with returned := fun p => if p = i then some v else s_i.returned p },
              { s_i with returned := fun p => if p = i then some v else s_i.returned p },
              .refl, ?_, .refl, ?_⟩
      · -- ideal output step
        simp only [IdealBRB.ideal_brb, IdealBRB.isCorrect, Order.add_one_le_iff, Decidable.not_not,
          label_map, h1, and_true]
        obtain ⟨hci, hret_none, _, _⟩ := hstep
        exact ⟨hci, by rw [h3 i hci]; exact hret_none, hsetup_v⟩
      · -- sim_rel preserved
        refine ⟨by rw [h1, BRB_LTS.output_corrupted hstep],
                by simp only [h2, BRB_LTS.output_broadcastVal hstep], ?_, ?_⟩
        · intro p hp
          have hp' := BRB_LTS.step_correct_prev hstep p hp
          by_cases heq : p = i
          · subst heq; simp; obtain ⟨_, _, _, rfl⟩ := hstep; simp
          · simp only [heq]; rw [h3 p hp']; obtain ⟨_, _, _, rfl⟩ := hstep; simp [heq]
        · intro w; constructor
          · intro hw; rw [← hisup]; exact (h4 w).mp hw
          · intro hw; exact (h4 w).mpr (by rw [← hisup] at hw; exact hw)
    · -- input i v: broadcastVal changes from none to some v.
      have hi := BRB_LTS.input_eq_sender hstep
      have hc := BRB_LTS.input_corrupted hstep
      have hr := BRB_LTS.input_returned hstep
      have hs := BRB_LTS.input_sendRecv hstep
      have hbv := BRB_LTS.input_broadcastVal hstep
      obtain ⟨h1, h2, h3, h4⟩ := hR
      have hbv_none : s_i.broadcastVal = none := by
        rw [h2]; obtain ⟨_, hbn, _⟩ := hstep; exact hbn
      refine ⟨s_i, { s_i with broadcastVal := some v }, { s_i with broadcastVal := some v },
              .refl, ?_, .refl, ?_⟩
      · -- ideal step
        simp only [IdealBRB.ideal_brb, Order.add_one_le_iff, label_map, hi, and_true, true_and]
        exact hbv_none
      · -- sim_rel preserved
        refine ⟨h1.trans hc.symm, ?_, ?_, ?_⟩
        · simp only [hbv]
        · intro p hp
          have hp' : BRB_LTS.isCorrect n Value s_r p := by
            simp only [BRB_LTS.isCorrect] at hp ⊢; rwa [← hc]
          rw [h3 p hp', hr]
        · intro w; rw [initSupport_congr hc hs]; exact h4 w

/-! ### Lifting Properties via Simulation -/

/-- Lift validity from ideal to real via the forward simulation.
    Strategy: (a) validity holds on stutter-valid ideal executions;
    (b) each concrete execution has a simulating stutter-valid abstract
    execution with matching external labels; (c) since validity only
    references external labels and label_map is identity on them,
    validity transfers to the concrete. -/
private theorem brb_sim_map_tau [Inhabited Value] [Inhabited (Fin n)]
    (hn : n > 3 * f) :
    (brb_forward_sim n f Value sender hn).label_map
      (BRB_LTS.brb_labelling n Value).tau =
      (IdealBRB.ideal_labelling n Value).tau := rfl

private theorem brb_sim_map_default [Inhabited Value] [Inhabited (Fin n)]
    (hn : n > 3 * f) :
    (brb_forward_sim n f Value sender hn).label_map
      (default : BRB_LTS.Label n Value) =
      (default : IdealBRB.Label n Value) := rfl

private theorem brb_sim_label_ext [Inhabited Value] [Inhabited (Fin n)]
    (hn : n > 3 * f) :
    ∀ l₁, (BRB_LTS.brb_labelling n Value).is_external l₁ = true →
      (IdealBRB.ideal_labelling n Value).is_external
        ((brb_forward_sim n f Value sender hn).label_map l₁) = true := by
  intro l₁ hl₁; cases l₁ <;>
    simp [BRB_LTS.brb_labelling, Labelling.is_external, label_map,
      IdealBRB.ideal_labelling, brb_forward_sim] at *

omit [DecidableEq Value] in
private theorem label_ext_compat [Inhabited Value] [Inhabited (Fin n)] :
    ∀ l₁ : BRB_LTS.Label n Value,
      (BRB_LTS.brb_labelling n Value).is_external l₁ = true →
      (IdealBRB.ideal_labelling n Value).is_external
        (label_map n Value l₁) = true := by
  intro l₁ hl₁; cases l₁ <;>
    simp [BRB_LTS.brb_labelling, IdealBRB.ideal_labelling, Labelling.is_external, label_map] at *

theorem real_validity [Inhabited Value] (hn : n > 3 * f) :
    (BRB_LTS.brb n f Value sender).satisfies
      (BRB_LTS.validity n Value sender) := by
  haveI : Inhabited (Fin n) := ⟨⟨0, by omega⟩⟩
  intro e_c hv_c
  obtain ⟨e_a, hv_a, hext_eq⟩ :=
    (brb_forward_sim n f Value sender hn).external_subseq_correspondence
      (label_ext_compat n Value)
      (brb_sim_map_tau n f Value sender hn)
      e_c hv_c
  have h_ideal := IdealBRB.ideal_validity_stutter n f Value sender e_a hv_a
  obtain ⟨c_to_a, a_to_c⟩ := LTS.external_label_transfer
    (BRB_LTS.brb_labelling n Value) (IdealBRB.ideal_labelling n Value)
    (label_map n Value) e_c.labels e_a.labels hext_eq
    (label_ext_compat n Value) (brb_sim_map_tau n f Value sender hn)
  intro hno_corrupt k i v hout
  obtain ⟨m, hm⟩ := c_to_a k (by rw [hout]; rfl)
  have hno_a : ∀ j, e_a.labels j ≠ IdealBRB.Label.corrupt sender := by
    intro j habs
    obtain ⟨k', hk', _⟩ := a_to_c j (by rw [habs]; rfl)
    have hlm : label_map n Value (e_c.labels k') = .corrupt sender := hk'.trans habs
    have : e_c.labels k' = .corrupt sender := by
      cases h : e_c.labels k' <;>
      (rw [h] at hlm; simp only [label_map, IdealBRB.Label.corrupt.injEq,
        BRB_LTS.Label.corrupt.injEq, reduceCtorEq] at hlm ⊢)
      exact hlm
    exact hno_corrupt k' this
  have ⟨m', hm'⟩ := h_ideal hno_a m i v (by rw [hm, hout]; rfl)
  obtain ⟨k', hk', _⟩ := a_to_c m' (by rw [hm']; rfl)
  have hlm : label_map n Value (e_c.labels k') = .input sender v := hk'.trans hm'
  refine ⟨k', ?_⟩
  cases h : e_c.labels k' <;> (rw [h] at hlm; simp only [label_map, IdealBRB.Label.input.injEq,
    BRB_LTS.Label.input.injEq, reduceCtorEq] at hlm ⊢) ; exact hlm

/-- Lift agreement from ideal to real via the forward simulation. -/
theorem real_agreement [Inhabited Value] (hn : n > 3 * f) :
    (BRB_LTS.brb n f Value sender).satisfies
      (BRB_LTS.agreement n Value) := by
  haveI : Inhabited (Fin n) := ⟨⟨0, by omega⟩⟩
  intro e_c hv_c
  obtain ⟨e_a, hv_a, hext_eq⟩ :=
    (brb_forward_sim n f Value sender hn).external_subseq_correspondence
      (label_ext_compat n Value)
      (brb_sim_map_tau n f Value sender hn)
      e_c hv_c
  have h_ideal := IdealBRB.ideal_agreement_stutter n f Value sender e_a hv_a
  obtain ⟨c_to_a, a_to_c⟩ := LTS.external_label_transfer
    (BRB_LTS.brb_labelling n Value) (IdealBRB.ideal_labelling n Value)
    (label_map n Value) e_c.labels e_a.labels hext_eq
    (label_ext_compat n Value) (brb_sim_map_tau n f Value sender hn)
  intro k₁ k₂ p q vp vq hout₁ hout₂
  obtain ⟨m₁, hm₁⟩ := c_to_a k₁ (by rw [hout₁]; rfl)
  obtain ⟨m₂, hm₂⟩ := c_to_a k₂ (by rw [hout₂]; rfl)
  exact h_ideal m₁ m₂ p q vp vq
    (by rw [hm₁, hout₁]; rfl) (by rw [hm₂, hout₂]; rfl)

end BRB_Simulation
