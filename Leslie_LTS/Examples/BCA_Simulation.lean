import Leslie_LTS.Framework
import Leslie_LTS.Examples.BCA
import Leslie_LTS.Examples.IdealBCA
import Leslie_LTS.Examples.UtilityByzantine
import Leslie_LTS.Examples.CorruptionInvariants

/-! # Forward Simulation: Real BCA → Ideal BCA

  Forward simulation from the real BCA protocol to the ideal BCA specification.
  Lifts safety properties (validity, agreement, binding) from ideal to real.
-/

open LTS

namespace BCA_Simulation

/-- Computably find an element satisfying a decidable predicate in a list,
    given a proof that one exists. -/
private def findWitness {α : Type _} (xs : List α) (p : α → Prop) [DecidablePred p]
    (h : ∃ x ∈ xs, p x) : { x : α // p x } :=
  match hf : xs.find? (fun x => decide (p x)) with
  | some x =>
    ⟨x, by have := List.find?_some hf; simpa using this⟩
  | none =>
    absurd h (by
      simp only [not_exists, not_and]
      intro x hx
      have := List.find?_eq_none.mp hf x hx
      simpa using this)

variable (T : Type) [DecidableEq T]
variable (n f : Nat)

/-! ### Computable Witness Helpers (simple, no forward references) -/

/-- Values appearing as echoed values across all processes. -/
private def echoCandidates (s : BCA_LTS.State T n) : List T :=
  (List.finRange n).filterMap (fun p => (s.local_ p).echoed)

/-- Values appearing as input values across all processes. -/
private def inputCandidates (s : BCA_LTS.State T n) : List T :=
  (List.finRange n).filterMap (fun p => (s.local_ p).input)

/-- Computable head of a nonempty filtered list. -/
private def findVoter (filt : List (Fin n)) (hpos : 0 < filt.length) : Fin n :=
  filt.get ⟨0, hpos⟩

private theorem findVoter_mem (filt : List (Fin n)) (hpos : 0 < filt.length) :
    findVoter n filt hpos ∈ filt :=
  List.get_mem filt ⟨0, hpos⟩

/-! ### Label Map -/

/-- Map real BCA labels to ideal BCA labels. -/
def label_map [Inhabited T] : BCA_LTS.Label T n → IdealBCA.Label T n
  | .corrupt i   => .corrupt i
  | .input i v   => .input i v
  | .output i v  => .output i v
  | .send _ _ _ _ => .bind default
  | .recv _ _ _ _ => .bind default

/-! ### Support Measures -/

/-- `|corrupted| + |{correct p : echoed(p) = some b}|`. -/
def echoSupport (s : BCA_LTS.State T n) (b : T) : Nat :=
  s.corrupted.length +
  ((List.finRange n).filter (fun p =>
    decide (p ∉ s.corrupted) && decide ((s.local_ p).echoed = some b))).length

/-- `|corrupted| + |{correct p : voted(some v)}|`. -/
def voteSupport (s : BCA_LTS.State T n) (v : T) : Nat :=
  s.corrupted.length +
  ((List.finRange n).filter (fun p =>
    decide (p ∉ s.corrupted) && decide ((s.local_ p).voted (some v) = true))).length

/-- Two distinct values each have `n − f` processes voting against them. -/
def voteContention (s : BCA_LTS.State T n) : Prop :=
  ∃ b₁ b₂ : T, b₁ ≠ b₂ ∧
    s.corrupted.length + ((List.finRange n).filter (fun p =>
      decide (p ∉ s.corrupted) &&
      ((s.local_ p).voted none || (s.local_ p).voted (some b₂)))).length ≥ n - f ∧
    s.corrupted.length + ((List.finRange n).filter (fun p =>
      decide (p ∉ s.corrupted) &&
      ((s.local_ p).voted none || (s.local_ p).voted (some b₁)))).length ≥ n - f

/-! ### Simulation Relation -/

/-- Simulation relation connecting real and ideal BCA states. -/
private theorem echoSupport_in_candidates {s : BCA_LTS.State T n} (b : T)
    (h : echoSupport T n s b > s.corrupted.length) :
    b ∈ echoCandidates T n s := by
  unfold echoSupport at h
  have hpos : ((List.finRange n).filter (fun p =>
    decide (p ∉ s.corrupted) && decide ((s.local_ p).echoed = some b))).length > 0 := by omega
  obtain ⟨p, hp⟩ := List.exists_mem_of_length_pos hpos
  simp only [decide_not, List.mem_filter, List.mem_finRange, Bool.and_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, decide_eq_true_eq,
    true_and] at hp
  exact List.mem_filterMap.mpr ⟨p, List.mem_finRange p, hp.2⟩

private def findNewEchoCrossing (f : Nat)
    (s_r s_r' : BCA_LTS.State T n) :
    Option { b : T //
      echoSupport T n s_r' b ≥ BCA_LTS.echoThreshold n f ∧
      ¬ echoSupport T n s_r b ≥ BCA_LTS.echoThreshold n f } :=
  let candidates := echoCandidates T n s_r
  let pred := fun b => decide (echoSupport T n s_r' b ≥ BCA_LTS.echoThreshold n f) &&
                       !decide (echoSupport T n s_r b ≥ BCA_LTS.echoThreshold n f)
  match hfind : candidates.find? pred with
  | some b =>
    have hpred : pred b = true := List.find?_some hfind
    have hge : echoSupport T n s_r' b ≥ BCA_LTS.echoThreshold n f := by
      simp only [pred, Bool.and_eq_true, decide_eq_true_eq] at hpred; exact hpred.1
    have hlt : ¬ echoSupport T n s_r b ≥ BCA_LTS.echoThreshold n f := by
      simp only [pred, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        Nat.not_le] at hpred
      exact Nat.not_le.mpr hpred.2
    some ⟨b, hge, hlt⟩
  | none => none

private theorem findNewEchoCrossing_complete {f : Nat}
    {s_r s_r' : BCA_LTS.State T n}
    (hn : n > 3 * f)
    (hbudget : s_r'.corrupted.length ≤ f)
    (hcl : ∀ p : Fin n, s_r'.local_ p = s_r.local_ p)
    (hex : ∃ b, echoSupport T n s_r' b ≥ BCA_LTS.echoThreshold n f ∧
               ¬ echoSupport T n s_r b ≥ BCA_LTS.echoThreshold n f) :
    (findNewEchoCrossing T n f s_r s_r').isSome = true := by
  obtain ⟨b, hge, hlt⟩ := hex
  have hgt : echoSupport T n s_r' b > s_r'.corrupted.length := by
    unfold BCA_LTS.echoThreshold at hge; omega
  have hmem_sr' := echoSupport_in_candidates T n b hgt
  have hmem_sr : b ∈ echoCandidates T n s_r := by
    obtain ⟨p, _, hp⟩ := List.mem_filterMap.mp hmem_sr'
    exact List.mem_filterMap.mpr ⟨p, List.mem_finRange p, by rw [← hcl p]; exact hp⟩
  unfold findNewEchoCrossing
  simp only
  split
  · rfl
  · next hfind =>
    have hnone := List.find?_eq_none.mp hfind b hmem_sr
    simp [hge, hlt] at hnone

def sim_rel (s_r : BCA_LTS.State T n) (s_i : IdealBCA.State T n) : Prop :=
  s_i.corrupted = s_r.corrupted ∧
  (∀ p, s_i.input_ p = (s_r.local_ p).input) ∧
  (∀ p, s_i.decided p = (s_r.local_ p).decided) ∧
  (∀ b, echoSupport T n s_r b ≥ BCA_LTS.echoThreshold n f →
    s_i.bound_value = some b ∨ voteContention T n f s_r) ∧
  (voteContention T n f s_r → s_i.bound_value ≠ none) ∧
  (∀ b, s_i.bound_value = some b →
    echoSupport T n s_r b ≥ BCA_LTS.echoThreshold n f ∨
    voteContention T n f s_r)

/-! ### Support Uniqueness -/

/-- At most one value can have `echoSupport ≥ n-f` when `n > 3f`. -/
theorem echoSupport_unique (hn : n > 3 * f) (s : BCA_LTS.State T n)
    (hbudget : s.corrupted.length ≤ f)
    (hnodup : s.corrupted.Nodup)
    (v w : T)
    (hv : echoSupport T n s v ≥ BCA_LTS.echoThreshold n f)
    (hw : echoSupport T n s w ≥ BCA_LTS.echoThreshold n f) :
    v = w := by
  if hvw : v = w then exact hvw else
  exfalso
  unfold echoSupport BCA_LTS.echoThreshold at hv hw
  have hnf : n ≥ f := by omega
  have hfv : ((List.finRange n).filter (fun p =>
      decide (p ∉ s.corrupted) && decide ((s.local_ p).echoed = some v))).length +
      f + s.corrupted.length ≥ n := by omega
  have hfw : ((List.finRange n).filter (fun p =>
      decide (p ∉ s.corrupted) && decide ((s.local_ p).echoed = some w))).length +
      f + s.corrupted.length ≥ n := by omega
  have h3 : ∀ (l : List (Fin n)),
      ((l.filter (fun p =>
      decide (p ∉ s.corrupted) && decide ((s.local_ p).echoed = some v))).length +
        (l.filter (fun p =>
        decide (p ∉ s.corrupted) && decide ((s.local_ p).echoed = some w))).length +
        (l.filter (fun p => decide (p ∈ s.corrupted))).length) ≤ l.length := by
    intro l
    apply three_way_filter_le _ _ _ l
    · intro x; by_contra h
      simp only [Bool.and_eq_true, Bool.not_eq_false, decide_eq_true_eq] at h
      exact hvw (Option.some.inj (h.1.2.symm.trans h.2.2))
    · intro x; by_contra h
      simp only [Bool.and_eq_true, Bool.not_eq_false, decide_eq_true_eq] at h
      exact h.1.1 h.2
    · intro x; by_contra h
      simp only [Bool.and_eq_true, Bool.not_eq_false, decide_eq_true_eq] at h
      exact h.1.1 h.2
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
      simp only [List.mem_filter, List.mem_finRange, decide_eq_true_eq, true_and]
      exact hx)
  omega

/-- Corrupted list either stays the same or grows by one element across any step. -/
private theorem step_corrupted_grow {s s' : BCA_LTS.State T n} {l : BCA_LTS.Label T n}
    (h : (BCA_LTS.bca T n f).step s l s') :
    s.corrupted = s'.corrupted ∨ ∃ i, s'.corrupted = i :: s.corrupted := by
  match l with
  | .corrupt i => right; exact ⟨i, BCA_LTS.corrupt_eq h ▸ rfl⟩
  | .send .. => left; exact (BCA_LTS.send_corrupted h).symm
  | .recv .. => left; exact (BCA_LTS.recv_corrupted h).symm
  | .output .. => left; exact (BCA_LTS.output_corrupted h).symm
  | .input .. => left; exact (BCA_LTS.input_corrupted h).symm

private def bca_corruption_spec : CorruptionInvariants.CorruptionSpec
    (BCA_LTS.bca T n f) (fun s => s.corrupted) f where
  init_empty := fun _ ⟨_, _, hc⟩ => hc
  step_corrupted := fun s l s' h => by
    match l with
    | .corrupt i => obtain ⟨hci, hb, rfl⟩ := h; right; exact ⟨i, rfl, hci, hb⟩
    | .send .. => left; exact BCA_LTS.send_corrupted h
    | .recv .. => left; exact BCA_LTS.recv_corrupted h
    | .output .. => left; exact BCA_LTS.output_corrupted h
    | .input .. => left; exact BCA_LTS.input_corrupted h

theorem corrupted_budget {s : BCA_LTS.State T n}
    (hreach : LTS.Reachable (BCA_LTS.bca T n f) s) :
    s.corrupted.length ≤ f :=
  CorruptionInvariants.corrupted_budget (bca_corruption_spec T n f) hreach

theorem corrupted_nodup {s : BCA_LTS.State T n}
    (hreach : LTS.Reachable (BCA_LTS.bca T n f) s) :
    s.corrupted.Nodup :=
  CorruptionInvariants.corrupted_nodup (bca_corruption_spec T n f) hreach

/-! ### Protocol Invariants -/

/-- Buffer echo(b) from correct q implies `q.echoed = some b`. -/
theorem buffer_echo_consistent {s : BCA_LTS.State T n}
    (hreach : LTS.Reachable (BCA_LTS.bca T n f) s)
    (q dst : Fin n) (b : T)
    (hcorr_q : BCA_LTS.isCorrect T n s q)
    (hbuf : s.buffer ⟨q, dst, .echo, some b⟩ = true) :
    (s.local_ q).echoed = some b := by
  induction hreach with
  | init hinit => obtain ⟨_, hbe, _⟩ := hinit; simp [hbe] at hbuf
  | step hreach_prev hstep ih =>
    have hcp := BCA_LTS.step_correct_prev hstep q hcorr_q
    rename_i s_prev l _
    match l with
    | .corrupt _ =>
      rw [BCA_LTS.corrupt_buffer hstep] at hbuf
      rw [BCA_LTS.corrupt_local hstep q]
      exact ih hcp hbuf
    | .send src dst' t mv =>
      rcases BCA_LTS.send_buffer hstep ⟨q, dst, .echo, some b⟩ hbuf with hmsg | hold
      · -- This message was just sent by src. So src = q.
        simp only [BCA_LTS.Message.mk.injEq] at hmsg
        obtain ⟨rfl, _, rfl, rfl⟩ := hmsg
        exact BCA_LTS.send_echo_echoed_correct hstep hcp
      · exact BCA_LTS.step_echoed_persist hstep q b hcorr_q (ih hcp hold)
    | .recv src dst' .init mv =>
      rcases BCA_LTS.recv_init_buffer hstep ⟨q, dst, .echo, some b⟩ hbuf with hmsg | hold
      · simp [BCA_LTS.Message.mk.injEq] at hmsg
      · exact BCA_LTS.step_echoed_persist hstep q b hcorr_q (ih hcp hold)
    | .recv src dst' .echo mv =>
      obtain ⟨hbuf_guard, rfl⟩ := hstep
      have hbuf_old : s_prev.buffer ⟨q, dst, .echo, some b⟩ = true := by
        simp only [BCA_LTS.Message.mk.injEq, true_and, Bool.if_false_left, Bool.decide_and,
          Bool.not_and, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
          decide_eq_false_iff_not] at hbuf
        by_cases hmeq : (⟨q, dst, .echo, some b⟩ : BCA_LTS.Message T n) = ⟨src, dst', .echo, mv⟩
        · -- consumed message = our target → it was in old buffer (guard)
          simp only [BCA_LTS.Message.mk.injEq, true_and] at hmeq
          obtain ⟨rfl, rfl, rfl⟩ := hmeq; exact hbuf_guard
        · exact hbuf.2
      have hstep' : (BCA_LTS.bca T n f).step s_prev (.recv src dst' .echo mv) _ :=
        ⟨hbuf_guard, rfl⟩
      exact BCA_LTS.step_echoed_persist hstep' q b hcorr_q (ih hcp hbuf_old)
    | .recv src dst' .vote mv =>
      rcases BCA_LTS.recv_vote_buffer hstep ⟨q, dst, .echo, some b⟩ hbuf with hmsg | hold
      · simp [BCA_LTS.Message.mk.injEq] at hmsg
      · exact BCA_LTS.step_echoed_persist hstep q b hcorr_q (ih hcp hold)
    | .output _ _ =>
      rw [BCA_LTS.output_buffer hstep] at hbuf
      exact BCA_LTS.step_echoed_persist hstep q b hcorr_q (ih hcp hbuf)
    | .input _ _ =>
      rw [BCA_LTS.input_buffer hstep] at hbuf
      exact BCA_LTS.step_echoed_persist hstep q b hcorr_q (ih hcp hbuf)

/-- `echoRecv p q b` and q correct implies `q.echoed = some b`. -/
theorem echo_trace {s : BCA_LTS.State T n}
    (hreach : LTS.Reachable (BCA_LTS.bca T n f) s)
    (p q : Fin n) (b : T)
    (hcorr_q : BCA_LTS.isCorrect T n s q)
    (hrecv : (s.local_ p).echoRecv q b = true) :
    (s.local_ q).echoed = some b := by
  induction hreach with
  | init hinit =>
    obtain ⟨hlocal, _, _⟩ := hinit
    simp [hlocal p, BCA_LTS.LocalState.init] at hrecv
  | step hreach_prev hstep ih =>
    have hcpq := BCA_LTS.step_correct_prev hstep q hcorr_q
    rename_i s_prev l _
    by_cases hnot : ∀ dst, l ≠ .recv q dst .echo (some b)
    · -- Not a matching recv echo: echoRecv was already true in prev
      have hprev := BCA_LTS.step_echoRecv_prev hstep p q b hrecv hnot
      exact BCA_LTS.step_echoed_persist hstep q b hcorr_q (ih hcpq hprev)
    · -- This IS a recv echo(some b) from q
      have ⟨dst', hrec_eq⟩ := Classical.not_forall.mp hnot
      have hrec_eq := Classical.byContradiction (fun h => hrec_eq h)
      subst hrec_eq
      have hbuf_old := hstep.1
      exact BCA_LTS.step_echoed_persist hstep q b hcorr_q
        (buffer_echo_consistent T n f hreach_prev q dst' b hcpq hbuf_old)

/-- Buffer vote(some b) from correct q implies `q.voted(some b)`. -/
theorem buffer_vote_consistent {s : BCA_LTS.State T n}
    (hreach : LTS.Reachable (BCA_LTS.bca T n f) s)
    (q dst : Fin n) (b : T)
    (hcorr_q : BCA_LTS.isCorrect T n s q)
    (hbuf : s.buffer ⟨q, dst, .vote, some b⟩ = true) :
    (s.local_ q).voted (some b) = true := by
  induction hreach with
  | init hinit => obtain ⟨_, hbe, _⟩ := hinit; simp [hbe] at hbuf
  | step hreach_prev hstep ih =>
    have hcp := BCA_LTS.step_correct_prev hstep q hcorr_q
    rename_i s_prev l _
    match l with
    | .corrupt _ =>
      rw [BCA_LTS.corrupt_buffer hstep] at hbuf
      rw [BCA_LTS.corrupt_local hstep q]
      exact ih hcp hbuf
    | .send src dst' t mv =>
      rcases BCA_LTS.send_buffer hstep ⟨q, dst, .vote, some b⟩ hbuf with hmsg | hold
      · simp only [BCA_LTS.Message.mk.injEq] at hmsg
        obtain ⟨rfl, _, rfl, rfl⟩ := hmsg
        exact BCA_LTS.send_vote_voted_correct hstep hcp
      · exact BCA_LTS.step_voted_persist hstep q b hcorr_q (ih hcp hold)
    | .recv src dst' .init mv =>
      rcases BCA_LTS.recv_init_buffer hstep ⟨q, dst, .vote, some b⟩ hbuf with hmsg | hold
      · simp [BCA_LTS.Message.mk.injEq] at hmsg
      · exact BCA_LTS.step_voted_persist hstep q b hcorr_q (ih hcp hold)
    | .recv src dst' .echo mv =>
      obtain ⟨hbuf_guard, rfl⟩ := hstep
      have hbuf_old : s_prev.buffer ⟨q, dst, .vote, some b⟩ = true := by
        simp only [BCA_LTS.Message.mk.injEq, reduceCtorEq, false_and, and_false, ↓reduceIte] at hbuf
        by_cases hmeq : (⟨q, dst, .vote, some b⟩ : BCA_LTS.Message T n) = ⟨src, dst', .echo, mv⟩
        · simp [BCA_LTS.Message.mk.injEq] at hmeq
        · exact hbuf
      have hstep' : (BCA_LTS.bca T n f).step s_prev (.recv src dst' .echo mv) _ :=
        ⟨hbuf_guard, rfl⟩
      exact BCA_LTS.step_voted_persist hstep' q b hcorr_q (ih hcp hbuf_old)
    | .recv src dst' .vote mv =>
      rcases BCA_LTS.recv_vote_buffer hstep ⟨q, dst, .vote, some b⟩ hbuf with hmsg | hold
      · simp only [BCA_LTS.Message.mk.injEq, true_and] at hmsg
        obtain ⟨rfl, rfl, rfl⟩ := hmsg
        have hbuf_old := hstep.1
        exact BCA_LTS.step_voted_persist hstep q b hcorr_q (ih hcp hbuf_old)
      · exact BCA_LTS.step_voted_persist hstep q b hcorr_q (ih hcp hold)
    | .output _ _ =>
      rw [BCA_LTS.output_buffer hstep] at hbuf
      exact BCA_LTS.step_voted_persist hstep q b hcorr_q (ih hcp hbuf)
    | .input _ _ =>
      rw [BCA_LTS.input_buffer hstep] at hbuf
      exact BCA_LTS.step_voted_persist hstep q b hcorr_q (ih hcp hbuf)

/-- `voteRecv p q (some b)` and q correct implies `q.voted(some b)`. -/
theorem vote_trace {s : BCA_LTS.State T n}
    (hreach : LTS.Reachable (BCA_LTS.bca T n f) s)
    (p q : Fin n) (b : T)
    (hcorr_q : BCA_LTS.isCorrect T n s q)
    (hrecv : (s.local_ p).voteRecv q (some b) = true) :
    (s.local_ q).voted (some b) = true := by
  induction hreach with
  | init hinit =>
    obtain ⟨hlocal, _, _⟩ := hinit
    simp [hlocal p, BCA_LTS.LocalState.init] at hrecv
  | step hreach_prev hstep ih =>
    have hcpq := BCA_LTS.step_correct_prev hstep q hcorr_q
    rename_i s_prev l _
    by_cases hnot : ∀ dst, l ≠ .recv q dst .vote (some b)
    · have hprev := BCA_LTS.step_voteRecv_prev hstep p q b hrecv hnot
      exact BCA_LTS.step_voted_persist hstep q b hcorr_q (ih hcpq hprev)
    · have ⟨dst', hrec_eq⟩ := Classical.not_forall.mp hnot
      have hrec_eq := Classical.byContradiction (fun h => hrec_eq h)
      subst hrec_eq
      have hbuf_old := hstep.1
      exact BCA_LTS.step_voted_persist hstep q b hcorr_q
        (buffer_vote_consistent T n f hreach_prev q dst' b hcpq hbuf_old)

/-- Buffer vote(none) from correct q implies `q.voted none`. -/
theorem buffer_vote_none_consistent {s : BCA_LTS.State T n}
    (hreach : LTS.Reachable (BCA_LTS.bca T n f) s)
    (q dst : Fin n)
    (hcorr_q : BCA_LTS.isCorrect T n s q)
    (hbuf : s.buffer ⟨q, dst, .vote, none⟩ = true) :
    (s.local_ q).voted none = true := by
  induction hreach with
  | init hinit => obtain ⟨_, hbe, _⟩ := hinit; simp [hbe] at hbuf
  | step hreach_prev hstep ih =>
    have hcp := BCA_LTS.step_correct_prev hstep q hcorr_q
    rename_i s_prev l _
    match l with
    | .corrupt _ =>
      rw [BCA_LTS.corrupt_buffer hstep] at hbuf
      rw [BCA_LTS.corrupt_local hstep q]
      exact ih hcp hbuf
    | .send src dst' t mv =>
      rcases BCA_LTS.send_buffer hstep ⟨q, dst, .vote, none⟩ hbuf with hmsg | hold
      · simp only [BCA_LTS.Message.mk.injEq] at hmsg
        obtain ⟨rfl, _, rfl, rfl⟩ := hmsg
        exact BCA_LTS.send_vote_voted_correct hstep hcp
      · exact BCA_LTS.step_voted_none_persist hstep q hcorr_q (ih hcp hold)
    | .recv src dst' .init mv =>
      rcases BCA_LTS.recv_init_buffer hstep ⟨q, dst, .vote, none⟩ hbuf with hmsg | hold
      · simp [BCA_LTS.Message.mk.injEq] at hmsg
      · exact BCA_LTS.step_voted_none_persist hstep q hcorr_q (ih hcp hold)
    | .recv src dst' .echo mv =>
      obtain ⟨hbuf_guard, rfl⟩ := hstep
      have hbuf_old : s_prev.buffer ⟨q, dst, .vote, none⟩ = true := by
        simp only [BCA_LTS.Message.mk.injEq, reduceCtorEq, false_and, and_false, ↓reduceIte] at hbuf
        by_cases hmeq : (⟨q, dst, .vote, none⟩ : BCA_LTS.Message T n) = ⟨src, dst', .echo, mv⟩
        · simp [BCA_LTS.Message.mk.injEq] at hmeq
        · exact hbuf
      have hstep' : (BCA_LTS.bca T n f).step s_prev (.recv src dst' .echo mv) _ :=
        ⟨hbuf_guard, rfl⟩
      exact BCA_LTS.step_voted_none_persist hstep' q hcorr_q (ih hcp hbuf_old)
    | .recv src dst' .vote mv =>
      rcases BCA_LTS.recv_vote_buffer hstep ⟨q, dst, .vote, none⟩ hbuf with hmsg | hold
      · simp only [BCA_LTS.Message.mk.injEq, true_and] at hmsg
        obtain ⟨rfl, rfl, rfl⟩ := hmsg
        have hbuf_old := hstep.1
        exact BCA_LTS.step_voted_none_persist hstep q hcorr_q (ih hcp hbuf_old)
      · exact BCA_LTS.step_voted_none_persist hstep q hcorr_q (ih hcp hold)
    | .output _ _ =>
      rw [BCA_LTS.output_buffer hstep] at hbuf
      exact BCA_LTS.step_voted_none_persist hstep q hcorr_q (ih hcp hbuf)
    | .input _ _ =>
      rw [BCA_LTS.input_buffer hstep] at hbuf
      exact BCA_LTS.step_voted_none_persist hstep q hcorr_q (ih hcp hbuf)

/-- `voteRecv p q none` and q correct implies `q.voted none`. -/
theorem vote_trace_none {s : BCA_LTS.State T n}
    (hreach : LTS.Reachable (BCA_LTS.bca T n f) s)
    (p q : Fin n)
    (hcorr_q : BCA_LTS.isCorrect T n s q)
    (hrecv : (s.local_ p).voteRecv q none = true) :
    (s.local_ q).voted none = true := by
  induction hreach with
  | init hinit =>
    obtain ⟨hlocal, _, _⟩ := hinit
    simp [hlocal p, BCA_LTS.LocalState.init] at hrecv
  | step hreach_prev hstep ih =>
    have hcpq := BCA_LTS.step_correct_prev hstep q hcorr_q
    rename_i s_prev l _
    by_cases hnot : ∀ dst, l ≠ .recv q dst .vote none
    · have hprev := BCA_LTS.step_voteRecv_none_prev hstep p q hrecv hnot
      exact BCA_LTS.step_voted_none_persist hstep q hcorr_q (ih hcpq hprev)
    · have ⟨dst', hrec_eq⟩ := Classical.not_forall.mp hnot
      have hrec_eq := Classical.byContradiction (fun h => hrec_eq h)
      subst hrec_eq
      have hbuf_old := hstep.1
      exact BCA_LTS.step_voted_none_persist hstep q hcorr_q
        (buffer_vote_none_consistent T n f hreach_prev q dst' hcpq hbuf_old)

/-- Helper: if input=b or countInitRecv≥threshold held in prev, it holds after any step. -/
private theorem init_conclusion_persist {s s' : BCA_LTS.State T n} {l : BCA_LTS.Label T n}
    (hstep : (BCA_LTS.bca T n f).step s l s') (q : Fin n) (b : T)
    (h : (s.local_ q).input = some b ∨
      BCA_LTS.countInitRecv T n (s.local_ q) b ≥ BCA_LTS.amplifyThreshold f) :
    (s'.local_ q).input = some b ∨
      BCA_LTS.countInitRecv T n (s'.local_ q) b ≥ BCA_LTS.amplifyThreshold f := by
  rcases h with hinp | hamp
  · left; exact BCA_LTS.step_input_persist hstep q b hinp
  · right; exact Nat.le_trans hamp (BCA_LTS.step_countInitRecv_mono hstep q b)

theorem buffer_init_consistent {s : BCA_LTS.State T n}
    (hreach : LTS.Reachable (BCA_LTS.bca T n f) s)
    (q dst : Fin n) (b : T)
    (hcorr_q : BCA_LTS.isCorrect T n s q)
    (hbuf : s.buffer ⟨q, dst, .init, some b⟩ = true) :
    (s.local_ q).input = some b ∨
    BCA_LTS.countInitRecv T n (s.local_ q) b ≥ BCA_LTS.amplifyThreshold f := by
  induction hreach with
  | init hinit => obtain ⟨_, hbe, _⟩ := hinit; simp [hbe] at hbuf
  | step hreach_prev hstep ih =>
    have hcp := BCA_LTS.step_correct_prev hstep q hcorr_q
    rename_i s_prev l _
    match l with
    | .corrupt _ =>
      rw [BCA_LTS.corrupt_buffer hstep] at hbuf
      rcases ih hcp hbuf with hinp | hamp
      · left; rw [BCA_LTS.corrupt_local hstep]; exact hinp
      · right; unfold BCA_LTS.countInitRecv at hamp ⊢
        rw [BCA_LTS.corrupt_local hstep]; exact hamp
    | .send src dst' t mv =>
      rcases BCA_LTS.send_buffer hstep ⟨q, dst, .init, some b⟩ hbuf with hmsg | hold
      · simp only [BCA_LTS.Message.mk.injEq] at hmsg
        obtain ⟨rfl, _, rfl, rfl⟩ := hmsg
        rcases hstep.1 with hbyz | ⟨_, _, hgate⟩
        · exact absurd hbyz hcp
        · exact init_conclusion_persist T n f hstep q b hgate
      · exact init_conclusion_persist T n f hstep q b (ih hcp hold)
    | .recv src dst' .echo mv =>
      obtain ⟨hbuf_guard, rfl⟩ := hstep
      have hbuf_old : s_prev.buffer ⟨q, dst, .init, some b⟩ = true := by
        simp only [BCA_LTS.Message.mk.injEq, reduceCtorEq, false_and, and_false, ↓reduceIte] at hbuf
        by_cases hmeq : (⟨q, dst, .init, some b⟩ : BCA_LTS.Message T n) = ⟨src, dst', .echo, mv⟩
        · simp [BCA_LTS.Message.mk.injEq] at hmeq
        · exact hbuf
      have hstep' : (BCA_LTS.bca T n f).step s_prev (.recv src dst' .echo mv) _ :=
        ⟨hbuf_guard, rfl⟩
      exact init_conclusion_persist T n f hstep' q b (ih hcp hbuf_old)
    | .recv src dst' .init mv =>
      rcases BCA_LTS.recv_init_buffer hstep ⟨q, dst, .init, some b⟩ hbuf with hmsg | hold
      · simp only [BCA_LTS.Message.mk.injEq, true_and] at hmsg
        obtain ⟨rfl, rfl, rfl⟩ := hmsg
        have hbuf_old := hstep.1
        exact init_conclusion_persist T n f hstep q b (ih hcp hbuf_old)
      · exact init_conclusion_persist T n f hstep q b (ih hcp hold)
    | .recv src dst' .vote mv =>
      rcases BCA_LTS.recv_vote_buffer hstep ⟨q, dst, .init, some b⟩ hbuf with hmsg | hold
      · simp [BCA_LTS.Message.mk.injEq] at hmsg
      · exact init_conclusion_persist T n f hstep q b (ih hcp hold)
    | .output _ _ =>
      rw [BCA_LTS.output_buffer hstep] at hbuf
      exact init_conclusion_persist T n f hstep q b (ih hcp hbuf)
    | .input _ _ =>
      rw [BCA_LTS.input_buffer hstep] at hbuf
      exact init_conclusion_persist T n f hstep q b (ih hcp hbuf)

/-- `initRecv p q b` and q correct implies `q.input = some b` or amplification. -/
theorem init_trace {s : BCA_LTS.State T n}
    (hreach : LTS.Reachable (BCA_LTS.bca T n f) s)
    (p q : Fin n) (b : T)
    (hcorr_q : BCA_LTS.isCorrect T n s q)
    (hrecv : (s.local_ p).initRecv q b = true) :
    (s.local_ q).input = some b ∨
    BCA_LTS.countInitRecv T n (s.local_ q) b ≥ BCA_LTS.amplifyThreshold f := by
  induction hreach with
  | init hinit =>
    obtain ⟨hlocal, _, _⟩ := hinit
    simp [hlocal p, BCA_LTS.LocalState.init] at hrecv
  | step hreach_prev hstep ih =>
    have hcpq := BCA_LTS.step_correct_prev hstep q hcorr_q
    rename_i s_prev l _
    by_cases hnot : ∀ dst, l ≠ .recv q dst .init (some b)
    · have hprev := BCA_LTS.step_initRecv_prev hstep p q b hrecv hnot
      exact init_conclusion_persist T n f hstep q b (ih hcpq hprev)
    · have ⟨dst', hrec_eq⟩ := Classical.not_forall.mp hnot
      have hrec_eq := Classical.byContradiction (fun h => hrec_eq h)
      subst hrec_eq
      have hbuf_old := hstep.1
      exact init_conclusion_persist T n f hstep q b
        (buffer_init_consistent T n f hreach_prev q dst' b hcpq hbuf_old)

/-- `|{correct q : input(q) = some b}|`. -/
private def realInputSupport (s : BCA_LTS.State T n) (b : T) : Nat :=
  ((List.finRange n).filter (fun q =>
    decide (q ∉ s.corrupted) && decide ((s.local_ q).input = some b))).length

omit [DecidableEq T] in
/-- voteContention is equal when corrupted and all voted values are unchanged. -/
private theorem voteContention_eq {s s' : BCA_LTS.State T n}
    (hc : s'.corrupted = s.corrupted)
    (hv : ∀ p w, (s'.local_ p).voted w = (s.local_ p).voted w) :
    voteContention T n f s' = voteContention T n f s := by
  have hfilt_eq : ∀ b, ((List.finRange n).filter (fun p =>
      decide (p ∉ s.corrupted) && ((s'.local_ p).voted none ||
      (s'.local_ p).voted (some b)))).length =
    ((List.finRange n).filter (fun p =>
      decide (p ∉ s.corrupted) && ((s.local_ p).voted none ||
      (s.local_ p).voted (some b)))).length :=
    fun b => congrArg List.length (List.filter_congr (fun p _ => by rw [hv p none, hv p (some b)]))
  simp only [voteContention, hc, hfilt_eq]

/-- Helper: `corrupted.length + filter(¬∈corrupted ∧ P)` is monotone when
    corrupted grows by at most one element and P is persistent. -/
private theorem corrupted_plus_filter_mono
    (l1 l2 : List (Fin n))
    (hgrow : l1 = l2 ∨ ∃ i, l2 = i :: l1)
    (P P' : Fin n → Bool)
    (hpersist : ∀ p, p ∉ l2 → P p = true → P' p = true) :
    l1.length + ((List.finRange n).filter (fun p => decide (p ∉ l1) && P p)).length ≤
    l2.length + ((List.finRange n).filter (fun p => decide (p ∉ l2) && P' p)).length := by
  rcases hgrow with hceq | ⟨i, hcgrow⟩
  · rw [← hceq]; apply Nat.add_le_add_left
    apply filter_length_mono; intro p hp
    simp only [decide_not, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not] at hp ⊢; exact ⟨hp.1, hpersist p (hceq ▸ hp.1) hp.2⟩
  · rw [hcgrow, List.length_cons]
    have hdec : ((List.finRange n).filter (fun p =>
        decide (p ∉ l1) && P p)).length ≤
      ((List.finRange n).filter (fun p =>
        !decide (p = i) && decide (p ∉ l1) && P p)).length + 1 := by
      have hsplit := filter_split
        (fun p : Fin n => decide (p ∉ l1) && P p)
        (fun p : Fin n => !decide (p = i))
        (List.finRange n)
      have hone : ((List.finRange n).filter (fun x =>
          decide (x ∉ l1) && P x && !!decide (x = i))).length ≤ 1 := by
        apply Nat.le_trans (filter_and_le _ _ _); simp only [Bool.not_not]
        have : ∀ x : Fin n, decide (x = i) = decide (x ∈ ([i] : List (Fin n))) := by
          intro x; simp
        simp only [this]; exact Nat.le_trans (filter_mem_le [i]) (by simp)
      have hcomm : ((List.finRange n).filter (fun x =>
          decide (x ∉ l1) && P x && !decide (x = i))).length =
        ((List.finRange n).filter (fun p =>
          !decide (p = i) && decide (p ∉ l1) && P p)).length := by
        apply congrArg List.length; apply List.filter_congr
        intro p _; simp [Bool.and_comm, Bool.and_left_comm]
      omega
    have hfilt_sub : ((List.finRange n).filter (fun p =>
        !decide (p = i) && decide (p ∉ l1) && P p)).length ≤
      ((List.finRange n).filter (fun p =>
        decide (p ∉ (i :: l1)) && P' p)).length := by
      apply filter_length_mono; intro p hp
      simp only [decide_not, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_false_iff_not, List.mem_cons, not_or, Bool.decide_and] at hp ⊢
      exact ⟨hp.1, hpersist p (by rw [hcgrow]; simp [List.mem_cons, hp.1.1, hp.1.2]) hp.2⟩
    omega

/-- `|corrupted| + realInputSupport` is monotone across steps. -/
private theorem step_support_mono {s s' : BCA_LTS.State T n} {l : BCA_LTS.Label T n}
    (h : (BCA_LTS.bca T n f).step s l s') (b : T) :
    s.corrupted.length + realInputSupport T n s b ≤
    s'.corrupted.length + realInputSupport T n s' b := by
  unfold realInputSupport
  exact corrupted_plus_filter_mono n s.corrupted s'.corrupted
    (step_corrupted_grow T n f h) _ _
    (fun p _ hinp => by
    simp only [decide_eq_true_eq] at hinp ⊢
    exact BCA_LTS.step_input_persist h p b hinp)

/-- `countInitRecv(b) ≥ f+1` implies `|corrupted| + inputSupport(b) ≥ f+1`. -/
theorem amplify_implies_inputSupport
    (b : T) :
    ∀ {s : BCA_LTS.State T n},
    LTS.Reachable (BCA_LTS.bca T n f) s →
    ∀ p, BCA_LTS.isCorrect T n s p →
    BCA_LTS.countInitRecv T n (s.local_ p) b ≥ BCA_LTS.amplifyThreshold f →
    s.corrupted.length + realInputSupport T n s b ≥ f + 1
  | _, .init ⟨hlocal, _, _⟩, p, _, hamp => by
    unfold BCA_LTS.countInitRecv BCA_LTS.amplifyThreshold at hamp
    rw [hlocal] at hamp; simp only [BCA_LTS.LocalState.init] at hamp
    have : (List.filter (fun x => false) (List.finRange n)) = ([] : List (Fin n)) :=
      List.filter_eq_nil_iff.mpr (fun _ _ => Bool.false_ne_true)
    rw [this] at hamp; simp at hamp
  | s1, .step (s := s0) (l := l) hreach0 hstep, p, hcorr_p, hamp => by
    have hcp := BCA_LTS.step_correct_prev hstep p hcorr_p
    by_cases hsup0 : s0.corrupted.length + realInputSupport T n s0 b ≥ f + 1
    · exact Nat.le_trans hsup0 (step_support_mono T n f hstep b)
    · -- Case 2: support < f+1 in pre-state.
      have hprev_low : BCA_LTS.countInitRecv T n (s0.local_ p) b <
          BCA_LTS.amplifyThreshold f :=
        Nat.lt_of_not_le fun hge =>
          absurd (amplify_implies_inputSupport b hreach0 p hcp hge) (by omega)
      match l, hstep with
      | .recv src dst .init mv, hstep =>
        by_cases hp : p = dst
        · subst hp
          rcases mv with _ | bv
          · -- mv = none: local_ p unchanged (none branch) → contradiction
            exfalso
            obtain ⟨_, rfl⟩ := hstep; simp only [↓reduceIte, ge_iff_le] at hamp
            unfold BCA_LTS.amplifyThreshold at hamp hprev_low; omega
          · -- mv = some bv
            by_cases hbv : bv = b
            · -- bv = b. Rewrite hstep to use b.
              rw [hbv] at hstep
              rw [BCA_LTS.recv_corrupted hstep]
              unfold BCA_LTS.countInitRecv BCA_LTS.amplifyThreshold at hamp hprev_low
              have hsplit := filter_split
                (fun q : Fin n => (s1.local_ p).initRecv q b)
                (fun q : Fin n => decide (q ∉ s0.corrupted))
                (List.finRange n)
              have hcorr_bound : ((List.finRange n).filter (fun q =>
                  (s1.local_ p).initRecv q b && !decide (q ∉ s0.corrupted))).length ≤
                  s0.corrupted.length := by
                apply Nat.le_trans (filter_and_le _ _ _)
                simp [Bool.not_not, decide_not]
                exact nodup_sub_length ((finRange_nodup n).sublist List.filter_sublist)
                  (fun x hx => by simp only [List.mem_filter, List.mem_finRange, decide_eq_true_eq,
                    true_and] at hx; exact hx)
              suffices hcorrect : ((List.finRange n).filter (fun q =>
                  (s1.local_ p).initRecv q b && decide (q ∉ s0.corrupted))).length ≤
                  realInputSupport T n s1 b by omega
              unfold realInputSupport
              apply filter_length_mono; intro q hq; simp only [decide_not, Bool.and_eq_true,
                Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
                decide_eq_true_eq] at hq ⊢
              obtain ⟨hinitrecv, hcorr_q⟩ := hq
              have hcorr_q' : q ∉ s1.corrupted := by
                rwa [BCA_LTS.recv_corrupted hstep]
              refine ⟨hcorr_q', ?_⟩
              have hcq0 : BCA_LTS.isCorrect T n s0 q := hcorr_q
              by_cases hqprev : (s0.local_ p).initRecv q b = true
              · -- Yes: in pre-state. init_trace on pre gives input=b or amplified.
                rcases init_trace T n f hreach0 p q b hcq0 hqprev with hinp | hamp_q
                · exact BCA_LTS.step_input_persist hstep q b hinp
                · -- q amplified in pre → IH gives support ≥ f+1 → contradicts hsup0
                  exact absurd (amplify_implies_inputSupport b hreach0 q hcq0 hamp_q) (by omega)
              · -- No: new entry. q must be src (only src was added).
                have hq_src : q = src := by
                  if hne : q = src then exact hne else
                  exact absurd (BCA_LTS.step_initRecv_prev hstep p q b hinitrecv
                    (by intro d h; simp only [BCA_LTS.Label.recv.injEq, and_self, and_true] at h
                        obtain ⟨rfl, _, _, rfl⟩ := h; exact hne rfl)) hqprev
                subst hq_src
                have hbuf := hstep.1
                rcases buffer_init_consistent T n f hreach0 q p b hcq0 hbuf with hinp | hamp_q
                · exact BCA_LTS.step_input_persist hstep q b hinp
                · exact absurd (amplify_implies_inputSupport b hreach0 q hcq0 hamp_q) (by omega)
            · -- bv ≠ b: countInitRecv for b unchanged → contradiction
              exfalso
              have heq : BCA_LTS.countInitRecv T n (s1.local_ p) b =
                  BCA_LTS.countInitRecv T n (s0.local_ p) b := by
                unfold BCA_LTS.countInitRecv; congr 1; apply List.filter_congr
                intro q _
                have hprev_ir := BCA_LTS.step_initRecv_prev hstep p q b
                have hmono_ir := BCA_LTS.step_initRecv_mono hstep p q b
                cases hx : (s1.local_ p).initRecv q b with
                | false =>
                  cases hy : (s0.local_ p).initRecv q b with
                  | false => rfl
                  | true => exact absurd (hmono_ir hy) (by rw [hx]; simp)
                | true =>
                  have := hprev_ir (by rw [hx]) (by
                    intro d h; simp only [BCA_LTS.Label.recv.injEq, Option.some.injEq,
                      true_and] at h
                    obtain ⟨_, _, _, rfl⟩ := h; exact hbv rfl)
                  rw [this]
              unfold BCA_LTS.amplifyThreshold at hamp hprev_low; omega
        · -- p ≠ dst: local_ p unchanged → countInitRecv unchanged → contradiction
          exfalso
          rw [show s1.local_ p = s0.local_ p from
            BCA_LTS.recv_local_other hstep p hp] at hamp
          unfold BCA_LTS.amplifyThreshold at hamp hprev_low; omega
      | .corrupt _, hstep =>
        rw [BCA_LTS.step_countInitRecv_eq hstep p b (by intro s d m; simp)] at hamp
        unfold BCA_LTS.amplifyThreshold at hamp hprev_low; omega
      | .send .., hstep =>
        rw [BCA_LTS.step_countInitRecv_eq hstep p b (by intro s d m; simp)] at hamp
        unfold BCA_LTS.amplifyThreshold at hamp hprev_low; omega
      | .recv _ _ .echo _, hstep =>
        rw [BCA_LTS.step_countInitRecv_eq hstep p b (by intro s d m; simp)] at hamp
        unfold BCA_LTS.amplifyThreshold at hamp hprev_low; omega
      | .recv _ _ .vote _, hstep =>
        rw [BCA_LTS.step_countInitRecv_eq hstep p b (by intro s d m; simp)] at hamp
        unfold BCA_LTS.amplifyThreshold at hamp hprev_low; omega
      | .output .., hstep =>
        rw [BCA_LTS.step_countInitRecv_eq hstep p b (by intro s d m; simp)] at hamp
        unfold BCA_LTS.amplifyThreshold at hamp hprev_low; omega
      | .input .., hstep =>
        rw [BCA_LTS.step_countInitRecv_eq hstep p b (by intro s d m; simp)] at hamp
        unfold BCA_LTS.amplifyThreshold at hamp hprev_low; omega

/-- `approved b` implies `countInitRecv(p, b) ≥ approveThreshold`. -/
theorem approved_implies_quorum {s : BCA_LTS.State T n}
    (hreach : LTS.Reachable (BCA_LTS.bca T n f) s)
    (p : Fin n) (b : T)
    (hcorr_p : BCA_LTS.isCorrect T n s p)
    (happroved : (s.local_ p).approved b = true) :
    BCA_LTS.countInitRecv T n (s.local_ p) b ≥ BCA_LTS.approveThreshold n f := by
  induction hreach with
  | init hinit =>
    obtain ⟨hlocal, _, _⟩ := hinit
    simp [hlocal, BCA_LTS.LocalState.init] at happroved
  | step hreach_prev hstep ih =>
    have hcp := BCA_LTS.step_correct_prev hstep p hcorr_p
    rename_i s0 _ _
    by_cases hprev : (s0.local_ p).approved b = true
    · have := ih hcp hprev
      have := BCA_LTS.step_countInitRecv_mono hstep p b
      omega
    · -- Newly set: only recv init(some b') to p=dst can set approved.
      rename_i l _
      match l with
      | .recv src dst .init mv =>
        by_cases hp : p = dst
        · subst hp
          rcases mv with _ | b'
          · -- mv = none: local_ p unchanged (none branch) → contradiction
            obtain ⟨_, rfl⟩ := hstep; simp only [↓reduceIte] at happroved
            exact absurd happroved hprev
          · -- mv = some b'. Check if b = b'.
            by_cases hdup : (s0.local_ p).initRecv src b' = false
            · -- New entry. Use recv_init_countInitRecv_inc for b'.
              by_cases hbb : b = b'
              · subst hbb
                have hinc := BCA_LTS.recv_init_countInitRecv_inc hstep hdup
                have hgate := BCA_LTS.recv_init_approved_threshold hstep hdup hprev happroved
                omega
              · -- b ≠ b'. Receiving init(b') doesn't set approved(b).
                rw [BCA_LTS.recv_init_approved_other hstep hbb] at happroved
                exact absurd happroved hprev
            · -- Duplicate: local_ p unchanged → contradiction
              obtain ⟨_, rfl⟩ := hstep; simp only [↓reduceIte, hdup,
                Bool.true_eq_false] at happroved
              exact absurd happroved hprev
        · rw [BCA_LTS.recv_local_other hstep p hp] at happroved
          simp [happroved] at hprev
      | .corrupt _ | .send .. | .recv _ _ .echo _ | .recv _ _ .vote _ | .output .. | .input .. =>
        rw [BCA_LTS.step_approved_eq hstep p b (by intro s d m; simp)] at happroved
        exact absurd happroved hprev

/-- `approved b` implies `|corrupted| + inputSupport(b) ≥ f + 1`. -/
theorem approval_implies_inputSupport {s : BCA_LTS.State T n}
    (hreach : LTS.Reachable (BCA_LTS.bca T n f) s)
    (hn : n > 3 * f)
    (p : Fin n) (b : T)
    (hcorr_p : BCA_LTS.isCorrect T n s p)
    (happroved : (s.local_ p).approved b = true) :
    s.corrupted.length +
    ((List.finRange n).filter (fun q =>
      decide (q ∉ s.corrupted) && decide ((s.local_ q).input = some b))).length ≥
    f + 1 := by
  have hcount : BCA_LTS.countInitRecv T n (s.local_ p) b ≥ BCA_LTS.amplifyThreshold f := by
    have hq := approved_implies_quorum T n f hreach p b hcorr_p happroved
    unfold BCA_LTS.approveThreshold at hq
    unfold BCA_LTS.amplifyThreshold
    have hle : f + 1 ≤ n - f := by
      have : f ≤ n := by omega
      omega
    omega
  exact amplify_implies_inputSupport T n f b hreach p hcorr_p hcount

/-- Find two distinct approved values for process p, using input candidates. -/
private def findTwoApproved (s : BCA_LTS.State T n) (p : Fin n) :
    Option { pair : T × T // pair.1 ≠ pair.2 ∧
      (s.local_ p).approved pair.1 = true ∧ (s.local_ p).approved pair.2 = true } :=
  let candidates := inputCandidates T n s
  let pred := fun (pair : T × T) =>
    decide (pair.1 ≠ pair.2) &&
    decide ((s.local_ p).approved pair.1 = true) &&
    decide ((s.local_ p).approved pair.2 = true)
  let pairs := (candidates.flatMap (fun b₁ => candidates.map (fun b₂ => (b₁, b₂))))
  match hfind : pairs.find? pred with
  | some pair =>
    have hpred : pred pair = true := List.find?_some hfind
    some ⟨pair,
      by simp only [pred, Bool.and_eq_true, decide_eq_true_eq] at hpred; exact hpred.1.1,
      by simp only [pred, Bool.and_eq_true, decide_eq_true_eq] at hpred; exact hpred.1.2,
      by simp only [pred, Bool.and_eq_true, decide_eq_true_eq] at hpred; exact hpred.2⟩
  | none => none

/-- Completeness: if two distinct approved values exist, `findTwoApproved` finds them. -/
private theorem findTwoApproved_complete {s : BCA_LTS.State T n}
    (hreach : LTS.Reachable (BCA_LTS.bca T n f) s)
    (hn : n > 3 * f)
    (p : Fin n) (hcorr : BCA_LTS.isCorrect T n s p)
    (h : ∃ v₁ v₂ : T, v₁ ≠ v₂ ∧
        (s.local_ p).approved v₁ = true ∧ (s.local_ p).approved v₂ = true) :
    (findTwoApproved T n s p).isSome = true := by
  obtain ⟨v₁, v₂, hne, ha1, ha2⟩ := h
  have hmem_of_approved : ∀ v, (s.local_ p).approved v = true → v ∈ inputCandidates T n s := by
    intro v hav
    have hais := approval_implies_inputSupport T n f hreach hn p v hcorr hav
    have hpos : ((List.finRange n).filter (fun q =>
        decide (q ∉ s.corrupted) && decide ((s.local_ q).input = some v))).length > 0 := by
      have := corrupted_budget T n f hreach; omega
    obtain ⟨q, hq⟩ := List.exists_mem_of_length_pos hpos
    simp only [decide_not, List.mem_filter, List.mem_finRange, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, decide_eq_true_eq,
      true_and] at hq
    exact List.mem_filterMap.mpr ⟨q, List.mem_finRange q, hq.2⟩
  have hmem1 := hmem_of_approved v₁ ha1
  have hmem2 := hmem_of_approved v₂ ha2
  have hpair_mem : (v₁, v₂) ∈ (inputCandidates T n s).flatMap (fun b₁ =>
    (inputCandidates T n s).map (fun b₂ => (b₁, b₂))) :=
    List.mem_flatMap.mpr ⟨v₁, hmem1, List.mem_map.mpr ⟨v₂, hmem2, rfl⟩⟩
  unfold findTwoApproved
  simp only
  split
  · rfl
  · next hfind =>
    have hnone := List.find?_eq_none.mp hfind (v₁, v₂) hpair_mem
    simp [hne, ha1, ha2] at hnone

/-- `echoed = some b` implies `approved b` for correct processes. -/
theorem echoed_implies_approved {s : BCA_LTS.State T n}
    (hreach : LTS.Reachable (BCA_LTS.bca T n f) s)
    (p : Fin n) (b : T)
    (hcorr_p : BCA_LTS.isCorrect T n s p)
    (hechoed : (s.local_ p).echoed = some b) :
    (s.local_ p).approved b = true := by
  induction hreach with
  | init hinit =>
    obtain ⟨hlocal, _, _⟩ := hinit
    simp [hlocal, BCA_LTS.LocalState.init] at hechoed
  | step hreach_prev hstep ih =>
    have hcp := BCA_LTS.step_correct_prev hstep p hcorr_p
    rename_i s_prev l _
    by_cases hprev : (s_prev.local_ p).echoed = some b
    · exact BCA_LTS.step_approved_persist hstep p b (ih hcp hprev)
    · -- echoed was just set. Only send echo can set echoed for correct processes.
      match l with
      | .send src dst .echo mv =>
        by_cases hp : p = src
        · subst hp
          rcases mv with _ | bv
          · rw [BCA_LTS.send_echo_none_echoed hstep] at hechoed
            exact absurd hechoed hprev
          · have hechoed_val := BCA_LTS.send_echo_echoed_correct hstep hcp
            rw [hechoed_val] at hechoed
            have hbv : bv = b := Option.some.inj hechoed
            rw [hbv] at hstep
            have ⟨happr, _⟩ := BCA_LTS.send_echo_gate hstep hcp
            exact BCA_LTS.step_approved_persist hstep p b happr
        · rw [BCA_LTS.send_echo_echoed_other hstep p hp] at hechoed
          exact absurd hechoed hprev
      | .corrupt _ | .send _ _ .init _ | .send _ _ .vote _ | .recv .. | .output .. | .input .. =>
        rw [BCA_LTS.step_echoed_eq hstep p (by intro d m h; simp at h)] at hechoed
        exact absurd hechoed hprev

/-- `voted none` and `voted (some b)` are mutually exclusive for correct processes. -/
theorem voted_none_excludes_some {s : BCA_LTS.State T n}
    (hreach : LTS.Reachable (BCA_LTS.bca T n f) s)
    (p : Fin n) (b : T)
    (hcorr : BCA_LTS.isCorrect T n s p)
    (hvnone : (s.local_ p).voted none = true)
    (hvsome : (s.local_ p).voted (some b) = true) : False := by
  induction hreach with
  | init hinit =>
    obtain ⟨hlocal, _, _⟩ := hinit
    simp [hlocal, BCA_LTS.LocalState.init] at hvnone
  | step hreach_prev hstep ih =>
    have hcp := BCA_LTS.step_correct_prev hstep p hcorr
    rename_i s_prev l _
    by_cases hprev_some : (s_prev.local_ p).voted (some b) = true
    · -- Yes. Was voted(none) already true in prev?
      by_cases hprev_none : (s_prev.local_ p).voted none = true
      · exact ih hcp hprev_none hprev_some
      · -- voted(none) newly set by this step. Must be send vote(none) with src = p.
        match l with
        | .send src dst .vote mv =>
          by_cases hp : p = src
          · subst hp
            rcases hstep.1 with hbyz | ⟨_, _, huniq, _⟩
            · exact absurd hbyz hcp
            · -- huniq: ∀ w, voted(prev) w → w = mv
              have := huniq _ hprev_some
              have hmv : mv = none := by
                if hne : mv = none then exact hne else
                exact absurd (by
                rwa [BCA_LTS.send_vote_voted_correct_other hstep hcp _ (Ne.symm hne)]
                at hvnone) hprev_none
              subst hmv; simp at this
          · rw [BCA_LTS.send_vote_voted_other hstep p hp] at hvnone
            exact hprev_none hvnone
        | .corrupt _ | .send _ _ .init _ | .send _ _ .echo _ | .recv .. | .output .. | .input .. =>
          rw [BCA_LTS.step_voted_eq hstep p none (by intro d m h; simp at h)] at hvnone
          exact hprev_none hvnone
    · -- voted(some b) newly set. Gate: ∀ w, voted w → w = some b.
      by_cases hprev_none : (s_prev.local_ p).voted none = true
      · match l with
        | .send src dst .vote mv =>
          by_cases hp : p = src
          · subst hp
            rcases hstep.1 with hbyz | ⟨_, _, huniq, _⟩
            · exact absurd hbyz hcp
            · have := huniq _ hprev_none
              have hmv : mv = some b := by
                if hne : mv = some b then exact hne else
                exact absurd (by
                rwa [BCA_LTS.send_vote_voted_correct_other hstep hcp _ (Ne.symm hne)]
                at hvsome) hprev_some
              subst hmv; simp at this
          · rw [BCA_LTS.send_vote_voted_other hstep p hp] at hvsome
            exact hprev_some hvsome
        | .corrupt _ | .send _ _ .init _ | .send _ _ .echo _ | .recv .. | .output .. | .input .. =>
          rw [BCA_LTS.step_voted_eq hstep p (some b) (by intro d m h; simp at h)] at hvsome
          exact hprev_some hvsome
      · -- Neither was true in prev. Both newly set by this step.
        match l with
        | .send src dst .vote mv =>
          by_cases hp : p = src
          · subst hp
            by_cases hmv : mv = none
            · subst hmv
              rw [BCA_LTS.send_vote_voted_correct_other hstep hcp (some b) (by simp)] at hvsome
              exact hprev_some hvsome
            · rw [BCA_LTS.send_vote_voted_correct_other hstep hcp none (Ne.symm hmv)] at hvnone
              exact hprev_none hvnone
          · rw [BCA_LTS.send_vote_voted_other hstep p hp] at hvnone hvsome
            exact hprev_none hvnone
        | .corrupt _ | .send _ _ .init _ | .send _ _ .echo _ | .recv .. | .output .. | .input .. =>
          rw [BCA_LTS.step_voted_eq hstep p none (by intro d m h; simp at h)] at hvnone
          exact hprev_none hvnone

/-- `voted none` implies two distinct values are approved. -/
theorem voted_none_implies_two_approved {s : BCA_LTS.State T n}
    (hreach : LTS.Reachable (BCA_LTS.bca T n f) s)
    (p : Fin n)
    (hcorr : BCA_LTS.isCorrect T n s p)
    (hvoted : (s.local_ p).voted none = true) :
    ∃ v₁ v₂ : T, v₁ ≠ v₂ ∧ (s.local_ p).approved v₁ = true ∧ (s.local_ p).approved v₂ = true := by
  induction hreach with
  | init hinit =>
    obtain ⟨hlocal, _, _⟩ := hinit
    simp [hlocal, BCA_LTS.LocalState.init] at hvoted
  | step hreach_prev hstep ih =>
    have hcp := BCA_LTS.step_correct_prev hstep p hcorr
    rename_i s_prev l _
    by_cases hprev : (s_prev.local_ p).voted none = true
    · -- Already true in pre-state. By IH, both approved in pre-state.
      obtain ⟨v₁, v₂, hne, h1, h2⟩ := ih hcp hprev
      exact ⟨v₁, v₂, hne, BCA_LTS.step_approved_persist hstep p v₁ h1,
        BCA_LTS.step_approved_persist hstep p v₂ h2⟩
    · -- Newly set. Must be send vote(none) with src = p.
      match l with
      | .send src dst .vote mv =>
        by_cases hp : p = src
        · subst hp
          rcases hstep.1 with hbyz | ⟨_, _, huniq, hgate⟩
          · exact absurd hbyz hcp
          · -- voted(none) is true in post but false in pre.
            have hmv : mv = none := by
              if hne : mv = none then exact hne else
              exact absurd (by
              rwa [BCA_LTS.send_vote_voted_correct_other hstep hcp _ (Ne.symm hne)] at hvoted) hprev
            subst hmv
            obtain ⟨v₁, v₂, hne, ha1, ha2⟩ := hgate
            exact ⟨v₁, v₂, hne,
              BCA_LTS.step_approved_persist hstep p v₁ ha1,
              BCA_LTS.step_approved_persist hstep p v₂ ha2⟩
        · rw [BCA_LTS.send_vote_voted_other hstep p hp] at hvoted
          exact absurd hvoted hprev
      | .corrupt _ | .send _ _ .init _ | .send _ _ .echo _ | .recv .. | .output .. | .input .. =>
        rw [BCA_LTS.step_voted_eq hstep p none (by intro d m h; simp at h)] at hvoted
        exact absurd hvoted hprev

/-- echoSupport is monotone across steps. -/
theorem step_echoSupport_mono {s s' : BCA_LTS.State T n} {l : BCA_LTS.Label T n}
    (h : (BCA_LTS.bca T n f).step s l s') (b : T) :
    echoSupport T n s b ≤ echoSupport T n s' b := by
  unfold echoSupport
  exact corrupted_plus_filter_mono n s.corrupted s'.corrupted
    (step_corrupted_grow T n f h) _ _
    (fun p hcorr hech => by
    simp only [decide_eq_true_eq] at hech ⊢
    exact BCA_LTS.step_echoed_persist h p b hcorr hech)

/-- echoSupport is monotone along valid executions. -/
theorem echoSupport_mono_along
    {e : Execution (BCA_LTS.State T n) (BCA_LTS.Label T n)}
    (hv : (BCA_LTS.bca T n f).valid_exec e) (b : T)
    {k : Nat} :
    ∀ k', k ≤ k' → echoSupport T n (e.states k) b ≤ echoSupport T n (e.states k') b := by
  intro k'; induction k' with
  | zero => intro hle; rw [show k = 0 from Nat.le_zero.mp hle]
  | succ k' ih =>
    intro hle; rcases Nat.eq_or_lt_of_le hle with rfl | hlt
    · exact Nat.le_refl _
    · exact Nat.le_trans (ih (by omega)) (step_echoSupport_mono T n f (hv.2 k') b)

/-- echoSupport is unchanged when corrupted and echoed are unchanged. -/
private theorem echoSupport_eq_of_eq {s_r s_r' : BCA_LTS.State T n}
    (hc : s_r'.corrupted = s_r.corrupted)
    (hechoed : ∀ p, (s_r'.local_ p).echoed = (s_r.local_ p).echoed)
    (b : T) : echoSupport T n s_r' b = echoSupport T n s_r b := by
  unfold echoSupport; rw [hc]; congr 1
  exact congrArg List.length (List.filter_congr (fun p _ => by simp [hechoed p]))

/-- voteContention is monotone across steps. -/
private theorem step_voteContention_mono {s s' : BCA_LTS.State T n} {l : BCA_LTS.Label T n}
    (h : (BCA_LTS.bca T n f).step s l s') :
    voteContention T n f s → voteContention T n f s' := by
  unfold voteContention
  intro ⟨b₁, b₂, hne, hf1, hf2⟩
  suffices hmono : ∀ b, s.corrupted.length +
      ((List.finRange n).filter (fun p =>
        decide (p ∉ s.corrupted) && ((s.local_ p).voted none ||
        (s.local_ p).voted (some b)))).length ≤ s'.corrupted.length +
      ((List.finRange n).filter (fun p =>
        decide (p ∉ s'.corrupted) && ((s'.local_ p).voted none ||
        (s'.local_ p).voted (some b)))).length from
    ⟨b₁, b₂, hne, Nat.le_trans hf1 (hmono b₂), Nat.le_trans hf2 (hmono b₁)⟩
  intro b
  exact corrupted_plus_filter_mono n s.corrupted s'.corrupted (step_corrupted_grow T n f h) _ _
    (fun p hcorr_p hpre => by
      simp only [Bool.or_eq_true] at hpre ⊢
      rcases hpre with hvn | hvb
      · left; exact BCA_LTS.step_voted_none_persist h p hcorr_p hvn
      · right; exact BCA_LTS.step_voted_persist h p b hcorr_p hvb)

theorem voted_some_implies_echoSupport {s : BCA_LTS.State T n}
    (hreach : LTS.Reachable (BCA_LTS.bca T n f) s)
    (p : Fin n) (b : T)
    (hcorr_p : BCA_LTS.isCorrect T n s p)
    (hvoted : (s.local_ p).voted (some b) = true) :
    echoSupport T n s b ≥ BCA_LTS.echoThreshold n f := by
  induction hreach with
  | init hinit =>
    obtain ⟨hlocal, _, _⟩ := hinit
    simp [hlocal p, BCA_LTS.LocalState.init] at hvoted
  | step hreach_prev hstep ih =>
    have hcp := BCA_LTS.step_correct_prev hstep p hcorr_p
    rename_i s_prev l _
    by_cases hvprev : (s_prev.local_ p).voted (some b) = true
    · -- Already true: use IH + monotonicity
      exact Nat.le_trans (ih hcp hvprev)
        (step_echoSupport_mono T n f hstep b)
    · -- Newly set: must be send vote with src=p, mv=some b
      match l with
      | .send src dst .vote mv =>
        by_cases hsrc : p = src
        · subst hsrc
          have hgate := hstep.1
          rcases hgate with hbyz | ⟨_, _, hvote_uniq, hecho_quorum⟩
          · exact absurd hbyz hcp
          · -- mv must be some b (since voted(some b) is true and wasn't before)
            have hmv : mv = some b := by
              by_cases hmv : mv = some b
              · exact hmv
              · rw [BCA_LTS.send_vote_voted_correct_other hstep hcp _ (Ne.symm hmv)] at hvoted
                exact absurd hvoted hvprev
            subst hmv
            have hecho_prev : echoSupport T n s_prev b ≥ BCA_LTS.echoThreshold n f := by
              unfold echoSupport
              unfold BCA_LTS.countEchoRecv BCA_LTS.echoThreshold at hecho_quorum
              apply Nat.le_trans hecho_quorum
              apply Nat.le_trans (filter_length_mono
                (fun q => (s_prev.local_ p).echoRecv q b)
                (fun q => decide (q ∈ s_prev.corrupted) ||
                  (decide (q ∉ s_prev.corrupted) && decide ((s_prev.local_ q).echoed = some b)))
                (List.finRange n)
                (fun q hq => by
                  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hq ⊢
                  by_cases hcq : q ∈ s_prev.corrupted
                  · left; exact hcq
                  · right; exact ⟨hcq, echo_trace T n f hreach_prev p q b hcq hq⟩))
              have hor := filter_or_le
                (fun q => decide (q ∈ s_prev.corrupted))
                (fun q =>
                  decide (q ∉ s_prev.corrupted) && decide ((s_prev.local_ q).echoed = some b))
                (List.finRange n)
              have hcorr_le : ((List.finRange n).filter
                  (fun q => decide (q ∈ s_prev.corrupted))).length ≤ s_prev.corrupted.length :=
                nodup_sub_length ((finRange_nodup n).sublist List.filter_sublist)
                  (fun x hx => by simp only [List.mem_filter, List.mem_finRange, decide_eq_true_eq,
                    true_and] at hx; exact hx)
              omega
            exact Nat.le_trans hecho_prev (step_echoSupport_mono T n f hstep b)
        · -- p ≠ src: voted unchanged for p
          rw [BCA_LTS.send_vote_voted_other hstep p hsrc] at hvoted
          exact absurd hvoted hvprev
      | .corrupt _ | .send _ _ .init _ | .send _ _ .echo _ | .recv .. | .output .. | .input .. =>
        rw [BCA_LTS.step_voted_eq hstep p (some b) (by intro d m h; simp at h)] at hvoted
        exact absurd hvoted hvprev

/-! ### Preservation Helpers -/

/-- sim_rel preserved when all relevant fields are unchanged. -/
private def sim_rel_preserved_trivial [Inhabited T]
    {s_r s_r' : BCA_LTS.State T n} {s_i : IdealBCA.State T n}
    (hR : sim_rel T n f s_r s_i)
    (hc : s_r'.corrupted = s_r.corrupted)
    (hechoed : ∀ p, (s_r'.local_ p).echoed = (s_r.local_ p).echoed)
    (hvoted : ∀ p w, (s_r'.local_ p).voted w = (s_r.local_ p).voted w)
    (hinp : ∀ p, (s_r'.local_ p).input = (s_r.local_ p).input)
    (hdec : ∀ p, (s_r'.local_ p).decided = (s_r.local_ p).decided) :
    Σ' s₂', InternalStar (IdealBCA.ideal_bca T n f)
      (IdealBCA.ideal_labelling T n) s_i s₂' ×'
      sim_rel T n f s_r' s₂' := by
  have hecho_eq : ∀ b, echoSupport T n s_r' b = echoSupport T n s_r b :=
    echoSupport_eq_of_eq T n hc hechoed
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hR
  refine ⟨s_i, .refl, h1.trans hc.symm, ?_, ?_, ?_, ?_, ?_⟩
  · intro p; rw [h2, hinp]
  · intro p; rw [h3, hdec]
  · intro b hb; rw [hecho_eq] at hb; rcases h4 b hb with hval | hvc_pre
    · exact Or.inl hval;
    · exact Or.inr (by rwa [voteContention_eq T n f hc hvoted])
  · intro hvc; apply h5; rwa [← voteContention_eq T n f hc hvoted]
  · intro b hb; rcases h6 b hb with hecho | hcont
    · left; rw [hecho_eq]; exact hecho
    · right; rwa [voteContention_eq T n f hc hvoted]

/-- sim_rel preserved when echoSupport is unchanged and voteContention is monotone. -/
private def sim_rel_preserved_echo_eq [Inhabited T]
    {s_r s_r' : BCA_LTS.State T n} {l : BCA_LTS.Label T n} {s_i : IdealBCA.State T n}
    (hR : sim_rel T n f s_r s_i)
    (hstep : (BCA_LTS.bca T n f).step s_r l s_r')
    (hc : s_r'.corrupted = s_r.corrupted)
    (hecho_eq : ∀ b, echoSupport T n s_r' b = echoSupport T n s_r b)
    (hinp : ∀ p, (s_r'.local_ p).input = (s_r.local_ p).input)
    (hdec : ∀ p, (s_r'.local_ p).decided = (s_r.local_ p).decided)
    (hvc_bound : voteContention T n f s_r' → s_i.bound_value ≠ none) :
    Σ' s₂', InternalStar (IdealBCA.ideal_bca T n f)
      (IdealBCA.ideal_labelling T n) s_i s₂' ×'
      sim_rel T n f s_r' s₂' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hR
  refine ⟨s_i, .refl, h1.trans hc.symm, ?_, ?_, ?_, ?_, ?_⟩
  · intro p; rw [h2, hinp]
  · intro p; rw [h3, hdec]
  · intro b hb; rw [hecho_eq] at hb; rcases h4 b hb with hval | hvc_pre
    · exact Or.inl hval
    · exact Or.inr (step_voteContention_mono T n f hstep hvc_pre)
  · exact hvc_bound
  · intro b hb; rcases h6 b hb with hecho | hcont
    · left; rw [hecho_eq]; exact hecho
    · right; exact step_voteContention_mono T n f hstep hcont

/-- At a reachable state, `voteContention` is decidable by searching
    `echoCandidates ++ inputCandidates`. Any value `b` with `voted (some b) = true`
    at a correct process must be in `echoCandidates` (via `voted_some_implies_echoSupport`).
    If only `voted none` processes contribute, any two distinct values from
    `inputCandidates` work (via `voted_none_implies_two_approved` +
    `approval_implies_inputSupport`). -/
private def decidableVoteContention [Inhabited T] [Inhabited (Fin n)]
    (s : BCA_LTS.State T n) (hreach : LTS.Reachable (BCA_LTS.bca T n f) s) (hn : n > 3 * f)
    (hbudget : s.corrupted.length ≤ f) :
    Decidable (voteContention T n f s) := by
  let search := (echoCandidates T n s ++ inputCandidates T n s)
  let pred := fun (pair : T × T) =>
    decide (pair.1 ≠ pair.2) &&
    decide (s.corrupted.length + ((List.finRange n).filter (fun p =>
      decide (p ∉ s.corrupted) &&
      ((s.local_ p).voted none || (s.local_ p).voted (some pair.2)))).length ≥ n - f) &&
    decide (s.corrupted.length + ((List.finRange n).filter (fun p =>
      decide (p ∉ s.corrupted) &&
      ((s.local_ p).voted none || (s.local_ p).voted (some pair.1)))).length ≥ n - f)
  let pairs := search.flatMap (fun b₁ => search.map (fun b₂ => (b₁, b₂)))
  -- Find a pair computably
  let result := pairs.find? pred
  match hfind : result with
  | some ⟨b₁, b₂⟩ =>
    have hpred : pred (b₁, b₂) = true := List.find?_some hfind
    have hp := by simp only [pred, Bool.and_eq_true, decide_eq_true_eq] at hpred; exact hpred
    exact isTrue ⟨b₁, b₂, hp.1.1, hp.1.2, hp.2⟩
  | none =>
    exact isFalse (fun ⟨b₁, b₂, hne, hcf1, hcf2⟩ => by
      have hany_false : ¬ ∃ x, x ∈ pairs ∧ pred x = true := by
        intro ⟨x, hmem, hpred⟩
        have := List.find?_eq_none.mp hfind x hmem
        simp [hpred] at this
      -- Show b₁ and b₂ can be replaced by values in `search`
      -- For any b with high count: either a correct process voted (some b) → b ∈ echoCandidates,
      -- or all counted correct processes voted none → any value in inputCandidates works
      -- Key: if no correct process voted (some b), count for b = count for any other value
      have hreplace : ∀ b, s.corrupted.length + ((List.finRange n).filter (fun p =>
          decide (p ∉ s.corrupted) &&
          ((s.local_ p).voted none || (s.local_ p).voted (some b)))).length ≥ n - f →
          ∃ b' ∈ search, s.corrupted.length + ((List.finRange n).filter (fun p =>
            decide (p ∉ s.corrupted) &&
            ((s.local_ p).voted none || (s.local_ p).voted (some b')))).length ≥ n - f := by
        intro b hge
        -- Is b voted by some correct process?
        by_cases hvoted_b : ∃ p : Fin n, p ∉ s.corrupted ∧ (s.local_ p).voted (some b) = true
        · -- Yes: b ∈ echoCandidates via voted_some_implies_echoSupport
          obtain ⟨p, hcorr_p, hvp⟩ := hvoted_b
          have hes := voted_some_implies_echoSupport T n f hreach p b hcorr_p hvp
          exact ⟨b, List.mem_append.mpr (Or.inl
            (echoSupport_in_candidates T n b (by unfold BCA_LTS.echoThreshold at hes; omega))), hge⟩
        · -- No: count for b = corrupted + none_voters (same for any value)
          simp only [not_exists, not_and] at hvoted_b
          -- The filter only counts none-voters (since no correct process voted some b)
          have hcount_eq : ∀ b', ((List.finRange n).filter (fun p =>
              decide (p ∉ s.corrupted) &&
              ((s.local_ p).voted none || (s.local_ p).voted (some b)))).length ≤
            ((List.finRange n).filter (fun p =>
              decide (p ∉ s.corrupted) &&
              ((s.local_ p).voted none || (s.local_ p).voted (some b')))).length := by
            intro b'
            apply filter_length_mono
            intro p; simp only [decide_not, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
              decide_eq_false_iff_not, Bool.or_eq_true, and_imp]
            intro hcorr hvote
            exact ⟨hcorr, hvote.elim Or.inl (fun hvs => absurd hvs (hvoted_b p hcorr))⟩
          -- Need any value in search. The count is ≥ n-f, so some correct process voted none.
          have hfilt_pos : ((List.finRange n).filter (fun p =>
              decide (p ∉ s.corrupted) && (s.local_ p).voted none)).length > 0 := by
            have : ((List.finRange n).filter (fun p => decide (p ∉ s.corrupted) &&
                ((s.local_ p).voted none || (s.local_ p).voted (some b)))).length > 0 := by omega
            apply Nat.lt_of_lt_of_le this
            apply filter_length_mono
            intro p; simp only [decide_not, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
              decide_eq_false_iff_not, Bool.or_eq_true, and_imp]
            intro hcorr hvote
            exact ⟨hcorr, hvote.elim id (fun hvs => absurd hvs (hvoted_b p hcorr))⟩
          obtain ⟨p, hp⟩ := List.exists_mem_of_length_pos hfilt_pos
          simp only [decide_not, List.mem_filter, List.mem_finRange, Bool.and_eq_true,
            Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, true_and] at hp
          -- p voted none → two approved → one is in inputCandidates
          have ⟨v₁, _, _, ha1, _⟩ := voted_none_implies_two_approved T n f hreach p hp.1 hp.2
          have hais := approval_implies_inputSupport T n f hreach hn p v₁ hp.1 ha1
          have hpos : ((List.finRange n).filter (fun q =>
              decide (q ∉ s.corrupted) && decide ((s.local_ q).input = some v₁))).length > 0 :=
              by omega
          obtain ⟨q, hq⟩ := List.exists_mem_of_length_pos hpos
          simp only [decide_not, List.mem_filter, List.mem_finRange, Bool.and_eq_true,
            Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, decide_eq_true_eq,
            true_and] at hq
          exact ⟨v₁, List.mem_append.mpr (Or.inr
            (List.mem_filterMap.mpr ⟨q, List.mem_finRange q, hq.2⟩)),
            Nat.le_trans hge (Nat.add_le_add_left (hcount_eq v₁) _)⟩
      -- Now use hreplace to find b₁', b₂' in search
      obtain ⟨b₁', hb₁'_mem, hb₁'_ge⟩ := hreplace b₁ hcf2
      obtain ⟨b₂', hb₂'_mem, hb₂'_ge⟩ := hreplace b₂ hcf1
      -- Need b₁' ≠ b₂'. If b₁' = b₂', find a second value.
      by_cases hne' : b₁' ≠ b₂'
      · have hmem : (b₁', b₂') ∈ pairs := List.mem_flatMap.mpr ⟨b₁', hb₁'_mem,
          List.mem_map.mpr ⟨b₂', hb₂'_mem, rfl⟩⟩
        have hpred : pred (b₁', b₂') = true := by
          simp only [pred, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨⟨hne', hb₂'_ge⟩, hb₁'_ge⟩
        exact absurd ⟨(b₁', b₂'), hmem, hpred⟩ hany_false
      · -- b₁' = b₂'
        have hne' : b₁' = b₂' := Decidable.not_not.mp hne'
        subst hne'
        exfalso
        -- Case split:
        by_cases hvb₁ : ∃ p : Fin n, p ∉ s.corrupted ∧ (s.local_ p).voted (some b₁) = true
        · -- b₁ ∈ echoCandidates
          obtain ⟨p₁, hcp₁, hvp₁⟩ := hvb₁
          have hb₁_search : b₁ ∈ search := List.mem_append.mpr (Or.inl
            (echoSupport_in_candidates T n b₁ (by
              have := voted_some_implies_echoSupport T n f hreach p₁ b₁ hcp₁ hvp₁
              unfold BCA_LTS.echoThreshold at this; omega)))
          by_cases hvb₂ : ∃ p : Fin n, p ∉ s.corrupted ∧ (s.local_ p).voted (some b₂) = true
          · -- Both in echoCandidates: (b₁, b₂) is a valid pair
            obtain ⟨p₂, hcp₂, hvp₂⟩ := hvb₂
            have hb₂_search : b₂ ∈ search := List.mem_append.mpr (Or.inl
              (echoSupport_in_candidates T n b₂ (by
                have := voted_some_implies_echoSupport T n f hreach p₂ b₂ hcp₂ hvp₂
                unfold BCA_LTS.echoThreshold at this; omega)))
            exact hany_false ⟨(b₁, b₂), List.mem_flatMap.mpr ⟨b₁, hb₁_search,
              List.mem_map.mpr ⟨b₂, hb₂_search, rfl⟩⟩,
              by simp only [pred, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨hne, hcf1⟩, hcf2⟩⟩
          · -- b₂ not voted-some: count b₂ = corrupted + none_voters
            -- Find a none-voter from b₂'s count
            simp only [not_exists, not_and] at hvb₂
            have : ((List.finRange n).filter (fun p => decide (p ∉ s.corrupted) &&
                ((s.local_ p).voted none || (s.local_ p).voted (some b₂)))).length > 0 := by omega
            obtain ⟨p, hp⟩ := List.exists_mem_of_length_pos this
            simp only [decide_not, List.mem_filter, List.mem_finRange, Bool.and_eq_true,
              Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Bool.or_eq_true,
              true_and] at hp
            have hvn : (s.local_ p).voted none = true :=
              hp.2.elim id (fun h => absurd h (hvb₂ p hp.1))
            -- p voted none → two approved values → two input candidates
            have ⟨v₁, v₂, hne_v, ha1, ha2⟩ :=
              voted_none_implies_two_approved T n f hreach p hp.1 hvn
            have hget_mem : ∀ v, (s.local_ p).approved v = true → v ∈ search := by
              intro v hav
              have hais := approval_implies_inputSupport T n f hreach hn p v hp.1 hav
              have hpos : ((List.finRange n).filter (fun q =>
                  decide (q ∉ s.corrupted) && decide ((s.local_ q).input = some v))).length > 0 :=
                  by omega
              obtain ⟨q, hq⟩ := List.exists_mem_of_length_pos hpos
              simp only [decide_not, List.mem_filter, List.mem_finRange, Bool.and_eq_true,
                Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, decide_eq_true_eq,
                true_and] at hq
              exact List.mem_append.mpr (Or.inr
                (List.mem_filterMap.mpr ⟨q, List.mem_finRange q, hq.2⟩))
            -- v₁ or v₂ ≠ b₁'. Use that one with b₁'.
            let ⟨v, hv_ne, hv_approved⟩ : { v : T // v ≠ b₁' ∧ (s.local_ p).approved v = true } :=
              if h : v₁ = b₁' then ⟨v₂, hne_v ∘ (· ▸ h), ha2⟩ else ⟨v₁, h, ha1⟩
            -- count for hv.1 ≥ corrupted + none_voters ≥ count for b₂ ≥ n-f
            have hv_count : s.corrupted.length + ((List.finRange n).filter (fun q =>
                decide (q ∉ s.corrupted) &&
                ((s.local_ q).voted none || (s.local_ q).voted (some v)))).length ≥ n - f := by
              apply Nat.le_trans hcf1; apply Nat.add_le_add_left
              apply filter_length_mono
              intro q; simp only [decide_not, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
                Bool.not_true, decide_eq_false_iff_not, Bool.or_eq_true, and_imp]
              intro hcorr hvote
              exact ⟨hcorr, hvote.elim Or.inl (fun h => absurd h (hvb₂ q hcorr))⟩
            exact hany_false ⟨(b₁', v), List.mem_flatMap.mpr ⟨b₁', hb₁'_mem,
              List.mem_map.mpr ⟨v, hget_mem v hv_approved, rfl⟩⟩, by
              simp only [pred, Bool.and_eq_true, decide_eq_true_eq]
              exact ⟨⟨hv_ne.symm, hv_count⟩, hb₁'_ge⟩⟩
        · -- b₁ not voted-some either: all counted = none-voters
          simp only [not_exists, not_and] at hvb₁
          -- Find a none-voter
          have : ((List.finRange n).filter (fun p => decide (p ∉ s.corrupted) &&
              ((s.local_ p).voted none || (s.local_ p).voted (some b₁)))).length > 0 := by omega
          obtain ⟨p, hp⟩ := List.exists_mem_of_length_pos this
          simp only [decide_not, List.mem_filter, List.mem_finRange, Bool.and_eq_true,
            Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Bool.or_eq_true,
            true_and] at hp
          have hvn : (s.local_ p).voted none = true :=
            hp.2.elim id (fun h => absurd h (hvb₁ p hp.1))
          have ⟨v₁, v₂, hne_v, ha1, ha2⟩ := voted_none_implies_two_approved T n f hreach p hp.1 hvn
          have hget_mem : ∀ v, (s.local_ p).approved v = true → v ∈ search := by
            intro v hav
            have hais := approval_implies_inputSupport T n f hreach hn p v hp.1 hav
            have hpos : ((List.finRange n).filter (fun q =>
                decide (q ∉ s.corrupted) && decide ((s.local_ q).input = some v))).length > 0 :=
                by omega
            obtain ⟨q, hq⟩ := List.exists_mem_of_length_pos hpos
            simp only [decide_not, List.mem_filter, List.mem_finRange, Bool.and_eq_true,
              Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, decide_eq_true_eq,
              true_and] at hq
            exact List.mem_append.mpr (Or.inr
              (List.mem_filterMap.mpr ⟨q, List.mem_finRange q, hq.2⟩))
          -- Both v₁, v₂ in search, v₁ ≠ v₂, counts ≥ n-f (= corrupted + none_voters)
          have hv_count : ∀ v, s.corrupted.length + ((List.finRange n).filter (fun q =>
              decide (q ∉ s.corrupted) &&
              ((s.local_ q).voted none || (s.local_ q).voted (some v)))).length ≥ n - f := by
            intro v; apply Nat.le_trans hcf2; apply Nat.add_le_add_left
            apply filter_length_mono
            intro q; simp only [decide_not, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
              decide_eq_false_iff_not, Bool.or_eq_true, and_imp]
            intro hcorr hvote
            exact ⟨hcorr, hvote.elim Or.inl (fun h => absurd h (hvb₁ q hcorr))⟩
          exact hany_false ⟨(v₁, v₂), List.mem_flatMap.mpr ⟨v₁, hget_mem v₁ ha1,
            List.mem_map.mpr ⟨v₂, hget_mem v₂ ha2, rfl⟩⟩, by
            simp only [pred, Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨⟨hne_v, hv_count v₂⟩, hv_count v₁⟩⟩)

/-- Find voteContention witnesses computably, or return none. -/
private def findVoteContention [Inhabited T] [Inhabited (Fin n)]
    (s : BCA_LTS.State T n) :
    Option { pair : T × T // pair.1 ≠ pair.2 ∧
      s.corrupted.length + ((List.finRange n).filter (fun p =>
        decide (p ∉ s.corrupted) &&
        ((s.local_ p).voted none || (s.local_ p).voted (some pair.2)))).length ≥ n - f ∧
      s.corrupted.length + ((List.finRange n).filter (fun p =>
        decide (p ∉ s.corrupted) &&
        ((s.local_ p).voted none || (s.local_ p).voted (some pair.1)))).length ≥ n - f } :=
  let search := echoCandidates T n s ++ inputCandidates T n s
  let pred := fun (pair : T × T) =>
    decide (pair.1 ≠ pair.2) &&
    decide (s.corrupted.length + ((List.finRange n).filter (fun p =>
      decide (p ∉ s.corrupted) &&
      ((s.local_ p).voted none || (s.local_ p).voted (some pair.2)))).length ≥ n - f) &&
    decide (s.corrupted.length + ((List.finRange n).filter (fun p =>
      decide (p ∉ s.corrupted) &&
      ((s.local_ p).voted none || (s.local_ p).voted (some pair.1)))).length ≥ n - f)
  let pairs := search.flatMap (fun b₁ => search.map (fun b₂ => (b₁, b₂)))
  match hfind : pairs.find? pred with
  | some pair =>
    have hpred := List.find?_some hfind
    some ⟨pair, by
    simp only [pred, Bool.and_eq_true, decide_eq_true_eq] at hpred
    exact ⟨hpred.1.1, hpred.1.2, hpred.2⟩⟩
  | none => none

/-- If voteContention holds at a reachable state, findVoteContention succeeds. -/
private theorem findVoteContention_complete [Inhabited T] [Inhabited (Fin n)]
    {s : BCA_LTS.State T n} (hreach : LTS.Reachable (BCA_LTS.bca T n f) s) (hn : n > 3 * f)
    (hbudget : s.corrupted.length ≤ f)
    (hvc : voteContention T n f s) :
    (findVoteContention T n f s).isSome = true := by
  unfold findVoteContention; simp only
  split
  · rfl
  · next hfind =>
    exfalso
    cases hdec : decidableVoteContention T n f s hreach hn hbudget with
    | isFalse h => exact h hvc
    | isTrue _ =>
      unfold decidableVoteContention at hdec; simp only at hdec; split at hdec;
      · next heq => exact absurd (heq.symm.trans hfind) (by simp)
      · next heq =>
        let toBool : Decidable (voteContention T n f s) → Bool := fun d => d.decide
        have : toBool (isFalse _) = toBool (isTrue _) := congrArg toBool hdec
        simp [toBool, Decidable.decide] at this

/-! ### Forward Simulation (skeleton) -/

/-- Transfer inputSupport bound from real state to ideal state via sim_rel. -/
private theorem inputSupport_transfer
    {s_r : BCA_LTS.State T n} {s_i : IdealBCA.State T n} {b : T}
    (hcorr : s_i.corrupted = s_r.corrupted)
    (hinp : ∀ p, s_i.input_ p = (s_r.local_ p).input)
    (hais : s_r.corrupted.length + realInputSupport T n s_r b ≥ f + 1) :
    s_i.corrupted.length + IdealBCA.inputSupport T n s_i b ≥ f + 1 := by
  rw [hcorr]; unfold IdealBCA.inputSupport
  apply Nat.le_trans hais; apply Nat.add_le_add_left
  apply filter_length_mono; intro q hq
  simp only [decide_not, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, decide_eq_true_eq, hcorr] at hq ⊢; rw [hinp]; exact hq

private def bca_init_sim [Inhabited T] [Inhabited (Fin n)] (hn : n > 3 * f) :
    ∀ s₁, (BCA_LTS.bca T n f).init s₁ →
      Σ' s₂, (IdealBCA.ideal_bca T n f).init s₂ ∧ sim_rel T n f s₁ s₂ := by
    intro s_r ⟨hlocal, hbuf, hcorr⟩
    refine ⟨⟨[], fun _ => none, none, fun _ => none⟩, ⟨rfl, fun _ => rfl, rfl, fun _ => rfl⟩, ?_⟩
    simp only [sim_rel]
    refine ⟨hcorr.symm, ?_, ?_, ?_, ?_, ?_⟩
    · intro p; simp [hlocal p, BCA_LTS.LocalState.init]
    · intro p; simp [hlocal p, BCA_LTS.LocalState.init]
    · intro b hb; exfalso
      simp only [echoSupport, hcorr, List.length_nil, List.not_mem_nil, not_false_eq_true,
        decide_true, Bool.true_and, zero_add, BCA_LTS.echoThreshold, ge_iff_le,
        tsub_le_iff_right] at hb
      have hne : ∀ p, (s_r.local_ p).echoed ≠ some b := by
        intro p; simp [hlocal p, BCA_LTS.LocalState.init]
      have hfilt : (List.finRange n).filter (fun p =>
        decide ((s_r.local_ p).echoed = some b)) = [] :=
        List.filter_eq_nil_iff.mpr (fun p _ => by simp [hne p])
      rw [hfilt] at hb; simp at hb; omega
    · intro hvc; unfold voteContention at hvc; rw [hcorr] at hvc; simp only [ne_eq,
      List.length_nil, List.not_mem_nil, not_false_eq_true, decide_true, Bool.true_and, zero_add,
      ge_iff_le, tsub_le_iff_right] at hvc
      obtain ⟨b₁, b₂, _, h1, _⟩ := hvc
      have hvnone : ∀ p : Fin n, (s_r.local_ p).voted none = false := by
        intro p; simp [hlocal p, BCA_LTS.LocalState.init]
      have hvsome : ∀ p : Fin n, ∀ b : T, (s_r.local_ p).voted (some b) = false := by
        intro p b; simp [hlocal p, BCA_LTS.LocalState.init]
      have hfilt_empty : ∀ b : T, (List.finRange n).filter
          (fun p => (s_r.local_ p).voted none || (s_r.local_ p).voted (some b)) = [] :=
        fun b => List.filter_eq_nil_iff.mpr (fun p _ => by simp [hvnone p, hvsome p])
      rw [hfilt_empty] at h1; simp at h1; omega
    · intro b hb; simp at hb

private def bca_step_internal [Inhabited T] [Inhabited (Fin n)] (hn : n > 3 * f) :
    ∀ s₁ l₁ s₁' s₂, LTS.Reachable (BCA_LTS.bca T n f) s₁ → sim_rel T n f s₁ s₂ →
      (BCA_LTS.bca_labelling T n).is_internal l₁ = true →
      (BCA_LTS.bca T n f).step s₁ l₁ s₁' →
      Σ' s₂', LTS.InternalStar (IdealBCA.ideal_bca T n f) (IdealBCA.ideal_labelling T n) s₂ s₂' ×'
        sim_rel T n f s₁' s₂' := by
    intro s_r l s_r' s_i hreach hR hint hstep
    simp only [BCA_LTS.bca_labelling] at hint
    rcases l with _ | ⟨src, dst, t, mv⟩ | ⟨src, dst, t, mv⟩ | _ | _
    · -- corrupt: not internal
      exact absurd hint (by simp)
    · -- send
      rcases t with _ | _ | _
      · -- send init: echoed, voted unchanged
        exact sim_rel_preserved_trivial T n f hR
          (BCA_LTS.send_corrupted hstep)
          (BCA_LTS.send_init_echoed hstep)
          (fun p w => BCA_LTS.send_init_voted hstep p w)
          (BCA_LTS.send_input hstep)
          (BCA_LTS.send_decided hstep)
      · -- send echo: echoed may change for src, voted unchanged
        rcases mv with _ | b
        · -- send echo none: echoed unchanged → trivially preserved
          exact sim_rel_preserved_trivial T n f hR
            (BCA_LTS.send_corrupted hstep)
            (BCA_LTS.send_echo_none_echoed hstep)
            (fun p w => BCA_LTS.send_echo_voted hstep p w)
            (BCA_LTS.send_input hstep)
            (BCA_LTS.send_decided hstep)
        · -- send echo (some b): echoed may change for src
          by_cases hbyz : src ∈ s_r.corrupted
          · -- src is byzantine: echoed unchanged
            have hgate := hstep.1
            exact sim_rel_preserved_trivial T n f hR
              (BCA_LTS.send_corrupted hstep)
              (fun p => by
                by_cases hp : p = src
                · exact hp ▸ BCA_LTS.send_echo_echoed_byzantine hstep hbyz
                · exact BCA_LTS.send_echo_echoed_other hstep p hp)
              (fun p w => BCA_LTS.send_echo_voted hstep p w)
              (BCA_LTS.send_input hstep)
              (BCA_LTS.send_decided hstep)
          · -- src is correct: echoed src → some b
            have hcorr_src : BCA_LTS.isCorrect T n s_r src := hbyz
            have hgate_detail := (hstep.1.resolve_left hbyz)
            obtain ⟨_, _, happroved, hechoed_old⟩ := hgate_detail
            have hcorr : s_r'.corrupted = s_r.corrupted := BCA_LTS.send_corrupted hstep
            have hechoed_src : (s_r'.local_ src).echoed = some b :=
              BCA_LTS.send_echo_echoed_correct hstep hcorr_src
            have hechoed_other : ∀ p, p ≠ src → (s_r'.local_ p).echoed = (s_r.local_ p).echoed :=
              fun p hp => BCA_LTS.send_echo_echoed_other hstep p hp
            have hvoted_eq : ∀ p w, (s_r'.local_ p).voted w = (s_r.local_ p).voted w :=
              fun p w => BCA_LTS.send_echo_voted hstep p w
            have hinp_eq : ∀ p, (s_r'.local_ p).input = (s_r.local_ p).input :=
              BCA_LTS.send_input hstep
            have hdec_eq : ∀ p, (s_r'.local_ p).decided = (s_r.local_ p).decided :=
              BCA_LTS.send_decided hstep
            have hecho_other_eq : ∀ b', b' ≠ b →
              echoSupport T n s_r' b' = echoSupport T n s_r b' := by
              intro b' hne; unfold echoSupport; rw [hcorr]; congr 1
              apply congrArg List.length; apply List.filter_congr; intro p _
              by_cases hp : p = src
              · subst hp; simp only [decide_not, hechoed_src, Option.some.injEq]
                rcases hechoed_old with heo | heo <;> simp [heo, hne.symm]
              · simp [hechoed_other p hp]
            have hecho_mono : echoSupport T n s_r b ≤ echoSupport T n s_r' b :=
              step_echoSupport_mono T n f hstep b
            obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hR
            by_cases hold : echoSupport T n s_r b ≥ BCA_LTS.echoThreshold n f
            · -- Already crossed: ideal stays put
              refine ⟨s_i, .refl, h1.trans hcorr.symm, ?_, ?_, ?_, ?_, ?_⟩
              · intro p; rw [h2, hinp_eq]
              · intro p; rw [h3, hdec_eq]
              · intro b' hb'; by_cases hbb : b' = b
                · rcases hbb ▸ h4 b hold with hval | hvc_pre
                  · exact Or.inl hval
                  · exact Or.inr (step_voteContention_mono T n f hstep hvc_pre)
                · rw [hecho_other_eq b' hbb] at hb'; rcases h4 b' hb' with hval | hvc_pre;
                  · exact Or.inl hval
                  · exact Or.inr (step_voteContention_mono T n f hstep hvc_pre)
              · intro hvc; apply h5
                rwa [← voteContention_eq T n f hcorr hvoted_eq]
              · intro b' hb'; rcases h6 b' hb' with hecho | hcont
                · by_cases hbb : b' = b
                  · subst hbb; left; exact Nat.le_trans hecho hecho_mono
                  · left; rw [hecho_other_eq b' hbb]; exact hecho
                · right; rwa [voteContention_eq T n f hcorr hvoted_eq]
            · -- Not yet crossed: check if now crossed
              by_cases hcross : echoSupport T n s_r' b ≥ BCA_LTS.echoThreshold n f
              · -- Newly crossed: need ideal bind(b) step
                have hreach' := LTS.Reachable.step hreach hstep
                rcases hbv : s_i.bound_value with _ | w
                · -- bound_value = none: fire bind(b).
                  let s_i' := { s_i with bound_value := some b }
                  have hbind_step : (IdealBCA.ideal_bca T n f).step s_i (.bind b) s_i' := by
                    simp only [IdealBCA.ideal_bca, Order.add_one_le_iff, ne_eq, ge_iff_le, hbv,
                      and_true, true_and, s_i']
                    exact inputSupport_transfer T n f h1 h2
                      (approval_implies_inputSupport T n f hreach hn src b hcorr_src happroved)
                  refine ⟨s_i', InternalStar.single (by
                    simp [IdealBCA.ideal_labelling]) hbind_step, ?_⟩
                  refine ⟨h1.trans hcorr.symm, ?_, ?_, ?_, ?_, ?_⟩
                  · intro p; rw [h2, hinp_eq]
                  · intro p; rw [h3, hdec_eq]
                  · intro b' hb'; simp only [Option.some.injEq, s_i']; left
                    exact echoSupport_unique T n f hn s_r'
                      (corrupted_budget T n f hreach') (corrupted_nodup T n f hreach')
                      b b' hcross hb'
                  · intro hvc; simp [s_i']
                  · intro b' hb'; simp only [Option.some.injEq, s_i'] at hb'; subst hb'
                    left; exact hcross
                · -- bound_value = some w: show w = b via h6 + uniqueness.
                  by_cases hecho_w : echoSupport T n s_r w ≥ BCA_LTS.echoThreshold n f
                  · -- echoSupport(w) ≥ threshold in s_r. Show w = b.
                    have hecho_w' : echoSupport T n s_r' w ≥ BCA_LTS.echoThreshold n f :=
                      Nat.le_trans hecho_w (step_echoSupport_mono T n f hstep w)
                    have hwb := echoSupport_unique T n f hn s_r'
                      (corrupted_budget T n f hreach') (corrupted_nodup T n f hreach')
                      w b hecho_w' hcross
                    rw [hwb] at hbv
                    refine ⟨s_i, .refl, h1.trans hcorr.symm, ?_, ?_, ?_, ?_, ?_⟩
                    · intro p; rw [h2, hinp_eq]
                    · intro p; rw [h3, hdec_eq]
                    · intro b' hb'; left; rw [hbv]
                      exact congrArg some (echoSupport_unique T n f hn s_r'
                        (corrupted_budget T n f hreach') (corrupted_nodup T n f hreach')
                        b b' hcross hb')
                    · intro hvc; apply h5
                      rwa [← voteContention_eq T n f hcorr hvoted_eq]
                    · intro b' hb'; rcases h6 b' hb' with hecho | hcont
                      · left; exact Nat.le_trans hecho (step_echoSupport_mono T n f hstep b')
                      · right; rwa [voteContention_eq T n f hcorr hvoted_eq]
                  · -- contention in s_r (from h6 + not hecho_w). h5 gives bound_value ≠ none.
                    have hvc_pre : voteContention T n f s_r := (h6 w hbv).resolve_left hecho_w
                    have hvc_eq := voteContention_eq T n f hcorr hvoted_eq
                    refine ⟨s_i, .refl, h1.trans hcorr.symm, ?_, ?_, ?_, ?_, ?_⟩
                    · intro p; rw [h2, hinp_eq]
                    · intro p; rw [h3, hdec_eq]
                    · intro b' hb'; right; rwa [hvc_eq]
                    · intro hvc; apply h5; rwa [← hvc_eq]
                    · intro b' hb'; rcases h6 b' hb' with hecho | hcont
                      · left; exact Nat.le_trans hecho (step_echoSupport_mono T n f hstep b')
                      · right; rwa [hvc_eq]
              · -- Still not crossed: ideal stays put
                refine ⟨s_i, .refl, h1.trans hcorr.symm, ?_, ?_, ?_, ?_, ?_⟩
                · intro p; rw [h2, hinp_eq]
                · intro p; rw [h3, hdec_eq]
                · intro b' hb'; by_cases hbb : b' = b
                  · exact absurd (hbb ▸ hb') hcross
                  · rw [hecho_other_eq b' hbb] at hb'; rcases h4 b' hb' with hval | hvc_pre
                    · exact Or.inl hval
                    · exact Or.inr (step_voteContention_mono T n f hstep hvc_pre)
                · intro hvc; apply h5
                  rwa [← voteContention_eq T n f hcorr hvoted_eq]
                · intro b' hb'; rcases h6 b' hb' with hecho | hcont
                  · by_cases hbb : b' = b
                    · exact absurd (hbb ▸ hecho) hold
                    · left; rw [hecho_other_eq b' hbb]; exact hecho
                  · right; rwa [voteContention_eq T n f hcorr hvoted_eq]
      · -- send vote: voted may change, echoed unchanged
        have hecho_eq : ∀ b, echoSupport T n s_r' b = echoSupport T n s_r b :=
          echoSupport_eq_of_eq T n (BCA_LTS.send_corrupted hstep)
            (fun p => BCA_LTS.send_vote_echoed hstep p)
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hR
        haveI := decidableVoteContention T n f s_r' (LTS.Reachable.step hreach hstep) hn
            (corrupted_budget T n f (LTS.Reachable.step hreach hstep))
        haveI := decidableVoteContention T n f s_r hreach hn (corrupted_budget T n f hreach)
        by_cases hnew_vc : voteContention T n f s_r' ∧ ¬voteContention T n f s_r
        · -- New contention: fire a bind step.
          obtain ⟨hvc, hold_vc⟩ := hnew_vc
          have hfvc := findVoteContention_complete T n f (LTS.Reachable.step hreach hstep) hn
            (corrupted_budget T n f (LTS.Reachable.step hreach hstep)) hvc
          let wit := (findVoteContention T n f s_r').get hfvc
          let cb₁ := wit.val.1; let cb₂ := wit.val.2
          have hcne : cb₁ ≠ cb₂ := wit.property.1
          -- wit.property uses s_r'.corrupted which = s_r.corrupted (send doesn't corrupt)
          have hcorr_eq := BCA_LTS.send_corrupted hstep
          have hcf1 : s_r.corrupted.length + ((List.finRange n).filter (fun p =>
              decide (p ∉ s_r.corrupted) &&
              ((s_r'.local_ p).voted none ||
              (s_r'.local_ p).voted (some cb₂)))).length ≥ n - f := by
            have := wit.property.2.1; simp only [hcorr_eq] at this; exact this
          have hcf2 : s_r.corrupted.length + ((List.finRange n).filter (fun p =>
              decide (p ∉ s_r.corrupted) &&
              ((s_r'.local_ p).voted none ||
              (s_r'.local_ p).voted (some cb₁)))).length ≥ n - f := by
            have := wit.property.2.2; simp only [hcorr_eq] at this; exact this
          have hbudget := corrupted_budget T n f hreach
          have hreach' := LTS.Reachable.step hreach hstep
          let filt := (List.finRange n).filter (fun p =>
              decide (p ∉ s_r.corrupted) &&
              ((s_r'.local_ p).voted none || (s_r'.local_ p).voted (some cb₂)))
          have hfilt_pos : filt.length > 0 := by
            have : s_r.corrupted.length + filt.length ≥ n - f := hcf1
            omega
          let voter := findVoter n filt hfilt_pos
          have hvm : voter ∈ filt := findVoter_mem n filt hfilt_pos
          rw [List.mem_filter] at hvm; simp only [List.mem_finRange, decide_not, Bool.and_eq_true,
            Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Bool.or_eq_true,
            true_and] at hvm
          have hvoter_not_corr : voter ∉ s_r.corrupted := by exact hvm.1
          have hvoter_voted_or : (s_r'.local_ voter).voted none = true ∨
              (s_r'.local_ voter).voted (some cb₂) = true := by exact hvm.2
          have hvoter_corr' : BCA_LTS.isCorrect T n s_r' voter :=
            show voter ∉ s_r'.corrupted by
              rw [BCA_LTS.send_corrupted hstep]; exact hvoter_not_corr
          by_cases hvnone : (s_r'.local_ voter).voted none = true
          · -- Voter voted ⊥: use voted_none_implies_two_approved.
            have happr2_ex :=
              voted_none_implies_two_approved T n f hreach' voter hvoter_corr' hvnone
            have hfta := findTwoApproved_complete T n f hreach' hn voter hvoter_corr' happr2_ex
            let ⟨⟨v₁, v₂⟩, hne, ha1_s', ha2_s'⟩ :=
              (findTwoApproved T n s_r' voter).get (by rw [hfta])
            have ha1_pre : (s_r.local_ voter).approved v₁ = true := by
              rwa [← BCA_LTS.step_approved_eq hstep voter v₁ (by intro s d m; simp)]
            have hais :=
              approval_implies_inputSupport T n f hreach hn voter v₁ hvoter_not_corr ha1_pre
            by_cases hbound : s_i.bound_value = none
            · -- Fire bind(v₁)
              let s_i' := { s_i with bound_value := some v₁ }
              have hbind_step : (IdealBCA.ideal_bca T n f).step s_i (.bind v₁) s_i' := by
                simp only [IdealBCA.ideal_bca, Order.add_one_le_iff, ne_eq, ge_iff_le, hbound,
                  and_true, true_and, s_i']
                exact inputSupport_transfer T n f h1 h2 hais
              refine ⟨s_i', InternalStar.single (by simp [IdealBCA.ideal_labelling]) hbind_step, ?_⟩
              refine ⟨h1.trans (BCA_LTS.send_corrupted hstep).symm, ?_, ?_, ?_, ?_, ?_⟩
              · intro p; simp [s_i', h2, BCA_LTS.send_input hstep]
              · intro p; simp [s_i', h3, BCA_LTS.send_decided hstep]
              · intro b hb; rw [hecho_eq] at hb
                rcases h4 b hb with hval | hvc_pre
                · exact absurd hval (by rw [hbound]; simp)
                · exact absurd hvc_pre hold_vc
              · intro _; simp [s_i']
              · intro b hb; simp only [Option.some.injEq, s_i'] at hb; subst hb
                right; show voteContention T n f s_r'
                unfold voteContention; rw [BCA_LTS.send_corrupted hstep]
                exact ⟨cb₁, cb₂, hcne, hcf1, hcf2⟩
            · exact sim_rel_preserved_echo_eq T n f ⟨h1, h2, h3, h4, h5, h6⟩ hstep
                (BCA_LTS.send_corrupted hstep) hecho_eq
                (BCA_LTS.send_input hstep) (BCA_LTS.send_decided hstep)
                (fun _ => hbound)
          · -- Voter voted (some cb₂): echoSupport(cb₂) ≥ threshold → bound already set.
            have hvbin : (s_r'.local_ voter).voted (some cb₂) = true := by
              rcases hvoter_voted_or with h | h
              · exact absurd h hvnone
              · exact h
            have hecho_cb₂ :=
              voted_some_implies_echoSupport T n f hreach' voter cb₂ hvoter_corr' hvbin
            rw [hecho_eq] at hecho_cb₂
            by_cases hbval : s_i.bound_value = some cb₂
            · exact sim_rel_preserved_echo_eq T n f ⟨h1, h2, h3, h4, h5, h6⟩ hstep
                (BCA_LTS.send_corrupted hstep) hecho_eq
                (BCA_LTS.send_input hstep) (BCA_LTS.send_decided hstep)
                (fun _ => by rw [hbval]; simp)
            · exfalso
              rcases h4 cb₂ hecho_cb₂ with hbval' | hvc_old
              · exact hbval hbval'
              · exact hold_vc hvc_old
        · exact sim_rel_preserved_echo_eq T n f ⟨h1, h2, h3, h4, h5, h6⟩ hstep
            (BCA_LTS.send_corrupted hstep) hecho_eq
            (BCA_LTS.send_input hstep) (BCA_LTS.send_decided hstep)
            (fun hvc => h5 (Decidable.byContradiction fun hno => hnew_vc ⟨hvc, hno⟩))
    · -- recv: echoed, voted unchanged for all recv types
      rcases t with _ | _ | _
      · -- recv init
        exact sim_rel_preserved_trivial T n f hR
          (BCA_LTS.recv_corrupted hstep)
          (BCA_LTS.recv_init_echoed hstep)
          (fun p w => BCA_LTS.recv_init_voted hstep p w)
          (BCA_LTS.recv_init_input hstep)
          (BCA_LTS.recv_init_decided hstep)
      · -- recv echo
        exact sim_rel_preserved_trivial T n f hR
          (BCA_LTS.recv_corrupted hstep)
          (BCA_LTS.recv_echo_echoed hstep)
          (fun p w => BCA_LTS.recv_echo_voted hstep p w)
          (BCA_LTS.recv_echo_input hstep)
          (BCA_LTS.recv_echo_decided hstep)
      · -- recv vote
        exact sim_rel_preserved_trivial T n f hR
          (BCA_LTS.recv_corrupted hstep)
          (BCA_LTS.recv_vote_echoed hstep)
          (fun p w => BCA_LTS.recv_vote_voted hstep p w)
          (BCA_LTS.recv_vote_input hstep)
          (BCA_LTS.recv_vote_decided hstep)
    · -- output: not internal
      exact absurd hint (by simp)
    · -- input: not internal
      exact absurd hint (by simp)

private def bca_step_external [Inhabited T] [Inhabited (Fin n)] (hn : n > 3 * f) :
    ∀ s₁ l₁ s₁' s₂, LTS.Reachable (BCA_LTS.bca T n f) s₁ → sim_rel T n f s₁ s₂ →
      (BCA_LTS.bca_labelling T n).is_external l₁ = true →
      (BCA_LTS.bca T n f).step s₁ l₁ s₁' →
      Σ' (s₂_mid : IdealBCA.State T n) (s₂_mid' : IdealBCA.State T n) (s₂' : IdealBCA.State T n),
        LTS.InternalStar (IdealBCA.ideal_bca T n f) (IdealBCA.ideal_labelling T n) s₂ s₂_mid ×'
        (IdealBCA.ideal_bca T n f).step s₂_mid (label_map T n l₁) s₂_mid' ×'
        LTS.InternalStar (IdealBCA.ideal_bca T n f) (IdealBCA.ideal_labelling T n) s₂_mid' s₂' ×'
        sim_rel T n f s₁' s₂' := by
    intro s_r l s_r' s_i hreach hR hext hstep
    simp only [Labelling.is_external, BCA_LTS.bca_labelling, Bool.not_eq_eq_eq_not,
      Bool.not_true] at hext
    rcases l with ⟨i⟩ | _ | _ | ⟨i, mv⟩ | ⟨i, v⟩
    · -- corrupt i: corrupted grows, local_ unchanged
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hR
      have hcl := BCA_LTS.corrupt_local hstep
      have hci := BCA_LTS.corrupt_isCorrect hstep
      have hcb := BCA_LTS.corrupt_budget hstep
      have hecho_mono : ∀ b, echoSupport T n s_r b ≤ echoSupport T n s_r' b :=
        fun b => step_echoSupport_mono T n f hstep b
      have hbudget_dec : s_r'.corrupted.length ≤ f := by
        rw [BCA_LTS.corrupt_eq hstep]; simp only [List.length_cons, Order.add_one_le_iff]
        exact Nat.lt_of_lt_of_le hcb (Nat.le_refl _)
      haveI : Decidable (∃ b', echoSupport T n s_r' b' ≥ BCA_LTS.echoThreshold n f ∧
          ¬echoSupport T n s_r b' ≥ BCA_LTS.echoThreshold n f) :=
        match hfnc : findNewEchoCrossing T n f s_r s_r' with
        | some ⟨b', hge, hlt⟩ => isTrue ⟨b', hge, hlt⟩
        | none => isFalse (fun hex => by
            have := findNewEchoCrossing_complete T n hn hbudget_dec hcl hex
            simp [hfnc] at this)
      by_cases hnew_cross : ∃ b', echoSupport T n s_r' b' ≥ BCA_LTS.echoThreshold n f ∧
          ¬echoSupport T n s_r b' ≥ BCA_LTS.echoThreshold n f
      · -- Some value b' newly crossed. Need a bind step before corrupt.
        have hfnc := findNewEchoCrossing_complete T n hn hbudget_dec hcl hnew_cross
        let witness := (findNewEchoCrossing T n f s_r s_r').get hfnc
        let b' := witness.val
        have hcross : echoSupport T n s_r' b' ≥ BCA_LTS.echoThreshold n f := witness.property.1
        have hold : ¬echoSupport T n s_r b' ≥ BCA_LTS.echoThreshold n f := witness.property.2
        have hreach' := LTS.Reachable.step hreach hstep
        have hbudget' := corrupted_budget T n f hreach'
        unfold echoSupport at hcross
        let filt := (List.finRange n).filter (fun p =>
            decide (p ∉ s_r.corrupted) && decide ((s_r.local_ p).echoed = some b'))
        have hfilt_pos : filt.length > 0 := by
          have hfilt_s' : ((List.finRange n).filter (fun p => decide (p ∉ s_r'.corrupted)
              && decide ((s_r'.local_ p).echoed = some b'))).length > 0 := by
            unfold BCA_LTS.echoThreshold at hcross; omega
          apply Nat.lt_of_lt_of_le hfilt_s'
          apply filter_length_mono; intro p hp; simp only [decide_not, Bool.and_eq_true,
            Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
            decide_eq_true_eq] at hp ⊢
          exact ⟨BCA_LTS.step_correct_prev hstep p hp.1, by rw [← hcl]; exact hp.2⟩
        let voter := findVoter n filt hfilt_pos
        have hvm : voter ∈ filt := findVoter_mem n filt hfilt_pos
        rw [List.mem_filter] at hvm; simp only [List.mem_finRange, decide_not, Bool.and_eq_true,
          Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, decide_eq_true_eq,
          true_and] at hvm
        have hvoter_corr : BCA_LTS.isCorrect T n s_r voter := by exact hvm.1
        have hvoter_echoed : (s_r.local_ voter).echoed = some b' := by exact hvm.2
        have happr := echoed_implies_approved T n f hreach voter b' hvoter_corr hvoter_echoed
        have hais := approval_implies_inputSupport T n f hreach hn voter b' hvoter_corr happr
        rcases hbv : s_i.bound_value with _ | w
        · -- bound_value = none: fire bind(b') then corrupt(i).
          let s_bind := { s_i with bound_value := some b' }
          let s_final := { s_bind with corrupted := i :: s_bind.corrupted }
          have hbind_step : (IdealBCA.ideal_bca T n f).step s_i (.bind b') s_bind := by
            simp only [IdealBCA.ideal_bca, Order.add_one_le_iff, ne_eq, ge_iff_le, hbv, and_true,
              true_and, s_bind]
            rw [h1]; unfold IdealBCA.inputSupport
            apply Nat.le_trans hais; apply Nat.add_le_add_left
            apply filter_length_mono; intro q hq
            simp only [decide_not, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
              decide_eq_false_iff_not, decide_eq_true_eq, h1] at hq ⊢; rw [h2]; exact hq
          have hcorrupt_step : (IdealBCA.ideal_bca T n f).step s_bind
              (.corrupt i) s_final := by
            simp only [IdealBCA.ideal_bca, IdealBCA.isCorrect, Order.add_one_le_iff, ne_eq,
              ge_iff_le, h1, and_true, s_bind, s_final]
            exact ⟨hci, hcb⟩
          refine ⟨s_bind, s_final, s_final,
            InternalStar.single (by simp [IdealBCA.ideal_labelling]) hbind_step,
            hcorrupt_step, .refl, ?_⟩
          refine ⟨by rw [BCA_LTS.corrupt_eq hstep]; simp [s_final, s_bind, h1], ?_, ?_, ?_, ?_, ?_⟩
          · intro p; simp [s_final, s_bind, h2, hcl]
          · intro p; rw [h3]; simp [hcl]
          · intro b'' hb''; left
            exact congrArg some (echoSupport_unique T n f hn s_r'
              (corrupted_budget T n f hreach') (corrupted_nodup T n f hreach')
              b' b'' hcross hb'')
          · intro hvc; simp [s_final, s_bind]
          · intro b'' hb''; simp only [Option.some.injEq, s_bind, s_final] at hb''; subst hb''
            left; exact hcross
        · -- bound_value = some w: contention holds, use it for sim_rel.
          by_cases hecho_w : echoSupport T n s_r w ≥ BCA_LTS.echoThreshold n f
          · -- echoSupport(w) ≥ threshold → w = b' by uniqueness
            have hecho_w' := Nat.le_trans hecho_w (hecho_mono w)
            have hwb := echoSupport_unique T n f hn s_r'
              (corrupted_budget T n f hreach') (corrupted_nodup T n f hreach')
              w b' hecho_w' hcross
            rw [hwb] at hbv
            let s_final := { s_i with corrupted := i :: s_i.corrupted }
            refine ⟨s_i, s_final, s_final, .refl, ?_, .refl, ?_⟩
            · simp only [IdealBCA.ideal_bca, IdealBCA.isCorrect, Order.add_one_le_iff, ne_eq,
              ge_iff_le, label_map, h1, and_true, s_final]
              exact ⟨hci, hcb⟩
            · refine ⟨by rw [BCA_LTS.corrupt_eq hstep]; simp [s_final, h1], ?_, ?_, ?_, ?_, ?_⟩
              · intro p; simp [s_final, h2, hcl]
              · intro p; rw [h3]; simp [hcl]
              · intro b'' hb''; left; rw [hbv]
                exact congrArg some (echoSupport_unique T n f hn s_r'
                  (corrupted_budget T n f hreach') (corrupted_nodup T n f hreach')
                  b' b'' hcross hb'')
              · intro hvc; change s_i.bound_value ≠ none; rw [hbv]; simp
              · intro b'' hb''; show _ ∨ _; rcases h6 b'' hb'' with he | hc
                · left; exact Nat.le_trans he (hecho_mono b'')
                · right; exact step_voteContention_mono T n f hstep hc
          · -- contention: use it for sim_rel
            have hvc_pre : voteContention T n f s_r := (h6 w hbv).resolve_left hecho_w
            let s_final := { s_i with corrupted := i :: s_i.corrupted }
            refine ⟨s_i, s_final, s_final, .refl, ?_, .refl, ?_⟩
            · simp only [IdealBCA.ideal_bca, IdealBCA.isCorrect, Order.add_one_le_iff, ne_eq,
              ge_iff_le, label_map, h1, and_true, s_final]
              exact ⟨hci, hcb⟩
            · refine ⟨by rw [BCA_LTS.corrupt_eq hstep]; simp [s_final, h1], ?_, ?_, ?_, ?_, ?_⟩
              · intro p; simp [s_final, h2, hcl]
              · intro p; rw [h3]; simp [hcl]
              · intro b'' hb''; right; exact step_voteContention_mono T n f hstep hvc_pre
              · intro hvc; change s_i.bound_value ≠ none; exact h5 hvc_pre
              · intro b'' hb''; rcases h6 b'' hb'' with he | hc
                · left; exact Nat.le_trans he (hecho_mono b'')
                · right; exact step_voteContention_mono T n f hstep hc
      · -- No new crossing. Check for new contention.
        simp only [not_exists, not_and] at hnew_cross
        haveI := decidableVoteContention T n f s_r' (LTS.Reachable.step hreach hstep) hn
            (corrupted_budget T n f (LTS.Reachable.step hreach hstep))
        haveI := decidableVoteContention T n f s_r hreach hn (corrupted_budget T n f hreach)
        by_cases hnew_vc : voteContention T n f s_r' ∧ ¬voteContention T n f s_r
        · -- New contention in s_r': need bind step before corrupt.
          obtain ⟨hvc, hold_vc⟩ := hnew_vc
          have hfvc := findVoteContention_complete T n f (LTS.Reachable.step hreach hstep) hn
            (corrupted_budget T n f (LTS.Reachable.step hreach hstep)) hvc
          let wit := (findVoteContention T n f s_r').get hfvc
          let cb₁ := wit.val.1; let cb₂ := wit.val.2
          have hcne : cb₁ ≠ cb₂ := wit.property.1
          have hcorr_eq : s_r'.corrupted = i :: s_r.corrupted := by rw [BCA_LTS.corrupt_eq hstep]
          have hcf1 : (i :: s_r.corrupted).length + ((List.finRange n).filter (fun p =>
              decide (p ∉ (i :: s_r.corrupted)) &&
              ((s_r'.local_ p).voted none ||
              (s_r'.local_ p).voted (some cb₂)))).length ≥ n - f := by
            have := wit.property.2.1; simp only [hcorr_eq] at this; exact this
          have hcf2 : (i :: s_r.corrupted).length + ((List.finRange n).filter (fun p =>
              decide (p ∉ (i :: s_r.corrupted)) &&
              ((s_r'.local_ p).voted none ||
              (s_r'.local_ p).voted (some cb₁)))).length ≥ n - f := by
            have := wit.property.2.2; simp only [hcorr_eq] at this; exact this
          have hbudget := corrupted_budget T n f hreach
          have hreach' := LTS.Reachable.step hreach hstep
          have hbudget' := corrupted_budget T n f hreach'
          let filt := (List.finRange n).filter (fun p =>
              decide (p ∉ (i :: s_r.corrupted)) &&
              ((s_r'.local_ p).voted none || (s_r'.local_ p).voted (some cb₂)))
          have hfilt_pos : filt.length > 0 := by
            have : (i :: s_r.corrupted).length + filt.length ≥ n - f := hcf1
            have : (i :: s_r.corrupted).length ≤ f := by
              rw [← show s_r'.corrupted = i :: s_r.corrupted from by rw [BCA_LTS.corrupt_eq hstep]]
              exact hbudget'
            omega
          let voter := findVoter n filt hfilt_pos
          have hvm : voter ∈ filt := findVoter_mem n filt hfilt_pos
          rw [List.mem_filter] at hvm; simp only [List.mem_finRange, List.mem_cons, not_or,
            Bool.decide_and, decide_not, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
            decide_eq_false_iff_not, Bool.or_eq_true, true_and] at hvm
          have hvoter_not_i : voter ≠ i := by exact fun h => hvm.1.1 h
          have hvoter_not_corrupted : voter ∉ s_r.corrupted := by exact hvm.1.2
          have hvoter_voted_or : (s_r'.local_ voter).voted none = true ∨
              (s_r'.local_ voter).voted (some cb₂) = true := by exact hvm.2
          have hvoter_corr' : BCA_LTS.isCorrect T n s_r' voter := by
            change voter ∉ s_r'.corrupted; rw [BCA_LTS.corrupt_eq hstep]
            simp only [List.mem_cons, not_or]; exact ⟨hvoter_not_i, hvoter_not_corrupted⟩
          have hvoter_corr : BCA_LTS.isCorrect T n s_r voter :=
            BCA_LTS.step_correct_prev hstep voter hvoter_corr'
          by_cases hvnone : (s_r'.local_ voter).voted none = true
          · -- Voter voted ⊥: use voted_none_implies_two_approved.
            have happr3_ex :=
              voted_none_implies_two_approved T n f hreach' voter hvoter_corr' hvnone
            have hfta := findTwoApproved_complete T n f hreach' hn voter hvoter_corr' happr3_ex
            let ⟨⟨v₁, v₂⟩, hne_v, ha1_s', ha2_s'⟩ :=
              (findTwoApproved T n s_r' voter).get (by rw [hfta])
            have ha1_pre : (s_r.local_ voter).approved v₁ = true := by
              rwa [← hcl]
            have hais := approval_implies_inputSupport T n f hreach hn voter v₁ hvoter_corr ha1_pre
            by_cases hbound : s_i.bound_value = none
            · let s_bind := { s_i with bound_value := some v₁ }
              let s_final := { s_bind with corrupted := i :: s_bind.corrupted }
              have hbind_step : (IdealBCA.ideal_bca T n f).step s_i (.bind v₁) s_bind := by
                simp only [IdealBCA.ideal_bca, Order.add_one_le_iff, ne_eq, ge_iff_le, hbound,
                  and_true, true_and, s_bind]
                exact inputSupport_transfer T n f h1 h2 hais
              have hcorrupt_step : (IdealBCA.ideal_bca T n f).step s_bind
                  (.corrupt i) s_final := by
                simp only [IdealBCA.ideal_bca, IdealBCA.isCorrect, Order.add_one_le_iff, ne_eq,
                  ge_iff_le, h1, and_true, s_bind, s_final]
                exact ⟨hci, hcb⟩
              refine ⟨s_bind, s_final, s_final,
                InternalStar.single (by simp [IdealBCA.ideal_labelling]) hbind_step,
                hcorrupt_step, .refl, ?_⟩
              refine ⟨by
                rw [BCA_LTS.corrupt_eq hstep]; simp [s_final, s_bind, h1], ?_, ?_, ?_, ?_, ?_⟩
              · intro p; simp [s_final, s_bind, h2, hcl]
              · intro p; rw [h3]; simp [hcl]
              · intro b' hb'
                have hold_echo := Nat.le_of_not_lt (fun h =>
                    hnew_cross b' hb' (Nat.not_le.mpr h))
                rcases h4 b' hold_echo with hval | hvc_pre
                · exact absurd hval (by rw [hbound]; simp)
                · exact absurd hvc_pre hold_vc
              · intro _; simp [s_final, s_bind]
              · intro b' hb'; simp only [Option.some.injEq, s_final, s_bind] at hb'; subst hb'
                right; show voteContention T n f s_r'
                unfold voteContention
                rw [show s_r'.corrupted = i :: s_r.corrupted from by rw [BCA_LTS.corrupt_eq hstep]]
                exact ⟨cb₁, cb₂, hcne, hcf1, hcf2⟩
            · -- bound_value already set: fire corrupt directly.
              refine ⟨s_i, { s_i with corrupted := i :: s_i.corrupted },
                      { s_i with corrupted := i :: s_i.corrupted },
                      .refl, ?_, .refl, ?_⟩
              · simp only [IdealBCA.ideal_bca, IdealBCA.isCorrect, Order.add_one_le_iff, ne_eq,
                ge_iff_le, label_map, h1, and_true]
                exact ⟨hci, hcb⟩
              · refine ⟨by rw [BCA_LTS.corrupt_eq hstep]; simp [h1], ?_, ?_, ?_, ?_, ?_⟩
                · intro p; simp [h2, hcl]
                · intro p; rw [h3]; simp [hcl]
                · intro b' hb'
                  rcases h4 b' (Nat.le_of_not_lt (fun h =>
                    hnew_cross b' hb' (Nat.not_le.mpr h))) with hval | hvc_pre
                  · exact Or.inl hval
                  · exact Or.inr (step_voteContention_mono T n f hstep hvc_pre)
                · intro _; exact hbound
                · intro b' hb'; show _ ∨ _
                  rcases h6 b' hb' with hecho | hcont
                  · left; exact Nat.le_trans hecho (hecho_mono b')
                  · right; exact step_voteContention_mono T n f hstep hcont
          · -- Voter voted (some cb₂): echoSupport(cb₂) ≥ threshold → bound already set.
            have hvbin : (s_r'.local_ voter).voted (some cb₂) = true := by
              rcases hvoter_voted_or with h | h
              · exact absurd h hvnone
              · exact h
            have hvbin_pre : (s_r.local_ voter).voted (some cb₂) = true := by rwa [← hcl]
            have hecho_cb₂ :=
              voted_some_implies_echoSupport T n f hreach voter cb₂ hvoter_corr hvbin_pre
            have hbval : s_i.bound_value = some cb₂ := by
              rcases h4 cb₂ hecho_cb₂ with hbval | hvc_old
              · exact hbval
              · exact absurd hvc_old hold_vc
            -- bound = some cb₂: fire corrupt directly.
            refine ⟨s_i, { s_i with corrupted := i :: s_i.corrupted },
                    { s_i with corrupted := i :: s_i.corrupted },
                    .refl, ?_, .refl, ?_⟩
            · simp only [IdealBCA.ideal_bca, IdealBCA.isCorrect, Order.add_one_le_iff, ne_eq,
              ge_iff_le, label_map, h1, and_true]
              exact ⟨hci, hcb⟩
            · refine ⟨by rw [BCA_LTS.corrupt_eq hstep]; simp [h1], ?_, ?_, ?_, ?_, ?_⟩
              · intro p; simp [h2, hcl]
              · intro p; rw [h3]; simp [hcl]
              · intro b' hb'
                rcases h4 b' (Nat.le_of_not_lt (fun h =>
                    hnew_cross b' hb' (Nat.not_le.mpr h))) with hval | hvc_pre
                · exact Or.inl hval
                · exact Or.inr (step_voteContention_mono T n f hstep hvc_pre)
              · intro _; rw [hbval]; simp
              · intro b' hb'; show _ ∨ _
                rcases h6 b' hb' with hecho | hcont
                · left; exact Nat.le_trans hecho (hecho_mono b')
                · right; exact step_voteContention_mono T n f hstep hcont
        · -- No new contention either.
          have hvc_impl : voteContention T n f s_r' → voteContention T n f s_r :=
            fun hvc' => Decidable.byContradiction fun hno => hnew_vc ⟨hvc', hno⟩
          refine ⟨s_i, { s_i with corrupted := i :: s_i.corrupted },
                  { s_i with corrupted := i :: s_i.corrupted },
                  .refl, ?_, .refl, ?_⟩
          · simp only [IdealBCA.ideal_bca, IdealBCA.isCorrect, Order.add_one_le_iff, ne_eq,
            ge_iff_le, label_map, h1, and_true]
            exact ⟨hci, hcb⟩
          · refine ⟨by rw [BCA_LTS.corrupt_eq hstep]; simp [h1], ?_, ?_, ?_, ?_, ?_⟩
            · intro p; simp [h2, hcl]
            · intro p; rw [h3]; simp [hcl]
            · intro b' hb'
              rcases h4 b' (Nat.le_of_not_lt (fun h =>
                    hnew_cross b' hb' (Nat.not_le.mpr h))) with hval | hvc_pre
              · exact Or.inl hval
              · exact Or.inr (step_voteContention_mono T n f hstep hvc_pre)
            · intro hvc; exact h5 (hvc_impl hvc)
            · intro b' hb'; show _ ∨ _
              rcases h6 b' hb' with hecho | hcont
              · left; exact Nat.le_trans hecho (hecho_mono b')
              · right; exact step_voteContention_mono T n f hstep hcont
    · -- send: not external
      exact absurd hext (by simp)
    · -- recv: not external
      exact absurd hext (by simp)
    · -- output i mv
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hR
      have hcorr := BCA_LTS.output_corrupted hstep
      have hci := BCA_LTS.output_isCorrect hstep
      have hdec_none := BCA_LTS.output_decided_none hstep
      have hecho_eq : ∀ b, echoSupport T n s_r' b = echoSupport T n s_r b :=
        echoSupport_eq_of_eq T n hcorr (BCA_LTS.output_echoed hstep)
      rcases mv with _ | b
      · -- output none (⊥)
        have happr := hstep.2.2.1.1
        have hfta := findTwoApproved_complete T n f hreach hn i hci happr
        let ⟨⟨v₁, v₂⟩, hne_v, ha1, ha2⟩ :=
          (findTwoApproved T n s_r i).get (by rw [hfta])
        have hais1 := approval_implies_inputSupport T n f hreach hn i v₁ hci ha1
        have hais2 := approval_implies_inputSupport T n f hreach hn i v₂ hci ha2
        have hvc_eq : voteContention T n f s_r' = voteContention T n f s_r :=
          voteContention_eq T n f hcorr (BCA_LTS.output_voted hstep)
        by_cases hbound : s_i.bound_value = none
        · -- Case 1: bound_value = none — fire bind(v₁) then output ⊥
          let s_bind := { s_i with bound_value := some v₁ }
          let s_out := { s_bind with decided :=
            fun p => if p = i then some none else s_bind.decided p }
          have hbind_step : (IdealBCA.ideal_bca T n f).step s_i (.bind v₁) s_bind := by
            simp only [IdealBCA.ideal_bca, Order.add_one_le_iff, ne_eq, ge_iff_le, hbound, and_true,
              true_and, s_bind]
            exact BCA_Simulation.inputSupport_transfer T n f h1 h2 hais1
          have hout_step : (IdealBCA.ideal_bca T n f).step s_bind
              (label_map T n (BCA_LTS.Label.output i none)) s_out := by
            simp only [IdealBCA.ideal_bca, Order.add_one_le_iff, ne_eq, ge_iff_le, label_map,
              Option.some.injEq, ↓existsAndEq, true_and, and_true, s_bind, s_out]
            refine ⟨?_, ?_, v₂, hne_v, ?_⟩
            · simp only [BCA_LTS.isCorrect, IdealBCA.isCorrect, h1] at hci ⊢; exact hci
            · rw [h3]; exact hdec_none
            · exact BCA_Simulation.inputSupport_transfer T n f
                (by simp [h1]) (by intro p; simp [h2]) hais2
          refine ⟨s_bind, s_out, s_out,
            InternalStar.single (by simp [IdealBCA.ideal_labelling]) hbind_step,
            hout_step, .refl, ?_⟩
          refine ⟨by simp only [s_bind, s_out]; rw [h1, hcorr], ?_, ?_, ?_, ?_, ?_⟩
          · intro p; simp only [s_out, s_bind]; rw [h2, BCA_LTS.output_input hstep]
          · intro p; simp only [s_out, s_bind]; by_cases hp : p = i
            · subst hp; simp [BCA_LTS.output_decided_self hstep]
            · simp [hp, h3, BCA_LTS.output_decided_other hstep p hp]
          · intro b hb; rw [hecho_eq] at hb; simp only [s_out, s_bind]
            rcases h4 b hb with hval | hvc_pre
            · exact absurd hval (by rw [hbound]; simp)
            · right; rw [hvc_eq]; exact hvc_pre
          · intro hvc; simp only [ne_eq, reduceCtorEq, not_false_eq_true, s_bind, s_out]
          · intro b hb; simp only [Option.some.injEq, s_bind, s_out] at hb; subst hb
            right; rw [hvc_eq]
            have hno_bin : ∀ p b', BCA_LTS.isCorrect T n s_r p →
                (s_r.local_ p).voted (some b') = true → False := by
              intro p b' hcorr_p hvoted_p
              have hes := voted_some_implies_echoSupport T n f hreach p b' hcorr_p hvoted_p
              rcases h4 b' hes with hval | hvc_pre
              · exact absurd hval (by rw [hbound]; simp)
              · exact absurd (h5 hvc_pre) (by rw [hbound]; simp)
            obtain ⟨vals, hvq⟩ := hstep.2.2.1.2
            unfold BCA_LTS.countAnyVoteRecv BCA_LTS.returnThreshold at hvq
            have hbudget := corrupted_budget T n f hreach
            have hsrc_bot : ∀ q, q ∉ s_r.corrupted →
                vals.any (fun v => (s_r.local_ i).voteRecv q v) = true →
                (s_r.local_ q).voted none = true := by
              intro q hcq hrecv
              obtain ⟨v, _, hvr⟩ := List.any_eq_true.mp hrecv
              match v with
              | none => exact vote_trace_none T n f hreach i q hcq hvr
              | some b' =>
                exact False.elim (hno_bin q b' hcq (vote_trace T n f hreach i q b' hcq hvr))
            have hcorr_src_ge : ((List.finRange n).filter (fun q =>
                decide (q ∉ s_r.corrupted) &&
                vals.any (fun v =>
                  (s_r.local_ i).voteRecv q v))).length ≥ n - f - s_r.corrupted.length := by
              have hsplit := filter_split
                (fun q : Fin n => vals.any (fun v => (s_r.local_ i).voteRecv q v))
                (fun q : Fin n => decide (q ∉ s_r.corrupted))
                (List.finRange n)
              have hcorr_bound : ((List.finRange n).filter (fun q =>
                  vals.any (fun v => (s_r.local_ i).voteRecv q v) &&
                  !decide (q ∉ s_r.corrupted))).length ≤ s_r.corrupted.length := by
                apply Nat.le_trans (filter_and_le _ _ _)
                simp [Bool.not_not, decide_not]
                exact Nat.le_trans (nodup_sub_length
                  ((finRange_nodup n).sublist List.filter_sublist)
                  (fun x hx => by simp only [List.mem_filter, List.mem_finRange, decide_eq_true_eq,
                    true_and] at hx; exact hx)) (Nat.le_refl _)
              have hcomm : ((List.finRange n).filter (fun q =>
                  vals.any (fun v => (s_r.local_ i).voteRecv q v) &&
                  decide (q ∉ s_r.corrupted))).length =
                ((List.finRange n).filter (fun q =>
                  decide (q ∉ s_r.corrupted) &&
                  vals.any (fun v => (s_r.local_ i).voteRecv q v))).length := by
                apply congrArg List.length; apply List.filter_congr
                intro q _; simp [Bool.and_comm]
              omega
            have hbot_ge : ((List.finRange n).filter (fun p =>
                decide (p ∉ s_r.corrupted) &&
                decide ((s_r.local_ p).voted none = true))).length
                ≥ n - f - s_r.corrupted.length := by
              apply Nat.le_trans hcorr_src_ge
              apply filter_length_mono; intro q hq
              simp only [decide_not, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
                decide_eq_false_iff_not, List.any_eq_true, Bool.decide_eq_true] at hq ⊢
              exact ⟨hq.1, hsrc_bot q hq.1 (List.any_eq_true.mpr hq.2)⟩
            have hbot_sub : ∀ bx, ((List.finRange n).filter (fun p =>
                decide (p ∉ s_r.corrupted) &&
                decide ((s_r.local_ p).voted none = true))).length ≤
              ((List.finRange n).filter (fun p =>
                decide (p ∉ s_r.corrupted) &&
                ((s_r.local_ p).voted none || (s_r.local_ p).voted (some bx)))).length := by
              intro bx; apply filter_length_mono; intro p hp
              simp only [decide_not, Bool.decide_eq_true, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
                Bool.not_true, decide_eq_false_iff_not, Bool.or_eq_true] at hp ⊢
              exact ⟨hp.1, Or.inl hp.2⟩
            exact ⟨v₁, v₂, hne_v,
              Nat.le_trans (by omega) (Nat.add_le_add_left (hbot_sub v₂) _),
              Nat.le_trans (by omega) (Nat.add_le_add_left (hbot_sub v₁) _)⟩
        · -- Case 2: bound_value = some w — output ⊥ directly
          let w := s_i.bound_value.get (Option.ne_none_iff_isSome.mp hbound)
          have hbv : s_i.bound_value = some w := by
            simp [w]
          have hb' : ∃ b', b' ≠ w ∧
              s_r.corrupted.length +
              ((List.finRange n).filter (fun q =>
                decide (q ∉ s_r.corrupted) && decide ((s_r.local_ q).input = some b'))).length ≥
              f + 1 := by
            by_cases h : v₁ = w
            · exact ⟨v₂, by rw [← h]; exact hne_v.symm, hais2⟩
            · exact ⟨v₁, h, hais1⟩
          have hb'_in_cands : ∃ b' ∈ inputCandidates T n s_r,
              b' ≠ w ∧ s_r.corrupted.length +
              ((List.finRange n).filter (fun q =>
                decide (q ∉ s_r.corrupted) && decide ((s_r.local_ q).input = some b'))).length ≥
              f + 1 := by
            obtain ⟨b', hne, hcount⟩ := hb'
            have hpos : ((List.finRange n).filter (fun q => decide (q ∉ s_r.corrupted)
              && decide ((s_r.local_ q).input = some b'))).length > 0 := by
              have := corrupted_budget T n f hreach; omega
            obtain ⟨q, hq⟩ := List.exists_mem_of_length_pos hpos
            simp only [decide_not, List.mem_filter, List.mem_finRange, Bool.and_eq_true,
              Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, decide_eq_true_eq,
              true_and] at hq
            exact ⟨b', List.mem_filterMap.mpr ⟨q, List.mem_finRange q, hq.2⟩, hne, hcount⟩
          let ⟨b', hne_b', hais_b'⟩ := findWitness (inputCandidates T n s_r)
            (fun b' => b' ≠ w ∧ s_r.corrupted.length +
              ((List.finRange n).filter (fun q =>
                decide (q ∉ s_r.corrupted) && decide ((s_r.local_ q).input = some b'))).length ≥
              f + 1) hb'_in_cands
          let s_out := { s_i with decided := fun p => if p = i then some none else s_i.decided p }
          have hout_step : (IdealBCA.ideal_bca T n f).step s_i
              (label_map T n (BCA_LTS.Label.output i none)) s_out := by
            simp only [IdealBCA.ideal_bca, Order.add_one_le_iff, ne_eq, ge_iff_le, label_map,
              and_true, s_out]
            refine ⟨?_, ?_, w, b', hne_b'.symm, hbv, ?_⟩
            · simp only [BCA_LTS.isCorrect, IdealBCA.isCorrect, h1] at hci ⊢; exact hci
            · rw [h3]; exact hdec_none
            · exact BCA_Simulation.inputSupport_transfer T n f h1 h2 hais_b'
          refine ⟨s_i, s_out, s_out, .refl, hout_step, .refl, ?_⟩
          refine ⟨by rw [h1, hcorr], ?_, ?_, ?_, ?_, ?_⟩
          · intro p; rw [h2, BCA_LTS.output_input hstep]
          · intro p; simp [s_out]; by_cases hp : p = i
            · subst hp; simp [BCA_LTS.output_decided_self hstep]
            · simp [hp, h3, BCA_LTS.output_decided_other hstep p hp]
          · intro b hb; rw [hecho_eq] at hb; simp only [s_out]
            rcases h4 b hb with hval | hvc_pre
            · exact Or.inl hval
            · right; rw [hvc_eq]; exact hvc_pre
          · intro hvc; simp only [s_out]; exact h5 (by rwa [← hvc_eq])
          · intro b hb; simp only [s_out] at hb; rcases h6 b hb with hecho | hcont
            · left; rw [hecho_eq]; exact hecho
            · right; rw [hvc_eq]; exact hcont
      · -- output some b: needs bound_value = some b
        have hgate := hstep
        obtain ⟨_, _, houtgate, rfl⟩ := hgate
        have hvote_quorum : BCA_LTS.countVoteRecv T n (s_r.local_ i) (some b) ≥
            BCA_LTS.returnThreshold n f := houtgate
        unfold BCA_LTS.countVoteRecv BCA_LTS.returnThreshold at hvote_quorum
        have hbudget := corrupted_budget T n f hreach
        have hfilt_pos : ((List.finRange n).filter (fun q =>
            decide (q ∉ s_r.corrupted) && (s_r.local_ i).voteRecv q (some b))).length > 0 := by
          have : ((List.finRange n).filter (fun q =>
              (s_r.local_ i).voteRecv q (some b))).length ≥ n - f := hvote_quorum
          have hsplit := filter_split
            (fun q : Fin n => (s_r.local_ i).voteRecv q (some b))
            (fun q : Fin n => decide (q ∉ s_r.corrupted))
            (List.finRange n)
          have hcorr_part := filter_and_le
            (fun q : Fin n => (s_r.local_ i).voteRecv q (some b))
            (fun q : Fin n => !decide (q ∉ s_r.corrupted))
            (List.finRange n)
          have hcorr_bound : ((List.finRange n).filter (fun q =>
              (s_r.local_ i).voteRecv q (some b) && !decide (q ∉ s_r.corrupted))).length ≤ f := by
            apply Nat.le_trans hcorr_part
            simp [Bool.not_not, decide_not]
            exact Nat.le_trans (nodup_sub_length ((finRange_nodup n).sublist List.filter_sublist)
              (fun x hx => by simp only [List.mem_filter, List.mem_finRange, decide_eq_true_eq,
                true_and] at hx; exact hx)) hbudget
          have hle : n - f ≤ ((List.finRange n).filter (fun q =>
              (s_r.local_ i).voteRecv q (some b) && decide (q ∉ s_r.corrupted))).length +
            ((List.finRange n).filter (fun q =>
              (s_r.local_ i).voteRecv q (some b) && !decide (q ∉ s_r.corrupted))).length :=
            hsplit ▸ this
          have hcorrect_pos : ((List.finRange n).filter (fun q =>
              (s_r.local_ i).voteRecv q (some b) && decide (q ∉ s_r.corrupted))).length > 0 := by
            omega
          apply Nat.lt_of_lt_of_le hcorrect_pos
          apply filter_length_mono; intro q hq
          simp only [decide_not, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
            decide_eq_false_iff_not] at hq ⊢; exact ⟨hq.2, hq.1⟩
        let filt := (List.finRange n).filter (fun q =>
            decide (q ∉ s_r.corrupted) && (s_r.local_ i).voteRecv q (some b))
        have hfilt_pos'' : filt.length > 0 := hfilt_pos
        let voter := findVoter n filt hfilt_pos''
        have hvm : voter ∈ filt := findVoter_mem n filt hfilt_pos''
        rw [List.mem_filter] at hvm; simp only [List.mem_finRange, decide_not, Bool.and_eq_true,
          Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, true_and] at hvm
        have hvoter_corr : BCA_LTS.isCorrect T n s_r voter := by exact hvm.1
        have hvoter_recv : (s_r.local_ i).voteRecv voter (some b) = true := by exact hvm.2
        have hvoted := vote_trace T n f hreach i voter b hvoter_corr hvoter_recv
        have hecho := voted_some_implies_echoSupport T n f hreach voter b hvoter_corr hvoted
        by_cases hbound : s_i.bound_value = some b
        · -- bound_value = some b: proceed with output step
          let s_i' := { s_i with decided :=
            fun p => if p = i then some (some b) else s_i.decided p }
          refine ⟨s_i, s_i', s_i', InternalStar.refl, ?_, InternalStar.refl, ?_⟩
          · -- ideal output step
            simp only [IdealBCA.ideal_bca, Order.add_one_le_iff, ne_eq, ge_iff_le, label_map, h1,
              hbound, and_self, and_true, s_i']
            exact ⟨by simp only [BCA_LTS.isCorrect, IdealBCA.isCorrect, h1] at hci ⊢; exact hci,
              by rw [h3]; exact hdec_none⟩
          · -- sim_rel preserved
            refine ⟨h1.trans hcorr.symm, ?_, ?_, ?_, ?_, ?_⟩
            · intro p; rw [h2, BCA_LTS.output_input hstep]
            · intro p; simp [s_i']; by_cases hp : p = i
              · subst hp; simp
              · simp [hp, h3, show (s_r'.local_ p).decided = (s_r.local_ p).decided from
                  BCA_LTS.output_decided_other hstep p hp]
            · intro b' hb'; rw [hecho_eq] at hb'; simp only [s_i']
              rcases h4 b' hb' with hval | hvc_pre
              · exact Or.inl hval
              · exact Or.inr (step_voteContention_mono T n f hstep hvc_pre)
            · intro hvc'; simp only [s_i']; apply h5
              rwa [← voteContention_eq T n f hcorr (BCA_LTS.output_voted hstep)]
            · intro b' hb'; simp only [s_i'] at hb'; rcases h6 b' hb' with hecho' | hcont
              · left; rw [hecho_eq]; exact hecho'
              · right; rwa [voteContention_eq T n f hcorr (BCA_LTS.output_voted hstep)]
        · -- contention + echoSupport(b) ≥ threshold.
          have hvc_pre : voteContention T n f s_r := (h4 b hecho).resolve_left hbound
          let w := s_i.bound_value.get (Option.ne_none_iff_isSome.mp (h5 hvc_pre))
          have hbv : s_i.bound_value = some w := by
            simp [w]
          by_cases hecho_w : echoSupport T n s_r w ≥ BCA_LTS.echoThreshold n f
          · -- echoSupport(w) ≥ threshold → uniqueness → w = b → bound = some b
            have hwb := echoSupport_unique T n f hn s_r
              (corrupted_budget T n f hreach) (corrupted_nodup T n f hreach)
              w b hecho_w hecho
            rw [hwb] at hbv
            let s_i' := { s_i with decided :=
              fun p => if p = i then some (some b) else s_i.decided p }
            refine ⟨s_i, s_i', s_i', InternalStar.refl, ?_, InternalStar.refl, ?_⟩
            · simp only [IdealBCA.ideal_bca, Order.add_one_le_iff, ne_eq, ge_iff_le, label_map, h1,
              hbv, and_self, and_true, s_i']
              exact ⟨by simp only [BCA_LTS.isCorrect, IdealBCA.isCorrect, h1] at hci ⊢; exact hci,
                by rw [h3]; exact hdec_none⟩
            · refine ⟨h1.trans hcorr.symm, ?_, ?_, ?_, ?_, ?_⟩
              · intro p; rw [h2, BCA_LTS.output_input hstep]
              · intro p; simp [s_i']; by_cases hp : p = i
                · subst hp; simp
                · simp [hp, h3, show (s_r'.local_ p).decided = (s_r.local_ p).decided from
                    BCA_LTS.output_decided_other hstep p hp]
              · intro b' hb'; rw [hecho_eq] at hb'; simp only [s_i']
                rcases h4 b' hb' with hval | hvc
                · exact Or.inl hval
                · exact Or.inr (step_voteContention_mono T n f hstep hvc)
              · intro hvc'; simp only [ne_eq, s_i']; apply h5
                rwa [← voteContention_eq T n f hcorr (BCA_LTS.output_voted hstep)]
              · intro b' hb'; simp only [s_i'] at hb'; rcases h6 b' hb' with hecho' | hcont
                · left; rw [hecho_eq]; exact hecho'
                · right; rwa [voteContention_eq T n f hcorr (BCA_LTS.output_voted hstep)]
          · -- contention + echoSupport(b) ≥ threshold + voteRecv quorum → contradiction.
            exfalso
            obtain ⟨cb₁, cb₂, hcne, hcf1, hcf2⟩ := hvc_pre
            have honly_b : ∀ p v, BCA_LTS.isCorrect T n s_r p →
                (s_r.local_ p).voted (some v) = true → v = b := by
              intro p v hcorr_p hvp
              exact echoSupport_unique T n f hn s_r
                (corrupted_budget T n f hreach) (corrupted_nodup T n f hreach)
                v b (voted_some_implies_echoSupport T n f hreach p v hcorr_p hvp) hecho
            have hbot_ge : s_r.corrupted.length +
                ((List.finRange n).filter (fun p =>
                  decide (p ∉ s_r.corrupted) &&
                  decide ((s_r.local_ p).voted none = true))).length ≥ n - f := by
              by_cases hcb1 : cb₁ = b
              · -- cb₁ = b, so cb₂ ≠ b (since cb₁ ≠ cb₂).
                have hcb2 : cb₂ ≠ b := by rw [← hcb1]; exact hcne.symm
                apply Nat.le_trans hcf1
                apply Nat.add_le_add_left
                apply filter_length_mono; intro p hp
                simp only [decide_not, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
                  decide_eq_false_iff_not, Bool.or_eq_true, Bool.decide_eq_true] at hp ⊢
                refine ⟨hp.1, ?_⟩
                rcases hp.2 with hvn | hvbin
                · exact hvn
                · -- p is correct and voted(some cb₂). By honly_b: cb₂ = b. Contradiction.
                  exact absurd (honly_b p cb₂ hp.1 hvbin) hcb2
              · -- cb₁ ≠ b. "Against cb₁" filter: voted ⊥ || voted cb₂.
                apply Nat.le_trans hcf2
                apply Nat.add_le_add_left
                apply filter_length_mono; intro p hp
                simp only [decide_not, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
                  decide_eq_false_iff_not, Bool.or_eq_true, Bool.decide_eq_true] at hp ⊢
                refine ⟨hp.1, ?_⟩
                rcases hp.2 with hvn | hvbin
                · exact hvn
                · exact absurd (honly_b p cb₁ hp.1 hvbin) hcb1
            have h3way : ∀ (l : List (Fin n)),
                (l.filter (fun r => decide (r ∉ s_r.corrupted) &&
                  decide ((s_r.local_ r).voted none = true))).length +
                (l.filter (fun r => decide (r ∉ s_r.corrupted) &&
                  (s_r.local_ i).voteRecv r (some b))).length +
                (l.filter (fun r => decide (r ∈ s_r.corrupted))).length ≤ l.length := by
              intro l; apply three_way_filter_le _ _ _ l
              · -- voted_none ∧ voteRecv while correct: contradiction via vote_trace
                intro r; by_contra h
                simp only [Bool.and_eq_true, Bool.not_eq_false, decide_eq_true_eq] at h
                exact voted_none_excludes_some T n f hreach r b h.1.1 h.1.2
                  (vote_trace T n f hreach i r b h.1.1 h.2.2)
              · -- ¬corrupted ∧ corrupted
                intro r; by_contra h
                simp only [Bool.and_eq_true, Bool.not_eq_false, decide_eq_true_eq] at h
                exact h.1.1 h.2
              · -- ¬corrupted ∧ corrupted
                intro r; by_contra h
                simp only [Bool.and_eq_true, Bool.not_eq_false, decide_eq_true_eq] at h
                exact h.1.1 h.2
            have h3 := h3way (List.finRange n)
            simp only [List.length_finRange] at h3
            have hvr_le : ((List.finRange n).filter
                (fun r => (s_r.local_ i).voteRecv r (some b))).length ≤
              ((List.finRange n).filter (fun r =>
                decide (r ∉ s_r.corrupted) && (s_r.local_ i).voteRecv r (some b))).length +
              ((List.finRange n).filter (fun r => decide (r ∈ s_r.corrupted))).length := by
              have hsplit := filter_split
                (fun r => (s_r.local_ i).voteRecv r (some b))
                (fun r => decide (r ∈ s_r.corrupted)) (List.finRange n)
              have hle := filter_and_le
                (fun r => (s_r.local_ i).voteRecv r (some b))
                (fun r => decide (r ∈ s_r.corrupted)) (List.finRange n)
              have hcomm : ((List.finRange n).filter
                  (fun r =>
                  (s_r.local_ i).voteRecv r (some b) && !decide (r ∈ s_r.corrupted))).length =
                  ((List.finRange n).filter (fun r =>
                  decide (r ∉ s_r.corrupted) && (s_r.local_ i).voteRecv r (some b))).length := by
                congr 1; apply List.filter_congr; intro r _
                rw [Bool.and_comm]; congr 1; exact decide_not.symm
              omega
            have hcc : ((List.finRange n).filter (fun r =>
                decide (r ∈ s_r.corrupted))).length ≤ f := by
              exact Nat.le_trans (nodup_sub_length ((finRange_nodup n).sublist List.filter_sublist)
                (fun x hx => by simp only [List.mem_filter, List.mem_finRange, decide_eq_true_eq,
                  true_and] at hx; exact hx)) hbudget
            omega
    · -- input i v: only input changes, echoSupport/voteSupport unchanged
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hR
      have hcorr := BCA_LTS.input_corrupted hstep
      have hinp_none := BCA_LTS.input_was_none hstep
      have hinp_none_i : s_i.input_ i = none := by rw [h2]; exact hinp_none
      refine ⟨s_i, { s_i with input_ := fun p => if p = i then some v else s_i.input_ p },
              { s_i with input_ := fun p => if p = i then some v else s_i.input_ p },
              .refl, ?_, .refl, ?_⟩
      · -- ideal step
        simp only [IdealBCA.ideal_bca, Order.add_one_le_iff, ne_eq, ge_iff_le, label_map, and_true]
        exact hinp_none_i
      · -- sim_rel preserved
        have hecho_eq := echoSupport_eq_of_eq T n hcorr (BCA_LTS.input_echoed hstep)
        refine ⟨h1.trans hcorr.symm, ?_, ?_, ?_, ?_, ?_⟩
        · intro p; simp only; by_cases hp : p = i
          · subst hp; simp [BCA_LTS.input_input_self hstep]
          · rw [if_neg hp, h2, BCA_LTS.input_input_other hstep p hp]
        · intro p; rw [h3, BCA_LTS.input_decided hstep]
        · intro b hb; rcases h4 b (by rwa [hecho_eq] at hb) with hval | hvc_pre
          · simp [hval]
          · right; rwa [voteContention_eq T n f hcorr (BCA_LTS.input_voted hstep)]
        · intro hvc; exact h5 (by rwa [← voteContention_eq T n f hcorr (BCA_LTS.input_voted hstep)])
        · intro b hb; simp only at hb; rcases h6 b hb with hecho | hcont
          · left; rw [hecho_eq]; exact hecho
          · right; rwa [voteContention_eq T n f hcorr (BCA_LTS.input_voted hstep)]


/-- The forward simulation from real BCA to ideal BCA. -/
def bca_forward_sim [Inhabited T] [Inhabited (Fin n)] (hn : n > 3 * f) :
    ForwardSim
      (BCA_LTS.bca T n f) (BCA_LTS.bca_labelling T n)
      (IdealBCA.ideal_bca T n f) (IdealBCA.ideal_labelling T n) where
  R := sim_rel T n f
  label_map := label_map T n
  init_sim := by
    exact bca_init_sim T n f hn
  step_internal := by
    exact bca_step_internal T n f hn
  step_external := by
    exact bca_step_external T n f hn

/-! ### Lifting Properties via Simulation -/

/-- All binary decisions match `bound_value`. -/
private def strong_agreement (s : BCA_LTS.State T n) : Prop :=
  ∀ p q v w,
    (s.local_ p).decided = some (some v) →
    (s.local_ q).decided = some (some w) →
    v = w

/-- Strong agreement holds at all reachable states. -/
private theorem real_strong_agreement [Inhabited T] [Inhabited (Fin n)] (hn : n > 3 * f) :
    (BCA_LTS.bca T n f).satisfies
      [ltl| □ ⌜ strong_agreement T n ⌝] :=
  (bca_forward_sim T n f hn).preserves_invariant
    (IdealBCA.inv T n f)
    (IdealBCA.inv_init T n f)
    (IdealBCA.inv_step T n f)
    (strong_agreement T n)
    (by intro s_r s_i ⟨_, _, hdec, _, _, _⟩ ⟨h1, _, _, _⟩ p q v w hpv hqw
        have hv := h1 p v ((hdec p).trans hpv)
        have hw := h1 q w ((hdec q).trans hqw)
        rw [hv] at hw; exact Option.some.inj hw)

/-- Lift agreement from ideal to real via the forward simulation. -/
theorem real_agreement [Inhabited T] [Inhabited (Fin n)] (hn : n > 3 * f) :
    (BCA_LTS.bca T n f).satisfies
      [ltl| □ ⌜ BCA_LTS.agreement T n ⌝] :=
  (bca_forward_sim T n f hn).preserves_invariant
    (IdealBCA.inv T n f)
    (IdealBCA.inv_init T n f)
    (IdealBCA.inv_step T n f)
    (BCA_LTS.agreement T n)
    (by intro s_r s_i ⟨_, _, hdec, _, _, _⟩ ⟨h1, _, _, _⟩ p q v w _ _ hpv hqw
        have hv := h1 p v ((hdec p).trans hpv)
        have hw := h1 q w ((hdec q).trans hqw)
        rw [hv] at hw; exact Option.some.inj hw)

/-- Lift validity from ideal to real via the forward simulation. -/
theorem real_validity [Inhabited T] [Inhabited (Fin n)] (hn : n > 3 * f) (val : T) :
    (BCA_LTS.bca T n f).satisfies
      [ltl| □ ⌜ BCA_LTS.validity T n val ⌝] :=
  (bca_forward_sim T n f hn).preserves_invariant
    (IdealBCA.inv T n f)
    (IdealBCA.inv_init T n f)
    (IdealBCA.inv_step T n f)
    (BCA_LTS.validity T n val)
    (by intro s_r s_i ⟨hcorr, hinp, hdec, _, _, _⟩ ⟨h1, h2, h3, h4⟩
        simp only [BCA_LTS.validity]
        intro hpre p
        rw [show (s_r.local_ p).decided = s_i.decided p from (hdec p).symm]
        have hpre_i : ∀ q, ¬IdealBCA.isCorrect T n s_i q ∨
            s_i.input_ q = none ∨ s_i.input_ q = some val := by
          intro q; simp only [IdealBCA.isCorrect, hcorr, hinp]; exact hpre q
        have no_support : ∀ w, w ≠ val → IdealBCA.inputSupport T n s_i w > 0 → False := by
          intro w hwv hpos
          simp only [IdealBCA.inputSupport] at hpos
          obtain ⟨q, hq⟩ := List.exists_mem_of_length_pos hpos
          simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hq
          obtain ⟨_, hqcorr, hqinp⟩ := hq
          rcases hpre_i q with hnc | hno | hyes
          · exact absurd hqcorr hnc
          · simp [hno] at hqinp
          · simp [hyes] at hqinp; exact hwv hqinp.symm
        match hd : s_i.decided p with
        | none => left; rfl
        | some (some w) =>
          by_cases hwv : w = val
          · right; rw [hwv]
          · exfalso; exact no_support w hwv (by have := h3 w (h1 p w hd); omega)
        | some none =>
          exfalso
          obtain ⟨b₁, b₂, hne, hs1, hs2⟩ := h2 p hd
          by_cases hb1v : b₁ = val
          · exact no_support b₂ (fun h => hne (hb1v.trans h.symm)) (by omega)
          · exact no_support b₁ hb1v (by omega))

/-- Binding: once some process decides, all future binary decisions agree. -/
theorem real_binding [Inhabited T] [Inhabited (Fin n)] (hn : n > 3 * f) :
    BCA_LTS.binding T n (BCA_LTS.bca T n f) :=
  (bca_forward_sim T n f hn).preserves_branching
    (W := T)
    (P_guard := fun s_i => ∃ p v, IdealBCA.isCorrect T n s_i p ∧ s_i.decided p = some v)
    (P_concl := fun b s_i => ∀ q w, IdealBCA.isCorrect T n s_i q →
      s_i.decided q = some (some w) → w = b)
    (Q_guard := fun s_r => ∃ p v, BCA_LTS.isCorrect T n s_r p ∧
      (s_r.local_ p).decided = some v)
    (Q_concl := fun b s_r => ∀ q w, BCA_LTS.isCorrect T n s_r q →
      (s_r.local_ q).decided = some (some w) → w = b)
    (IdealBCA.ideal_binding T n f)
    (by -- guard transfer: Q_guard s_r → P_guard s_i
      intro s_r s_i ⟨hcorr, _, hdec, _, _, _⟩ ⟨p, v, hcorr_p, hdec_p⟩
      exact ⟨p, v,
        by simp only [IdealBCA.isCorrect, BCA_LTS.isCorrect, hcorr] at hcorr_p ⊢; exact hcorr_p,
        by rw [hdec p]; exact hdec_p⟩)
    (by -- conclusion transfer: P_concl b s_i → Q_concl b s_r
      intro b s_r s_i ⟨hcorr, _, hdec, _, _, _⟩ hconcl q w hcorr_q hdec_q
      exact hconcl q w
        (by simp only [IdealBCA.isCorrect, BCA_LTS.isCorrect, hcorr] at hcorr_q ⊢; exact hcorr_q)
        (by rw [hdec q]; exact hdec_q))

end BCA_Simulation
