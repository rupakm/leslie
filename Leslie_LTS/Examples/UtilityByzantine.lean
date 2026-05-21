import Leslie_LTS.Framework

/-! # Quorum and counting lemmas for LTS-based Byzantine protocols

  General-purpose lemmas for quorum intersection and pigeonhole arguments
  over `Fin n` and `List.finRange`. Used by BRB, BCA, and other
  LTS-based Byzantine protocol proofs.
-/

/-- A nodup sublist has bounded length. -/
theorem nodup_sub_length {α : Type}
    {l m : List α} (hnd : l.Nodup) (hsub : ∀ x ∈ l, x ∈ m) :
    l.length ≤ m.length := by
  classical
  induction l generalizing m with
  | nil => simp
  | cons a t ih =>
    have ⟨hat, hnd_t⟩ := List.nodup_cons.mp hnd
    have ha := hsub a (List.mem_cons.mpr (.inl rfl))
    have h1 := ih hnd_t fun x hx =>
      (List.mem_erase_of_ne (show x ≠ a from fun h => hat (h ▸ hx))).mpr
        (hsub x (List.mem_cons.mpr (.inr hx)))
    have h2 := List.length_erase_of_mem ha
    have : m.length ≥ 1 := by cases m with | nil => simp at ha | cons => simp
    simp [List.length_cons]; omega

/-- `List.finRange n` has no duplicates. -/
theorem finRange_nodup : ∀ n, (List.finRange n).Nodup := by
  intro n; induction n with
  | zero => simp [List.finRange]
  | succ n ih =>
    rw [List.finRange_succ, List.nodup_cons]
    constructor
    · simp [List.mem_map]
    · exact ih.map fun a b h => Fin.ext (Nat.succ.inj (Fin.val_eq_of_eq h))

/-- Monotonicity: if P implies Q pointwise then |filter P| ≤ |filter Q|. -/
theorem filter_length_mono {α : Type} (P Q : α → Bool) (l : List α)
    (h : ∀ x, P x = true → Q x = true) :
    (l.filter P).length ≤ (l.filter Q).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.filter_cons]
    cases hpa : P a <;> cases hqa : Q a <;>
      (try exact absurd (h a hpa) (by rw [hqa]; decide)) <;>
      (simp +decide only [ite_true, ite_false, List.length_cons]; omega)

/-- |filter(· ∈ l)| ≤ l.length. -/
theorem filter_mem_le {n : Nat} (l : List (Fin n)) :
    ((List.finRange n).filter (fun p => decide (p ∈ l))).length ≤ l.length :=
  nodup_sub_length ((finRange_nodup n).sublist List.filter_sublist)
    (fun x hx => by simp only [List.mem_filter, List.mem_finRange, decide_eq_true_eq,
      true_and] at hx; exact hx)

/-- |filter (P ∧ Q)| ≤ |filter Q|. -/
theorem filter_and_le {α : Type} (P Q : α → Bool) (l : List α) :
    (l.filter (fun x => P x && Q x)).length ≤ (l.filter Q).length := by
  rw [← List.filter_filter]; exact List.filter_sublist.length_le

/-- |filter P| = |filter (P ∧ Q)| + |filter (P ∧ ¬Q)|. -/
theorem filter_split {α : Type} (P Q : α → Bool) (l : List α) :
    (l.filter P).length =
    (l.filter (fun x => P x && Q x)).length +
    (l.filter (fun x => P x && !Q x)).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.filter_cons]
    cases P a <;> cases Q a <;> simp <;> omega

/-- |filter(P ∨ Q)| ≤ |filter P| + |filter Q|. -/
theorem filter_or_le {α : Type} (P Q : α → Bool) (l : List α) :
    (l.filter (fun x => P x || Q x)).length ≤
    (l.filter P).length + (l.filter Q).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.filter_cons]
    cases P a <;> cases Q a <;> simp <;> omega

/-- Three-way partition: mutually exclusive P, Q, R have |P| + |Q| + |R| ≤ |l|. -/
theorem three_way_filter_le {α : Type} (P Q R : α → Bool) (l : List α)
    (hdisj : ∀ x, (P x && Q x) = false)
    (hdisj2 : ∀ x, (P x && R x) = false)
    (hdisj3 : ∀ x, (Q x && R x) = false) :
    (l.filter P).length + (l.filter Q).length + (l.filter R).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.filter_cons, List.length_cons]
    have := hdisj a; have := hdisj2 a; have := hdisj3 a
    cases hpa : P a <;> cases hqa : Q a <;> cases hra : R a <;> simp [*] at * <;> omega

/-- If P src = false, adding `q = src` increases filter length by exactly one. -/
theorem filter_succ_of_new {n : Nat} (P : Fin n → Bool)
    (src : Fin n) (hnew : P src = false) :
    ((List.finRange n).filter (fun q => decide (q = src) || P q)).length =
    ((List.finRange n).filter P).length + 1 := by
  have aux : ∀ (l : List (Fin n)), src ∈ l → l.Nodup →
      (l.filter (fun q => decide (q = src) || P q)).length =
      (l.filter P).length + 1 := by
    intro l; induction l with
    | nil => intro h; exact absurd h (by simp)
    | cons a t ih =>
      intro hin hnd
      simp only [List.filter_cons]
      rcases List.mem_cons.mp hin with rfl | hmem
      · have hsrc_notin : src ∉ t := (List.nodup_cons.mp hnd).1
        simp only [decide_true, hnew, Bool.or_false, ↓reduceIte, List.length_cons,
          Bool.false_eq_true, Nat.add_right_cancel_iff]
        have heq : ∀ q ∈ t, (decide (q = src) || P q) = P q := by
          intro q hq
          have : q ≠ src := fun h => hsrc_notin (h ▸ hq)
          simp [this]
        rw [List.filter_congr heq]
      · have hnd_t := (List.nodup_cons.mp hnd).2
        have hane : a ≠ src := by
          intro h; subst h; exact (List.nodup_cons.mp hnd).1 hmem
        simp only [hane, decide_false, Bool.false_or]
        cases hra : P a
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih hmem hnd_t
        · simp only [↓reduceIte, List.length_cons, Nat.add_right_cancel_iff]; rw [ih hmem hnd_t]
  exact aux (List.finRange n) (List.mem_finRange src) (finRange_nodup n)

/-- Strict monotonicity: P ⊂ Q with a witness gives |filter Q| ≥ |filter P| + 1. -/
theorem filter_length_strict_mono {n : Nat} (P Q : Fin n → Bool)
    (hmono : ∀ x, P x = true → Q x = true)
    (x : Fin n) (hP : P x = false) (hQ : Q x = true) :
    ((List.finRange n).filter Q).length ≥ ((List.finRange n).filter P).length + 1 := by
  have hsplit := filter_split Q P (List.finRange n)
  have heq : ((List.finRange n).filter (fun x => Q x && P x)).length =
      ((List.finRange n).filter P).length := by
    congr 1; apply List.filter_congr
    intro y _
    cases hpy : P y <;> cases hqy : Q y <;>
      (try exact absurd (hmono y hpy) (by rw [hqy]; decide)) <;> simp +decide
  have hge : ((List.finRange n).filter (fun x => Q x && !P x)).length ≥ 1 := by
    have : x ∈ (List.finRange n).filter (fun y => Q y && !P y) := by
      simp [List.mem_filter, hP, hQ]
    match h : (List.finRange n).filter (fun y => Q y && !P y) with
    | [] => exact absurd (List.mem_nil_iff x |>.mp (h ▸ this)) (by simp)
    | _ :: _ => simp
  omega

/-- Pigeonhole: if |{r | P r}| > |corrupted|, some r satisfies P and is not corrupted. -/
theorem pigeonhole_filter {n : Nat} (P : Fin n → Bool) (corrupted : List (Fin n))
    (hgt : corrupted.length < ((List.finRange n).filter P).length) :
    ∃ q, P q = true ∧ q ∉ corrupted := by
  let Q : Fin n → Bool := fun x => decide (x ∈ corrupted)
  have hsplit := filter_split P Q (List.finRange n)
  have hle : ((List.finRange n).filter (fun x => P x && Q x)).length ≤
      corrupted.length := by
    calc ((List.finRange n).filter (fun x => P x && Q x)).length
        ≤ ((List.finRange n).filter Q).length := filter_and_le P Q _
      _ ≤ corrupted.length := by
          apply nodup_sub_length ((finRange_nodup n).sublist List.filter_sublist)
          intro x hx; simp only [List.mem_filter, List.mem_finRange, decide_eq_true_eq, true_and,
            Q] at hx; exact hx
  obtain ⟨q, hq⟩ := List.exists_mem_of_length_pos (by omega :
    0 < ((List.finRange n).filter (fun x => P x && !Q x)).length)
  have ⟨_, hq2⟩ := List.mem_filter.mp hq
  simp only [Q, Bool.and_eq_true, Bool.not_eq_true'] at hq2
  exact ⟨q, hq2.1, fun h => by simp [h] at hq2⟩

/-- If every correct process satisfies A, then |filter A| ≥ n - f. -/
theorem count_correct_ge {n f : Nat} (corrupted : List (Fin n))
    (hbudget : corrupted.length ≤ f) (A : Fin n → Bool)
    (hall : ∀ p, p ∉ corrupted → A p = true) :
    ((List.finRange n).filter A).length ≥ n - f := by
  have hmono : ((List.finRange n).filter
      (fun p => decide (p ∉ corrupted))).length ≤
      ((List.finRange n).filter A).length := by
    apply filter_length_mono
    intro p hp
    simp only [decide_eq_true_eq] at hp
    exact hall p hp
  have hneg_le :
      ((List.finRange n).filter (fun p => !decide (p ∉ corrupted))).length ≤ f := by
    calc ((List.finRange n).filter (fun p => !decide (p ∉ corrupted))).length
        ≤ ((List.finRange n).filter (fun p => decide (p ∈ corrupted))).length := by
          apply filter_length_mono; intro p hp
          simp only [Bool.not_eq_true', decide_eq_false_iff_not, Classical.not_not,
            decide_eq_true_eq] at hp ⊢; exact hp
      _ ≤ corrupted.length := filter_mem_le corrupted
      _ ≤ f := hbudget
  have hsplit := filter_split (fun _ : Fin n => true)
    (fun p => decide (p ∉ corrupted)) (List.finRange n)
  have htriv : (List.finRange n).filter (fun _ : Fin n => true) = List.finRange n := by
    apply List.filter_eq_self.mpr; intros; rfl
  have heq1 : ((List.finRange n).filter
      (fun x => (fun _ : Fin n => true) x && decide (x ∉ corrupted))).length =
      ((List.finRange n).filter (fun p => decide (p ∉ corrupted))).length := rfl
  have heq2 : ((List.finRange n).filter
      (fun x => (fun _ : Fin n => true) x && !decide (x ∉ corrupted))).length =
      ((List.finRange n).filter (fun p => !decide (p ∉ corrupted))).length := rfl
  rw [htriv, heq1, heq2] at hsplit
  have hfin : (List.finRange n).length = n := List.length_finRange
  omega

/-- Budget → intersected count: |filter (M ∧ ¬corrupted)| ≥ k - f. -/
theorem intersect_correct_ge {n f k : Nat} (corrupted : List (Fin n)) (M : Fin n → Bool)
    (hbudget : corrupted.length ≤ f)
    (hM : ((List.finRange n).filter M).length ≥ k) :
    ((List.finRange n).filter (fun s => M s && decide (s ∉ corrupted))).length ≥ k - f := by
  have hsplit := filter_split M (fun s => decide (s ∉ corrupted)) (List.finRange n)
  have hMnotC_le : ((List.finRange n).filter
      (fun s => M s && !decide (s ∉ corrupted))).length ≤ f := by
    calc ((List.finRange n).filter (fun s => M s && !decide (s ∉ corrupted))).length
        ≤ ((List.finRange n).filter (fun s => !decide (s ∉ corrupted))).length :=
          filter_and_le M (fun s => !decide (s ∉ corrupted)) _
      _ ≤ corrupted.length := by
          apply nodup_sub_length ((finRange_nodup n).sublist List.filter_sublist)
          intro x hx; simp only [decide_not, Bool.not_not, List.mem_filter, List.mem_finRange,
            decide_eq_true_eq, true_and] at hx; exact hx
      _ ≤ f := hbudget
  omega

/-- Echo quorum intersection: two quorums of size ≥ n−f for different values
    contradict n > 3f. -/
theorem echo_quorum_intersection {n f : Nat} {α : Type}
    (hn : n > 3 * f)
    (v w : α) (p1 p2 : Fin n)
    (echoRecv : Fin n → Fin n → α → Bool)
    (echoed : Fin n → Option α)
    (corrupted : List (Fin n))
    (hbudget : corrupted.length ≤ f)
    (hetrace : ∀ p q val, p ∉ corrupted →
      echoRecv q p val = true → echoed p = some val)
    (hv : ((List.finRange n).filter (echoRecv p1 · v)).length ≥ n - f)
    (hw : ((List.finRange n).filter (echoRecv p2 · w)).length ≥ n - f) :
    v = w := by
  classical
  if hvw : v = w then exact hvw else
  exfalso
  have echo_mono := fun (proc : Fin n) (val : α) =>
    filter_length_mono
      (fun r => echoRecv proc r val && !decide (r ∈ corrupted))
      (fun r => decide (r ∉ corrupted) && decide (echoed r = some val))
      (List.finRange n)
      (fun r hr => by
        rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hr
        rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
        exact ⟨hr.2, hetrace r proc val hr.2 hr.1⟩)
  let cc := ((List.finRange n).filter (fun r => decide (r ∈ corrupted))).length
  have hcc_le : cc ≤ f :=
    Nat.le_trans
      (nodup_sub_length ((finRange_nodup n).sublist List.filter_sublist)
        (fun x hx => by simp only [List.mem_filter, List.mem_finRange, decide_eq_true_eq,
          true_and] at hx; exact hx))
      hbudget
  have hcount_v : ((List.finRange n).filter (fun r =>
      decide (r ∉ corrupted) && decide (echoed r = some v))).length ≥ n - f - cc := by
    apply Nat.le_trans _ (echo_mono p1 v)
    have hsplit := filter_split (echoRecv p1 · v)
      (fun r => decide (r ∈ corrupted)) (List.finRange n)
    have hle := filter_and_le (echoRecv p1 · v)
      (fun r => decide (r ∈ corrupted)) (List.finRange n)
    omega
  have hcount_w : ((List.finRange n).filter (fun r =>
      decide (r ∉ corrupted) && decide (echoed r = some w))).length ≥ n - f - cc := by
    apply Nat.le_trans _ (echo_mono p2 w)
    have hsplit := filter_split (echoRecv p2 · w)
      (fun r => decide (r ∈ corrupted)) (List.finRange n)
    have hle := filter_and_le (echoRecv p2 · w)
      (fun r => decide (r ∈ corrupted)) (List.finRange n)
    omega
  have h3 : ∀ (l : List (Fin n)),
      (l.filter (fun r => decide (r ∉ corrupted) && decide (echoed r = some v))).length +
      (l.filter (fun r => decide (r ∉ corrupted) && decide (echoed r = some w))).length +
      (l.filter (fun r => decide (r ∈ corrupted))).length
      ≤ l.length := by
    intro l; induction l with
    | nil => simp
    | cons a t ih =>
      simp only [List.filter_cons, List.length_cons]
      split <;> split <;> split <;>
        (rename_i h1 h2 h3; simp only [Bool.and_eq_true, decide_eq_true_eq] at h1 h2 h3;
         first
           | (obtain ⟨hna, _⟩ := h1; exact absurd h3 hna)
           | (obtain ⟨hna, _⟩ := h2; exact absurd h3 hna)
           | (have := h1.2.symm.trans h2.2; simp only [Option.some.injEq] at this;
              exact absurd this hvw)
           | (simp only [List.length_cons]; omega)
           | omega)
  have h3way := h3 (List.finRange n)
  have hlen : (List.finRange n).length = n := List.length_finRange
  omega

/-- Extract equalities from a Boolean decide-pair update. -/
theorem or_decide_pair_eq {α β : Type} [DecidableEq α] [DecidableEq β]
    {a a' : α} {b b' : β} {old : Bool}
    (h_old : old = false)
    (h_new : (decide (a = a') && decide (b = b') || old) = true) :
    a = a' ∧ b = b' := by
  simp only [h_old, Bool.or_false, Bool.and_eq_true, decide_eq_true_eq] at h_new; exact h_new
