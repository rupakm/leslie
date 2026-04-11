import Leslie.Cutoff
import Leslie.Examples.Combinators.QuorumSystem

/-! ## Cutoff Theorem for Termination

    The safety cutoff transfers invariants: if `inv` holds for n ≤ K, it
    holds for all n. Can we transfer *termination*?

    **Result**: For TV-deterministic protocols (successor threshold view
    determined by current threshold view alone), termination within T rounds
    transfers across n with the SAME bound T and the SAME cutoff K.

    **Key condition**: `tvDeterministic` — two configs with the same threshold
    view produce successors with the same threshold view. This holds for
    protocols where above-threshold values are absorbing (OneThirdRule,
    ThresholdConsensus, any consensus where decided states don't change).
-/

open TLA

namespace TLA.TerminationCutoff

/-! ### TV-Deterministic Protocols -/

/-- A `SymThreshAlg` is TV-deterministic if the successor threshold view
    depends only on the current threshold view, not on exact counts. -/
def tvDeterministic (alg : SymThreshAlg k α_num α_den) : Prop :=
  ∀ n₁ n₂ (c₁ : Config k n₁) (c₂ : Config k n₂),
    c₁.threshView α_num α_den = c₂.threshView α_num α_den →
    (Config.succ alg c₁).threshView α_num α_den =
    (Config.succ alg c₂).threshView α_num α_den

/-- Iterated successor: apply `Config.succ` t times. -/
def Config.iterSucc (alg : SymThreshAlg k α_num α_den) :
    Nat → Config k n → Config k n
  | 0, c => c
  | t + 1, c => Config.iterSucc alg t (Config.succ alg c)

/-- For TV-deterministic protocols, iterated successors preserve
    the threshold view correspondence. -/
theorem iterSucc_tv_eq
    {alg : SymThreshAlg k α_num α_den}
    (h_det : tvDeterministic alg)
    (n₁ n₂ : Nat) (c₁ : Config k n₁) (c₂ : Config k n₂)
    (h_tv : c₁.threshView α_num α_den = c₂.threshView α_num α_den) :
    ∀ t, (Config.iterSucc alg t c₁).threshView α_num α_den =
         (Config.iterSucc alg t c₂).threshView α_num α_den := by
  intro t
  induction t generalizing c₁ c₂ with
  | zero => simp [Config.iterSucc, h_tv]
  | succ t ih =>
    simp only [Config.iterSucc]
    exact ih (Config.succ alg c₁) (Config.succ alg c₂)
      (h_det n₁ n₂ c₁ c₂ h_tv)

/-! ### Termination cutoff theorem -/

/-- A "decided" predicate on threshold views. -/
abbrev TVDecided (k : Nat) := ThreshView k → Prop

/-- **Termination cutoff for TV-deterministic protocols.**

    If the protocol terminates within T rounds from initial config c₀ at
    some n₀, then for any n and any config c with the same initial
    threshold view, it terminates within T rounds.

    The proof: by `iterSucc_tv_eq`, the threshold view at each round
    is the same for c and c₀. So if c₀'s trace reaches "decided" at
    step t, so does c's. -/
theorem termination_cutoff_tv_deterministic
    {alg : SymThreshAlg k α_num α_den}
    (h_det : tvDeterministic alg)
    (decided : TVDecided k)
    (T : Nat) (n₀ : Nat) (c₀ : Config k n₀)
    -- Termination at n₀: some step t ≤ T reaches decided
    (h_term : ∃ t, t ≤ T ∧ decided
      ((Config.iterSucc alg t c₀).threshView α_num α_den))
    -- Any n with matching initial threshold view
    (n : Nat) (c : Config k n)
    (h_tv : c.threshView α_num α_den = c₀.threshView α_num α_den) :
    ∃ t, t ≤ T ∧ decided
      ((Config.iterSucc alg t c).threshView α_num α_den) := by
  obtain ⟨t, ht, h_dec⟩ := h_term
  refine ⟨t, ht, ?_⟩
  have h_eq := iterSucc_tv_eq h_det n n₀ c c₀ h_tv t
  rw [h_eq]; exact h_dec

/-- **Bounded termination for all n**, combining:
    1. `thresh_scaling_down`: every large-n config maps to a small-n config
       with the same threshold view
    2. `termination_cutoff_tv_deterministic`: same initial TV → same
       termination behavior

    If termination within T rounds is verified for all n ≤ K, then
    termination within T rounds holds for all n. -/
theorem bounded_termination_cutoff
    {alg : SymThreshAlg k α_num α_den}
    (hα : α_num < α_den) (h_half : 2 * α_num ≥ α_den)
    (h_det : tvDeterministic alg)
    (decided : TVDecided k)
    (T : Nat)
    -- Verified for small instances
    (h_small : ∀ n, n ≤ cutoffBound k α_num α_den →
      ∀ c : Config k n, ∃ t, t ≤ T ∧ decided
        ((Config.iterSucc alg t c).threshView α_num α_den)) :
    ∀ n (c : Config k n), ∃ t, t ≤ T ∧ decided
      ((Config.iterSucc alg t c).threshView α_num α_den) := by
  intro n c
  obtain ⟨n', hn', c', hc'⟩ := thresh_scaling_down k α_num α_den hα h_half n c
  exact termination_cutoff_tv_deterministic h_det decided T n' c'
    (h_small n' hn' c') n c hc'.symm

/-! ### When is a protocol TV-deterministic?

    **Sufficient condition: absorbing at threshold.** If every above-threshold
    value maps to itself under the update, then:
    - Above-threshold counts are preserved (all holders stay)
    - Below-threshold counts redistribute but their threshold status
      depends only on the redistribution, which is determined by the TV

    In OneThirdRule: if >2n/3 hold value 0, after the round, everyone
    who received the supermajority adopts 0. Under reliable communication,
    ALL n processes adopt 0. So 0 is still above threshold. Below-threshold
    values go to 0.

    More generally: any protocol where the decided state is absorbing
    (processes don't change value after deciding) is TV-deterministic
    once a decision threshold is reached. -/

/-- A value is absorbing at threshold: if above threshold, maps to itself. -/
def AbsorbingAtThreshold (alg : SymThreshAlg k α_num α_den) : Prop :=
  ∀ v : Fin k, ∀ tv : ThreshView k, tv v = true → alg.update v tv = v

/-! ### Discussion: scope and limitations

    **What this covers:**
    - Bounded termination (within T rounds) under reliable communication
    - Symmetric threshold protocols that are TV-deterministic
    - The cutoff bound K is the same as for safety -- no extra cost

    **What this does NOT cover:**
    - Eventual termination under weak communication predicates (e.g.,
      "eventually synchronous"). The communication predicate is an
      environmental assumption independent of n.
    - Protocols where the successor TV depends on exact counts (not
      TV-deterministic). These may still terminate for all n, but the
      bound T might depend on n.
    - Probabilistic termination (e.g., Ben-Or with random coins).

    **Open question:** For non-TV-deterministic protocols, can we bound
    T as a function of n? The threshold view space is finite (2^k),
    so any deterministic execution from a fixed config must enter a cycle
    within 2^k steps. If no cycle contains a "decided" view, the protocol
    doesn't terminate from that config. If every cycle contains a decided
    view, termination is guaranteed within 2^k rounds. But 2^k may be
    much larger than the actual termination time T observed at small n.

    **Conjecture:** For the class of protocols where below-threshold counts
    "converge" (the redistribution approaches a fixed point), termination
    time T(n) is bounded by a function of k alone, independent of n.
    This would give a termination cutoff even for non-TV-deterministic
    protocols, but the bound would be T = O(2^k) rather than the
    empirically observed T = O(1). -/

/-! ### Collapsing protocols: a sufficient condition for TV-determinism -/

/-- A `SymThreshAlg` is **collapsing** if whenever any threshold is crossed,
    the update maps ALL values to the same target. -/
def isCollapsing (alg : SymThreshAlg k α_num α_den) : Prop :=
  ∀ tv : ThreshView k, (∃ v, tv v = true) →
    ∃ target, ∀ v, alg.update v tv = target

/-- A `SymThreshAlg` is **identity below threshold** if when no threshold is
    crossed, the update preserves every value. -/
def isIdentityBelowThreshold (alg : SymThreshAlg k α_num α_den) : Prop :=
  ∀ tv : ThreshView k, (∀ v, tv v = false) → ∀ v, alg.update v tv = v

/-! #### Helper: indicator sum -/

/-- Sum of a constant-zero map is zero. -/
private theorem list_map_zero_sum {α : Type} (l : List α) :
    (l.map fun _ => (0 : Nat)).sum = 0 := by
  induction l with | nil => rfl | cons _ _ ih => simp [List.sum_cons, ih]

/-- Indicator sum over `finRange k`: exactly 1. -/
private theorem fin_indicator_sum (k : Nat) (v : Fin k) :
    ((List.finRange k).map fun w => if w = v then 1 else (0 : Nat)).sum = 1 := by
  induction k with
  | zero => exact v.elim0
  | succ k ih =>
    rw [List.finRange_succ]
    simp only [List.map, List.sum_cons]
    by_cases hv : v = 0
    · subst hv; simp only [ite_true]
      have : ((List.finRange k).map Fin.succ).map
          (fun w => if w = (0 : Fin (k+1)) then 1 else (0 : Nat)) =
          ((List.finRange k).map Fin.succ).map (fun _ => (0 : Nat)) := by
        apply List.map_congr_left; intro w hw
        simp only [List.mem_map] at hw; obtain ⟨x, _, rfl⟩ := hw
        exact if_neg (Fin.succ_ne_zero x)
      rw [this, list_map_zero_sum]
    · rw [if_neg (Ne.symm hv)]
      simp only [Nat.zero_add]
      obtain ⟨v', rfl⟩ : ∃ v' : Fin k, v = Fin.succ v' :=
        ⟨v.pred (by omega), (Fin.succ_pred v (by omega)).symm⟩
      rw [show ((List.finRange k).map Fin.succ).map
            (fun w => if w = Fin.succ v' then 1 else (0 : Nat)) =
          (List.finRange k).map (fun w => if w = v' then 1 else (0 : Nat)) from by
        rw [List.map_map]; apply List.map_congr_left; intro w _
        show (if Fin.succ w = Fin.succ v' then 1 else (0 : Nat)) =
             if w = v' then 1 else 0
        by_cases h : w = v' <;> simp [h, Fin.succ_inj]]
      exact ih v'

/-! #### SuccCounts helpers -/

/-- When the update is the identity, successor counts equal current counts. -/
private theorem succCounts_of_identity {k α_num α_den n : Nat}
    (alg : SymThreshAlg k α_num α_den) (c : Config k n)
    (h_id : ∀ v, alg.update v (c.threshView α_num α_den) = v)
    (v : Fin k) : succCounts alg c v = c.counts v := by
  simp only [succCounts]
  -- Rewrite update to identity
  rw [show ((List.finRange k).map fun w =>
        if alg.update w (c.threshView α_num α_den) = v then c.counts w else 0) =
      (List.finRange k).map (fun w => if w = v then c.counts w else 0) from
    List.map_congr_left (fun w _ => by rw [h_id w])]
  -- Factor out c.counts v
  rw [show ((List.finRange k).map fun w => if w = v then c.counts w else 0) =
      (List.finRange k).map (fun w => c.counts v * if w = v then 1 else 0) from
    List.map_congr_left (fun w _ => by by_cases h : w = v <;> simp [h])]
  rw [show ((List.finRange k).map fun w => c.counts v * if w = v then 1 else 0).sum =
      c.counts v * ((List.finRange k).map fun w => if w = v then 1 else 0).sum from by
    induction (List.finRange k) with
    | nil => simp | cons x xs ih => simp [List.sum_cons, Nat.mul_add, ih]]
  rw [fin_indicator_sum]; omega

/-- When all values map to a target, successor count at target equals n. -/
private theorem succCounts_all_to_target {k α_num α_den n : Nat}
    (alg : SymThreshAlg k α_num α_den) (c : Config k n)
    (target : Fin k)
    (h_all : ∀ v, alg.update v (c.threshView α_num α_den) = target) :
    succCounts alg c target = n := by
  simp only [succCounts]
  rw [show ((List.finRange k).map fun v =>
        if alg.update v (c.threshView α_num α_den) = target then c.counts v else 0) =
      (List.finRange k).map c.counts from
    List.map_congr_left (fun v _ => by simp [h_all v])]
  exact c.sum_eq

/-- When all values map to a target, successor count at other values is 0. -/
private theorem succCounts_all_to_target_other {k α_num α_den n : Nat}
    (alg : SymThreshAlg k α_num α_den) (c : Config k n)
    (target : Fin k) (v : Fin k)
    (h_all : ∀ w, alg.update w (c.threshView α_num α_den) = target)
    (hne : v ≠ target) :
    succCounts alg c v = 0 := by
  simp only [succCounts]
  suffices ∀ w ∈ List.finRange k,
    (if alg.update w (c.threshView α_num α_den) = v then c.counts w else 0) = 0 by
    rw [show ((List.finRange k).map fun w =>
          if alg.update w (c.threshView α_num α_den) = v
          then c.counts w else 0) = (List.finRange k).map (fun _ => 0) from
      List.map_congr_left this]
    exact list_map_zero_sum _
  intro w _
  simp [show alg.update w (c.threshView α_num α_den) ≠ v from by
    rw [h_all w]; exact Ne.symm hne]

/-! #### Threshold-crossing lemmas -/

/-- If any threshold is crossed, n > 0. -/
private theorem n_pos_of_thresh {k α_num α_den n : Nat} (c : Config k n)
    (v : Fin k) (htv : c.threshView α_num α_den v = true) : n > 0 := by
  simp [Config.threshView, decide_eq_true_eq] at htv
  by_contra h
  have hn : n = 0 := by omega
  subst hn
  have hcv : c.counts v = 0 := by
    have := TLA.mem_le_sum (List.finRange k) c.counts v (List.mem_finRange v)
    rw [c.sum_eq] at this; omega
  rw [hcv] at htv; simp at htv

/-- No threshold exists implies all bits are false. -/
private theorem all_false_of_not_exists_true {k : Nat} {tv : ThreshView k}
    (h : ¬∃ v, tv v = true) : ∀ v, tv v = false := by
  intro v; by_contra hv
  exact h ⟨v, by cases htv : tv v <;> simp_all⟩

/-- The successor threshold view unfolds to a decide on succCounts. -/
private theorem succ_threshView_eq {k α_num α_den n : Nat}
    (alg : SymThreshAlg k α_num α_den) (c : Config k n) (v : Fin k) :
    (Config.succ alg c).threshView α_num α_den v =
    decide (succCounts alg c v * α_den > α_num * n) := by
  simp [Config.succ, Config.threshView]

/-! ### The collapsing lemma -/

/-- **Collapsing + identity below threshold implies TV-deterministic.**

    When a threshold is crossed, the collapsing property sends ALL processes
    to the same target, making successor counts `(n, 0, ..., 0)` at target.
    The successor TV depends only on `n > 0` (which follows from the threshold
    being crossed) and `alpha_num < alpha_den`.

    When no threshold is crossed, the identity property preserves counts,
    so the successor TV equals the current TV. -/
theorem collapsing_identity_tvDeterministic
    {k α_num α_den : Nat} (hα : α_num < α_den)
    (alg : SymThreshAlg k α_num α_den)
    (h_col : isCollapsing alg)
    (h_id : isIdentityBelowThreshold alg) :
    tvDeterministic alg := by
  intro n₁ n₂ c₁ c₂ htv
  by_cases h_any : ∃ v, c₁.threshView α_num α_den v = true
  · -- Some threshold is crossed: collapsing to a single target
    obtain ⟨v₀, hv₀⟩ := h_any
    obtain ⟨t, ht₁⟩ := h_col (c₁.threshView α_num α_den) ⟨v₀, hv₀⟩
    have ht₂ : ∀ v, alg.update v (c₂.threshView α_num α_den) = t := by
      intro v; rw [← htv]; exact ht₁ v
    have hn₁ : n₁ > 0 := n_pos_of_thresh c₁ v₀ hv₀
    have hn₂ : n₂ > 0 := n_pos_of_thresh c₂ v₀ (by rw [← htv]; exact hv₀)
    funext v
    rw [succ_threshView_eq, succ_threshView_eq]
    by_cases hv : v = t
    · -- v = target: both configs have succCounts = n, both above threshold
      subst hv
      rw [succCounts_all_to_target alg c₁ v ht₁,
          succCounts_all_to_target alg c₂ v ht₂]
      have h1 : n₁ * α_den > α_num * n₁ := by
        rw [Nat.mul_comm α_num]; exact (Nat.mul_lt_mul_left hn₁).mpr hα
      have h2 : n₂ * α_den > α_num * n₂ := by
        rw [Nat.mul_comm α_num]; exact (Nat.mul_lt_mul_left hn₂).mpr hα
      simp [h1, h2]
    · -- v ≠ target: both configs have succCounts = 0
      rw [succCounts_all_to_target_other alg c₁ t v ht₁ hv,
          succCounts_all_to_target_other alg c₂ t v ht₂ hv]
      simp
  · -- No threshold crossed: identity preserves TV
    have h_none₁ := all_false_of_not_exists_true h_any
    have h_none₂ : ∀ v, c₂.threshView α_num α_den v = false := by
      intro v; rw [← htv]; exact h_none₁ v
    have hid₁ := h_id _ h_none₁
    have hid₂ := h_id _ h_none₂
    funext v
    rw [succ_threshView_eq, succ_threshView_eq,
        succCounts_of_identity alg c₁ hid₁ v,
        succCounts_of_identity alg c₂ hid₂ v]
    -- Goal: decide (c₁.counts v * ...) = decide (c₂.counts v * ...)
    -- This is exactly threshView c₁ v = threshView c₂ v
    exact congrFun htv v

/-! ### Example 1: OneThirdRule (k=2, alpha=2/3) -/

/-- The OneThirdRule is collapsing: when any threshold is crossed,
    all values map to the above-threshold value. -/
theorem otr_collapsing : isCollapsing otr_symthresh := by
  intro tv ⟨v, hv⟩
  simp only [otr_symthresh]
  by_cases h0 : tv 0 = true
  · exact ⟨0, fun _ => by simp [h0]⟩
  · have h0f : tv 0 = false := Bool.eq_false_iff.mpr h0
    have h1 : tv 1 = true := by
      have : v = 0 ∨ v = 1 := by omega
      rcases this with rfl | rfl <;> simp_all
    exact ⟨1, fun _ => by simp [h0f, h1]⟩

/-- The OneThirdRule is identity below threshold. -/
theorem otr_identity : isIdentityBelowThreshold otr_symthresh := by
  intro tv h_all v
  simp only [otr_symthresh]
  simp [h_all 0, h_all 1]

/-- **OneThirdRule is TV-deterministic** (via the collapsing lemma). -/
theorem otr_tvDeterministic : tvDeterministic otr_symthresh :=
  collapsing_identity_tvDeterministic (by omega) otr_symthresh
    otr_collapsing otr_identity

/-! ### Example 2: Majority Rule (k=2, alpha=1/2) -/

/-- The majority rule: adopt the majority value if one exists. -/
def majority_symthresh : SymThreshAlg 2 1 2 where
  update := fun v tv =>
    if tv 0 then (0 : Fin 2)
    else if tv 1 then (1 : Fin 2)
    else v

/-- The majority rule is collapsing. -/
theorem majority_collapsing : isCollapsing majority_symthresh := by
  intro tv ⟨v, hv⟩
  simp only [majority_symthresh]
  by_cases h0 : tv 0 = true
  · exact ⟨0, fun _ => by simp [h0]⟩
  · have h0f : tv 0 = false := Bool.eq_false_iff.mpr h0
    have h1 : tv 1 = true := by
      have : v = 0 ∨ v = 1 := by omega
      rcases this with rfl | rfl <;> simp_all
    exact ⟨1, fun _ => by simp [h0f, h1]⟩

/-- The majority rule is identity below threshold. -/
theorem majority_identity : isIdentityBelowThreshold majority_symthresh := by
  intro tv h_all v
  simp only [majority_symthresh]
  simp [h_all 0, h_all 1]

/-- **Majority rule is TV-deterministic** (via the collapsing lemma). -/
theorem majority_tvDeterministic : tvDeterministic majority_symthresh :=
  collapsing_identity_tvDeterministic (by omega) majority_symthresh
    majority_collapsing majority_identity

/-! ### Example 3: Absorbing Consensus / ThresholdConsensus (k=4, alpha=2/3)

    States 0,1 = value 0 (undecided, decided).
    States 2,3 = value 1 (undecided, decided).
    When value-0 states are above threshold, everyone decides on 0 (state 1).
    When value-1 states are above threshold, everyone decides on 1 (state 3).
    Otherwise, keep current state. -/

/-- The absorbing consensus algorithm (same as `tcSymThreshAlg` from
    CutoffIntegration). Defined here to avoid import dependency. -/
def absorbing_symthresh : SymThreshAlg 4 2 3 where
  update := fun s tv =>
    if tv 0 ∨ tv 1 then (1 : Fin 4)
    else if tv 2 ∨ tv 3 then (3 : Fin 4)
    else s

/-- Absorbing consensus is collapsing. -/
theorem absorbing_collapsing : isCollapsing absorbing_symthresh := by
  intro tv ⟨v, hv⟩
  simp only [absorbing_symthresh]
  by_cases h01 : tv 0 = true ∨ tv 1 = true
  · exact ⟨1, fun _ => by simp [h01]⟩
  · -- Neither tv 0 nor tv 1 is true, so tv 2 ∨ tv 3
    have h0f : tv 0 = false := by cases htv0 : tv 0 <;> simp_all
    have h1f : tv 1 = false := by cases htv1 : tv 1 <;> simp_all
    have h23 : tv 2 = true ∨ tv 3 = true := by
      have : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> simp_all
    exact ⟨3, fun _ => by simp [h0f, h1f, h23]⟩

/-- Absorbing consensus is identity below threshold. -/
theorem absorbing_identity : isIdentityBelowThreshold absorbing_symthresh := by
  intro tv h_all v
  simp only [absorbing_symthresh]
  simp [h_all 0, h_all 1, h_all 2, h_all 3]

/-- **Absorbing consensus is TV-deterministic** (via the collapsing lemma). -/
theorem absorbing_tvDeterministic : tvDeterministic absorbing_symthresh :=
  collapsing_identity_tvDeterministic (by omega) absorbing_symthresh
    absorbing_collapsing absorbing_identity

/-! ### Example 4: Direct proof for OTR (without collapsing lemma)

    For comparison, here is a direct proof that OTR is TV-deterministic,
    by unfolding definitions and case-splitting on threshold view bits.
    This demonstrates the manual proof approach; the collapsing lemma
    (`otr_tvDeterministic`) provides a cleaner proof. -/

set_option maxHeartbeats 800000 in
/-- **OneThirdRule is TV-deterministic** (direct proof by case analysis).
    Uses the same helpers as the collapsing proof but applies them manually. -/
theorem otr_tvDeterministic_direct : tvDeterministic otr_symthresh := by
  intro n₁ n₂ c₁ c₂ htv
  funext v
  rw [succ_threshView_eq, succ_threshView_eq]
  -- Extract threshold view bits
  have htv0 : c₁.threshView 2 3 0 = c₂.threshView 2 3 0 := congrFun htv 0
  have htv1 : c₁.threshView 2 3 1 = c₂.threshView 2 3 1 := congrFun htv 1
  -- Case split on whether value 0 is above threshold
  by_cases h0 : c₁.threshView 2 3 0 = true
  · -- Value 0 above threshold: all map to 0
    have h0₂ : c₂.threshView 2 3 0 = true := htv0 ▸ h0
    have hall₁ : ∀ w, otr_symthresh.update w (c₁.threshView 2 3) = 0 := by
      intro w; simp [otr_symthresh, h0]
    have hall₂ : ∀ w, otr_symthresh.update w (c₂.threshView 2 3) = 0 := by
      intro w; simp [otr_symthresh, h0₂]
    have hn₁ : n₁ > 0 := n_pos_of_thresh c₁ 0 h0
    have hn₂ : n₂ > 0 := n_pos_of_thresh c₂ 0 h0₂
    by_cases hv : v = 0
    · subst hv
      rw [succCounts_all_to_target _ _ _ hall₁, succCounts_all_to_target _ _ _ hall₂]
      simp only [decide_eq_decide]
      constructor <;> intro _ <;>
        (rw [Nat.mul_comm 2]; exact (Nat.mul_lt_mul_left ‹_ > 0›).mpr (by omega))
    · rw [succCounts_all_to_target_other _ _ _ _ hall₁ hv,
          succCounts_all_to_target_other _ _ _ _ hall₂ hv]
      simp
  · by_cases h1 : c₁.threshView 2 3 1 = true
    · -- Value 1 above threshold: all map to 1
      have h0f : c₁.threshView 2 3 0 = false := Bool.eq_false_iff.mpr h0
      have h1₂ : c₂.threshView 2 3 1 = true := htv1 ▸ h1
      have h0f₂ : c₂.threshView 2 3 0 = false := by rw [← htv0]; exact h0f
      have hall₁ : ∀ w, otr_symthresh.update w (c₁.threshView 2 3) = 1 := by
        intro w; simp [otr_symthresh, h0f, h1]
      have hall₂ : ∀ w, otr_symthresh.update w (c₂.threshView 2 3) = 1 := by
        intro w; simp [otr_symthresh, h0f₂, h1₂]
      have hn₁ : n₁ > 0 := n_pos_of_thresh c₁ 1 h1
      have hn₂ : n₂ > 0 := n_pos_of_thresh c₂ 1 h1₂
      by_cases hv : v = 1
      · subst hv
        rw [succCounts_all_to_target _ _ _ hall₁, succCounts_all_to_target _ _ _ hall₂]
        simp only [decide_eq_decide]
        constructor <;> intro _ <;>
          (rw [Nat.mul_comm 2]; exact (Nat.mul_lt_mul_left ‹_ > 0›).mpr (by omega))
      · rw [succCounts_all_to_target_other _ _ _ _ hall₁ hv,
            succCounts_all_to_target_other _ _ _ _ hall₂ hv]
        simp
    · -- No threshold: identity
      have h0f : c₁.threshView 2 3 0 = false := Bool.eq_false_iff.mpr h0
      have h1f : c₁.threshView 2 3 1 = false := Bool.eq_false_iff.mpr h1
      have h0f₂ : c₂.threshView 2 3 0 = false := by rw [← htv0]; exact h0f
      have h1f₂ : c₂.threshView 2 3 1 = false := by rw [← htv1]; exact h1f
      have hid₁ : ∀ w, otr_symthresh.update w (c₁.threshView 2 3) = w := by
        intro w; simp [otr_symthresh, h0f, h1f]
      have hid₂ : ∀ w, otr_symthresh.update w (c₂.threshView 2 3) = w := by
        intro w; simp [otr_symthresh, h0f₂, h1f₂]
      rw [succCounts_of_identity _ _ hid₁, succCounts_of_identity _ _ hid₂]
      exact congrFun htv v

end TLA.TerminationCutoff
