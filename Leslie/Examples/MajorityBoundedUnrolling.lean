import Leslie.Cutoff
import Leslie.Examples.Combinators.ConfigRoundBridge

/-! ## Majority Rule: Bounded-Unrolling Cutoff (stateless BMC)

    This file implements the bounded-unrolling cutoff theorem for the
    majority rule (threshold `> n/2`), mirroring
    `Leslie/Examples/OneThirdRuleBoundedUnrolling.lean` for OTR.

    ### Parameter differences vs. OTR

    * `SymThreshAlg 2 2 3` → `SymThreshAlg 2 1 2`
    * super-majority `counts v * 3 > 2 * n` → majority `counts v * 2 > n`
    * cutoff bound `7` → `5`
    * safety diameter bound follows the same "phase-2 locks in one step"
      structure, so the depth-2 trace check still suffices.

    The `cutoff_reliable` preconditions `α_num < α_den` and
    `2 * α_num ≥ α_den` both hold for `(1, 2)`: `1 < 2` and `2 ≥ 2`
    (the borderline case — checked that `cutoff_reliable` accepts it).
-/

open TLA

namespace Majority.BoundedUnrolling

/-- The majority-rule symmetric threshold algorithm. The update function
    is identical to OTR; only the threshold parameters differ. -/
def majority_symthresh : SymThreshAlg 2 1 2 where
  update := fun v tv =>
    if tv 0 then (0 : Fin 2)
    else if tv 1 then (1 : Fin 2)
    else v

theorem majority_cutoff_bound : cutoffBound 2 1 2 = 5 := by
  simp [cutoffBound]

/-! ### Sub-task 1: progress measure and phase classification -/

/-- Global majority predicate on a configuration. -/
def hasMajority {n : Nat} (c : Config 2 n) (v : Fin 2) : Prop :=
  c.counts v * 2 > n

/-- A config is in *phase 1* iff no value has a global majority. -/
def phase1State {n : Nat} (c : Config 2 n) : Prop :=
  ∀ v : Fin 2, ¬ hasMajority c v

/-- A config is in *phase 2* iff some value has a global majority. -/
def phase2State {n : Nat} (c : Config 2 n) : Prop :=
  ∃ v : Fin 2, hasMajority c v

/-- The progress measure. -/
def maxHolderCount {n : Nat} (c : Config 2 n) : Nat :=
  max (c.counts 0) (c.counts 1)

theorem phase1_or_phase2 {n : Nat} (c : Config 2 n) :
    phase1State c ∨ phase2State c := by
  by_cases h : ∃ v : Fin 2, c.counts v * 2 > n
  · exact Or.inr h
  · refine Or.inl ?_
    intro v hv
    exact h ⟨v, hv⟩

/-- Extensionality for `Config`. -/
theorem Config.ext {k n : Nat} {c₁ c₂ : Config k n}
    (h : c₁.counts = c₂.counts) : c₁ = c₂ := by
  cases c₁; cases c₂; cases h; rfl

/-- Case split on `Fin 2`. -/
theorem fin2_cases (v : Fin 2) : v = 0 ∨ v = 1 := by
  rcases v with ⟨i, hi⟩
  match i, hi with
  | 0, _ => exact Or.inl rfl
  | 1, _ => exact Or.inr rfl

/-! ### Sub-task 2: Observations 1, 2, 3 -/

/-- **Observation 1.** `majority_symthresh.update` adopts `v` only when
    `v` has a global majority at the current configuration. -/
theorem obs1_adoption_requires_majority {n : Nat} (c : Config 2 n)
    (w v : Fin 2)
    (h : majority_symthresh.update w (c.threshView 1 2) = v)
    (hne : majority_symthresh.update w (c.threshView 1 2) ≠ w) :
    hasMajority c v := by
  simp only [majority_symthresh] at h hne
  by_cases h0 : c.threshView 1 2 0 = true
  · simp [h0] at h hne
    subst h
    simp [Config.threshView, decide_eq_true_eq] at h0
    exact h0
  · have h0' : c.threshView 1 2 0 = false := by
      cases hv : c.threshView 1 2 0 <;> simp_all
    simp [h0'] at h hne
    by_cases h1 : c.threshView 1 2 1 = true
    · simp [h1] at h hne
      subst h
      simp [Config.threshView, decide_eq_true_eq] at h1
      exact h1
    · have h1' : c.threshView 1 2 1 = false := by
        cases hv : c.threshView 1 2 1 <;> simp_all
      simp [h1'] at hne

/-- **Observation 2 (phase 1 absorbing).** -/
theorem obs2_phase1_absorbing {n : Nat} (c : Config 2 n)
    (h : phase1State c) :
    c.succ majority_symthresh = c := by
  have htv0 : c.threshView 1 2 0 = false := by
    have := h 0
    simp [hasMajority, Config.threshView] at this ⊢
    omega
  have htv1 : c.threshView 1 2 1 = false := by
    have := h 1
    simp [hasMajority, Config.threshView] at this ⊢
    omega
  have hupd : ∀ w : Fin 2, majority_symthresh.update w (c.threshView 1 2) = w := by
    intro w
    simp only [majority_symthresh, htv0, htv1]
    simp
  apply Config.ext
  funext v
  simp only [Config.succ, succCounts]
  rw [show ((List.finRange 2).map fun w =>
        if majority_symthresh.update w (c.threshView 1 2) = v then c.counts w else 0) =
      ((List.finRange 2).map fun w => if w = v then c.counts w else 0) from
    List.map_congr_left (fun w _ => by rw [hupd w])]
  rcases fin2_cases v with rfl | rfl <;> simp [List.finRange, List.sum_cons]

/-- Helper: in phase 2, every `w` updates to the majority holder `v`. -/
private theorem phase2_all_to_v {n : Nat} (c : Config 2 n) (v : Fin 2)
    (hv : hasMajority c v) :
    ∀ w : Fin 2, majority_symthresh.update w (c.threshView 1 2) = v := by
  have htv_v : c.threshView 1 2 v = true := by
    simp [Config.threshView, decide_eq_true_eq]; exact hv
  have htv_w : ∀ w : Fin 2, w ≠ v → c.threshView 1 2 w = false := by
    intro w hne
    simp only [Config.threshView, decide_eq_false_iff_not, Nat.not_lt]
    have h_sum := c.sum_eq
    simp [List.finRange] at h_sum
    simp [hasMajority] at hv
    rcases fin2_cases v with rfl | rfl <;> rcases fin2_cases w with rfl | rfl <;>
      simp_all <;> omega
  intro w
  simp only [majority_symthresh]
  rcases fin2_cases v with rfl | rfl
  · simp [htv_v]
  · have h0 := htv_w 0 (by
      intro h; exact (by simp [Fin.ext_iff] at h : (0:Fin 2) ≠ 1) h)
    simp [h0, htv_v]

/-- In phase 2, one `Config.succ` step produces a locked configuration
    on the majority value. -/
theorem phase2_one_step_to_locked {n : Nat} (c : Config 2 n)
    (v : Fin 2) (hv : hasMajority c v) :
    (c.succ majority_symthresh).counts v = n := by
  have h_all_to_v := phase2_all_to_v c v hv
  simp only [Config.succ, succCounts]
  rw [show ((List.finRange 2).map fun w =>
        if majority_symthresh.update w (c.threshView 1 2) = v then c.counts w else 0) =
      (List.finRange 2).map c.counts from
    List.map_congr_left (fun w _ => by simp [h_all_to_v w])]
  exact c.sum_eq

/-- **Observation 3 (phase 2 absorbing + monotone).** -/
theorem obs3_phase2_absorbing_monotone {n : Nat} (c : Config 2 n)
    (v : Fin 2) (hv : hasMajority c v) :
    hasMajority (c.succ majority_symthresh) v ∧
    (c.succ majority_symthresh).counts v ≥ c.counts v := by
  have h_succ_eq_n : (c.succ majority_symthresh).counts v = n :=
    phase2_one_step_to_locked c v hv
  have hv_le : c.counts v ≤ n := by
    have := mem_le_sum (List.finRange 2) c.counts v (List.mem_finRange v)
    rw [c.sum_eq] at this; exact this
  refine ⟨?_, ?_⟩
  · -- hasMajority (succ c) v : succ counts v * 2 > n
    simp [hasMajority, h_succ_eq_n]
    -- Need n * 2 > n, i.e. n ≥ 1. From hv: c.counts v * 2 > n, so n < c.counts v * 2 ≤ 2n,
    -- which requires n ≥ 1.
    simp [hasMajority] at hv
    omega
  · rw [h_succ_eq_n]; exact hv_le

/-! ### Sub-task 3: Safety diameter bound -/

/-- Locked configurations. -/
def isLocked {n : Nat} (c : Config 2 n) : Prop :=
  ∃ v : Fin 2, c.counts v = n

/-- A locked configuration is a fixpoint of `Config.succ`. -/
theorem locked_is_fixpoint {n : Nat} (c : Config 2 n) (v : Fin 2)
    (hlock : c.counts v = n) :
    c.succ majority_symthresh = c := by
  by_cases hn : n = 0
  · apply Config.ext
    funext w
    have h_sum := c.sum_eq
    simp [List.finRange, hn] at h_sum
    have hw0 : c.counts 0 = 0 := h_sum.1
    have hw1 : c.counts 1 = 0 := h_sum.2
    have hw : c.counts w = 0 := by rcases fin2_cases w with rfl | rfl <;> assumption
    have h_succ_sum :
        ((List.finRange 2).map (c.succ majority_symthresh).counts).sum = n :=
      succCounts_sum majority_symthresh c
    simp [List.finRange, hn] at h_succ_sum
    have hsw : (c.succ majority_symthresh).counts w = 0 := by
      rcases fin2_cases w with rfl | rfl
      · exact h_succ_sum.1
      · exact h_succ_sum.2
    rw [hsw, hw]
  · have hmaj : hasMajority c v := by
      simp [hasMajority, hlock]; omega
    have h_succ_v := phase2_one_step_to_locked c v hmaj
    apply Config.ext
    funext w
    by_cases hw : w = v
    · subst hw; rw [h_succ_v, hlock]
    · have h_sum := c.sum_eq
      simp [List.finRange] at h_sum
      have hcw : c.counts w = 0 := by
        rcases fin2_cases v with rfl | rfl <;> rcases fin2_cases w with rfl | rfl <;>
          simp_all
      have h_succ_sum :
          ((List.finRange 2).map (c.succ majority_symthresh).counts).sum = n :=
        succCounts_sum majority_symthresh c
      simp [List.finRange] at h_succ_sum
      have hsw : (c.succ majority_symthresh).counts w = 0 := by
        rcases fin2_cases v with rfl | rfl <;> rcases fin2_cases w with rfl | rfl <;>
          simp_all
      rw [hsw, hcw]

/-- **Safety diameter bound.** Two `Config.succ` applications reach a fixpoint. -/
theorem safety_diameter_bound {n : Nat} (c : Config 2 n) :
    (c.succ majority_symthresh).succ majority_symthresh =
      c.succ majority_symthresh := by
  rcases phase1_or_phase2 c with hph1 | ⟨v, hv⟩
  · have hfix := obs2_phase1_absorbing c hph1
    rw [hfix]; exact hfix
  · have hlock : (c.succ majority_symthresh).counts v = n :=
      phase2_one_step_to_locked c v hv
    exact locked_is_fixpoint (c.succ majority_symthresh) v hlock

/-! ### Sub-task 4: the main theorem -/

/-- The "no two majorities" invariant — always true by pigeonhole. -/
def noTwoMajorities : ConfigInv 2 :=
  fun n c => ¬ (c.counts 0 * 2 > n ∧ c.counts 1 * 2 > n)

theorem noTwoMajorities_always (n : Nat) (c : Config 2 n) :
    noTwoMajorities n c := by
  simp only [noTwoMajorities]
  intro ⟨h0, h1⟩
  have := c.sum_eq
  simp [List.finRange] at this
  omega

theorem noTwoMajorities_threshDetermined :
    noTwoMajorities.threshDetermined 1 2 := by
  intro n₁ n₂ c₁ c₂ htv
  simp only [noTwoMajorities]
  constructor
  · intro h ⟨h0, h1⟩
    apply h
    refine ⟨?_, ?_⟩
    · have := congrFun htv 0
      simp [Config.threshView, decide_eq_decide] at this
      exact this.mpr h0
    · have := congrFun htv 1
      simp [Config.threshView, decide_eq_decide] at this
      exact this.mpr h1
  · intro h ⟨h0, h1⟩
    apply h
    refine ⟨?_, ?_⟩
    · have := congrFun htv 0
      simp [Config.threshView, decide_eq_decide] at this
      exact this.mp h0
    · have := congrFun htv 1
      simp [Config.threshView, decide_eq_decide] at this
      exact this.mp h1

/-- Config-level lock-preservation. -/
def lockPreservedInv : ConfigInv 2 :=
  fun _n c => ∀ v : Fin 2,
    hasMajority c v →
      hasMajority (c.succ majority_symthresh) v

theorem lockPreservedInv_holds : ∀ n (c : Config 2 n), lockPreservedInv n c := by
  intro n c v hv
  exact (obs3_phase2_absorbing_monotone c v hv).1

/-- Depth-2 bounded trace safety predicate. -/
def boundedTraceSafe {n : Nat} (c : Config 2 n) : Prop :=
  noTwoMajorities n c ∧
  noTwoMajorities n (c.succ majority_symthresh) ∧
  noTwoMajorities n ((c.succ majority_symthresh).succ majority_symthresh)

theorem boundedTraceSafe_holds {n : Nat} (c : Config 2 n) :
    boundedTraceSafe c :=
  ⟨noTwoMajorities_always n c,
   noTwoMajorities_always n (c.succ majority_symthresh),
   noTwoMajorities_always n ((c.succ majority_symthresh).succ majority_symthresh)⟩

/-- **Main theorem: Majority bounded-unrolling cutoff.** -/
theorem majority_bounded_unrolling_cutoff :
    (∀ n (c : Config 2 n), noTwoMajorities n c) ↔
    (∀ n ≤ 5, ∀ c : Config 2 n, boundedTraceSafe c) := by
  constructor
  · intro hall n _hle c
    exact ⟨hall n c, hall n _, hall n _⟩
  · intro hsmall
    have h_small : ∀ n, n ≤ cutoffBound 2 1 2 → ∀ c : Config 2 n,
        noTwoMajorities n c := by
      intro n hn c
      rw [majority_cutoff_bound] at hn
      exact (hsmall n hn c).1
    exact cutoff_reliable majority_symthresh (by omega) (by omega)
      noTwoMajorities noTwoMajorities_threshDetermined h_small

/-! ### Sub-task 5: executable demo at `n = 5` -/

/-- Canonical config at n = 5 with counts `(a, 5 - a)`. -/
def canonical5 (a : Nat) (hle : a ≤ 5) : Config 2 5 where
  counts := fun v => if v = 0 then a else 5 - a
  sum_eq := by
    simp [List.finRange, List.sum_cons]
    omega

/-- Representatives of the three equivalence classes modulo `v0 ↔ v1`. -/
def canonicalConfigs5 : List (Config 2 5) :=
  [canonical5 0 (by omega),
   canonical5 1 (by omega),
   canonical5 2 (by omega)]

/-- Decidable version of `noTwoMajorities`. -/
def noTwoMajoritiesB {n : Nat} (c : Config 2 n) : Bool :=
  ! (decide (c.counts 0 * 2 > n) && decide (c.counts 1 * 2 > n))

/-- Depth-2 executable trace check. -/
def traceSafeB {n : Nat} (c : Config 2 n) : Bool :=
  noTwoMajoritiesB c &&
  noTwoMajoritiesB (c.succ majority_symthresh) &&
  noTwoMajoritiesB ((c.succ majority_symthresh).succ majority_symthresh)

def verifyCanonical5 : Bool :=
  (canonicalConfigs5.map traceSafeB).all id

/-- **Executable certificate.** -/
theorem verifyCanonical5_ok : verifyCanonical5 = true := by
  native_decide

#eval verifyCanonical5

/-! ### Bonus: RoundState-level lifting via the ConfigRoundBridge -/

/-- Majority rule packaged as a `RoundSymThreshAlg` (ready for
    `RoundState`-level use via the Config↔Round bridge). -/
def majorityRsta : TLA.ConfigRoundBridge.RoundSymThreshAlg 2 1 2 :=
  { sta := majority_symthresh }

/-- RoundState-level `noTwoMajorities`: trivially lifted from the
    Config-level tautology via the bridge's `RoundStateInv`. -/
theorem majority_noTwoMajorities_rs (n : Nat)
    (s : RoundState (Fin n) (Fin 2)) :
    TLA.ConfigRoundBridge.RoundStateInv noTwoMajorities s := by
  unfold TLA.ConfigRoundBridge.RoundStateInv
  exact noTwoMajorities_always n (TLA.ConfigRoundBridge.stateConfig s)

end Majority.BoundedUnrolling
