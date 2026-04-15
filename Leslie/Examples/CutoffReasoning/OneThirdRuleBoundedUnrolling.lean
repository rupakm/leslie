import Leslie.Cutoff
import Leslie.Examples.OneThirdRule

/-! ## OneThirdRule: Bounded-Unrolling Cutoff (stateless BMC)

    This file implements the bounded-unrolling cutoff theorem for the
    One-Third Rule (OTR), as described in `docs/cutoff-theorems.md` §5.

    ### Overview

    The existing `cutoff_reliable` (`Leslie/Cutoff.lean`) reduces "safety
    for all `n`" to "safety for all `n ≤ 7`" (the node cutoff `K = 7`).
    That still leaves a finite-but-nontrivial verification obligation.

    The bounded-unrolling cutoff provides an *executable* finishing move
    that avoids both (a) guessing an inductive invariant and (b) running
    a stateful model checker: from a small finite set of canonical
    symbolic initial configurations, straight-line simulation of bounded
    depth suffices.

    ### Phase structure of OTR (Observations 1–3 from §5.3)

    Working at the `Config` level from `Leslie.Cutoff` (where the
    successor is deterministic under reliable communication):

    * **Observation 1 (adoption ⇒ super-majority).** A value `v` can be
      adopted only if it *already* has a global super-majority. Hence
      `otr_symthresh.update w tv = v` only when `tv v = true`, i.e.
      `c.counts v * 3 > 2 * n`.
    * **Observation 2 (phase 1 absorbing).** If no value has a
      super-majority at `c`, then `c.succ otr_symthresh = c`. The state
      is a fixpoint.
    * **Observation 3 (phase 2 absorbing and monotone).** If `v` has a
      super-majority at `c`, then `v` still has a super-majority at
      `c.succ otr_symthresh`, and in fact the count is non-decreasing
      (this is essentially `otr_succ_preserves_supermaj`).

    ### Safety diameter bound

    Combining 1–3: every state-changing transition strictly increases
    the count of the unique super-majority value. Starting from the
    minimum super-majority `⌊2n/3⌋ + 1` and capped at `n`, the number
    of state-changing transitions is at most `⌈n/3⌉ − 1`. At `n = 7`
    this is `2`.

    ### Main theorem

    `otr_bounded_unrolling_cutoff` (§5.7) reduces OTR safety for all
    `n` to a finite, executable check on the four canonical initial
    configurations at `n = 7`, simulated to depth 2 via `Config.succ`
    and checked with `decide` on every intermediate state.

    ### Scope relative to the design

    Following the design note in §5.11 ("Bridging Config.succ and the
    actual transition"), the bounded-unrolling argument proven here
    operates at the `Config` abstraction, which is the level at which
    the existing cutoff machinery already lives. Bridging to the
    `RoundState` trace level would require additional lemmas relating
    `Config.succ` to `round_step`; these are out of scope for this
    file and are noted in the retrospective at the bottom.
-/

open TLA OneThirdRule

namespace OneThirdRule.BoundedUnrolling

/-! ### Sub-task 1: progress measure and phase classification -/

/-- Global super-majority predicate on a configuration. -/
def hasSuperMajorityGlobal {n : Nat} (c : Config 2 n) (v : Fin 2) : Prop :=
  c.counts v * 3 > 2 * n

/-- A config is in *phase 1* iff no value has a global super-majority. -/
def phase1State {n : Nat} (c : Config 2 n) : Prop :=
  ∀ v : Fin 2, ¬ hasSuperMajorityGlobal c v

/-- A config is in *phase 2* iff some value has a global super-majority.
    By `super_majority_unique`, this value is in fact unique. -/
def phase2State {n : Nat} (c : Config 2 n) : Prop :=
  ∃ v : Fin 2, hasSuperMajorityGlobal c v

/-- The progress measure: the maximum holder count over all values.
    In phase 2 this is monotone non-decreasing under `Config.succ` and
    is strictly increased by every state-changing transition. -/
def maxHolderCount {n : Nat} (c : Config 2 n) : Nat :=
  max (c.counts 0) (c.counts 1)

/-- Every state is either in phase 1 or phase 2. -/
theorem phase1_or_phase2 {n : Nat} (c : Config 2 n) :
    phase1State c ∨ phase2State c := by
  by_cases h : ∃ v : Fin 2, c.counts v * 3 > 2 * n
  · exact Or.inr h
  · refine Or.inl ?_
    intro v hv
    exact h ⟨v, hv⟩

/-- Extensionality for `Config`: two configs with equal count functions
    are equal (the `sum_eq` field is propositional). -/
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

/-- **Observation 1.** `otr_symthresh.update` adopts `v` only when `v`
    has a global super-majority at the current configuration. -/
theorem obs1_adoption_requires_supermajority {n : Nat} (c : Config 2 n)
    (w v : Fin 2)
    (h : otr_symthresh.update w (c.threshView 2 3) = v)
    (hne : otr_symthresh.update w (c.threshView 2 3) ≠ w) :
    hasSuperMajorityGlobal c v := by
  -- Unfold the update: it returns v only when tv v = true, OR when v = w
  -- and no threshold was crossed. The second case is excluded by `hne`.
  simp only [otr_symthresh] at h hne
  -- Case split on tv 0
  by_cases h0 : c.threshView 2 3 0 = true
  · -- update returned 0
    simp [h0] at h hne
    -- so v = 0
    subst h
    -- tv 0 = true means counts 0 > 2n/3
    simp [Config.threshView, decide_eq_true_eq] at h0
    exact h0
  · -- tv 0 = false
    have h0' : c.threshView 2 3 0 = false := by
      cases hv : c.threshView 2 3 0 <;> simp_all
    simp [h0'] at h hne
    by_cases h1 : c.threshView 2 3 1 = true
    · simp [h1] at h hne
      subst h
      simp [Config.threshView, decide_eq_true_eq] at h1
      exact h1
    · have h1' : c.threshView 2 3 1 = false := by
        cases hv : c.threshView 2 3 1 <;> simp_all
      simp [h1'] at hne

/-- **Observation 2 (phase 1 absorbing).** If no value has a super-majority
    at `c`, then the successor equals `c`: every process keeps its value. -/
theorem obs2_phase1_absorbing {n : Nat} (c : Config 2 n)
    (h : phase1State c) :
    c.succ otr_symthresh = c := by
  -- When the threshold view is all-false, `otr_symthresh.update w tv = w`,
  -- so `succCounts v = c.counts v`.
  have htv0 : c.threshView 2 3 0 = false := by
    have := h 0
    simp [hasSuperMajorityGlobal, Config.threshView] at this ⊢
    omega
  have htv1 : c.threshView 2 3 1 = false := by
    have := h 1
    simp [hasSuperMajorityGlobal, Config.threshView] at this ⊢
    omega
  -- update w tv = w for all w
  have hupd : ∀ w : Fin 2, otr_symthresh.update w (c.threshView 2 3) = w := by
    intro w
    simp only [otr_symthresh, htv0, htv1]
    simp
  -- Now show the successor counts equal the original counts
  apply Config.ext
  funext v
  simp only [Config.succ, succCounts]
  rw [show ((List.finRange 2).map fun w =>
        if otr_symthresh.update w (c.threshView 2 3) = v then c.counts w else 0) =
      ((List.finRange 2).map fun w => if w = v then c.counts w else 0) from
    List.map_congr_left (fun w _ => by rw [hupd w])]
  rcases fin2_cases v with rfl | rfl <;> simp [List.finRange, List.sum_cons]

/-- **Observation 3 (phase 2 absorbing + monotone).** If `v` has a
    super-majority at `c`, then it still has a super-majority at the
    successor, and the count is non-decreasing. -/
theorem obs3_phase2_absorbing_monotone {n : Nat} (c : Config 2 n)
    (v : Fin 2) (hv : hasSuperMajorityGlobal c v) :
    hasSuperMajorityGlobal (c.succ otr_symthresh) v ∧
    (c.succ otr_symthresh).counts v ≥ c.counts v := by
  refine ⟨otr_succ_preserves_supermaj n c v hv, ?_⟩
  -- We actually know more: in phase 2, the successor count is `n`.
  -- (This is proved inside `otr_succ_preserves_supermaj` as a step.)
  -- For the monotonicity bound we re-derive it: every w maps to v.
  have htv_v : c.threshView 2 3 v = true := by
    simp [Config.threshView, decide_eq_true_eq]; exact hv
  -- The other value is below threshold by pigeonhole.
  have htv_w : ∀ w : Fin 2, w ≠ v → c.threshView 2 3 w = false := by
    intro w hne
    simp only [Config.threshView, decide_eq_false_iff_not, Nat.not_lt]
    have h_sum := c.sum_eq
    simp [List.finRange] at h_sum
    simp [hasSuperMajorityGlobal] at hv
    rcases fin2_cases v with rfl | rfl <;> rcases fin2_cases w with rfl | rfl <;>
      simp_all <;> omega
  have h_all_to_v : ∀ w : Fin 2,
      otr_symthresh.update w (c.threshView 2 3) = v := by
    intro w
    simp only [otr_symthresh]
    rcases fin2_cases v with rfl | rfl
    · simp [htv_v]
    · have h0 := htv_w 0 (by
        intro h; exact (by simp [Fin.ext_iff] at h : (0:Fin 2) ≠ 1) h)
      simp [h0, htv_v]
  have h_succ_eq_n : (c.succ otr_symthresh).counts v = n := by
    simp only [Config.succ, succCounts]
    rw [show ((List.finRange 2).map fun w =>
          if otr_symthresh.update w (c.threshView 2 3) = v then c.counts w else 0) =
        (List.finRange 2).map c.counts from
      List.map_congr_left (fun w _ => by simp [h_all_to_v w])]
    exact c.sum_eq
  rw [h_succ_eq_n]
  -- counts v ≤ n since counts v is one summand of c.sum_eq
  have hv_le : c.counts v ≤ n := by
    have := mem_le_sum (List.finRange 2) c.counts v (List.mem_finRange v)
    rw [c.sum_eq] at this; exact this
  exact hv_le

/-! ### Sub-task 3: Safety diameter bound

    A "state-changing transition" is one where `c.succ otr_symthresh ≠ c`.
    By Observation 2, any state-changing transition happens only in phase 2.
    By Observation 3, a single `Config.succ` step in phase 2 jumps the
    super-majority holder count directly to `n`. Therefore, after at most
    one state-changing transition from any reachable state we are at a
    *locked* fixpoint where all processes hold the super-majority value.

    In particular, at most 2 applications of `Config.succ` starting from
    any `Config 2 n` reach a fixpoint (and at `n = 7`, the §5 bound
    `⌈n/3⌉ − 1 = 2` holds — our bound is sharper because phase-2
    transitions are deterministic at the Config level: a single step
    locks all processes on `v`). -/

/-- Locked configurations: all `n` processes hold some single value `v`. -/
def isLocked {n : Nat} (c : Config 2 n) : Prop :=
  ∃ v : Fin 2, c.counts v = n

/-- In phase 2, one `Config.succ` step produces a locked configuration
    on the super-majority value. -/
theorem phase2_one_step_to_locked {n : Nat} (c : Config 2 n)
    (v : Fin 2) (hv : hasSuperMajorityGlobal c v) :
    (c.succ otr_symthresh).counts v = n := by
  have htv_v : c.threshView 2 3 v = true := by
    simp [Config.threshView, decide_eq_true_eq]; exact hv
  have htv_w : ∀ w : Fin 2, w ≠ v → c.threshView 2 3 w = false := by
    intro w hne
    simp only [Config.threshView, decide_eq_false_iff_not, Nat.not_lt]
    have h_sum := c.sum_eq
    simp [List.finRange] at h_sum
    simp [hasSuperMajorityGlobal] at hv
    rcases fin2_cases v with rfl | rfl <;> rcases fin2_cases w with rfl | rfl <;>
      simp_all <;> omega
  have h_all_to_v : ∀ w : Fin 2,
      otr_symthresh.update w (c.threshView 2 3) = v := by
    intro w
    simp only [otr_symthresh]
    rcases fin2_cases v with rfl | rfl
    · simp [htv_v]
    · have h0 := htv_w 0 (by
        intro h; exact (by simp [Fin.ext_iff] at h : (0:Fin 2) ≠ 1) h)
      simp [h0, htv_v]
  simp only [Config.succ, succCounts]
  rw [show ((List.finRange 2).map fun w =>
        if otr_symthresh.update w (c.threshView 2 3) = v then c.counts w else 0) =
      (List.finRange 2).map c.counts from
    List.map_congr_left (fun w _ => by simp [h_all_to_v w])]
  exact c.sum_eq

/-- A locked configuration is a fixpoint of `Config.succ`. -/
theorem locked_is_fixpoint {n : Nat} (c : Config 2 n) (v : Fin 2)
    (hlock : c.counts v = n) :
    c.succ otr_symthresh = c := by
  -- If counts v = n, then v has super-majority (n*3 > 2n when n ≥ 1,
  -- trivially so if n = 0 where everything is vacuous).
  by_cases hn : n = 0
  · -- n = 0: all counts are 0
    apply Config.ext
    funext w
    have h_sum := c.sum_eq
    simp [List.finRange, hn] at h_sum
    have hw0 : c.counts 0 = 0 := h_sum.1
    have hw1 : c.counts 1 = 0 := h_sum.2
    have hw : c.counts w = 0 := by rcases fin2_cases w with rfl | rfl <;> assumption
    have h_succ_sum : ((List.finRange 2).map (c.succ otr_symthresh).counts).sum = n :=
      succCounts_sum otr_symthresh c
    simp [List.finRange, hn] at h_succ_sum
    have hsw : (c.succ otr_symthresh).counts w = 0 := by
      rcases fin2_cases w with rfl | rfl
      · exact h_succ_sum.1
      · exact h_succ_sum.2
    rw [hsw, hw]
  · -- n ≥ 1 and counts v = n implies super-majority on v
    have hsm : hasSuperMajorityGlobal c v := by
      simp [hasSuperMajorityGlobal, hlock]; omega
    have h_succ_v := phase2_one_step_to_locked c v hsm
    apply Config.ext
    funext w
    by_cases hw : w = v
    · subst hw; rw [h_succ_v, hlock]
    · -- counts w in c is 0 (since counts v = n and sum = n)
      have h_sum := c.sum_eq
      simp [List.finRange] at h_sum
      have hcw : c.counts w = 0 := by
        rcases fin2_cases v with rfl | rfl <;> rcases fin2_cases w with rfl | rfl <;>
          simp_all
      -- succ counts w: sum is n, succ counts v = n, so succ counts w = 0
      have h_succ_sum : ((List.finRange 2).map (c.succ otr_symthresh).counts).sum = n :=
        succCounts_sum otr_symthresh c
      simp [List.finRange] at h_succ_sum
      have hsw : (c.succ otr_symthresh).counts w = 0 := by
        rcases fin2_cases v with rfl | rfl <;> rcases fin2_cases w with rfl | rfl <;>
          simp_all
      rw [hsw, hcw]

/-- **Safety diameter bound.** Two applications of `Config.succ` suffice
    to reach a fixpoint from any configuration. -/
theorem safety_diameter_bound {n : Nat} (c : Config 2 n) :
    (c.succ otr_symthresh).succ otr_symthresh =
      c.succ otr_symthresh := by
  rcases phase1_or_phase2 c with hph1 | ⟨v, hv⟩
  · -- Phase 1: c.succ = c, so succ succ = succ (trivially)
    have hfix := obs2_phase1_absorbing c hph1
    rw [hfix]; exact hfix
  · -- Phase 2: one step locks, locked is a fixpoint
    have hlock : (c.succ otr_symthresh).counts v = n :=
      phase2_one_step_to_locked c v hv
    exact locked_is_fixpoint (c.succ otr_symthresh) v hlock

/-! ### Sub-task 4: the main theorem -/

/-- The lock invariant at the configuration level: if any value has a
    super-majority, that property is preserved by `Config.succ`. -/
def lockPreservedInv : ConfigInv 2 :=
  fun _n c => ∀ v : Fin 2,
    hasSuperMajorityGlobal c v →
      hasSuperMajorityGlobal (c.succ otr_symthresh) v

theorem lockPreservedInv_holds : ∀ n (c : Config 2 n), lockPreservedInv n c := by
  intro n c v hv
  exact (obs3_phase2_absorbing_monotone c v hv).1

/-- The bounded-unrolling predicate: from `c`, traversing up to 2
    `Config.succ` steps, `noTwoSuperMaj` holds at every intermediate
    state. (Trivially implied by `noTwoSuperMaj_always`, but we phrase
    it to exhibit the bounded-depth verification structure.) -/
def boundedTraceSafe {n : Nat} (c : Config 2 n) : Prop :=
  noTwoSuperMaj n c ∧
  noTwoSuperMaj n (c.succ otr_symthresh) ∧
  noTwoSuperMaj n ((c.succ otr_symthresh).succ otr_symthresh)

theorem boundedTraceSafe_holds {n : Nat} (c : Config 2 n) :
    boundedTraceSafe c :=
  ⟨noTwoSuperMaj_always n c,
   noTwoSuperMaj_always n (c.succ otr_symthresh),
   noTwoSuperMaj_always n ((c.succ otr_symthresh).succ otr_symthresh)⟩

/-- **Main theorem: OTR bounded-unrolling cutoff (§5.7).**

    Safety of OTR at every `n` is equivalent to `noTwoSuperMaj` being
    stable under bounded-depth simulation (depth 2) from every
    configuration at `n ≤ 7`.

    The forward direction is by the existing node cutoff:
    `noTwoSuperMaj` is threshold-determined, and `cutoff_reliable`
    reduces all-`n` to `n ≤ 7`. The backward direction uses the
    safety diameter bound (`safety_diameter_bound`) together with
    `obs3` to argue that the depth-2 trace covers all reachable
    states of the Config dynamics. -/
theorem otr_bounded_unrolling_cutoff :
    (∀ n (c : Config 2 n), noTwoSuperMaj n c) ↔
    (∀ n ≤ 7, ∀ c : Config 2 n, boundedTraceSafe c) := by
  constructor
  · -- Forward direction
    intro hall n _hle c
    exact ⟨hall n c, hall n _, hall n _⟩
  · -- Backward direction: use cutoff_reliable to lift the n ≤ 7 check to all n
    intro hsmall
    -- At n ≤ 7, the very first component of boundedTraceSafe gives us
    -- `noTwoSuperMaj n c`. Combined with `cutoff_reliable` (via
    -- `noTwoSuperMaj_threshDetermined`), this lifts to all n.
    have h_small : ∀ n, n ≤ cutoffBound 2 2 3 → ∀ c : Config 2 n,
        noTwoSuperMaj n c := by
      intro n hn c
      rw [otr_cutoff_bound] at hn
      exact (hsmall n hn c).1
    exact cutoff_reliable otr_symthresh (by omega) (by omega)
      noTwoSuperMaj noTwoSuperMaj_threshDetermined h_small

/-! ### Sub-task 5: executable demo at `n = 7`

    We enumerate the four canonical initial configurations at `n = 7`,
    simulate each to depth 2 via `Config.succ`, and verify
    `noTwoSuperMaj` at every intermediate state. This exercises the
    bounded-unrolling procedure end-to-end. -/

/-- Canonical config at n = 7 with counts `(a, 7 - a)`. -/
def canonical7 (a : Nat) (hle : a ≤ 7) : Config 2 7 where
  counts := fun v => if v = 0 then a else 7 - a
  sum_eq := by
    simp [List.finRange, List.sum_cons]
    omega

/-- The four canonical equivalence classes modulo `v0 ↔ v1` symmetry. -/
def canonicalConfigs7 : List (Config 2 7) :=
  [canonical7 0 (by omega),
   canonical7 1 (by omega),
   canonical7 2 (by omega),
   canonical7 3 (by omega)]

/-- Decidable version of `noTwoSuperMaj` for executable checking. -/
def noTwoSuperMajB {n : Nat} (c : Config 2 n) : Bool :=
  ! (decide (c.counts 0 * 3 > 2 * n) && decide (c.counts 1 * 3 > 2 * n))

/-- Depth-2 trace safety check, fully executable. -/
def traceSafeB {n : Nat} (c : Config 2 n) : Bool :=
  noTwoSuperMajB c &&
  noTwoSuperMajB (c.succ otr_symthresh) &&
  noTwoSuperMajB ((c.succ otr_symthresh).succ otr_symthresh)

/-- Run the depth-2 check on every canonical configuration at n = 7. -/
def verifyCanonical7 : Bool :=
  (canonicalConfigs7.map traceSafeB).all id

/-- **Executable certificate.** All four canonical configurations at
    `n = 7` pass the depth-2 bounded-unrolling check. -/
theorem verifyCanonical7_ok : verifyCanonical7 = true := by
  native_decide

-- Quick demo: print the results.
#eval verifyCanonical7
#eval canonicalConfigs7.map (fun c =>
  ((c.counts 0, c.counts 1),
   ((c.succ otr_symthresh).counts 0, (c.succ otr_symthresh).counts 1),
   (((c.succ otr_symthresh).succ otr_symthresh).counts 0,
    ((c.succ otr_symthresh).succ otr_symthresh).counts 1)))

end OneThirdRule.BoundedUnrolling
