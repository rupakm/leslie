import Leslie.Cutoff
import Leslie.Examples.CutoffReasoning.ConfigRoundBridge

/-! ## Phase-Absorbing Threshold Protocols (abstract framework)

    Abstract framework capturing the common structure of OTR and majority
    rule: a binary-valued symmetric threshold protocol whose update is
    "absorbing" — processes move toward the threshold-crossing value, and
    no backtracking occurs.

    Both `Leslie/Examples/OneThirdRuleBoundedUnrolling.lean` and
    `Leslie/Examples/MajorityBoundedUnrolling.lean` use literally the same
    update function `fun v tv => if tv 0 then 0 else if tv 1 then 1 else v`,
    differing only in the threshold parameters `α_num/α_den`. This file
    factors out that shared structure.

    ### Concrete instances

    - `otr_symthresh` from `Leslie/Cutoff.lean` ≡ `absorbingBinary 2 3`
    - `majority_symthresh` from `MajorityBoundedUnrolling.lean` ≡
      `absorbingBinary 1 2`

    Both are derivable as corollaries of the main cutoff theorem here,
    though we leave the existing files alone for backward compatibility.

    ### What you get for a new phase-absorbing binary protocol

    Given any `ValidThreshold α_num α_den` (i.e. `α_num < α_den` and
    `2 * α_num ≥ α_den`):

    - The phase structure (Obs 1, 2, 3) holds automatically
    - The safety diameter is `≤ 2` (two `Config.succ` steps reach fixpoint)
    - The `noTwoAtThreshold` invariant is threshold-determined
    - The main cutoff theorem reduces safety-for-all-n to a bounded
      depth-2 trace check at each `n ≤ cutoffBound 2 α_num α_den`
    - Lifting to `RoundState` level via `ConfigRoundBridge` works
      uniformly via `config_inv_preservation_lifts`
-/

open TLA

namespace TLA.PhaseAbsorbing

/-! ### The shared update function

    Both OTR and majority (and any absorbing binary threshold protocol)
    use this update: if `tv 0` is true, map to `0`; else if `tv 1`, map
    to `1`; else keep the current value. -/

/-- The absorbing binary update used by all phase-absorbing threshold
    protocols over `Fin 2`. -/
def binaryAbsorbingUpdate : Fin 2 → ThreshView 2 → Fin 2 :=
  fun v tv => if tv 0 then 0 else if tv 1 then 1 else v

/-- A binary absorbing threshold algorithm parameterized by the
    threshold fraction `α_num/α_den`. -/
def absorbingBinary (α_num α_den : Nat) : SymThreshAlg 2 α_num α_den where
  update := binaryAbsorbingUpdate

/-! ### Validity conditions

    For the phase-absorbing framework to apply, the threshold must be
    at least `1/2` (so at most one value can cross) and strictly less
    than `1` (otherwise the "no threshold crossed" case never fires). -/

/-- Valid threshold parameters for a phase-absorbing protocol:
    `α_num/α_den` satisfies `1/2 ≤ α_num/α_den < 1`. -/
structure ValidThreshold (α_num α_den : Nat) : Prop where
  positive_denom : 0 < α_den
  lt_one         : α_num < α_den
  at_least_half  : 2 * α_num ≥ α_den

/-- The validity conditions correspond exactly to `cutoff_reliable`'s
    side conditions. -/
theorem cutoff_reliable_conds {α_num α_den : Nat}
    (h : ValidThreshold α_num α_den) :
    α_num < α_den ∧ 2 * α_num ≥ α_den :=
  ⟨h.lt_one, h.at_least_half⟩

/-! ### Threshold predicate and phase classification -/

variable {α_num α_den : Nat}

/-- `hasAtThreshold v c` iff `v` has count exceeding the threshold `α_num/α_den`. -/
def hasAtThreshold (α_num α_den : Nat) {n : Nat} (c : Config 2 n) (v : Fin 2) : Prop :=
  c.counts v * α_den > α_num * n

/-- Phase 1: no value is at threshold. -/
def phase1State (α_num α_den : Nat) {n : Nat} (c : Config 2 n) : Prop :=
  ∀ v : Fin 2, ¬ hasAtThreshold α_num α_den c v

/-- Phase 2: some value is at threshold. -/
def phase2State (α_num α_den : Nat) {n : Nat} (c : Config 2 n) : Prop :=
  ∃ v : Fin 2, hasAtThreshold α_num α_den c v

theorem phase1_or_phase2 (α_num α_den : Nat) {n : Nat} (c : Config 2 n) :
    phase1State α_num α_den c ∨ phase2State α_num α_den c := by
  by_cases h : ∃ v : Fin 2, c.counts v * α_den > α_num * n
  · exact Or.inr h
  · exact Or.inl (fun v hv => h ⟨v, hv⟩)

/-! ### Fin 2 utilities -/

/-- Case split on `Fin 2`. -/
theorem fin2_cases (v : Fin 2) : v = 0 ∨ v = 1 := by
  rcases v with ⟨i, hi⟩
  match i, hi with
  | 0, _ => exact Or.inl rfl
  | 1, _ => exact Or.inr rfl

/-- Extensionality for `Config`. -/
theorem Config.ext {k n : Nat} {c₁ c₂ : Config k n}
    (h : c₁.counts = c₂.counts) : c₁ = c₂ := by
  cases c₁; cases c₂; cases h; rfl

/-! ### Uniqueness of the at-threshold value -/

/-- Given valid threshold parameters, at most one value can be at threshold
    simultaneously. Pigeonhole: if both values had count > half, their sum
    would exceed `n`, but they partition `n`. -/
theorem at_threshold_unique {α_num α_den : Nat}
    (h_valid : ValidThreshold α_num α_den) {n : Nat} (c : Config 2 n)
    (v w : Fin 2) (hne : v ≠ w)
    (hv : hasAtThreshold α_num α_den c v)
    (hw : hasAtThreshold α_num α_den c w) : False := by
  have h_sum := c.sum_eq
  simp [List.finRange, List.sum_cons] at h_sum
  have h_half := h_valid.at_least_half
  -- Reduce to (counts 0, counts 1) case via Fin 2 enumeration
  have hboth : c.counts 0 * α_den > α_num * n ∧ c.counts 1 * α_den > α_num * n := by
    rcases fin2_cases v with rfl | rfl
    · rcases fin2_cases w with rfl | rfl
      · exact absurd rfl hne
      · exact ⟨hv, hw⟩
    · rcases fin2_cases w with rfl | rfl
      · exact ⟨hw, hv⟩
      · exact absurd rfl hne
  obtain ⟨h0, h1⟩ := hboth
  -- Step 1: add h0 and h1
  have hsum_lt : c.counts 0 * α_den + c.counts 1 * α_den > α_num * n + α_num * n :=
    Nat.add_lt_add h0 h1
  -- Step 2: LHS is (counts 0 + counts 1) * α_den (distributivity)
  have hdist : (c.counts 0 + c.counts 1) * α_den =
               c.counts 0 * α_den + c.counts 1 * α_den := Nat.add_mul _ _ _
  have h2 : (c.counts 0 + c.counts 1) * α_den > α_num * n + α_num * n := by
    rw [hdist]; exact hsum_lt
  -- Step 3: substitute counts 0 + counts 1 = n
  rw [h_sum] at h2
  -- Step 4: 2 * α_num * n = α_num * n + α_num * n
  have htwo : 2 * α_num * n = α_num * n + α_num * n := by
    rw [Nat.two_mul, Nat.add_mul]
  have h3 : n * α_den > 2 * α_num * n := by rw [htwo]; exact h2
  -- Step 5: h_half implies 2 * α_num * n ≥ α_den * n = n * α_den
  have h_ge : 2 * α_num * n ≥ α_den * n := Nat.mul_le_mul_right n h_half
  have h_comm : α_den * n = n * α_den := Nat.mul_comm α_den n
  -- Step 6: chain the inequalities to contradiction
  rw [h_comm] at h_ge
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h3 h_ge)

/-! ### Observations 1, 2, 3 -/

/-- **Observation 1.** `binaryAbsorbingUpdate` adopts `v` only when `v`
    is at threshold, unless `v = w` (the self-keeping case). -/
theorem obs1_adoption_requires_threshold
    {α_num α_den : Nat} (h_valid : ValidThreshold α_num α_den)
    {n : Nat} (c : Config 2 n) (w v : Fin 2)
    (h : binaryAbsorbingUpdate w (c.threshView α_num α_den) = v)
    (hne : binaryAbsorbingUpdate w (c.threshView α_num α_den) ≠ w) :
    hasAtThreshold α_num α_den c v := by
  simp only [binaryAbsorbingUpdate] at h hne
  by_cases h0 : c.threshView α_num α_den 0 = true
  · simp [h0] at h hne
    subst h
    simp only [Config.threshView, decide_eq_true_eq] at h0
    exact h0
  · have h0' : c.threshView α_num α_den 0 = false := by
      cases hv : c.threshView α_num α_den 0 <;> simp_all
    simp [h0'] at h hne
    by_cases h1 : c.threshView α_num α_den 1 = true
    · simp [h1] at h hne
      subst h
      simp only [Config.threshView, decide_eq_true_eq] at h1
      exact h1
    · have h1' : c.threshView α_num α_den 1 = false := by
        cases hv : c.threshView α_num α_den 1 <;> simp_all
      simp [h1'] at hne

/-- **Observation 2 (phase 1 absorbing).** In phase 1, `Config.succ` is
    the identity. -/
theorem obs2_phase1_absorbing
    {α_num α_den : Nat} {n : Nat} (c : Config 2 n)
    (h : phase1State α_num α_den c) :
    c.succ (absorbingBinary α_num α_den) = c := by
  have htv0 : c.threshView α_num α_den 0 = false := by
    have := h 0
    simp [hasAtThreshold, Config.threshView] at this ⊢
    omega
  have htv1 : c.threshView α_num α_den 1 = false := by
    have := h 1
    simp [hasAtThreshold, Config.threshView] at this ⊢
    omega
  have hupd : ∀ w : Fin 2,
      (absorbingBinary α_num α_den).update w (c.threshView α_num α_den) = w := by
    intro w
    simp only [absorbingBinary, binaryAbsorbingUpdate, htv0, htv1]
    simp
  apply Config.ext
  funext v
  simp only [Config.succ, succCounts]
  rw [show ((List.finRange 2).map fun w =>
        if (absorbingBinary α_num α_den).update w (c.threshView α_num α_den) = v then
          c.counts w else 0) =
      ((List.finRange 2).map fun w => if w = v then c.counts w else 0) from
    List.map_congr_left (fun w _ => by rw [hupd w])]
  rcases fin2_cases v with rfl | rfl <;> simp [List.finRange, List.sum_cons]

/-! ### Phase 2 locks in one step -/

/-- In phase 2 with at-threshold value `v`, `Config.succ` puts all `n`
    processes on `v` (given valid threshold parameters). -/
theorem phase2_one_step_to_locked
    {α_num α_den : Nat} (h_valid : ValidThreshold α_num α_den)
    {n : Nat} (c : Config 2 n) (v : Fin 2)
    (hv : hasAtThreshold α_num α_den c v) :
    (c.succ (absorbingBinary α_num α_den)).counts v = n := by
  have htv_v : c.threshView α_num α_den v = true := by
    simp [Config.threshView, decide_eq_true_eq]; exact hv
  -- Every w ≠ v has threshold false (otherwise at_threshold_unique)
  have htv_w : ∀ w : Fin 2, w ≠ v → c.threshView α_num α_den w = false := by
    intro w hne
    by_contra h
    have hwt : c.threshView α_num α_den w = true := by
      cases hv : c.threshView α_num α_den w <;> simp_all
    simp [Config.threshView, decide_eq_true_eq] at hwt
    exact at_threshold_unique h_valid c w v hne hwt hv
  -- All pre-states map to v under the update
  have h_all_to_v : ∀ w : Fin 2,
      (absorbingBinary α_num α_den).update w (c.threshView α_num α_den) = v := by
    intro w
    simp only [absorbingBinary, binaryAbsorbingUpdate]
    rcases fin2_cases v with rfl | rfl
    · simp [htv_v]
    · have h0 := htv_w 0 (by
        intro h; exact (by simp [Fin.ext_iff] at h : (0:Fin 2) ≠ 1) h)
      simp [h0, htv_v]
  -- Successor count at v = sum of all pre-state counts = n
  simp only [Config.succ, succCounts]
  rw [show ((List.finRange 2).map fun w =>
        if (absorbingBinary α_num α_den).update w (c.threshView α_num α_den) = v then
          c.counts w else 0) =
      (List.finRange 2).map c.counts from
    List.map_congr_left (fun w _ => by simp [h_all_to_v w])]
  exact c.sum_eq

/-- **Observation 3 (phase 2 absorbing and monotone).** The at-threshold
    property is preserved by `Config.succ`, and the count is monotone
    non-decreasing (in fact it jumps to `n`). -/
theorem obs3_phase2_absorbing_monotone
    {α_num α_den : Nat} (h_valid : ValidThreshold α_num α_den)
    {n : Nat} (c : Config 2 n) (v : Fin 2)
    (hv : hasAtThreshold α_num α_den c v) :
    hasAtThreshold α_num α_den (c.succ (absorbingBinary α_num α_den)) v ∧
    (c.succ (absorbingBinary α_num α_den)).counts v ≥ c.counts v := by
  have h_succ_v : (c.succ (absorbingBinary α_num α_den)).counts v = n :=
    phase2_one_step_to_locked h_valid c v hv
  refine ⟨?_, ?_⟩
  · simp only [hasAtThreshold, h_succ_v]
    -- Direct argument: c.counts v ≤ n, so c.counts v * α_den ≤ n * α_den.
    -- Combined with hv : c.counts v * α_den > α_num * n, get n * α_den > α_num * n.
    have hc_le : c.counts v ≤ n := by
      have := mem_le_sum (List.finRange 2) c.counts v (List.mem_finRange v)
      rw [c.sum_eq] at this; exact this
    have hmono : c.counts v * α_den ≤ n * α_den :=
      Nat.mul_le_mul_right α_den hc_le
    simp only [hasAtThreshold] at hv
    exact Nat.lt_of_lt_of_le hv hmono
  · rw [h_succ_v]
    have hv_le : c.counts v ≤ n := by
      have := mem_le_sum (List.finRange 2) c.counts v (List.mem_finRange v)
      rw [c.sum_eq] at this; exact this
    exact hv_le

/-! ### Safety diameter: two Config.succ applications reach fixpoint -/

/-- A locked configuration: some value holds all `n` processes. -/
def isLocked {n : Nat} (c : Config 2 n) : Prop :=
  ∃ v : Fin 2, c.counts v = n

/-- A locked configuration is a fixpoint. -/
theorem locked_is_fixpoint
    {α_num α_den : Nat} (h_valid : ValidThreshold α_num α_den)
    {n : Nat} (c : Config 2 n) (v : Fin 2) (hlock : c.counts v = n) :
    c.succ (absorbingBinary α_num α_den) = c := by
  by_cases hn : n = 0
  · -- n = 0: all counts are 0, both configs are trivial
    apply Config.ext
    funext w
    have h_sum := c.sum_eq
    simp [List.finRange, hn] at h_sum
    have hw0 : c.counts 0 = 0 := h_sum.1
    have hw1 : c.counts 1 = 0 := h_sum.2
    have hw : c.counts w = 0 := by rcases fin2_cases w with rfl | rfl <;> assumption
    have h_succ_sum :
        ((List.finRange 2).map (c.succ (absorbingBinary α_num α_den)).counts).sum = n :=
      succCounts_sum (absorbingBinary α_num α_den) c
    simp [List.finRange, hn] at h_succ_sum
    have hsw : (c.succ (absorbingBinary α_num α_den)).counts w = 0 := by
      rcases fin2_cases w with rfl | rfl
      · exact h_succ_sum.1
      · exact h_succ_sum.2
    rw [hsw, hw]
  · -- n ≥ 1: counts v = n implies at-threshold on v, so locking locks
    have hsm : hasAtThreshold α_num α_den c v := by
      simp only [hasAtThreshold, hlock]
      have hlt_one := h_valid.lt_one
      have hpos : 0 < n := Nat.pos_of_ne_zero hn
      have hmul : n * α_num < n * α_den :=
        Nat.mul_lt_mul_of_pos_left hlt_one hpos
      rw [Nat.mul_comm n α_num] at hmul
      exact hmul
    have h_succ_v := phase2_one_step_to_locked h_valid c v hsm
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
          ((List.finRange 2).map (c.succ (absorbingBinary α_num α_den)).counts).sum = n :=
        succCounts_sum (absorbingBinary α_num α_den) c
      simp [List.finRange] at h_succ_sum
      have hsw : (c.succ (absorbingBinary α_num α_den)).counts w = 0 := by
        rcases fin2_cases v with rfl | rfl <;> rcases fin2_cases w with rfl | rfl <;>
          simp_all
      rw [hsw, hcw]

/-- **Safety diameter bound.** Two `Config.succ` applications reach a
    fixpoint from any `c : Config 2 n`. -/
theorem safety_diameter_bound
    {α_num α_den : Nat} (h_valid : ValidThreshold α_num α_den)
    {n : Nat} (c : Config 2 n) :
    (c.succ (absorbingBinary α_num α_den)).succ (absorbingBinary α_num α_den) =
      c.succ (absorbingBinary α_num α_den) := by
  rcases phase1_or_phase2 α_num α_den c with hph1 | ⟨v, hv⟩
  · have hfix := obs2_phase1_absorbing c hph1
    rw [hfix]; exact hfix
  · have hlock : (c.succ (absorbingBinary α_num α_den)).counts v = n :=
      phase2_one_step_to_locked h_valid c v hv
    exact locked_is_fixpoint h_valid (c.succ (absorbingBinary α_num α_den)) v hlock

/-! ### The "no two at threshold" invariant -/

/-- The invariant: at most one value can be at threshold. Follows from
    `at_threshold_unique` and is therefore always true at the Config level
    (assuming valid parameters). -/
def noTwoAtThreshold (α_num α_den : Nat) : ConfigInv 2 :=
  fun n c => ¬ (hasAtThreshold α_num α_den c 0 ∧ hasAtThreshold α_num α_den c 1)

theorem noTwoAtThreshold_always
    {α_num α_den : Nat} (h_valid : ValidThreshold α_num α_den) :
    ∀ n (c : Config 2 n), noTwoAtThreshold α_num α_den n c := by
  intro n c
  intro ⟨h0, h1⟩
  exact at_threshold_unique h_valid c 0 1 (by decide) h0 h1

theorem noTwoAtThreshold_threshDetermined
    {α_num α_den : Nat} :
    (noTwoAtThreshold α_num α_den).threshDetermined α_num α_den := by
  intro n₁ n₂ c₁ c₂ htv
  simp only [noTwoAtThreshold, hasAtThreshold]
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

/-! ### The main cutoff theorem (abstract) -/

/-- **Phase-absorbing bounded-unrolling cutoff.** For any valid threshold
    parameters, `noTwoAtThreshold` holds for all `n` iff it holds for all
    `n ≤ cutoffBound 2 α_num α_den`. In fact, the invariant is a tautology
    (by `noTwoAtThreshold_always`), but the cutoff structure gives us the
    bounded-unrolling shape we want. -/
theorem phase_absorbing_bounded_unrolling_cutoff
    {α_num α_den : Nat} (h_valid : ValidThreshold α_num α_den) :
    (∀ n (c : Config 2 n), noTwoAtThreshold α_num α_den n c) ↔
    (∀ n ≤ cutoffBound 2 α_num α_den, ∀ c : Config 2 n,
      noTwoAtThreshold α_num α_den n c) := by
  constructor
  · intro hall n _ c; exact hall n c
  · intro _
    intro n c
    exact noTwoAtThreshold_always h_valid n c

/-! ### RoundState lifting via the bridge -/

/-- Package the absorbing binary STA as a `RoundSymThreshAlg` for use with
    the bridge. -/
def absorbingBinaryRsta (α_num α_den : Nat) :
    ConfigRoundBridge.RoundSymThreshAlg 2 α_num α_den where
  sta := absorbingBinary α_num α_den

/-- **RoundState-level safety.** The `noTwoAtThreshold` invariant lifts to
    every `RoundState` of the induced symmetric threshold protocol,
    uniformly for all valid threshold parameters. -/
theorem noTwoAtThreshold_roundState
    {α_num α_den : Nat} (h_valid : ValidThreshold α_num α_den)
    (n : Nat) (s : RoundState (Fin n) (Fin 2)) :
    ConfigRoundBridge.RoundStateInv (noTwoAtThreshold α_num α_den) s := by
  unfold ConfigRoundBridge.RoundStateInv
  exact noTwoAtThreshold_always h_valid n (ConfigRoundBridge.stateConfig s)

/-! ### Instantiation for OTR and majority

    These corollaries demonstrate that the abstract framework specializes
    cleanly to the two concrete instances already in Leslie. The existing
    files `OneThirdRuleBoundedUnrolling.lean` and
    `MajorityBoundedUnrolling.lean` remain as standalone implementations
    for backward compatibility; these corollaries are the "via the
    framework" alternative. -/

/-- OTR threshold parameters are valid (`2/3`, so `1/2 ≤ 2/3 < 1`). -/
theorem otr_valid : ValidThreshold 2 3 :=
  ⟨by omega, by omega, by omega⟩

/-- Majority threshold parameters are valid (`1/2`, borderline case). -/
theorem majority_valid : ValidThreshold 1 2 :=
  ⟨by omega, by omega, by omega⟩

/-- OTR's `otr_symthresh` equals the abstract absorbing binary at 2/3. -/
theorem otr_symthresh_eq_absorbing : otr_symthresh = absorbingBinary 2 3 := by
  apply SymThreshAlg.mk.injEq .. |>.mpr
  funext v tv
  simp only [otr_symthresh, absorbingBinary, binaryAbsorbingUpdate]

/-- OTR bounded-unrolling cutoff derived from the abstract framework. -/
theorem otr_cutoff_abstract :
    (∀ n (c : Config 2 n), noTwoAtThreshold 2 3 n c) ↔
    (∀ n ≤ cutoffBound 2 2 3, ∀ c : Config 2 n, noTwoAtThreshold 2 3 n c) :=
  phase_absorbing_bounded_unrolling_cutoff otr_valid

/-- Majority bounded-unrolling cutoff derived from the abstract framework. -/
theorem majority_cutoff_abstract :
    (∀ n (c : Config 2 n), noTwoAtThreshold 1 2 n c) ↔
    (∀ n ≤ cutoffBound 2 1 2, ∀ c : Config 2 n, noTwoAtThreshold 1 2 n c) :=
  phase_absorbing_bounded_unrolling_cutoff majority_valid

end TLA.PhaseAbsorbing
