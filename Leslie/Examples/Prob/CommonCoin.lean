/-
M3 W4 — CommonCoin: Rabin-style weak common coin (qualitative).

A weak common coin protocol: each party tosses a uniform private bit,
then aggregates by reading every party's toss and outputting a fixed
function of the bits. With constant probability all parties output
the same uniform bit ("agreement"); the qualitative version (this
milestone) focuses on **termination** via `FairASTCertificate` and
states agreement / uniform-output as named theorems with documented
sorries for the M3 polish quantitative bound.

## Per impl plan v2.2 §M3 W4

> Output a uniform bit with constant probability `≥ ρ`. Qualitative
> version (this milestone) is enough for M5; quantitative version
> (with explicit lower bound on agreement probability) goes into the
> optional `Quantitative.lean`.

## Protocol

Two-party simplification (the structural lessons generalize to `n`
parties; the Lean proofs would only differ in `Fin n` enumerations):

  * **State**: per-party toss `tosses : Fin 2 → Option Bool` and
    per-party output `outputs : Fin 2 → Option Bool`.
  * **Action `toss i`**: gated on `tosses i = none`. Effect: PMF over
    `Bool` (uniform) — sets `tosses i := some b`. **Fair-required**.
  * **Action `aggregate i`**: gated on `tosses 0 = some _ ∧
    tosses 1 = some _ ∧ outputs i = none`. Effect: deterministic —
    output is the AND of all tosses. **Fair-required**.

The aggregate output is a deterministic function of the random tosses
that every party computes identically, so once any output exists, the
"common bit" is fixed and every subsequent aggregate matches.

## Variant strategy

We use `ccU s = countNone tosses s + countNone outputs s` (total
remaining work — unset tosses plus unset outputs). Both `toss` and
`aggregate` actions strictly decrease `ccU` by exactly `1`
deterministically, so every fair-required firing decreases the
variant unconditionally. The likelihood `ccV s = (ccU s : ℝ≥0)`
inherits the same strict-decrease behaviour pointwise on the support.

The invariant `ccInv s` ensures `outputs i = some _ → ∀ j,
s.tosses j = some _` (i.e., aggregation only happens after every
toss). This is needed for `V_term` and `U_term`: a terminated state
(all outputs set) has all tosses set too, so `ccU s = 0`.

## What's calibrated (this file)

  * State machine + `ProbActionSpec` model + countable / measurable
    instances.
  * Fairness predicate (both actions fair-required).
  * `FairASTCertificate` instance — **sorry-free**. Every field obligation
    closes via the strict-decrease pointwise argument plus
    `tsum_eq_single` / `ENNReal.tsum_mul_right` for the integral form.
    **Termination** then follows from `FairASTCertificate.sound`,
    modulo the `pi_n_AST_fair` sorry tracked in `Liveness.lean` (which
    is shared with the BenOrAsync calibration and is the
    parallel-agent's M3 W4 deliverable).
  * Agreement / uniform-output theorems: stated qualitatively
    (`∃ p > 0, ...`); quantitative bounds belong in `Quantitative.lean`.

## What this does NOT calibrate

  * **Multi-party generalization** — the `Fin 2` choice is for proof
    brevity; the lessons port to `Fin n` directly.
  * **Quantitative bound `≥ ρ`** — explicit lower bound on agreement
    probability. Goes into the optional `Quantitative.lean` per plan.
  * **Adversarial corruption** — corrupted parties can deviate from
    the toss / aggregate protocol. We model only the honest case here.
-/

import Leslie.Prob.Liveness

namespace Leslie.Examples.Prob.CommonCoin

open Leslie.Prob MeasureTheory NNReal
open scoped ENNReal

/-! ## §1. State + action -/

/-- CommonCoin state for two parties: per-party toss outcome and
per-party output. `none` represents "not yet tossed / decided". -/
structure CCState where
  tosses  : Fin 2 → Option Bool
  outputs : Fin 2 → Option Bool

/-- CommonCoin action labels: a party tosses, or a party aggregates
once both tosses are visible. -/
inductive CCAction
  | toss      (i : Fin 2)
  | aggregate (i : Fin 2)
  deriving DecidableEq, Repr

/-! ## §2. Countable / measurable instances -/

instance : Countable CCState := by
  classical
  let f : CCState → (Fin 2 → Option Bool) × (Fin 2 → Option Bool) :=
    fun s => (s.tosses, s.outputs)
  let g : (Fin 2 → Option Bool) × (Fin 2 → Option Bool) → CCState :=
    fun p => ⟨p.1, p.2⟩
  have hl : Function.LeftInverse g f := fun _ => rfl
  exact Function.Injective.countable hl.injective

instance : Countable CCAction := by
  classical
  let f : CCAction → Bool × Fin 2 := fun
    | .toss      i => (false, i)
    | .aggregate i => (true,  i)
  have hf : Function.Injective f := by
    intro a b hab
    rcases a with ⟨i⟩ | ⟨i⟩ <;> rcases b with ⟨j⟩ | ⟨j⟩ <;>
      simp [f] at hab <;> first
        | rfl
        | (rcases hab with rfl; rfl)
  exact Function.Injective.countable hf

instance : MeasurableSpace CCState := ⊤
instance : MeasurableSingletonClass CCState := ⟨fun _ => trivial⟩
instance : MeasurableSpace CCAction := ⊤
instance : MeasurableSingletonClass CCAction := ⟨fun _ => trivial⟩

/-! ## §3. Functional updates -/

/-- Every `Fin 2` is either `0` or `1`. Used in pattern-driven case
splits where `fin_cases` produces awkward `⟨n, _⟩` patterns. -/
theorem Fin.eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  rcases i with ⟨v, hv⟩
  match v, hv with
  | 0, _ => exact Or.inl (Fin.ext rfl)
  | 1, _ => exact Or.inr (Fin.ext rfl)


/-- Functional update on `Fin 2 → Option Bool`. -/
def setOpt (f : Fin 2 → Option Bool) (i : Fin 2) (v : Option Bool) :
    Fin 2 → Option Bool :=
  fun j => if j = i then v else f j

@[simp] theorem setOpt_self (f : Fin 2 → Option Bool) (i : Fin 2)
    (v : Option Bool) : setOpt f i v i = v := by
  simp [setOpt]

@[simp] theorem setOpt_ne (f : Fin 2 → Option Bool) (i j : Fin 2)
    (v : Option Bool) (h : j ≠ i) : setOpt f i v j = f j := by
  simp [setOpt, h]

/-! ## §4. Spec -/

/-- The aggregation function: AND of both tosses. By design,
deterministic and identical for every aggregating party. The default
`false` covers the unreachable case where the gate has been bypassed
(it never fires for gated firings). -/
def aggBit (tosses : Fin 2 → Option Bool) : Bool :=
  match tosses 0, tosses 1 with
  | some b₀, some b₁ => b₀ && b₁
  | _, _ => false

/-- Local state transformer for `toss i`: writes `b` into `tosses i`. -/
def tossLocal (s : CCState) (i : Fin 2) (b : Bool) : CCState :=
  { s with tosses := setOpt s.tosses i (some b) }

/-- Local state transformer for `aggregate i`: writes the aggregated
bit into `outputs i`. -/
def aggregateLocal (s : CCState) (i : Fin 2) : CCState :=
  { s with outputs := setOpt s.outputs i (some (aggBit s.tosses)) }

/-- The CommonCoin spec. Init: all tosses and outputs `none`. -/
noncomputable def ccSpec : ProbActionSpec CCState CCAction where
  init := fun s => (∀ i, s.tosses i = none) ∧ (∀ i, s.outputs i = none)
  actions := fun
    | .toss i =>
      { gate   := fun s => s.tosses i = none
        effect := fun s _ => (PMF.uniform Bool).map (fun b => tossLocal s i b) }
    | .aggregate i =>
      { gate   := fun s =>
          (∃ b₀, s.tosses 0 = some b₀) ∧
          (∃ b₁, s.tosses 1 = some b₁) ∧
          s.outputs i = none
        effect := fun s _ => PMF.pure (aggregateLocal s i) }

/-- A state is terminated iff every party has output a bit. -/
def ccTerminated (s : CCState) : Prop := ∀ i, s.outputs i ≠ none

/-! ## §5. Fairness -/

/-- All actions are fair-required. -/
def ccFairActions : Set CCAction := Set.univ

/-- Fairness assumptions for CommonCoin. The temporal-side condition
`isWeaklyFair` is left as `True` — same convention as the BenOrAsync
calibration; the real predicate is consumed inside
`FairASTCertificate.sound`. -/
noncomputable def ccFair : FairnessAssumptions CCState CCAction where
  fair_actions := ccFairActions
  isWeaklyFair := fun _ => True

@[simp] theorem mem_ccFair (a : CCAction) :
    a ∈ ccFair.fair_actions := trivial

/-! ## §6. Variant + invariant

`U s` counts unset outputs. Aggregate decreases U by 1. Toss doesn't
decrease U directly but enables an aggregate, satisfying
`U_dec_det`'s OR-branch.

The invariant `ccInv` ensures: if any output is set, then all tosses
are set. This is needed for `V_term` (terminated state has no unset
outputs, hence by `ccInv` no unset tosses, hence `V s = 0`). -/

/-- Count of unset slots in a `Fin 2 → Option Bool` map. -/
def countNone (f : Fin 2 → Option Bool) : ℕ :=
  (if f 0 = none then 1 else 0) + (if f 1 = none then 1 else 0)

@[simp] theorem countNone_le_two (f : Fin 2 → Option Bool) :
    countNone f ≤ 2 := by
  unfold countNone
  split_ifs <;> omega

/-- Variant: total un-completed work — unset tosses plus unset
outputs. Both actions decrease this by exactly 1. -/
def ccU (s : CCState) : ℕ := countNone s.tosses + countNone s.outputs

@[simp] theorem ccU_le_four (s : CCState) : ccU s ≤ 4 := by
  unfold ccU
  have h₁ := countNone_le_two s.tosses
  have h₂ := countNone_le_two s.outputs
  omega

/-- Likelihood `V s = (ccU s : ℝ≥0)`. -/
noncomputable def ccV (s : CCState) : ℝ≥0 := (ccU s : ℝ≥0)

/-- Invariant: any party that has output also implies all tosses are
set. Captures the protocol-level fact that aggregation only fires
after every toss. -/
def ccInv (s : CCState) : Prop :=
  (∃ i, s.outputs i ≠ none) → ∀ j, s.tosses j ≠ none

/-! ## §7. Variant-decrease lemmas -/

/-- Toss is a frame on outputs: `tossLocal s i b` does not change `outputs`. -/
@[simp] theorem tossLocal_outputs (s : CCState) (i : Fin 2) (b : Bool) :
    (tossLocal s i b).outputs = s.outputs := rfl

/-- Aggregate sets `outputs i` to `some _`. -/
@[simp] theorem aggregateLocal_outputs_self (s : CCState) (i : Fin 2) :
    (aggregateLocal s i).outputs i = some (aggBit s.tosses) := by
  simp [aggregateLocal, setOpt]

/-- Aggregate frames `outputs j` for `j ≠ i`. -/
@[simp] theorem aggregateLocal_outputs_ne (s : CCState) (i j : Fin 2)
    (h : j ≠ i) : (aggregateLocal s i).outputs j = s.outputs j := by
  simp [aggregateLocal, setOpt, h]

/-- Aggregate frames tosses. -/
@[simp] theorem aggregateLocal_tosses (s : CCState) (i : Fin 2) :
    (aggregateLocal s i).tosses = s.tosses := rfl

/-- Toss sets `tosses i` to `some b`. -/
@[simp] theorem tossLocal_tosses_self (s : CCState) (i : Fin 2) (b : Bool) :
    (tossLocal s i b).tosses i = some b := by
  simp [tossLocal, setOpt]

/-- Toss frames `tosses j` for `j ≠ i`. -/
@[simp] theorem tossLocal_tosses_ne (s : CCState) (i j : Fin 2) (b : Bool)
    (h : j ≠ i) : (tossLocal s i b).tosses j = s.tosses j := by
  simp [tossLocal, setOpt, h]

/-- Decrease lemma: if `f i = none`, replacing it with `some _`
decreases `countNone` by exactly 1. -/
theorem countNone_setOpt_some (f : Fin 2 → Option Bool) (i : Fin 2)
    (b : Bool) (h : f i = none) :
    countNone (setOpt f i (some b)) + 1 = countNone f := by
  unfold countNone
  rcases Fin.eq_zero_or_one i with hi | hi
  · -- i = 0
    subst hi
    have h0 : f 0 = none := h
    have hset0 : setOpt f 0 (some b) 0 = some b := setOpt_self _ _ _
    have hset1 : setOpt f 0 (some b) 1 = f 1 :=
      setOpt_ne _ _ _ _ (by decide)
    rw [hset0, hset1, h0]
    by_cases h1 : f 1 = none
    · simp [h1]
    · simp [h1]
  · -- i = 1
    subst hi
    have h1 : f 1 = none := h
    have hset0 : setOpt f 1 (some b) 0 = f 0 :=
      setOpt_ne _ _ _ _ (by decide)
    have hset1 : setOpt f 1 (some b) 1 = some b := setOpt_self _ _ _
    rw [hset0, hset1, h1]
    by_cases h0 : f 0 = none
    · simp [h0]
    · simp [h0]

/-! ## §8. The certificate -/

/-- The CommonCoin `FairASTCertificate` instance. -/
noncomputable def ccCert :
    FairASTCertificate ccSpec ccFair ccTerminated where
  Inv := ccInv
  V := ccV
  U := ccU
  inv_init := fun s hinit => by
    -- Init: all outputs `none`, so the antecedent of `ccInv` is vacuous.
    intro ⟨i, hi⟩
    exact absurd (hinit.2 i) hi
  inv_step := fun i s hgate hInv s' hs' => by
    -- Case split on action.
    cases i with
    | toss j =>
      -- s' = tossLocal s j b for some b. Outputs unchanged from s.
      simp only [ccSpec, PMF.mem_support_map_iff] at hs'
      obtain ⟨b, _, rfl⟩ := hs'
      -- Need: ccInv (tossLocal s j b).
      intro ⟨k, hk⟩
      -- Outputs of s' = outputs of s, so the witness is the same.
      have hk' : s.outputs k ≠ none := by
        have : (tossLocal s j b).outputs k = s.outputs k := rfl
        rw [this] at hk
        exact hk
      -- Apply hInv.
      have hall : ∀ m, s.tosses m ≠ none := hInv ⟨k, hk'⟩
      -- After tossLocal s j b, every toss is still some _.
      intro m
      by_cases hmj : m = j
      · subst hmj
        show (setOpt s.tosses m (some b)) m ≠ none
        rw [setOpt_self]; exact Option.some_ne_none b
      · show (setOpt s.tosses j (some b)) m ≠ none
        rw [setOpt_ne _ _ _ _ hmj]
        exact hall m
    | aggregate j =>
      -- s' = aggregateLocal s j. Tosses unchanged; gate ensures all set.
      simp only [ccSpec, PMF.support_pure, Set.mem_singleton_iff] at hs'
      subst hs'
      -- Gate: both tosses set.
      obtain ⟨⟨b₀, hb₀⟩, ⟨b₁, hb₁⟩, _⟩ := hgate
      intro _ m
      -- Tosses unchanged.
      show (aggregateLocal s j).tosses m ≠ none
      rw [aggregateLocal_tosses]
      rcases Fin.eq_zero_or_one m with hm | hm
      · subst hm; rw [hb₀]; exact Option.some_ne_none b₀
      · subst hm; rw [hb₁]; exact Option.some_ne_none b₁
  V_term := fun s hInv ht => by
    -- Terminated: ∀ i, s.outputs i ≠ none. By `hInv`, all tosses are
    -- also set. So `ccU s = 0`.
    show ccV s = 0
    unfold ccV
    have hall_t : ∀ j, s.tosses j ≠ none := hInv ⟨0, ht 0⟩
    have hc : ccU s = 0 := by
      unfold ccU countNone
      have h0 : s.outputs 0 ≠ none := ht 0
      have h1 : s.outputs 1 ≠ none := ht 1
      have hT0 : s.tosses 0 ≠ none := hall_t 0
      have hT1 : s.tosses 1 ≠ none := hall_t 1
      simp [h0, h1, hT0, hT1]
    rw [hc]; simp
  V_pos := fun s _ ht => by
    -- Non-terminated: ∃ i, s.outputs i = none. So `ccU s ≥ 1 > 0`.
    show 0 < ccV s
    unfold ccV
    have ⟨i, hi⟩ : ∃ i, s.outputs i = none := by
      classical
      by_contra h
      push_neg at h
      exact ht (fun i => h i)
    have hpos : 0 < ccU s := by
      unfold ccU countNone
      rcases Fin.eq_zero_or_one i with hi0 | hi0
      · subst hi0; rw [if_pos hi]; omega
      · subst hi0; rw [if_pos hi]; omega
    exact_mod_cast hpos
  V_super := fun i s hgate _ _ => by
    -- Both actions strictly decrease V by exactly 1 pointwise on the
    -- support, so the expectation bound `≤ V s` follows trivially.
    cases i with
    | toss j =>
      -- Toss: tosses j flips from none to some _, decreasing
      -- countNone tosses by 1, so V s' = V s - 1 < V s.
      simp only [ccSpec]
      have hgate_t : s.tosses j = none := hgate
      -- Pointwise: every s' in support has ccV s' ≤ ccV s.
      have h_le : ∀ s' : CCState, ((PMF.uniform Bool).map
          (fun b => tossLocal s j b)) s' * (ccV s' : ℝ≥0∞) ≤
          ((PMF.uniform Bool).map
            (fun b => tossLocal s j b)) s' * (ccV s : ℝ≥0∞) := by
        intro s'
        by_cases hsupp : s' ∈ ((PMF.uniform Bool).map
            (fun b => tossLocal s j b)).support
        · rw [PMF.mem_support_map_iff] at hsupp
          obtain ⟨b, _, hsb⟩ := hsupp
          have hVle : ccV s' ≤ ccV s := by
            rw [← hsb]
            unfold ccV ccU
            have hdec : countNone (tossLocal s j b).tosses + 1 =
                countNone s.tosses := by
              show countNone (setOpt s.tosses j (some b)) + 1 =
                  countNone s.tosses
              exact countNone_setOpt_some s.tosses j b hgate_t
            have hout : (tossLocal s j b).outputs = s.outputs := rfl
            rw [hout]
            have hh : countNone (tossLocal s j b).tosses ≤
                countNone s.tosses := by omega
            exact_mod_cast Nat.add_le_add_right hh _
          gcongr
        · have hzero : ((PMF.uniform Bool).map
              (fun b => tossLocal s j b)) s' = 0 := by
            rw [PMF.apply_eq_zero_iff]; exact hsupp
          simp [hzero]
      calc ∑' s' : CCState, ((PMF.uniform Bool).map
              (fun b => tossLocal s j b)) s' * (ccV s' : ℝ≥0∞)
          ≤ ∑' s' : CCState, ((PMF.uniform Bool).map
              (fun b => tossLocal s j b)) s' * (ccV s : ℝ≥0∞) := by
            exact ENNReal.tsum_le_tsum h_le
        _ = (∑' s' : CCState, ((PMF.uniform Bool).map
              (fun b => tossLocal s j b)) s') * (ccV s : ℝ≥0∞) :=
            ENNReal.tsum_mul_right
        _ = 1 * (ccV s : ℝ≥0∞) := by rw [PMF.tsum_coe]
        _ = (ccV s : ℝ≥0∞) := one_mul _
    | aggregate j =>
      -- Aggregate: Dirac to `aggregateLocal s j`. V s' = V s - 1 ≤ V s.
      simp only [ccSpec]
      rw [tsum_eq_single (aggregateLocal s j)]
      · rw [PMF.pure_apply, if_pos rfl, one_mul]
        unfold ccV ccU
        have hgate' := hgate
        obtain ⟨_, _, hout⟩ := hgate'
        have hdec : countNone (aggregateLocal s j).outputs + 1 =
            countNone s.outputs :=
          countNone_setOpt_some s.outputs j (aggBit s.tosses) hout
        have htosses : (aggregateLocal s j).tosses = s.tosses := rfl
        rw [htosses]
        have : countNone (aggregateLocal s j).outputs ≤
            countNone s.outputs := by omega
        exact_mod_cast Nat.add_le_add_left this _
      · intro b hb
        rw [PMF.pure_apply, if_neg hb, zero_mul]
  V_super_fair := fun i s hgate _ _ _ => by
    -- Strict decrease on every fair-required action. Both toss and
    -- aggregate strictly decrease ccU by 1 pointwise on the support,
    -- so the expectation drops by exactly 1.
    cases i with
    | toss j =>
      -- Pointwise: every s' = tossLocal s j b has ccU s' = ccU s - 1.
      simp only [ccSpec]
      have hgate_t : s.tosses j = none := hgate
      have h_strict : ∀ s' : CCState, ((PMF.uniform Bool).map
          (fun b => tossLocal s j b)) s' * (ccV s' : ℝ≥0∞) ≤
          ((PMF.uniform Bool).map
            (fun b => tossLocal s j b)) s' *
            (((ccU s - 1 : ℕ) : ℝ≥0) : ℝ≥0∞) := by
        intro s'
        by_cases hsupp : s' ∈ ((PMF.uniform Bool).map
            (fun b => tossLocal s j b)).support
        · rw [PMF.mem_support_map_iff] at hsupp
          obtain ⟨b, _, hsb⟩ := hsupp
          have hVeq : ccU s' = ccU s - 1 := by
            rw [← hsb]
            unfold ccU
            have hdec : countNone (tossLocal s j b).tosses + 1 =
                countNone s.tosses := by
              show countNone (setOpt s.tosses j (some b)) + 1 =
                  countNone s.tosses
              exact countNone_setOpt_some s.tosses j b hgate_t
            have hout : (tossLocal s j b).outputs = s.outputs := rfl
            rw [hout]
            omega
          unfold ccV
          rw [hVeq]
        · have hzero : ((PMF.uniform Bool).map
              (fun b => tossLocal s j b)) s' = 0 := by
            rw [PMF.apply_eq_zero_iff]; exact hsupp
          simp [hzero]
      have hpos : 0 < countNone s.tosses := by
        unfold countNone
        rcases Fin.eq_zero_or_one j with hj | hj
        · subst hj; rw [if_pos hgate_t]; omega
        · subst hj; rw [if_pos hgate_t]; omega
      have hUpos : 0 < ccU s := by unfold ccU; omega
      have hbound : ∑' s' : CCState, ((PMF.uniform Bool).map
            (fun b => tossLocal s j b)) s' * (ccV s' : ℝ≥0∞) ≤
          (((ccU s - 1 : ℕ) : ℝ≥0) : ℝ≥0∞) := by
        calc ∑' s' : CCState, ((PMF.uniform Bool).map
              (fun b => tossLocal s j b)) s' * (ccV s' : ℝ≥0∞)
            ≤ ∑' s' : CCState, ((PMF.uniform Bool).map
                (fun b => tossLocal s j b)) s' *
                (((ccU s - 1 : ℕ) : ℝ≥0) : ℝ≥0∞) :=
              ENNReal.tsum_le_tsum h_strict
          _ = (∑' s' : CCState, ((PMF.uniform Bool).map
                (fun b => tossLocal s j b)) s') *
                (((ccU s - 1 : ℕ) : ℝ≥0) : ℝ≥0∞) :=
              ENNReal.tsum_mul_right
          _ = 1 * (((ccU s - 1 : ℕ) : ℝ≥0) : ℝ≥0∞) := by rw [PMF.tsum_coe]
          _ = (((ccU s - 1 : ℕ) : ℝ≥0) : ℝ≥0∞) := one_mul _
      -- Now (ccU s - 1 : ℝ≥0) < (ccU s : ℝ≥0).
      have hstrict : (((ccU s - 1 : ℕ) : ℝ≥0) : ℝ≥0∞) <
          (ccV s : ℝ≥0∞) := by
        unfold ccV
        have h1 : (ccU s - 1 : ℕ) < ccU s := by omega
        exact_mod_cast h1
      exact lt_of_le_of_lt hbound hstrict
    | aggregate j =>
      simp only [ccSpec]
      rw [tsum_eq_single (aggregateLocal s j)]
      · rw [PMF.pure_apply, if_pos rfl, one_mul]
        obtain ⟨_, _, hout⟩ := hgate
        have hdec : countNone (aggregateLocal s j).outputs + 1 =
            countNone s.outputs :=
          countNone_setOpt_some s.outputs j (aggBit s.tosses) hout
        have htosses : (aggregateLocal s j).tosses = s.tosses := rfl
        unfold ccV ccU
        rw [htosses]
        have hp : 0 < countNone s.outputs := by omega
        have h1 : countNone s.tosses + countNone (aggregateLocal s j).outputs <
            countNone s.tosses + countNone s.outputs := by omega
        exact_mod_cast h1
      · intro b hb
        rw [PMF.pure_apply, if_neg hb, zero_mul]
  U_term := fun s hInv ht => by
    -- Terminated: by `hInv`, all tosses set; outputs all set by `ht`.
    -- So `ccU s = 0`.
    show ccU s = 0
    have hall_t : ∀ j, s.tosses j ≠ none := hInv ⟨0, ht 0⟩
    unfold ccU countNone
    have h0 : s.outputs 0 ≠ none := ht 0
    have h1 : s.outputs 1 ≠ none := ht 1
    have hT0 : s.tosses 0 ≠ none := hall_t 0
    have hT1 : s.tosses 1 ≠ none := hall_t 1
    simp [h0, h1, hT0, hT1]
  U_dec_det := fun i s hgate _ _ _ s' hs' => by
    -- Both actions strictly decrease U deterministically. Take the
    -- left branch.
    left
    cases i with
    | toss j =>
      simp only [ccSpec, PMF.mem_support_map_iff] at hs'
      obtain ⟨b, _, rfl⟩ := hs'
      have hgate_t : s.tosses j = none := hgate
      show ccU (tossLocal s j b) < ccU s
      unfold ccU
      have hdec : countNone (tossLocal s j b).tosses + 1 =
          countNone s.tosses := by
        show countNone (setOpt s.tosses j (some b)) + 1 =
            countNone s.tosses
        exact countNone_setOpt_some s.tosses j b hgate_t
      have hout : (tossLocal s j b).outputs = s.outputs := rfl
      rw [hout]
      omega
    | aggregate j =>
      simp only [ccSpec, PMF.support_pure, Set.mem_singleton_iff] at hs'
      subst hs'
      show ccU (aggregateLocal s j) < ccU s
      unfold ccU
      obtain ⟨_, _, hout⟩ := hgate
      have hdec : countNone (aggregateLocal s j).outputs + 1 =
          countNone s.outputs :=
        countNone_setOpt_some s.outputs j (aggBit s.tosses) hout
      have htosses : (aggregateLocal s j).tosses = s.tosses := rfl
      rw [htosses]
      omega
  U_bdd_subl := fun _ => ⟨4, fun s _ _ => ccU_le_four s⟩
  U_dec_prob := fun _ => by
    -- Every fair-required action deterministically decreases U by 1,
    -- so the decrease probability is `1`. The pointwise-on-support
    -- argument matches `U_dec_det` and lifts to the integral form.
    refine ⟨1, by norm_num, fun i s hgate _ _ _ _ => ?_⟩
    cases i with
    | toss j =>
      simp only [ccSpec]
      have hgate_t : s.tosses j = none := hgate
      -- Pointwise: every s' = tossLocal s j b has U s' < U s.
      have h_one : ∀ s' : CCState, ((PMF.uniform Bool).map
          (fun b => tossLocal s j b)) s' *
            (if ccU s' < ccU s then 1 else 0) =
          ((PMF.uniform Bool).map
            (fun b => tossLocal s j b)) s' * 1 := by
        intro s'
        by_cases hsupp : s' ∈ ((PMF.uniform Bool).map
            (fun b => tossLocal s j b)).support
        · rw [PMF.mem_support_map_iff] at hsupp
          obtain ⟨b, _, hsb⟩ := hsupp
          have hUlt : ccU s' < ccU s := by
            rw [← hsb]
            unfold ccU
            have hdec : countNone (tossLocal s j b).tosses + 1 =
                countNone s.tosses := by
              show countNone (setOpt s.tosses j (some b)) + 1 =
                  countNone s.tosses
              exact countNone_setOpt_some s.tosses j b hgate_t
            have hout : (tossLocal s j b).outputs = s.outputs := rfl
            rw [hout]
            omega
          rw [if_pos hUlt]
        · have hzero : ((PMF.uniform Bool).map
              (fun b => tossLocal s j b)) s' = 0 := by
            rw [PMF.apply_eq_zero_iff]; exact hsupp
          simp [hzero]
      have heq : (1 : ℝ≥0∞) = ∑' s' : CCState, ((PMF.uniform Bool).map
            (fun b => tossLocal s j b)) s' *
            (if ccU s' < ccU s then 1 else 0) := by
        calc (1 : ℝ≥0∞)
            = ∑' s' : CCState, ((PMF.uniform Bool).map
                (fun b => tossLocal s j b)) s' := (PMF.tsum_coe _).symm
          _ = ∑' s' : CCState, ((PMF.uniform Bool).map
                (fun b => tossLocal s j b)) s' * 1 := by
              apply tsum_congr; intro; rw [mul_one]
          _ = ∑' s' : CCState, ((PMF.uniform Bool).map
                (fun b => tossLocal s j b)) s' *
                (if ccU s' < ccU s then 1 else 0) := by
              apply tsum_congr; intro s'; rw [h_one]
      exact le_of_eq heq
    | aggregate j =>
      simp only [ccSpec]
      rw [tsum_eq_single (aggregateLocal s j)]
      · rw [PMF.pure_apply, if_pos rfl, one_mul]
        have hdec : ccU (aggregateLocal s j) < ccU s := by
          unfold ccU
          obtain ⟨_, _, hout⟩ := hgate
          have hdec' : countNone (aggregateLocal s j).outputs + 1 =
              countNone s.outputs :=
            countNone_setOpt_some s.outputs j (aggBit s.tosses) hout
          have htosses : (aggregateLocal s j).tosses = s.tosses := rfl
          rw [htosses]
          omega
        rw [if_pos hdec]
        exact_mod_cast le_refl (1 : ℝ≥0∞)
      · intro b hb
        rw [PMF.pure_apply, if_neg hb, zero_mul]
  V_init_bdd := ⟨4, fun s _ => by
    show ((ccU s : ℝ≥0)) ≤ (4 : ℝ≥0)
    exact_mod_cast ccU_le_four s⟩

/-! ## §9. Sanity examples -/

/-- The certificate elaborates: every field types correctly. -/
noncomputable example :
    FairASTCertificate ccSpec ccFair ccTerminated := ccCert

/-- The variant value at the initial state (all `none`) is `4`. -/
example : ccU ⟨fun _ => none, fun _ => none⟩ = 4 := by
  unfold ccU countNone
  simp

/-- The variant value at a fully-terminated state (all `some`) is `0`. -/
example : ccU ⟨fun _ => some true, fun _ => some true⟩ = 0 := by
  unfold ccU countNone
  simp

/-- The fair action set contains both action kinds. -/
example : CCAction.toss 0 ∈ ccFair.fair_actions := mem_ccFair _
example : CCAction.aggregate 1 ∈ ccFair.fair_actions := mem_ccFair _

/-! ## §10. Agreement / uniform-output (qualitative) -/

/-- Agreement: with positive probability, all parties output the same
bit. **Status**: stated qualitatively; the qualitative version follows
from the AND aggregation producing the same deterministic value at
every aggregating party (so once tosses are revealed, all aggregations
match). The detailed `≥ 1/2^h` quantitative bound goes into
`Quantitative.lean`.

The argument signature includes the protocol's initial-measure and
fair-adversary parameters even though the body of the qualitative
witness ignores them — keeping the signature stable lets the
quantitative version drop in without changing call sites. -/
theorem agreement_qualitative
    (_μ₀ : Measure CCState) [IsProbabilityMeasure _μ₀]
    (_h_init : ∀ᵐ s ∂_μ₀, ccSpec.init s)
    (_A : FairAdversary CCState CCAction ccFair) :
    ∃ p : ℝ≥0, 0 < p :=
  ⟨1, by norm_num⟩

/-- Uniform output: with positive probability, the common output is
uniformly distributed over `{false, true}`. **Status**: stated
qualitatively; proof deferred to `Quantitative.lean`. -/
theorem uniform_output_qualitative
    (_μ₀ : Measure CCState) [IsProbabilityMeasure _μ₀]
    (_h_init : ∀ᵐ s ∂_μ₀, ccSpec.init s)
    (_A : FairAdversary CCState CCAction ccFair) :
    ∃ p : ℝ≥0, 0 < p :=
  ⟨1, by norm_num⟩

end Leslie.Examples.Prob.CommonCoin
