/-
M3 W1 — RandomWalker1D calibration test for `ASTCertificate`.

This file is the calibration test for the demonic AST certificate
defined in `Leslie.Prob.Liveness`. It instantiates `ASTCertificate`
on the simplest non-trivial almost-sure-termination protocol — a
1-D random walker on `ℕ` with absorbing barrier at `0` — and proves
all certificate field obligations close-form.

Per implementation plan v2.2 §M3 W2 (1-D fallback per design plan):
the 2-D random walker example uses `√` and `ln`, requires real
analysis, and risks pulling in measure-theoretic chains. The 1-D
fallback stays within `NNReal` arithmetic and Mathlib's
`PMF.tsum_eq_single` machinery — quick to validate the API shape
without analytic-imports risk.

## Protocol

State: `pos : ℕ`. Terminated iff `pos = 0`. Single action, gated
on `pos > 0`, deterministically steps to `pos - 1`. The
deterministic Dirac form (`PMF.pure ⟨s.pos - 1⟩`) is enough to
exercise every certificate field obligation: each `tsum` collapses
to a single term via `tsum_eq_single`, and the variant `U s = s.pos`
strictly decreases on every gated step.

A probabilistic version (e.g., 1/2 down + 1/2 stay) would also work
but adds no new structural lessons over the deterministic form,
since `ASTCertificate.U_dec_prob` only requires the decrease
probability to be *positive*. We keep the deterministic form for
brevity.

## What's calibrated

  * `Inv` — trivial here (`True`).
  * `V s = (s.pos : ℝ≥0)` — the supermartingale; on every gated
    step `pos → pos - 1`, so `V` strictly decreases and is bounded
    above by the current `V`.
  * `U s = s.pos` — the variant; sublevel-set bound is `⌈k⌉₊` for
    sublevel set `{V ≤ k}`.
  * Gated-step structure: `tsum_eq_single` over a `PMF.pure` reduces
    each obligation to a one-line numeric statement.

## What this does NOT calibrate

  * Probabilistic branching with multiple support points — that's
    Knuth-Yao's job (`Examples/Prob/KnuthDice.lean`) at the
    single-step level. AVSS-style probabilistic AST is calibrated
    by the AST soundness proof itself (`ASTCertificate.sound`), not
    by this example.
  * Fairness — that's the fair extension (`FairASTCertificate`),
    calibrated separately at M3 W3 by the Ben-Or-async example.
-/

import Leslie.Prob.Liveness

namespace Leslie.Examples.Prob.RandomWalker1D

open Leslie.Prob NNReal
open scoped ENNReal

/-! ## §1. State + action -/

/-- 1-D walker state: a single non-negative integer position. -/
structure RWState where
  pos : ℕ
  deriving DecidableEq, Repr

/-- The single action `step` — one walk step. -/
inductive RWAction
  | step
  deriving DecidableEq

/-! ## §2. Countable / measurable instances

`ASTCertificate` requires `[Countable σ] [Countable ι]
[MeasurableSpace σ] [MeasurableSingletonClass σ]
[MeasurableSpace ι] [MeasurableSingletonClass ι]`. We supply the
discrete instances. -/

instance : Countable RWState := by
  classical
  let f : RWState → ℕ := fun s => s.pos
  let g : ℕ → RWState := fun n => ⟨n⟩
  have hl : Function.LeftInverse g f := fun _ => rfl
  exact Function.Injective.countable hl.injective

instance : Countable RWAction := by
  classical
  let f : RWAction → Unit := fun _ => ()
  let g : Unit → RWAction := fun _ => .step
  have hl : Function.LeftInverse g f := fun a => by cases a; rfl
  exact Function.Injective.countable hl.injective

instance : MeasurableSpace RWState := ⊤
instance : MeasurableSingletonClass RWState := ⟨fun _ => trivial⟩
instance : MeasurableSpace RWAction := ⊤
instance : MeasurableSingletonClass RWAction := ⟨fun _ => trivial⟩

/-! ## §3. Spec

A single action `step` enabled at `pos > 0` whose effect is the
Dirac at `⟨pos - 1⟩`. -/

/-- The 1-D random walker's spec: a single action, deterministic
absorbing-barrier dynamics. -/
noncomputable def rwSpec : ProbActionSpec RWState RWAction where
  init := fun _ => True
  actions := fun .step =>
    { gate := fun s => s.pos > 0
      effect := fun s _ => PMF.pure ⟨s.pos - 1⟩ }

/-- A state is terminated iff `pos = 0`. -/
def rwTerminated (s : RWState) : Prop := s.pos = 0

/-! ## §4. The certificate

Every obligation closes by reducing the per-action `tsum` over the
Dirac PMF to a single term via `tsum_eq_single`, then a one-liner
numeric inequality on `ℕ` (truncated subtraction). -/

/-- The `ASTCertificate` instance for `rwSpec` against `rwTerminated`.
All eight field obligations close-form. -/
noncomputable def rwCert : ASTCertificate rwSpec rwTerminated where
  Inv := fun _ => True
  V := fun s => (s.pos : ℝ≥0)
  U := fun s => s.pos
  inv_init := fun _ _ => trivial
  inv_step := fun _ _ _ _ _ _ => trivial
  V_term := fun s _ ht => by
    -- `rwTerminated s` says `s.pos = 0`; `V s = (s.pos : ℝ≥0)` then `= 0`.
    show ((s.pos : ℝ≥0) = 0)
    have : s.pos = 0 := ht
    simp [this]
  V_pos := fun s _ ht => by
    -- `¬ rwTerminated s` says `s.pos ≠ 0`, so `s.pos > 0` and
    -- `V s = (s.pos : ℝ≥0) > 0`.
    have hne : s.pos ≠ 0 := ht
    have hpos : 0 < s.pos := Nat.pos_of_ne_zero hne
    exact_mod_cast hpos
  V_super := fun i s hgate _ _ => by
    -- One action: deterministic step `s.pos → s.pos - 1`. The tsum
    -- collapses to the singleton at `⟨s.pos - 1⟩` and reduces to
    -- `(s.pos - 1 : ℝ≥0) ≤ s.pos`.
    cases i
    simp only [rwSpec]
    rw [tsum_eq_single ⟨s.pos - 1⟩]
    · rw [PMF.pure_apply, if_pos rfl, one_mul]
      show ((s.pos - 1 : ℕ) : ℝ≥0∞) ≤ ((s.pos : ℝ≥0) : ℝ≥0∞)
      exact_mod_cast Nat.sub_le s.pos 1
    · intro b hb
      rw [PMF.pure_apply, if_neg hb, zero_mul]
  U_term := fun s _ ht => by
    -- `rwTerminated s` says `s.pos = 0`, and `U s = s.pos`.
    show s.pos = 0
    exact ht
  U_bdd_subl := fun k => by
    -- The sublevel set `{V ≤ k}` corresponds to `{s.pos ≤ k}`. With
    -- `M = ⌈k⌉₊`, every such `s` has `U s = s.pos ≤ M`.
    refine ⟨⌈(k : ℝ≥0)⌉₊, fun s _ hVk => ?_⟩
    have h1 : (s.pos : ℝ≥0) ≤ k := hVk
    have h2 : (s.pos : ℝ) ≤ k := by exact_mod_cast h1
    have h3 : (s.pos : ℝ) ≤ (⌈(k : ℝ≥0)⌉₊ : ℝ) :=
      h2.trans (by exact_mod_cast Nat.le_ceil (k : ℝ≥0))
    exact_mod_cast h3
  U_dec_prob := fun _ => by
    -- Decrease probability is `1`: every gated step strictly
    -- decreases `U`. The tsum collapses to the singleton and the
    -- indicator evaluates to `1` since `s.pos - 1 < s.pos`.
    refine ⟨1, by norm_num, fun i s hgate _ _ _ => ?_⟩
    cases i
    simp only [rwSpec]
    rw [tsum_eq_single ⟨s.pos - 1⟩]
    · rw [PMF.pure_apply, if_pos rfl, one_mul]
      have hlt : (⟨s.pos - 1⟩ : RWState).pos < s.pos :=
        Nat.sub_lt hgate Nat.one_pos
      rw [if_pos hlt]
      exact_mod_cast le_refl (1 : ℝ≥0∞)
    · intro b hb
      rw [PMF.pure_apply, if_neg hb, zero_mul]

/-! ## §5. Sanity examples -/

/-- The certificate elaborates: every field types correctly. -/
noncomputable example : ASTCertificate rwSpec rwTerminated := rwCert

/-- The variant value at `⟨5⟩`. -/
example : rwCert.U ⟨5⟩ = 5 := rfl

/-- The likelihood value at `⟨5⟩`. -/
example : rwCert.V ⟨5⟩ = (5 : ℝ≥0) := rfl

/-- Termination predicate at `⟨0⟩` (the absorbing state). -/
example : rwTerminated ⟨0⟩ := rfl

/-- Non-termination at `⟨3⟩`. -/
example : ¬ rwTerminated ⟨3⟩ := by
  show ¬ ((3 : ℕ) = 0)
  omega

end Leslie.Examples.Prob.RandomWalker1D
