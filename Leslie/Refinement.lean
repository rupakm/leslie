import Leslie.Rules.Basic
import Leslie.Rules.StatePred
import Leslie.Tactics.Structural

/-! ## Refinement for TLA Specifications

    This file defines:
    - `Spec`: a TLA specification (init, next, fairness)
    - `exec.map`: mapping executions through a state function
    - `refines_via`: refinement between specifications via a mapping
    - The Abadi-Lamport refinement mapping theorem (safety)
    - Transitivity of refinement
    - Invariant-based refinement
-/

open Classical

namespace TLA

/-! ### Specifications -/

structure Spec (σ : Type u) where
  init : σ → Prop
  next : action σ
  fair : List (action σ) := []

def Spec.safety (spec : Spec σ) : pred σ :=
  [tlafml| ⌜ spec.init ⌝ ∧ □ ⟨spec.next⟩]

def Spec.formula (spec : Spec σ) : pred σ :=
  [tlafml| ⌜ spec.init ⌝ ∧ □ ⟨spec.next⟩ ∧ ⋀ a ∈ spec.fair, 𝒲ℱ a]

/-- The safety specification with stuttering: □[Next]_vars instead of □⟨Next⟩.
    This allows steps where the state doesn't change. -/
def Spec.safety_stutter (spec : Spec σ) : pred σ :=
  [tlafml| ⌜ spec.init ⌝ ∧ □ ⟨fun s s' => spec.next s s' ∨ s = s'⟩]

/-! ### Execution Mapping -/

def exec.map {σ : Type u} {τ : Type v} (f : σ → τ) (e : exec σ) : exec τ :=
  fun n => f (e n)

@[simp] theorem exec.map_apply {σ : Type u} {τ : Type v} (f : σ → τ) (e : exec σ) (n : Nat) :
    exec.map f e n = f (e n) := rfl

theorem exec.map_drop {σ : Type u} {τ : Type v} (f : σ → τ) (e : exec σ) (k : Nat) :
    (exec.map f e).drop k = exec.map f (e.drop k) := by
  funext n ; simp [exec.map, exec.drop]

theorem exec.map_comp {σ : Type u} {τ : Type v} {υ : Type w}
    (f : σ → τ) (g : τ → υ) (e : exec σ) :
    exec.map g (exec.map f e) = exec.map (g ∘ f) e := by
  funext n ; simp [exec.map]

/-! ### Refinement -/

/-- Concrete spec refines abstract spec via mapping `f`:
    every concrete behavior, mapped through `f`, is an abstract behavior. -/
def refines_via {σ : Type u} {τ : Type v}
    (f : σ → τ) (concrete : pred σ) (abstract : pred τ) : Prop :=
  ∀ e, concrete e → abstract (exec.map f e)

theorem refines_via_trans {σ : Type u} {τ : Type v} {υ : Type w}
    {f : σ → τ} {g : τ → υ} {p : pred σ} {q : pred τ} {r : pred υ}
    (h1 : refines_via f p q) (h2 : refines_via g q r) :
    refines_via (g ∘ f) p r := by
  intro e hp
  have hq := h1 e hp
  have hr := h2 (exec.map f e) hq
  rwa [exec.map_comp] at hr

/-! ### Helpers -/

/-- Extract `next (e k) (e (k+1))` from `□⟨next⟩`. -/
theorem always_action_at {σ : Type u} {next : action σ} {e : exec σ} (k : Nat)
    (h : e |=tla= □ ⟨next⟩) : next (e k) (e (k + 1)) := by
  have hk := h k
  simp [action_pred, exec.drop] at hk
  rwa [Nat.add_comm] at hk

/-- Key lemma: if every concrete step maps to an abstract step,
    then □⟨next_c⟩ on `e` implies □⟨next_a⟩ on `exec.map f e`. -/
private theorem map_always_next {σ : Type u} {τ : Type v}
    (next_c : action σ) (next_a : action τ)
    (f : σ → τ) (e : exec σ)
    (hn : e |=tla= □ ⟨next_c⟩)
    (hstep : ∀ s s', next_c s s' → next_a (f s) (f s')) :
    (exec.map f e) |=tla= □ ⟨next_a⟩ := by
  intro k
  rw [exec.map_drop]
  simp [action_pred, exec.drop, exec.map]
  rw [Nat.add_comm]
  exact hstep _ _ (always_action_at k hn)

private theorem map_always_next_or_stutter {σ : Type u} {τ : Type v}
    (next_c : action σ) (next_a : action τ)
    (f : σ → τ) (e : exec σ)
    (hn : e |=tla= □ ⟨next_c⟩)
    (hstep : ∀ s s', next_c s s' → next_a (f s) (f s') ∨ f s = f s') :
    (exec.map f e) |=tla= □ ⟨fun s s' => next_a s s' ∨ s = s'⟩ := by
  intro k
  rw [exec.map_drop]
  simp [action_pred, exec.drop, exec.map]
  rw [Nat.add_comm]
  exact hstep _ _ (always_action_at k hn)

/-- Variant with an invariant: the step condition may depend on an invariant. -/
private theorem map_always_next_inv {σ : Type u} {τ : Type v}
    (next_c : action σ) (next_a : action τ)
    (f : σ → τ) (e : exec σ)
    (inv : σ → Prop)
    (hinv : ∀ k, inv (e k))
    (hn : e |=tla= □ ⟨next_c⟩)
    (hstep : ∀ s s', inv s → next_c s s' → next_a (f s) (f s')) :
    (exec.map f e) |=tla= □ ⟨next_a⟩ := by
  intro k
  rw [exec.map_drop]
  simp [action_pred, exec.drop, exec.map]
  rw [Nat.add_comm]
  exact hstep _ _ (hinv k) (always_action_at k hn)

private theorem map_always_next_or_stutter_inv {σ : Type u} {τ : Type v}
    (next_c : action σ) (next_a : action τ)
    (f : σ → τ) (e : exec σ)
    (inv : σ → Prop)
    (hinv : ∀ k, inv (e k))
    (hn : e |=tla= □ ⟨next_c⟩)
    (hstep : ∀ s s', inv s → next_c s s' →
      next_a (f s) (f s') ∨ f s = f s') :
    (exec.map f e) |=tla= □ ⟨fun s s' => next_a s s' ∨ s = s'⟩ := by
  intro k
  rw [exec.map_drop]
  simp [action_pred, exec.drop, exec.map]
  rw [Nat.add_comm]
  exact hstep _ _ (hinv k) (always_action_at k hn)

/-! ### The Refinement Mapping Theorem (Safety, No Stuttering) -/

theorem refinement_mapping_nostutter {σ : Type u} {τ : Type v}
    (concrete : Spec σ) (abstract : Spec τ)
    (f : σ → τ)
    (hinit : ∀ s, concrete.init s → abstract.init (f s))
    (hnext : ∀ s s', concrete.next s s' → abstract.next (f s) (f s')) :
    refines_via f concrete.safety abstract.safety := by
  intro e ⟨hi, hn⟩
  exact ⟨hinit (e 0) hi, map_always_next _ _ f e hn hnext⟩

/-! ### The Refinement Mapping Theorem (Safety, With Stuttering) -/

theorem refinement_mapping_stutter {σ : Type u} {τ : Type v}
    (concrete : Spec σ) (abstract : Spec τ)
    (f : σ → τ)
    (hinit : ∀ s, concrete.init s → abstract.init (f s))
    (hnext : ∀ s s', concrete.next s s' →
      abstract.next (f s) (f s') ∨ f s = f s') :
    refines_via f concrete.safety abstract.safety_stutter := by
  intro e ⟨hi, hn⟩
  exact ⟨hinit (e 0) hi, map_always_next_or_stutter _ _ f e hn hnext⟩

/-! ### Refinement with Invariants -/

private theorem build_invariant {σ : Type u} {e : exec σ}
    {init : σ → Prop} {next : action σ} {inv : σ → Prop}
    (hi : e |=tla= ⌜ init ⌝) (hn : e |=tla= □ ⟨next⟩)
    (hinv_init : ∀ s, init s → inv s)
    (hinv_next : ∀ s s', inv s → next s s' → inv s') :
    ∀ k, inv (e k) := by
  intro k ; induction k with
  | zero => exact hinv_init _ hi
  | succ k ih => exact hinv_next _ _ ih (always_action_at k hn)

theorem refinement_mapping_with_invariant {σ : Type u} {τ : Type v}
    (concrete : Spec σ) (abstract : Spec τ)
    (f : σ → τ)
    (inv : σ → Prop)
    (hinv_init : ∀ s, concrete.init s → inv s)
    (hinv_next : ∀ s s', inv s → concrete.next s s' → inv s')
    (hinit : ∀ s, concrete.init s → abstract.init (f s))
    (hnext : ∀ s s', inv s → concrete.next s s' →
      abstract.next (f s) (f s')) :
    refines_via f concrete.safety abstract.safety := by
  intro e ⟨hi, hn⟩
  have hinv := build_invariant hi hn hinv_init hinv_next
  exact ⟨hinit (e 0) hi, map_always_next_inv _ _ f e _ hinv hn hnext⟩

theorem refinement_mapping_stutter_with_invariant {σ : Type u} {τ : Type v}
    (concrete : Spec σ) (abstract : Spec τ)
    (f : σ → τ)
    (inv : σ → Prop)
    (hinv_init : ∀ s, concrete.init s → inv s)
    (hinv_next : ∀ s s', inv s → concrete.next s s' → inv s')
    (hinit : ∀ s, concrete.init s → abstract.init (f s))
    (hnext : ∀ s s', inv s → concrete.next s s' →
      abstract.next (f s) (f s') ∨ f s = f s') :
    refines_via f concrete.safety abstract.safety_stutter := by
  intro e ⟨hi, hn⟩
  have hinv := build_invariant hi hn hinv_init hinv_next
  exact ⟨hinit (e 0) hi, map_always_next_or_stutter_inv _ _ f e _ hinv hn hnext⟩

/-! ### Safety and Safety-Stutter Relationship -/

/-- `safety` implies `safety_stutter`: every behavior satisfying Init ∧ □⟨Next⟩
    also satisfies Init ∧ □⟨Next ∨ id⟩. -/
theorem safety_implies_safety_stutter (spec : Spec σ) :
    pred_implies spec.safety spec.safety_stutter := by
  intro e ⟨hi, hn⟩
  exact ⟨hi, fun k => by have := hn k ; simp [action_pred, exec.drop] at * ; exact Or.inl this⟩

/-- Refinement mapping from `safety_stutter` to `safety_stutter`:
    if every concrete step (or stutter) maps to an abstract step or stutter,
    then stuttering safety refines stuttering safety. -/
theorem refinement_mapping_stutter_stutter {σ : Type u} {τ : Type v}
    (concrete : Spec σ) (abstract : Spec τ)
    (f : σ → τ)
    (hinit : ∀ s, concrete.init s → abstract.init (f s))
    (hnext : ∀ s s', concrete.next s s' →
      abstract.next (f s) (f s') ∨ f s = f s') :
    refines_via f concrete.safety_stutter abstract.safety_stutter := by
  intro e ⟨hi, hn⟩
  refine ⟨hinit (e 0) hi, ?_⟩
  intro k
  rw [exec.map_drop]
  simp only [action_pred, exec.drop, exec.map, Nat.zero_add]
  have hk := hn k
  simp only [action_pred, exec.drop, Nat.zero_add] at hk
  have hcomm : ∀ n, 1 + n = n + 1 := fun n => Nat.add_comm 1 n
  rw [hcomm] at hk ⊢
  rcases hk with hstep | heq
  · exact hnext _ _ hstep
  · exact Or.inr (congrArg f heq)

/-! ### Refinement Preserves Safety Properties -/

theorem refines_preserves_invariant {σ : Type u} {τ : Type v}
    (f : σ → τ) (spec_c : Spec σ) (spec_a : Spec τ)
    (inv : τ → Prop)
    (href : refines_via f spec_c.safety spec_a.safety)
    (hinv : pred_implies spec_a.safety [tlafml| □ ⌜ inv ⌝]) :
    pred_implies spec_c.safety [tlafml| □ ⌜ inv ∘ f ⌝] := by
  intro e hc
  have ha := href e hc
  have hall := hinv _ ha
  intro k
  have hk := hall k
  rw [exec.map_drop] at hk
  simp [state_pred, exec.drop, exec.map, Function.comp] at *
  exact hk

theorem refines_stutter_preserves_invariant {σ : Type u} {τ : Type v}
    (f : σ → τ) (spec_c : Spec σ) (spec_a : Spec τ)
    (inv : τ → Prop)
    (href : refines_via f spec_c.safety spec_a.safety_stutter)
    (hinv : pred_implies spec_a.safety_stutter [tlafml| □ ⌜ inv ⌝]) :
    pred_implies spec_c.safety [tlafml| □ ⌜ inv ∘ f ⌝] := by
  intro e hc
  have ha := href e hc
  have hall := hinv _ ha
  intro k
  have hk := hall k
  rw [exec.map_drop] at hk
  simp [state_pred, exec.drop, exec.map, Function.comp] at *
  exact hk

end TLA
