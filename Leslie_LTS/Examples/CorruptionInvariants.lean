import Leslie_LTS.Framework

/-! # Generic corruption invariants for Byzantine protocols

  Any LTS where the corrupted list grows by at most one element per step
  (on corrupt steps) and stays unchanged otherwise gets `corrupted_budget`
  and `corrupted_nodup` for free.
-/

open LTS

namespace CorruptionInvariants

variable {State Label : Type} {n : Nat}

/-- A system has standard corruption behaviour. -/
structure CorruptionSpec (sys : System State Label) (corrupted : State → List (Fin n)) (f : Nat)
  where
  init_empty : ∀ s, sys.init s → corrupted s = []
  step_corrupted : ∀ s l s', sys.step s l s' →
    corrupted s' = corrupted s ∨
    (∃ i, corrupted s' = i :: corrupted s ∧ i ∉ corrupted s ∧ (corrupted s).length + 1 ≤ f)

/-- The corrupted list length stays within budget in any reachable state. -/
theorem corrupted_budget {sys : System State Label} {corrupted : State → List (Fin n)} {f : Nat}
    (spec : CorruptionSpec sys corrupted f)
    {s : State} (hreach : Reachable sys s) :
    (corrupted s).length ≤ f := by
  induction hreach with
  | init hinit => rw [spec.init_empty _ hinit]; simp
  | step _ hstep ih =>
    rcases spec.step_corrupted _ _ _ hstep with heq | ⟨_, heq, _, hbudget⟩
    · rwa [heq]
    · rw [heq, List.length_cons]; omega

/-- The corrupted list is always nodup in any reachable state. -/
theorem corrupted_nodup {sys : System State Label} {corrupted : State → List (Fin n)} {f : Nat}
    (spec : CorruptionSpec sys corrupted f)
    {s : State} (hreach : Reachable sys s) :
    (corrupted s).Nodup := by
  induction hreach with
  | init hinit => rw [spec.init_empty _ hinit]; exact List.nodup_nil
  | step _ hstep ih =>
    rcases spec.step_corrupted _ _ _ hstep with heq | ⟨_, heq, hni, _⟩
    · rwa [heq]
    · rw [heq]; exact List.nodup_cons.mpr ⟨hni, ih⟩

end CorruptionInvariants
