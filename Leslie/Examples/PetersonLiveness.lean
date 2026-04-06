import Leslie.Examples.Peterson
import Leslie.Rules.WF
import Leslie.Rules.LeadsTo

/-! ## Peterson's Algorithm: Starvation Freedom

    Under weak fairness of all 8 actions, if process 0 is waiting,
    it eventually enters the critical section.

    **Property**: `pc0 = .waiting ↝ pc0 = .cs`

    The proof proceeds in two stages:
    1. If pc1 = cs: WF(exit1) ensures pc1 leaves cs, which sets flag1 := false.
    2. If flag1 = false: WF(enter0) ensures process 0 enters cs.
-/

open TLA

namespace PetersonLiveness

open Peterson

/-! ### Fair specification -/

def petersonFair : ActionSpec PState PAction where
  init := peterson.init
  actions := peterson.actions
  fair := [.setFlag0, .setFlag1, .setTurn0, .setTurn1,
           .enter0, .enter1, .exit0, .exit1]

/-! ### Extract fairness components -/

private theorem extractNext (e : exec PState) (h : petersonFair.toSpec.formula e) :
    always (action_pred peterson.next) e := h.2.1

set_option linter.unusedSimpArgs false in
private theorem extractWF (e : exec PState) (h : petersonFair.toSpec.formula e)
    (a : PAction) : weak_fairness (peterson.actions a).toAction e := by
  have hwf := h.2.2
  simp only [petersonFair, ActionSpec.toSpec, Foldable.fold, tla_true] at hwf
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, _⟩ := hwf
  cases a <;> assumption

/-! ### Invariant -/

theorem always_inv :
    pred_implies petersonFair.toSpec.formula [tlafml| □ ⌜ inv ⌝] := by
  intro e hspec
  exact init_invariant inv_init
    (fun s s' hn hi => inv_next s s' hn hi) e ⟨hspec.1, extractNext e hspec⟩

/-! ### Stage 1: waiting0 ∧ pc1=cs ↝ waiting0 ∧ flag1=false

    When pc1=cs, only exit1 changes pc1, and it sets flag1:=false, pc1:=idle.
    No action can move pc0 from waiting to anything other than cs (via enter0),
    and enter0 requires flag1=false ∨ turn=false, but when pc1=cs, by inv,
    turn=true and flag1=true, so enter0 is disabled. -/

theorem cs1_leads_to_flag1_false :
    pred_implies petersonFair.toSpec.formula
      (leads_to
        (state_pred (fun s => s.pc0 = .waiting ∧ s.pc1 = .cs))
        (state_pred (fun s => s.pc0 = .waiting ∧ s.flag1 = false))) := by
  intro e hspec
  apply wf1
    (state_pred (fun s => s.pc0 = .waiting ∧ s.pc1 = .cs))
    (state_pred (fun s => s.pc0 = .waiting ∧ s.flag1 = false))
    peterson.next (peterson.actions .exit1).toAction e
  refine ⟨?_, ?_, ?_, extractNext e hspec, extractWF e hspec .exit1⟩
  · -- Safety: p ∧ ⟨next⟩ ⇒ ◯p ∨ ◯q
    -- Each non-exit1 action either has a contradictory gate or preserves pc0=waiting ∧ pc1=cs.
    -- exit1 transitions to pc1=idle, flag1=false, preserving pc0=waiting → q holds.
    sorry
  · -- Progress: exit1 fires → pc0=waiting (preserved), flag1=false (exit1 sets it)
    sorry
  · -- Enablement: exit1 is enabled when pc1=cs
    intro m hp
    simp only [state_pred, tla_enabled, exec.drop, tla_or, Nat.add_zero,
               GatedAction.toAction] at hp ⊢
    left
    exact ⟨{ (e m) with flag1 := false, pc1 := .idle },
      show (peterson.actions .exit1).fires (e m) _ from
        ⟨by simp [peterson, hp.2], by simp [peterson]⟩⟩

/-! ### Stage 2: waiting0 ∧ flag1=false ↝ cs0

    When flag1=false, enter0's gate `pc0=waiting ∧ (flag1=false ∨ turn=false)` holds.
    Under WF(enter0), enter0 fires → pc0=cs. -/

theorem flag1_false_leads_to_cs :
    pred_implies petersonFair.toSpec.formula
      (leads_to
        (state_pred (fun s => s.pc0 = .waiting ∧ s.flag1 = false))
        (state_pred (fun s => s.pc0 = .cs))) := by
  intro e hspec
  apply wf1
    (state_pred (fun s => s.pc0 = .waiting ∧ s.flag1 = false))
    (state_pred (fun s => s.pc0 = .cs))
    peterson.next (peterson.actions .enter0).toAction e
  refine ⟨?_, ?_, ?_, extractNext e hspec, extractWF e hspec .enter0⟩
  · -- Safety: flag1=false is preserved by all actions except setFlag1
    -- setFlag1 requires pc1=idle, and after setFlag1, pc1=flagged, so pc0 is still waiting
    -- But flag1 becomes true... this breaks p. However, enter0 has priority since flag1=false.
    -- Actually, setFlag1 CAN fire when flag1=false (its gate is pc1=idle).
    -- After setFlag1: flag1=true, pc1=flagged. Now p breaks and q doesn't hold.
    -- So this WF1 formulation is WRONG for this p: flag1=false is not preserved.
    -- Fix: use the invariant to observe that when pc0=waiting ∧ flag1=false,
    -- by inv, pc1=idle (flag1=false ↔ pc1=idle). So setFlag1 fires and flag1 becomes true.
    -- But enter0 is also enabled (flag1=false). Both are enabled simultaneously.
    -- WF1 safety says: p ∧ next ⇒ ◯p ∨ ◯q. If setFlag1 fires, neither p nor q.
    -- So we need p to be stronger: p = waiting ∧ flag1=false ∧ inv.
    -- With inv: flag1=false → pc1=idle. And pc0=waiting, pc1=idle.
    -- enter0 gate: pc0=waiting ∧ (flag1=false ∨ turn=false). YES, enabled.
    -- But setFlag1 also enabled (gate: pc1=idle).
    -- After setFlag1: flag1=true, pc1=flagged. pc0=waiting. Neither p nor q.
    -- WF1 doesn't work without p being preserved.
    -- Alternative: use p = waiting ∧ enter0.gate, which is inductive:
    -- enter0.gate = pc0=waiting ∧ (flag1=false ∨ turn=false)
    -- After setFlag1: flag1=true, turn unchanged. If turn=false, still p.
    -- If turn=true and flag1 was false before, after setFlag1 flag1=true turn=true: ¬p.
    -- So this ALSO doesn't work.
    -- The right approach: don't use WF1 with flag1=false. Instead, directly show
    -- that when pc0=waiting, eventually enter0 fires, using the full phase analysis.
    sorry
  · sorry
  · -- Enablement
    intro m hp
    simp only [state_pred, tla_enabled, exec.drop, tla_or, Nat.add_zero,
               GatedAction.toAction] at hp ⊢
    left
    exact ⟨{ (e m) with pc0 := .cs },
      show (peterson.actions .enter0).fires (e m) _ from
        ⟨by simp [peterson, hp.1, hp.2], by simp [peterson]⟩⟩

/-! ### Main theorem -/

theorem starvation_freedom_0 :
    pred_implies petersonFair.toSpec.formula
      (leads_to (state_pred (fun s => s.pc0 = .waiting))
                (state_pred (fun s => s.pc0 = .cs))) := by
  intro e hspec k hp
  have hinv := always_inv e hspec
  have hinv_k := hinv k
  simp only [state_pred, exec.drop, Nat.add_zero] at hp hinv_k
  by_cases hpc1_cs : (e k).pc1 = .cs
  · -- pc1=cs: Stage 1 gives flag1=false, then Stage 2 gives cs
    have h1 := cs1_leads_to_flag1_false e hspec k
      (show state_pred _ (e.drop k) by
        simp only [state_pred, exec.drop, Nat.add_zero]; exact ⟨hp, hpc1_cs⟩)
    obtain ⟨j1, hj1⟩ := h1
    -- hj1 : state_pred _ (e.drop (k + j1))
    -- = (e.drop j1 (e.drop k)) at exec.satisfies level
    -- We need it at (e.drop (k + j1))
    simp only [exec.drop_drop] at hj1
    have h2 := flag1_false_leads_to_cs e hspec (k + j1)
      (show state_pred _ (e.drop (k + j1)) from hj1)
    obtain ⟨j2, hj2⟩ := h2
    simp only [exec.drop_drop] at hj2
    exact ⟨j1 + j2, by simp only [exec.drop_drop]; rw [← Nat.add_assoc]; exact hj2⟩
  · -- pc1≠cs: by inv, either flag1=false (enter directly) or flag1=true
    by_cases hf1 : (e k).flag1 = false
    · exact flag1_false_leads_to_cs e hspec k
        (show state_pred _ (e.drop k) by
          simp only [state_pred, exec.drop, Nat.add_zero]; exact ⟨hp, hf1⟩)
    · -- flag1=true, pc1≠cs: process 1 is in {flagged, waiting}.
      -- Eventually process 1 either enters cs (then Stage 1+2) or
      -- turn becomes false (enabling enter0). Full argument is complex.
      sorry

end PetersonLiveness
