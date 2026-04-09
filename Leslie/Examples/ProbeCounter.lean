import Leslie.Refinement
import Leslie.Rules.WF
import Leslie.Rules.LeadsTo

/-! ## Probe Counter Liveness: Validating leads_to_via_nat

    A simple countdown protocol: state is a Nat counter.
    One fair action decrements the counter (if > 0).
    Under weak fairness, the counter eventually reaches 0.

    **Property**: `counter > 0 ↝ counter = 0`

    This validates the `leads_to_via_nat` well-founded induction rule.
    The pattern transfers to TileLink's probing_leads_to_grantReady proof
    (where the "counter" is |{j | probesRemaining j = true}|).
-/

open TLA

namespace ProbeCounter

/-! ### Spec: state = Nat, action = decrement -/

def decrement (s s' : Nat) : Prop := s > 0 ∧ s' = s - 1

def countdownSpec : Spec Nat where
  init := fun s => True
  next := decrement
  fair := [decrement]

/-! ### Basic lemmas -/

theorem decrement_enabled_of_pos {s : Nat} (h : s > 0) : enabled decrement s :=
  ⟨s - 1, h, rfl⟩

theorem decrement_decreases {s s' : Nat} (h : decrement s s') : s' < s := by
  rcases h with ⟨hpos, hs'⟩; omega

/-! ### Main theorem using leads_to_via_nat

    Property: counter > 0 ↝ counter = 0.
    Measure: the counter value itself.
    Each decrement step decreases the measure by 1. -/

theorem countdown_reaches_zero :
    pred_implies countdownSpec.formula
      (leads_to (state_pred (fun s : Nat => s > 0))
                (state_pred (fun s : Nat => s = 0))) := by
  -- Use leads_to_via_nat with μ = state value
  apply leads_to_via_nat (fun e => e 0)
  · -- Step case: k > 0, counter = k ↝ (counter = 0) ∨ (counter > 0 ∧ counter < k)
    intro k hk e ⟨_, hnext, hwf⟩ i hp hμ
    -- Extract WF(decrement) from fairness
    have hwf : weak_fairness decrement e := by
      simp only [countdownSpec, tla_bigwedge, Foldable.fold, tla_true] at hwf
      exact hwf.1
    -- Use WF1 on the original execution to get one decrement step
    -- WF1 gives: (counter > 0 ∧ counter = k) ↝ (counter = 0 ∨ (counter > 0 ∧ counter < k))
    have h1 : leads_to
        (fun e => e 0 > 0 ∧ e 0 = k)
        (fun e => e 0 = 0 ∨ (e 0 > 0 ∧ e 0 < k))
        e := by
      apply wf1 _ _ decrement decrement e
      refine ⟨?_, ?_, ?_, hnext, hwf⟩
      · -- Safety: p ∧ next → ◯p ∨ ◯q. After decrement, counter changes → always ◯q.
        intro m ⟨⟨hp', hcount⟩, hstep⟩
        simp only [action_pred, exec.drop, later, Nat.add_zero, tla_or, decrement] at *
        rcases hstep with ⟨hpos, hs'⟩
        right
        by_cases h0 : e m - 1 = 0
        · left; rw [hs']; exact h0
        · right; rw [hs', hcount]; omega
      · -- Progress: p ∧ next ∧ a → ◯q
        intro m ⟨⟨hp', hcount⟩, _, hstep⟩
        simp only [action_pred, exec.drop, later, Nat.add_zero, tla_or, decrement] at *
        rcases hstep with ⟨hpos, hs'⟩
        by_cases h0 : e m - 1 = 0
        · left; rw [hs']; exact h0
        · right; constructor
          · rw [hs']; omega
          · rw [hs', hcount]; omega
      · -- Enablement: p → Enabled a ∨ q
        intro m ⟨hp', _⟩
        simp only [tla_enabled, tla_or, exec.drop] at *
        left; exact decrement_enabled_of_pos hp'
    -- Apply leads_to at position i
    obtain ⟨j, hj⟩ := h1 i ⟨hp, hμ⟩
    simp only [exec.drop_drop] at hj
    rcases hj with hq | ⟨hp'', hlt⟩
    · exact ⟨j, Or.inl hq⟩
    · exact ⟨j, Or.inr ⟨hp'', hlt⟩⟩
  · -- Base case: counter = 0 → counter > 0 is false → contradiction
    intro e _ i hp hμ
    -- hp : (e.drop i) 0 > 0, hμ : (e.drop i) 0 = 0 → contradiction
    simp only [state_pred, exec.drop] at hp hμ
    omega

end ProbeCounter
