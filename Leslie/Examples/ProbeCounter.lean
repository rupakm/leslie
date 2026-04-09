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
  init := fun _s => True
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

/-! ## Variant 1: Stutter + Decrement

    Two actions: `stutter` (s' = s) and `decrement` (s' = s - 1).
    The combined next-step is their disjunction. Only `decrement` is fair.
    Stutter steps can happen arbitrarily often but don't block progress.

    **Property**: `counter > 0 ↝ counter = 0`

    This is closer to TileLink where many actions leave the probe count
    unchanged and only specific actions (recvProbeAck) decrease it. -/

namespace StutterDecrement

def stutter (s s' : Nat) : Prop := s' = s
def decrement (s s' : Nat) : Prop := s > 0 ∧ s' = s - 1
def next (s s' : Nat) : Prop := stutter s s' ∨ decrement s s'

def spec : Spec Nat where
  init := fun _ => True
  next := next
  fair := [decrement]  -- only decrement is fair; stutter can starve

theorem decrement_enabled_of_pos {s : Nat} (h : s > 0) : enabled decrement s :=
  ⟨s - 1, h, rfl⟩

theorem countdown_reaches_zero :
    pred_implies spec.formula
      (leads_to (state_pred (fun s : Nat => s > 0))
                (state_pred (fun s : Nat => s = 0))) := by
  apply leads_to_via_nat (fun e => e 0)
  · -- Step case: k > 0
    intro k hk e ⟨_, hnext, hwf⟩ i hp hμ
    have hwf : weak_fairness decrement e := by
      simp only [spec, tla_bigwedge, Foldable.fold, tla_true] at hwf; exact hwf.1
    -- WF1 with next = stutter ∨ decrement, fair action = decrement
    have h1 : leads_to
        (fun e => e 0 > 0 ∧ e 0 = k)
        (fun e => e 0 = 0 ∨ (e 0 > 0 ∧ e 0 < k))
        e := by
      apply wf1 _ _ next decrement e
      refine ⟨?_, ?_, ?_, hnext, hwf⟩
      · -- Safety: stutter preserves p; decrement gives q
        intro m ⟨⟨hp', hcount⟩, hstep⟩
        simp only [action_pred, exec.drop, later, Nat.add_zero, tla_or, next] at *
        rcases hstep with hstut | hdec
        · -- Stutter: s' = s → p preserved
          left; rw [stutter] at hstut; rw [hstut]; exact ⟨hp', hcount⟩
        · -- Decrement: counter changes → q
          right; rcases hdec with ⟨hpos, hs'⟩
          by_cases h0 : e m - 1 = 0
          · left; rw [hs']; exact h0
          · right; rw [hs', hcount]; omega
      · -- Progress: decrement fires → q
        intro m ⟨⟨hp', hcount⟩, _, hstep⟩
        simp only [action_pred, exec.drop, later, Nat.add_zero, tla_or, decrement] at *
        rcases hstep with ⟨hpos, hs'⟩
        by_cases h0 : e m - 1 = 0
        · left; rw [hs']; exact h0
        · right; rw [hs', hcount]; omega
      · -- Enablement: counter > 0 → decrement enabled
        intro m ⟨hp', _⟩
        simp only [tla_enabled, tla_or, exec.drop] at *
        left; exact decrement_enabled_of_pos hp'
    obtain ⟨j, hj⟩ := h1 i ⟨hp, hμ⟩
    simp only [exec.drop_drop] at hj
    rcases hj with hq | ⟨hp'', hlt⟩
    · exact ⟨j, Or.inl hq⟩
    · exact ⟨j, Or.inr ⟨hp'', hlt⟩⟩
  · -- Base case
    intro e _ i hp hμ
    simp only [state_pred, exec.drop] at hp hμ; omega

end StutterDecrement

/-! ## Variant 2: Non-deterministic Decrement

    Single action: decrement by a non-deterministically chosen amount
    (any d with 1 ≤ d ≤ s). Under weak fairness, the counter reaches 0.

    **Property**: `counter > 0 ↝ counter = 0`

    This models TileLink scenarios where a single action might consume
    multiple probes at once (e.g., if the model batched probe processing). -/

namespace NondetDecrement

def ndDecrement (s s' : Nat) : Prop := ∃ d, d ≥ 1 ∧ d ≤ s ∧ s' = s - d

def spec : Spec Nat where
  init := fun _ => True
  next := ndDecrement
  fair := [ndDecrement]

theorem ndDecrement_enabled_of_pos {s : Nat} (h : s > 0) : enabled ndDecrement s :=
  ⟨s - 1, 1, by omega, by omega, by omega⟩

theorem ndDecrement_decreases {s s' : Nat} (h : ndDecrement s s') : s' < s := by
  obtain ⟨d, hd1, hd2, hs'⟩ := h; omega

theorem countdown_reaches_zero :
    pred_implies spec.formula
      (leads_to (state_pred (fun s : Nat => s > 0))
                (state_pred (fun s : Nat => s = 0))) := by
  apply leads_to_via_nat (fun e => e 0)
  · -- Step case: k > 0
    intro k hk e ⟨_, hnext, hwf⟩ i hp hμ
    have hwf : weak_fairness ndDecrement e := by
      simp only [spec, tla_bigwedge, Foldable.fold, tla_true] at hwf; exact hwf.1
    have h1 : leads_to
        (fun e => e 0 > 0 ∧ e 0 = k)
        (fun e => e 0 = 0 ∨ (e 0 > 0 ∧ e 0 < k))
        e := by
      apply wf1 _ _ ndDecrement ndDecrement e
      refine ⟨?_, ?_, ?_, hnext, hwf⟩
      · -- Safety: ndDecrement gives q (may jump past 0 or land exactly)
        intro m ⟨⟨hp', hcount⟩, hstep⟩
        simp only [action_pred, exec.drop, later, Nat.add_zero, tla_or, ndDecrement] at *
        obtain ⟨d, hd1, hd2, hs'⟩ := hstep
        right
        by_cases h0 : e m - d = 0
        · left; rw [hs']; exact h0
        · right; rw [hs', hcount]; omega
      · -- Progress: same as safety (single action)
        intro m ⟨⟨hp', hcount⟩, _, hstep⟩
        simp only [action_pred, exec.drop, later, Nat.add_zero, tla_or, ndDecrement] at *
        obtain ⟨d, hd1, hd2, hs'⟩ := hstep
        by_cases h0 : e m - d = 0
        · left; rw [hs']; exact h0
        · right; rw [hs', hcount]; omega
      · -- Enablement
        intro m ⟨hp', _⟩
        simp only [tla_enabled, tla_or, exec.drop] at *
        left; exact ndDecrement_enabled_of_pos hp'
    obtain ⟨j, hj⟩ := h1 i ⟨hp, hμ⟩
    simp only [exec.drop_drop] at hj
    rcases hj with hq | ⟨hp'', hlt⟩
    · exact ⟨j, Or.inl hq⟩
    · exact ⟨j, Or.inr ⟨hp'', hlt⟩⟩
  · -- Base case
    intro e _ i hp hμ
    simp only [state_pred, exec.drop] at hp hμ; omega

end NondetDecrement
