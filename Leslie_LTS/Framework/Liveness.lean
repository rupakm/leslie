import Leslie_LTS.Framework.Rules

/-! # Liveness and Fairness for LTS

    This module collects all liveness-related definitions and proof rules
    for labelled transition systems:

    * **Fairness**: weak fairness (justice) and strong fairness (compassion)
      for labels, matching the standard TLA definitions.
    * **Leads-to proof rules**: transitivity, disjunction elimination,
      strengthening via invariants, well-founded induction (lattice rule).
    * **WF1**: the core liveness proof rule — derive `p ↝ q` from a
      single fair action that makes progress.
-/

open Classical

namespace LTS

variable {State : Type u} {Label : Type v}

/-! ## Fairness Definitions -/

/-- **Weak fairness** (justice) for a label: if `l` is *continuously*
    enabled (enabled at every future step from some point onward), it
    eventually fires. This matches TLA's `WF(a)`:

    `□ ((□ Enabled l) → ◇ ⟨l fires⟩)`

    A single moment of being disabled resets the obligation. This is
    strictly weaker than strong fairness. -/
def weak_fairness (sys : System State Label) (l : Label) : TraceProp State Label :=
  always (tp_implies (always (state_prop (sys.enabled l)))
                     (eventually (step_prop (fun _ l' _ => l = l'))))

/-- **Strong fairness** (compassion) for a label: if `l` is enabled
    *infinitely often*, it eventually fires. This matches TLA's `SF(a)`:

    `□ ((□ ◇ Enabled l) → ◇ ⟨l fires⟩)`

    Unlike weak fairness, strong fairness requires progress even when
    enablement is intermittent — the label need not be continuously
    enabled, just recurrently so. -/
def strong_fairness (sys : System State Label) (l : Label) : TraceProp State Label :=
  always (tp_implies (always (eventually (state_prop (sys.enabled l))))
                     (eventually (step_prop (fun _ l' _ => l = l'))))

/-- Strong fairness implies weak fairness: continuous enablement
    (`□ Enabled l`) implies infinitely-often enablement
    (`□ ◇ Enabled l`), so the strong fairness obligation is
    strictly harder to avoid. -/
theorem strong_fairness_implies_weak (sys : System State Label) (l : Label) :
    tp_entails (strong_fairness sys l) (weak_fairness sys l) := by
  intro e k hsf j halways
  apply hsf j
  intro j'
  exact ⟨0, halways j'⟩

/-! ## Leads-to Proof Rules -/

/-- **Transitivity**: `(p ↝ q) ∧ (q ↝ r) → (p ↝ r)`. -/
theorem leads_to_trans (p q r : TraceProp State Label) :
    tp_entails (tp_and (leads_to p q) (leads_to q r)) (leads_to p r) := by
  intro e k ⟨hpq, hqr⟩ j hp
  obtain ⟨j₁, hq⟩ := hpq j hp
  -- hq : q e (k + j + j₁), need q e (k + (j + j₁)) for hqr
  have hq' : q e (k + (j + j₁)) := by
    rw [show k + (j + j₁) = k + j + j₁ from by omega]; exact hq
  obtain ⟨j₂, hr⟩ := hqr (j + j₁) hq'
  -- hr : r e (k + (j + j₁) + j₂), need r e (k + j + (j₁ + j₂))
  exact ⟨j₁ + j₂, by rw [show k + j + (j₁ + j₂) = k + (j + j₁) + j₂ from by omega]; exact hr⟩

/-- **Transitivity** (curried, under a hypothesis):
    `Γ → (p ↝ q)` and `Γ → (q ↝ r)` imply `Γ → (p ↝ r)`. -/
theorem leads_to_chain {Γ p q r : TraceProp State Label}
    (h1 : tp_entails Γ (leads_to p q))
    (h2 : tp_entails Γ (leads_to q r)) :
    tp_entails Γ (leads_to p r) :=
  fun e k hΓ => leads_to_trans p q r e k ⟨h1 e k hΓ, h2 e k hΓ⟩

/-- **Three-step chaining**: `Γ → (p ↝ q)` and `Γ → (q ↝ r)` and `Γ → (r ↝ s)`
    imply `Γ → (p ↝ s)`. -/
theorem leads_to_chain3 {Γ p q r s : TraceProp State Label}
    (h1 : tp_entails Γ (leads_to p q))
    (h2 : tp_entails Γ (leads_to q r))
    (h3 : tp_entails Γ (leads_to r s)) :
    tp_entails Γ (leads_to p s) :=
  leads_to_chain h1 (leads_to_chain h2 h3)

/-- **Disjunction elimination**: `Γ → (p₁ ↝ q)` and `Γ → (p₂ ↝ q)`
    imply `Γ → (p₁ ∨ p₂ ↝ q)`. -/
theorem leads_to_or {Γ p1 p2 q : TraceProp State Label}
    (h1 : tp_entails Γ (leads_to p1 q))
    (h2 : tp_entails Γ (leads_to p2 q)) :
    tp_entails Γ (leads_to (tp_or p1 p2) q) :=
  fun e k hΓ j hp => hp.elim (h1 e k hΓ j) (h2 e k hΓ j)

/-- **Reflexivity**: `⊨ p ↝ p`. -/
theorem leads_to_refl (p : TraceProp State Label) :
    tp_valid (leads_to p p) :=
  fun _e _k _j hp => ⟨0, hp⟩

/-- **Consequence rule**: `(p' → p) → (q → q') → Γ → (p ↝ q) → Γ → (p' ↝ q')`. -/
theorem leads_to_conseq {Γ p p' q q' : TraceProp State Label}
    (hleft : tp_entails p' p) (hright : tp_entails q q')
    (h : tp_entails Γ (leads_to p q)) :
    tp_entails Γ (leads_to p' q') :=
  fun e k hΓ j hp' => by
    obtain ⟨j', hq⟩ := h e k hΓ j (hleft e (k + j) hp')
    exact ⟨j', hright e (k + j + j') hq⟩

/-- **Invariant strengthening**: `Γ → □ inv` and `Γ → (p ∧ inv ↝ q)`
    imply `Γ → (p ↝ q)`. -/
theorem leads_to_strengthen_lhs {Γ p q inv : TraceProp State Label}
    (hinv : tp_entails Γ (always inv))
    (h : tp_entails Γ (leads_to (tp_and p inv) q)) :
    tp_entails Γ (leads_to p q) :=
  fun e k hΓ j hp =>
    h e k hΓ j ⟨hp, hinv e k hΓ j⟩

/-- **Combination**: `Γ → (p₁ ↝ q₁)` and `Γ → (p₂ ↝ q₂)` and
    `q₁ ∧ □Γ → □q₁` and `q₂ ∧ □Γ → □q₂`
    imply `Γ → (p₁ ∧ p₂ ↝ q₁ ∧ q₂)`.

    The stability conditions (`qᵢ ∧ □Γ → □qᵢ`) ensure that once
    each conclusion is achieved, it persists — so at
    `max(j₁, j₂)` both conclusions hold simultaneously. -/
theorem leads_to_combine {Γ p₁ q₁ p₂ q₂ : TraceProp State Label}
    (h1 : tp_entails (always Γ) (leads_to p₁ q₁))
    (h2 : tp_entails (always Γ) (leads_to p₂ q₂))
    (hstable1 : ∀ e k, q₁ e k → (∀ j, Γ e (k + j)) → ∀ j, q₁ e (k + j))
    (hstable2 : ∀ e k, q₂ e k → (∀ j, Γ e (k + j)) → ∀ j, q₂ e (k + j)) :
    tp_entails (always Γ) (leads_to (tp_and p₁ p₂) (tp_and q₁ q₂)) := by
  intro e k hΓ j ⟨hp₁, hp₂⟩
  -- Get q₁ at some future offset j₁
  obtain ⟨j₁, hq₁⟩ := h1 e k hΓ j hp₁
  -- Get q₂ at some future offset j₂
  obtain ⟨j₂, hq₂⟩ := h2 e k hΓ j hp₂
  -- At max(j₁, j₂), both hold by stability.
  -- Use j₁ + j₂ as the common offset (both q₁ and q₂ persist).
  refine ⟨j₁ + j₂, ?_, ?_⟩
  · -- q₁ persists from (k + j + j₁) to (k + j + j₁ + j₂)
    have hΓ_from : ∀ i, Γ e (k + j + j₁ + i) := fun i => by
      rw [show k + j + j₁ + i = k + (j + j₁ + i) from by omega]; exact hΓ (j + j₁ + i)
    have := hstable1 e (k + j + j₁) hq₁ hΓ_from j₂
    rw [show k + j + (j₁ + j₂) = k + j + j₁ + j₂ from by omega]
    exact this
  · -- q₂ persists from (k + j + j₂) to (k + j + j₂ + j₁)
    have hΓ_from : ∀ i, Γ e (k + j + j₂ + i) := fun i => by
      rw [show k + j + j₂ + i = k + (j + j₂ + i) from by omega]; exact hΓ (j + j₂ + i)
    have := hstable2 e (k + j + j₂) hq₂ hΓ_from j₁
    rw [show k + j + (j₁ + j₂) = k + j + j₂ + j₁ from by omega]
    exact this

/-- **Combination (split hypothesis)**: `□Γ ∧ Γ' → (p₁ ↝ q₁)` and `□Γ ∧ Γ' → (p₂ ↝ q₂)`
    and `q₁ ∧ □Γ → □q₁` and `q₂ ∧ □Γ → □q₂`
    imply `□Γ ∧ Γ' → (p₁ ∧ p₂ ↝ q₁ ∧ q₂)`.

    This variant splits the hypothesis into a persistent part `Γ`
    (under `□`) and a one-shot part `Γ'` (e.g., fairness assumptions).
    The stability conditions only require the persistent `□Γ`. -/
theorem leads_to_combine' {Γ Γ' p₁ q₁ p₂ q₂ : TraceProp State Label}
    (h1 : tp_entails (tp_and (always Γ) Γ') (leads_to p₁ q₁))
    (h2 : tp_entails (tp_and (always Γ) Γ') (leads_to p₂ q₂))
    (hstable1 : ∀ e k, q₁ e k → (∀ j, Γ e (k + j)) → ∀ j, q₁ e (k + j))
    (hstable2 : ∀ e k, q₂ e k → (∀ j, Γ e (k + j)) → ∀ j, q₂ e (k + j)) :
    tp_entails (tp_and (always Γ) Γ') (leads_to (tp_and p₁ p₂) (tp_and q₁ q₂)) := by
  intro e k ⟨hΓ, hΓ'⟩ j ⟨hp₁, hp₂⟩
  obtain ⟨j₁, hq₁⟩ := h1 e k ⟨hΓ, hΓ'⟩ j hp₁
  obtain ⟨j₂, hq₂⟩ := h2 e k ⟨hΓ, hΓ'⟩ j hp₂
  refine ⟨j₁ + j₂, ?_, ?_⟩
  · have hΓ_from : ∀ i, Γ e (k + j + j₁ + i) := fun i => by
      rw [show k + j + j₁ + i = k + (j + j₁ + i) from by omega]; exact hΓ (j + j₁ + i)
    have := hstable1 e (k + j + j₁) hq₁ hΓ_from j₂
    rw [show k + j + (j₁ + j₂) = k + j + j₁ + j₂ from by omega]
    exact this
  · have hΓ_from : ∀ i, Γ e (k + j + j₂ + i) := fun i => by
      rw [show k + j + j₂ + i = k + (j + j₂ + i) from by omega]; exact hΓ (j + j₂ + i)
    have := hstable2 e (k + j + j₂) hq₂ hΓ_from j₁
    rw [show k + j + (j₁ + j₂) = k + j + j₂ + j₁ from by omega]
    exact this

/-! ## Well-Founded Induction for Leads-to -/

/-- **Well-founded induction** for leads-to using a `ℕ`-valued measure.
    If for every `m > 0`, `p ∧ (μ = m)` leads to `q ∨ (p ∧ μ < m)`,
    and `p ∧ (μ = 0)` leads to `q`, then `p ↝ q`.

    This is the standard TLA lattice rule (Lamport): each step either
    achieves `q` or makes progress toward it by decreasing the measure.

    The step and base conditions are stated at arbitrary positions,
    avoiding the need for a hypothesis `Γ` to hold at intermediate
    points. Use `leads_to_strengthen_lhs` to incorporate invariants. -/
theorem leads_to_wf {p q : TraceProp State Label}
    (μ : Execution State Label → Nat → Nat)
    (hstep : ∀ m : Nat, m > 0 →
      ∀ e n, p e n → μ e n = m →
        ∃ j, q e (n + j) ∨ (p e (n + j) ∧ μ e (n + j) < m))
    (hbase : ∀ e n, p e n → μ e n = 0 → ∃ j, q e (n + j)) :
    tp_valid (leads_to p q) := by
  intro e k j hp
  -- Goal: ∃ j', q e (k + j + j')
  show ∃ j', q e (k + j + j')
  suffices h : ∀ bound, μ e (k + j) ≤ bound → ∃ j', q e (k + j + j') from
    h (μ e (k + j)) (Nat.le_refl _)
  intro bound
  induction bound generalizing j with
  | zero =>
    intro hle
    exact hbase e (k + j) hp (Nat.le_zero.mp hle)
  | succ m ih =>
    intro hle
    by_cases hm : μ e (k + j) = 0
    · exact hbase e (k + j) hp hm
    · obtain ⟨j', hj'⟩ := hstep (μ e (k + j)) (Nat.pos_of_ne_zero hm) e (k + j) hp rfl
      rcases hj' with hq | ⟨hp', hlt⟩
      · exact ⟨j', hq⟩
      · have hle' : μ e (k + j + j') ≤ m := by omega
        obtain ⟨j'', hq⟩ := ih (j + j') (by
          rw [show k + (j + j') = k + j + j' from by omega]; exact hp') (by
          rw [show k + (j + j') = k + j + j' from by omega]; exact hle')
        exact ⟨j' + j'', by rw [show k + j + (j' + j'') = k + (j + j') + j'' from by omega]; exact hq⟩

/-- **Lexicographic well-founded induction** for leads-to using two
    `ℕ`-valued measures `(μ₁, μ₂)`. Each step either achieves `q`,
    decreases `μ₁`, or keeps `μ₁` the same and decreases `μ₂`.

    This generalizes `leads_to_wf` to lexicographic orderings,
    useful when progress on one dimension can reset the other. -/
theorem leads_to_wf_lex {p q : TraceProp State Label}
    (μ₁ μ₂ : Execution State Label → Nat → Nat)
    (hstep : ∀ m₁ m₂ : Nat, (m₁ > 0 ∨ m₂ > 0) →
      ∀ e n, p e n → μ₁ e n = m₁ → μ₂ e n = m₂ →
        ∃ j, q e (n + j) ∨
          (p e (n + j) ∧
            (μ₁ e (n + j) < m₁ ∨
              (μ₁ e (n + j) = m₁ ∧ μ₂ e (n + j) < m₂))))
    (hbase : ∀ e n, p e n → μ₁ e n = 0 → μ₂ e n = 0 →
        ∃ j, q e (n + j)) :
    tp_valid (leads_to p q) := by
  -- Reduce to leads_to_wf on μ₁; for each fixed μ₁, inner induction on μ₂.
  apply leads_to_wf μ₁
  · -- Outer step: μ₁ = m₁ > 0
    intro m₁ hm₁ e n hp hμ₁
    -- Inner: show ∃ j, q (n+j) ∨ (p (n+j) ∧ μ₁ (n+j) < m₁) by induction on μ₂
    suffices h : ∀ bound, μ₂ e n ≤ bound →
        ∃ j, q e (n + j) ∨ (p e (n + j) ∧ μ₁ e (n + j) < m₁) from
      h (μ₂ e n) (Nat.le_refl _)
    intro bound
    induction bound generalizing n with
    | zero =>
      intro hle
      have hμ₂ : μ₂ e n = 0 := Nat.le_zero.mp hle
      obtain ⟨j, hj⟩ := hstep m₁ 0 (Or.inl hm₁) e n hp hμ₁ hμ₂
      rcases hj with hq | ⟨hp', hlt⟩
      · exact ⟨j, Or.inl hq⟩
      · rcases hlt with hlt₁ | ⟨_, hlt₂⟩
        · exact ⟨j, Or.inr ⟨hp', hlt₁⟩⟩
        · omega
    | succ m ih =>
      intro hle
      by_cases hμ₂ : μ₂ e n = 0
      · obtain ⟨j, hj⟩ := hstep m₁ 0 (Or.inl hm₁) e n hp hμ₁ hμ₂
        rcases hj with hq | ⟨hp', hlt⟩
        · exact ⟨j, Or.inl hq⟩
        · rcases hlt with hlt₁ | ⟨_, hlt₂⟩
          · exact ⟨j, Or.inr ⟨hp', hlt₁⟩⟩
          · omega
      · obtain ⟨j, hj⟩ := hstep m₁ (μ₂ e n)
          (Or.inr (Nat.pos_of_ne_zero hμ₂)) e n hp hμ₁ rfl
        rcases hj with hq | ⟨hp', hlt⟩
        · exact ⟨j, Or.inl hq⟩
        · rcases hlt with hlt₁ | ⟨heq₁, hlt₂⟩
          · exact ⟨j, Or.inr ⟨hp', hlt₁⟩⟩
          · have hle' : μ₂ e (n + j) ≤ m := by omega
            obtain ⟨j', hj'⟩ := ih (n + j) hp' heq₁ hle'
            exact ⟨j + j', by rw [show n + (j + j') = n + j + j' from by omega]; exact hj'⟩
  · -- Outer base: μ₁ = 0. Inner induction on μ₂.
    intro e n hp hμ₁
    suffices h : ∀ bound, μ₂ e n ≤ bound → ∃ j, q e (n + j) from
      h (μ₂ e n) (Nat.le_refl _)
    intro bound
    induction bound generalizing n with
    | zero =>
      intro hle
      exact hbase e n hp hμ₁ (Nat.le_zero.mp hle)
    | succ m ih =>
      intro hle
      by_cases hμ₂ : μ₂ e n = 0
      · exact hbase e n hp hμ₁ hμ₂
      · obtain ⟨j, hj⟩ := hstep 0 (μ₂ e n)
          (Or.inr (Nat.pos_of_ne_zero hμ₂)) e n hp hμ₁ rfl
        rcases hj with hq | ⟨hp', hlt⟩
        · exact ⟨j, hq⟩
        · rcases hlt with hlt₁ | ⟨heq₁, hlt₂⟩
          · omega
          · have hle' : μ₂ e (n + j) ≤ m := by omega
            obtain ⟨j', hq⟩ := ih (n + j) hp' heq₁ hle'
            exact ⟨j + j', by rw [show n + (j + j') = n + j + j' from by omega]; exact hq⟩

/-! ## WF1 — Core Liveness Proof Rule -/

/-- Structured premises for the WF1 rule. Using a structure avoids
    positional destructuring and makes each obligation named. -/
structure WF1Premises (sys : System State Label)
    (p q : TraceProp State Label) (l : Label) (e : Execution State Label) : Prop where
  /-- The execution is valid. -/
  valid : sys.valid_exec e
  /-- Weak fairness for label `l`. -/
  fair : weak_fairness sys l e 0
  /-- Safety: if `p` holds and a step fires, then `p` or `q` holds next. -/
  safety : ∀ k, p e k →
    sys.step (e.states k) (e.labels k) (e.states (k + 1)) →
    p e (k + 1) ∨ q e (k + 1)
  /-- Progress: if `p` holds and label `l` fires, then `q` holds next. -/
  progress : ∀ k, p e k →
    sys.step (e.states k) (e.labels k) (e.states (k + 1)) →
    e.labels k = l → q e (k + 1)
  /-- Enablement: if `p` holds, then `l` is enabled or `q` holds. -/
  enablement : ∀ k, p e k → sys.enabled l (e.states k) ∨ q e k

/-- **WF1 rule** for labelled transition systems.

    Derive `p ↝ q` from a single weakly-fair label `l` that makes progress.
    The four obligations are:

    1. **Safety**: if `p` holds and any valid step fires, then `p` or `q`
       holds in the next state.
    2. **Progress**: if `p` holds and label `l` fires, then `q` holds in
       the next state.
    3. **Enablement**: if `p` holds, then either `l` is enabled or `q`
       already holds.
    4. **Fairness**: the execution is valid and satisfies `WF(l)`. -/
theorem wf1 {sys : System State Label}
    {p q : TraceProp State Label} {l : Label} {e : Execution State Label}
    (h : WF1Premises sys p q l e) : leads_to p q e 0 := by
  intro j hp
  simp only [Nat.zero_add] at hp ⊢
  -- hp : p e j, goal : ∃ j', q e (j + j')
  -- Case: q already holds at j.
  by_cases hq_now : q e j
  · exact ⟨0, by simpa using hq_now⟩
  · -- q doesn't hold at j. Walk forward: p persists until q or l fires.
    -- Claim: p holds at all positions in [j..j+n] unless q appears earlier.
    have p_persists : ∀ n, (∀ i, i < n → ¬q e (j + i + 1)) →
        (∀ i, i ≤ n → p e (j + i)) := by
      intro n hnoq i hi
      induction i with
      | zero => simpa using hp
      | succ i ih =>
        have hp_i := ih (by omega)
        rcases h.safety (j + i) hp_i (h.valid.2 (j + i)) with hp_next | hq_next
        · rwa [show j + i + 1 = j + (i + 1) from by omega] at hp_next
        · exfalso
          exact hnoq i (by omega) (by rwa [show j + i + 1 = j + (i + 1) from by omega])
    -- Either q eventually appears, or p holds forever.
    by_cases hq_event : ∃ n, q e (j + n)
    · obtain ⟨n, hqn⟩ := hq_event
      exact ⟨n, hqn⟩
    · -- q never appears. Then p holds forever.
      have hq_all : ∀ n, ¬q e (j + n) := fun n hq => hq_event ⟨n, hq⟩
      have p_always : ∀ i, p e (j + i) := by
        intro i
        exact p_persists i
          (fun k _ => by rw [show j + k + 1 = j + (k + 1) from by omega]; exact hq_all (k + 1))
          i (Nat.le_refl _)
      -- By enablement, l is always enabled (since q never holds).
      have enabled_always : ∀ i, sys.enabled l (e.states (j + i)) := by
        intro i
        rcases h.enablement (j + i) (p_always i) with hen | hq
        · exact hen
        · exact absurd hq (hq_all i)
      -- Apply weak fairness at position j.
      have hwf_j := h.fair j
      simp only [Nat.zero_add] at hwf_j
      obtain ⟨n, hfire⟩ := hwf_j enabled_always
      -- l fires at position j + n, so by hprogress, q holds at j + n + 1
      -- hfire : step_prop (fun _ l' _ => l = l') e (j + n), i.e., l = e.labels (j + n)
      have hfire' : e.labels (j + n) = l := by exact hfire.symm
      have hq_next := h.progress (j + n) (p_always n) (h.valid.2 (j + n)) hfire'
      show ∃ j', q e (j + j')
      exact ⟨n + 1, by rw [show j + (n + 1) = j + n + 1 from by omega]; exact hq_next⟩

/-! ## Fairness Alternative Characterizations -/

/-- **Weak fairness alternative characterization**:
    `WF(l) ↔ □◇(¬Enabled l ∨ l fires)`.

    Weak fairness is equivalent to: infinitely often, either `l` is
    disabled or `l` fires. -/
theorem weak_fairness_iff_alt (sys : System State Label) (l : Label)
    (e : Execution State Label) (k : Nat) :
    weak_fairness sys l e k ↔
      always (eventually (tp_or
        (tp_not (state_prop (sys.enabled l)))
        (step_prop (fun _ l' _ => l = l')))) e k := by
  constructor
  · -- (⇒) WF(l) → □◇(¬Enabled l ∨ l fires)
    intro hwf j
    show ∃ j', tp_or (tp_not (state_prop (sys.enabled l)))
      (step_prop (fun _ l' _ => l = l')) e (k + j + j')
    by_cases hen : ∀ j', sys.enabled l (e.states (k + j + j'))
    · obtain ⟨n, hfire⟩ := hwf j hen
      exact ⟨n, Or.inr hfire⟩
    · have ⟨n, hn⟩ := Classical.not_forall.mp hen
      exact ⟨n, Or.inl hn⟩
  · -- (⇐) □◇(¬Enabled l ∨ l fires) → WF(l)
    -- Assume □◇(¬Enabled l ∨ l fires) and □(Enabled l) from some point.
    -- Each occurrence of ¬Enabled contradicts □(Enabled), so only
    -- "l fires" witnesses survive — giving ◇(l fires).
    intro halt j hen
    -- halt : ∀ j', ∃ j'', (¬enabled ∨ fires) at (k + j' + j'')
    -- hen  : ∀ j', enabled at (k + j + j')
    -- Goal : ∃ j', fires at (k + j + j')
    obtain ⟨n, hn⟩ := halt j
    rcases hn with hdis | hfire
    · -- ¬Enabled at (k + j + n) contradicts hen
      exact absurd (hen n) hdis
    · exact ⟨n, hfire⟩

end LTS
