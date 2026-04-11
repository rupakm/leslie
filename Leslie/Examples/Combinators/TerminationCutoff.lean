import Leslie.Cutoff
import Leslie.Examples.Combinators.QuorumSystem

/-! ## Cutoff Theorem for Termination

    The safety cutoff transfers invariants: if `inv` holds for n ≤ K, it
    holds for all n. Can we transfer *termination*?

    **Result**: For TV-deterministic protocols (successor threshold view
    determined by current threshold view alone), termination within T rounds
    transfers across n with the SAME bound T and the SAME cutoff K.

    **Key condition**: `tvDeterministic` — two configs with the same threshold
    view produce successors with the same threshold view. This holds for
    protocols where above-threshold values are absorbing (OneThirdRule,
    ThresholdConsensus, any consensus where decided states don't change).
-/

open TLA

namespace TLA.TerminationCutoff

/-! ### TV-Deterministic Protocols -/

/-- A `SymThreshAlg` is TV-deterministic if the successor threshold view
    depends only on the current threshold view, not on exact counts. -/
def tvDeterministic (alg : SymThreshAlg k α_num α_den) : Prop :=
  ∀ n₁ n₂ (c₁ : Config k n₁) (c₂ : Config k n₂),
    c₁.threshView α_num α_den = c₂.threshView α_num α_den →
    (Config.succ alg c₁).threshView α_num α_den =
    (Config.succ alg c₂).threshView α_num α_den

/-- Iterated successor: apply `Config.succ` t times. -/
def Config.iterSucc (alg : SymThreshAlg k α_num α_den) :
    Nat → Config k n → Config k n
  | 0, c => c
  | t + 1, c => Config.iterSucc alg t (Config.succ alg c)

/-- For TV-deterministic protocols, iterated successors preserve
    the threshold view correspondence. -/
theorem iterSucc_tv_eq
    {alg : SymThreshAlg k α_num α_den}
    (h_det : tvDeterministic alg)
    (n₁ n₂ : Nat) (c₁ : Config k n₁) (c₂ : Config k n₂)
    (h_tv : c₁.threshView α_num α_den = c₂.threshView α_num α_den) :
    ∀ t, (Config.iterSucc alg t c₁).threshView α_num α_den =
         (Config.iterSucc alg t c₂).threshView α_num α_den := by
  intro t
  induction t generalizing c₁ c₂ with
  | zero => simp [Config.iterSucc, h_tv]
  | succ t ih =>
    simp only [Config.iterSucc]
    exact ih (Config.succ alg c₁) (Config.succ alg c₂)
      (h_det n₁ n₂ c₁ c₂ h_tv)

/-! ### Termination cutoff theorem -/

/-- A "decided" predicate on threshold views. -/
abbrev TVDecided (k : Nat) := ThreshView k → Prop

/-- **Termination cutoff for TV-deterministic protocols.**

    If the protocol terminates within T rounds from initial config c₀ at
    some n₀, then for any n and any config c with the same initial
    threshold view, it terminates within T rounds.

    The proof: by `iterSucc_tv_eq`, the threshold view at each round
    is the same for c and c₀. So if c₀'s trace reaches "decided" at
    step t, so does c's. -/
theorem termination_cutoff_tv_deterministic
    {alg : SymThreshAlg k α_num α_den}
    (h_det : tvDeterministic alg)
    (decided : TVDecided k)
    (T : Nat) (n₀ : Nat) (c₀ : Config k n₀)
    -- Termination at n₀: some step t ≤ T reaches decided
    (h_term : ∃ t, t ≤ T ∧ decided
      ((Config.iterSucc alg t c₀).threshView α_num α_den))
    -- Any n with matching initial threshold view
    (n : Nat) (c : Config k n)
    (h_tv : c.threshView α_num α_den = c₀.threshView α_num α_den) :
    ∃ t, t ≤ T ∧ decided
      ((Config.iterSucc alg t c).threshView α_num α_den) := by
  obtain ⟨t, ht, h_dec⟩ := h_term
  refine ⟨t, ht, ?_⟩
  have h_eq := iterSucc_tv_eq h_det n n₀ c c₀ h_tv t
  rw [h_eq]; exact h_dec

/-- **Bounded termination for all n**, combining:
    1. `thresh_scaling_down`: every large-n config maps to a small-n config
       with the same threshold view
    2. `termination_cutoff_tv_deterministic`: same initial TV → same
       termination behavior

    If termination within T rounds is verified for all n ≤ K, then
    termination within T rounds holds for all n. -/
theorem bounded_termination_cutoff
    {alg : SymThreshAlg k α_num α_den}
    (hα : α_num < α_den) (h_half : 2 * α_num ≥ α_den)
    (h_det : tvDeterministic alg)
    (decided : TVDecided k)
    (T : Nat)
    -- Verified for small instances
    (h_small : ∀ n, n ≤ cutoffBound k α_num α_den →
      ∀ c : Config k n, ∃ t, t ≤ T ∧ decided
        ((Config.iterSucc alg t c).threshView α_num α_den)) :
    ∀ n (c : Config k n), ∃ t, t ≤ T ∧ decided
      ((Config.iterSucc alg t c).threshView α_num α_den) := by
  intro n c
  obtain ⟨n', hn', c', hc'⟩ := thresh_scaling_down k α_num α_den hα h_half n c
  exact termination_cutoff_tv_deterministic h_det decided T n' c'
    (h_small n' hn' c') n c hc'.symm

/-! ### When is a protocol TV-deterministic?

    **Sufficient condition: absorbing at threshold.** If every above-threshold
    value maps to itself under the update, then:
    - Above-threshold counts are preserved (all holders stay)
    - Below-threshold counts redistribute but their threshold status
      depends only on the redistribution, which is determined by the TV

    In OneThirdRule: if >2n/3 hold value 0, after the round, everyone
    who received the supermajority adopts 0. Under reliable communication,
    ALL n processes adopt 0. So 0 is still above threshold. Below-threshold
    values go to 0.

    More generally: any protocol where the decided state is absorbing
    (processes don't change value after deciding) is TV-deterministic
    once a decision threshold is reached. -/

/-- A value is absorbing at threshold: if above threshold, maps to itself. -/
def AbsorbingAtThreshold (alg : SymThreshAlg k α_num α_den) : Prop :=
  ∀ v : Fin k, ∀ tv : ThreshView k, tv v = true → alg.update v tv = v

/-! ### Discussion: scope and limitations

    **What this covers:**
    - Bounded termination (within T rounds) under reliable communication
    - Symmetric threshold protocols that are TV-deterministic
    - The cutoff bound K is the same as for safety — no extra cost

    **What this does NOT cover:**
    - Eventual termination under weak communication predicates (e.g.,
      "eventually synchronous"). The communication predicate is an
      environmental assumption independent of n.
    - Protocols where the successor TV depends on exact counts (not
      TV-deterministic). These may still terminate for all n, but the
      bound T might depend on n.
    - Probabilistic termination (e.g., Ben-Or with random coins).

    **Open question:** For non-TV-deterministic protocols, can we bound
    T as a function of n? The threshold view space is finite (2^k),
    so any deterministic execution from a fixed config must enter a cycle
    within 2^k steps. If no cycle contains a "decided" view, the protocol
    doesn't terminate from that config. If every cycle contains a decided
    view, termination is guaranteed within 2^k rounds. But 2^k may be
    much larger than the actual termination time T observed at small n.

    **Conjecture:** For the class of protocols where below-threshold counts
    "converge" (the redistribution approaches a fixed point), termination
    time T(n) is bounded by a function of k alone, independent of n.
    This would give a termination cutoff even for non-TV-deterministic
    protocols, but the bound would be T = O(2^k) rather than the
    empirically observed T = O(1). -/

end TLA.TerminationCutoff
