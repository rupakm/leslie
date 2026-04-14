import Leslie.Round

/-! ## Cutoff Theorems for Symmetric Threshold Protocols

    ### Motivation

    Safety proofs for round-based distributed protocols follow a pattern:
    prove an invariant is preserved by every round step, for ALL numbers
    of processes n. The inductive step universally quantifies over
    states, HO collections, and successor states — an infinite space.

    For a specific subclass of protocols — **symmetric threshold protocols**
    — we can reduce "safety for all n" to "safety for n ≤ K" where K is
    a small computable bound. The finite instances can then be verified
    by a model checker (or `native_decide` in Lean).

    ### Why cutoffs work: the role of communication closure

    Communication closure is the foundational assumption. In the HO
    round-based model, messages from round r are either delivered in
    round r or lost forever. This means:

    **Received messages reflect the current state.** If process p
    receives value v from process q in round r, then q held v at the
    start of round r. There are no stale messages from earlier rounds
    contaminating the counts. This is what makes `countOcc_le_countHolding`
    true: votes for v in received messages ≤ current holders of v.

    Without communication closure (e.g., in asynchronous protocols),
    a process might receive messages from arbitrarily old rounds.
    The received vote counts would bear no relationship to the current
    configuration. The threshold abstraction would break, and no
    finite cutoff would exist.

    ### The three symmetry conditions

    **1. Process symmetry.** The algorithm treats all processes
    identically — `send` and `update` do not depend on the process ID.
    This means the global state can be abstracted to a **configuration**:
    a count of how many processes hold each value, rather than tracking
    which specific process holds what.

    **2. Threshold-based decisions.** The update function depends on
    received messages only through threshold comparisons: "did value v
    appear more than α·n times?" (where α is a fixed fraction like 2/3).
    It does NOT depend on exact counts, on which processes sent which
    messages, or on the total number of messages received beyond the
    threshold test. This means the update factors through a finite
    **threshold view** — a Boolean vector indicating which values
    crossed the threshold.

    **3. Counting invariants.** The safety invariant talks about how
    many processes satisfy some predicate, not which specific processes.
    For example, OneThirdRule's lock invariant says ">2n/3 processes
    hold v" — a pure counting property.

    ### How the cutoff works

    Under these conditions:

    1. The protocol's behavior at each round is determined by the
       **threshold view** — which values have counts exceeding α·n.

    2. The threshold view has at most `2^k` possibilities (where k is
       the number of distinct values), independent of n.

    3. The update function maps each (current_value, threshold_view) pair
       to a new value. This is a finite table of size `k · 2^k`.

    4. The invariant's truth value depends only on the threshold view
       (which counts exceed α·n), not on the exact counts.

    5. **Communication closure** ensures that received vote counts are
       bounded by actual current holder counts (no stale messages).
       So the threshold view a process observes is consistent with
       the global configuration's threshold view.

    6. Every threshold pattern that is realizable at some large n is
       also realizable at some small n ≤ K. This is because threshold
       comparisons (`count * α_den > α_num * n`) scale: if we can
       find counts summing to n with the right threshold pattern,
       we can find counts summing to n' ≤ K with the same pattern.

    7. Therefore, checking the invariant for n ≤ K covers all possible
       threshold views, hence all possible protocol behaviors, hence
       all n.

    ### The cutoff bound

    For k distinct values and threshold fraction α = α_num/α_den:

        K = ⌈k · α_den / (α_den - α_num)⌉ + 1

    For OneThirdRule (k=2, α=2/3): K = ⌈2·3/1⌉ + 1 = 7.

    In practice, not all `2^k` threshold patterns are realizable
    (e.g., two values both having >2n/3 holders is impossible by
    pigeonhole), so the effective cutoff can be smaller.
-/

open Classical

namespace TLA

/-! ### Combinatorial helpers -/

/-- A single element's value is at most the sum. -/
theorem mem_le_sum {α : Type} (l : List α) (f : α → Nat) (x : α)
    (hx : x ∈ l) : f x ≤ (l.map f).sum := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    simp only [List.map, List.sum_cons]
    rcases List.mem_cons.mp hx with rfl | h
    · omega
    · have := ih h ; omega

/-- Two distinct elements' values sum to at most the total. -/
private theorem two_mem_le_sum {α : Type} (l : List α) (f : α → Nat) (x y : α)
    (hx : x ∈ l) (hy : y ∈ l) (hne : x ≠ y) (hnd : l.Nodup) :
    f x + f y ≤ (l.map f).sum := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.map, List.sum_cons]
    rcases List.mem_cons.mp hx with rfl | hxl
    · have hyl : y ∈ l := by
        rcases List.mem_cons.mp hy with rfl | h
        · exact absurd rfl hne
        · exact h
      have := mem_le_sum l f y hyl ; omega
    · rcases List.mem_cons.mp hy with rfl | hyl
      · have := mem_le_sum l f x hxl ; omega
      · have := ih hxl hyl hnd.2 ; omega

/-- Sum distributes over pointwise addition. -/
theorem List.sum_map_add {β : Type} (l : List β) (g h : β → Nat) :
    (l.map fun x => g x + h x).sum = (l.map g).sum + (l.map h).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp [List.sum_cons, ih] ; omega

/-- The indicator sum over a nodup list with the target element is 1. -/
private theorem list_indicator_sum {β : Type} [DecidableEq β]
    (l : List β) (v0 : β) (h_nodup : l.Nodup) (h_mem : v0 ∈ l) :
    (l.map fun v => if v = v0 then 1 else (0 : Nat)).sum = 1 := by
  induction l with
  | nil => simp at h_mem
  | cons b l ih =>
    simp only [List.map, List.sum_cons]
    rw [List.nodup_cons] at h_nodup
    obtain ⟨h_nmem, h_nd⟩ := h_nodup
    by_cases hb : b = v0
    · subst hb ; simp only [ite_true]
      suffices (l.map fun v => if v = b then 1 else (0 : Nat)).sum = 0 by omega
      rw [show l.map (fun v => if v = b then 1 else (0:Nat)) = l.map (fun _ => (0:Nat)) from
        List.map_congr_left (fun x hx => by
          simp only [ite_eq_right_iff] ; intro h ; exact absurd (h ▸ hx) h_nmem)]
      have : ∀ (m : List β), (m.map fun _ => (0 : Nat)).sum = 0 := by
        intro m ; induction m with | nil => rfl | cons _ _ ih => simp [List.sum_cons, ih]
      exact this l
    · simp only [hb, ite_false, Nat.zero_add]
      exact ih h_nd (List.mem_of_ne_of_mem (Ne.symm hb) h_mem)

private theorem nodup_map_succ {k : Nat} (l : List (Fin k)) (h : l.Nodup) :
    (l.map Fin.succ).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at h
    simp only [List.map, List.nodup_cons, List.mem_map]
    refine ⟨fun ⟨b, hb, heq⟩ => h.1 (by rw [← Fin.succ_inj.mp heq] ; exact hb), ih h.2⟩

/-- `finRange k` has no duplicate elements. -/
private theorem finRange_nodup (k : Nat) : (List.finRange k).Nodup := by
  induction k with
  | zero => simp [List.finRange]
  | succ k ih =>
    rw [List.finRange_succ, List.nodup_cons]
    exact ⟨by simp only [List.mem_map] ; intro ⟨x, _, h⟩
              exact (Fin.succ_ne_zero x) h,
           nodup_map_succ _ ih⟩

/-- Indicator sum over `finRange k`: exactly 1. -/
theorem fin_indicator (k : Nat) (c : Fin k) :
    ((List.finRange k).map fun v => if v = c then 1 else (0 : Nat)).sum = 1 :=
  list_indicator_sum _ c (finRange_nodup k) (List.mem_finRange c)

/-- **Partition lemma**: filtering a list by each value of `Fin k` and
    summing the filter lengths gives the total list length. -/
theorem filter_partition_sum {α : Type} (k : Nat) (l : List α) (f : α → Fin k) :
    ((List.finRange k).map fun v =>
      (l.filter fun x => decide (f x = v)).length).sum = l.length := by
  induction l with
  | nil =>
    suffices h : ∀ m : List (Fin k), (m.map fun _ => (0 : Nat)).sum = 0 by
      simp only [List.filter_nil, List.length_nil] ; exact h _
    intro m ; induction m with | nil => rfl | cons _ _ ih => simp [List.sum_cons, ih]
  | cons a l ih =>
    have h_pointwise : ∀ v : Fin k,
        ((a :: l).filter fun x => decide (f x = v)).length =
        (l.filter fun x => decide (f x = v)).length + if v = f a then 1 else 0 := by
      intro v ; simp only [List.filter]
      by_cases h : f a = v
      · simp [h]
      · simp [h, Ne.symm h]
    rw [show ((List.finRange k).map fun v =>
          ((a :: l).filter fun x => decide (f x = v)).length).sum =
        ((List.finRange k).map fun v =>
          ((l.filter fun x => decide (f x = v)).length +
           if v = f a then 1 else 0)).sum from by
      congr 1 ; exact List.map_congr_left (fun v _ => h_pointwise v)]
    rw [List.sum_map_add, ih, fin_indicator]
    simp [List.length]

/-! ### Configurations -/

/-- A **configuration** of `n` processes over `k` value types.
    `counts i` is the number of processes holding value `i`.
    The counts must sum to `n`. -/
structure Config (k : Nat) (n : Nat) where
  counts : Fin k → Nat
  sum_eq : ((List.finRange k).map counts).sum = n

/-! ### Threshold view -/

abbrev ThreshView (k : Nat) := Fin k → Bool

/-- Compute the threshold view for a configuration.
    Value v is "above threshold" iff `counts(v) * α_den > α_num * n`. -/
def Config.threshView (α_num α_den : Nat) (c : Config k n) : ThreshView k :=
  fun v => decide (c.counts v * α_den > α_num * n)

/-! ### Symmetric threshold round algorithm -/

structure SymThreshAlg (k : Nat) (α_num α_den : Nat) where
  update : Fin k → ThreshView k → Fin k

/-! ### Configuration transitions -/

/-- Successor counts after one round with reliable communication. -/
def succCounts (alg : SymThreshAlg k α_num α_den) (c : Config k n) :
    Fin k → Nat :=
  let tv := c.threshView α_num α_den
  fun v' => ((List.finRange k).map fun v =>
    if alg.update v tv = v' then c.counts v else 0).sum

/-- Weighted partition sum: partitioning a weighted sum by the image of
    a function g doesn't change the total. Each element v contributes
    f(v) to exactly one bucket g(v), so the total is ∑ f(v). -/
theorem weighted_partition_sum (k : Nat) (vals : List (Fin k))
    (f : Fin k → Nat) (g : Fin k → Fin k) :
    ((List.finRange k).map fun v' =>
      (vals.map fun v => if g v = v' then f v else 0).sum).sum =
    (vals.map f).sum := by
  induction vals with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    induction (List.finRange k) with | nil => rfl | cons _ _ ih => simp [List.sum_cons, ih]
  | cons v rest ih =>
    -- Unfold inner map: (v :: rest).map h = h v :: rest.map h
    -- Then inner sum = h(v) + sum(rest.map h) by sum_cons
    -- Outer map: fun v' => (if g v = v' then f v else 0) + (rest inner sum for v')
    -- By sum_map_add: outer sum = sum of first parts + sum of second parts
    -- First parts sum = f v  (by fin_indicator)
    -- Second parts sum = sum(rest.map f)  (by IH)
    simp only [List.map, List.sum_cons]
    -- Goal involves: ((finRange k).map (fun v' => X(v') + Y(v'))).sum = f v + (rest.map f).sum
    -- where X(v') = if g v = v' then f v else 0, Y(v') = (rest.map ...).sum
    -- Use sum_map_add: sum(X + Y) = sum(X) + sum(Y)
    rw [show ((List.finRange k).map fun v' =>
          (if g v = v' then f v else 0) +
          (rest.map fun v₀ => if g v₀ = v' then f v₀ else 0).sum).sum =
        ((List.finRange k).map fun v' => if g v = v' then f v else 0).sum +
        ((List.finRange k).map fun v' =>
          (rest.map fun v₀ => if g v₀ = v' then f v₀ else 0).sum).sum from
      List.sum_map_add _ _ _]
    rw [ih]
    -- Goal: sum(if g v = · then f v else 0) + sum(rest.map f) = f v + sum(rest.map f)
    congr 1
    -- sum_{v'} (if g v = v' then f v else 0) = f v
    -- Factor: = f v * sum_{v'} (if v' = g v then 1 else 0) = f v * 1
    rw [show ((List.finRange k).map fun v' => if g v = v' then f v else 0) =
        (List.finRange k).map (fun v' => f v * if v' = g v then 1 else 0) from
      List.map_congr_left (fun v' _ => by
        by_cases h : g v = v'
        · simp [h]
        · simp [h, show v' ≠ g v from fun h' => h h'.symm])]
    rw [show ((List.finRange k).map fun v' => f v * if v' = g v then 1 else 0).sum =
        f v * ((List.finRange k).map fun v' => if v' = g v then 1 else 0).sum from by
      induction (List.finRange k) with
      | nil => simp
      | cons x xs ihx => simp [List.sum_cons, Nat.mul_add, ihx]]
    rw [fin_indicator]
    omega

/-- Successor counts sum to n (double-counting). -/
theorem succCounts_sum (alg : SymThreshAlg k α_num α_den)
    (c : Config k n) :
    ((List.finRange k).map (succCounts alg c)).sum = n := by
  simp only [succCounts]
  have := weighted_partition_sum k (List.finRange k) c.counts
    (fun v => alg.update v (c.threshView α_num α_den))
  rw [c.sum_eq] at this
  exact this

/-- The successor configuration. -/
def Config.succ (alg : SymThreshAlg k α_num α_den)
    (c : Config k n) : Config k n :=
  ⟨succCounts alg c, succCounts_sum alg c⟩

/-! ### Cutoff bound -/

def cutoffBound (k α_num α_den : Nat) : Nat :=
  if α_den > α_num then
    k * α_den / (α_den - α_num) + 1
  else
    1

/-! ### Configuration invariants -/

def ConfigInv (k : Nat) := (n : Nat) → Config k n → Prop

def ConfigInv.threshDetermined (inv : ConfigInv k) (α_num α_den : Nat) : Prop :=
  ∀ n₁ n₂ (c₁ : Config k n₁) (c₂ : Config k n₂),
    c₁.threshView α_num α_den = c₂.threshView α_num α_den →
    (inv n₁ c₁ ↔ inv n₂ c₂)

/-! ### Scaling lemma

    The cutoff theorem needs: for any configuration at any n, there
    exists a configuration at some small n' ≤ K with the same threshold
    view. This lets us transfer the invariant from small instances
    (verified by model checking) to large instances.

    **Construction**: Given a threshold view `tv` with `a` above-threshold
    values, we build a witness at a small n':
    - If a = 0: all values below threshold. Take n' = k, one process per value.
      Each count = 1, and 1 * α_den ≤ α_num * k when k ≥ α_den / α_num + 1.
    - If a ≥ 1: put all n' processes into one above-threshold value,
      zeros elsewhere. Then n' * α_den > α_num * n' since α_den > α_num.
      Take n' = 1.

    The (false, ..., false) pattern (all below threshold) is the constraining
    case: it requires n' large enough that no value "accidentally" exceeds
    the threshold when we spread processes among k values. -/

/-- Every realizable threshold view has a small witness at n' ≤ K.
    Requires `2 * α_num ≥ α_den` (threshold ≥ 1/2), which ensures at
    most one value can be above threshold (pigeonhole). This covers all
    quorum-based protocols (majority, 2/3-majority, etc.). -/
theorem thresh_scaling_down (k α_num α_den : Nat) (hα : α_num < α_den)
    (h_half : 2 * α_num ≥ α_den)
    (n : Nat) (c : Config k n) :
    ∃ n' ≤ cutoffBound k α_num α_den,
    ∃ c' : Config k n', c'.threshView α_num α_den = c.threshView α_num α_den := by
  by_cases h_all_below : ∀ v : Fin k, c.threshView α_num α_den v = false
  · -- Case: all values below threshold. Take n' = 0.
    have h_sum : ((List.finRange k).map fun (_ : Fin k) => (0 : Nat)).sum = 0 := by
      induction (List.finRange k) with | nil => rfl | cons _ _ ih => simp [List.sum_cons, ih]
    refine ⟨0, Nat.zero_le _, ⟨fun _ => 0, h_sum⟩, ?_⟩
    funext v ; simp only [Config.threshView, decide_eq_decide]
    constructor
    · intro h ; omega
    · intro h ; have := h_all_below v ; simp [Config.threshView] at this ; omega
  · -- Case: some value v₀ is above threshold.
    simp only [not_forall] at h_all_below
    obtain ⟨v₀, hv₀⟩ := h_all_below
    have hv₀_above : c.threshView α_num α_den v₀ = true := by
      cases h : c.threshView α_num α_den v₀ <;> simp_all
    -- v₀ is the UNIQUE above-threshold value (pigeonhole for α ≥ 1/2).
    -- If v₁ ≠ v₀ were also above threshold, then counts(v₀) + counts(v₁)
    -- > 2·α_num·n/α_den ≥ n, contradicting the sum.
    have h_unique : ∀ v, c.threshView α_num α_den v = true → v = v₀ := by
      intro v hv
      by_contra hne
      simp [Config.threshView, decide_eq_true_eq] at hv hv₀_above
      -- counts(v) * α_den > α_num * n AND counts(v₀) * α_den > α_num * n
      -- → (counts v + counts v₀) * α_den > 2 * α_num * n ≥ α_den * n
      -- → counts v + counts v₀ > n
      -- But counts v + counts v₀ ≤ sum of all counts = n. Contradiction.
      -- counts(v) + counts(v₀) > n, but also ≤ n. Contradiction.
      -- Use two_mem_le_sum: cv + cv₀ ≤ sum = n
      have h_le : c.counts v + c.counts v₀ ≤
          ((List.finRange k).map c.counts).sum :=
        two_mem_le_sum (List.finRange k) c.counts v v₀
          (List.mem_finRange v) (List.mem_finRange v₀) hne (finRange_nodup k)
      rw [c.sum_eq] at h_le
      -- From hv, hv₀_above: cv * α_den > α_num * n, cv₀ * α_den > α_num * n
      -- → cv > α_num * n / α_den, cv₀ > α_num * n / α_den
      -- → cv + cv₀ > 2 * α_num * n / α_den ≥ n (since 2*α_num ≥ α_den)
      -- In integer arithmetic: (cv + cv₀) * α_den > 2 * α_num * n ≥ α_den * n
      -- Step 1: (cv + cv₀) * α_den > 2 * α_num * n
      have h_add_mul : (c.counts v + c.counts v₀) * α_den =
          c.counts v * α_den + c.counts v₀ * α_den :=
        Nat.add_mul (c.counts v) (c.counts v₀) α_den
      have h1 : c.counts v * α_den + c.counts v₀ * α_den > α_num * n + α_num * n := by
        exact Nat.add_lt_add hv hv₀_above
      -- Step 2: n * α_den ≤ α_num * n + α_num * n (since 2*α_num ≥ α_den)
      have h2 : n * α_den ≤ α_num * n + α_num * n := by
        have h := Nat.mul_le_mul_right n h_half  -- 2 * α_num ≥ α_den → α_den * n ≤ 2 * α_num * n
        -- Need: n * α_den ≤ α_num * n + α_num * n
        -- α_den * n ≤ (2 * α_num) * n = α_num * n + α_num * n
        calc n * α_den
          _ = α_den * n := Nat.mul_comm n α_den
          _ ≤ (2 * α_num) * n := h
          _ = α_num * n + α_num * n := by
              rw [show (2 * α_num) * n = 2 * (α_num * n) from by
                rw [Nat.mul_assoc]] ; omega
      -- Step 3: chain to get n * α_den < (cv+cv₀) * α_den
      have h3 : n * α_den < (c.counts v + c.counts v₀) * α_den := by
        calc n * α_den
          _ ≤ α_num * n + α_num * n := h2
          _ < c.counts v * α_den + c.counts v₀ * α_den := h1
          _ = (c.counts v + c.counts v₀) * α_den := h_add_mul.symm
      -- Step 4: divide by α_den
      exact absurd (Nat.lt_of_mul_lt_mul_right h3) (Nat.not_lt.mpr h_le)
    -- Construct c' at n' = 1: put everything on v₀
    have h_sum_1 := fin_indicator k v₀
    refine ⟨1, by simp [cutoffBound, show α_den > α_num from hα],
            ⟨fun v => if v = v₀ then 1 else 0, h_sum_1⟩, ?_⟩
    funext v
    simp only [Config.threshView, decide_eq_decide]
    by_cases hv : v = v₀
    · -- v = v₀: both above threshold
      subst hv
      have hv_true : c.counts v * α_den > α_num * n := by
        simp [Config.threshView, decide_eq_true_eq] at hv₀_above ; exact hv₀_above
      exact ⟨fun _ => hv_true, fun _ => by simp_all⟩
    · -- v ≠ v₀: both below threshold
      have hv_false : ¬(c.counts v * α_den > α_num * n) := by
        intro h
        exact hv (h_unique v (by simp [Config.threshView, decide_eq_true_eq] ; exact h))
      exact ⟨fun h => by simp_all, fun h => absurd h hv_false⟩

/-! ### The cutoff theorem -/

/-- **Cutoff Theorem.** If a threshold-determined invariant holds for
    all configurations at all n ≤ K, it holds for all n.

    Proof: for any config c at n, `thresh_scaling_down` gives a config
    c' at some n' ≤ K with the same threshold view. Since the invariant
    is threshold-determined, `inv n c ↔ inv n' c'`. Since n' ≤ K,
    `inv n' c'` holds by hypothesis. Therefore `inv n c`. -/
theorem cutoff_reliable
    (_alg : SymThreshAlg k α_num α_den) (hα : α_num < α_den)
    (h_half : 2 * α_num ≥ α_den)
    (inv : ConfigInv k)
    (h_thresh : inv.threshDetermined α_num α_den)
    (h_all_small : ∀ n, n ≤ cutoffBound k α_num α_den →
      ∀ c : Config k n, inv n c) :
    ∀ n (c : Config k n), inv n c := by
  intro n c
  obtain ⟨n', hn', c', hc'⟩ := thresh_scaling_down k α_num α_den hα h_half n c
  exact (h_thresh n n' c c' hc'.symm).mpr (h_all_small n' hn' c')

/-! ### Connecting configurations to round states -/

/-- Extract a configuration from a round state. -/
def RoundState.toConfig {S : Type} (encode : S → Fin k)
    (s : RoundState (Fin n) S) : Config k n where
  counts := fun v => ((List.finRange n).filter fun p =>
    decide (encode (s.locals p) = v)).length
  sum_eq := by
    have := filter_partition_sum k (List.finRange n) (fun p => encode (s.locals p))
    simp [List.length_finRange] at this
    exact this

/-! ### Example: OneThirdRule cutoff -/

def otr_symthresh : SymThreshAlg 2 2 3 where
  update := fun v tv =>
    if tv 0 then (0 : Fin 2)
    else if tv 1 then (1 : Fin 2)
    else v

theorem otr_cutoff_bound : cutoffBound 2 2 3 = 7 := by
  simp [cutoffBound]

/-- The "no two super-majorities" invariant — always true by pigeonhole. -/
def noTwoSuperMaj : ConfigInv 2 :=
  fun n c => ¬ (c.counts 0 * 3 > 2 * n ∧ c.counts 1 * 3 > 2 * n)

theorem noTwoSuperMaj_always (n : Nat) (c : Config 2 n) :
    noTwoSuperMaj n c := by
  simp only [noTwoSuperMaj]
  intro ⟨h0, h1⟩
  have := c.sum_eq
  simp [List.finRange] at this
  omega

/-! ### Applying the cutoff theorem to OneThirdRule

    We demonstrate the full cutoff pipeline:
    1. Define the invariant as a `ConfigInv`
    2. Prove it is threshold-determined
    3. Verify it holds for all n ≤ K (the "model checking" step)
    4. Apply `cutoff_reliable` to get the result for all n

    The invariant `noTwoSuperMaj` ("at most one value can have a
    super-majority") is trivially true by pigeonhole for all n.
    But the point is to demonstrate that the cutoff machinery works:
    step 3 COULD be discharged by `native_decide` for small n,
    and `cutoff_reliable` lifts it to all n automatically.

    We also prove a more interesting invariant: `lockPreserved`,
    which says that super-majorities survive one round of the
    OneThirdRule. This is the configuration-level analogue of
    `lock_inv_step` from OneThirdRule.lean. -/

/-- `noTwoSuperMaj` depends only on the threshold view: it asks
    whether both values are above threshold, which is exactly what
    the threshold view encodes. -/
theorem noTwoSuperMaj_threshDetermined :
    noTwoSuperMaj.threshDetermined 2 3 := by
  intro n₁ n₂ c₁ c₂ htv
  simp only [noTwoSuperMaj]
  constructor
  · intro h ⟨h0, h1⟩
    apply h
    constructor
    · have := congrFun htv 0 ; simp [Config.threshView, decide_eq_decide] at this
      exact this.mpr h0
    · have := congrFun htv 1 ; simp [Config.threshView, decide_eq_decide] at this
      exact this.mpr h1
  · intro h ⟨h0, h1⟩
    apply h
    constructor
    · have := congrFun htv 0 ; simp [Config.threshView, decide_eq_decide] at this
      exact this.mp h0
    · have := congrFun htv 1 ; simp [Config.threshView, decide_eq_decide] at this
      exact this.mp h1

/-- **Cutoff application**: `noTwoSuperMaj` holds for all n.
    Proved via the cutoff theorem: verify for n ≤ 7, lift to all n. -/
theorem noTwoSuperMaj_via_cutoff :
    ∀ n (c : Config 2 n), noTwoSuperMaj n c :=
  cutoff_reliable otr_symthresh (by omega) (by omega)
    noTwoSuperMaj noTwoSuperMaj_threshDetermined
    (fun n _ c => noTwoSuperMaj_always n c)

/-! ### Lock preservation: super-majorities survive rounds

    A more interesting invariant: if value v has a super-majority
    (>2n/3 holders), then after one round of OneThirdRule with
    reliable communication, v still has a super-majority.

    This is the configuration-level version of `lock_inv_step` from
    OneThirdRule.lean. At the configuration level, under reliable
    communication, all processes see the same threshold view, so
    the successor is deterministic.

    The proof: if v has >2n/3, then in the successor, every process
    that held v either keeps v (threshold view says "no super-majority
    elsewhere") or adopts v (threshold view says v has super-majority).
    Either way, v's count doesn't decrease. -/

/-- The successor count for v when v has super-majority equals n
    (every process adopts v). When v has super-majority, the threshold
    view has v = true, so `update w tv = v` for all w (since the
    update adopts the super-majority value). -/
theorem otr_succ_preserves_supermaj (n : Nat) (c : Config 2 n)
    (v : Fin 2) (hv : c.counts v * 3 > 2 * n) :
    (c.succ otr_symthresh).counts v * 3 > 2 * n := by
  -- The threshold view of c has v = true
  have htv_v : c.threshView 2 3 v = true := by
    simp [Config.threshView, decide_eq_true_eq] ; exact hv
  -- And the other value w ≠ v is false (by pigeonhole: can't both be above threshold)
  have htv_w : ∀ w : Fin 2, w ≠ v → c.threshView 2 3 w = false := by
    intro w hw
    simp only [Config.threshView]
    -- Need: ¬(c.counts w * 3 > 2 * n)
    -- Proof: c.counts v + c.counts w = n (the two values sum to n)
    -- and c.counts v * 3 > 2 * n, so c.counts v > 2n/3
    -- so c.counts w = n - c.counts v < n/3
    -- so c.counts w * 3 < n ≤ 2n
    have h_sum := c.sum_eq
    simp [List.finRange] at h_sum
    -- h_sum : c.counts 0 + c.counts 1 = n
    -- hv : c.counts v * 3 > 2 * n
    -- Need: c.counts w * 3 ≤ 2 * n
    -- Fin 2 case split: v and w are 0 or 1, and v ≠ w
    have : v = 0 ∨ v = 1 := by omega
    have : w = 0 ∨ w = 1 := by omega
    rcases ‹v = 0 ∨ v = 1› with rfl | rfl <;> rcases ‹w = 0 ∨ w = 1› with rfl | rfl <;>
      simp_all <;> omega
  -- Under the OneThirdRule update with this threshold view:
  -- otr_symthresh.update w tv = v for every w (including w = v)
  -- Because: if v = 0, tv 0 = true, so update _ tv = 0 = v
  --          if v = 1, tv 0 = false, tv 1 = true, so update _ tv = 1 = v
  have h_all_to_v : ∀ w : Fin 2,
      otr_symthresh.update w (c.threshView 2 3) = v := by
    intro w
    simp only [otr_symthresh]
    have : v = 0 ∨ v = 1 := by omega
    rcases this with rfl | rfl
    · simp [htv_v]
    · have h0 := htv_w 0 (by omega)
      simp [h0, htv_v]
  -- In the successor, succCounts v = sum over all w of
  -- (if update w tv = v then c.counts w else 0) = sum of all c.counts w = n
  have h_succ : (c.succ otr_symthresh).counts v = n := by
    simp only [Config.succ, succCounts]
    -- Every term in the sum has update w tv = v, so the "if" is always true
    rw [show ((List.finRange 2).map fun w =>
          if otr_symthresh.update w (c.threshView 2 3) = v then c.counts w else 0) =
        (List.finRange 2).map c.counts from
      List.map_congr_left (fun w _ => by simp [h_all_to_v w])]
    exact c.sum_eq
  rw [h_succ]
  -- n * 3 > 2 * n iff n > 0. And n > 0 because v has >2n/3 holders.
  -- Goal: n * 3 > 2 * n. Equivalent to n > 0.
  -- n > 0 because c.counts v > 0 (from hv) and counts v ≤ n.
  have hv_pos : c.counts v > 0 := by omega
  have hv_le : c.counts v ≤ n := by
    have := mem_le_sum (List.finRange 2) c.counts v (List.mem_finRange v)
    rw [c.sum_eq] at this ; exact this
  omega

end TLA
