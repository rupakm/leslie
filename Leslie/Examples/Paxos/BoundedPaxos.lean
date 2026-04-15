import Leslie.Examples.Paxos
import Leslie.Examples.Combinators.PhaseCounting

/-! # Faithful m-proposer single-decree Paxos bounded unrolling

    Wraps `Leslie/Examples/Paxos.lean`'s real quorum-gated Paxos model in a
    `PhaseCountingSystem` and derives a bounded-unrolling theorem at trace
    depth `2·m·n + m`.

    The phase counter counts fired actions:
    - each `p1b p i` flips one `got1b p i` bit (`m·n` such bits),
    - each `p2a p` sets one `prop p` slot from `none` to `some` (`m` slots),
    - each `p2b p i` flips one `did2b p i` bit (`m·n` such bits).

    Total capacity `2·m·n + m`. Each step strictly increases the counter by
    one, so the counter is monotone and bounded, giving the abstract
    bounded-unrolling theorem for free.

    This file replaces the earlier `BoundedTwoProposer.lean` /
    `BoundedMProposer.lean` defer-rule shortcut models. Those were sound but
    forced the safety invariant to reference proposer volatile state, which
    precluded any fault-model extension. This wrapper inherits its safety
    proof directly from the existing `PaxosTextbookN.agreement` theorem.

    No Mathlib. No sorries.
-/

open TLA

namespace PaxosTextbookN.Bounded

open PaxosTextbookN

/-! ## Section 1: Counting primitives -/

/-- Count of `some` entries in a `Fin k → Option α` function. -/
def countSome {α : Type} {k : Nat} (f : Fin k → Option α) : Nat :=
  ((List.finRange k).filter fun i => (f i).isSome).length

theorem countSome_le {α : Type} {k : Nat} (f : Fin k → Option α) :
    countSome f ≤ k := by
  unfold countSome
  have := List.length_filter_le (fun i => (f i).isSome) (List.finRange k)
  simpa [List.length_finRange] using this

theorem countTrue_le {n : Nat} (f : Fin n → Bool) : countTrue f ≤ n := by
  unfold countTrue
  have := List.length_filter_le (fun i => f i) (List.finRange n)
  simpa [List.length_finRange] using this

/-! ### Delta lemma: flipping one bit from false to true -/

/-- Generic helper: if `f` and `g` are boolean functions agreeing off of
    `i`, with `f i = false` and `g i = true`, then on any Nodup list `L`,
    `(L.filter g).length = (L.filter f).length + (if i ∈ L then 1 else 0)`. -/
private theorem filter_flip_one_aux {n : Nat} (f g : Fin n → Bool) (i : Fin n)
    (hne : ∀ j, j ≠ i → f j = g j) (hfi : f i = false) (hgi : g i = true) :
    ∀ (L : List (Fin n)), L.Nodup →
      (L.filter g).length =
        (L.filter f).length + (if i ∈ L then 1 else 0) := by
  intro L hnd
  induction L with
  | nil => simp
  | cons x xs ih =>
    have hnd' : xs.Nodup := (List.nodup_cons.mp hnd).2
    have hxnot : x ∉ xs := (List.nodup_cons.mp hnd).1
    have ih' := ih hnd'
    by_cases hxi : x = i
    · -- x = i: can't subst (i is a free var); derive everything from hxi
      have hxieq : x = i := hxi
      have hnotin : i ∉ xs := hxi ▸ hxnot
      have ih'' : (List.filter g xs).length = (List.filter f xs).length := by
        have := ih hnd'
        simp [hnotin] at this
        exact this
      have hmemcons : i ∈ (x :: xs) := hxieq ▸ (List.mem_cons_self (a := i) (l := xs))
      have hfx : f x = false := hxieq ▸ hfi
      have hgx : g x = true := hxieq ▸ hgi
      have hlenF : (List.filter f (x :: xs)).length = (List.filter f xs).length := by
        rw [List.filter_cons, hfx]; simp
      have hlenG : (List.filter g (x :: xs)).length = (List.filter g xs).length + 1 := by
        rw [List.filter_cons, hgx]; simp
      rw [hlenF, hlenG, ih'']
      simp [hmemcons]
    · have hagx : f x = g x := hne x hxi
      have hne' : i ≠ x := fun h => hxi h.symm
      have hmem_iff : (i ∈ x :: xs) ↔ i ∈ xs := by
        constructor
        · intro h
          rcases List.mem_cons.mp h with h | h
          · exact absurd h hne'
          · exact h
        · exact fun h => List.mem_cons_of_mem _ h
      by_cases hfx : f x = true
      · have hgx : g x = true := hagx ▸ hfx
        have : (if f x = true then x :: List.filter f xs else List.filter f xs).length
             = (List.filter f xs).length + 1 := by rw [hfx]; simp
        have hG : (if g x = true then x :: List.filter g xs else List.filter g xs).length
             = (List.filter g xs).length + 1 := by rw [hgx]; simp
        simp only [List.filter_cons]
        rw [this, hG, ih']
        by_cases hmem : i ∈ xs
        · have hmc : (i ∈ x :: xs) := hmem_iff.mpr hmem
          simp [hmc, hmem]
        · have hnmc : ¬ (i ∈ x :: xs) := fun h => hmem (hmem_iff.mp h)
          simp [hnmc, hmem]
      · have hfx' : f x = false := by cases h : f x <;> simp_all
        have hgx' : g x = false := hagx ▸ hfx'
        have : (if f x = true then x :: List.filter f xs else List.filter f xs).length
             = (List.filter f xs).length := by rw [hfx']; simp
        have hG : (if g x = true then x :: List.filter g xs else List.filter g xs).length
             = (List.filter g xs).length := by rw [hgx']; simp
        simp only [List.filter_cons]
        rw [this, hG, ih']
        by_cases hmem : i ∈ xs
        · have hmc : (i ∈ x :: xs) := hmem_iff.mpr hmem
          simp [hmc, hmem]
        · have hnmc : ¬ (i ∈ x :: xs) := fun h => hmem (hmem_iff.mp h)
          simp [hnmc, hmem]

/-- If `f j = g j` for all `j ≠ i`, `f i = false`, and `g i = true`, then
    `countTrue g = countTrue f + 1`. -/
theorem countTrue_flip_one {n : Nat} (f g : Fin n → Bool) (i : Fin n)
    (hne : ∀ j, j ≠ i → f j = g j) (hfi : f i = false) (hgi : g i = true) :
    countTrue g = countTrue f + 1 := by
  unfold countTrue
  have hh := filter_flip_one_aux f g i hne hfi hgi (List.finRange n)
    (List.nodup_finRange n)
  have hmem : i ∈ List.finRange n := List.mem_finRange i
  simpa [hmem] using hh

/-- Specialized form: `setFn f i true` where `f i = false` adds exactly one
    to `countTrue`. -/
theorem countTrue_setFn_true {n : Nat} (f : Fin n → Bool) (i : Fin n)
    (h : f i = false) :
    countTrue (setFn f i true) = countTrue f + 1 := by
  apply countTrue_flip_one f (setFn f i true) i
  · intro j hj; simp [setFn, hj]
  · exact h
  · simp [setFn]

/-! ### Sum of a `Nat`-valued function over `Fin m` -/

/-- Sum `f 0 + f 1 + ... + f (m-1)`. -/
def finSumN {m : Nat} (f : Fin m → Nat) : Nat :=
  ((List.finRange m).map f).foldr (· + ·) 0

theorem finSumN_le_mul {m : Nat} (f : Fin m → Nat) (k : Nat)
    (h : ∀ p, f p ≤ k) : finSumN f ≤ m * k := by
  unfold finSumN
  suffices h' : ∀ (L : List (Fin m)), (L.map f).foldr (· + ·) 0 ≤ L.length * k by
    have := h' (List.finRange m); simpa [List.length_finRange] using this
  intro L
  induction L with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.foldr_cons, List.length_cons]
    have hx : f x ≤ k := h x
    have hmul : (xs.length + 1) * k = xs.length * k + k := by
      rw [Nat.add_mul, Nat.one_mul]
    omega

/-- If `f` and `g` agree off of `i`, and `g i = f i + 1`, then their sums
    differ by 1. -/
theorem finSumN_update_plus_one {m : Nat} (f g : Fin m → Nat) (i : Fin m)
    (hagree : ∀ j, j ≠ i → f j = g j) (hstep : g i = f i + 1) :
    finSumN g = finSumN f + 1 := by
  unfold finSumN
  suffices h : ∀ (L : List (Fin m)), L.Nodup →
      (L.map g).foldr (· + ·) 0 =
        (L.map f).foldr (· + ·) 0 + (if i ∈ L then 1 else 0) by
    have hh := h (List.finRange m) (List.nodup_finRange m)
    have hmem : i ∈ List.finRange m := List.mem_finRange i
    simpa [hmem] using hh
  intro L hnd
  induction L with
  | nil => simp
  | cons x xs ih =>
    have hnd' : xs.Nodup := (List.nodup_cons.mp hnd).2
    have hxnot : x ∉ xs := (List.nodup_cons.mp hnd).1
    have ih' := ih hnd'
    simp only [List.map_cons, List.foldr_cons]
    by_cases hxi : x = i
    · have hxieq : x = i := hxi
      have hnotin : i ∉ xs := hxi ▸ hxnot
      have ih'' :
          (List.map g xs).foldr (· + ·) 0 = (List.map f xs).foldr (· + ·) 0 := by
        have := ih hnd'
        simp [hnotin] at this
        exact this
      have hmemcons : (i ∈ (x :: xs)) := hxieq ▸ (List.mem_cons_self (a := i) (l := xs))
      rw [show (if i ∈ x :: xs then (1 : Nat) else 0) = 1 from by simp [hmemcons]]
      rw [ih'', hxieq, hstep]; omega
    · have hagx : f x = g x := hagree x hxi
      have hne' : i ≠ x := fun h => hxi h.symm
      have hmem_iff : (i ∈ x :: xs) ↔ i ∈ xs := by
        constructor
        · intro h
          rcases List.mem_cons.mp h with h | h
          · exact absurd h hne'
          · exact h
        · exact fun h => List.mem_cons_of_mem _ h
      by_cases hmem : i ∈ xs
      · have hmem_cons : i ∈ x :: xs := hmem_iff.mpr hmem
        rw [ih', ← hagx]
        simp [hmem_cons, hmem]; omega
      · have hnmem_cons : ¬ (i ∈ x :: xs) := fun h => hmem (hmem_iff.mp h)
        rw [ih', ← hagx]
        simp [hnmem_cons, hmem]

/-! ## Section 2: The phase counter -/

/-- Phase counter for `PaxosState n m`: total number of `got1b` bits set,
    plus total number of `did2b` bits set, plus number of filled `prop`
    slots. Each step flips exactly one of these on. -/
def phaseCounter {n m : Nat} (s : PaxosState n m) : Nat :=
  finSumN (fun p => countTrue (s.got1b p)) +
  finSumN (fun p => countTrue (s.did2b p)) +
  countSome s.prop

/-- Canonical initial state used as the start of all bounded traces. -/
def initialPaxos (n m : Nat) : PaxosState n m where
  prom  := fun _ => 0
  acc   := fun _ => none
  got1b := fun _ _ => false
  rep   := fun _ _ => none
  prop  := fun _ => none
  did2b := fun _ _ => false

theorem initialPaxos_isInit {n m : Nat} (ballot : Fin m → Nat) :
    (paxos n m ballot).init (initialPaxos n m) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rfl

theorem finSumN_const_zero {m : Nat} :
    finSumN (fun _ : Fin m => (0 : Nat)) = 0 := by
  unfold finSumN
  induction List.finRange m with
  | nil => simp
  | cons x xs ih => simpa using ih

theorem countTrue_allFalse {n : Nat} : countTrue (fun _ : Fin n => false) = 0 := by
  unfold countTrue; simp

theorem phaseCounter_init (n m : Nat) :
    phaseCounter (initialPaxos n m) = 0 := by
  unfold phaseCounter initialPaxos countSome
  simp only [countTrue_allFalse]
  rw [finSumN_const_zero]
  simp

theorem phaseCounter_le (n m : Nat) (s : PaxosState n m) :
    phaseCounter s ≤ 2 * m * n + m := by
  unfold phaseCounter
  have h1 : finSumN (fun p => countTrue (s.got1b p)) ≤ m * n :=
    finSumN_le_mul _ n (fun _ => countTrue_le _)
  have h2 : finSumN (fun p => countTrue (s.did2b p)) ≤ m * n :=
    finSumN_le_mul _ n (fun _ => countTrue_le _)
  have h3 : countSome s.prop ≤ m := countSome_le _
  have hmn : 2 * m * n = m * n + m * n := by
    rw [Nat.mul_assoc, Nat.two_mul]
  omega

/-! ## Section 3: Counter monotonicity along each action -/

/-- A `p1b p i` step, with shape matching the transition in `Paxos.lean`,
    increases the counter by exactly one. -/
theorem phaseCounter_step_p1b {n m : Nat} (ballot : Fin m → Nat)
    (s : PaxosState n m) (p : Fin m) (i : Fin n)
    (hg : s.got1b p i = false) :
    phaseCounter ({ s with
        prom := setFn s.prom i (ballot p)
        got1b := setFn s.got1b p (setFn (s.got1b p) i true)
        rep := setFn s.rep p (setFn (s.rep p) i (s.acc i)) }) =
      phaseCounter s + 1 := by
  unfold phaseCounter
  have hgot_sum :
      finSumN (fun q => countTrue (setFn s.got1b p (setFn (s.got1b p) i true) q)) =
      finSumN (fun q => countTrue (s.got1b q)) + 1 := by
    apply finSumN_update_plus_one
      (fun q => countTrue (s.got1b q))
      (fun q => countTrue (setFn s.got1b p (setFn (s.got1b p) i true) q))
      p
    · intro q hq; simp [setFn, hq]
    · have : setFn s.got1b p (setFn (s.got1b p) i true) p = setFn (s.got1b p) i true := by
        simp [setFn]
      rw [this]
      exact countTrue_setFn_true (s.got1b p) i hg
  show
    finSumN (fun q => countTrue (setFn s.got1b p (setFn (s.got1b p) i true) q)) +
      finSumN (fun p_1 => countTrue (s.did2b p_1)) + countSome s.prop =
    finSumN (fun p_1 => countTrue (s.got1b p_1)) +
      finSumN (fun p_1 => countTrue (s.did2b p_1)) + countSome s.prop + 1
  rw [hgot_sum]; omega

theorem phaseCounter_step_p2b {n m : Nat} (ballot : Fin m → Nat)
    (s : PaxosState n m) (p : Fin m) (i : Fin n) (v : Value)
    (hd : s.did2b p i = false) :
    phaseCounter ({ s with
        prom := setFn s.prom i (ballot p)
        acc := setFn s.acc i (some (ballot p, v))
        did2b := setFn s.did2b p (setFn (s.did2b p) i true) }) =
      phaseCounter s + 1 := by
  unfold phaseCounter
  have hdid_sum :
      finSumN (fun q => countTrue (setFn s.did2b p (setFn (s.did2b p) i true) q)) =
      finSumN (fun q => countTrue (s.did2b q)) + 1 := by
    apply finSumN_update_plus_one
      (fun q => countTrue (s.did2b q))
      (fun q => countTrue (setFn s.did2b p (setFn (s.did2b p) i true) q))
      p
    · intro q hq; simp [setFn, hq]
    · have : setFn s.did2b p (setFn (s.did2b p) i true) p = setFn (s.did2b p) i true := by
        simp [setFn]
      rw [this]
      exact countTrue_setFn_true (s.did2b p) i hd
  show
    finSumN (fun p_1 => countTrue (s.got1b p_1)) +
      finSumN (fun q => countTrue (setFn s.did2b p (setFn (s.did2b p) i true) q)) +
      countSome s.prop =
    finSumN (fun p_1 => countTrue (s.got1b p_1)) +
      finSumN (fun p_1 => countTrue (s.did2b p_1)) + countSome s.prop + 1
  rw [hdid_sum]; omega

theorem phaseCounter_step_p2a {n m : Nat}
    (s : PaxosState n m) (p : Fin m) (v : Value)
    (hp : s.prop p = none) :
    phaseCounter ({ s with prop := setFn s.prop p (some v) }) =
      phaseCounter s + 1 := by
  unfold phaseCounter
  have hcs : countSome (setFn s.prop p (some v)) = countSome s.prop + 1 := by
    unfold countSome
    have hnone : (s.prop p).isSome = false := by simp [hp]
    have hnew : (setFn s.prop p (some v) p).isSome = true := by simp [setFn]
    have :=
      countTrue_flip_one
        (f := fun q : Fin m => (s.prop q).isSome)
        (g := fun q : Fin m => (setFn s.prop p (some v) q).isSome)
        p
        (by intro j hj; simp [setFn, hj])
        hnone
        hnew
    unfold countTrue at this
    exact this
  show
    finSumN (fun p_1 => countTrue (s.got1b p_1)) +
      finSumN (fun p_1 => countTrue (s.did2b p_1)) + countSome (setFn s.prop p (some v)) =
    finSumN (fun p_1 => countTrue (s.got1b p_1)) +
      finSumN (fun p_1 => countTrue (s.did2b p_1)) + countSome s.prop + 1
  rw [hcs]; omega

/-! ## Section 4: The PhaseCountingSystem instantiation -/

/-- Step relation lifted from `paxos n m ballot`. -/
def paxosStep {n m : Nat} (ballot : Fin m → Nat)
    (s s' : PaxosState n m) (a : PaxosAction n m) : Prop :=
  ((paxos n m ballot).actions a).fires s s'

/-- Every step of `paxosStep` increases `phaseCounter` by exactly one. -/
theorem phaseCounter_step {n m : Nat} (ballot : Fin m → Nat)
    (s s' : PaxosState n m) (a : PaxosAction n m)
    (h : paxosStep ballot s s' a) :
    phaseCounter s' = phaseCounter s + 1 := by
  cases a with
  | p1b p i =>
    simp only [paxosStep, GatedAction.fires] at h
    dsimp only [paxos] at h
    obtain ⟨⟨hg1, _⟩, rfl⟩ := h
    exact phaseCounter_step_p1b ballot s p i hg1
  | p2a p =>
    simp only [paxosStep, GatedAction.fires] at h
    dsimp only [paxos] at h
    obtain ⟨⟨hg1, _⟩, v, rfl, _⟩ := h
    exact phaseCounter_step_p2a s p v hg1
  | p2b p i =>
    simp only [paxosStep, GatedAction.fires] at h
    dsimp only [paxos] at h
    obtain ⟨⟨hg1, _⟩, v, _, rfl⟩ := h
    exact phaseCounter_step_p2b ballot s p i v hg1

/-- The bounded-unrolling system wrapping real Paxos. -/
def boundedPaxos (n m : Nat) (ballot : Fin m → Nat) : PhaseCounting.PhaseCountingSystem where
  State        := PaxosState n m
  Action       := PaxosAction n m
  step         := paxosStep ballot
  init         := initialPaxos n m
  phaseCounter := phaseCounter
  bound        := 2 * m * n + m
  init_zero    := phaseCounter_init n m
  step_mono    := by
    intro s s' a h
    have := phaseCounter_step ballot s s' a h
    omega
  step_bounded := by
    intro s s' _ _
    exact phaseCounter_le n m s'

/-! ## Section 5: Safety via PaxosInv -/

/-- Framework-reachability in `boundedPaxos` implies `PaxosInv`. Uses
    term-mode structural recursion (mirroring `Reachable.of_refined`)
    because `Reachable` takes its `PhaseCountingSystem` as a parameter,
    not an index, making `induction`'s motive awkward. -/
theorem paxosInv_of_reachable {n m : Nat} (ballot : Fin m → Nat)
    (h_inj : Function.Injective ballot) :
    ∀ {s : PaxosState n m},
      PhaseCounting.Reachable (boundedPaxos n m ballot) s → PaxosInv ballot s
  | _, .init => paxos_inv_init ballot _ (initialPaxos_isInit ballot)
  | _, .step a hr hstep =>
      paxos_inv_next h_inj _ _ (paxosInv_of_reachable ballot h_inj hr) ⟨a, hstep⟩

/-- The safety target: any two proposers that reach a `did2b` majority
    propose the same value. This is the conclusion of
    `PaxosTextbookN.agreement`. -/
def Safe {n m : Nat} (s : PaxosState n m) : Prop :=
  ∀ p q, majority (s.did2b p) = true → majority (s.did2b q) = true →
         s.prop p = s.prop q

/-- **Main agreement theorem.** Every framework-reachable state of
    `boundedPaxos` satisfies `Safe`. Delegates to the existing
    `PaxosTextbookN.agreement` theorem via `PaxosInv` preservation. -/
theorem boundedPaxos_agreement {n m : Nat} (ballot : Fin m → Nat)
    (h_inj : Function.Injective ballot)
    (s : PaxosState n m)
    (h : PhaseCounting.Reachable (boundedPaxos n m ballot) s) :
    Safe s := by
  intro p q hmp hmq
  exact agreement h_inj (paxosInv_of_reachable ballot h_inj h) p q hmp hmq

/-- Bounded-unrolling corollary: `Safe` holds at every framework-reachable
    state iff it holds along every trace of length `≤ 2·m·n + m`. -/
theorem boundedPaxos_bounded_unrolling {n m : Nat} (ballot : Fin m → Nat) :
    PhaseCounting.safeAll (boundedPaxos n m ballot) Safe ↔
    PhaseCounting.safeUpTo (boundedPaxos n m ballot) Safe (2 * m * n + m) :=
  PhaseCounting.phase_counting_bounded_unrolling (boundedPaxos n m ballot) Safe

end PaxosTextbookN.Bounded
