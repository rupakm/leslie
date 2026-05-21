import Leslie_LTS.Framework.LTL

/-! # Proof Rules for LTS Properties

    Inductive invariants, safety, and basic temporal reasoning.
-/

open Classical

namespace LTS

variable {State : Type u} {Label : Type v}

/-! ## Invariant Rules -/

/-- Inductive invariant for trace properties: if `P` holds at position 0
    of every valid execution and is preserved by stepping forward,
    then `□ P` holds. `P e k` has access to the full execution `e`
    and the current position `k`, so it can reference both past and future. -/
theorem System.invariant (sys : System State Label)
    (P : TraceProp State Label)
    (hinit : ∀ e, sys.valid_exec e → P e 0)
    (hstep : ∀ e k, sys.valid_exec e → P e k → P e (k + 1)) :
    sys.satisfies (always P) := by
  intro e hv j
  show P e (0 + j)
  induction j with
  | zero => exact hinit e hv
  | succ j ih => exact hstep e (0 + j) hv ih

/-- Invariant with strengthening: prove a stronger invariant `I`,
    then weaken to the desired property `P`. -/
theorem System.invariant_via (sys : System State Label)
    (I P : TraceProp State Label)
    (hinit : ∀ e, sys.valid_exec e → I e 0)
    (hstep : ∀ e k, sys.valid_exec e → I e k → I e (k + 1))
    (hcons : ∀ e k, I e k → P e k) :
    sys.satisfies (always P) := by
  have hI := sys.invariant I hinit hstep
  intro e hv j
  have := hI e hv j; simp[Nat.zero_add]; simp only [Nat.zero_add] at this
  exact hcons e j this

/-- Two invariants can be combined into a single conjunctive invariant. -/
theorem System.invariant_and (sys : System State Label)
    (P Q : TraceProp State Label)
    (hP : sys.satisfies (always P))
    (hQ : sys.satisfies (always Q)) :
    sys.satisfies (always (tp_and P Q)) :=
  fun e hv j => ⟨hP e hv j, hQ e hv j⟩

/-- State-predicate invariant: convenience wrapper for `System.invariant`
    when the property is a state predicate `P : State → Prop`. -/
theorem System.state_invariant (sys : System State Label)
    (P : State → Prop)
    (hinit : ∀ s, sys.init s → P s)
    (hstep : ∀ s l s', P s → sys.step s l s' → P s') :
    sys.satisfies [ltl| □ ⌜ P ⌝] :=
  sys.invariant (state_prop P)
    (fun _ hv => hinit _ hv.1)
    (fun _ k hv hp => hstep _ _ _ hp (hv.2 k))

/-- State-predicate invariant with strengthening: convenience wrapper for
    `System.invariant_via` when both `I` and `P` are state predicates. -/
theorem System.state_invariant_via (sys : System State Label)
    (I P : State → Prop)
    (hinit : ∀ s, sys.init s → I s)
    (hstep : ∀ s l s', I s → sys.step s l s' → I s')
    (hcons : ∀ s, I s → P s) :
    sys.satisfies [ltl| □ ⌜ P ⌝] :=
  sys.invariant_via (state_prop I) (state_prop P)
    (fun _ hv => hinit _ hv.1)
    (fun _ k hv hp => hstep _ _ _ hp (hv.2 k))
    (fun _ _ h => hcons _ h)

/-! ## Basic Temporal Lemmas -/

/-- `□ p` entails `p`: always implies now. -/
theorem always_weaken (p : TraceProp State Label) :
    tp_entails (always p) p := by
  intro e k h; exact h 0

/-- `□ p` entails `◇ p`: always implies eventually. -/
theorem always_weaken_to_eventually (p : TraceProp State Label) :
    tp_entails (always p) (eventually p) := by
  intro e k h; exact ⟨0, h 0⟩

/-- `p` entails `◇ p`: now implies eventually. -/
theorem now_weaken_to_eventually (p : TraceProp State Label) :
    tp_entails p (eventually p) := by
  intro e k h; exact ⟨0, h⟩

/-- `□` distributes over conjunction. -/
theorem always_and (p q : TraceProp State Label) :
    always (tp_and p q) = tp_and (always p) (always q) := by
  funext e k; simp [always, tp_and]; constructor
  · intro h; exact ⟨fun j => (h j).1, fun j => (h j).2⟩
  · intro ⟨h1, h2⟩ j; exact ⟨h1 j, h2 j⟩

/-- `◇` distributes over disjunction. -/
theorem eventually_or (p q : TraceProp State Label) :
    eventually (tp_or p q) = tp_or (eventually p) (eventually q) := by
  funext e k; simp [eventually, tp_or]; constructor
  · intro ⟨j, hj⟩; rcases hj with h | h
    · exact Or.inl ⟨j, h⟩
    · exact Or.inr ⟨j, h⟩
  · intro h; rcases h with ⟨j, hj⟩ | ⟨j, hj⟩
    · exact ⟨j, Or.inl hj⟩
    · exact ⟨j, Or.inr hj⟩

/-- Negation of always is eventually-not (duality). -/
theorem not_always (p : TraceProp State Label) :
    tp_not (always p) = eventually (tp_not p) := by
  funext e k; simp [always, eventually, tp_not, not_forall]

/-- Negation of eventually is always-not (duality). -/
theorem not_eventually (p : TraceProp State Label) :
    tp_not (eventually p) = always (tp_not p) := by
  funext e k; simp [always, eventually, tp_not, not_exists]

/-- `□` is idempotent: `□ □ p = □ p`. -/
theorem always_idem (p : TraceProp State Label) :
    always (always p) = always p := by
  funext e k; simp [always]; constructor
  · intro h j; have := h 0 j; rwa [Nat.add_zero] at this
  · intro h j₁ j₂; rw [show k + j₁ + j₂ = k + (j₁ + j₂) from by omega]; exact h (j₁ + j₂)

/-- `◇` is idempotent: `◇ ◇ p = ◇ p`. -/
theorem eventually_idem (p : TraceProp State Label) :
    eventually (eventually p) = eventually p := by
  funext e k; simp [eventually]; constructor
  · intro ⟨j₁, j₂, h⟩; exact ⟨j₁ + j₂, by rwa [show k + (j₁ + j₂) = k + j₁ + j₂ from by omega]⟩
  · intro ⟨j, h⟩; exact ⟨j, 0, by rwa [show k + j + 0 = k + j from by omega]⟩

/-- `□` is monotone: if `p` entails `q` then `□ p` entails `□ q`. -/
theorem always_monotone (p q : TraceProp State Label)
    (h : tp_entails p q) : tp_entails (always p) (always q) :=
  fun e k hp j => h e (k + j) (hp j)

/-- `◇` is monotone: if `p` entails `q` then `◇ p` entails `◇ q`. -/
theorem eventually_monotone (p q : TraceProp State Label)
    (h : tp_entails p q) : tp_entails (eventually p) (eventually q) :=
  fun e k ⟨j, hj⟩ => ⟨j, h e (k + j) hj⟩

/-- `□` commutes with universal quantification. -/
theorem always_forall {α : Sort w} (p : α → TraceProp State Label) :
    always (tp_forall p) = tp_forall (fun x => always (p x)) := by
  funext e k; simp [always, tp_forall]
  exact ⟨fun h x j => h j x, fun h j x => h x j⟩

end LTS
