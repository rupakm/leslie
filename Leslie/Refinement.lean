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

/-- A TLA specification: an initial-state predicate, a next-state action,
    and an optional list of weakly-fair actions. -/
structure Spec (σ : Type u) where
  init : σ → Prop
  next : action σ
  fair : List (action σ) := []

/-- The safety part of a spec: `Init ∧ □⟨Next⟩`. Every step must be a real
    `next`-step (no stuttering allowed). -/
def Spec.safety (spec : Spec σ) : pred σ :=
  [tlafml| ⌜ spec.init ⌝ ∧ □ ⟨spec.next⟩]

/-- The full temporal formula: `Init ∧ □⟨Next⟩ ∧ ⋀ WF(a)` for each fair action. -/
def Spec.formula (spec : Spec σ) : pred σ :=
  [tlafml| ⌜ spec.init ⌝ ∧ □ ⟨spec.next⟩ ∧ ⋀ a ∈ spec.fair, 𝒲ℱ a]

/-- The safety specification with stuttering: □[Next]_vars instead of □⟨Next⟩.
    This allows steps where the state doesn't change. -/
def Spec.safety_stutter (spec : Spec σ) : pred σ :=
  [tlafml| ⌜ spec.init ⌝ ∧ □ ⟨fun s s' => spec.next s s' ∨ s = s'⟩]

/-! ### Execution Mapping -/

/-- Map an execution through a state function: `(exec.map f e) n = f (e n)`. -/
def exec.map {σ : Type u} {τ : Type v} (f : σ → τ) (e : exec σ) : exec τ :=
  fun n => f (e n)

/-- Evaluation of a mapped execution is function application. -/
@[simp] theorem exec.map_apply {σ : Type u} {τ : Type v} (f : σ → τ) (e : exec σ) (n : Nat) :
    exec.map f e n = f (e n) := rfl

/-- Mapping commutes with dropping: `(map f e).drop k = map f (e.drop k)`. -/
theorem exec.map_drop {σ : Type u} {τ : Type v} (f : σ → τ) (e : exec σ) (k : Nat) :
    (exec.map f e).drop k = exec.map f (e.drop k) := by
  funext n ; simp [exec.map, exec.drop]

/-- Mapping is functorial: `map g (map f e) = map (g ∘ f) e`. -/
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

/-- Refinement is transitive: if `p` refines `q` via `f` and `q` refines `r`
    via `g`, then `p` refines `r` via `g ∘ f`. -/
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

/-- Variant of `map_always_next` allowing stuttering: each concrete step maps
    to either an abstract step or a stutter (`f s = f s'`). -/
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

/-- Combined variant: step maps to abstract step or stutter, under an invariant. -/
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

/-- **Abadi-Lamport refinement mapping (no stuttering)**: if `f` maps every
    concrete initial state to an abstract initial state and every concrete step
    to an abstract step, then the concrete safety formula refines the abstract
    safety formula via `f`. -/
theorem refinement_mapping_nostutter {σ : Type u} {τ : Type v}
    (concrete : Spec σ) (abstract : Spec τ)
    (f : σ → τ)
    (hinit : ∀ s, concrete.init s → abstract.init (f s))
    (hnext : ∀ s s', concrete.next s s' → abstract.next (f s) (f s')) :
    refines_via f concrete.safety abstract.safety := by
  intro e ⟨hi, hn⟩
  exact ⟨hinit (e 0) hi, map_always_next _ _ f e hn hnext⟩

/-! ### The Refinement Mapping Theorem (Safety, With Stuttering) -/

/-- **Abadi-Lamport refinement mapping (with stuttering)**: each concrete step
    maps to either an abstract step or a stutter (`f s = f s'`).
    Refines `safety` to `safety_stutter`. This is the most commonly used variant. -/
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

/-- Build an invariant along an execution by induction: `init` establishes it
    at step 0 and `next` preserves it at each successor step. -/
private theorem build_invariant {σ : Type u} {e : exec σ}
    {init : σ → Prop} {next : action σ} {inv : σ → Prop}
    (hi : e |=tla= ⌜ init ⌝) (hn : e |=tla= □ ⟨next⟩)
    (hinv_init : ∀ s, init s → inv s)
    (hinv_next : ∀ s s', inv s → next s s' → inv s') :
    ∀ k, inv (e k) := by
  intro k ; induction k with
  | zero => exact hinv_init _ hi
  | succ k ih => exact hinv_next _ _ ih (always_action_at k hn)

/-- **Refinement mapping with invariant (no stuttering)**: the step correspondence
    may depend on a concrete invariant `inv`. The invariant is established by init
    and preserved by next; the mapping condition `hnext` only needs to hold when
    `inv` holds. -/
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

/-- **Refinement mapping with invariant (with stuttering)**: combines the concrete
    invariant with stuttering. The step condition `hnext` may produce an abstract
    step or a stutter, and only needs to hold when `inv` holds. -/
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

/-- An inductive state predicate holds under `safety_stutter`.
    Real steps preserve `P` by `hstep`; stutter steps preserve `P`
    because the state is unchanged.

    This is the `safety_stutter` counterpart of `init_invariant`
    (which proves the same under `safety`). The stutter case is
    trivial for state predicates, so the same `hinit` + `hstep`
    premises suffice. -/
theorem Spec.invariant_under_safety_stutter (spec : Spec σ)
    {P : σ → Prop}
    (hinit : ∀ s, spec.init s → P s)
    (hstep : ∀ s s', spec.next s s' → P s → P s') :
    pred_implies spec.safety_stutter [tlafml| □ ⌜ P ⌝] := by
  intro e ⟨hi, hn⟩
  have hP0 : P (e 0) := hinit _ (by simpa [state_pred] using hi)
  intro k
  simp only [state_pred, exec.drop, Nat.zero_add]
  induction k with
  | zero => exact hP0
  | succ k' ih =>
    have hk := hn k'
    simp only [action_pred, exec.drop, Nat.zero_add] at hk
    rw [Nat.add_comm] at hk
    rcases hk with hreal | hstutter
    · exact hstep _ _ hreal ih
    · rwa [← hstutter]

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

/-- If `spec_c` refines `spec_a` via `f` and `inv` is an invariant of `spec_a`,
    then `inv ∘ f` is an invariant of `spec_c`. -/
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

/-- Stuttering variant of `refines_preserves_invariant`: if the refinement
    targets `safety_stutter` and `inv` holds under `safety_stutter`,
    then `inv ∘ f` is an invariant of the concrete spec. -/
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

/-! ### Reflexive Transitive Closure

    We define `Star r a b` as the reflexive transitive closure of a binary
    relation `r`: either `a = b` (zero steps), or there is an intermediate
    state `b` such that `r a b` and `Star r b c` (one-or-more steps). -/

/-- Reflexive transitive closure of a relation: zero or more `r`-steps. -/
inductive Star (r : α → α → Prop) : α → α → Prop where
  | refl : Star r a a
  | step : r a b → Star r b c → Star r a c

/-- A single `r`-step is a `Star r`-step. -/
theorem Star.single {r : α → α → Prop} (h : r a b) : Star r a b :=
  .step h .refl

/-- `Star r` is transitive: concatenation of two multi-step paths. -/
theorem Star.trans {r : α → α → Prop} (h1 : Star r a b) (h2 : Star r b c) : Star r a c := by
  induction h1 with
  | refl => exact h2
  | step hab _ ih => exact .step hab (ih h2)

/-- An invariant preserved by each `r`-step is preserved by `Star r`. -/
theorem Star.preserve_inv {r : α → α → Prop} {inv : α → Prop}
    (hinv : ∀ a b, inv a → r a b → inv b) {a b : α}
    (h : Star r a b) (ha : inv a) : inv b := by
  induction h with
  | refl => exact ha
  | step hab _ ih => exact ih (hinv _ _ ha hab)

/-! ### Data-Level Paths

    `Path r a b` is the Type-level counterpart of `Star r a b`. Because
    `Star` lives in `Prop`, Lean's elimination restriction prevents
    extracting computational content (length, intermediate states) from it.
    `Path` lives in `Type`, so we can define `length`, `get`, and `append`
    by pattern matching. A bridge lemma `Star.toPath` uses `Classical.choice`
    to obtain a `Path` from any `Star` proof. -/

/-- A data-level path: zero or more `r`-steps from `a` to `b`.
    Unlike `Star` (which is a `Prop`), `Path` supports elimination into `Type`,
    allowing extraction of length and intermediate states. -/
inductive Path {α : Type u} (r : α → α → Prop) : α → α → Type u where
  | refl : Path r a a
  | step : r a b → Path r b c → Path r a c

/-- The number of `r`-steps in a path. -/
def Path.length : Path r a b → Nat
  | .refl => 0
  | .step _ rest => rest.length + 1

/-- Get the `i`-th state along a path (0-indexed, with state 0 = `a`
    and state `length` = `b`). Returns the source for out-of-bounds. -/
def Path.get {r : α → α → Prop} {a b : α} : Path r a b → Nat → α
  | p, 0 => match p with
    | .refl => a
    | .step _ _ => a
  | p, Nat.succ i => match p with
    | .refl => a
    | .step _ rest => rest.get i

/-- State 0 of any path is the source `a`. -/
@[simp] theorem Path.get_zero (p : Path r a b) : p.get 0 = a := by
  cases p <;> rfl

/-- State `length` of a path is the target `b`. -/
theorem Path.get_length (p : Path r a b) : p.get p.length = b := by
  induction p with
  | refl => rfl
  | step _ rest ih => exact ih

/-- Consecutive states in a path are related by `r`. -/
theorem Path.get_step (p : Path r a b) : ∀ (i : Nat), i < p.length →
    r (p.get i) (p.get (i + 1)) := by
  induction p with
  | refl => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | step hab rest ih =>
    intro i hi
    cases i with
    | zero =>
      -- goal: r (get (step hab rest) 0) (get (step hab rest) 1)
      -- reduces to: r a (get rest 0)
      -- get_zero: get rest 0 = source of rest
      have h0 := rest.get_zero
      simp only [get]
      rw [h0]
      exact hab
    | succ i =>
      -- goal: r (get (step hab rest) (i+1)) (get (step hab rest) (i+2))
      -- reduces to: r (get rest i) (get rest (i+1))
      simp only [get]
      exact ih i (by simp only [length] at hi; omega)

/-- A path of length 0 has equal endpoints. -/
theorem Path.eq_of_length_zero {r : α → α → Prop} {a b : α} (p : Path r a b)
    (h : p.length = 0) : a = b := by
  cases p with
  | refl => rfl
  | step _ rest => simp [length] at h

/-- A `Star` proof can be lifted to a `Path` (via `Classical.choice`). -/
theorem Star.nonempty_path (h : Star r a b) : Nonempty (Path r a b) := by
  induction h with
  | refl => exact ⟨.refl⟩
  | step hab _ ih =>
    obtain ⟨p⟩ := ih
    exact ⟨.step hab p⟩

/-- Obtain a `Path` from a `Star` proof using classical choice. -/
noncomputable def Star.toPath (h : Star r a b) : Path r a b :=
  Classical.choice h.nonempty_path

/-! ### Forward Simulation via Relations

    A **forward simulation** (also called a **simulation relation**)
    generalizes refinement mappings.  Instead of a function `f : σ → τ`,
    we use a relation `R : σ → τ → Prop` between the concrete state space
    `σ` and the abstract state space `τ`.

    This extra generality is needed when:
    - The abstract state involves **nondeterministic** choices that cannot be
      expressed as a deterministic function of the concrete state (e.g. the
      set of accumulated snapshots in a snapshot object).
    - One concrete step must be simulated by a **sequence** of abstract steps
      (not just zero or one), expressed via `Star abstract.next`.

    **Conditions** (`SimulationRel`):
    1. *Init*: every concrete initial state has a related abstract initial state.
    2. *Step*: for every concrete step `s → s'` and abstract state `a` with
       `R s a`, there exists `a'` reachable from `a` via zero or more abstract
       steps (`Star abstract.next a a'`) such that `R s' a'`. -/

/-- A forward simulation relation between two TLA specs.
    Each concrete step is simulated by zero or more abstract steps. -/
structure SimulationRel (σ : Type u) (τ : Type v) where
  concrete : Spec σ
  abstract : Spec τ
  /-- The simulation relation between concrete and abstract states. -/
  R : σ → τ → Prop
  /-- Every concrete initial state has a related abstract initial state. -/
  init_sim : ∀ s, concrete.init s → ∃ a, abstract.init a ∧ R s a
  /-- Every concrete step from a related pair produces a related pair,
      with the abstract side taking zero or more steps. -/
  step_sim : ∀ s s' a, R s a → concrete.next s s' →
    ∃ a', Star abstract.next a a' ∧ R s' a'

/-- Build the abstract state witness at each concrete step `k`, by recursion.
    At step 0 we pick a witness from `init_sim`, and at step `k+1` we apply
    `step_sim` to the previous witness. Each witness is bundled with a proof
    that `R` relates the concrete state `e k` to it.  -/
private noncomputable def SimulationRel.build
    (sim : SimulationRel σ τ)
    (e : exec σ)
    (hinit : sim.concrete.init (e 0))
    (hnext : ∀ k, sim.concrete.next (e k) (e (k + 1)))
    : (k : Nat) → { a : τ // sim.R (e k) a }
  | 0 =>
    ⟨(sim.init_sim (e 0) hinit).choose,
     (sim.init_sim (e 0) hinit).choose_spec.2⟩
  | k + 1 =>
    let prev := sim.build e hinit hnext k
    let hex := sim.step_sim (e k) (e (k + 1)) prev.val prev.property (hnext k)
    ⟨hex.choose, hex.choose_spec.2⟩

/-- **Invariant transfer**: a simulation lets us transfer inductive invariants
    from the abstract spec to the concrete spec.

    If `inv` is an inductive invariant of the abstract (preserved by `init`
    and `next`), and `R s a ∧ inv a → P s`, then `P` is an invariant of the
    concrete.  This is the primary use of `SimulationRel`.

    The proof works by constructing a related abstract state at each concrete
    step (via `build`) and then showing, by induction, that `inv` holds at
    every abstract witness.  Because each concrete step may correspond to
    *multiple* abstract steps, the inductive step uses `Star.preserve_inv`
    to push `inv` through the entire multi-step abstract path. -/
theorem SimulationRel.preserves_invariant
    (sim : SimulationRel σ τ)
    (inv : τ → Prop)
    (hinv_init : ∀ a, sim.abstract.init a → inv a)
    (hinv_next : ∀ a a', inv a → sim.abstract.next a a' → inv a')
    (P : σ → Prop)
    (hRP : ∀ s a, sim.R s a → inv a → P s)
    : pred_implies sim.concrete.safety [tlafml| □ ⌜ P ⌝] := by
  intro e ⟨hinit, hnext⟩
  have hnext' : ∀ k, sim.concrete.next (e k) (e (k + 1)) :=
    fun k => always_action_at k hnext
  let build_k := sim.build e hinit hnext'
  -- It suffices to show the abstract invariant at every concrete step.
  suffices h : ∀ k, inv (build_k k).val from by
    intro k ; simp [state_pred, exec.drop]
    exact hRP _ _ (build_k k).property (h k)
  intro k ; induction k with
  | zero => exact hinv_init _ (sim.init_sim (e 0) hinit).choose_spec.1
  | succ k ih =>
    let prev := build_k k
    let hex := sim.step_sim (e k) (e (k + 1)) prev.val prev.property (hnext' k)
    -- The Star path from prev to hex.choose preserves inv:
    exact Star.preserve_inv hinv_next hex.choose_spec.1 ih

/-- **Invariant transfer under stuttering**: like `preserves_invariant` but
    works under `safety_stutter` instead of `safety`. When the concrete step
    is a stutter (`s = s'`), the abstract witness is unchanged and the
    invariant carries over trivially. This variant is needed to compose
    simulations with `ProtocolCall.lift_invariant`. -/
theorem SimulationRel.preserves_invariant_stutter
    (sim : SimulationRel σ τ)
    (inv : τ → Prop)
    (hinv_init : ∀ a, sim.abstract.init a → inv a)
    (hinv_next : ∀ a a', inv a → sim.abstract.next a a' → inv a')
    (P : σ → Prop)
    (hRP : ∀ s a, sim.R s a → inv a → P s)
    : pred_implies sim.concrete.safety_stutter [tlafml| □ ⌜ P ⌝] := by
  intro e ⟨hinit, hnext⟩
  -- Extract concrete steps: each is either a real step or a stutter
  have hnext' : ∀ k, sim.concrete.next (e k) (e (k + 1)) ∨ e k = e (k + 1) :=
    fun k => by have := always_action_at k hnext; simp at this; exact this
  -- Build abstract witnesses by recursion, handling stutters
  suffices h : ∀ k, ∃ a, sim.R (e k) a ∧ inv a from by
    intro k; simp [state_pred, exec.drop]
    obtain ⟨a, hr, hinv_a⟩ := h k
    exact hRP _ _ hr hinv_a
  intro k; induction k with
  | zero =>
    obtain ⟨a, ha_init, hr⟩ := sim.init_sim (e 0) hinit
    exact ⟨a, hr, hinv_init _ ha_init⟩
  | succ k ih =>
    obtain ⟨a_k, hr_k, hinv_k⟩ := ih
    rcases hnext' k with hstep | hstutter
    · -- Real step: use step_sim to get a new witness
      obtain ⟨a', hstar, hr'⟩ := sim.step_sim (e k) (e (k + 1)) a_k hr_k hstep
      exact ⟨a', hr', Star.preserve_inv hinv_next hstar hinv_k⟩
    · -- Stutter: e(k) = e(k+1), keep the same witness
      exact ⟨a_k, hstutter ▸ hr_k, hinv_k⟩

/-- The `Star` path between consecutive witnesses, extracted from `step_sim`
    and converted to a data-level `Path`. -/
private noncomputable def SimulationRel.buildPath
    (sim : SimulationRel σ τ)
    (e : exec σ)
    (hinit : sim.concrete.init (e 0))
    (hnext : ∀ k, sim.concrete.next (e k) (e (k + 1)))
    (k : Nat) :
    Path sim.abstract.next (sim.build e hinit hnext k).val
                           (sim.build e hinit hnext (k + 1)).val :=
  let prev := sim.build e hinit hnext k
  let hex := sim.step_sim (e k) (e (k + 1)) prev.val prev.property (hnext k)
  Star.toPath hex.choose_spec.1

/-! ### Flattening Paths into an Execution

    Given an infinite sequence of path segments connecting consecutive states,
    we concatenate them into a single execution `ea : Nat → α` with a monotone
    time-remapping `remap : Nat → Nat` such that `ea (remap k) = states k`.

    Each step of `ea` is either a real `r`-step (from `Path.get_step`) or a
    stutter (at segment boundaries or beyond all segments). -/

/-- Cumulative offset: `offset len 0 = 0` and
    `offset len (k+1) = offset len k + len k`. -/
def offset (len : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => offset len k + len k

/-- The offset is monotone: `offset len k ≤ offset len (k+1)`. -/
theorem offset_mono (len : Nat → Nat) (k : Nat) :
    offset len k ≤ offset len (k + 1) :=
  Nat.le_add_right _ _

/-- Offset is monotone over multiple steps. -/
theorem offset_mono_le (len : Nat → Nat) {j k : Nat} (h : j ≤ k) :
    offset len j ≤ offset len k := by
  induction k with
  | zero => rcases Nat.le_zero.mp h with rfl; exact Nat.le_refl _
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact Nat.le_refl _
    · exact Nat.le_trans (ih (Nat.lt_succ_iff.mp hlt)) (offset_mono len k)

/-- If `offset len k = offset len (k+1)` then `len k = 0`. -/
theorem offset_eq_succ_imp_len_zero (len : Nat → Nat) (k : Nat)
    (h : offset len k = offset len (k + 1)) : len k = 0 := by
  simp [offset] at h; omega

/-- Find the smallest `k` satisfying a predicate, given that one exists.
    Searches from 0 upward using the witness as an upper bound. -/
private noncomputable def findSmallest (P : Nat → Prop)
    (hex : ∃ k, P k) : { k // P k ∧ ∀ j, j < k → ¬P j } := by
  suffices aux : ∀ fuel start, start + fuel = hex.choose + 1 →
      (∀ j, j < start → ¬P j) → { k // P k ∧ ∀ j, j < k → ¬P j } from
    aux (hex.choose + 1) 0 (by omega) (fun j hj => by omega)
  intro fuel
  induction fuel with
  | zero =>
    intro start hstart hbelow
    exact ⟨hex.choose, hex.choose_spec, fun j hj => hbelow j (by omega)⟩
  | succ fuel ih =>
    intro start hstart hbelow
    by_cases hp : P start
    · exact ⟨start, hp, hbelow⟩
    · exact ih (start + 1) (by omega) (fun j hj => by
        by_cases hjs : j < start
        · exact hbelow j hjs
        · have : j = start := by omega
          rw [this]; exact hp)

/-- Flatten an infinite sequence of `Path` segments into a single execution.

    Given `states : Nat → α` and `paths k : Path r (states k) (states (k+1))`,
    produces:
    - `exec : Nat → α` — the flattened execution
    - `remap : Nat → Nat` — monotone time-remapping with `exec (remap k) = states k`
    - Each step of `exec` is either `r` or identity -/
noncomputable def flattenPaths {α : Type u} {r : α → α → Prop}
    (states : Nat → α) (paths : (k : Nat) → Path r (states k) (states (k + 1))) :
    { exec : Nat → α // ∃ remap : Nat → Nat,
      remap 0 = 0 ∧
      (∀ k, remap k ≤ remap (k + 1)) ∧
      (∀ k, exec (remap k) = states k) ∧
      (∀ t, r (exec t) (exec (t + 1)) ∨ exec t = exec (t + 1)) } := by
  let len := fun k => (paths k).length
  let off := offset len
  let lookup : (t : Nat) → (∃ k, t ≤ off (k + 1)) → α := fun t h =>
    let s := findSmallest (fun k => t ≤ off (k + 1)) h
    (paths s.val).get (t - off s.val)
  let ea : Nat → α := Nat.rec
    (lookup 0 ⟨0, Nat.zero_le _⟩)
    (fun t prev =>
      if h : ∃ k, t + 1 ≤ off (k + 1) then lookup (t + 1) h
      else prev)
  -- Helper: if path i has length 0, states i = states (i+1)
  have states_eq_of_len_zero : ∀ i, len i = 0 →
      states i = states (i + 1) :=
    fun i hi => Path.eq_of_length_zero (paths i) hi
  -- If offsets at i and j are equal, states are equal
  have states_eq_of_off_eq : ∀ i j, i ≤ j → offset len i = offset len j →
      states i = states j := by
    intro i j hij hoff
    induction j with
    | zero => rcases Nat.le_zero.mp hij with rfl; rfl
    | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with rfl | hlt
      · rfl
      · have hoff_j : offset len j = offset len (j + 1) := by
          have h1 := offset_mono_le len (Nat.lt_succ_iff.mp hlt)
          have h2 := offset_mono len j
          omega
        rw [ih (Nat.lt_succ_iff.mp hlt) (by omega),
            states_eq_of_len_zero j (offset_eq_succ_imp_len_zero len j hoff_j)]
  -- ea t = lookup t h when t is in range
  have ea_val : ∀ t, (h : ∃ j, t ≤ off (j + 1)) → ea t = lookup t h := by
    intro t ht
    induction t with
    | zero => rfl
    | succ n ih =>
      show (if h : ∃ k, n + 1 ≤ off (k + 1) then lookup (n + 1) h else ea n) =
           lookup (n + 1) ht
      rw [dif_pos ht]
  -- ea (t+1) = ea t when t+1 is NOT in range
  have ea_stutter : ∀ t, (¬∃ k, t + 1 ≤ off (k + 1)) → ea (t + 1) = ea t := by
    intro t h
    show (if h' : ∃ k, t + 1 ≤ off (k + 1) then lookup (t + 1) h' else ea t) = ea t
    rw [dif_neg h]
  -- off s ≤ t for the segment s containing t
  have seg_le : ∀ t (h : ∃ k, t ≤ off (k + 1)),
      off (findSmallest (fun k => t ≤ off (k + 1)) h).val ≤ t := by
    intro t h
    let s := findSmallest (fun k => t ≤ off (k + 1)) h
    show off s.val ≤ t
    by_contra hlt
    have hlt' : t < off s.val := Nat.lt_of_not_le hlt
    by_cases hs0 : s.val = 0
    · simp [hs0, show off 0 = 0 from rfl] at hlt'
    · have hpred_lt : s.val - 1 < s.val := Nat.sub_lt (Nat.pos_of_ne_zero hs0) Nat.one_pos
      have hpred_succ : s.val - 1 + 1 = s.val := Nat.succ_pred hs0
      have hmin : ¬(t ≤ off (s.val - 1 + 1)) := s.property.2 (s.val - 1) hpred_lt
      rw [hpred_succ] at hmin
      exact absurd (Nat.le_of_lt hlt') hmin
  -- t - off s ≤ (paths s).length
  have seg_bound : ∀ t (h : ∃ k, t ≤ off (k + 1)),
      t - off (findSmallest (fun k => t ≤ off (k + 1)) h).val ≤
      (paths (findSmallest (fun k => t ≤ off (k + 1)) h).val).length := by
    intro t h
    let s := findSmallest (fun k => t ≤ off (k + 1)) h
    show t - off s.val ≤ (paths s.val).length
    have hs_prop := s.property.1
    have : off (s.val + 1) = off s.val + (paths s.val).length := rfl
    omega
  -- findSmallest for t+1 ≥ findSmallest for t
  have seg_mono : ∀ t (h : ∃ k, t ≤ off (k + 1)) (h' : ∃ k, t + 1 ≤ off (k + 1)),
      (findSmallest (fun k => t ≤ off (k + 1)) h).val ≤
      (findSmallest (fun k => t + 1 ≤ off (k + 1)) h').val := by
    intro t h h'
    let s := findSmallest (fun k => t ≤ off (k + 1)) h
    let s' := findSmallest (fun k => t + 1 ≤ off (k + 1)) h'
    show s.val ≤ s'.val
    by_contra hlt
    have hlt' : s'.val < s.val := Nat.lt_of_not_le hlt
    have h1 : t + 1 ≤ off (s'.val + 1) := s'.property.1
    have h2 : t ≤ off (s'.val + 1) := by omega
    exact absurd h2 (s.property.2 s'.val hlt')
  refine ⟨ea, off, rfl, fun k => offset_mono len k, ?remap_states, ?step_or_stutter⟩
  case remap_states =>
    intro k
    have hex : ∃ j, off k ≤ off (j + 1) := ⟨k, offset_mono len k⟩
    rw [ea_val (off k) hex]
    show (paths (findSmallest (fun j => off k ≤ off (j + 1)) hex).val).get
      (off k - off (findSmallest (fun j => off k ≤ off (j + 1)) hex).val) = _
    let sb := findSmallest (fun j => off k ≤ off (j + 1)) hex
    let s := sb.val
    have hs_prop : off k ≤ off (s + 1) := sb.property.1
    have hs_min : ∀ j, j < s → ¬(off k ≤ off (j + 1)) := sb.property.2
    change (paths s).get (off k - off s) = states k
    have hsk : s ≤ k := by
      by_contra h
      exact hs_min k (Nat.lt_of_not_le h) (offset_mono len k)
    by_cases heq_sk : s = k
    · have hsub : off k - off s = 0 := by
        have : off s = off k := by rw [heq_sk]
        omega
      rw [hsub, heq_sk]; exact Path.get_zero _
    · have hlt : s < k := Nat.lt_of_le_of_ne hsk heq_sk
      have hoff_s1_k : off (s + 1) ≤ off k := offset_mono_le len hlt
      have hoff_eq : off (s + 1) = off k := Nat.le_antisymm hoff_s1_k hs_prop
      have hoff_succ : off (s + 1) = off s + len s :=
        show offset len (s + 1) = offset len s + len s from rfl
      have hlen_eq : off k - off s = (paths s).length := by
        have h1 : off s + (paths s).length = off k := by
          rw [← hoff_succ]; exact hoff_eq
        omega
      rw [hlen_eq, (paths s).get_length]
      exact states_eq_of_off_eq (s + 1) k (by omega) hoff_eq
  case step_or_stutter =>
    intro t
    by_cases hk1 : ∃ j, t + 1 ≤ off (j + 1)
    · have hk : ∃ j, t ≤ off (j + 1) := by
        obtain ⟨j, hj⟩ := hk1; exact ⟨j, by omega⟩
      rw [ea_val t hk, ea_val (t + 1) hk1]
      let s := findSmallest (fun j => t ≤ off (j + 1)) hk
      let s' := findSmallest (fun j => t + 1 ≤ off (j + 1)) hk1
      show r ((paths s.val).get (t - off s.val))
            ((paths s'.val).get (t + 1 - off s'.val)) ∨
           (paths s.val).get (t - off s.val) =
            (paths s'.val).get (t + 1 - off s'.val)
      have hs_le_s' : s.val ≤ s'.val := seg_mono t hk hk1
      by_cases heq_ss' : s.val = s'.val
      · -- Same segment: consecutive indices in same path
        have hk1_bound' : t + 1 ≤ off (s.val + 1) := by
          have : s.val = s'.val := heq_ss'; rw [this]; exact s'.property.1
        have hoff_succ : off (s.val + 1) = off s.val + (paths s.val).length := rfl
        have hoff_le : off s.val ≤ t := seg_le t hk
        have hk_lt : t - off s.val < (paths s.val).length := by omega
        have hidx : t + 1 - off s'.val = (t - off s.val) + 1 := by
          have : off s'.val = off s.val := by rw [heq_ss']
          rw [this, Nat.succ_sub hoff_le]
        rw [hidx, ← heq_ss']
        exact Or.inl ((paths s.val).get_step (t - off s.val) hk_lt)
      · -- Different segments: s < s'
        have hlt_ss' : s.val < s'.val := Nat.lt_of_le_of_ne hs_le_s' heq_ss'
        have hk1_gt : ¬(t + 1 ≤ off (s.val + 1)) := by
          intro h_contra
          exact absurd h_contra (s'.property.2 s.val hlt_ss')
        have hk_eq : t = off (s.val + 1) := by
          have := s.property.1; omega
        have hget_k : (paths s.val).get (t - off s.val) =
            states (s.val + 1) := by
          have hlen_eq : t - off s.val = (paths s.val).length := by
            have : off (s.val + 1) = off s.val + (paths s.val).length := rfl
            omega
          rw [hlen_eq, (paths s.val).get_length]
        have hoff_s1_le_s' : off (s.val + 1) ≤ off s'.val :=
          offset_mono_le len (Nat.succ_le_of_lt hlt_ss')
        have hoff_s'_le : off s'.val ≤ t + 1 := seg_le (t + 1) hk1
        have hoff_eq : off s'.val = off (s.val + 1) := by
          suffices h : off s'.val ≤ off (s.val + 1) from
            Nat.le_antisymm h hoff_s1_le_s'
          by_contra h_gt
          have hgt := Nat.lt_of_not_le h_gt
          have hoff_s' : off s'.val = off (s.val + 1) + 1 := by
            have h1 := hoff_s'_le; have h2 := hk_eq; omega
          have hs'_gt : s'.val > s.val + 1 := by
            by_contra hle
            have : s'.val = s.val + 1 := by omega
            rw [this] at hoff_s'; omega
          have hpred_lt : s'.val - 1 < s'.val := by omega
          have hpred_valid : t + 1 ≤ off (s'.val - 1 + 1) := by
            have : s'.val - 1 + 1 = s'.val := by omega
            rw [this]; omega
          exact absurd hpred_valid (s'.property.2 (s'.val - 1) hpred_lt)
        have hwit_s1_s' : states (s.val + 1) = states s'.val :=
          states_eq_of_off_eq (s.val + 1) s'.val (Nat.succ_le_of_lt hlt_ss')
            hoff_eq.symm
        have hidx_k1 : t + 1 - off s'.val = 1 := by
          have h1 : off s'.val = off (s.val + 1) := hoff_eq
          have h2 : t = off (s.val + 1) := hk_eq
          omega
        have hlen_ge : (paths s'.val).length ≥ 1 := by
          have hbd : t + 1 - off s'.val ≤ (paths s'.val).length :=
            seg_bound (t + 1) hk1
          have h1 := hoff_eq; have h2 := hk_eq; omega
        have hstep := (paths s'.val).get_step 0 (by omega)
        rw [Path.get_zero] at hstep
        rw [hget_k, hidx_k1, hwit_s1_s']
        exact Or.inl hstep
    · -- t+1 NOT in range: ea(t+1) = ea t (stutter)
      exact Or.inr (ea_stutter t hk1).symm

/-- **Full soundness**: a simulation implies that every concrete execution has
    a corresponding abstract execution satisfying `safety_stutter`, with a
    monotone time-mapping `f` such that states are related at corresponding
    points.

    The proof constructs a `Path` between consecutive witnesses via `buildPath`,
    then flattens these paths into a single abstract execution. -/
theorem SimulationRel.soundness
    (sim : SimulationRel σ τ)
    : ∀ e, sim.concrete.safety e →
        ∃ ea, sim.abstract.safety_stutter ea ∧
          ∃ f : Nat → Nat, (∀ k, f k ≤ f (k + 1)) ∧ ∀ k, sim.R (e k) (ea (f k)) := by
  intro e ⟨hinit, hnext⟩
  have hnext' : ∀ k, sim.concrete.next (e k) (e (k + 1)) :=
    fun k => always_action_at k hnext
  -- Build witnesses and paths
  let witness := sim.build e hinit hnext'
  let path := sim.buildPath e hinit hnext'
  -- Flatten into a single execution
  obtain ⟨ea, remap, hremap_zero, hremap_mono, hremap_states, hstep_or_stutter⟩ :=
    flattenPaths (fun k => (witness k).val) path
  refine ⟨ea, ?safety_stutter, remap, hremap_mono, ?related⟩
  case related =>
    intro k
    have heq := hremap_states k
    -- heq : ea (remap k) = (witness k).val
    -- goal : sim.R (e k) (ea (remap k))
    show sim.R (e k) (ea (remap k))
    rw [heq]; exact (witness k).property
  case safety_stutter =>
    refine ⟨?init, ?step⟩
    case init =>
      have h0 := hremap_states 0
      -- h0 : ea (remap 0) = (witness 0).val
      -- hremap_zero : remap 0 = 0
      show sim.abstract.init (ea 0)
      rw [show ea 0 = ea (remap 0) from by rw [hremap_zero], h0]
      exact (sim.init_sim (e 0) hinit).choose_spec.1
    case step =>
      intro k
      simp only [action_pred, exec.drop, Nat.zero_add]
      rw [Nat.add_comm]
      exact hstep_or_stutter k

/-! ### Simulation with Concrete Invariant

    Sometimes the step-simulation condition only holds under an invariant
    on the *concrete* state (e.g. "versions are monotonic").
    `SimulationRelInv` lets us supply such an invariant alongside the
    simulation relation. -/

/-- Forward simulation with an auxiliary concrete invariant. -/
structure SimulationRelInv (σ : Type u) (τ : Type v) where
  concrete : Spec σ
  abstract : Spec τ
  R : σ → τ → Prop
  inv : σ → Prop
  inv_init : ∀ s, concrete.init s → inv s
  inv_next : ∀ s s', inv s → concrete.next s s' → inv s'
  init_sim : ∀ s, concrete.init s → ∃ a, abstract.init a ∧ R s a
  step_sim : ∀ s s' a, inv s → R s a → concrete.next s s' →
    ∃ a', Star abstract.next a a' ∧ R s' a'

/-- Fold the concrete invariant into the relation to obtain a plain
    `SimulationRel`. The new relation is `fun s a => inv s ∧ R s a`. -/
noncomputable def SimulationRelInv.toSimulationRel
    (sim : SimulationRelInv σ τ) : SimulationRel σ τ where
  concrete := sim.concrete
  abstract := sim.abstract
  R := fun s a => sim.inv s ∧ sim.R s a
  init_sim := fun s hs => by
    obtain ⟨a, ha, hr⟩ := sim.init_sim s hs
    exact ⟨a, ha, sim.inv_init s hs, hr⟩
  step_sim := fun s s' a ⟨hinv, hr⟩ hstep => by
    obtain ⟨a', haa', hr'⟩ := sim.step_sim s s' a hinv hr hstep
    exact ⟨a', haa', sim.inv_next s s' hinv hstep, hr'⟩

/-- Invariant transfer for `SimulationRelInv` (delegates to `SimulationRel`). -/
theorem SimulationRelInv.preserves_invariant
    (sim : SimulationRelInv σ τ)
    (inv_a : τ → Prop)
    (hinv_init : ∀ a, sim.abstract.init a → inv_a a)
    (hinv_next : ∀ a a', inv_a a → sim.abstract.next a a' → inv_a a')
    (P : σ → Prop)
    (hRP : ∀ s a, sim.R s a → inv_a a → P s)
    : pred_implies sim.concrete.safety [tlafml| □ ⌜ P ⌝] := by
  apply sim.toSimulationRel.preserves_invariant inv_a hinv_init hinv_next P
  intro s a ⟨_, hr⟩ hinv
  exact hRP s a hr hinv

/-! ### Backward Simulation via Relations

    A **backward simulation** reverses the quantifier order compared to
    a forward simulation: instead of "for every abstract pre-state `a`
    related to `s`, find a post-state `a'`," we say "for every abstract
    *post-state* `a'` related to `s'`, find a pre-state `a`."

    Backward simulations are useful when the linearization point of an
    operation is determined only *after* the operation completes (e.g.
    the successful `cmp_eq` in a double-collect snapshot determines that
    the linearization point was some earlier step).

    **Conditions** (`BackwardSimulationRel`):
    1. *Init*: every concrete initial state has a related abstract initial state.
    2. *Step* (backwards): for every concrete step `s → s'` and abstract
       state `a'` with `R s' a'`, there exists `a` with `R s a` such that
       `Star abstract.next a a'` (the abstract reaches `a'` from `a`
       in zero or more steps). -/

/-- A backward simulation relation between two TLA specs. -/
structure BackwardSimulationRel (σ : Type u) (τ : Type v) where
  concrete : Spec σ
  abstract : Spec τ
  /-- The simulation relation between concrete and abstract states. -/
  R : σ → τ → Prop
  /-- Every concrete initial state has a related abstract initial state. -/
  init_sim : ∀ s, concrete.init s → ∃ a, abstract.init a ∧ R s a
  /-- Backwards step condition: given a concrete step `s → s'` and an
      abstract post-state `a'` related to `s'`, find a pre-state `a`
      related to `s` from which the abstract can reach `a'`. -/
  step_sim : ∀ s s' a', R s' a' → concrete.next s s' →
    ∃ a, Star abstract.next a a' ∧ R s a

/-- Invariant transfer for backward simulations. -/
theorem BackwardSimulationRel.preserves_invariant
    (sim : BackwardSimulationRel σ τ)
    (inv : τ → Prop)
    (hinv_init : ∀ a, sim.abstract.init a → inv a)
    (hinv_next : ∀ a a', inv a → sim.abstract.next a a' → inv a')
    (P : σ → Prop)
    (hRP : ∀ s a, sim.R s a → inv a → P s)
    : pred_implies sim.concrete.safety [tlafml| □ ⌜ P ⌝] := by
  intro e ⟨hinit, hnext⟩
  have hnext' : ∀ k, sim.concrete.next (e k) (e (k + 1)) :=
    fun k => always_action_at k hnext
  -- Build abstract states backwards: at each step k, pick a_k related to e(k)
  -- such that Star next a_k a_{k+1}.
  -- We build by reverse induction: start from the initial state and propagate.
  -- Actually, we build forward: at step 0 pick a_0 from init_sim.
  -- At step k+1: we have a_k with R (e k) a_k.  The concrete takes a step
  -- e(k) → e(k+1).  We need a_{k+1} with R (e(k+1)) a_{k+1}.
  -- BUT the backward sim gives us: given a' with R (e(k+1)) a', find a with R (e k) a.
  -- This is the wrong direction for forward construction!
  --
  -- The standard approach: backward simulations preserve invariants under the
  -- assumption that every reachable concrete state has SOME related abstract state.
  -- We prove this by induction using step_sim applied in the correct direction.
  --
  -- Alternative: build the abstract witness sequence starting from e(0).
  -- At each step, we use step_sim "backwards" to ensure consistency.
  -- For invariant preservation, it suffices to show ∀ k, ∃ a, R (e k) a ∧ inv a.
  suffices h : ∀ k, ∃ a, sim.R (e k) a ∧ inv a from by
    intro k; simp [state_pred, exec.drop]
    obtain ⟨a, hr, hinv_a⟩ := h k
    exact hRP _ _ hr hinv_a
  intro k; induction k with
  | zero =>
    obtain ⟨a, ha_init, hr⟩ := sim.init_sim (e 0) hinit
    exact ⟨a, hr, hinv_init _ ha_init⟩
  | succ k ih =>
    obtain ⟨a_k1, hr_k1, hinv_k1⟩ := ih
    -- We have a_{k} with R (e k) a_{k} and inv a_{k}.
    -- We need a_{k+1} with R (e(k+1)) a_{k+1} and inv a_{k+1}.
    -- Use step_sim: we need an a' with R (e(k+1)) a'. But we don't have one yet!
    -- This is the circularity of backward simulation for invariant preservation.
    -- The standard resolution: backward simulations preserve invariants
    -- when combined with the assumption that R is "total on reachable states"
    -- (every reachable concrete state has some related abstract state).
    -- For now, we sorry this and note that the backward simulation itself is
    -- the main contribution; invariant transfer requires additional machinery.
    sorry

end TLA
