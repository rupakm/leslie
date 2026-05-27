/-! # Labelled Transition Systems — Core Definitions

    This module defines the core `LTS` structure and reachability.
    It is intentionally independent of the TLA modules.
-/

namespace LTS

/-- A Labelled Transition System: a set of initial states and a
    labelled transition relation `step s l s'` meaning "state `s`
    transitions to `s'` via label `l`." -/
structure System (State : Type u) (Label : Type v) where
  init : State → Prop
  step : State → Label → State → Prop

variable {State : Type u} {Label : Type v}

/-- A label `l` is enabled in state `s` if some successor exists. -/
def System.enabled (sys : System State Label) (l : Label) (s : State) : Prop :=
  ∃ s', sys.step s l s'

/-- Some label is enabled in state `s`. -/
def System.any_enabled (sys : System State Label) (s : State) : Prop :=
  ∃ l, sys.enabled l s

/-- Reachability: `s` is reachable if there is a finite labelled path
    from some initial state to `s`. -/
inductive Reachable (sys : System State Label) : State → Prop where
  | init : sys.init s → Reachable sys s
  | step : Reachable sys s → sys.step s l s' → Reachable sys s'

/-- Reflexive transitive closure of the step relation from a given state. -/
inductive Star (sys : System State Label) : State → State → Prop where
  | refl : Star sys s s
  | step : sys.step s l s' → Star sys s' s'' → Star sys s s''

/-- A single step is a `Star`-step. -/
theorem Star.single {sys : System State Label} (h : sys.step s l s') :
    Star sys s s' :=
  .step h .refl

/-- `Star` is transitive: concatenation of two multi-step paths. -/
theorem Star.trans {sys : System State Label}
    (h1 : Star sys a b) (h2 : Star sys b c) : Star sys a c := by
  induction h1 with
  | refl => exact h2
  | step hs _ ih => exact .step hs (ih h2)

/-- An invariant preserved by each step is preserved by `Star`. -/
theorem Star.preserve_inv {sys : System State Label} {inv : State → Prop}
    (hinv : ∀ s l s', inv s → sys.step s l s' → inv s')
    (h : Star sys a b) (ha : inv a) : inv b := by
  induction h with
  | refl => exact ha
  | step hs _ ih => exact ih (hinv _ _ _ ha hs)

/-! ## Internal/External Labels -/

/-- A classification of labels into internal (silent/τ) and external (visible).
    Internal steps are unobservable; external steps must be matched
    by simulations. -/
structure Labelling (Label : Type v) where
  /-- Whether a label is internal (silent). -/
  is_internal : Label → Bool
  /-- The silent action τ, always internal. -/
  tau : Label
  /-- τ is internal. -/
  tau_internal : is_internal tau = true

/-- A label is external (visible) if it is not internal. -/
def Labelling.is_external {Label : Type v} (lab : Labelling Label) (l : Label) : Bool :=
  !lab.is_internal l

/-- Reflexive transitive closure restricted to internal steps only. -/
inductive InternalStar {State : Type u} {Label : Type v}
    (sys : System State Label) (lab : Labelling Label) : State → State → Type (max u v) where
  /-- Zero internal steps. -/
  | refl : InternalStar sys lab s s
  /-- One internal step followed by more internal steps. -/
  | step : lab.is_internal l = true → sys.step s l s' →
      InternalStar sys lab s' s'' → InternalStar sys lab s s''

/-- A single internal step is an `InternalStar`-step. -/
def InternalStar.single {sys : System State Label} {lab : Labelling Label}
    (hint : lab.is_internal l = true) (h : sys.step s l s') :
    InternalStar sys lab s s' :=
  .step hint h .refl

/-- `InternalStar` is transitive. -/
def InternalStar.trans {sys : System State Label} {lab : Labelling Label}
    (h1 : InternalStar sys lab a b) (h2 : InternalStar sys lab b c) :
    InternalStar sys lab a c :=
  match h1 with
  | .refl => h2
  | .step hint hs rest => .step hint hs (rest.trans h2)

/-- An invariant preserved by each step is preserved by `InternalStar`. -/
theorem InternalStar.preserve_inv {sys : System State Label} {lab : Labelling Label}
    {inv : State → Prop}
    (hinv : ∀ s l s', inv s → sys.step s l s' → inv s')
    (h : InternalStar sys lab a b) (ha : inv a) : inv b := by
  induction h with
  | refl => exact ha
  | step _ hs _ ih => exact ih (hinv _ _ _ ha hs)

/-- `InternalStar` implies `Star` (forget the internal label condition). -/
theorem InternalStar.toStar {sys : System State Label} {lab : Labelling Label}
    (h : InternalStar sys lab a b) : Star sys a b := by
  induction h with
  | refl => exact .refl
  | step _ hs _ ih => exact .step hs ih

/-- Number of internal steps in this path. -/
def InternalStar.length {sys : System State Label} {lab : Labelling Label} :
    {a b : State} → InternalStar sys lab a b → Nat
  | _, _, .refl       => 0
  | _, _, .step _ _ rest => 1 + rest.length

/-- The path is empty (length zero) — i.e. the abstract took no real step.
    Note: this is NOT the same as `a = b`, because an internal cycle yields a
    non-empty path with equal endpoints. -/
def InternalStar.IsEmpty {sys : System State Label} {lab : Labelling Label} :
    {a b : State} → InternalStar sys lab a b → Prop
  | _, _, .refl       => True
  | _, _, .step _ _ _ => False

/-- `Reachable` is preserved by `Star` steps. -/
theorem Star.reachable {sys : System State Label}
    (h : Star sys a b) (ha : Reachable sys a) : Reachable sys b := by
  induction h with
  | refl => exact ha
  | step hs _ ih => exact ih (.step ha hs)

end LTS
