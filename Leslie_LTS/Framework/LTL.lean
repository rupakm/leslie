import Leslie_LTS.Framework.Trace

/-! # LTL with Past-Time Operators

    Defines trace properties evaluated at a position within an execution,
    with both future-time operators (□, ◇, 𝑈, ◯) and past-time operators
    (■, ◆, 𝑆, ●). This allows expressing properties that reference both
    future and past, such as "whenever set_up is set, input occurred earlier."

    Formulas are evaluated as `P e k` where `e` is the execution and `k`
    is the current position. Future operators quantify over `j ≥ k`,
    past operators over `j ≤ k`.
-/

namespace LTS

variable {State : Type u} {Label : Type v}

/-! ## Trace Properties -/

/-- A trace property: a predicate on an execution at a given position.
    `P e k` means "P holds on execution `e` at position `k`." -/
def TraceProp (State : Type u) (Label : Type v) :=
  Execution State Label → Nat → Prop

/-! ## Atomic Propositions -/

/-- Lift a state predicate to a trace property (looks at the current state). -/
def state_prop {State : Type u} {Label : Type v}
    (p : State → Prop) : TraceProp State Label :=
  fun e k => p (e.states k)

/-- Lift a label predicate to a trace property (looks at the current label). -/
def label_prop {State : Type u} {Label : Type v}
    (p : Label → Prop) : TraceProp State Label :=
  fun e k => p (e.labels k)

/-- Lift a step predicate (state, label, next-state) to a trace property. -/
def step_prop {State : Type u} {Label : Type v}
    (p : State → Label → State → Prop) : TraceProp State Label :=
  fun e k => p (e.states k) (e.labels k) (e.states (k + 1))

/-- A pure proposition lifted to a trace property (independent of execution
    and position). -/
def pure_prop {State : Type u} {Label : Type v}
    (p : Prop) : TraceProp State Label :=
  fun _ _ => p

/-! ## Boolean Combinators -/

def tp_true  {State : Type u} {Label : Type v} : TraceProp State Label := fun _ _ => True
def tp_false {State : Type u} {Label : Type v} : TraceProp State Label := fun _ _ => False

def tp_and {State : Type u} {Label : Type v}
    (p q : TraceProp State Label) : TraceProp State Label :=
  fun e k => p e k ∧ q e k

def tp_or {State : Type u} {Label : Type v}
    (p q : TraceProp State Label) : TraceProp State Label :=
  fun e k => p e k ∨ q e k

def tp_not {State : Type u} {Label : Type v}
    (p : TraceProp State Label) : TraceProp State Label :=
  fun e k => ¬ p e k

def tp_implies {State : Type u} {Label : Type v}
    (p q : TraceProp State Label) : TraceProp State Label :=
  fun e k => p e k → q e k

def tp_forall {α : Sort w} {State : Type u} {Label : Type v}
    (p : α → TraceProp State Label) : TraceProp State Label :=
  fun e k => ∀ x, p x e k

def tp_exists {α : Sort w} {State : Type u} {Label : Type v}
    (p : α → TraceProp State Label) : TraceProp State Label :=
  fun e k => ∃ x, p x e k

/-! ## Future-Time Temporal Operators -/

/-- Always (□): `p` holds at all future positions (including the current one). -/
def always {State : Type u} {Label : Type v}
    (p : TraceProp State Label) : TraceProp State Label :=
  fun e k => ∀ j, p e (k + j)

/-- Eventually (◇): `p` holds at some future position (including the current one). -/
def eventually {State : Type u} {Label : Type v}
    (p : TraceProp State Label) : TraceProp State Label :=
  fun e k => ∃ j, p e (k + j)

/-- Next (◯): `p` holds at the next position. -/
def next {State : Type u} {Label : Type v}
    (p : TraceProp State Label) : TraceProp State Label :=
  fun e k => p e (k + 1)

/-- Until (𝑈): `q` eventually holds, and `p` holds at all positions before it. -/
def ltl_until {State : Type u} {Label : Type v}
    (p q : TraceProp State Label) : TraceProp State Label :=
  fun e k => ∃ i, q e (k + i) ∧ ∀ j, j < i → p e (k + j)

/-- Weak until (𝑊): `p` holds until `q`, or `p` holds forever. -/
def wuntil {State : Type u} {Label : Type v}
    (p q : TraceProp State Label) : TraceProp State Label :=
  fun e k => ltl_until p q e k ∨ always p e k

/-- Release (𝑅): dual of until. -/
def release {State : Type u} {Label : Type v}
    (p q : TraceProp State Label) : TraceProp State Label :=
  fun e k => (∀ j, q e (k + j)) ∨
             ∃ j, p e (k + j) ∧ ∀ i, i ≤ j → q e (k + i)

/-! ## Past-Time Temporal Operators -/

/-- Historically (■): `p` held at all past positions (including the current one). -/
def historically {State : Type u} {Label : Type v}
    (p : TraceProp State Label) : TraceProp State Label :=
  fun e k => ∀ j, j ≤ k → p e j

/-- Once (◆): `p` held at some past position (including the current one). -/
def once {State : Type u} {Label : Type v}
    (p : TraceProp State Label) : TraceProp State Label :=
  fun e k => ∃ j, j ≤ k ∧ p e j

/-- Previous (●): `p` held at the previous position.
    False at position 0 (no previous position). -/
def prev {State : Type u} {Label : Type v}
    (p : TraceProp State Label) : TraceProp State Label :=
  fun e k => ∃ _ : k > 0, p e (k - 1)

/-- Since (𝑆): `q` held at some past position, and `p` held at all
    positions between then and now. -/
def ltl_since {State : Type u} {Label : Type v}
    (p q : TraceProp State Label) : TraceProp State Label :=
  fun e k => ∃ j, j ≤ k ∧ q e j ∧ ∀ i, j < i → i ≤ k → p e i

/-! ## Derived Temporal Operators -/

/-- Leads-to (↝): whenever `p` holds, `q` eventually follows. -/
def leads_to {State : Type u} {Label : Type v}
    (p q : TraceProp State Label) : TraceProp State Label :=
  always (tp_implies p (eventually q))

/-! ## Satisfaction and Validity -/

/-- An execution satisfies a trace property (evaluated at position 0). -/
def Execution.satisfies (e : Execution State Label)
    (φ : TraceProp State Label) : Prop :=
  φ e 0

/-- A system satisfies a trace property if all its valid executions do. -/
def System.satisfies (sys : System State Label)
    (φ : TraceProp State Label) : Prop :=
  ∀ e, sys.valid_exec e → φ e 0

/-- A trace property is valid if it holds on all executions at all positions. -/
def tp_valid {State : Type u} {Label : Type v}
    (p : TraceProp State Label) : Prop :=
  ∀ e k, p e k

/-- Trace property entailment: `p` entails `q` if at every position,
    `p` implies `q`. -/
def tp_entails {State : Type u} {Label : Type v}
    (p q : TraceProp State Label) : Prop :=
  ∀ e k, p e k → q e k

@[refl] theorem tp_entails_refl (p : TraceProp State Label) :
    tp_entails p p := fun _ _ h => h

theorem tp_entails_trans {p q r : TraceProp State Label} :
    tp_entails p q → tp_entails q r → tp_entails p r :=
  fun hpq hqr e k hp => hqr e k (hpq e k hp)

/-! ## Syntax -/

declare_syntax_cat ltlfml
syntax (priority := low) term:max : ltlfml
syntax "(" ltlfml ")" : ltlfml

-- Atomic propositions
syntax "⌜ " term " ⌝" : ltlfml
syntax "⌞ " term " ⌟" : ltlfml
syntax "act⟨ " term " ⟩" : ltlfml
syntax "lbl⟨ " term " ⟩" : ltlfml

-- Constants
syntax "⊤" : ltlfml
syntax "⊥" : ltlfml

-- Unary future temporal
syntax:max "□" ltlfml:40 : ltlfml
syntax:max "◇" ltlfml:40 : ltlfml
syntax:max "◯" ltlfml:40 : ltlfml

-- Unary past temporal
syntax:max "■" ltlfml:40 : ltlfml
syntax:max "◆" ltlfml:40 : ltlfml
syntax:max "●" ltlfml:40 : ltlfml

-- Negation
syntax:max "¬" ltlfml:40 : ltlfml

-- Binary
syntax:35 ltlfml:36 " ∧ " ltlfml:35 : ltlfml
syntax:30 ltlfml:31 " ∨ " ltlfml:30 : ltlfml
syntax:15 ltlfml:16 " → " ltlfml:15 : ltlfml
syntax:25 ltlfml:26 " 𝑈 " ltlfml:25 : ltlfml
syntax:25 ltlfml:26 " 𝑊 " ltlfml:25 : ltlfml
syntax:25 ltlfml:26 " 𝑅 " ltlfml:25 : ltlfml
syntax:25 ltlfml:26 " 𝑆 " ltlfml:25 : ltlfml
syntax:20 ltlfml:21 " ↝ " ltlfml:20 : ltlfml

-- Quantifiers
syntax "∀ " ident ", " ltlfml:51 : ltlfml
syntax "∀ " ident " : " term ", " ltlfml:51 : ltlfml
syntax "∃ " ident ", " ltlfml:51 : ltlfml
syntax "∃ " ident " : " term ", " ltlfml:51 : ltlfml

-- Wrapper
syntax "[ltl|" ltlfml "]" : term

macro_rules
  | `([ltl| ( $f:ltlfml ) ]) => `([ltl| $f ])
  | `([ltl| ⌜ $t:term ⌝ ]) => `(LTS.state_prop $t)
  | `([ltl| ⌞ $t:term ⌟ ]) => `(LTS.pure_prop $t)
  | `([ltl| act⟨ $t:term ⟩ ]) => `(LTS.step_prop $t)
  | `([ltl| lbl⟨ $t:term ⟩ ]) => `(LTS.label_prop $t)
  | `([ltl| ⊤ ]) => `(LTS.tp_true)
  | `([ltl| ⊥ ]) => `(LTS.tp_false)
  -- Future temporal
  | `([ltl| □ $f:ltlfml ]) => `(LTS.always [ltl| $f ])
  | `([ltl| ◇ $f:ltlfml ]) => `(LTS.eventually [ltl| $f ])
  | `([ltl| ◯ $f:ltlfml ]) => `(LTS.next [ltl| $f ])
  -- Past temporal
  | `([ltl| ■ $f:ltlfml ]) => `(LTS.historically [ltl| $f ])
  | `([ltl| ◆ $f:ltlfml ]) => `(LTS.once [ltl| $f ])
  | `([ltl| ● $f:ltlfml ]) => `(LTS.prev [ltl| $f ])
  -- Negation
  | `([ltl| ¬ $f:ltlfml ]) => `(LTS.tp_not [ltl| $f ])
  -- Binary
  | `([ltl| $f1:ltlfml ∧ $f2:ltlfml ]) => `(LTS.tp_and [ltl| $f1 ] [ltl| $f2 ])
  | `([ltl| $f1:ltlfml ∨ $f2:ltlfml ]) => `(LTS.tp_or [ltl| $f1 ] [ltl| $f2 ])
  | `([ltl| $f1:ltlfml → $f2:ltlfml ]) => `(LTS.tp_implies [ltl| $f1 ] [ltl| $f2 ])
  | `([ltl| $f1:ltlfml 𝑈 $f2:ltlfml ]) => `(LTS.ltl_until [ltl| $f1 ] [ltl| $f2 ])
  | `([ltl| $f1:ltlfml 𝑊 $f2:ltlfml ]) => `(LTS.wuntil [ltl| $f1 ] [ltl| $f2 ])
  | `([ltl| $f1:ltlfml 𝑅 $f2:ltlfml ]) => `(LTS.release [ltl| $f1 ] [ltl| $f2 ])
  | `([ltl| $f1:ltlfml 𝑆 $f2:ltlfml ]) => `(LTS.ltl_since [ltl| $f1 ] [ltl| $f2 ])
  | `([ltl| $f1:ltlfml ↝ $f2:ltlfml ]) => `(LTS.leads_to [ltl| $f1 ] [ltl| $f2 ])
  -- Quantifiers
  | `([ltl| ∀ $x:ident, $f:ltlfml]) => `(LTS.tp_forall fun $x => [ltl| $f ])
  | `([ltl| ∀ $x:ident : $t, $f:ltlfml]) => `(LTS.tp_forall fun $x : $t => [ltl| $f ])
  | `([ltl| ∃ $x:ident, $f:ltlfml]) => `(LTS.tp_exists fun $x => [ltl| $f ])
  | `([ltl| ∃ $x:ident : $t, $f:ltlfml]) => `(LTS.tp_exists fun $x : $t => [ltl| $f ])
  | `([ltl| $t:term ]) => `($t)

-- Entailment/satisfaction notations
syntax:max ltlfml:max " |-ltl- " ltlfml:max : term
syntax:max "|-ltl- " ltlfml:max : term
syntax:max term " |=ltl= " ltlfml:max : term

macro_rules
  | `($f1:ltlfml |-ltl- $f2:ltlfml) => `(LTS.tp_entails [ltl| $f1 ] [ltl| $f2 ])
  | `(|-ltl- $f1:ltlfml) => `(LTS.tp_valid [ltl| $f1 ])
  | `($e:term |=ltl= $f:ltlfml) => `(LTS.Execution.satisfies $e [ltl| $f ])

/-! ## External Trace Properties

    An **external trace property** is a predicate on label sequences that
    is meant to be applied to the external label subsequence. Properties
    expressed this way depend only on observable (external) behavior and
    can be transferred across forward simulations. -/

/-- An external trace property: a predicate on the external label
    subsequence. -/
def ExternalTraceProp (Label : Type v) := (Nat → Label) → Prop

/-- Lift an external trace property to a full trace property by
    extracting the external label subsequence from an execution.
    The lifted property is position-independent (same at all positions). -/
def ExternalTraceProp.lift {State : Type u} {Label : Type v}
    (lab : Labelling Label)
    (φ : ExternalTraceProp Label) : TraceProp State Label :=
  fun e _k => φ (externalSubseq lab e.labels)

/-- Map an external trace property through a label function.
    `φ.map f` holds on a label sequence `g` iff `φ` holds on `f ∘ g`. -/
def ExternalTraceProp.map {L₁ : Type v₁} {L₂ : Type v₂}
    (f : L₁ → L₂) (φ : ExternalTraceProp L₂) : ExternalTraceProp L₁ :=
  fun labels => φ (f ∘ labels)

end LTS
