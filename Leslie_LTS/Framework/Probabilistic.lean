import Leslie_LTS.Framework.Basic
import Leslie_LTS.Framework.Trace
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-! # Probabilistic Labelled Transition Systems (PLTS)

    A PLTS extends an LTS by replacing deterministic successor states with
    probability distributions over successor states. The transition relation
    becomes `step s l μ` meaning "state `s` transitions via label `l` to
    the distribution `μ : PMF State`."

    ## Connections to LTS

    There are two natural mappings between LTS and PLTS:

    1. **LTS → PLTS** (`fromLTS`): Each deterministic transition `s --l--> s'`
       becomes a transition to the Dirac distribution `s --l--> PMF.pure s'`.

    2. **PLTS → LTS** (`toLTS`): Each probabilistic transition `s --l--> μ`
       is unfolded into the set of transitions `s --l--> s'` for every
       `s'` in the support of `μ`.

    These form a Galois-like connection: `toLTS (fromLTS sys)` recovers
    exactly the original LTS step relation, and `fromLTS (toLTS psys)`
    refines the original PLTS (every Dirac step corresponds to a supported
    successor).
-/

namespace PLTS

/-- A Probabilistic Labelled Transition System: a set of initial states and a
    labelled transition relation `step s l μ` meaning "state `s`
    transitions via label `l` to the distribution `μ` over successor states." -/
structure System (State : Type u) (Label : Type v) where
  init : State → Prop
  step : State → Label → PMF State → Prop

variable {State : Type u} {Label : Type v}

/-- A label `l` is enabled in state `s` if some distribution successor exists. -/
def System.enabled (sys : System State Label) (l : Label) (s : State) : Prop :=
  ∃ μ, sys.step s l μ

/-- Some label is enabled in state `s`. -/
def System.any_enabled (sys : System State Label) (s : State) : Prop :=
  ∃ l, sys.enabled l s

/-! ## Mapping from LTS to PLTS -/

/-- Embed a (non-probabilistic) LTS into a PLTS by mapping each deterministic
    transition `s --l--> s'` to a transition `s --l--> PMF.pure s'`
    (Dirac distribution concentrated at `s'`). -/
def fromLTS (sys : LTS.System State Label) : System State Label where
  init := sys.init
  step := fun s l μ => ∃ s', sys.step s l s' ∧ μ = PMF.pure s'

/-! ## Mapping from PLTS to LTS -/

/-- Unfold a PLTS into a (non-probabilistic) LTS by replacing each
    probabilistic transition `s --l--> μ` with the set of transitions
    `{s --l--> s' | s' ∈ μ.support}`. -/
def toLTS (sys : System State Label) : LTS.System State Label where
  init := sys.init
  step := fun s l s' => ∃ μ, sys.step s l μ ∧ s' ∈ μ.support

/-! ## Roundtrip Properties -/

/-- `toLTS ∘ fromLTS` recovers the original LTS step relation exactly:
    `(toLTS (fromLTS sys)).step s l s'` iff `sys.step s l s'`. -/
theorem toLTS_fromLTS_step (sys : LTS.System State Label)
    (s : State) (l : Label) (s' : State) :
    (toLTS (fromLTS sys)).step s l s' ↔ sys.step s l s' := by
  constructor
  · rintro ⟨μ, ⟨s'', hstep, rfl⟩, hmem⟩
    rw [PMF.mem_support_pure_iff] at hmem
    rw [hmem]; exact hstep
  · intro hstep
    exact ⟨PMF.pure s', ⟨s', hstep, rfl⟩, by rw [PMF.mem_support_pure_iff]⟩

/-- `toLTS ∘ fromLTS` preserves init. -/
theorem toLTS_fromLTS_init (sys : LTS.System State Label)
    (s : State) :
    (toLTS (fromLTS sys)).init s ↔ sys.init s :=
  Iff.rfl

/-- The LTS obtained from `toLTS (fromLTS sys)` has the same init and step
    as the original `sys`. -/
theorem toLTS_fromLTS_init_eq (sys : LTS.System State Label) :
    (toLTS (fromLTS sys)).init = sys.init :=
  rfl

theorem toLTS_fromLTS_step_eq (sys : LTS.System State Label) :
    (toLTS (fromLTS sys)).step = sys.step := by
  funext s l s'
  exact propext (toLTS_fromLTS_step sys s l s')

/-- `toLTS ∘ fromLTS` recovers the original LTS exactly. -/
theorem toLTS_fromLTS_eq (sys : LTS.System State Label) :
    toLTS (fromLTS sys) = sys := by
  have h1 : (toLTS (fromLTS sys)).init = sys.init := rfl
  have h2 : (toLTS (fromLTS sys)).step = sys.step := toLTS_fromLTS_step_eq sys
  rcases sys with ⟨i, s⟩; exact LTS.System.mk.injEq .. |>.mpr ⟨h1, h2⟩

/-- Execution validity is preserved by the `toLTS ∘ fromLTS` roundtrip. -/
theorem toLTS_fromLTS_valid_exec (sys : LTS.System State Label)
    (e : LTS.Execution State Label) :
    (toLTS (fromLTS sys)).valid_exec e ↔ sys.valid_exec e := by
  simp only [LTS.System.valid_exec]
  constructor
  · rintro ⟨hi, hs⟩
    exact ⟨hi, fun k => (toLTS_fromLTS_step sys _ _ _).mp (hs k)⟩
  · rintro ⟨hi, hs⟩
    exact ⟨hi, fun k => (toLTS_fromLTS_step sys _ _ _).mpr (hs k)⟩

/-- In the other direction: every step of `fromLTS (toLTS psys)` corresponds
    to a Dirac distribution at some supported successor of the original PLTS. -/
theorem fromLTS_toLTS_step (psys : System State Label)
    (s : State) (l : Label) (μ : PMF State) :
    (fromLTS (toLTS psys)).step s l μ ↔
      ∃ s', (∃ ν, psys.step s l ν ∧ s' ∈ ν.support) ∧ μ = PMF.pure s' := by
  simp [fromLTS, toLTS]

/-! ## Reachability -/

/-- A state is reachable in a PLTS if it is reachable in the underlying LTS
    obtained by unfolding distributions to their supports. -/
def Reachable (sys : System State Label) (s : State) : Prop :=
  LTS.Reachable (toLTS sys) s

/-- Initial states are reachable. -/
theorem Reachable.init {sys : System State Label} (h : sys.init s) :
    Reachable sys s :=
  LTS.Reachable.init h

/-- If `s` is reachable and `s --l--> μ` with `s' ∈ μ.support`,
    then `s'` is reachable. -/
theorem Reachable.step {sys : System State Label}
    (hr : Reachable sys s) {μ : PMF State}
    (hstep : sys.step s l μ) (hmem : s' ∈ μ.support) :
    Reachable sys s' :=
  LTS.Reachable.step hr ⟨μ, hstep, hmem⟩

/-! ## Enabled and Support -/

/-- The enabled labels in a PLTS are preserved by `toLTS`. -/
theorem toLTS_enabled (sys : System State Label) (l : Label) (s : State) :
    (toLTS sys).enabled l s ↔ sys.enabled l s := by
  constructor
  · rintro ⟨s', μ, hstep, _⟩
    exact ⟨μ, hstep⟩
  · rintro ⟨μ, hstep⟩
    obtain ⟨s', hs'⟩ := μ.support_nonempty
    exact ⟨s', μ, hstep, hs'⟩

/-- The enabled labels in an LTS are preserved by `fromLTS`. -/
theorem fromLTS_enabled (sys : LTS.System State Label) (l : Label) (s : State) :
    (fromLTS sys).enabled l s ↔ sys.enabled l s := by
  constructor
  · rintro ⟨μ, s', hstep, _⟩
    exact ⟨s', hstep⟩
  · rintro ⟨s', hstep⟩
    exact ⟨PMF.pure s', s', hstep, rfl⟩

/-! ## Invariant Transfer

    Safety properties (invariants) transfer between PLTS and its underlying LTS
    since reachability in the PLTS is defined via the underlying LTS. -/

/-- An inductive invariant of a PLTS: if `P` holds on all initial states and
    is preserved by every transition (for all states in the support of the
    successor distribution), then `P` holds on all reachable states. -/
theorem toLTS_invariant (sys : System State Label) (P : State → Prop)
    (hinit : ∀ s, sys.init s → P s)
    (hstep : ∀ s l μ, P s → sys.step s l μ → ∀ s' ∈ μ.support, P s') :
    ∀ s, Reachable sys s → P s := by
  intro s hr
  induction hr with
  | init hinit' => exact hinit _ hinit'
  | step _ hstep' ih =>
    obtain ⟨μ, hstep_p, hmem⟩ := hstep'
    exact hstep _ _ μ ih hstep_p _ hmem

/-! ## Lifting Properties -/

/-- An LTS invariant that holds on `toLTS sys` can be stated directly
    on the PLTS. -/
theorem invariant_iff_toLTS (sys : System State Label) (P : State → Prop) :
    (∀ s, Reachable sys s → P s) ↔
    (∀ s, LTS.Reachable (toLTS sys) s → P s) :=
  Iff.rfl

/-- Reachability in a PLTS obtained from `fromLTS` coincides with
    reachability in the original LTS. -/
theorem reachable_fromLTS (sys : LTS.System State Label) (s : State) :
    Reachable (fromLTS sys) s ↔ LTS.Reachable sys s := by
  constructor
  · intro hr
    induction hr with
    | init h => exact LTS.Reachable.init h
    | step _ hstep ih =>
      obtain ⟨μ, ⟨s'', hstep', rfl⟩, hmem⟩ := hstep
      rw [PMF.mem_support_pure_iff] at hmem
      rw [hmem]; exact LTS.Reachable.step ih hstep'
  · intro hr
    induction hr with
    | init h => exact Reachable.init h
    | @step s l s' _ hstep ih =>
      exact Reachable.step ih ⟨s', hstep, rfl⟩ (by rw [PMF.mem_support_pure_iff])

end PLTS
