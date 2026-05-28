import Leslie_LTS.Framework.Rules
import Leslie_LTS.Framework.Simulation
import Mathlib.Order.RelClasses

/-! # Parallel Composition of Labelled Transition Systems

    CCS/CSP-style parallel composition with synchronization on shared labels.
-/

namespace LTS

/-! ## Composed Label Type -/

/-- Labels in a composed system: either one component moves alone,
    or both synchronize. -/
inductive CompLabel (L₁ : Type u) (L₂ : Type v) where
  /-- An independent action of the left component. -/
  | left  : L₁ → CompLabel L₁ L₂
  /-- An independent action of the right component. -/
  | right : L₂ → CompLabel L₁ L₂
  /-- A synchronized action of both components. -/
  | sync  : L₁ → L₂ → CompLabel L₁ L₂
deriving DecidableEq

/-! ## Parallel Composition -/

/-- Parallel composition of two LTS with a synchronization predicate.
    - `sync_on l₁ l₂` means labels `l₁` and `l₂` must happen simultaneously.
    - A `left l₁` step requires `l₁` to not synchronize with any `l₂`.
    - A `right l₂` step requires `l₂` to not synchronize with any `l₁`.
    - A `sync l₁ l₂` step requires `sync_on l₁ l₂`. -/
def parallel {S₁ : Type u₁} {L₁ : Type v₁} {S₂ : Type u₂} {L₂ : Type v₂}
    (sys₁ : System S₁ L₁) (sys₂ : System S₂ L₂)
    (sync_on : L₁ → L₂ → Prop) : System (S₁ × S₂) (CompLabel L₁ L₂) where
  init := fun ⟨s₁, s₂⟩ => sys₁.init s₁ ∧ sys₂.init s₂
  step := fun ⟨s₁, s₂⟩ cl ⟨s₁', s₂'⟩ =>
    match cl with
    | .left l₁ =>
        (∀ l₂, ¬ sync_on l₁ l₂) ∧
        sys₁.step s₁ l₁ s₁' ∧ s₂' = s₂
    | .right l₂ =>
        (∀ l₁, ¬ sync_on l₁ l₂) ∧
        sys₂.step s₂ l₂ s₂' ∧ s₁' = s₁
    | .sync l₁ l₂ =>
        sync_on l₁ l₂ ∧
        sys₁.step s₁ l₁ s₁' ∧ sys₂.step s₂ l₂ s₂'

/-- Interleaving composition: no synchronization (all labels independent). -/
def interleave {S₁ : Type u₁} {L₁ : Type v₁} {S₂ : Type u₂} {L₂ : Type v₂}
    (sys₁ : System S₁ L₁) (sys₂ : System S₂ L₂) :
    System (S₁ × S₂) (CompLabel L₁ L₂) :=
  parallel sys₁ sys₂ (fun _ _ => False)

/-- CSP-style composition: same label type, synchronize on equal labels. -/
def csp_parallel {S₁ : Type u₁} {S₂ : Type u₂} {L : Type v}
    (sys₁ : System S₁ L) (sys₂ : System S₂ L) :
    System (S₁ × S₂) (CompLabel L L) :=
  parallel sys₁ sys₂ (fun l₁ l₂ => l₁ = l₂)

/-! ## Projection Lemmas -/

/-- Left projection of a composed execution: extract the `sys₁` state component. -/
def Execution.proj_left {S₁ : Type u₁} {L₁ : Type v₁} {S₂ : Type u₂} {L₂ : Type v₂}
    (e : Execution (S₁ × S₂) (CompLabel L₁ L₂)) : Nat → S₁ :=
  fun n => (e.states n).1

/-- Right projection of a composed execution: extract the `sys₂` state component. -/
def Execution.proj_right {S₁ : Type u₁} {L₁ : Type v₁} {S₂ : Type u₂} {L₂ : Type v₂}
    (e : Execution (S₁ × S₂) (CompLabel L₁ L₂)) : Nat → S₂ :=
  fun n => (e.states n).2

/-! ## Invariant Lifting -/

/-- An invariant of `sys₁` lifts to the parallel composition (left projection):
    if `P` is an inductive invariant of `sys₁`, then `P ∘ Prod.fst` is an
    invariant of the composed system. -/
theorem parallel_lift_invariant_left
    {S₁ : Type u₁} {L₁ : Type v₁} {S₂ : Type u₂} {L₂ : Type v₂}
    {sys₁ : System S₁ L₁} {sys₂ : System S₂ L₂}
    {sync_on : L₁ → L₂ → Prop}
    (P : S₁ → Prop)
    (hinit : ∀ s, sys₁.init s → P s)
    (hstep : ∀ s l s', P s → sys₁.step s l s' → P s') :
    (parallel sys₁ sys₂ sync_on).satisfies
      [ltl| □ ⌜ fun p => P p.1 ⌝] := by
  apply System.invariant
  · intro e hv; exact hinit (e.states 0).1 hv.1.1
  · intro e k hv hP
    simp only [state_prop] at hP ⊢
    have hstep_c := hv.2 k
    cases hl : e.labels k with
    | left l₁ =>
      simp [parallel, hl] at hstep_c
      exact hstep _ l₁ _ hP hstep_c.2.1
    | right _ =>
      simp [parallel, hl] at hstep_c
      rw [hstep_c.2.2]; exact hP
    | sync l₁ _ =>
      simp [parallel, hl] at hstep_c
      exact hstep _ l₁ _ hP hstep_c.2.1

/-- An invariant of `sys₂` lifts to the parallel composition (right projection):
    if `P` is an inductive invariant of `sys₂`, then `P ∘ Prod.snd` is an
    invariant of the composed system. -/
theorem parallel_lift_invariant_right
    {S₁ : Type u₁} {L₁ : Type v₁} {S₂ : Type u₂} {L₂ : Type v₂}
    {sys₁ : System S₁ L₁} {sys₂ : System S₂ L₂}
    {sync_on : L₁ → L₂ → Prop}
    (P : S₂ → Prop)
    (hinit : ∀ s, sys₂.init s → P s)
    (hstep : ∀ s l s', P s → sys₂.step s l s' → P s') :
    (parallel sys₁ sys₂ sync_on).satisfies
      [ltl| □ ⌜ fun p => P p.2 ⌝] := by
  apply System.invariant
  · intro e hv; exact hinit (e.states 0).2 hv.1.2
  · intro e k hv hP
    simp only [state_prop] at hP ⊢
    have hstep_c := hv.2 k
    cases hl : e.labels k with
    | left _ =>
      simp [parallel, hl] at hstep_c
      rw [hstep_c.2.2]; exact hP
    | right l₂ =>
      simp [parallel, hl] at hstep_c
      exact hstep _ l₂ _ hP hstep_c.2.1
    | sync _ l₂ =>
      simp [parallel, hl] at hstep_c
      exact hstep _ l₂ _ hP hstep_c.2.2

/-! ## Label Hiding -/

/-- Hide labels by projecting to a visible subset.
    Internal labels (mapped to `none`) become invisible. -/
def hide {State : Type u} {Label : Type v} {Visible : Type w}
    (sys : System State Label)
    (project : Label → Option Visible) : System State (Option Visible) where
  init := sys.init
  step := fun s v s' => ∃ l, sys.step s l s' ∧ project l = v

/-- Restriction: only allow transitions whose labels satisfy a predicate. -/
def restrict {State : Type u} {Label : Type v}
    (sys : System State Label)
    (allowed : Label → Prop) : System State Label where
  init := sys.init
  step := fun s l s' => allowed l ∧ sys.step s l s'

/-! ## Indexed Parallel Composition -/

/-- Labels in an indexed parallel composition: either a single instance
    acts independently, or all instances act with the same label. -/
inductive ICompLabel (I : Type u) (L : Type v) where
  /-- An independent action of a single instance. -/
  | ind  (inst : I) (l : L)
  /-- A synchronized action: all instances step with the same label. -/
  | global (l : L)

/-- Indexed parallel composition of a family of systems.
    - `sync_on l` means label `l` must fire on ALL instances simultaneously.
    - An `ind inst l` step requires `¬ sync_on l` and only instance `inst` steps.
    - A `global l` step requires `sync_on l` and ALL instances step with `l`. -/
def iparallel {I : Type u₁} {S : Type u₂} {L : Type v} [DecidableEq I]
    (sys : I → System S L)
    (sync_on : L → Prop) : System (I → S) (ICompLabel I L) where
  init := fun sf => ∀ i, (sys i).init (sf i)
  step := fun sf cl sf' =>
    match cl with
    | .ind inst l =>
        ¬ sync_on l ∧
        (sys inst).step (sf inst) l (sf' inst) ∧
        ∀ j, j ≠ inst → sf' j = sf j
    | .global l =>
        sync_on l ∧
        ∀ i, (sys i).step (sf i) l (sf' i)

/-- Indexed interleaving: no synchronization (all labels are independent). -/
def iinterleave {I : Type u₁} {S : Type u₂} {L : Type v} [DecidableEq I]
    (sys : I → System S L) : System (I → S) (ICompLabel I L) :=
  iparallel sys (fun _ => False)

/-! ## Composed Labellings -/

/-- Canonical labelling for binary parallel composition.
    A composed label is internal iff all component labels are internal. -/
def parallel_labelling {LA : Type v₁} {LB : Type v₂}
    (labA : Labelling LA) (labB : Labelling LB) :
    Labelling (CompLabel LA LB) where
  is_internal := fun cl =>
    match cl with
    | .left la => labA.is_internal la
    | .right lb => labB.is_internal lb
    | .sync la lb => labA.is_internal la && labB.is_internal lb
  tau := .left labA.tau
  tau_internal := labA.tau_internal

/-- Canonical labelling for indexed parallel composition.
    A composed label is internal iff the underlying label is internal. -/
def iparallel_labelling {I : Type u₁} {L : Type v} [Inhabited I]
    (lab : Labelling L) :
    Labelling (ICompLabel I L) where
  is_internal := fun cl =>
    match cl with
    | .ind _ l => lab.is_internal l
    | .global l => lab.is_internal l
  tau := .ind default lab.tau
  tau_internal := lab.tau_internal

/-! ## Simulation Lifting for `parallel`

    If both components have forward simulations, and the sync predicates
    are compatible, the parallel composition has a forward simulation. -/

/-- Forward simulation lifts through binary parallel composition.

    Given per-component simulations `simA : sysA₁ ≲ sysA₂` and
    `simB : sysB₁ ≲ sysB₂`, produces a simulation
    `parallel sysA₁ sysB₁ ≲ parallel sysA₂ sysB₂`.

    The composed simulation relation is pointwise:
    `R (sa₁, sb₁) (sa₂, sb₂) := simA.R sa₁ sa₂ ∧ simB.R sb₁ sb₂`.

    The composed label map is structural:
    `.left la ↦ .left (mapA la)`, `.right lb ↦ .right (mapB lb)`,
    `.sync la lb ↦ .sync (mapA la) (mapB lb)`. -/
-- Helper: project reachability to the left component.
private theorem reachable_left
    {SA : Type _} {LA : Type _} {SB : Type _} {LB : Type _}
    {sysA : System SA LA} {sysB : System SB LB} {sync_on : LA → LB → Prop}
    (p : SA × SB) (h : Reachable (parallel sysA sysB sync_on) p) :
    Reachable sysA p.1 := by
  induction h with
  | init hinit => exact .init hinit.1
  | @step s l s' _ hstep ih =>
    obtain ⟨sa, sb⟩ := s; obtain ⟨sa', sb'⟩ := s'
    match l with
    | .left la => simp [parallel] at hstep; exact .step ih hstep.2.1
    | .right _ => simp [parallel] at hstep; rw [hstep.2.2]; exact ih
    | .sync la _ => simp [parallel] at hstep; exact .step ih hstep.2.1

-- Helper: project reachability to the right component.
private theorem reachable_right
    {SA : Type _} {LA : Type _} {SB : Type _} {LB : Type _}
    {sysA : System SA LA} {sysB : System SB LB} {sync_on : LA → LB → Prop}
    (p : SA × SB) (h : Reachable (parallel sysA sysB sync_on) p) :
    Reachable sysB p.2 := by
  induction h with
  | init hinit => exact .init hinit.2
  | @step s l s' _ hstep ih =>
    obtain ⟨sa, sb⟩ := s; obtain ⟨sa', sb'⟩ := s'
    match l with
    | .left _ => simp [parallel] at hstep; rw [hstep.2.2]; exact ih
    | .right lb => simp [parallel] at hstep; exact .step ih hstep.2.1
    | .sync _ lb => simp [parallel] at hstep; exact .step ih hstep.2.2

-- Helper: lift an A-side InternalStar to the composed system (B unchanged).
def lift_star_left
    {SA : Type _} {LA : Type _} {SB : Type _} {LB : Type _}
    {sysA : System SA LA} {sysB : System SB LB}
    {labA : Labelling LA} {labB : Labelling LB}
    {sync_on : LA → LB → Prop}
    (hsync_ext : ∀ la lb, sync_on la lb →
      labA.is_external la = true ∧ labB.is_external lb = true)
    {sa sa' : SA} (sb : SB)
    (hstar : InternalStar sysA labA sa sa') :
    InternalStar (parallel sysA sysB sync_on) (parallel_labelling labA labB)
      (sa, sb) (sa', sb) :=
  match hstar with
  | .refl => .refl
  | .step (l := la) hint hstep rest =>
    have hnosyn : ∀ lb, ¬sync_on la lb := fun lb hsyn => by
      have := (hsync_ext _ lb hsyn).1; simp [Labelling.is_external, hint] at this
    .step (show (parallel_labelling labA labB).is_internal (.left la) = true from hint)
      (show (parallel sysA sysB sync_on).step (sa, sb) (.left la) (_, sb) from
        ⟨hnosyn, hstep, rfl⟩) (lift_star_left hsync_ext sb rest)

-- Helper: lift a B-side InternalStar to the composed system (A unchanged).
def lift_star_right
    {SA : Type _} {LA : Type _} {SB : Type _} {LB : Type _}
    {sysA : System SA LA} {sysB : System SB LB}
    {labA : Labelling LA} {labB : Labelling LB}
    {sync_on : LA → LB → Prop}
    (hsync_ext : ∀ la lb, sync_on la lb →
      labA.is_external la = true ∧ labB.is_external lb = true)
    (sa : SA) {sb sb' : SB}
    (hstar : InternalStar sysB labB sb sb') :
    InternalStar (parallel sysA sysB sync_on) (parallel_labelling labA labB)
      (sa, sb) (sa, sb') :=
  match hstar with
  | .refl => .refl
  | .step (l := lb) hint hstep rest =>
    have hnosyn : ∀ la, ¬sync_on la lb := fun la hsyn => by
      have := (hsync_ext la _ hsyn).2; simp [Labelling.is_external, hint] at this
    .step (show (parallel_labelling labA labB).is_internal (.right lb) = true from hint)
      (show (parallel sysA sysB sync_on).step (sa, sb) (.right lb) (sa, _) from
        ⟨hnosyn, hstep, rfl⟩) (lift_star_right hsync_ext sa rest)

@[simp] theorem lift_star_left_isEmpty_iff
    {SA : Type uA} {LA : Type vA} {SB : Type uB} {LB : Type vB}
    {sysA : System SA LA} {sysB : System SB LB}
    {labA : Labelling LA} {labB : Labelling LB}
    {sync_on : LA → LB → Prop}
    (hsync_ext : ∀ la lb, sync_on la lb →
      labA.is_external la = true ∧ labB.is_external lb = true)
    {sa sa' : SA} (sb : SB)
    (hstar : InternalStar sysA labA sa sa') :
    (lift_star_left (sysB := sysB) hsync_ext sb hstar).IsEmpty ↔ hstar.IsEmpty := by
  cases hstar with
  | refl => simp [lift_star_left, InternalStar.IsEmpty]
  | step _ _ _ => simp [lift_star_left, InternalStar.IsEmpty]

@[simp] theorem lift_star_right_isEmpty_iff
    {SA : Type uA} {LA : Type vA} {SB : Type uB} {LB : Type vB}
    {sysA : System SA LA} {sysB : System SB LB}
    {labA : Labelling LA} {labB : Labelling LB}
    {sync_on : LA → LB → Prop}
    (hsync_ext : ∀ la lb, sync_on la lb →
      labA.is_external la = true ∧ labB.is_external lb = true)
    (sa : SA) {sb sb' : SB}
    (hstar : InternalStar sysB labB sb sb') :
    (lift_star_right (sysA := sysA) hsync_ext sa hstar).IsEmpty ↔ hstar.IsEmpty := by
  cases hstar with
  | refl => simp [lift_star_right, InternalStar.IsEmpty]
  | step _ _ _ => simp [lift_star_right, InternalStar.IsEmpty]

/-- The composed label map for `parallel_forward_sim`. Defined separately
    so it remains computable even when the simulations use classical choice. -/
def parallel_label_map
    {LA₁ : Type v₁} {LA₂ : Type v₂} {LB₁ : Type v₃} {LB₂ : Type v₄}
    (mapA : LA₁ → LA₂) (mapB : LB₁ → LB₂) :
    CompLabel LA₁ LB₁ → CompLabel LA₂ LB₂
  | .left la => .left (mapA la)
  | .right lb => .right (mapB lb)
  | .sync la lb => .sync (mapA la) (mapB lb)

def parallel_forward_sim
    {SA₁ : Type u₁} {LA₁ : Type v₁} {SA₂ : Type u₂} {LA₂ : Type v₂}
    {SB₁ : Type u₃} {LB₁ : Type v₃} {SB₂ : Type u₄} {LB₂ : Type v₄}
    {sysA₁ : System SA₁ LA₁} {sysA₂ : System SA₂ LA₂}
    {sysB₁ : System SB₁ LB₁} {sysB₂ : System SB₂ LB₂}
    {labA₁ : Labelling LA₁} {labA₂ : Labelling LA₂}
    {labB₁ : Labelling LB₁} {labB₂ : Labelling LB₂}
    {sync₁ : LA₁ → LB₁ → Prop} {sync₂ : LA₂ → LB₂ → Prop}
    (simA : ForwardSim sysA₁ labA₁ sysA₂ labA₂)
    (simB : ForwardSim sysB₁ labB₁ sysB₂ labB₂)
    (hsync : ∀ la lb, sync₁ la lb → sync₂ (simA.label_map la) (simB.label_map lb))
    (hnosync_left : ∀ la,
      (∀ lb, ¬sync₁ la lb) → ∀ lb₂, ¬sync₂ (simA.label_map la) lb₂)
    (hnosync_right : ∀ lb,
      (∀ la, ¬sync₁ la lb) → ∀ la₂, ¬sync₂ la₂ (simB.label_map lb))
    (hsync_ext : ∀ la lb, sync₂ la lb →
      labA₂.is_external la = true ∧ labB₂.is_external lb = true)
    (hmap_int_a : ∀ la, labA₁.is_internal la = true →
      labA₂.is_internal (simA.label_map la) = true)
    (hmap_int_b : ∀ lb, labB₁.is_internal lb = true →
      labB₂.is_internal (simB.label_map lb) = true) :
    ForwardSim
      (parallel sysA₁ sysB₁ sync₁) (parallel_labelling labA₁ labB₁)
      (parallel sysA₂ sysB₂ sync₂) (parallel_labelling labA₂ labB₂) where
  R := fun (sa₁, sb₁) (sa₂, sb₂) => simA.R sa₁ sa₂ ∧ simB.R sb₁ sb₂
  label_map := parallel_label_map simA.label_map simB.label_map
  init_sim := by
    intro ⟨sa₁, sb₁⟩ ⟨ha, hb⟩
    obtain ⟨sa₂, ha₂, hRa⟩ := simA.init_sim sa₁ ha
    obtain ⟨sb₂, hb₂, hRb⟩ := simB.init_sim sb₁ hb
    exact ⟨(sa₂, sb₂), ⟨ha₂, hb₂⟩, hRa, hRb⟩
  step_internal := by
    intro ⟨sa₁, sb₁⟩ cl ⟨sa₁', sb₁'⟩ ⟨sa₂, sb₂⟩ hreach ⟨hRa, hRb⟩ hint hstep
    match cl with
    | .left la =>
      simp [parallel_labelling] at hint
      obtain ⟨_, hstepA, rfl⟩ := hstep
      obtain ⟨sa₂', hstarA, hRa'⟩ := simA.step_internal sa₁ la sa₁' sa₂
        (reachable_left _ hreach) hRa hint hstepA
      exact ⟨(sa₂', sb₂), lift_star_left hsync_ext sb₂ hstarA, hRa', hRb⟩
    | .right lb =>
      simp [parallel_labelling] at hint
      obtain ⟨_, hstepB, rfl⟩ := hstep
      obtain ⟨sb₂', hstarB, hRb'⟩ := simB.step_internal sb₁ lb sb₁' sb₂
        (reachable_right _ hreach) hRb hint hstepB
      exact ⟨(sa₂, sb₂'), lift_star_right hsync_ext sa₂ hstarB, hRa, hRb'⟩
    | .sync la lb =>
      simp [parallel_labelling, Bool.and_eq_true] at hint
      obtain ⟨hintA, hintB⟩ := hint
      obtain ⟨hsyn, hstepA, hstepB⟩ := hstep
      obtain ⟨sa₂', hstarA, hRa'⟩ := simA.step_internal sa₁ la sa₁' sa₂
        (reachable_left _ hreach) hRa hintA hstepA
      obtain ⟨sb₂', hstarB, hRb'⟩ := simB.step_internal sb₁ lb sb₁' sb₂
        (reachable_right _ hreach) hRb hintB hstepB
      exact ⟨(sa₂', sb₂'),
        (lift_star_left hsync_ext sb₂ hstarA).trans
          (lift_star_right hsync_ext sa₂' hstarB),
        hRa', hRb'⟩
  step_external := by
    intro ⟨sa₁, sb₁⟩ cl ⟨sa₁', sb₁'⟩ ⟨sa₂, sb₂⟩ hreach ⟨hRa, hRb⟩ hext hstep
    match cl with
    | .left la =>
      simp [parallel_labelling, Labelling.is_external] at hext
      have hextA : labA₁.is_external la = true := by
        simp [Labelling.is_external, hext]
      obtain ⟨hnosyn, hstepA, rfl⟩ := hstep
      obtain ⟨sa₂m, sa₂m', sa₂', hpreA, hstepA₂, hpostA, hRa'⟩ :=
        simA.step_external sa₁ la sa₁' sa₂
          (reachable_left _ hreach) hRa hextA hstepA
      exact ⟨(sa₂m, sb₂), (sa₂m', sb₂), (sa₂', sb₂),
        lift_star_left hsync_ext sb₂ hpreA,
        ⟨hnosync_left la hnosyn, hstepA₂, rfl⟩,
        lift_star_left hsync_ext sb₂ hpostA,
        hRa', hRb⟩
    | .right lb =>
      simp [parallel_labelling, Labelling.is_external] at hext
      have hextB : labB₁.is_external lb = true := by
        simp [Labelling.is_external, hext]
      obtain ⟨hnosyn, hstepB, rfl⟩ := hstep
      obtain ⟨sb₂m, sb₂m', sb₂', hpreB, hstepB₂, hpostB, hRb'⟩ :=
        simB.step_external sb₁ lb sb₁' sb₂
          (reachable_right _ hreach) hRb hextB hstepB
      exact ⟨(sa₂, sb₂m), (sa₂, sb₂m'), (sa₂, sb₂'),
        lift_star_right hsync_ext sa₂ hpreB,
        ⟨hnosync_right lb hnosyn, hstepB₂, rfl⟩,
        lift_star_right hsync_ext sa₂ hpostB,
        hRa, hRb'⟩
    | .sync la lb =>
      obtain ⟨hsyn, hstepA, hstepB⟩ := hstep
      -- Both must be external (from hsync + hsync_ext + hmap_int)
      have hextA : labA₁.is_external la = true := by
        simp only [Labelling.is_external]
        match hint : labA₁.is_internal la with
        | false => rfl
        | true =>
          have := (hsync_ext _ _ (hsync la lb hsyn)).1
          simp [Labelling.is_external, hmap_int_a la hint] at this
      have hextB : labB₁.is_external lb = true := by
        simp only [Labelling.is_external]
        match hint : labB₁.is_internal lb with
        | false => rfl
        | true =>
          have := (hsync_ext _ _ (hsync la lb hsyn)).2
          simp [Labelling.is_external, hmap_int_b lb hint] at this
      obtain ⟨sa₂m, sa₂m', sa₂', hpreA, hstepA₂, hpostA, hRa'⟩ :=
        simA.step_external sa₁ la sa₁' sa₂
          (reachable_left _ hreach) hRa hextA hstepA
      obtain ⟨sb₂m, sb₂m', sb₂', hpreB, hstepB₂, hpostB, hRb'⟩ :=
        simB.step_external sb₁ lb sb₁' sb₂
          (reachable_right _ hreach) hRb hextB hstepB
      exact ⟨(sa₂m, sb₂m), (sa₂m', sb₂m'), (sa₂', sb₂'),
        (lift_star_left hsync_ext sb₂ hpreA).trans
          (lift_star_right hsync_ext sa₂m hpreB),
        ⟨hsync la lb hsyn, hstepA₂, hstepB₂⟩,
        (lift_star_left hsync_ext sb₂m' hpostA).trans
          (lift_star_right hsync_ext sa₂' hpostB),
        hRa', hRb'⟩

/-! ## Simulation Lifting for `iparallel`

    If every instance has a forward simulation (with the same label map),
    the indexed parallel composition has a forward simulation.
    Requires `Fintype I` to sequence per-instance `InternalStar`s
    in the `.global` case. -/

-- Helper: project reachability to a single instance.
private theorem iparallel_reachable
    {I : Type u₁} {S : Type u₂} {L : Type v} [DecidableEq I]
    {sys : I → System S L} {sync_on : L → Prop}
    (sf : I → S) (h : Reachable (iparallel sys sync_on) sf) (i : I) :
    Reachable (sys i) (sf i) := by
  induction h with
  | init hinit => exact .init (hinit i)
  | @step sf l sf' _ hstep ih =>
    match l with
    | .ind inst l =>
      obtain ⟨_, hstep_inst, hunchanged⟩ := hstep
      by_cases hi : i = inst
      · subst hi; exact .step ih hstep_inst
      · rw [hunchanged i hi]; exact ih
    | .global l =>
      exact .step ih (hstep.2 i)

-- Local update helper.
private def updateAt {I : Type u₁} {S : Type u₂} [DecidableEq I] (sf : I → S) (inst : I) (s : S) : I → S :=
  fun j => if j = inst then s else sf j

private theorem updateAt_self {I : Type u₁} {S : Type u₂} [DecidableEq I] (sf : I → S) (inst : I) (s : S) :
    updateAt sf inst s inst = s := by simp [updateAt]

private theorem updateAt_other {I : Type u₁} {S : Type u₂} [DecidableEq I] (sf : I → S) (inst : I) (s : S)
    (j : I) (hj : j ≠ inst) : updateAt sf inst s j = sf j := by
  simp [updateAt, hj]

-- Helper: lift a per-instance InternalStar to the composed system.
private def lift_istar
    {I : Type u₁} {S : Type u₂} {L : Type v} [DecidableEq I] [Inhabited I]
    {sys : I → System S L} {lab : Labelling L}
    {sync_on : L → Prop}
    (hsync_ext : ∀ l, sync_on l → lab.is_external l = true)
    (idx : I) (sf : I → S) {s s' : S}
    (hstar : InternalStar (sys idx) lab s s')
    (heq : sf idx = s) :
    Σ' sf', InternalStar (iparallel sys sync_on) (iparallel_labelling lab) sf sf' ×'
      (sf' idx = s' ∧ ∀ j, j ≠ idx → sf' j = sf j) :=
  match hstar with
  | .refl => ⟨sf, .refl, heq, fun _ _ => rfl⟩
  | .step (l := l) hint hstep rest =>
    let sf_mid := updateAt sf idx _
    have hstep_par : (iparallel sys sync_on).step sf (.ind idx l) sf_mid := by
      refine ⟨fun hsyn => ?_, ?_, fun j hj => updateAt_other sf idx _ j hj⟩
      · have := hsync_ext _ hsyn; simp [Labelling.is_external, hint] at this
      · have : sf_mid idx = _ := updateAt_self sf idx _
        rw [heq, this]; exact hstep
    have hint_par : (iparallel_labelling lab).is_internal (.ind idx l) = true := hint
    let ⟨sf', hstar', heq', hunch'⟩ := lift_istar hsync_ext idx sf_mid rest (updateAt_self sf idx _)
    ⟨sf', .step hint_par hstep_par hstar', heq',
      fun j hj => (hunch' j hj).trans (updateAt_other sf idx _ j hj)⟩

-- Helper: sequence per-instance InternalStars over a list of instances.
private def sequence_istars
    {I : Type u₁} {S : Type u₂} {L : Type v} [DecidableEq I] [Inhabited I]
    {sys : I → System S L} {lab : Labelling L}
    {sync_on : L → Prop}
    (hsync_ext : ∀ l, sync_on l → lab.is_external l = true)
    (instances : List I)
    (sf : I → S) (targets : I → S)
    (hstars : ∀ i, i ∈ instances →
      InternalStar (sys i) lab (sf i) (targets i))
    (hnodup : instances.Nodup) :
    Σ' sf', InternalStar (iparallel sys sync_on) (iparallel_labelling lab) sf sf' ×'
      ((∀ i, i ∈ instances → sf' i = targets i) ∧
      (∀ i, i ∉ instances → sf' i = sf i)) :=
  match instances, hstars, hnodup with
  | [], _, _ => ⟨sf, .refl, fun _ h => by simp at h, fun _ _ => rfl⟩
  | x :: rest, hstars, hnodup =>
    have hnodup_rest := (List.nodup_cons.mp hnodup).2
    have hnx := (List.nodup_cons.mp hnodup).1
    let ⟨sf_mid, hstar_x, heq_x, hunch_x⟩ :=
      lift_istar hsync_ext x sf (hstars x (List.mem_cons_self ..)) rfl
    have hstars_rest : ∀ i, i ∈ rest →
        InternalStar (sys i) lab (sf_mid i) (targets i) := by
      intro i hi
      rw [hunch_x i (fun h => hnx (h ▸ hi))]
      exact hstars i (List.mem_cons_of_mem _ hi)
    let ⟨sf', hstar_rest, heq_rest, hunch_rest⟩ :=
      sequence_istars hsync_ext rest sf_mid targets hstars_rest hnodup_rest
    ⟨sf', hstar_x.trans hstar_rest,
      fun i hi => by
        rcases List.mem_cons.mp hi with rfl | h
        · rw [hunch_rest i hnx, heq_x]
        · exact heq_rest i h,
      fun i hi => by
        have hi_rest : i ∉ rest := fun h => hi (List.mem_cons_of_mem _ h)
        have hi_x : i ≠ x := fun h => hi (h ▸ List.mem_cons_self ..)
        rw [hunch_rest i hi_rest, hunch_x i hi_x]⟩

/-- Forward simulation lifts through indexed parallel composition.

    Given per-instance simulations `∀ i, sys₁ i ≲ sys₂ i` with a
    common label map, produces `iparallel sys₁ ≲ iparallel sys₂`.

    The composed simulation relation is pointwise:
    `R sf₁ sf₂ := ∀ i, (sim i).R (sf₁ i) (sf₂ i)`.

    The composed label map is structural:
    `.ind inst l ↦ .ind inst (map l)`, `.global l ↦ .global (map l)`. -/
def iparallel_forward_sim
    {I : Type u₁} {S₁ : Type u₂} {L₁ : Type v₁}
    {S₂ : Type u₃} {L₂ : Type v₂}
    [DecidableEq I] [Inhabited I]
    {sys₁ : I → System S₁ L₁} {sys₂ : I → System S₂ L₂}
    {lab₁ : Labelling L₁} {lab₂ : Labelling L₂}
    {sync₁ : L₁ → Prop} {sync₂ : L₂ → Prop}
    (sim : ∀ i, ForwardSim (sys₁ i) lab₁ (sys₂ i) lab₂)
    (hmap_eq : ∀ i j, (sim i).label_map = (sim j).label_map)
    (hsync : ∀ l, sync₁ l → sync₂ ((sim default).label_map l))
    (hnosync : ∀ l, ¬sync₁ l → ¬sync₂ ((sim default).label_map l))
    (hsync_ext : ∀ l, sync₂ l → lab₂.is_external l = true)
    (hmap_int : ∀ l, lab₁.is_internal l = true →
      lab₂.is_internal ((sim default).label_map l) = true)
    -- Complete enumeration of I (replaces Fintype)
    (enum : List I) (henum : ∀ i, i ∈ enum) (hnodup : enum.Nodup) :
    ForwardSim
      (iparallel sys₁ sync₁) (iparallel_labelling lab₁)
      (iparallel sys₂ sync₂) (iparallel_labelling lab₂) where
  R := fun sf₁ sf₂ => ∀ i, (sim i).R (sf₁ i) (sf₂ i)
  label_map := fun cl =>
    match cl with
    | .ind inst l => .ind inst ((sim default).label_map l)
    | .global l => .global ((sim default).label_map l)
  init_sim := by
    intro sf₁ hinit
    -- For each i, get abstract initial state
    have := fun i => (sim i).init_sim (sf₁ i) (hinit i)
    exact ⟨fun i => (this i).1, fun i => (this i).2.1,
      fun i => (this i).2.2⟩
  step_internal := by
    intro sf₁ cl sf₁' sf₂ hreach hR hint hstep
    match cl with
    | .ind idx l =>
      simp [iparallel_labelling] at hint
      obtain ⟨hnosyn, hstep_inst, hunchanged⟩ := hstep
      -- Simulate instance idx internally
      let wsim := (sim idx).step_internal
        (sf₁ idx) l (sf₁' idx) (sf₂ idx)
        (iparallel_reachable sf₁ hreach idx) (hR idx) hint hstep_inst
      obtain ⟨sf₂', hstar_par, heq_idx, hunchanged'⟩ :=
        lift_istar hsync_ext idx sf₂ wsim.2.1 rfl
      exact ⟨sf₂', hstar_par, fun i => by
        by_cases hi : i = idx
        · subst hi; rw [heq_idx]; exact wsim.2.2
        · rw [hunchanged' i hi, hunchanged i hi]; exact hR i⟩
    | .global l =>
      simp [iparallel_labelling] at hint
      obtain ⟨hsyn, _⟩ := hstep
      have := hsync_ext _ (hsync l hsyn)
      simp [Labelling.is_external, hmap_int l hint] at this
  step_external := by
    intro sf₁ cl sf₁' sf₂ hreach hR hext hstep
    match cl with
    | .ind idx l =>
      simp [iparallel_labelling, Labelling.is_external] at hext
      have hextL : lab₁.is_external l = true := by simp [Labelling.is_external, hext]
      obtain ⟨hnosyn, hstep_idx, hunchanged⟩ := hstep
      have hlmap : (sim idx).label_map = (sim default).label_map := hmap_eq idx default
      let wsim := (sim idx).step_external (sf₁ idx) l (sf₁' idx) (sf₂ idx)
          (iparallel_reachable sf₁ hreach idx) (hR idx) hextL hstep_idx
      let s₂m := wsim.1; let s₂m' := wsim.2.1; let s₂' := wsim.2.2.1
      have hpre := wsim.2.2.2.1; have hstep₂ := wsim.2.2.2.2.1
      have hpost := wsim.2.2.2.2.2.1; have hR_idx := wsim.2.2.2.2.2.2
      obtain ⟨sf₂_pre, hstar_pre, heq_pre, hunch_pre⟩ :=
        lift_istar hsync_ext idx sf₂ hpre rfl
      have hmid_eq : updateAt sf₂_pre idx s₂m' idx = s₂m' := updateAt_self sf₂_pre idx s₂m'
      have hstep_ext : (iparallel sys₂ sync₂).step sf₂_pre
          (.ind idx ((sim default).label_map l)) (updateAt sf₂_pre idx s₂m') := by
        refine ⟨hnosync l hnosyn, ?_, fun j hj => updateAt_other sf₂_pre idx s₂m' j hj⟩
        · rw [heq_pre, ← hlmap, hmid_eq]; exact hstep₂
      obtain ⟨sf₂_post, hstar_post, heq_post, hunch_post⟩ :=
        lift_istar hsync_ext idx (updateAt sf₂_pre idx s₂m') hpost hmid_eq
      exact ⟨sf₂_pre, updateAt sf₂_pre idx s₂m', sf₂_post,
        hstar_pre, hstep_ext, hstar_post,
        fun i => by
          by_cases hi : i = idx
          · subst hi; rw [heq_post]; exact hR_idx
          · rw [hunch_post i hi, updateAt_other sf₂_pre idx s₂m' i hi,
                hunch_pre i hi, hunchanged i hi]; exact hR i⟩
    | .global l =>
      simp [iparallel_labelling, Labelling.is_external] at hext
      have hextL : lab₁.is_external l = true := by simp [Labelling.is_external, hext]
      obtain ⟨hsyn, hstep_all⟩ := hstep
      have hsim_all := fun i => (sim i).step_external
        (sf₁ i) l (sf₁' i) (sf₂ i)
        (iparallel_reachable sf₁ hreach i) (hR i) hextL (hstep_all i)
      let pre_target := fun i => (hsim_all i).1
      let mid_state := fun i => (hsim_all i).2.1
      let post_target := fun i => (hsim_all i).2.2.1
      have hpre := fun i => (hsim_all i).2.2.2.1
      have hstep₂ := fun i => (hsim_all i).2.2.2.2.1
      have hpost := fun i => (hsim_all i).2.2.2.2.2.1
      have hR' := fun i => (hsim_all i).2.2.2.2.2.2
      obtain ⟨sf₂_pre, hstar_pre, heq_pre, _⟩ :=
        sequence_istars hsync_ext enum sf₂ pre_target (fun i _ => hpre i) hnodup
      have hstep_ext : (iparallel sys₂ sync₂).step sf₂_pre
          (.global ((sim default).label_map l)) mid_state := by
        refine ⟨hsync l hsyn, fun i => ?_⟩
        have hlmap : (sim i).label_map = (sim default).label_map := hmap_eq i default
        rw [heq_pre i (henum i), ← hlmap]; exact hstep₂ i
      obtain ⟨sf₂_post, hstar_post, heq_post, _⟩ :=
        sequence_istars hsync_ext enum mid_state post_target (fun i _ => hpost i) hnodup
      exact ⟨sf₂_pre, mid_state, sf₂_post,
        hstar_pre, hstep_ext, hstar_post,
        fun i => by rw [heq_post i (henum i)]; exact hR' i⟩

/-! ## Fair Labels for Parallel Composition

    Building blocks for lifting `ForwardSim.WeakDivPreserving` witnesses
    through parallel composition (Gaspard Lemma 12). -/

/-- The fair-label classifier for a binary parallel composition. A
    `.left la` step is fair iff the A-component classifies `la` as fair at
    the A-component state; analogously for `.right`. A `.sync la lb` step
    is fair iff both components classify their respective labels as fair
    at their respective states. -/
def parallel_fair_labels
    {SA : Type uA} {LA : Type vA} {SB : Type uB} {LB : Type vB}
    (fairA : SA → LA → Prop) (fairB : SB → LB → Prop) :
    SA × SB → CompLabel LA LB → Prop
  | (sa, _),  .left la     => fairA sa la
  | (_, sb),  .right lb    => fairB sb lb
  | (sa, sb), .sync la lb  => fairA sa la ∧ fairB sb lb

/-! ## Compositionality of `WeakDivPreserving` (Gaspard Lemma 12) -/

/-- **Compositionality** (Gaspard CONCUR 2026, Lemma 12): given
    `WeakDivPreserving` witnesses for two component simulations whose
    compatibility conditions match those required by `parallel_forward_sim`,
    the composed parallel simulation is also `WeakDivPreserving`.

    The composed `rank` is the lex-disjoint-union of the per-component ranks
    on the state pair (A component first, then B). The composed
    `fair_elision_progress` case-splits on the composed label and invokes
    the appropriate per-component witness clause. The composed
    `fair_deadlock_diverges` requires both components to be at fair
    deadlocks (so neither side can take a fair step), then composes the
    per-component abstract divergences.

    Construction sketched (Phase 2.3). `rank` and `rank_wf` are fully
    proven via lexicographic composition of the per-component ranks;
    `fair_elision_progress` and `fair_deadlock_diverges` are sketched with
    sub-sorries pending follow-up. -/
noncomputable def compose_with_compatible
    {SA₁ : Type uA₁} {LA₁ : Type vA₁} {SA₂ : Type uA₂} {LA₂ : Type vA₂}
    {SB₁ : Type uB₁} {LB₁ : Type vB₁} {SB₂ : Type uB₂} {LB₂ : Type vB₂}
    {sysA₁ : System SA₁ LA₁} {sysA₂ : System SA₂ LA₂}
    {sysB₁ : System SB₁ LB₁} {sysB₂ : System SB₂ LB₂}
    {labA₁ : Labelling LA₁} {labA₂ : Labelling LA₂}
    {labB₁ : Labelling LB₁} {labB₂ : Labelling LB₂}
    {sync₁ : LA₁ → LB₁ → Prop} {sync₂ : LA₂ → LB₂ → Prop}
    {simA : ForwardSim sysA₁ labA₁ sysA₂ labA₂}
    {simB : ForwardSim sysB₁ labB₁ sysB₂ labB₂}
    (hsync : ∀ la lb, sync₁ la lb → sync₂ (simA.label_map la) (simB.label_map lb))
    (hnosync_left : ∀ la,
      (∀ lb, ¬sync₁ la lb) → ∀ lb₂, ¬sync₂ (simA.label_map la) lb₂)
    (hnosync_right : ∀ lb,
      (∀ la, ¬sync₁ la lb) → ∀ la₂, ¬sync₂ la₂ (simB.label_map lb))
    (hsync_ext : ∀ la lb, sync₂ la lb →
      labA₂.is_external la = true ∧ labB₂.is_external lb = true)
    (hmap_int_a : ∀ la, labA₁.is_internal la = true →
      labA₂.is_internal (simA.label_map la) = true)
    (hmap_int_b : ∀ lb, labB₁.is_internal lb = true →
      labB₂.is_internal (simB.label_map lb) = true)
    {fairA₁ : SA₁ → LA₁ → Prop} {fairA₂ : SA₂ → LA₂ → Prop}
    {fairB₁ : SB₁ → LB₁ → Prop} {fairB₂ : SB₂ → LB₂ → Prop}
    (wdA : simA.WeakDivPreserving fairA₁ fairA₂)
    (wdB : simB.WeakDivPreserving fairB₁ fairB₂) :
    (parallel_forward_sim simA simB hsync hnosync_left hnosync_right
        hsync_ext hmap_int_a hmap_int_b).WeakDivPreserving
      (parallel_fair_labels fairA₁ fairB₁)
      (parallel_fair_labels fairA₂ fairB₂) where
  rank := Prod.Lex wdA.rank wdB.rank
  rank_wf := wdA.rank_wf.prod_lex wdB.rank_wf
  fair_elision_progress := by
    -- Structure of the proof: case split on the composed label.
    intro ⟨sa₁, sb₁⟩ cl ⟨sa₁', sb₁'⟩ ⟨sa₂, sb₂⟩ hreach hR hint hfair hstep hempty
    obtain ⟨hRa, hRb⟩ := hR
    match cl with
    | .left la =>
      -- Composed elision (hempty) ↔ A's InternalStar is empty.
      -- Apply wdA.fair_elision_progress to get rank decrease (→
      -- Prod.Lex.left case of composed rank) or A's abstract divergence
      -- (→ lift to composed FairlyWeaklyDiverges).
      sorry
    | .right lb =>
      -- Symmetric to .left, using wdB and Prod.Lex.right.
      sorry
    | .sync la lb =>
      -- Composed elision requires both A's and B's stars to be empty.
      -- The composed sync step requires both components internal (already
      -- destructured via hint). Both A and B step in lock-step; either
      -- witness's fair_elision_progress can be applied (whichever fair
      -- component drives the rank decrease).
      sorry
  fair_deadlock_diverges := by
    -- A fair-deadlock of the composition means no fair composed label is
    -- enabled. By structure of `parallel`, this implies (roughly) that
    -- the A component cannot take any fair A-step AND the B component
    -- cannot take any fair B-step AND no fair sync is possible. Then by
    -- wdA.fair_deadlock_diverges and wdB.fair_deadlock_diverges, both
    -- abstract components fairly weakly diverge, which gives composed
    -- FairlyWeaklyDiverges (via a helper).
    --
    -- ===== Step 1: destructure inputs =====
    intro s₁ s₂ hreach hR hfd
    obtain ⟨sa₁, sb₁⟩ := s₁
    obtain ⟨sa₂, sb₂⟩ := s₂
    obtain ⟨hRa, hRb⟩ := hR
    -- ===== Step 2: derive component fair-deadlocks =====
    -- For the A component: suppose `sysA₁.step sa₁ la sa₁'` with
    -- `fairA₁ sa₁ la`. We want a contradiction with `hfd`.
    -- Case split on whether `la` synchronizes with anything.
    have hfdA : FairDeadlock sysA₁ fairA₁ sa₁ := by
      intro la sa₁' hstepA hfairA
      by_cases hnosync : ∀ lb, ¬ sync₁ la lb
      · -- `.left la` is enabled; fair label is `fairA₁ sa₁ la`.
        have hcstep : (parallel sysA₁ sysB₁ sync₁).step
            (sa₁, sb₁) (.left la) (sa₁', sb₁) := ⟨hnosync, hstepA, rfl⟩
        have hcfair : parallel_fair_labels fairA₁ fairB₁ (sa₁, sb₁) (.left la) :=
          hfairA
        exact hfd (.left la) (sa₁', sb₁) hcstep hcfair
      · -- `la` syncs with some `lb`. The composed `.left la` step is blocked.
        -- The remaining option is a `.sync la lb` step (or no enabled
        -- composed step using `la`). We cannot in general derive a
        -- contradiction without an additional fairness assumption about
        -- the syncing partner. This is the unresolved sub-case.
        sorry
    have hfdB : FairDeadlock sysB₁ fairB₁ sb₁ := by
      intro lb sb₁' hstepB hfairB
      by_cases hnosync : ∀ la, ¬ sync₁ la lb
      · -- `.right lb` is enabled; fair label is `fairB₁ sb₁ lb`.
        have hcstep : (parallel sysA₁ sysB₁ sync₁).step
            (sa₁, sb₁) (.right lb) (sa₁, sb₁') := ⟨hnosync, hstepB, rfl⟩
        have hcfair : parallel_fair_labels fairA₁ fairB₁ (sa₁, sb₁) (.right lb) :=
          hfairB
        exact hfd (.right lb) (sa₁, sb₁') hcstep hcfair
      · -- Symmetric to `hfdA`'s syncing sub-case.
        sorry
    -- ===== Step 3: apply per-component witnesses =====
    have hdivA : FairlyWeaklyDiverges sysA₂ labA₂ fairA₂ sa₂ :=
      wdA.fair_deadlock_diverges sa₁ sa₂ (reachable_left _ hreach) hRa hfdA
    have hdivB : FairlyWeaklyDiverges sysB₂ labB₂ fairB₂ sb₂ :=
      wdB.fair_deadlock_diverges sb₁ sb₂ (reachable_right _ hreach) hRb hfdB
    -- ===== Step 4: combine per-component divergences =====
    -- Four sub-cases by the disjunctions in `hdivA` and `hdivB`. We prove
    -- the "both fair-deadlock" sub-case in full (per task spec); other
    -- sub-cases are scoped sorries.
    -- Helper: lift A's fair-divergence at sa₂ to a composed fair-divergence
    -- at (sa₂, sb₂) via `.left _` actions (B unchanged).
    have lift_A_fdiv : ∀ sb,
        FairDiverges sysA₂ labA₂ fairA₂ sa₂ →
        FairDiverges (parallel sysA₂ sysB₂ sync₂)
          (parallel_labelling labA₂ labB₂)
          (parallel_fair_labels fairA₂ fairB₂) (sa₂, sb) := by
      intro sb ⟨eA, heA0, heAstep, heAfair⟩
      refine ⟨{ states := fun n => (eA.states n, sb),
                 labels := fun n => .left (eA.labels n) }, ?_, ?_, ?_⟩
      · simp [heA0]
      · intro k
        obtain ⟨hsteA, hintA⟩ := heAstep k
        refine ⟨?_, ?_⟩
        · -- Composed step `.left (eA.labels k)` requires non-sync.
          refine ⟨fun lb hsyn => ?_, hsteA, rfl⟩
          have := (hsync_ext _ lb hsyn).1
          simp [Labelling.is_external, hintA] at this
        · -- Composed label is internal because A's label is internal.
          show (parallel_labelling labA₂ labB₂).is_internal (.left _) = true
          simp [parallel_labelling, hintA]
      · intro N
        obtain ⟨k, hkN, hfair_k⟩ := heAfair N
        refine ⟨k, hkN, ?_⟩
        -- `parallel_fair_labels _ _ (_, sb) (.left _) = fairA₂ _ _`.
        exact hfair_k
    -- Helper: lift B's fair-divergence at sb₂ to a composed fair-divergence
    -- at (sa, sb₂) via `.right _` actions (A unchanged).
    have lift_B_fdiv : ∀ sa,
        FairDiverges sysB₂ labB₂ fairB₂ sb₂ →
        FairDiverges (parallel sysA₂ sysB₂ sync₂)
          (parallel_labelling labA₂ labB₂)
          (parallel_fair_labels fairA₂ fairB₂) (sa, sb₂) := by
      intro sa ⟨eB, heB0, heBstep, heBfair⟩
      refine ⟨{ states := fun n => (sa, eB.states n),
                 labels := fun n => .right (eB.labels n) }, ?_, ?_, ?_⟩
      · simp [heB0]
      · intro k
        obtain ⟨hsteB, hintB⟩ := heBstep k
        refine ⟨?_, ?_⟩
        · refine ⟨fun la hsyn => ?_, hsteB, rfl⟩
          have := (hsync_ext la _ hsyn).2
          simp [Labelling.is_external, hintB] at this
        · show (parallel_labelling labA₂ labB₂).is_internal (.right _) = true
          simp [parallel_labelling, hintB]
      · intro N
        obtain ⟨k, hkN, hfair_k⟩ := heBfair N
        refine ⟨k, hkN, ?_⟩
        exact hfair_k
    rcases hdivA with hfdivA | ⟨sa_dead, ⟨hpathA⟩, hfdA_dead⟩
    · -- A fair-diverges abstractly. In either B sub-case, lift A's
      -- divergence via `.left _` (B unchanged). The composed state is a
      -- fair divergence, regardless of B's status.
      exact Or.inl (lift_A_fdiv sb₂ hfdivA)
    · -- A reaches a fair-deadlock at `sa_dead` via internal path.
      rcases hdivB with hfdivB | ⟨sb_dead, ⟨hpathB⟩, hfdB_dead⟩
      · -- B fair-diverges. Walk A's path to (sa_dead, sb₂), then build
        -- a composed fair divergence from B's fair divergence (A unchanged).
        have hpath_lifted :
            InternalStar (parallel sysA₂ sysB₂ sync₂)
              (parallel_labelling labA₂ labB₂) (sa₂, sb₂) (sa_dead, sb₂) :=
          lift_star_left hsync_ext sb₂ hpathA
        -- From (sa_dead, sb₂), B's fair divergence lifts via `.right _`.
        have hdiv_lifted :
            FairlyWeaklyDiverges (parallel sysA₂ sysB₂ sync₂)
              (parallel_labelling labA₂ labB₂)
              (parallel_fair_labels fairA₂ fairB₂) (sa_dead, sb₂) :=
          Or.inl (lift_B_fdiv sa_dead hfdivB)
        exact FairlyWeaklyDiverges.lift hpath_lifted hdiv_lifted
      · -- ===== "Both fair-deadlock" sub-case: fully proven =====
        -- Walk A's path (B fixed at sb₂), then B's path (A fixed at sa_dead).
        -- The composed state (sa_dead, sb_dead) is a fair-deadlock of
        -- the composed abstract system.
        refine Or.inr ⟨(sa_dead, sb_dead), ?_, ?_⟩
        · -- Internal path from (sa₂, sb₂) to (sa_dead, sb_dead).
          refine ⟨(lift_star_left hsync_ext sb₂ hpathA).trans
                  (lift_star_right hsync_ext sa_dead hpathB)⟩
        · -- (sa_dead, sb_dead) is a composed fair-deadlock.
          intro cl s' hcstep hcfair
          match cl with
          | .left la =>
            obtain ⟨_, hstepA, _⟩ := hcstep
            -- `hcfair : fairA₂ sa_dead la` — contradicts `hfdA_dead`.
            exact hfdA_dead la _ hstepA hcfair
          | .right lb =>
            obtain ⟨_, hstepB, _⟩ := hcstep
            exact hfdB_dead lb _ hstepB hcfair
          | .sync la lb =>
            obtain ⟨_, hstepA, _⟩ := hcstep
            -- `hcfair = ⟨fairA₂ sa_dead la, fairB₂ sb_dead lb⟩`;
            -- first conjunct contradicts `hfdA_dead`.
            exact hfdA_dead la _ hstepA hcfair.1

end LTS
