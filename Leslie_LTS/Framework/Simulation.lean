import Leslie_LTS.Framework.Rules
import Leslie_LTS.Framework.Divergence
import Leslie_LTS.Framework.Liveness
import Mathlib.Data.Nat.Find

/-! # Simulation Relations for LTS

    Forward and backward simulations with label mappings.
    Adapted from Leslie_LTS.Refinement but with labelled transitions.
-/

open Classical

namespace LTS

variable {S₁ : Type u₁} {L₁ : Type v₁} {S₂ : Type u₂} {L₂ : Type v₂}

/-! ## Functional Refinement Mapping -/

/-- A functional refinement mapping between two LTS: a pair of
    functions (state map, label map) such that init and step
    are preserved pointwise. -/
structure RefinementMap
    (concrete : System S₁ L₁)
    (abstract : System S₂ L₂) where
  /-- The function mapping concrete states to abstract states. -/
  state_map : S₁ → S₂
  /-- The function mapping concrete labels to abstract labels. -/
  label_map : L₁ → L₂
  /-- Every concrete initial state maps to an abstract initial state. -/
  init_preserved : ∀ s, concrete.init s → abstract.init (state_map s)
  /-- Every concrete step maps to a valid abstract step. -/
  step_preserved : ∀ s l s', concrete.step s l s' →
    abstract.step (state_map s) (label_map l) (state_map s')

/-- A refinement mapping preserves all invariants:
    if `P` is an invariant of the abstract system, then `P ∘ state_map`
    is an invariant of the concrete system. -/
theorem RefinementMap.preserves_invariant
    {concrete : System S₁ L₁} {abstract : System S₂ L₂}
    (rm : RefinementMap concrete abstract)
    (P : S₂ → Prop)
    (hP : abstract.satisfies [ltl| □ ⌜ P ⌝]) :
    concrete.satisfies [ltl| □ ⌜ P ∘ rm.state_map ⌝] := by
  intro e hv k
  simp [state_prop, Function.comp]
  have habs : abstract.valid_exec (e.map rm.state_map rm.label_map) := by
    constructor
    · exact rm.init_preserved _ hv.1
    · intro n; simp [Execution.map, Function.comp]; exact rm.step_preserved _ _ _ (hv.2 n)
  have := hP _ habs k
  simp [state_prop, Execution.map, Function.comp] at this
  exact this

/-- A refinement mapping maps valid concrete executions to valid abstract executions. -/
theorem RefinementMap.map_valid_exec
    {concrete : System S₁ L₁} {abstract : System S₂ L₂}
    (rm : RefinementMap concrete abstract)
    {e : Execution S₁ L₁} (hv : concrete.valid_exec e) :
    abstract.valid_exec (e.map rm.state_map rm.label_map) := by
  constructor
  · exact rm.init_preserved _ hv.1
  · intro n; simp [Execution.map, Function.comp]; exact rm.step_preserved _ _ _ (hv.2 n)

/-! ## Forward Simulation (Relational) -/

/-- A forward simulation relation between two LTS with a label mapping.
    Each concrete step `s₁ -l₁→ s₁'` is matched by an abstract step
    `s₂ -(label_map l₁)→ s₂'` with `R s₁' s₂'`. -/
structure ForwardSimStrong
    (concrete : System S₁ L₁)
    (abstract : System S₂ L₂) where
  /-- The simulation relation between concrete and abstract states. -/
  R : S₁ → S₂ → Prop
  /-- The function mapping concrete labels to abstract labels. -/
  label_map : L₁ → L₂
  /-- Every concrete initial state has a related abstract initial state. -/
  init_sim : ∀ s₁, concrete.init s₁ →
    Σ' s₂, abstract.init s₂ ∧ R s₁ s₂
  /-- Every concrete step from a related pair produces a related pair,
      with the abstract side taking a matching step. -/
  step_sim : ∀ s₁ l₁ s₁' s₂, R s₁ s₂ → concrete.step s₁ l₁ s₁' →
    Σ' s₂', abstract.step s₂ (label_map l₁) s₂' ∧ R s₁' s₂'

/-- Build abstract state witnesses along a concrete execution by recursion. -/
private def ForwardSimStrong.build
    {concrete : System S₁ L₁} {abstract : System S₂ L₂}
    (sim : ForwardSimStrong concrete abstract)
    (e : Execution S₁ L₁)
    (hinit : concrete.init (e.states 0))
    (hstep : ∀ k, concrete.step (e.states k) (e.labels k) (e.states (k + 1)))
    : (k : Nat) → { s₂ : S₂ // sim.R (e.states k) s₂ }
  | 0 =>
    let w := sim.init_sim (e.states 0) hinit
    ⟨w.1, w.2.2⟩
  | k + 1 =>
    let prev := sim.build e hinit hstep k
    let w := sim.step_sim (e.states k) (e.labels k) (e.states (k + 1))
      prev.val prev.property (hstep k)
    ⟨w.1, w.2.2⟩

/-- Forward simulation transfers invariants from the abstract to the concrete system:
    if `inv` is an inductive invariant of the abstract system and `R s₁ s₂ ∧ inv s₂ → P s₁`,
    then `P` holds at all states of any valid concrete execution. -/
theorem ForwardSimStrong.preserves_invariant
    {concrete : System S₁ L₁} {abstract : System S₂ L₂}
    (sim : ForwardSimStrong concrete abstract)
    (inv : S₂ → Prop)
    (hinv_init : ∀ s₂, abstract.init s₂ → inv s₂)
    (hinv_step : ∀ s₂ l₂ s₂', inv s₂ → abstract.step s₂ l₂ s₂' → inv s₂')
    (P : S₁ → Prop)
    (hRP : ∀ s₁ s₂, sim.R s₁ s₂ → inv s₂ → P s₁)
    : concrete.satisfies [ltl| □ ⌜ P ⌝] := by
  intro e hv k
  simp [state_prop]
  let w := sim.build e hv.1 hv.2
  suffices h : ∀ n, inv (w n).val from hRP _ _ (w k).property (h k)
  intro n; induction n with
  | zero =>
    exact hinv_init _ (sim.init_sim (e.states 0) hv.1).2.1
  | succ n ih =>
    let prev := w n
    let hex := sim.step_sim (e.states n) (e.labels n) (e.states (n + 1))
      prev.val prev.property (hv.2 n)
    exact hinv_step _ _ _ ih hex.2.1

/-! ## Forward Simulation with Stuttering -/

/-- Forward simulation with stuttering: internal concrete steps are elided
    (the abstract system stays put), while external concrete steps are
    matched one-to-one via the label map. -/
structure ForwardSimStutter
    (concrete : System S₁ L₁) (lab₁ : Labelling L₁)
    (abstract : System S₂ L₂) where
  /-- The simulation relation between concrete and abstract states. -/
  R : S₁ → S₂ → Prop
  /-- The function mapping concrete external labels to abstract labels. -/
  label_map : L₁ → L₂
  /-- Every concrete initial state has a related abstract initial state. -/
  init_sim : ∀ s₁, concrete.init s₁ →
    ∃ s₂, abstract.init s₂ ∧ R s₁ s₂
  /-- An internal concrete step is elided: the abstract stays put
      and the relation is preserved. -/
  step_internal : ∀ s₁ l₁ s₁' s₂, R s₁ s₂ →
    lab₁.is_internal l₁ = true → concrete.step s₁ l₁ s₁' → R s₁' s₂
  /-- An external concrete step is matched by exactly one abstract step
      with the mapped label. -/
  step_external : ∀ s₁ l₁ s₁' s₂, R s₁ s₂ →
    lab₁.is_external l₁ = true → concrete.step s₁ l₁ s₁' →
    ∃ s₂', abstract.step s₂ (label_map l₁) s₂' ∧ R s₁' s₂'

/-- Stuttering forward simulation transfers invariants from
    the abstract to the concrete system. -/
theorem ForwardSimStutter.preserves_invariant
    {concrete : System S₁ L₁} {lab₁ : Labelling L₁}
    {abstract : System S₂ L₂}
    (sim : ForwardSimStutter concrete lab₁ abstract)
    (inv : S₂ → Prop)
    (hinv_init : ∀ s₂, abstract.init s₂ → inv s₂)
    (hinv_step : ∀ s₂ l₂ s₂', inv s₂ → abstract.step s₂ l₂ s₂' → inv s₂')
    (P : S₁ → Prop)
    (hRP : ∀ s₁ s₂, sim.R s₁ s₂ → inv s₂ → P s₁)
    : concrete.satisfies [ltl| □ ⌜ P ⌝] := by
  intro e hv k
  simp [state_prop]
  suffices h : ∀ n, ∃ s₂, sim.R (e.states n) s₂ ∧ inv s₂ from by
    obtain ⟨s₂, hr, hinv⟩ := h k; exact hRP _ _ hr hinv
  intro n; induction n with
  | zero =>
    obtain ⟨s₂, ha, hr⟩ := sim.init_sim _ hv.1
    exact ⟨s₂, hr, hinv_init _ ha⟩
  | succ n ih =>
    obtain ⟨s₂, hr, hinv⟩ := ih
    by_cases hint : lab₁.is_internal (e.labels n) = true
    · exact ⟨s₂, sim.step_internal _ _ _ s₂ hr hint (hv.2 n), hinv⟩
    · have hext : lab₁.is_external (e.labels n) = true := by
        simp [Labelling.is_external, hint]
      obtain ⟨s₂', hstep, hr'⟩ := sim.step_external _ _ _ s₂ hr hext (hv.2 n)
      exact ⟨s₂', hr', hinv_step _ _ _ hinv hstep⟩

/-! ## Forward Simulation (Weak, via Internal/External Labels)

    A concrete step with an internal label is simulated by zero or more
    internal abstract steps. A concrete step with an external label `l₁`
    is simulated by zero or more internal abstract steps, then one external
    step with `label_map l₁`, then zero or more internal abstract steps. -/

/-- Forward simulation between two LTS with internal/external label distinction.
    One concrete step may be simulated by zero or more abstract steps,
    depending on whether the label is internal or external. -/
structure ForwardSim
    (concrete : System S₁ L₁) (lab₁ : Labelling L₁)
    (abstract : System S₂ L₂) (lab₂ : Labelling L₂) where
  /-- The simulation relation between concrete and abstract states. -/
  R : S₁ → S₂ → Prop
  /-- The function mapping concrete external labels to abstract external labels. -/
  label_map : L₁ → L₂
  /-- Every concrete initial state has a related abstract initial state. -/
  init_sim : ∀ s₁, concrete.init s₁ →
    Σ' s₂, abstract.init s₂ ∧ R s₁ s₂
  /-- An internal concrete step from a reachable state is simulated by
      zero or more internal abstract steps. -/
  step_internal : ∀ s₁ l₁ s₁' s₂, Reachable concrete s₁ → R s₁ s₂ →
    lab₁.is_internal l₁ = true → concrete.step s₁ l₁ s₁' →
    Σ' s₂', InternalStar abstract lab₂ s₂ s₂' ×' R s₁' s₂'
  /-- An external concrete step from a reachable state is simulated by:
      zero or more internal abstract steps, then one external step with
      the mapped label, then zero or more internal abstract steps. -/
  step_external : ∀ s₁ l₁ s₁' s₂, Reachable concrete s₁ → R s₁ s₂ →
    lab₁.is_external l₁ = true → concrete.step s₁ l₁ s₁' →
    Σ' (s₂_mid : S₂) (s₂_mid' : S₂) (s₂' : S₂),
      InternalStar abstract lab₂ s₂ s₂_mid ×'
      abstract.step s₂_mid (label_map l₁) s₂_mid' ×'
      InternalStar abstract lab₂ s₂_mid' s₂' ×'
      R s₁' s₂'

/-- Forward simulation transfers invariants from the abstract to the concrete system. -/
theorem ForwardSim.preserves_invariant
    {concrete : System S₁ L₁} {lab₁ : Labelling L₁}
    {abstract : System S₂ L₂} {lab₂ : Labelling L₂}
    (sim : ForwardSim concrete lab₁ abstract lab₂)
    (inv : S₂ → Prop)
    (hinv_init : ∀ s₂, abstract.init s₂ → inv s₂)
    (hinv_step : ∀ s₂ l₂ s₂', inv s₂ → abstract.step s₂ l₂ s₂' → inv s₂')
    (P : S₁ → Prop)
    (hRP : ∀ s₁ s₂, sim.R s₁ s₂ → inv s₂ → P s₁)
    : concrete.satisfies [ltl| □ ⌜ P ⌝] := by
  intro e hv k
  simp [state_prop]
  have hreach := System.valid_exec_reachable hv
  suffices h : ∀ n, ∃ s₂, sim.R (e.states n) s₂ ∧ inv s₂ from by
    obtain ⟨s₂, hr, hinv⟩ := h k; exact hRP _ _ hr hinv
  intro n; induction n with
  | zero =>
    obtain ⟨s₂, ha, hr⟩ := sim.init_sim _ hv.1
    exact ⟨s₂, hr, hinv_init _ ha⟩
  | succ n ih =>
    obtain ⟨s₂, hr, hinv⟩ := ih
    by_cases hint : lab₁.is_internal (e.labels n) = true
    · obtain ⟨s₂', hstar, hr'⟩ :=
        sim.step_internal _ _ _ s₂ (hreach n) hr hint (hv.2 n)
      exact ⟨s₂', hr', InternalStar.preserve_inv hinv_step hstar hinv⟩
    · have hext : lab₁.is_external (e.labels n) = true := by
        simp [Labelling.is_external, hint]
      obtain ⟨s₂_mid, s₂_mid', s₂', hstar1, hstep, hstar2, hr'⟩ :=
        sim.step_external _ _ _ s₂ (hreach n) hr hext (hv.2 n)
      have hinv_mid := InternalStar.preserve_inv hinv_step hstar1 hinv
      have hinv_mid' := hinv_step _ _ _ hinv_mid hstep
      exact ⟨s₂', hr', InternalStar.preserve_inv hinv_step hstar2 hinv_mid'⟩

/-! ## Lifting Branching Properties

    A **branching property** has the form:
    ```
    ∀ s, Reachable sys s → Guard(s) →
      ∃ w, ∀ s', Star sys s s' → Concl(w, s')
    ```
    Unlike trace properties (which speak about a single execution), branching
    properties quantify over **all possible continuations** from a state.

    A forward simulation can lift such properties from abstract to concrete,
    provided the guard and conclusion transfer through the simulation relation.
-/

/-- Every reachable concrete state has a related reachable abstract state. -/
theorem ForwardSim.reachable_sim
    {concrete : System S₁ L₁} {lab₁ : Labelling L₁}
    {abstract : System S₂ L₂} {lab₂ : Labelling L₂}
    (sim : ForwardSim concrete lab₁ abstract lab₂)
    (s₁ : S₁) (hr : Reachable concrete s₁) :
    ∃ s₂, Reachable abstract s₂ ∧ sim.R s₁ s₂ := by
  induction hr with
  | init hinit =>
    obtain ⟨s₂, ha, hR⟩ := sim.init_sim _ hinit
    exact ⟨s₂, .init ha, hR⟩
  | step hreach hstep ih =>
    obtain ⟨s₂, hreach₂, hR⟩ := ih
    by_cases hint : lab₁.is_internal ‹_› = true
    · obtain ⟨s₂', hstar, hR'⟩ := sim.step_internal _ _ _ s₂ hreach hR hint hstep
      exact ⟨s₂', hstar.toStar.reachable hreach₂, hR'⟩
    · have hext : lab₁.is_external ‹_› = true := by simp [Labelling.is_external, hint]
      obtain ⟨s₂_mid, s₂_mid', s₂', hstar1, hstep₂, hstar2, hR'⟩ :=
        sim.step_external _ _ _ s₂ hreach hR hext hstep
      have hr_mid := hstar1.toStar.reachable hreach₂
      have hr_mid' := Reachable.step hr_mid hstep₂
      exact ⟨s₂', hstar2.toStar.reachable hr_mid', hR'⟩

/-- A concrete `Star` path lifts to an abstract `Star` path preserving `R`. -/
theorem ForwardSim.star_sim
    {concrete : System S₁ L₁} {lab₁ : Labelling L₁}
    {abstract : System S₂ L₂} {lab₂ : Labelling L₂}
    (sim : ForwardSim concrete lab₁ abstract lab₂)
    {s₁ s₁' : S₁} {s₂ : S₂}
    (hstar : Star concrete s₁ s₁')
    (hreach : Reachable concrete s₁)
    (hR : sim.R s₁ s₂) :
    ∃ s₂', Star abstract s₂ s₂' ∧ sim.R s₁' s₂' := by
  induction hstar generalizing s₂ with
  | refl => exact ⟨s₂, .refl, hR⟩
  | step hstep _ ih =>
    by_cases hint : lab₁.is_internal ‹_› = true
    · obtain ⟨s₂_next, hstar_abs, hR_next⟩ :=
        sim.step_internal _ _ _ s₂ hreach hR hint hstep
      obtain ⟨s₂', hstar_rest, hR'⟩ :=
        ih (.step hreach hstep) hR_next
      exact ⟨s₂', hstar_abs.toStar.trans hstar_rest, hR'⟩
    · have hext : lab₁.is_external ‹_› = true := by simp [Labelling.is_external, hint]
      obtain ⟨s₂_mid, s₂_mid', s₂_next, hstar1, hstep₂, hstar2, hR_next⟩ :=
        sim.step_external _ _ _ s₂ hreach hR hext hstep
      obtain ⟨s₂', hstar_rest, hR'⟩ :=
        ih (.step hreach hstep) hR_next
      exact ⟨s₂', (hstar1.toStar.trans (.step hstep₂ hstar2.toStar)).trans hstar_rest, hR'⟩

/-- **Branching property lifting**: if the abstract system satisfies a branching
    property of the form `∀ reachable s, Guard(s) → ∃ w, ∀ continuation s', Concl(w, s')`,
    and the guard/conclusion transfer through the simulation relation `R`,
    then the concrete system satisfies the analogous branching property. -/
theorem ForwardSim.preserves_branching
    {concrete : System S₁ L₁} {lab₁ : Labelling L₁}
    {abstract : System S₂ L₂} {lab₂ : Labelling L₂}
    (sim : ForwardSim concrete lab₁ abstract lab₂)
    {P_guard : S₂ → Prop} {P_concl : W → S₂ → Prop}
    {Q_guard : S₁ → Prop} {Q_concl : W → S₁ → Prop}
    (h_abs : ∀ s₂, Reachable abstract s₂ → P_guard s₂ →
      ∃ w, ∀ s₂', Star abstract s₂ s₂' → P_concl w s₂')
    (h_guard : ∀ s₁ s₂, sim.R s₁ s₂ → Q_guard s₁ → P_guard s₂)
    (h_concl : ∀ w s₁ s₂, sim.R s₁ s₂ → P_concl w s₂ → Q_concl w s₁)
    : ∀ s₁, Reachable concrete s₁ → Q_guard s₁ →
        ∃ w, ∀ s₁', Star concrete s₁ s₁' → Q_concl w s₁' := by
  intro s₁ hreach₁ hguard₁
  obtain ⟨s₂, hreach₂, hR⟩ := sim.reachable_sim s₁ hreach₁
  obtain ⟨w, habs⟩ := h_abs s₂ hreach₂ (h_guard s₁ s₂ hR hguard₁)
  exact ⟨w, fun s₁' hstar => by
    obtain ⟨s₂', hstar₂, hR'⟩ := sim.star_sim hstar hreach₁ hR
    exact h_concl w s₁' s₂' hR' (habs s₂' hstar₂)⟩

/-! ## Lifting External Trace Properties

    A forward simulation preserves external trace properties: the external
    label subsequence of a concrete execution corresponds (via `label_map`)
    to the external label subsequence of the abstract execution.

    The key fact: for a `ForwardSim`, each concrete external step produces
    exactly one abstract external step with the mapped label, and each
    concrete internal step produces only internal abstract steps. So the
    external label subsequences are in 1-to-1 correspondence. -/

/-- One step of the simulation: given a witness at step `k`, produce the
    next witness and an `LPath` connecting them. Returns a sigma type so
    the witness and path share the same target by construction. -/
private def ForwardSim.stepHelper
    {concrete : System S₁ L₁} {lab₁ : Labelling L₁}
    {abstract : System S₂ L₂} {lab₂ : Labelling L₂}
    (sim : ForwardSim concrete lab₁ abstract lab₂)
    [Inhabited L₂]
    (e : Execution S₁ L₁) (hv : concrete.valid_exec e)
    (k : Nat) (s₂ : S₂) (hR : sim.R (e.states k) s₂) :
    { p : Σ (s₂' : S₂), LPath abstract.step s₂ s₂' //
      sim.R (e.states (k + 1)) p.1 ∧
      -- Internal step → all path labels internal
      (lab₁.is_internal (e.labels k) = true →
        ∀ i, i < p.2.length → lab₂.is_internal (p.2.get_label i) = true) ∧
      -- External step → one label = label_map, rest internal
      (lab₁.is_external (e.labels k) = true →
        ∃ idx, idx < p.2.length ∧
          p.2.get_label idx = sim.label_map (e.labels k) ∧
          (∀ j, j < p.2.length → j ≠ idx →
            lab₂.is_internal (p.2.get_label j) = true)) } :=
  let hreach := System.valid_exec_reachable hv k
  if hint : lab₁.is_internal (e.labels k) = true then
    let hex := sim.step_internal _ _ _ s₂ hreach hR hint (hv.2 k)
    let ilp := hex.2.1.toInternalLPath
    ⟨⟨hex.1, ilp.val⟩,
     hex.2.2,
     fun _ i hi => ilp.property i hi,
     fun hext => absurd hint (by simp [Labelling.is_external] at hext; simp [hext])⟩
  else
    let hext : lab₁.is_external (e.labels k) = true := by
      simp [Labelling.is_external, hint]
    let hex := sim.step_external _ _ _ s₂ hreach hR hext (hv.2 k)
    let hspec := hex.2.2.2
    let star1 := hspec.1.toInternalLPath
    let star2 := hspec.2.2.1.toInternalLPath
    let path := star1.val.append (LPath.single hspec.2.1 |>.append star2.val)
    ⟨⟨hex.2.2.1, path⟩,
     hspec.2.2.2,
     fun hint' => absurd hint' (by simp [Labelling.is_external] at hext; simp [hext]),
     fun _ => ⟨star1.val.length, by
        have hpath : (⟨hex.2.2.1, path⟩ :
            Σ s₂', LPath abstract.step s₂ s₂').2 = path := rfl
        rw [hpath]
        have hlen : path.length = star1.val.length + (1 + star2.val.length) := by
          simp [path, LPath.length_append, LPath.length_single]
        refine ⟨by omega, ?_, ?_⟩
        · -- Middle label = label_map
          show path.get_label star1.val.length = sim.label_map (e.labels k)
          have h1 : path.get_label star1.val.length =
              (LPath.single hspec.2.1 |>.append star2.val).get_label 0 := by
            show path.get_label (star1.val.length + 0) = _
            exact LPath.get_label_append_right star1.val _ 0
              (by simp [LPath.length_append, LPath.length_single]; omega)
          rw [h1, LPath.get_label_append_left _ _ _ (by simp [LPath.length_single])]
          exact LPath.get_label_single _
        · -- Other labels are internal
          intro j hj hne
          show lab₂.is_internal (path.get_label j) = true
          by_cases hjl : j < star1.val.length
          · rw [LPath.get_label_append_left _ _ _ hjl]
            exact star1.property j hjl
          · have hge : j ≥ star1.val.length := by omega
            have hji : j - star1.val.length <
                ((LPath.single hspec.2.1).append star2.val).length := by
              simp [LPath.length_append, LPath.length_single]; omega
            rw [show j = star1.val.length + (j - star1.val.length) from by omega,
                LPath.get_label_append_right star1.val _ _ hji]
            have hgt : j - star1.val.length ≥ 1 := by omega
            have hsub : j - star1.val.length - 1 < star2.val.length := by omega
            rw [show j - star1.val.length =
                (LPath.single hspec.2.1).length + (j - star1.val.length - 1) from by
                  simp [LPath.length_single]; omega,
                LPath.get_label_append_right _ _ _ hsub]
            exact star2.property _ hsub⟩⟩

/-- Build abstract state witnesses along a concrete execution by iterating
    `stepHelper`. At each step `k`, we have an abstract state related by `R`. -/
private def ForwardSim.buildWitness
    {concrete : System S₁ L₁} {lab₁ : Labelling L₁}
    {abstract : System S₂ L₂} {lab₂ : Labelling L₂}
    (sim : ForwardSim concrete lab₁ abstract lab₂)
    [Inhabited L₂]
    (e : Execution S₁ L₁) (hv : concrete.valid_exec e) :
    (k : Nat) → { s₂ : S₂ // sim.R (e.states k) s₂ }
  | 0 =>
    let w := sim.init_sim (e.states 0) hv.1
    ⟨w.1, w.2.2⟩
  | k + 1 =>
    let prev := sim.buildWitness e hv k
    let result := sim.stepHelper e hv k prev.val prev.property
    ⟨result.val.1, result.property.1⟩

/-- Extract the `LPath` between consecutive witnesses. The endpoints match
    by construction since both `buildWitness` and `buildLPath` use
    `stepHelper`, so the target `(buildWitness (k+1)).1` is definitionally
    `(stepHelper k (buildWitness k).1 (buildWitness k).2).1`. -/
private def ForwardSim.buildLPath
    {concrete : System S₁ L₁} {lab₁ : Labelling L₁}
    {abstract : System S₂ L₂} {lab₂ : Labelling L₂}
    (sim : ForwardSim concrete lab₁ abstract lab₂)
    [Inhabited L₂]
    (e : Execution S₁ L₁) (hv : concrete.valid_exec e)
    (k : Nat) :
    LPath abstract.step
      (sim.buildWitness e hv k).val
      (sim.buildWitness e hv (k + 1)).val :=
  let prev := sim.buildWitness e hv k
  let result := sim.stepHelper e hv k prev.val prev.property
  result.val.2

/-- For an internal concrete step, all labels in the abstract path are internal.
    Accesses the label property from `stepHelper`'s enriched return type. -/
private theorem ForwardSim.buildLPath_internal
    {concrete : System S₁ L₁} {lab₁ : Labelling L₁}
    {abstract : System S₂ L₂} {lab₂ : Labelling L₂}
    (sim : ForwardSim concrete lab₁ abstract lab₂)
    [Inhabited L₂]
    (e : Execution S₁ L₁) (hv : concrete.valid_exec e) (k : Nat)
    (hint : lab₁.is_internal (e.labels k) = true) :
    ∀ i, i < (sim.buildLPath e hv k).length →
      lab₂.is_internal ((sim.buildLPath e hv k).get_label i) = true :=
  (sim.stepHelper e hv k _ _).property.2.1 hint

/-- For an external concrete step, the path has one external label (`label_map l₁`)
    and the rest are internal. -/
private theorem ForwardSim.buildLPath_external
    {concrete : System S₁ L₁} {lab₁ : Labelling L₁}
    {abstract : System S₂ L₂} {lab₂ : Labelling L₂}
    (sim : ForwardSim concrete lab₁ abstract lab₂)
    [Inhabited L₂]
    (e : Execution S₁ L₁) (hv : concrete.valid_exec e) (k : Nat)
    (hext : lab₁.is_external (e.labels k) = true) :
    ∃ idx, idx < (sim.buildLPath e hv k).length ∧
      (sim.buildLPath e hv k).get_label idx = sim.label_map (e.labels k) ∧
      (∀ j, j < (sim.buildLPath e hv k).length → j ≠ idx →
        lab₂.is_internal ((sim.buildLPath e hv k).get_label j) = true) :=
  (sim.stepHelper e hv k _ _).property.2.2 hext

/-- Cumulative offset for flattening path segments. -/
private def loffset (len : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => loffset len k + len k

private theorem loffset_mono (len : Nat → Nat) (k : Nat) :
    loffset len k ≤ loffset len (k + 1) :=
  Nat.le_add_right _ _

private theorem loffset_mono_le (len : Nat → Nat) {j k : Nat} (h : j ≤ k) :
    loffset len j ≤ loffset len k := by
  induction k with
  | zero => rcases Nat.le_zero.mp h with rfl; exact Nat.le_refl _
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact Nat.le_refl _
    · exact Nat.le_trans (ih (Nat.lt_succ_iff.mp hlt)) (loffset_mono len k)

/-- Find the smallest `k` satisfying a decidable predicate, bounded by a witness. -/
private def lfindSmallest (P : Nat → Prop) [DecidablePred P]
    (bound : Nat) (hbound : P bound) : { k // P k ∧ ∀ j, j < k → ¬P j } := by
  suffices aux : ∀ fuel start, start + fuel = bound + 1 →
      (∀ j, j < start → ¬P j) → { k // P k ∧ ∀ j, j < k → ¬P j } from
    aux (bound + 1) 0 (by omega) (fun j hj => by omega)
  intro fuel
  induction fuel with
  | zero =>
    intro start hstart hbelow
    exact ⟨bound, hbound, fun j hj => hbelow j (by omega)⟩
  | succ fuel ih =>
    intro start hstart hbelow
    by_cases hp : P start
    · exact ⟨start, hp, hbelow⟩
    · exact ih (start + 1) (by omega) (fun j hj => by
        by_cases hjs : j < start
        · exact hbelow j hjs
        · have : j = start := by omega
          rw [this]; exact hp)

/-- Flatten an infinite sequence of `LPath` segments into a single `Execution`.

    Adapts `TLA.flattenPaths` from `Refinement.lean` to the LTS setting,
    producing both states and labels. The construction:
    - States: `ea.states t` = `(paths s).get_state (t - off s)` where `s` is
      the segment containing position `t`.
    - Labels: `ea.labels t` = `(paths s).get_label (t - off s)` when inside a
      segment; `default` at stutter positions. -/
private noncomputable def flattenLPaths {S : Type u} {L : Type v}
    [Inhabited L]
    {step : S → L → S → Prop}
    (stutter_label : L)
    (states : Nat → S)
    (paths : (k : Nat) → LPath step (states k) (states (k + 1))) :
    { e : Execution S L //
      (∀ k, e.states (loffset (fun k => (paths k).length) k) = states k) ∧
      (∀ t, step (e.states t) (e.labels t) (e.states (t + 1)) ∨
            (e.states t = e.states (t + 1) ∧ e.labels t = stutter_label)) ∧
      -- Label at segment k, index i comes from paths k
      (∀ k i, i < (paths k).length →
        e.labels (loffset (fun k => (paths k).length) k + i) =
          (paths k).get_label i) ∧
      -- Labels beyond all segments use the stutter label
      (∀ t, (¬∃ k, t + 1 ≤ loffset (fun k => (paths k).length) (k + 1)) →
        e.labels t = stutter_label) } := by
  let len := fun k => (paths k).length
  let off := loffset len
  -- Lookup: given t in range, find the segment and index within it
  let lookupState : (t : Nat) → (∃ k, t ≤ off (k + 1)) → S := fun t h =>
    let s := lfindSmallest (fun k => t ≤ off (k + 1)) h.choose h.choose_spec
    (paths s.val).get_state (t - off s.val)
  -- Label lookup uses the segment containing t+1 (where the step lives)
  let lookupLabel : (t : Nat) → (∃ k, t + 1 ≤ off (k + 1)) → L := fun t h =>
    let s := lfindSmallest (fun k => t + 1 ≤ off (k + 1)) h.choose h.choose_spec
    (paths s.val).get_label (t - off s.val)
  -- Build state sequence
  let ea_states : Nat → S := Nat.rec
    (lookupState 0 ⟨0, Nat.zero_le _⟩)
    (fun t prev =>
      if h : ∃ k, t + 1 ≤ off (k + 1) then lookupState (t + 1) h
      else prev)
  -- Build label sequence: label at position t uses segment containing t+1
  let ea_labels : Nat → L := fun t =>
    if h : ∃ k, t + 1 ≤ off (k + 1) then lookupLabel t h
    else stutter_label
  -- Helper: if path i has length 0, states i = states (i+1)
  have states_eq_of_len_zero : ∀ i, len i = 0 →
      states i = states (i + 1) :=
    fun i hi => LPath.eq_of_length_zero (paths i) hi
  -- If offsets at i and j are equal, states are equal
  have states_eq_of_off_eq : ∀ i j, i ≤ j → loffset len i = loffset len j →
      states i = states j := by
    intro i j hij hoff
    induction j with
    | zero => rcases Nat.le_zero.mp hij with rfl; rfl
    | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with rfl | hlt
      · rfl
      · have hoff_j : loffset len j = loffset len (j + 1) := by
          have h1 := loffset_mono_le len (Nat.lt_succ_iff.mp hlt)
          have h2 := loffset_mono len j
          omega
        rw [ih (Nat.lt_succ_iff.mp hlt) (by omega),
            states_eq_of_len_zero j (by simp [loffset] at hoff_j; omega)]
  -- ea_states t = lookupState t when t is in range
  have ea_states_val : ∀ t, (h : ∃ j, t ≤ off (j + 1)) →
      ea_states t = lookupState t h := by
    intro t ht
    induction t with
    | zero => rfl
    | succ n _ =>
      show (if h : ∃ k, n + 1 ≤ off (k + 1) then lookupState (n + 1) h
            else ea_states n) = lookupState (n + 1) ht
      rw [dif_pos ht]
  -- ea_states (t+1) = ea_states t when t+1 is NOT in range
  have ea_states_stutter : ∀ t, (¬∃ k, t + 1 ≤ off (k + 1)) →
      ea_states (t + 1) = ea_states t := by
    intro t h
    show (if h' : ∃ k, t + 1 ≤ off (k + 1) then lookupState (t + 1) h'
          else ea_states t) = ea_states t
    rw [dif_neg h]
  -- ea_labels t = lookupLabel t when t+1 is in range
  have ea_labels_val : ∀ t, (h : ∃ j, t + 1 ≤ off (j + 1)) →
      ea_labels t = lookupLabel t h := by
    intro t ht; exact dif_pos ht
  -- ea_labels t = stutter_label when t+1 is NOT in range
  have ea_labels_stutter : ∀ t, (¬∃ k, t + 1 ≤ off (k + 1)) →
      ea_labels t = stutter_label := by
    intro t h; exact dif_neg h
  -- off s ≤ t for the segment s containing t
  have seg_le : ∀ t (h : ∃ k, t ≤ off (k + 1)),
      off (lfindSmallest (fun k => t ≤ off (k + 1)) h.choose h.choose_spec).val ≤ t := by
    intro t h
    let s := lfindSmallest (fun k => t ≤ off (k + 1)) h.choose h.choose_spec
    show off s.val ≤ t
    by_cases hs0 : s.val = 0
    · simp [hs0, show off 0 = (0 : Nat) from rfl]
    · by_cases hle : off s.val ≤ t
      · exact hle
      · have hlt' : t < off s.val := by omega
        have hpred_lt : s.val - 1 < s.val := by omega
        have hpred_succ : s.val - 1 + 1 = s.val := by omega
        have hmin : ¬(t ≤ off (s.val - 1 + 1)) := s.property.2 (s.val - 1) hpred_lt
        rw [hpred_succ] at hmin
        omega
  -- t - off s ≤ (paths s).length
  have seg_bound : ∀ t (h : ∃ k, t ≤ off (k + 1)),
      t - off (lfindSmallest (fun k => t ≤ off (k + 1)) h.choose h.choose_spec).val ≤
      (paths (lfindSmallest (fun k => t ≤ off (k + 1)) h.choose h.choose_spec).val).length := by
    intro t h
    let s := lfindSmallest (fun k => t ≤ off (k + 1)) h.choose h.choose_spec
    show t - off s.val ≤ (paths s.val).length
    have hs_prop := s.property.1
    have : off (s.val + 1) = off s.val + (paths s.val).length := rfl
    omega
  -- findSmallest for t+1 ≥ findSmallest for t
  have seg_mono : ∀ t (h : ∃ k, t ≤ off (k + 1)) (h' : ∃ k, t + 1 ≤ off (k + 1)),
      (lfindSmallest (fun k => t ≤ off (k + 1)) h.choose h.choose_spec).val ≤
      (lfindSmallest (fun k => t + 1 ≤ off (k + 1)) h'.choose h'.choose_spec).val := by
    intro t h h'
    let s := lfindSmallest (fun k => t ≤ off (k + 1)) h.choose h.choose_spec
    let s' := lfindSmallest (fun k => t + 1 ≤ off (k + 1)) h'.choose h'.choose_spec
    show s.val ≤ s'.val
    by_cases hle : s.val ≤ s'.val
    · exact hle
    · exfalso
      have hlt' : s'.val < s.val := by omega
      have h1 : t + 1 ≤ off (s'.val + 1) := s'.property.1
      have h2 : t ≤ off (s'.val + 1) := by omega
      exact absurd h2 (s.property.2 s'.val hlt')
  refine ⟨⟨ea_states, ea_labels⟩, ?remap, ?step_or_stutter, ?labels_seg, ?labels_stutter⟩
  case remap =>
    intro k
    have hex : ∃ j, off k ≤ off (j + 1) := ⟨k, loffset_mono len k⟩
    show ea_states (off k) = states k
    rw [ea_states_val (off k) hex]
    show (paths (lfindSmallest (fun j => off k ≤ off (j + 1)) hex.choose hex.choose_spec).val).get_state
      (off k - off (lfindSmallest (fun j => off k ≤ off (j + 1)) hex.choose hex.choose_spec).val) = _
    let sb := lfindSmallest (fun j => off k ≤ off (j + 1)) hex.choose hex.choose_spec
    let s := sb.val
    have hs_prop : off k ≤ off (s + 1) := sb.property.1
    have hs_min : ∀ j, j < s → ¬(off k ≤ off (j + 1)) := sb.property.2
    change (paths s).get_state (off k - off s) = states k
    have hsk : s ≤ k := by
      by_cases h : s ≤ k
      · exact h
      · exfalso; exact hs_min k (by omega) (loffset_mono len k)
    by_cases heq_sk : s = k
    · have hsub : off k - off s = 0 := by
        have : off s = off k := by rw [heq_sk]
        omega
      rw [hsub, heq_sk]; exact LPath.get_state_zero _
    · have hlt : s < k := Nat.lt_of_le_of_ne hsk heq_sk
      have hoff_s1_k : off (s + 1) ≤ off k := loffset_mono_le len hlt
      have hoff_eq : off (s + 1) = off k := Nat.le_antisymm hoff_s1_k hs_prop
      have hlen_eq : off k - off s = (paths s).length := by
        have h1 : off s + (paths s).length = off k := by
          show loffset len s + (paths s).length = loffset len k
          rw [← show loffset len (s + 1) = loffset len s + len s from rfl]
          exact hoff_eq
        omega
      rw [hlen_eq, (paths s).get_state_length]
      exact states_eq_of_off_eq (s + 1) k (by omega) hoff_eq
  case step_or_stutter =>
    intro t
    by_cases hk1 : ∃ j, t + 1 ≤ off (j + 1)
    · have hk : ∃ j, t ≤ off (j + 1) := by
        obtain ⟨j, hj⟩ := hk1; exact ⟨j, by omega⟩
      let s := lfindSmallest (fun j => t ≤ off (j + 1)) hk.choose hk.choose_spec
      let s' := lfindSmallest (fun j => t + 1 ≤ off (j + 1)) hk1.choose hk1.choose_spec
      have hs_le_s' : s.val ≤ s'.val := seg_mono t hk hk1
      by_cases heq_ss' : s.val = s'.val
      · -- Same segment: consecutive step within one path
        -- s and s' are the same segment, so s = s' for both state and label lookups
        have hoff_le : off s.val ≤ t := seg_le t hk
        have hk_lt : t - off s.val < (paths s.val).length := by
          have hk1_bound' : t + 1 ≤ off (s.val + 1) := by
            have : s.val = s'.val := heq_ss'; rw [this]; exact s'.property.1
          have : off (s.val + 1) = off s.val + (paths s.val).length := rfl
          omega
        have hidx : t + 1 - off s'.val = (t - off s.val) + 1 := by
          have : off s'.val = off s.val := by rw [heq_ss']
          rw [this, Nat.succ_sub hoff_le]
        -- The label segment for t is also s (since t+1 ≤ off(s+1), findSmallest gives s)
        -- lookupLabel t hk1 uses lfindSmallest(t+1 ≤ off(k+1)) = s' = s
        have hst : ea_states t = (paths s.val).get_state (t - off s.val) :=
          ea_states_val t hk
        have hst1 : ea_states (t + 1) = (paths s'.val).get_state (t + 1 - off s'.val) :=
          ea_states_val (t + 1) hk1
        have hlt : ea_labels t = (paths s'.val).get_label (t - off s'.val) :=
          ea_labels_val t hk1
        simp only at ⊢
        rw [hst, hst1, hlt, ← heq_ss', Nat.succ_sub hoff_le]
        exact Or.inl ((paths s.val).get_step (t - off s.val) hk_lt)
      · -- Different segments: boundary between two paths
        have hlt_ss' : s.val < s'.val := Nat.lt_of_le_of_ne hs_le_s' heq_ss'
        have hk1_gt : ¬(t + 1 ≤ off (s.val + 1)) := by
          intro h_contra
          exact absurd h_contra (s'.property.2 s.val hlt_ss')
        have hk_eq : t = off (s.val + 1) := by
          have := s.property.1; omega
        have hget_k : (paths s.val).get_state (t - off s.val) =
            states (s.val + 1) := by
          have hlen_eq : t - off s.val = (paths s.val).length := by
            have : off (s.val + 1) = off s.val + (paths s.val).length := rfl
            omega
          rw [hlen_eq, (paths s.val).get_state_length]
        have hoff_s1_le_s' : off (s.val + 1) ≤ off s'.val :=
          loffset_mono_le len (Nat.succ_le_of_lt hlt_ss')
        have hoff_s'_le : off s'.val ≤ t + 1 := seg_le (t + 1) hk1
        have hoff_eq : off s'.val = off (s.val + 1) := by
          suffices h : off s'.val ≤ off (s.val + 1) from
            Nat.le_antisymm h hoff_s1_le_s'
          by_cases h_le : off s'.val ≤ off (s.val + 1)
          · exact h_le
          · exfalso
            have hgt : off (s.val + 1) < off s'.val := by omega
            have hoff_s' : off s'.val = off (s.val + 1) + 1 := by
              have h1 := hoff_s'_le; have h2 := hk_eq; omega
            have hs'_gt : s'.val > s.val + 1 := by
              by_cases hle : s'.val ≤ s.val + 1
              · have : s'.val = s.val + 1 := by omega
                rw [this] at hoff_s'; omega
              · omega
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
        rw [LPath.get_state_zero] at hstep
        -- Label at t uses segment s' (containing t+1), at index t - off s' = 0
        have hlbl_idx : t - off s'.val = 0 := by
          have := hoff_eq; have := hk_eq; omega
        have hst : ea_states t = (paths s.val).get_state (t - off s.val) :=
          ea_states_val t hk
        have hst1 : ea_states (t + 1) = (paths s'.val).get_state (t + 1 - off s'.val) :=
          ea_states_val (t + 1) hk1
        have hlt : ea_labels t = (paths s'.val).get_label (t - off s'.val) :=
          ea_labels_val t hk1
        simp only at ⊢
        rw [hst, hst1, hlt, hget_k, hidx_k1, hwit_s1_s', hlbl_idx]
        exact Or.inl hstep
    · -- t+1 NOT in range: stutter
      have hst := ea_states_stutter t hk1
      have hlt := ea_labels_stutter t hk1
      simp only at hst hlt ⊢
      exact Or.inr ⟨hst.symm, hlt⟩
  case labels_seg =>
    intro k i hi
    have hlen_eq : len k = (paths k).length := rfl
    have hrange : ∃ j, off k + i + 1 ≤ off (j + 1) :=
      ⟨k, by have : off (k + 1) = off k + len k := rfl; omega⟩
    show ea_labels (off k + i) = (paths k).get_label i
    rw [ea_labels_val (off k + i) hrange]
    let s := lfindSmallest (fun j => off k + i + 1 ≤ off (j + 1)) hrange.choose hrange.choose_spec
    show (paths s.val).get_label (off k + i - off s.val) = (paths k).get_label i
    have hs_eq : s.val = k := by
      apply Nat.le_antisymm
      · -- s.val ≤ k: k satisfies the predicate, so s ≤ k
        by_cases hle : s.val ≤ k
        · exact hle
        · exfalso
          have hlt : k < s.val := by omega
          have : off k + i + 1 ≤ off (k + 1) := by
            have : off (k + 1) = off k + len k := rfl; omega
          exact absurd this (s.property.2 k hlt)
      · -- k ≤ s.val: if s.val < k, the offset bound contradicts
        by_cases hle : k ≤ s.val
        · exact hle
        · exfalso
          have hlt : s.val < k := by omega
          have h1 : off (s.val + 1) ≤ off k := loffset_mono_le len hlt
          have h2 : off k + i + 1 ≤ off (s.val + 1) := s.property.1
          omega
    have hsub : off k + i - off k = i := by omega
    rw [hs_eq, hsub]
  case labels_stutter =>
    intro t ht
    show ea_labels t = stutter_label
    exact ea_labels_stutter t ht

/-- For a `ForwardSim`, every valid concrete execution has a corresponding
    valid abstract execution whose external label subsequence matches
    (via `label_map`) the concrete external label subsequence.

    The proof follows `SimulationRel.soundness` from `Refinement.lean`:
    1. Build abstract state witnesses at each concrete step boundary
    2. Build `LPath` segments between consecutive witnesses
    3. Flatten into a single abstract `Execution`
    4. Show validity and external label correspondence -/
theorem ForwardSim.external_subseq_correspondence
    {concrete : System S₁ L₁} {lab₁ : Labelling L₁}
    {abstract : System S₂ L₂} {lab₂ : Labelling L₂}
    (sim : ForwardSim concrete lab₁ abstract lab₂)
    -- External labels map correctly
    (h_label_ext : ∀ l₁, lab₁.is_external l₁ = true →
      lab₂.is_external (sim.label_map l₁) = true)
    -- label_map sends τ to τ (for external subsequence beyond last label)
    (h_map_tau : sim.label_map lab₁.tau = lab₂.tau)
    (e₁ : Execution S₁ L₁) (hv₁ : concrete.valid_exec e₁) :
    ∃ e₂ : Execution S₂ L₂, abstract.valid_exec_stutter lab₂ e₂ ∧
      externalSubseq lab₂ e₂.labels = sim.label_map ∘ externalSubseq lab₁ e₁.labels := by
  haveI : Inhabited L₂ := ⟨lab₂.tau⟩
  -- Build abstract witnesses and LPath segments
  let wit := sim.buildWitness e₁ hv₁
  let lpaths := sim.buildLPath e₁ hv₁
  -- Flatten into a single abstract execution (step-or-stutter)
  obtain ⟨e₂, hremap, hsos, hlabels_seg, hlabels_stutter⟩ :=
    flattenLPaths lab₂.tau (fun k => (wit k).val) lpaths
  refine ⟨e₂, ⟨?_, ?_⟩, ?_⟩
  · -- Init: e₂.states 0 = (wit 0).val, which is an abstract initial state
    have h0 : e₂.states 0 = (wit 0).val := hremap 0
    rw [h0]
    exact (sim.init_sim (e₁.states 0) hv₁.1).2.1
  · -- Steps: each position is step-or-stutter (directly from flattenLPaths)
    exact hsos
  · -- External subsequence correspondence
    -- Key lemma: for each external concrete step n₁, the corresponding
    -- position in e₂ has the matching external count and label.
    -- (The counting argument that relates externalCount in e₁ to externalCount
    -- in e₂ via the flattened path structure.)
    let off := loffset (fun k => (lpaths k).length)
    -- Core counting lemma: external count in e₂ at segment boundaries
    -- matches external count in e₁.
    -- At off k, the external labels seen in e₂ = external labels in e₁[0..k).
    -- Segment counting: external labels in segment m of e₂
    -- Segment label externality: for internal steps, all labels are internal
    have seg_all_internal : ∀ m,
        lab₁.is_internal (e₁.labels m) = true →
        ∀ i, i < (lpaths m).length →
          lab₂.is_external ((lpaths m).get_label i) = false := by
      intro m hint i hi
      have : lab₂.is_internal ((lpaths m).get_label i) = true :=
        sim.buildLPath_internal e₁ hv₁ m hint i hi
      simp [Labelling.is_external, this]
    -- External count through a segment: count increases by the number of
    -- external labels in that segment's path.
    have count_through_seg : ∀ m,
        externalCount lab₂ e₂.labels (off (m + 1)) =
          externalCount lab₂ e₂.labels (off m) +
            ((List.range (lpaths m).length).filter
              (fun i => lab₂.is_external ((lpaths m).get_label i))).length := by
      intro m
      -- off (m+1) = off m + len m; step through positions one at a time
      suffices h : ∀ j, j ≤ (lpaths m).length →
          externalCount lab₂ e₂.labels (off m + j) =
            externalCount lab₂ e₂.labels (off m) +
              ((List.range j).filter
                (fun i => lab₂.is_external ((lpaths m).get_label i))).length by
        have : off (m + 1) = off m + (lpaths m).length := rfl
        rw [this]; exact h _ (Nat.le_refl _)
      intro j hj; induction j with
      | zero => simp
      | succ j ih =>
        have hj_lt : j < (lpaths m).length := by omega
        have heq : off m + (j + 1) = (off m + j) + 1 := by omega
        rw [heq, externalCount_succ, hlabels_seg m j hj_lt, ih (by omega)]
        simp only [List.range_succ, List.filter_append, List.length_append,
                    List.filter_cons, List.filter_nil]
        split <;> simp <;> omega
    -- For internal steps: 0 external labels in segment
    have seg_internal_zero : ∀ m,
        lab₁.is_internal (e₁.labels m) = true →
        ((List.range (lpaths m).length).filter
          (fun i => lab₂.is_external ((lpaths m).get_label i))).length = 0 := by
      intro m hint
      have hempty : (List.range (lpaths m).length).filter
          (fun i => lab₂.is_external ((lpaths m).get_label i)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro i hi
        simp only [List.mem_range] at hi
        simp [seg_all_internal m hint i hi]
      simp [hempty]
    -- For external steps: exactly 1 external label in segment
    have seg_external_one : ∀ m,
        lab₁.is_external (e₁.labels m) = true →
        ((List.range (lpaths m).length).filter
          (fun i => lab₂.is_external ((lpaths m).get_label i))).length = 1 := by
      intro m hext
      obtain ⟨idx, hidx_lt, hidx_label, hidx_rest⟩ :=
        sim.buildLPath_external e₁ hv₁ m hext
      have h_idx_ext : lab₂.is_external ((lpaths m).get_label idx) = true := by
        rw [hidx_label]; exact h_label_ext _ hext
      have h_other_int : ∀ j, j < (lpaths m).length → j ≠ idx →
          lab₂.is_external ((lpaths m).get_label j) = false := by
        intro j hj hne
        have : lab₂.is_internal ((lpaths m).get_label j) = true := hidx_rest j hj hne
        simp [Labelling.is_external, this]
      -- Induction: exactly one element of range(len) passes the filter
      suffices ∀ n, idx < n → n ≤ (lpaths m).length →
          ((List.range n).filter
            (fun i => lab₂.is_external ((lpaths m).get_label i))).length = 1 from
        this _ hidx_lt (Nat.le_refl _)
      intro n; induction n with
      | zero => intro h; exact absurd h (Nat.not_lt_zero _)
      | succ n ih =>
        intro hidx_le hn_le
        simp only [List.range_succ, List.filter_append, List.length_append,
                    List.filter_cons, List.filter_nil]
        by_cases heq : idx = n
        · -- idx = n: this element passes; all earlier elements don't
          subst heq
          have hempty : (List.range idx).filter
              (fun i => lab₂.is_external ((lpaths m).get_label i)) = [] := by
            rw [List.filter_eq_nil_iff]
            intro j hj; simp only [List.mem_range] at hj
            simp only [Bool.not_eq_true]
            exact h_other_int j (by omega) (by omega)
          simp only [h_idx_ext, hempty, ite_true, List.length_nil,
                      List.length_cons, Nat.zero_add]
        · -- idx < n: this element doesn't pass; IH gives 1
          have hpn : lab₂.is_external ((lpaths m).get_label n) = false :=
            h_other_int n (by omega) (by omega)
          simp only [hpn]
          exact ih (by omega) (by omega)
    have count_at_boundary : ∀ m,
        externalCount lab₂ e₂.labels (off m) = externalCount lab₁ e₁.labels m := by
      intro m; induction m with
      | zero =>
        show externalCount lab₂ e₂.labels 0 = externalCount lab₁ e₁.labels 0
        simp [externalCount_zero]
      | succ m ih =>
        rw [externalCount_succ, count_through_seg m, ih]
        by_cases hint : lab₁.is_internal (e₁.labels m) = true
        · rw [seg_internal_zero m hint]
          simp [Labelling.is_external, hint]
        · have hext : lab₁.is_external (e₁.labels m) = true := by
            simp [Labelling.is_external, hint]
          rw [seg_external_one m hext]
          simp [hext]
    -- If all labels in a prefix of segment m are internal, external count is stable.
    have count_stable_internal : ∀ m bound,
        bound ≤ (lpaths m).length →
        (∀ j, j < bound → lab₂.is_internal ((lpaths m).get_label j) = true) →
        externalCount lab₂ e₂.labels (off m + bound) =
          externalCount lab₂ e₂.labels (off m) := by
      intro m bound hbound hint_all
      induction bound with
      | zero => simp
      | succ j ih =>
        have hj_lt : j < (lpaths m).length := by omega
        have heq : off m + (j + 1) = (off m + j) + 1 := by omega
        rw [heq, externalCount_succ, hlabels_seg m j hj_lt]
        simp [Labelling.is_external, hint_all j (by omega),
              ih (by omega) (fun i hi => hint_all i (by omega))]
    -- Every external label in e₂ is inside some segment (not at stutter positions)
    -- and comes from an external concrete step via label_map.
    have e2_ext_from_e1 : ∀ n₂,
        lab₂.is_external (e₂.labels n₂) = true →
        ∃ n₁, lab₁.is_external (e₁.labels n₁) = true ∧
          externalCount lab₂ e₂.labels n₂ = externalCount lab₁ e₁.labels n₁ ∧
          e₂.labels n₂ = sim.label_map (e₁.labels n₁) := by
      intro n₂ hext₂
      -- n₂ is not a stutter position (stutter = tau = internal)
      by_cases hrange : ∃ k, n₂ + 1 ≤ off (k + 1)
      · -- n₂ is in some segment. Find the segment m with off m ≤ n₂ < off(m+1).
        have ⟨m, hm_le, hm_lt⟩ : ∃ m, off m ≤ n₂ ∧ n₂ < off (m + 1) := by
          let s := lfindSmallest (fun k => n₂ + 1 ≤ off (k + 1)) hrange.choose hrange.choose_spec
          refine ⟨s.val, ?_, by have := s.property.1; omega⟩
          by_cases hs0 : s.val = 0
          · simp [hs0, show off 0 = 0 from rfl]
          · by_cases hle : off s.val ≤ n₂
            · exact hle
            · exfalso
              have h_pred : ¬(n₂ + 1 ≤ off ((s.val - 1) + 1)) :=
                s.property.2 (s.val - 1) (by omega)
              rw [show (s.val - 1) + 1 = s.val from by omega] at h_pred
              omega
        have hi_lt : n₂ - off m < (lpaths m).length := by
          have : off (m + 1) = off m + (lpaths m).length := rfl; omega
        have hlbl : e₂.labels n₂ = (lpaths m).get_label (n₂ - off m) := by
          have := hlabels_seg m (n₂ - off m) hi_lt
          rwa [show off m + (n₂ - off m) = n₂ from by omega] at this
        -- Step m must be external (if internal, all labels are internal)
        have hm_ext : lab₁.is_external (e₁.labels m) = true := by
          by_cases hint : lab₁.is_internal (e₁.labels m) = true
          · exfalso
            have := seg_all_internal m hint (n₂ - off m) hi_lt
            rw [← hlbl] at this; simp [this] at hext₂
          · simp [Labelling.is_external, hint]
        -- The label is label_map (e₁.labels m)
        obtain ⟨idx, hidx_lt, hidx_label, hidx_rest⟩ :=
          sim.buildLPath_external e₁ hv₁ m hm_ext
        -- n₂ - off m must equal idx (the unique external position)
        have hlen_eq : (sim.buildLPath e₁ hv₁ m).length = (lpaths m).length := rfl
        have h_is_idx : n₂ - off m = idx := by
          by_cases heq : n₂ - off m = idx
          · exact heq
          · exfalso
            have hint_j : lab₂.is_internal ((lpaths m).get_label (n₂ - off m)) = true :=
              hidx_rest (n₂ - off m) hi_lt heq
            rw [← hlbl] at hint_j
            simp [Labelling.is_external, hint_j] at hext₂
        refine ⟨m, hm_ext, ?_, ?_⟩
        · -- externalCount correspondence: all labels before idx are internal
          rw [show n₂ = off m + (n₂ - off m) from by omega,
              count_stable_internal m (n₂ - off m) (by omega)
                (fun j hj => hidx_rest j (by omega) (by omega)),
              count_at_boundary]
        · -- label correspondence
          rw [hlbl, h_is_idx, hidx_label]
      · -- Stutter position: label = tau = internal, contradicts hext₂
        exfalso
        have hdef := hlabels_stutter n₂ hrange
        have : lab₂.is_internal (e₂.labels n₂) = true := by rw [hdef]; exact lab₂.tau_internal
        simp [Labelling.is_external, this] at hext₂
    -- Forward direction: external label in e₁ → corresponding one in e₂
    have ext_corr : ∀ n₁ k,
        externalCount lab₁ e₁.labels n₁ = k →
        lab₁.is_external (e₁.labels n₁) = true →
        ∃ n₂, externalCount lab₂ e₂.labels n₂ = k ∧
          lab₂.is_external (e₂.labels n₂) = true ∧
          e₂.labels n₂ = sim.label_map (e₁.labels n₁) := by
      intro n₁ k hcount hext
      -- Get the external label position within the segment
      obtain ⟨idx, hidx_lt, hidx_label, hidx_rest⟩ :=
        sim.buildLPath_external e₁ hv₁ n₁ hext
      -- The position in e₂
      let n₂ := off n₁ + idx
      have hlen_eq : (sim.buildLPath e₁ hv₁ n₁).length = (lpaths n₁).length := rfl
      refine ⟨n₂, ?_, ?_, ?_⟩
      · -- externalCount: all labels before idx are internal
        rw [count_stable_internal n₁ idx (by omega)
              (fun j hj => hidx_rest j (by omega) (by omega)),
            count_at_boundary n₁, hcount]
      · -- lab₂.is_external (e₂.labels n₂) = true
        have : e₂.labels n₂ = (lpaths n₁).get_label idx :=
          hlabels_seg n₁ idx hidx_lt
        rw [this, hidx_label]; exact h_label_ext _ hext
      · -- e₂.labels n₂ = sim.label_map (e₁.labels n₁)
        have : e₂.labels n₂ = (lpaths n₁).get_label idx :=
          hlabels_seg n₁ idx hidx_lt
        rw [this, hidx_label]
    funext k; simp only [Function.comp]
    by_cases hk : ∃ n₁, externalCount lab₁ e₁.labels n₁ = k ∧
        lab₁.is_external (e₁.labels n₁) = true
    · obtain ⟨n₁, hcount₁, hext₁⟩ := hk
      obtain ⟨n₂, hcount₂, hext₂, hlbl⟩ := ext_corr n₁ k hcount₁ hext₁
      rw [externalSubseq_eq lab₂ e₂.labels hcount₂ hext₂,
          externalSubseq_eq lab₁ e₁.labels hcount₁ hext₁, hlbl]
    · rw [externalSubseq_default lab₁ e₁.labels k hk]
      have hk₂ : ¬∃ n₂, externalCount lab₂ e₂.labels n₂ = k ∧
          lab₂.is_external (e₂.labels n₂) = true := by
        intro ⟨n₂, hcount₂, hext₂⟩
        obtain ⟨n₁, hext₁, hcount_eq, _⟩ := e2_ext_from_e1 n₂ hext₂
        exact hk ⟨n₁, hcount_eq ▸ hcount₂, hext₁⟩
      rw [externalSubseq_default lab₂ e₂.labels k hk₂, h_map_tau]

/-- Transfer lemma: given matching external subsequences, an external label
    at some position in one execution has a counterpart in the other. -/
theorem external_label_transfer
    {L₁ : Type v₁} {L₂ : Type v₂}
    (lab₁ : Labelling L₁) (lab₂ : Labelling L₂)
    (f : L₁ → L₂)
    (labels₁ : Nat → L₁) (labels₂ : Nat → L₂)
    (hext_eq : externalSubseq lab₂ labels₂ = f ∘ externalSubseq lab₁ labels₁)
    (hf_ext : ∀ l₁, lab₁.is_external l₁ = true → lab₂.is_external (f l₁) = true)
    (hf_tau : f lab₁.tau = lab₂.tau)
    -- Forward: external label in labels₁ → f(label) at some position in labels₂
    : (∀ k, lab₁.is_external (labels₁ k) = true →
        ∃ m, labels₂ m = f (labels₁ k)) ∧
    -- Backward: external label in labels₂ that is in range of f →
    -- the preimage appears at some position in labels₁
      (∀ m, lab₂.is_external (labels₂ m) = true →
        ∃ k, f (labels₁ k) = labels₂ m ∧ lab₁.is_external (labels₁ k) = true) := by
  constructor
  · intro k hext
    have h1 := external_label_in_subseq lab₁ labels₁ hext
    have h2 : lab₂.is_external (externalSubseq lab₂ labels₂
        (externalCount lab₁ labels₁ k)) = true := by
      rw [hext_eq, Function.comp, h1]; exact hf_ext _ hext
    obtain ⟨m, hm, _, _⟩ := externalSubseq_source lab₂ labels₂ _ h2
    exact ⟨m, by rw [hm, hext_eq, Function.comp, h1]⟩
  · intro m hext
    have h1 := external_label_in_subseq lab₂ labels₂ hext
    have h2 : externalSubseq lab₂ labels₂ (externalCount lab₂ labels₂ m) =
        f (externalSubseq lab₁ labels₁ (externalCount lab₂ labels₂ m)) := by
      rw [hext_eq, Function.comp]
    rw [h1] at h2
    -- externalSubseq lab₁ labels₁ at this index gives some label l₁ with f l₁ = labels₂ m
    by_cases hext₁ : lab₁.is_external (externalSubseq lab₁ labels₁
        (externalCount lab₂ labels₂ m)) = true
    · obtain ⟨k, hk, hk_ext, _⟩ := externalSubseq_source lab₁ labels₁ _ hext₁
      exact ⟨k, by rw [hk]; exact h2.symm, hk_ext⟩
    · -- externalSubseq returns tau → f(tau) = lab₂.tau = labels₂ m
      -- But lab₂.tau is internal, contradicting labels₂ m external
      exfalso
      have hno : ¬∃ n, externalCount lab₁ labels₁ n = externalCount lab₂ labels₂ m ∧
          lab₁.is_external (labels₁ n) = true := by
        intro ⟨n, hn_count, hn_ext⟩
        exact absurd (externalSubseq_eq lab₁ labels₁ hn_count hn_ext ▸ hn_ext) hext₁
      have := externalSubseq_default lab₁ labels₁ _ hno
      rw [this, hf_tau] at h2
      have : lab₂.is_external lab₂.tau = false := by
        simp [Labelling.is_external, lab₂.tau_internal]
      rw [h2] at hext; rw [this] at hext; exact Bool.false_ne_true hext

/-- A `ForwardSim` preserves external trace properties.

    Given an `ExternalTraceProp` that holds for all stuttering-valid abstract
    executions (when applied to the abstract external subsequence), the
    corresponding mapped property holds for all valid concrete executions.

    The correspondence condition `h_subseq` asserts that for every valid
    concrete execution, there exists a stuttering-valid abstract execution
    whose external label subsequence equals `label_map` applied to the
    concrete external label subsequence. -/
theorem ForwardSim.preserves_external_trace_prop
    {concrete : System S₁ L₁} {lab₁ : Labelling L₁}
    {abstract : System S₂ L₂} {lab₂ : Labelling L₂}
    (sim : ForwardSim concrete lab₁ abstract lab₂)
    (φ : ExternalTraceProp L₂)
    (h_abs : ∀ e, abstract.valid_exec_stutter lab₂ e → φ (externalSubseq lab₂ e.labels))
    (h_subseq : ∀ e₁, concrete.valid_exec e₁ →
      ∃ e₂, abstract.valid_exec_stutter lab₂ e₂ ∧
        externalSubseq lab₂ e₂.labels = sim.label_map ∘ externalSubseq lab₁ e₁.labels)
    : concrete.satisfies ((φ.map sim.label_map).lift lab₁) := by
  intro e₁ hv₁
  obtain ⟨e₂, hv₂, heq⟩ := h_subseq e₁ hv₁
  show φ (sim.label_map ∘ externalSubseq lab₁ e₁.labels)
  rw [← heq]
  exact h_abs e₂ hv₂

/-- Convenience: combine `external_subseq_correspondence` with
    `preserves_external_trace_prop` to get a single-step transfer. -/
theorem ForwardSim.lift_external_trace_prop
    {concrete : System S₁ L₁} {lab₁ : Labelling L₁}
    {abstract : System S₂ L₂} {lab₂ : Labelling L₂}
    (sim : ForwardSim concrete lab₁ abstract lab₂)
    (h_label_ext : ∀ l₁, lab₁.is_external l₁ = true →
      lab₂.is_external (sim.label_map l₁) = true)
    (h_map_tau : sim.label_map lab₁.tau = lab₂.tau)
    (φ : ExternalTraceProp L₂)
    (h_abs : ∀ e, abstract.valid_exec_stutter lab₂ e → φ (externalSubseq lab₂ e.labels))
    : concrete.satisfies ((φ.map sim.label_map).lift lab₁) :=
  sim.preserves_external_trace_prop φ h_abs
    (fun e₁ hv₁ => sim.external_subseq_correspondence h_label_ext
      h_map_tau e₁ hv₁)

/-! ## Weak-Divergence Preservation (Gaspard CONCUR 2026, §6.2 + §6.4)

    A *witness* that an existing `ForwardSim` is weak-divergence-preserving
    under fair scheduling. The witness packages:

    * a well-founded `rank` on concrete states (the terminating relation `→`
      from Prop. 11);
    * a clause restricting `rank`'s discharge obligation to *fair* internal
      elisions (the §6.4 adaptation);
    * a fair-deadlock clause forcing the abstract to fairly weakly diverge
      at any concrete fair-deadlock state.

    From a witness, fair weak divergence transfers from concrete to abstract,
    and consequently `assumes_fair_wf`-style liveness properties transfer
    from abstract to concrete (see `transfers_satisfaction`).
-/

/-- Witness that a `ForwardSim` is weak-divergence-preserving under the
    given fair-label classifications on each side.

    **Refined design (Gaspard 2026-05-28):** the witness obligations are all
    direct (no disjunctions). Per Gaspard, this formulation is sound *and*
    complete for non-probabilistic programs. The "helpful directions"
    terminology used informally is implicit: the "helpful" labels are
    exactly those at which `rank` decreases (cases (a) and (b) below). -/
structure ForwardSim.WeakDivPreserving
    {S₁ : Type u₁} {L₁ : Type v₁} {S₂ : Type u₂} {L₂ : Type v₂}
    {concrete : System S₁ L₁} {lab₁ : Labelling L₁}
    {abstract : System S₂ L₂} {lab₂ : Labelling L₂}
    (sim : ForwardSim concrete lab₁ abstract lab₂)
    (fair_labels₁ : S₁ → L₁ → Prop)
    (fair_labels₂ : S₂ → L₂ → Prop)
    where
  /-- Well-founded "rank" on concrete states (Prop. 11's terminating relation). -/
  rank : S₁ → S₁ → Prop
  rank_wf : WellFounded rank
  /-- Unfair internal concrete steps cannot *grow* the rank. (They may
      decrease it or leave it unchanged.) Bridges unfair-prefix walks in
      soundness. -/
  rank_non_increasing :
    ∀ s l s', concrete.step s l s' →
      lab₁.is_internal l = true → ¬ fair_labels₁ s l →
      s' = s ∨ rank s' s
  /-- **Gaspard's clause (a)** + skip constraint: when the abstract responds
      to a fair internal concrete step with a skip transition (empty
      `InternalStar`), the concrete label is "helpful" — equivalently, the
      rank strictly decreases. -/
  rank_decreases_on_fair_elision :
    ∀ s₁ l₁ s₁' s₂
      (hreach : Reachable concrete s₁)
      (hR : sim.R s₁ s₂)
      (hint : lab₁.is_internal l₁ = true)
      (hfair : fair_labels₁ s₁ l₁)
      (hstep : concrete.step s₁ l₁ s₁'),
      (sim.step_internal s₁ l₁ s₁' s₂ hreach hR hint hstep).2.1.IsEmpty →
      rank s₁' s₁
  /-- **Gaspard's clause (b)**: when the abstract responds to a fair
      internal concrete step with a non-skip whose `InternalStar` contains
      an *unfair* label (per `fair_labels₂`), the rank strictly decreases.
      (Stated as the contrapositive of "no rank decrease ⇒ AllFair".) -/
  rank_decreases_on_unfair_abstract :
    ∀ s₁ l₁ s₁' s₂
      (hreach : Reachable concrete s₁)
      (hR : sim.R s₁ s₂)
      (hint : lab₁.is_internal l₁ = true)
      (hfair : fair_labels₁ s₁ l₁)
      (hstep : concrete.step s₁ l₁ s₁'),
      ¬ (sim.step_internal s₁ l₁ s₁' s₂ hreach hR hint hstep).2.1.IsEmpty →
      ¬ (sim.step_internal s₁ l₁ s₁' s₂ hreach hR hint hstep).2.1.AllFair
          fair_labels₂ →
      rank s₁' s₁
  /-- Fair-deadlock clause: a concrete fair-deadlock forces an abstract one. -/
  fair_deadlock_diverges :
    ∀ s₁ s₂, Reachable concrete s₁ → sim.R s₁ s₂ →
      FairDeadlock concrete fair_labels₁ s₁ →
      FairlyWeaklyDiverges abstract lab₂ fair_labels₂ s₂

namespace ForwardSim

variable {S₁ : Type u₁} {L₁ : Type v₁} {S₂ : Type u₂} {L₂ : Type v₂}
variable {concrete : System S₁ L₁} {lab₁ : Labelling L₁}
variable {abstract : System S₂ L₂} {lab₂ : Labelling L₂}

/-- Walk an `InternalStar` of concrete internal steps through the simulation:
    each concrete internal step produces an abstract `InternalStar`, and these
    compose into a single abstract `InternalStar` whose target is related to
    the concrete target by `sim.R`. -/
def walk_internal_star
    (sim : ForwardSim concrete lab₁ abstract lab₂)
    {s₁ s₁' : S₁} {s₂ : S₂}
    (hreach : Reachable concrete s₁)
    (hR : sim.R s₁ s₂)
    (hstar : InternalStar concrete lab₁ s₁ s₁') :
    Σ' s₂', InternalStar abstract lab₂ s₂ s₂' ×' sim.R s₁' s₂' :=
  match hstar with
  | .refl => ⟨s₂, .refl, hR⟩
  | .step (l := l) (s' := s_mid) hint hstep rest =>
      let mid := sim.step_internal s₁ l s_mid s₂ hreach hR hint hstep
      let hreach_mid : Reachable concrete s_mid := .step hreach hstep
      let tail := sim.walk_internal_star hreach_mid mid.2.2 rest
      ⟨tail.1, mid.2.1.trans tail.2.1, tail.2.2⟩

end ForwardSim

namespace ForwardSim.WeakDivPreserving

variable {S₁ : Type u₁} {L₁ : Type v₁} {S₂ : Type u₂} {L₂ : Type v₂}
variable {concrete : System S₁ L₁} {lab₁ : Labelling L₁}
variable {abstract : System S₂ L₂} {lab₂ : Labelling L₂}
variable {fair_labels₁ : S₁ → L₁ → Prop} {fair_labels₂ : S₂ → L₂ → Prop}

/-- **Soundness** (Gaspard Prop. 11 forward direction, §6.4 fair adaptation):
    a `WeakDivPreserving` witness lifts fairly weak divergence from concrete
    to abstract.

    The witness's new fields (`rank_non_increasing` and
    `fair_non_elision_progress`, added in the design refinement of
    2026-05-28) replace the external `h_abs_fair` hypothesis that earlier
    versions of this theorem required.

    The deadlock case is proven by walking the τ-path through the
    simulation and applying `fair_deadlock_diverges`, then lifting back
    with `FairlyWeaklyDiverges.lift`.

    The fair-divergence case (Case A) is partially proven via well-founded
    induction on `wd.rank`. Two inner sorries remain:
      * the `k₀ > 0` sub-case of rank-decrease, now solvable using
        `rank_non_increasing` to bridge the unfair prefix;
      * Case (ii) — building an infinite fair abstract execution from a
        sequence of non-empty `walk_internal_star` outputs, now solvable
        using `fair_non_elision_progress` to guarantee each contribution
        is `AllFair`. Mechanically intricate; needs new
        `Execution`-from-`InternalStar`-sequence machinery in `Trace.lean`. -/
theorem preserves_fair_weak_divergence
    {sim : ForwardSim concrete lab₁ abstract lab₂}
    (wd : sim.WeakDivPreserving fair_labels₁ fair_labels₂)
    {s₁ : S₁} {s₂ : S₂}
    (hreach : Reachable concrete s₁) (hR : sim.R s₁ s₂)
    (hdiv : FairlyWeaklyDiverges concrete lab₁ fair_labels₁ s₁) :
    FairlyWeaklyDiverges abstract lab₂ fair_labels₂ s₂ := by
  rcases hdiv with hfair_div | ⟨s_dead, ⟨hpath⟩, hfd⟩
  · -- Fair-divergence case (Case A).
    --
    -- We do strong well-founded induction on `wd.rank` over the concrete
    -- start state `s₁`, generalising over `s₂`, `hreach`, `hR`, and the
    -- fair-divergence witness.  At each step we walk the concrete
    -- fair-divergence forward to its *first* fair index `k₀ ≥ 0`, push
    -- everything through `sim.step_internal` (via `walk_internal_star`),
    -- then case-split on whether the abstract `InternalStar` produced by
    -- that fair step is empty (elided) or non-empty (real progress).
    --
    -- Case (i)  [elided]:  the witness's `fair_elision_progress` clause
    --                      gives either a rank-decrease (recurse via the
    --                      WF IH) or direct abstract fair-weak-divergence
    --                      at the abstract image — lifted back through
    --                      the composed `InternalStar`.
    -- Case (ii) [non-empty]: combined with `h_abs_fair`, the fair concrete
    --                        step produces an `AllFair` abstract path of
    --                        length ≥ 1.  Iterating this case produces an
    --                        infinite fair abstract execution.
    --
    -- The full Case (ii) construction (build the infinite abstract execution
    -- from a sequence of non-empty `InternalStar`s) is structurally heavy and
    -- is left as a single inner `sorry` below (see `case_ii` block) with a
    -- detailed comment.  Case (i) is proved in full modulo this.
    --
    -- We strengthen to a generic well-founded recursion claim over s₁.
    suffices hWF :
        ∀ s₁ : S₁, Reachable concrete s₁ →
          ∀ s₂ : S₂, sim.R s₁ s₂ →
          FairDiverges concrete lab₁ fair_labels₁ s₁ →
          FairlyWeaklyDiverges abstract lab₂ fair_labels₂ s₂ from
      hWF s₁ hreach s₂ hR hfair_div
    intro s₁ hreach
    induction s₁ using wd.rank_wf.induction with
    | _ s₁ ih_rank =>
      intro s₂ hR hfair_div
      obtain ⟨e₁, he₁0, hstep_int, hcofair⟩ := hfair_div
      -- Pick the LEAST fair index `k₀ ≥ 0` in e₁ via `Nat.find`. Minimality
      -- (`hno_fair_before`) is what lets `rank_non_increasing` bridge the
      -- unfair prefix in the k₀ > 0 sub-case below.
      have h_ex_fair : ∃ k, fair_labels₁ (e₁.states k) (e₁.labels k) := by
        obtain ⟨k, _, hk⟩ := hcofair 0; exact ⟨k, hk⟩
      obtain ⟨k₀, hfair_k₀, hno_fair_before⟩ :
          ∃ k₀, fair_labels₁ (e₁.states k₀) (e₁.labels k₀)
              ∧ ∀ i, i < k₀ → ¬ fair_labels₁ (e₁.states i) (e₁.labels i) :=
        ⟨Nat.find h_ex_fair, Nat.find_spec h_ex_fair,
         fun _ hi => Nat.find_min h_ex_fair hi⟩
      -- Walk e₁ from index 0 to index k₀ through `sim.step_internal`.
      -- Build the InternalStar of concrete internal steps from s₁ to e₁.states k₀.
      have hpath_to_k₀ : InternalStar concrete lab₁ s₁ (e₁.states k₀) := by
        have base : ∀ k, InternalStar concrete lab₁ (e₁.states 0) (e₁.states k) := by
          intro k
          induction k with
          | zero => exact .refl
          | succ k ih =>
            exact ih.trans (.single (hstep_int k).2 (hstep_int k).1)
        have := base k₀
        rw [he₁0] at this
        exact this
      -- Push the path through the simulation.
      let walk := sim.walk_internal_star hreach hR hpath_to_k₀
      -- Reachability of e₁.states k₀.
      have hreach_k₀ : Reachable concrete (e₁.states k₀) :=
        hpath_to_k₀.toStar.reachable hreach
      -- At position k₀ we have a fair internal concrete step.
      have hstep_k₀ : concrete.step (e₁.states k₀) (e₁.labels k₀) (e₁.states (k₀ + 1)) :=
        (hstep_int k₀).1
      have hint_k₀ : lab₁.is_internal (e₁.labels k₀) = true := (hstep_int k₀).2
      -- Apply step_internal at position k₀ to get the abstract InternalStar.
      let mid := sim.step_internal (e₁.states k₀) (e₁.labels k₀) (e₁.states (k₀ + 1))
                  walk.1 hreach_k₀ walk.2.2 hint_k₀ hstep_k₀
      have hreach_k₀_succ : Reachable concrete (e₁.states (k₀ + 1)) :=
        .step hreach_k₀ hstep_k₀
      -- The tail of e₁ is itself a fair divergence at e₁.states (k₀ + 1).
      have htail_div : FairDiverges concrete lab₁ fair_labels₁ (e₁.states (k₀ + 1)) := by
        refine ⟨e₁.drop (k₀ + 1), ?_, ?_, ?_⟩
        · -- (drop (k₀+1) e₁).states 0 = e₁.states (k₀+1)
          show e₁.states (0 + (k₀ + 1)) = e₁.states (k₀ + 1)
          congr 1; omega
        · intro k
          have hk := hstep_int (k + (k₀ + 1))
          have heq1 : (Execution.drop (k₀ + 1) e₁).states k = e₁.states (k + (k₀ + 1)) := rfl
          have heq2 : (Execution.drop (k₀ + 1) e₁).labels k = e₁.labels (k + (k₀ + 1)) := rfl
          have heq3 : (Execution.drop (k₀ + 1) e₁).states (k + 1)
                       = e₁.states (k + (k₀ + 1) + 1) := by
            show e₁.states (k + 1 + (k₀ + 1)) = e₁.states (k + (k₀ + 1) + 1)
            congr 1; omega
          rw [heq1, heq2, heq3]
          exact hk
        · intro N
          obtain ⟨k, hkN, hfair_k⟩ := hcofair (N + (k₀ + 1))
          refine ⟨k - (k₀ + 1), by omega, ?_⟩
          have heqs : (Execution.drop (k₀ + 1) e₁).states (k - (k₀ + 1)) = e₁.states k := by
            show e₁.states ((k - (k₀ + 1)) + (k₀ + 1)) = e₁.states k
            congr 1; omega
          have heql : (Execution.drop (k₀ + 1) e₁).labels (k - (k₀ + 1)) = e₁.labels k := by
            show e₁.labels ((k - (k₀ + 1)) + (k₀ + 1)) = e₁.labels k
            congr 1; omega
          rw [heqs, heql]; exact hfair_k
      -- Classical case-split on whether the abstract step at k₀ is empty.
      by_cases h_empty : mid.2.1.IsEmpty
      · -- Case (i): elided.  Apply `rank_decreases_on_fair_elision`.
        -- Under Gaspard's refined formulation, the disjunctive
        -- `rank ∨ FairlyWeaklyDiverges` is replaced by direct `rank`
        -- decrease: a fair skip MUST be helpful (decrease rank).
        have hrank : wd.rank (e₁.states (k₀ + 1)) (e₁.states k₀) :=
          wd.rank_decreases_on_fair_elision (e₁.states k₀) (e₁.labels k₀)
            (e₁.states (k₀ + 1)) walk.1 hreach_k₀ walk.2.2 hint_k₀
            hfair_k₀ hstep_k₀ h_empty
        -- Unified Case-(i) handler covering both `k₀ = 0` and `k₀ > 0`.
        --
        -- Helper `transfer_at_pivot m _ hrec`: given an index `m ≥ 1` along
        -- the concrete fair-divergence with `wd.rank (e₁.states m) s₁`,
        -- lift fair divergence at `e₁.states m` to abstract divergence at
        -- `s₂` via the WF IH `ih_rank` (walking the `m`-prefix through the
        -- simulation as an `InternalStar`, then lifting back).
        have transfer_at_pivot :
            ∀ m, 0 < m → wd.rank (e₁.states m) s₁ →
              FairlyWeaklyDiverges abstract lab₂ fair_labels₂ s₂ := by
          intro m _ hrec
          have hpath_m : InternalStar concrete lab₁ s₁ (e₁.states m) := by
            have base : ∀ k, InternalStar concrete lab₁ (e₁.states 0) (e₁.states k) := by
              intro k
              induction k with
              | zero => exact .refl
              | succ k ih =>
                exact ih.trans (.single (hstep_int k).2 (hstep_int k).1)
            have := base m
            rw [he₁0] at this; exact this
          let walk_m := sim.walk_internal_star hreach hR hpath_m
          have hreach_m : Reachable concrete (e₁.states m) :=
            hpath_m.toStar.reachable hreach
          have htail_div_m : FairDiverges concrete lab₁ fair_labels₁
              (e₁.states m) := by
            refine ⟨e₁.drop m, ?_, ?_, ?_⟩
            · show e₁.states (0 + m) = e₁.states m
              congr 1; omega
            · intro k
              have hk := hstep_int (k + m)
              have heq1 : (Execution.drop m e₁).states k = e₁.states (k + m) := rfl
              have heq2 : (Execution.drop m e₁).labels k = e₁.labels (k + m) := rfl
              have heq3 : (Execution.drop m e₁).states (k + 1)
                           = e₁.states (k + m + 1) := by
                show e₁.states (k + 1 + m) = e₁.states (k + m + 1)
                congr 1; omega
              rw [heq1, heq2, heq3]; exact hk
            · intro N
              obtain ⟨k, hkN, hfair_k⟩ := hcofair (N + m)
              refine ⟨k - m, by omega, ?_⟩
              have heqs : (Execution.drop m e₁).states (k - m) = e₁.states k := by
                show e₁.states ((k - m) + m) = e₁.states k
                congr 1; omega
              have heql : (Execution.drop m e₁).labels (k - m) = e₁.labels k := by
                show e₁.labels ((k - m) + m) = e₁.labels k
                congr 1; omega
              rw [heqs, heql]; exact hfair_k
          have habs_at_walk_m : FairlyWeaklyDiverges abstract lab₂ fair_labels₂
              walk_m.1 :=
            ih_rank (e₁.states m) hrec hreach_m walk_m.1 walk_m.2.2 htail_div_m
          exact FairlyWeaklyDiverges.lift walk_m.2.1 habs_at_walk_m
        -- Case-split on whether any unfair prefix step strictly decreases rank.
        -- If so, take the LEAST such index `j₀`; by minimality + the
        -- equality clause of `rank_non_increasing`, every prior step is an
        -- equality, so `e₁.states j₀ = s₁` and `rank (e₁.states (j₀+1)) s₁`.
        -- Otherwise every prefix step is an equality (vacuous when `k₀ = 0`),
        -- so `e₁.states k₀ = s₁`, and the elision rank from `hrank` gives
        -- `rank (e₁.states (k₀+1)) s₁`.
        by_cases hQ : ∃ j, j < k₀ ∧ wd.rank (e₁.states (j + 1)) (e₁.states j)
        · -- Strict-rank step somewhere in the prefix.  Pivot at `j₀ + 1`.
          let j₀ : Nat := Nat.find hQ
          have hj₀_lt : j₀ < k₀ := (Nat.find_spec hQ).1
          have hj₀_rank : wd.rank (e₁.states (j₀ + 1)) (e₁.states j₀) :=
            (Nat.find_spec hQ).2
          have hj₀_min : ∀ i, i < j₀ →
              ¬ (i < k₀ ∧ wd.rank (e₁.states (i + 1)) (e₁.states i)) :=
            fun i hi => Nat.find_min hQ hi
          have h_prefix_eq : ∀ i, i < j₀ → e₁.states (i + 1) = e₁.states i := by
            intro i hi
            have hi_lt_k₀ : i < k₀ := lt_trans hi hj₀_lt
            have hunfair := hno_fair_before i hi_lt_k₀
            rcases wd.rank_non_increasing (e₁.states i) (e₁.labels i)
                    (e₁.states (i + 1)) (hstep_int i).1 (hstep_int i).2 hunfair
              with heq | hr
            · exact heq
            · exact absurd ⟨hi_lt_k₀, hr⟩ (hj₀_min i hi)
          have hj₀_eq_s₁ : e₁.states j₀ = s₁ := by
            have huniv : ∀ i, i ≤ j₀ → e₁.states i = e₁.states 0 := by
              intro i
              induction i with
              | zero => intro _; rfl
              | succ i ih =>
                intro hi
                have hi_lt : i < j₀ := by omega
                have hi_le : i ≤ j₀ := Nat.le_of_lt hi_lt
                rw [h_prefix_eq i hi_lt, ih hi_le]
            rw [huniv j₀ (Nat.le_refl _), he₁0]
          have hrec : wd.rank (e₁.states (j₀ + 1)) s₁ := hj₀_eq_s₁ ▸ hj₀_rank
          exact transfer_at_pivot (j₀ + 1) (Nat.succ_pos _) hrec
        · -- All unfair prefix steps are equalities (vacuous if `k₀ = 0`).
          push_neg at hQ
          have h_prefix_eq : ∀ i, i < k₀ → e₁.states (i + 1) = e₁.states i := by
            intro i hi
            have hunfair := hno_fair_before i hi
            rcases wd.rank_non_increasing (e₁.states i) (e₁.labels i)
                    (e₁.states (i + 1)) (hstep_int i).1 (hstep_int i).2 hunfair
              with heq | hr
            · exact heq
            · exact absurd hr (hQ i hi)
          have hek0_eq_s₁ : e₁.states k₀ = s₁ := by
            have huniv : ∀ i, i ≤ k₀ → e₁.states i = e₁.states 0 := by
              intro i
              induction i with
              | zero => intro _; rfl
              | succ i ih =>
                intro hi
                have hi_lt : i < k₀ := by omega
                have hi_le : i ≤ k₀ := Nat.le_of_lt hi_lt
                rw [h_prefix_eq i hi_lt, ih hi_le]
            rw [huniv k₀ (Nat.le_refl _), he₁0]
          have hrec : wd.rank (e₁.states (k₀ + 1)) s₁ := hek0_eq_s₁ ▸ hrank
          exact transfer_at_pivot (k₀ + 1) (Nat.succ_pos _) hrec
      · -- Case (ii): non-empty abstract step.  By `h_abs_fair`, mid.2.1 is
        -- AllFair on the abstract side and has length ≥ 1.  Iterating this
        -- argument cofinally many times produces a fair abstract divergence.
        --
        -- Detailed construction sketch (left as inner sorry):
        --   * Define `s₂_seq : ℕ → S₂` and `path_seq : ℕ → InternalStar abstract …`
        --     by recursion using `walk_internal_star` between consecutive fair
        --     concrete indices (k₀ < k₁ < k₂ < ...).
        --   * At each fair index k_i, apply `sim.step_internal` to get a
        --     non-empty AllFair abstract InternalStar (by `h_abs_fair`, since
        --     we are at a fair label).  If at any of these the InternalStar
        --     becomes empty, defer to Case (i) at that index using `ih_rank`.
        --   * Concatenate all abstract InternalStars into one infinite
        --     execution. Fairness follows because each non-empty AllFair
        --     contributes ≥ 1 fair abstract label, infinitely often.
        --   * The resulting witness is `FairDiverges abstract lab₂ fair_labels₂ walk.1`
        --     lifted back to `s₂` via `FairlyWeaklyDiverges.lift walk.2.1`.
        --
        -- This construction is mechanically intricate (~200 LOC) and uses
        -- Classical.choice + Execution-from-InternalStar-sequence machinery
        -- that does not currently exist as a helper.  Deferred.
        sorry
  · -- Deadlock case: walk the τ-path through the simulation, then apply
    -- the witness's `fair_deadlock_diverges`, then lift back.
    let walk := sim.walk_internal_star hreach hR hpath
    have hdead : FairlyWeaklyDiverges abstract lab₂ fair_labels₂ walk.1 := by
      apply wd.fair_deadlock_diverges s_dead walk.1
      · -- Reachable concrete s_dead
        exact hpath.toStar.reachable hreach
      · -- sim.R s_dead walk.1
        exact walk.2.2
      · exact hfd
    exact FairlyWeaklyDiverges.lift walk.2.1 hdead

/-- **Headline transfer.** A property provable on the abstract under
    fair-WF assumptions (via `assumes_fair_wf`) transfers to the concrete
    under the corresponding fair-WF assumptions.

    **Index-map design** (per design call): because the abstract execution
    constructed by flattening can include stutter steps (when the abstract
    elides concrete internal moves), concrete and abstract index spaces do
    not align 1-to-1. Instead, the client provides:

    * `h_prop_transfer`: takes a strictly monotonic index map `idx` such
      that the concrete state at `k` corresponds to the abstract state at
      `idx k` (via `sim.R`). The map starts at `idx 0 = 0`. This is the
      same shape `external_subseq_correspondence` already uses internally
      (mapping concrete external indices to abstract external indices).

    * `h_fair_compat`: concrete fair labels map to abstract fair labels
      via `sim.label_map`. (The witness's `fair_non_elision_progress`
      replaces the earlier external `h_abs_fair` hypothesis.) -/
theorem transfers_satisfaction
    {sim : ForwardSim concrete lab₁ abstract lab₂}
    (wd : sim.WeakDivPreserving fair_labels₁ fair_labels₂)
    (h_fair_compat :
      ∀ s₁ l₁ s₂, sim.R s₁ s₂ → fair_labels₁ s₁ l₁ →
        fair_labels₂ s₂ (sim.label_map l₁))
    (φ_abs : TraceProp S₂ L₂) (φ_con : TraceProp S₁ L₁)
    (h_prop_transfer :
      ∀ (e₁ : Execution S₁ L₁) (e₂ : Execution S₂ L₂) (idx : Nat → Nat),
        concrete.valid_exec e₁ → abstract.valid_exec e₂ →
        (∀ k, idx k < idx (k + 1)) →       -- strict monotonicity
        idx 0 = 0 →
        (∀ k, sim.R (e₁.states k) (e₂.states (idx k))) →
        φ_abs e₂ 0 → φ_con e₁ 0)
    (h_abs :
      abstract.satisfies (assumes_fair_wf abstract fair_labels₂ φ_abs)) :
    concrete.satisfies (assumes_fair_wf concrete fair_labels₁ φ_con) := by
  sorry

-- `compose_with_compatible` (Gaspard Lemma 12) lives in `Composition.lean`
-- because its statement depends on `parallel_forward_sim`.

end ForwardSim.WeakDivPreserving

end LTS
