import Leslie.Action

/-! ## Hierarchical Protocol Composition

    This file defines protocol composition where a main protocol **calls**
    a sub-protocol. The sub-protocol runs as part of the composed system,
    and its safety properties lift automatically to the composed level.

    The key abstraction: a **protocol call** is a state projection `proj`
    from the composed state to the sub-protocol's state, such that
    the projection is a refinement mapping (with stuttering).

    This means:
    - The sub-protocol's state is embedded in the composed state
    - Every composed step either corresponds to a sub-protocol step
      (under projection) or leaves the sub-state unchanged
    - Any safety property of the sub-protocol holds in the composed system

    Composition is hierarchical: if protocol B calls protocol C, and
    protocol A calls protocol B, then A's composed system also satisfies
    C's properties (via `refines_via_trans`).

    ### Usage

    1. Define the composed `ActionSpec` with state `σ` and actions `ι`
    2. Define the sub-protocol `ActionSpec` with state `σ_sub` and actions `ι_sub`
    3. Provide a projection `proj : σ → σ_sub`
    4. Build a `ProtocolCall` by proving init and step preservation
    5. Use `ProtocolCall.lift_invariant` to import sub-protocol invariants
    6. Chain with `ProtocolCall.compose` for hierarchical composition
-/

open Classical

namespace TLA

/-! ### Protocol Call -/

/-- A protocol call: the composed protocol's state projects onto the
    sub-protocol's state via `proj`, forming a refinement mapping.

    - `init_proj`: the initial state projects to a valid sub-protocol initial state
    - `step_proj`: every step of the composed protocol either maps to a
      sub-protocol step or leaves the sub-state unchanged (stutter) -/
structure ProtocolCall (σ : Type u) (σ_sub : Type v)
    (ι : Type w) (ι_sub : Type x) where
  /-- The composed protocol (main + sub interleaved). -/
  composed : ActionSpec σ ι
  /-- The sub-protocol's specification. -/
  sub : ActionSpec σ_sub ι_sub
  /-- State projection from composed to sub-protocol. -/
  proj : σ → σ_sub
  /-- Init maps to sub-init. -/
  init_proj : ∀ s, composed.init s → sub.init (proj s)
  /-- Every composed step either maps to a sub step or stutters on sub-state. -/
  step_proj : ∀ s s', composed.next s s' →
    sub.next (proj s) (proj s') ∨ proj s = proj s'

/-- The projection is a refinement mapping from composed safety to
    sub safety (with stuttering). -/
theorem ProtocolCall.refines (pc : ProtocolCall σ σ_sub ι ι_sub) :
    refines_via pc.proj pc.composed.safety pc.sub.toSpec.safety_stutter := by
  apply refinement_mapping_stutter pc.composed.toSpec pc.sub.toSpec
  · exact pc.init_proj
  · intro s s' hnext
    exact pc.step_proj s s' hnext

/-! ### Lifting Properties -/

/-- Lift an invariant from the sub-protocol to the composed protocol.
    If the sub-protocol guarantees `□P` under its safety, the composed
    protocol guarantees `□(P ∘ proj)` under its safety. -/
theorem ProtocolCall.lift_invariant (pc : ProtocolCall σ σ_sub ι ι_sub)
    {P : σ_sub → Prop}
    (hP : pred_implies pc.sub.toSpec.safety_stutter [tlafml| □ ⌜ P ⌝]) :
    pred_implies pc.composed.safety [tlafml| □ ⌜ fun s => P (pc.proj s) ⌝] := by
  intro e hcomp k
  have hsub := pc.refines e hcomp
  have hall := hP (exec.map pc.proj e) hsub k
  simp only [state_pred, exec.drop, exec.map] at hall ⊢
  exact hall

/-- Lift an inductive invariant (proved by init + step preservation).
    This is the most common case: the sub-protocol's invariant is proved
    by showing init establishes it and every step preserves it.
    Stutter steps trivially preserve state predicates. -/
theorem ProtocolCall.lift_inductive_invariant (pc : ProtocolCall σ σ_sub ι ι_sub)
    {P : σ_sub → Prop}
    (hinit : ∀ s, pc.sub.init s → P s)
    (hstep : ∀ s s', pc.sub.next s s' → P s → P s') :
    pred_implies pc.composed.safety [tlafml| □ ⌜ fun s => P (pc.proj s) ⌝] := by
  apply pc.lift_invariant
  -- Prove □P under safety_stutter
  intro e ⟨hinit_e, hnext_e⟩
  -- The init gives P at step 0
  have hP0 : P (e 0) := by
    have := hinit_e
    simp [state_pred] at this
    exact hinit _ this
  -- Each step either preserves P (sub step) or stutters (P trivially preserved)
  intro k
  simp [state_pred, exec.drop] at *
  induction k with
  | zero => exact hP0
  | succ k' ih =>
    have hstep_k := hnext_e k'
    simp [action_pred, exec.drop] at hstep_k
    rw [Nat.add_comm] at hstep_k
    rcases hstep_k with hreal | hstutter
    · exact hstep _ _ hreal ih
    · rw [← hstutter] ; exact ih

/-- Lift a consequence of an inductive invariant. If `I` is inductive
    (init + step) and `P` follows from `I`, then `□(P ∘ proj)` holds.
    This avoids needing `P` itself to be inductive. -/
theorem ProtocolCall.lift_consequence (pc : ProtocolCall σ σ_sub ι ι_sub)
    {I P : σ_sub → Prop}
    (hinit : ∀ s, pc.sub.init s → I s)
    (hstep : ∀ s s', pc.sub.next s s' → I s → I s')
    (hcons : ∀ s, I s → P s) :
    pred_implies pc.composed.safety [tlafml| □ ⌜ fun s => P (pc.proj s) ⌝] := by
  intro e hsafety k
  have hinv := pc.lift_inductive_invariant hinit hstep e hsafety k
  simp only [state_pred, exec.drop] at hinv ⊢
  exact hcons _ hinv

/-! ### Hierarchical Composition -/

/-- Compose two protocol calls: if A calls B and B calls C,
    then A transitively calls C.
    Requires compatibility: A's sub-protocol is B's composed protocol. -/
def ProtocolCall.compose
    (ab : ProtocolCall σ σ_B ι_A ι_B)
    (bc : ProtocolCall σ_B σ_C ι_B ι_C)
    (hcompat : ab.sub = bc.composed) :
    ProtocolCall σ σ_C ι_A ι_C where
  composed := ab.composed
  sub := bc.sub
  proj := bc.proj ∘ ab.proj
  init_proj := fun s hinit =>
    bc.init_proj (ab.proj s) (hcompat ▸ ab.init_proj s hinit)
  step_proj := fun s s' hstep => by
    rcases ab.step_proj s s' hstep with hab | hab_stutter
    · -- A step maps to a B step; check if B step maps to C step
      rcases bc.step_proj _ _ (hcompat ▸ hab) with hbc | hbc_stutter
      · left ; exact hbc
      · right ; simp [Function.comp] ; exact hbc_stutter
    · -- A step stutters on B state; hence stutters on C state
      right ; simp [Function.comp] ; rw [hab_stutter]

/-- Hierarchical lifting: if A calls B calls C, and C guarantees `□P`,
    then A guarantees `□(P ∘ proj_C ∘ proj_B)`. -/
theorem ProtocolCall.lift_hierarchical
    (ab : ProtocolCall σ σ_B ι_A ι_B)
    (bc : ProtocolCall σ_B σ_C ι_B ι_C)
    (hcompat : ab.sub = bc.composed)
    {P : σ_C → Prop}
    (hP : pred_implies bc.sub.toSpec.safety_stutter [tlafml| □ ⌜ P ⌝]) :
    pred_implies ab.composed.safety
      [tlafml| □ ⌜ fun s => P (bc.proj (ab.proj s)) ⌝] :=
  (ab.compose bc hcompat).lift_invariant hP

/-! ### Liveness Lifting

    Safety properties lift automatically (via `lift_invariant`). Liveness
    properties (leads-to, eventually) require fairness: the sub-protocol's
    actions must fire often enough in the composed system.

    We provide two approaches:
    1. **General**: the user proves that the composed formula implies the
       sub formula on the projected execution. All temporal properties lift.
    2. **Structured**: the user provides a fairness mapping (each fair sub-action
       has a corresponding composed action with matching enablement). -/

/-- The projection commutes with `exec.drop`: the projected execution
    dropped by `k` is the same as dropping then projecting. -/
private theorem exec.map_drop_comm {σ : Type u} {τ : Type v} (f : σ → τ) (e : exec σ) (k : Nat) :
    (exec.map f e).drop k = exec.map f (e.drop k) := by
  funext n ; simp [exec.map, exec.drop]

/-- General liveness lifting: if the composed formula implies the sub formula
    on the projected execution, then ANY temporal property of the sub-protocol
    lifts to the composed protocol (with the projection composed in).

    This covers leads-to, eventually, and any other temporal operator. The
    user must prove the formula implication, which includes both safety
    (already provided by `ProtocolCall.refines`) and fairness (protocol-specific). -/
theorem ProtocolCall.lift_temporal (pc : ProtocolCall σ σ_sub ι ι_sub)
    {Γ_composed : pred σ} {Γ_sub : pred σ_sub}
    {φ : pred σ_sub}
    (hΓ : ∀ e, Γ_composed e → Γ_sub (exec.map pc.proj e))
    (hφ : pred_implies Γ_sub φ) :
    pred_implies Γ_composed (fun e => φ (exec.map pc.proj e)) := by
  intro e hcomp
  exact hφ (exec.map pc.proj e) (hΓ e hcomp)

/-- Lift a leads-to result from the sub-protocol to the composed protocol.
    The user provides:
    - `hΓ`: the composed formula implies the sub formula on the projection
      (this is the safety refinement + fairness transfer)
    - `hPQ`: the sub-protocol proves `P ↝ Q` under its formula

    The result is `(P ∘ proj) ↝ (Q ∘ proj)` under the composed formula. -/
theorem ProtocolCall.lift_leads_to (pc : ProtocolCall σ σ_sub ι ι_sub)
    {Γ_composed : pred σ} {Γ_sub : pred σ_sub}
    {P Q : σ_sub → Prop}
    (hΓ : ∀ e, Γ_composed e → Γ_sub (exec.map pc.proj e))
    (hPQ : pred_implies Γ_sub (leads_to (state_pred P) (state_pred Q))) :
    pred_implies Γ_composed
      (leads_to (state_pred (fun s => P (pc.proj s))) (state_pred (fun s => Q (pc.proj s)))) := by
  intro e hcomp k hPk
  have hsub := hΓ e hcomp
  have hlt := hPQ (exec.map pc.proj e) hsub k
  simp only [state_pred, exec.drop] at hlt hPk ⊢
  exact hlt hPk

/-- Lift an eventually result from the sub-protocol. -/
theorem ProtocolCall.lift_eventually (pc : ProtocolCall σ σ_sub ι ι_sub)
    {Γ_composed : pred σ} {Γ_sub : pred σ_sub}
    {P : σ_sub → Prop}
    (hΓ : ∀ e, Γ_composed e → Γ_sub (exec.map pc.proj e))
    (hP : pred_implies Γ_sub (eventually (state_pred P))) :
    pred_implies Γ_composed (eventually (state_pred (fun s => P (pc.proj s)))) := by
  intro e hcomp
  have hsub := hΓ e hcomp
  obtain ⟨k, hk⟩ := hP (exec.map pc.proj e) hsub
  refine ⟨k, ?_⟩
  simp only [state_pred, exec.drop, exec.map] at hk ⊢
  exact hk

/-! ### Fairness Transfer

    To establish the formula implication `hΓ` needed for liveness lifting,
    we provide a structured fairness transfer condition. For each weakly-fair
    action in the sub-protocol, there must be a corresponding composed action
    such that:
    1. When the sub-action fires (on the projection), the composed action fires
    2. When the sub-action is enabled (on the projection), the composed action
       is enabled

    These conditions ensure that weak fairness of the composed action implies
    weak fairness of the sub-action on the projected execution. -/

/-- Fairness mapping: each fair sub-action corresponds to a composed action
    with matching fires and enablement. -/
structure FairnessMap (σ : Type u) (σ_sub : Type v) where
  /-- Projection from composed to sub state. -/
  proj : σ → σ_sub
  /-- The sub-protocol action (on sub-state). -/
  sub_action : action σ_sub
  /-- The corresponding composed action. -/
  composed_action : action σ
  /-- Fires transfer: composed fires implies sub fires on projection. -/
  fires_proj : ∀ s s', composed_action s s' → sub_action (proj s) (proj s')
  /-- Enablement transfer: sub enabled at projection implies composed enabled. -/
  enabled_proj : ∀ s, enabled sub_action (proj s) → enabled composed_action s

/-- If the composed system has weak fairness on the composed action,
    then the projected execution has weak fairness on the sub action. -/
theorem FairnessMap.transfer_wf (fm : FairnessMap σ σ_sub) (e : exec σ)
    (hwf : exec.satisfies (weak_fairness fm.composed_action) e) :
    exec.satisfies (weak_fairness fm.sub_action) (exec.map fm.proj e) := by
  -- Work at the semantic level via exec.map_drop
  rw [exec.satisfies] at hwf ⊢
  unfold weak_fairness at hwf ⊢
  intro k henabled
  -- Rewrite through exec.map_drop to normalize
  rw [exec.map_drop] at henabled ⊢
  -- Transfer enablement
  have hcomp_enabled : (e.drop k) |=tla= □ (Enabled fm.composed_action) := by
    intro j
    have hsub := henabled j
    rw [exec.map_drop] at hsub
    simp only [tla_enabled, state_pred, exec.drop, exec.map] at hsub ⊢
    exact fm.enabled_proj _ hsub
  -- Apply composed WF
  have := hwf k hcomp_enabled
  obtain ⟨j, hfire⟩ := this
  refine ⟨j, ?_⟩
  simp only [action_pred, exec.drop, exec.map] at hfire ⊢
  exact fm.fires_proj _ _ hfire

end TLA
