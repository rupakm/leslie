import Leslie_LTS.Framework

/-! # Ideal Byzantine Reliable Broadcast — LTS Formulation

  An abstract specification of BRB that hides all message-passing
  complexity. The key idea:

  - An internal `commit` transition sets `set_up := some v` for some value `v`.
  - A correct process can output `v` only when `set_up = some v`.
  - The `commit` value is unconstrained in the ideal; the simulation
    relation determines which value gets committed based on the real state.

  The external labels (`corrupt`, `input`, `output`) match the real BRB.
  The `commit` label is internal.
-/

open LTS

namespace IdealBRB

variable (n f : Nat) (Value : Type)

/-! ### State -/

/-- The ideal BRB state. -/
structure State (n : Nat) (Value : Type) where
  /-- List of corrupted processes. -/
  corrupted : List (Fin n)
  /-- The sender's broadcast input (set by `input`). -/
  broadcastVal : Option Value
  /-- The committed value: once set, all outputs must match it. -/
  set_up : Option Value
  /-- Per-process output (at most one per process). -/
  returned : Fin n → Option Value

/-- A process is correct if it has not been corrupted. -/
def isCorrect (s : State n Value) (p : Fin n) : Prop := p ∉ s.corrupted

/-! ### Labels -/

/-- Labels of the ideal BRB. External labels match the real BRB;
    `commit` is the sole internal label. -/
inductive Label (n : Nat) (Value : Type) where
  /-- The adversary corrupts a process (external). -/
  | corrupt (i : Fin n)
  /-- The environment provides input to a process (external). -/
  | input (i : Fin n) (v : Value)
  /-- A correct process outputs a value (external). -/
  | output (i : Fin n) (v : Value)
  /-- The system commits to a value (internal). -/
  | commit (v : Value)

instance [Inhabited Value] : Inhabited (Label n Value) := ⟨.commit default⟩

/-! ### The Ideal BRB System -/

/-- The ideal BRB as a labelled transition system. -/
def ideal_brb (sender : Fin n) : System (State n Value) (Label n Value) where
  init := fun s =>
    s.corrupted = [] ∧
    s.broadcastVal = none ∧
    s.set_up = none ∧
    (∀ p, s.returned p = none)
  step := fun s lbl s' =>
    match lbl with
    | .corrupt i =>
        isCorrect n Value s i ∧
        s.corrupted.length + 1 ≤ f ∧
        s' = { s with corrupted := i :: s.corrupted }
    | .input i v =>
        i = sender ∧
        s.broadcastVal = none ∧
        s' = { s with broadcastVal := some v }
    | .output i v =>
        isCorrect n Value s i ∧
        s.returned i = none ∧
        s.set_up = some v ∧
        s' = { s with
          returned := fun p => if p = i then some v else s.returned p }
    | .commit v =>
        s.set_up = none ∧
        ((isCorrect n Value s sender ∧ s.broadcastVal = some v) ∨
         ¬ isCorrect n Value s sender) ∧
        s' = { s with set_up := some v }

/-! ### Internal / External Labelling -/

/-- The labelling: `commit` is internal;
    `corrupt`, `input`, `output` are external. -/
def ideal_labelling [Inhabited Value] : Labelling (Label n Value) where
  is_internal := fun l =>
    match l with
    | .corrupt _ => false
    | .input _ _ => false
    | .output _ _ => false
    | .commit _ => true
  tau := .commit default
  tau_internal := rfl

/-! ### Step-Preservation Lemmas (Monotonicity)

    Simple per-step invariants: once certain fields are set, no
    transition resets them. Used by `ideal_brb_totality`'s leads-to
    chain and by protocol invariants more broadly. -/

section monotonicity
variable {n f : Nat} {Value : Type} [DecidableEq Value]
         {sender : Fin n} [Inhabited Value]

/-- `set_up` is monotone: once `some v`, it stays `some v`. -/
theorem set_up_persist {s s' : State n Value}
    {l : Label n Value}
    (hstep : (ideal_brb (n := n) (f := f) (Value := Value) sender).step s l s')
    {v : Value} (h : s.set_up = some v) :
    s'.set_up = some v := by
  simp only [ideal_brb] at hstep
  match l with
  | .corrupt _ => obtain ⟨_, _, rfl⟩ := hstep; exact h
  | .input _ _ => obtain ⟨_, _, rfl⟩ := hstep; exact h
  | .output _ _ => obtain ⟨_, _, _, rfl⟩ := hstep; exact h
  | .commit w =>
    obtain ⟨hnone, _, rfl⟩ := hstep
    exact absurd h (by rw [hnone]; simp)

/-- `returned p` is monotone: once `some v`, it stays. -/
theorem returned_persist {s s' : State n Value}
    {l : Label n Value}
    (hstep : (ideal_brb (n := n) (f := f) (Value := Value) sender).step s l s')
    {p : Fin n} {v : Value} (h : s.returned p = some v) :
    s'.returned p = some v := by
  simp only [ideal_brb] at hstep
  match l with
  | .corrupt _ => obtain ⟨_, _, rfl⟩ := hstep; exact h
  | .input _ _ => obtain ⟨_, _, rfl⟩ := hstep; exact h
  | .commit _ => obtain ⟨_, _, rfl⟩ := hstep; exact h
  | .output i w =>
    obtain ⟨_, hnone_i, _, rfl⟩ := hstep
    show (if p = i then some w else s.returned p) = some v
    split
    · next heq => rw [heq] at h; simp [hnone_i] at h
    · exact h

/-- `broadcastVal` is monotone: once `some v`, it stays. -/
theorem broadcastVal_persist {s s' : State n Value}
    {l : Label n Value}
    (hstep : (ideal_brb (n := n) (f := f) (Value := Value) sender).step s l s')
    {v : Value} (h : s.broadcastVal = some v) :
    s'.broadcastVal = some v := by
  simp only [ideal_brb] at hstep
  match l with
  | .corrupt _ => obtain ⟨_, _, rfl⟩ := hstep; exact h
  | .output _ _ => obtain ⟨_, _, _, rfl⟩ := hstep; exact h
  | .commit _ => obtain ⟨_, _, rfl⟩ := hstep; exact h
  | .input _ _ =>
    obtain ⟨_, hnone, rfl⟩ := hstep
    simp [hnone] at h

/-- `broadcastVal` persists along a valid execution: if `broadcastVal
    = some v` at position `k`, it stays `some v` at all `k' ≥ k`. -/
theorem broadcastVal_persist_along
    {e : Execution (State n Value) (Label n Value)}
    (hv : (ideal_brb (n := n) (f := f) (Value := Value) sender).valid_exec e)
    {k : Nat} {v : Value}
    (h : (e.states k).broadcastVal = some v) :
    ∀ k', k ≤ k' → (e.states k').broadcastVal = some v := by
  intro k'
  induction k' with
  | zero =>
    intro hle
    have : k = 0 := Nat.le_zero.mp hle
    rw [this] at h; exact h
  | succ k' ih =>
    intro hle
    rcases Nat.eq_or_lt_of_le hle with rfl | hlt
    · exact h
    · have hle' : k ≤ k' := by omega
      have hprev := ih hle'
      exact broadcastVal_persist (hv.2 k') hprev

/-- `returned p` persists along a valid execution: once `some v`, stays. -/
theorem returned_persist_along
    {e : Execution (State n Value) (Label n Value)}
    (hv : (ideal_brb (n := n) (f := f) (Value := Value) sender).valid_exec e)
    {k : Nat} {p : Fin n} {v : Value}
    (h : (e.states k).returned p = some v) :
    ∀ k', k ≤ k' → (e.states k').returned p = some v := by
  intro k'
  induction k' with
  | zero =>
    intro hle
    have : k = 0 := Nat.le_zero.mp hle
    rw [this] at h; exact h
  | succ k' ih =>
    intro hle
    rcases Nat.eq_or_lt_of_le hle with rfl | hlt
    · exact h
    · have hle' : k ≤ k' := by omega
      have hprev := ih hle'
      exact returned_persist (hv.2 k') hprev

/-- `set_up` persists along a valid execution. -/
theorem set_up_persist_along
    {e : Execution (State n Value) (Label n Value)}
    (hv : (ideal_brb (n := n) (f := f) (Value := Value) sender).valid_exec e)
    {k : Nat} {v : Value}
    (h : (e.states k).set_up = some v) :
    ∀ k', k ≤ k' → (e.states k').set_up = some v := by
  intro k'
  induction k' with
  | zero =>
    intro hle
    have : k = 0 := Nat.le_zero.mp hle
    rw [this] at h; exact h
  | succ k' ih =>
    intro hle
    rcases Nat.eq_or_lt_of_le hle with rfl | hlt
    · exact h
    · have hle' : k ≤ k' := by omega
      have hprev := ih hle'
      exact set_up_persist (hv.2 k') hprev

/-- Corruption is monotone: if `p ∈ s.corrupted`, then `p ∈ s'.corrupted`
    for any step. -/
theorem corrupted_mem_persist {s s' : State n Value}
    {l : Label n Value}
    (hstep : (ideal_brb (n := n) (f := f) (Value := Value) sender).step s l s')
    {p : Fin n} (h : p ∈ s.corrupted) :
    p ∈ s'.corrupted := by
  simp only [ideal_brb] at hstep
  match l with
  | .corrupt _ => obtain ⟨_, _, rfl⟩ := hstep; exact List.mem_cons.mpr (Or.inr h)
  | .input _ _ => obtain ⟨_, _, rfl⟩ := hstep; exact h
  | .output _ _ => obtain ⟨_, _, _, rfl⟩ := hstep; exact h
  | .commit _ => obtain ⟨_, _, rfl⟩ := hstep; exact h

/-- Corruption persists along a valid execution. -/
theorem corrupted_mem_persist_along
    {e : Execution (State n Value) (Label n Value)}
    (hv : (ideal_brb (n := n) (f := f) (Value := Value) sender).valid_exec e)
    {k : Nat} {p : Fin n}
    (h : p ∈ (e.states k).corrupted) :
    ∀ k', k ≤ k' → p ∈ (e.states k').corrupted := by
  intro k'
  induction k' with
  | zero =>
    intro hle; have : k = 0 := Nat.le_zero.mp hle; rw [this] at h; exact h
  | succ k' ih =>
    intro hle
    rcases Nat.eq_or_lt_of_le hle with rfl | hlt
    · exact h
    · exact corrupted_mem_persist (hv.2 k') (ih (by omega))

end monotonicity

/-! ### Safety Properties (label-based)

    Properties are expressed purely in terms of the observable label
    trace, without inspecting internal state. -/

/-- **Validity** (label-based): if the sender is never corrupted and some
    process outputs `v`, then `input sender v` appears in the trace. -/
def validity (sender : Fin n) : TraceProp (State n Value) (Label n Value) :=
  fun e _k =>
    (∀ k, e.labels k ≠ .corrupt sender) →
    ∀ k i v, e.labels k = .output i v →
      ∃ k', e.labels k' = .input sender v

/-- **Agreement** (label-based): all output values in the trace agree. -/
def agreement : TraceProp (State n Value) (Label n Value) :=
  fun e _k => ∀ k₁ k₂ p q vp vq,
    e.labels k₁ = .output p vp →
    e.labels k₂ = .output q vq →
    vp = vq

/-! ### Safety Theorems -/

/-- If `broadcastVal = some v` at position `k`, then `.input sender v`
    appeared earlier. Proved by `System.invariant` (forward induction). -/
private theorem broadcastVal_trace_inv (sender : Fin n) :
    (ideal_brb n f Value sender).satisfies
      (always (fun e k => ∀ v, (e.states k).broadcastVal = some v →
        ∃ k', e.labels k' = .input sender v)) := by
  apply System.invariant
  · intro e hv v h; exact absurd (hv.1.2.1 ▸ h) (by simp)
  · intro e k hv ih v hbv
    have hstep := hv.2 k
    match hl : e.labels k with
    | .corrupt _ => rw [hl] at hstep; rw [hstep.2.2] at hbv; exact ih v hbv
    | .input i w =>
      rw [hl] at hstep
      obtain ⟨hi_eq, _, heq⟩ := hstep
      rw [heq] at hbv; simp only [Option.some.injEq] at hbv; exact ⟨k, by rw [hl, hi_eq, hbv]⟩
    | .output _ _ => rw [hl] at hstep; rw [hstep.2.2.2] at hbv; exact ih v hbv
    | .commit _ => rw [hl] at hstep; rw [hstep.2.2] at hbv; exact ih v hbv

/-- If `sender ∈ corrupted` at position `k`, then `.corrupt sender`
    appeared earlier. Proved by `System.invariant` (forward induction). -/
private theorem corrupted_trace_inv (sender : Fin n) :
    (ideal_brb n f Value sender).satisfies
      (always (fun e k => sender ∈ (e.states k).corrupted →
        ∃ k', e.labels k' = .corrupt sender)) := by
  apply System.invariant
  · intro e hv h; simp [hv.1.1] at h
  · intro e k hv ih hmem
    have hstep := hv.2 k
    match hl : e.labels k with
    | .corrupt i =>
      rw [hl] at hstep; rw [hstep.2.2] at hmem; simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact ⟨k, hl⟩
      · exact ih hmem
    | .input _ _ => rw [hl] at hstep; rw [hstep.2.2] at hmem; exact ih hmem
    | .output _ _ => rw [hl] at hstep; rw [hstep.2.2.2] at hmem; exact ih hmem
    | .commit _ => rw [hl] at hstep; rw [hstep.2.2] at hmem; exact ih hmem

/-- Trace invariant: if the sender has never been corrupted and
    `set_up = some v` at state `k`, then `.input sender v` appeared
    earlier in the trace. Proved by `System.invariant` using
    `broadcastVal_trace_inv` and `corrupted_trace_inv`. -/
theorem ideal_validity_inv (sender : Fin n) :
    (ideal_brb n f Value sender).satisfies
      (always (fun e k =>
        (∀ j, e.labels j ≠ .corrupt sender) →
        ∀ v, (e.states k).set_up = some v →
          ∃ k', e.labels k' = .input sender v)) := by
  apply System.invariant
  · intro e hv _ v hsu; exact absurd (hv.1.2.2.1 ▸ hsu) (by simp)
  · intro e k hv ih hno_corrupt v hsu
    have hstep := hv.2 k
    match hl : e.labels k with
    | .corrupt _ => rw [hl] at hstep; rw [hstep.2.2] at hsu; exact ih hno_corrupt v hsu
    | .input _ _ => rw [hl] at hstep; rw [hstep.2.2] at hsu; exact ih hno_corrupt v hsu
    | .output _ _ => rw [hl] at hstep; rw [hstep.2.2.2] at hsu; exact ih hno_corrupt v hsu
    | .commit w =>
      rw [hl] at hstep
      obtain ⟨_, hor, heq⟩ := hstep
      rw [heq] at hsu; simp only [Option.some.injEq] at hsu; subst hsu
      rcases hor with ⟨_, hbv⟩ | hcorrupt
      · have := broadcastVal_trace_inv n f Value sender e hv k
        simp only [Nat.zero_add] at this; exact this w hbv
      · exfalso
        have := corrupted_trace_inv n f Value sender e hv k
        simp only [Nat.zero_add] at this
        have ⟨k', hk'⟩ := this (by
          simp only [isCorrect, Decidable.not_not] at hcorrupt; exact hcorrupt)
        exact hno_corrupt k' hk'

/-- `set_up` is permanent: once set to `some v`, it stays `some v`. -/
private theorem set_up_perm (sender : Fin n) :
    ∀ s l s', (ideal_brb n f Value sender).step s l s' →
      s.set_up = some v → s'.set_up = some v := by
  intro s l s' hstep hsu
  match l with
  | .corrupt _ => obtain ⟨_, _, rfl⟩ := hstep; exact hsu
  | .input _ _ => obtain ⟨_, _, rfl⟩ := hstep; exact hsu
  | .output _ _ => obtain ⟨_, _, _, rfl⟩ := hstep; exact hsu
  | .commit _ => obtain ⟨hsu_none, _, _⟩ := hstep; rw [hsu] at hsu_none; contradiction

/-- `set_up` permanence extended along a valid execution. -/
private theorem set_up_perm_exec (sender : Fin n) {e : Execution _ _}
    (hv : (ideal_brb n f Value sender).valid_exec e)
    {k k' : Nat} (hle : k ≤ k')
    (hsu : (e.states k).set_up = some v) :
    (e.states k').set_up = some v := by
  induction k' with
  | zero => exact Nat.le_zero.mp hle ▸ hsu
  | succ k' ih =>
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · exact heq ▸ hsu
    · exact set_up_perm n f Value sender _ _ _ (hv.2 k') (ih (Nat.lt_succ_iff.mp hlt))

/-- Validity holds for the ideal BRB (derived from `ideal_validity_inv`). -/
theorem ideal_validity (sender : Fin n) :
    (ideal_brb n f Value sender).satisfies (validity n Value sender) := by
  intro e hv hno_corrupt k i v hout
  have hstep := hv.2 k; rw [hout] at hstep
  have hsu : (e.states k).set_up = some v := hstep.2.2.1
  have := ideal_validity_inv n f Value sender e hv k
  simp only [Nat.zero_add] at this
  exact this hno_corrupt v hsu

/-- Agreement holds for the ideal BRB. -/
theorem ideal_agreement (sender : Fin n) :
    (ideal_brb n f Value sender).satisfies (agreement n Value) := by
  intro e hv k₁ k₂ p q vp vq hout₁ hout₂
  have hstep₁ := hv.2 k₁; rw [hout₁] at hstep₁
  have hstep₂ := hv.2 k₂; rw [hout₂] at hstep₂
  have hsu₁ : (e.states k₁).set_up = some vp := hstep₁.2.2.1
  have hsu₂ : (e.states k₂).set_up = some vq := hstep₂.2.2.1
  rcases Nat.le_total k₁ k₂ with hle | hle
  · have := set_up_perm_exec n f Value sender hv hle hsu₁
    rw [hsu₂] at this; exact (Option.some.inj this).symm
  · have := set_up_perm_exec n f Value sender hv hle hsu₂
    rw [hsu₁] at this; exact Option.some.inj this

/-- Validity holds on stuttering-valid executions of the ideal BRB.
    Stutter labels (τ = .commit default) are not `.output`, so stutter
    positions are invisible to the property. -/
theorem ideal_validity_stutter [Inhabited Value] (sender : Fin n) :
    ∀ e, (ideal_brb n f Value sender).valid_exec_stutter (ideal_labelling n Value) e →
      validity n Value sender e 0 := by
  intro e ⟨hinit, hsos⟩ hno_corrupt k i v hout
  rcases hsos k with hstep | ⟨_, hlbl⟩
  · -- Real step: same as ideal_validity
    rw [hout] at hstep
    have hsu : (e.states k).set_up = some v := hstep.2.2.1
    suffices ∀ j, (∀ m, e.labels m ≠ .corrupt sender) →
        ∀ v, (e.states j).set_up = some v →
          ∃ k', e.labels k' = .input sender v by
      exact this k hno_corrupt v hsu
    intro j; induction j with
    | zero => intro _ v hsu'; exact absurd (hinit.2.2.1 ▸ hsu') (by simp)
    | succ j ih =>
      intro hno v hsu'
      rcases hsos j with hstep_j | ⟨heq_s, _⟩
      · -- Real step at j
        match hl : e.labels j with
        | .corrupt _ => rw [hl] at hstep_j; rw [hstep_j.2.2] at hsu'; exact ih hno v hsu'
        | .input _ _ => rw [hl] at hstep_j; rw [hstep_j.2.2] at hsu'; exact ih hno v hsu'
        | .output _ _ => rw [hl] at hstep_j; rw [hstep_j.2.2.2] at hsu'; exact ih hno v hsu'
        | .commit w =>
          rw [hl] at hstep_j
          obtain ⟨_, hor, heq⟩ := hstep_j
          rw [heq] at hsu'; simp only [Option.some.injEq] at hsu'; subst hsu'
          rcases hor with ⟨_, hbv⟩ | hcorrupt
          · -- broadcastVal = some w: find when it was set
            suffices ∀ m, (e.states m).broadcastVal = some w →
                ∃ k', e.labels k' = .input sender w by exact this j hbv
            intro m; induction m with
            | zero => intro h; exact absurd (hinit.2.1 ▸ h) (by simp)
            | succ m ihm =>
              intro hbv_m
              rcases hsos m with hstep_m | ⟨heq_m, _⟩
              · match hlm : e.labels m with
                | .corrupt _ => rw [hlm] at hstep_m; rw [hstep_m.2.2] at hbv_m; exact ihm hbv_m
                | .input i' w' =>
                  rw [hlm] at hstep_m
                  obtain ⟨hi, _, heq_m⟩ := hstep_m
                  rw [heq_m] at hbv_m; simp only [Option.some.injEq] at hbv_m
                  exact ⟨m, by rw [hlm, hi, hbv_m]⟩
                | .output _ _ => rw [hlm] at hstep_m; rw [hstep_m.2.2.2] at hbv_m; exact ihm hbv_m
                | .commit _ => rw [hlm] at hstep_m; rw [hstep_m.2.2] at hbv_m; exact ihm hbv_m
              · rw [← heq_m] at hbv_m; exact ihm hbv_m
          · -- Sender corrupt: find .corrupt sender label
            exfalso
            suffices ∀ m, sender ∈ (e.states m).corrupted →
                ∃ k', e.labels k' = .corrupt sender by
              obtain ⟨k', hk'⟩ := this j (by simp only [isCorrect,
                Decidable.not_not] at hcorrupt; exact hcorrupt)
              exact hno k' hk'
            intro m; induction m with
            | zero => intro h; simp [hinit.1] at h
            | succ m ihm =>
              intro hmem
              rcases hsos m with hstep_m | ⟨heq_m, _⟩
              · match hlm : e.labels m with
                | .corrupt i =>
                  rw [hlm] at hstep_m; rw [hstep_m.2.2] at hmem; simp only [List.mem_cons] at hmem
                  rcases hmem with rfl | hmem
                  · exact ⟨m, hlm⟩
                  · exact ihm hmem
                | .input _ _ => rw [hlm] at hstep_m; rw [hstep_m.2.2] at hmem; exact ihm hmem
                | .output _ _ => rw [hlm] at hstep_m; rw [hstep_m.2.2.2] at hmem; exact ihm hmem
                | .commit _ => rw [hlm] at hstep_m; rw [hstep_m.2.2] at hmem; exact ihm hmem
              · rw [← heq_m] at hmem; exact ihm hmem
      · -- Stutter at j: state unchanged
        rw [← heq_s] at hsu'; exact ih hno v hsu'
  · -- Stutter: default ≠ .output, contradicts hout
    exact absurd (hlbl ▸ hout) nofun

/-- Agreement holds on stuttering-valid executions of the ideal BRB. -/
theorem ideal_agreement_stutter [Inhabited Value] (sender : Fin n) :
    ∀ e, (ideal_brb n f Value sender).valid_exec_stutter (ideal_labelling n Value) e →
      agreement n Value e 0 := by
  intro e ⟨hinit, hsos⟩ k₁ k₂ p q vp vq hout₁ hout₂
  have hstep₁ : (ideal_brb n f Value sender).step
    (e.states k₁) (e.labels k₁) (e.states (k₁ + 1)) := by
    rcases hsos k₁ with h | ⟨_, hlbl⟩
    · exact h
    · exact absurd (hlbl ▸ hout₁) nofun
  have hstep₂ : (ideal_brb n f Value sender).step
    (e.states k₂) (e.labels k₂) (e.states (k₂ + 1)) := by
    rcases hsos k₂ with h | ⟨_, hlbl⟩
    · exact h
    · exact absurd (hlbl ▸ hout₂) nofun
  rw [hout₁] at hstep₁; rw [hout₂] at hstep₂
  have hsu₁ : (e.states k₁).set_up = some vp := hstep₁.2.2.1
  have hsu₂ : (e.states k₂).set_up = some vq := hstep₂.2.2.1
  have set_up_perm_stutter : ∀ w, ∀ k k', k ≤ k' →
      (e.states k).set_up = some w → (e.states k').set_up = some w := by
    intro w k k' hle hsu
    induction k' with
    | zero => exact Nat.le_zero.mp hle ▸ hsu
    | succ k' ih =>
      rcases Nat.eq_or_lt_of_le hle with rfl | hlt
      · exact hsu
      · have ih' := ih (Nat.lt_succ_iff.mp hlt)
        rcases hsos k' with hstep | ⟨heq, _⟩
        · exact set_up_perm n f Value sender _ _ _ hstep ih'
        · rwa [← heq]
  rcases Nat.le_total k₁ k₂ with hle | hle
  · have := set_up_perm_stutter vp k₁ k₂ hle hsu₁
    rw [hsu₂] at this; exact (Option.some.inj this).symm
  · have := set_up_perm_stutter vq k₂ k₁ hle hsu₂
    rw [hsu₁] at this; exact Option.some.inj this

end IdealBRB
