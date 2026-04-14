import Leslie.Round
import Leslie.Cutoff

/-! ## Config ↔ Round Bridge

    Bridges the Config-level cutoff framework (`Leslie/Cutoff.lean`) to
    the raw `RoundState`-level protocol model (`Leslie/Round.lean`).

    Under reliable communication (every process hears every other),
    `round_step` of an induced symmetric threshold `RoundAlg` projects
    to `Config.succ` of the underlying `SymThreshAlg`. This file proves
    that projection and uses it to transfer Config-level invariant
    preservation to the RoundState level.

    ### Structure

    1. `RoundSymThreshAlg` — a `SymThreshAlg` packaged so that it
       induces a `RoundAlg` over `Fin k` states.
    2. `filter_update_eq_sum_over_values` — the arithmetic re-grouping
       lemma at the heart of the bridge.
    3. `round_step_projects_to_config_succ` — the main bridge theorem.
    4. `config_inv_preservation_lifts` — preservation transfer from
       Config level to RoundState level.
    5. A minimal binary-OTR worked example demonstrating end-to-end
       usage. -/

open TLA

namespace TLA.ConfigRoundBridge

variable {k α_num α_den : Nat}

/-! ### The bridge structure -/

/-- A symmetric threshold round algorithm: a `SymThreshAlg` packaged
    so it induces a `RoundAlg` over `Fin k` states with `Fin k`
    messages. -/
structure RoundSymThreshAlg (k α_num α_den : Nat) where
  sta : SymThreshAlg k α_num α_den

namespace RoundSymThreshAlg

variable (rsta : RoundSymThreshAlg k α_num α_den)

/-- The induced `RoundAlg`. Local state and messages are both `Fin k`.
    Each process broadcasts its state, and updates based on the
    threshold view of received messages. -/
def toRoundAlg (n : Nat) : RoundAlg (Fin n) (Fin k) (Fin k) where
  init := fun _p _s => True
  send := fun _p s => s
  update := fun _p s msgs =>
    let tv : ThreshView k := fun v =>
      decide
        (((List.finRange n).filter
          fun q => match msgs q with
                   | some m => decide (m = v)
                   | none   => false).length * α_den > α_num * n)
    rsta.sta.update s tv

end RoundSymThreshAlg

/-- The Config abstraction of a RoundState whose locals are already `Fin k`. -/
def stateConfig {k n : Nat} (s : RoundState (Fin n) (Fin k)) : Config k n :=
  s.toConfig id

/-! ### The arithmetic core: counting by source value -/

/-- Counting processes whose post-state equals `v'` by partitioning
    on their pre-state value. Proved over an arbitrary list. -/
private theorem filter_update_eq_sum_over_values
    {k : Nat} (sta : SymThreshAlg k α_num α_den)
    {α : Type} (L : List α) (f : α → Fin k) (v' : Fin k) (tv : ThreshView k) :
    (L.filter fun p => decide (sta.update (f p) tv = v')).length =
    ((List.finRange k).map fun v =>
      if sta.update v tv = v' then
        (L.filter fun p => decide (f p = v)).length
      else 0).sum := by
  induction L with
  | nil =>
    simp only [List.filter_nil, List.length_nil]
    -- RHS: every summand is 0, sum is 0.
    have h : ∀ M : List (Fin k),
        (M.map fun v =>
          if sta.update v tv = v' then
            (([] : List α).filter fun p => decide (f p = v)).length
          else 0).sum = 0 := by
      intro M
      induction M with
      | nil => rfl
      | cons w ws ih =>
        rw [List.map_cons, List.sum_cons, ih]
        simp
    exact (h (List.finRange k)).symm
  | cons a L ih =>
    have h_pointwise : ∀ v : Fin k,
        (if sta.update v tv = v' then
          ((a :: L).filter fun x => decide (f x = v)).length
        else 0) =
        (if sta.update v tv = v' then
          (L.filter fun x => decide (f x = v)).length
        else 0) +
        (if sta.update v tv = v' ∧ v = f a then 1 else 0) := by
      intro v
      by_cases hv : sta.update v tv = v'
      · simp only [hv, if_true]
        simp only [List.filter]
        by_cases hfa : f a = v
        · simp only [decide_eq_true hfa, List.length_cons]
          have : v = f a := hfa.symm
          simp [this]
        · have hne : ¬ decide (f a = v) = true := by
            simp [hfa]
          simp only [hne, if_false]
          have hne2 : ¬ v = f a := fun heq => hfa heq.symm
          simp [hne2]
      · simp [hv]
    rw [show ((List.finRange k).map fun v =>
          if sta.update v tv = v' then
            ((a :: L).filter fun x => decide (f x = v)).length
          else 0).sum =
        ((List.finRange k).map fun v =>
          (if sta.update v tv = v' then
             (L.filter fun x => decide (f x = v)).length
           else 0) +
          (if sta.update v tv = v' ∧ v = f a then 1 else 0)).sum from by
      congr 1
      exact List.map_congr_left (fun v _ => h_pointwise v)]
    rw [_root_.TLA.List.sum_map_add, ← ih]
    -- Extra-sum simplification: only v = f a contributes, and only if update (f a) tv = v'
    have h_extra :
        ((List.finRange k).map fun v =>
          if sta.update v tv = v' ∧ v = f a then 1 else 0).sum =
        (if sta.update (f a) tv = v' then 1 else 0) := by
      rw [show ((List.finRange k).map fun v =>
            if sta.update v tv = v' ∧ v = f a then 1 else 0) =
          ((List.finRange k).map fun v =>
            (if sta.update (f a) tv = v' then 1 else 0) *
            (if v = f a then 1 else 0)) from by
        apply List.map_congr_left
        intro v _
        by_cases hfa : v = f a
        · subst hfa; simp
        · simp [hfa]]
      -- Factor the constant multiplier out of the sum
      rw [show ((List.finRange k).map fun v =>
            (if sta.update (f a) tv = v' then 1 else 0) *
            (if v = f a then 1 else 0)).sum =
          (if sta.update (f a) tv = v' then 1 else 0) *
          ((List.finRange k).map fun v => if v = f a then 1 else 0).sum from by
        induction (List.finRange k) with
        | nil => simp
        | cons w ws ihx =>
          simp only [List.map_cons, List.sum_cons, ihx, Nat.mul_add]]
      rw [_root_.TLA.fin_indicator]
      omega
    rw [h_extra]
    -- Now: (filter P (a::L)).length = (filter P L).length + (if update (f a) tv = v' then 1 else 0)
    simp only [List.filter]
    by_cases hav : sta.update (f a) tv = v'
    · have : decide (sta.update (f a) tv = v') = true := decide_eq_true hav
      simp [this, hav]
    · have : ¬ decide (sta.update (f a) tv = v') = true := by simp [hav]
      simp [this, hav]

/-! ### The core bridge lemmas -/

/-- Under reliable HO, the received-message count for value `v` at process `p`
    equals the global `counts v` of the pre-state config. -/
theorem received_count_eq_global_count
    {k n : Nat} (rsta : RoundSymThreshAlg k α_num α_den)
    (s : RoundState (Fin n) (Fin k))
    (ho : HOCollection (Fin n))
    (h_reliable : ∀ p q : Fin n, ho p q = true)
    (p : Fin n) (v : Fin k) :
    ((List.finRange n).filter fun q =>
      match delivered (rsta.toRoundAlg n) s ho p q with
      | some m => decide (m = v)
      | none   => false).length =
    (stateConfig s).counts v := by
  simp only [stateConfig, RoundState.toConfig]
  congr 1
  apply List.filter_congr
  intro q _
  simp only [delivered, h_reliable, if_true]
  rfl

/-- The threshold view computed by each process from its received messages
    under reliable HO equals the global threshold view of the pre-state. -/
theorem received_threshView_eq_global
    {k n : Nat} (rsta : RoundSymThreshAlg k α_num α_den)
    (s : RoundState (Fin n) (Fin k))
    (ho : HOCollection (Fin n))
    (h_reliable : ∀ p q : Fin n, ho p q = true)
    (p : Fin n) :
    (fun v : Fin k =>
      decide
        (((List.finRange n).filter fun q =>
          match delivered (rsta.toRoundAlg n) s ho p q with
          | some m => decide (m = v)
          | none   => false).length * α_den > α_num * n)) =
    (stateConfig s).threshView α_num α_den := by
  funext v
  simp only [Config.threshView]
  rw [received_count_eq_global_count rsta s ho h_reliable p v]

/-- **Bridge theorem:** under reliable HO, one `round_step` of the induced
    RoundAlg projects to one `Config.succ` of the underlying `SymThreshAlg`. -/
theorem round_step_projects_to_config_succ
    {k n : Nat} (rsta : RoundSymThreshAlg k α_num α_den)
    (s s' : RoundState (Fin n) (Fin k))
    (ho : HOCollection (Fin n))
    (h_reliable : ∀ p q : Fin n, ho p q = true)
    (h_step : round_step (rsta.toRoundAlg n) ho s s') :
    stateConfig s' = Config.succ rsta.sta (stateConfig s) := by
  obtain ⟨_hround, hlocals⟩ := h_step
  -- Both sides are Config k n. Show they have the same `counts`.
  show (⟨_, _⟩ : Config k n) = ⟨_, _⟩
  congr 1
  funext v'
  simp only [stateConfig, RoundState.toConfig, Config.succ, succCounts]
  -- Rewrite s'.locals p to the update expression
  have hp : ∀ p : Fin n,
      (s'.locals p : Fin k) =
      rsta.sta.update (s.locals p) ((stateConfig s).threshView α_num α_den) := by
    intro p
    have := hlocals p
    simp only [RoundSymThreshAlg.toRoundAlg] at this
    rw [this]
    congr 1
    exact received_threshView_eq_global rsta s ho h_reliable p
  have hLHS :
      ((List.finRange n).filter fun p => decide (id (s'.locals p) = v')).length =
      ((List.finRange n).filter fun p =>
        decide (rsta.sta.update (s.locals p)
                  ((stateConfig s).threshView α_num α_den) = v')).length := by
    congr 1
    apply List.filter_congr
    intro p _
    simp only [id]
    rw [hp p]
  rw [hLHS]
  exact filter_update_eq_sum_over_values rsta.sta (List.finRange n)
    (fun p => s.locals p) v' ((stateConfig s).threshView α_num α_den)

/-! ### Lifting Config-level invariants to RoundState level -/

/-- A RoundState-level invariant derived from a `ConfigInv`. -/
def RoundStateInv {k n : Nat} (inv : ConfigInv k)
    (s : RoundState (Fin n) (Fin k)) : Prop :=
  inv n (stateConfig s)

/-- **Preservation transfer:** if a `ConfigInv` is preserved by `Config.succ`,
    then its RoundState version is preserved by `round_step` under reliable HO. -/
theorem config_inv_preservation_lifts
    {k n : Nat} (rsta : RoundSymThreshAlg k α_num α_den)
    (inv : ConfigInv k)
    (h_cfg : ∀ c : Config k n, inv n c → inv n (Config.succ rsta.sta c))
    (s s' : RoundState (Fin n) (Fin k))
    (ho : HOCollection (Fin n))
    (h_reliable : ∀ p q : Fin n, ho p q = true)
    (h_step : round_step (rsta.toRoundAlg n) ho s s')
    (h_inv : RoundStateInv inv s) :
    RoundStateInv inv s' := by
  unfold RoundStateInv at h_inv ⊢
  rw [round_step_projects_to_config_succ rsta s s' ho h_reliable h_step]
  exact h_cfg _ h_inv

/-! ### Example: minimal binary SymThresh protocol -/

/-- The binary OTR-like symthresh algorithm. -/
def binaryOtrSTA : SymThreshAlg 2 2 3 where
  update := fun v tv =>
    if tv 0 then (0 : Fin 2)
    else if tv 1 then (1 : Fin 2)
    else v

/-- Packaged as a `RoundSymThreshAlg`. -/
def binaryOtrRsta : RoundSymThreshAlg 2 2 3 where
  sta := binaryOtrSTA

/-- Lifted safety: `noTwoSuperMaj` holds at every RoundState.

    Combines `noTwoSuperMaj_always` (Config-level tautology) with the
    bridge. Since the invariant is always true at the Config level,
    it lifts trivially to the RoundState level. -/
theorem binaryOtr_noTwoSuperMaj (n : Nat) (s : RoundState (Fin n) (Fin 2)) :
    RoundStateInv noTwoSuperMaj s := by
  unfold RoundStateInv
  exact noTwoSuperMaj_always n (stateConfig s)

/-- The binary OTR uses the same underlying `SymThreshAlg` as `otr_symthresh`. -/
theorem binaryOtrSTA_eq_otr_symthresh : binaryOtrSTA = otr_symthresh := rfl

end TLA.ConfigRoundBridge
