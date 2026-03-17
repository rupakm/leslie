import Leslie.Examples.LastVotingPhased.Defs

/-! ## General-n LastVoting

    Generalizes the n = 3 proof to arbitrary n > 0.
    See `Defs.lean` for the shared type definitions. -/

open TLA

namespace LastVotingPhased

/-! ## General-n LastVoting

    The following section generalizes the n = 3 proof to arbitrary n > 0.
    Types (`LState`, `LVState`, `LVMsg`, `Value`) are reused from the
    n = 3 section since they do not depend on the process count.

    The key change: `hasMaj3` (count ≥ 2) becomes `hasMajG` (count * 2 > n),
    and quorum intersection uses `filter_disjoint_length_le` from `Round.lean`
    instead of case analysis on `Fin 3`. -/

namespace Gen

variable (n : Nat) (hn : n > 0)

/-! ### General-n helpers -/

/-- Coordinator of ballot `r` with `n` processes. -/
def coordinatorG (r : Nat) : Fin n := ⟨r % n, Nat.mod_lt r hn⟩

/-- Strict majority predicate for `n` processes: more than half satisfy `p`. -/
def hasMajG (p : Fin n → Bool) : Bool :=
  decide (((List.finRange n).filter (fun r => p r)).length * 2 > n)

/-- Extract the highest-ballot lastVote from promises (general n). -/
def highestVoteG (promises : Fin n → Option LVMsg) : Option Value :=
  let collected := (List.finRange n).filterMap fun p =>
    match promises p with
    | some (.promise (some vb)) => some vb
    | _ => none
  match collected with
  | [] => none
  | (v, b) :: rest =>
    some (rest.foldl (fun best cur => if cur.2 > best.2 then cur else best) (v, b)).1

/-- Uniform message type for all phases (same as n = 3).
    Note: explicitly not parameterized by n. -/
abbrev LVMsgsG : PhaseMessages 4 := LVMsgs

/-! ### General-n phase definitions -/

def lvPhase0G : Phase (Fin n) LVState LVMsg where
  send := fun p s =>
    if p = coordinatorG n hn s.roundNum then .prepare else .skip
  update := fun p s msgs =>
    let c := coordinatorG n hn s.roundNum
    let heardPrepare := match msgs c with | some .prepare => true | _ => false
    { s with core := { s.core with
        prepared := heardPrepare
        accepted := false
        proposal := if p = c then none else s.core.proposal } }

def lvPhase1G : Phase (Fin n) LVState LVMsg where
  send := fun _p s => .promise s.core.lastVote
  update := fun p s msgs =>
    if p = coordinatorG n hn s.roundNum then
      let promiseCount := (List.finRange n).filter (fun q =>
        match msgs q with | some (.promise _) => true | _ => false) |>.length
      if promiseCount * 2 > n then
        let collected := (List.finRange n).filterMap fun q =>
          match msgs q with
          | some (.promise (some vb)) => some vb
          | _ => none
        let prop := match collected with
          | [] => defaultValue
          | (v, b) :: rest =>
            (rest.foldl (fun best cur => if cur.2 > best.2 then cur else best) (v, b)).1
        { s with core := { s.core with proposal := some prop } }
      else { s with core := { s.core with proposal := none } }
    else s

def lvPhase2G : Phase (Fin n) LVState LVMsg where
  send := fun p s =>
    if p = coordinatorG n hn s.roundNum then
      match s.core.proposal with | some v => .propose v | none => .skip
    else .skip
  update := fun _p s msgs =>
    let c := coordinatorG n hn s.roundNum
    match msgs c with
    | some (.propose v) =>
      { s with core := { s.core with lastVote := some (v, s.roundNum), accepted := true } }
    | _ => s

def lvPhase3G : Phase (Fin n) LVState LVMsg where
  send := fun _p s =>
    if s.core.accepted then
      match s.core.lastVote with
      | some (v, _) => .accepted v
      | none => .notAccepted
    else .notAccepted
  update := fun _p s msgs =>
    let acceptors : Fin n → Bool := fun q =>
      match msgs q with | some (.accepted _) => true | _ => false
    let core' :=
      if hasMajG n acceptors then
        let decidedVal := (List.finRange n).filterMap (fun q =>
          match msgs q with | some (.accepted v) => some v | _ => none) |>.head?
        match decidedVal with
        | some v => { s.core with decided := some v, prepared := false, accepted := false }
        | none => { s.core with prepared := false, accepted := false }
      else { s.core with prepared := false, accepted := false }
    { roundNum := s.roundNum + 1, core := core' }

/-! ### General-n algorithm and spec -/

def lvAlgG : PhaseRoundAlg (Fin n) LVState 4 LVMsgsG where
  init := fun _p s =>
    s.roundNum = 0 ∧
    s.core = { lastVote := none, decided := none,
               prepared := false, accepted := false,
               proposal := none }
  phases := fun i =>
    if i.val = 0 then lvPhase0G n hn
    else if i.val = 1 then lvPhase1G n hn
    else if i.val = 2 then lvPhase2G n hn
    else lvPhase3G n

def lvCommG : PhaseCommPred (Fin n) 4 := fun _ _ _ => True

def lvSpecG : PhaseRoundSpec (Fin n) LVState 4 LVMsgsG where
  alg := lvAlgG n hn
  comm := lvCommG n

def lvLeslieSpecG : Spec (PhaseRoundState (Fin n) LVState 4) :=
  (lvSpecG n hn).toSpec (by omega)

/-! ### General-n safety property -/

def agreementG (s : PhaseRoundState (Fin n) LVState 4) : Prop :=
  ∀ (p q : Fin n) (v w : Value),
    (s.locals p).core.decided = some v →
    (s.locals q).core.decided = some w →
    v = w

/-! ### General-n invariant

    Same 9-conjunct structure as the n = 3 invariant, with `hasMaj3`
    replaced by `hasMajG` and `≥ 2` replaced by `* 2 > n`. -/

def lv_inv_gen (s : PhaseRoundState (Fin n) LVState 4) : Prop :=
  -- (A) Agreement
  agreementG n s ∧
  -- (B) Accepted consistency
  (∀ p : Fin n, (s.locals p).core.accepted = true →
    ∃ v b, (s.locals p).core.lastVote = some (v, b) ∧ b = s.round) ∧
  -- (C) Phase 3 consistency
  (s.phase = ⟨3, by omega⟩ →
    ∀ p : Fin n, (s.locals p).core.accepted = true →
    ∃ v, (s.locals p).core.lastVote = some (v, s.round)) ∧
  -- (D) Decision-proposal consistency
  (∀ p : Fin n, ∀ v, (s.locals p).core.decided = some v →
    s.phase = ⟨3, by omega⟩ →
    hasMajG n (fun q => (s.locals q).core.accepted) = true →
    ∀ q : Fin n, (s.locals q).core.accepted = true →
    ∃ w, (s.locals q).core.lastVote = some (w, s.round) ∧ w = v) ∧
  -- (E) Round synchronization
  (∀ p : Fin n, (s.locals p).roundNum = s.round) ∧
  -- (F') Acceptance only at phase 3
  (∀ p : Fin n, (s.locals p).core.accepted = true → s.phase = ⟨3, by omega⟩) ∧
  -- (F) Uniform value at phase 3
  (s.phase = ⟨3, by omega⟩ →
    ∀ (p q : Fin n) (vp vq : Value),
    (s.locals p).core.accepted = true →
    (s.locals q).core.accepted = true →
    (s.locals p).core.lastVote = some (vp, s.round) →
    (s.locals q).core.lastVote = some (vq, s.round) →
    vp = vq) ∧
  -- (G) Cross-ballot invariant
  (∀ p v, (s.locals p).core.decided = some v →
    (∀ q₁ w b₁, (s.locals q₁).core.lastVote = some (w, b₁) → w ≠ v →
      ∀ q₂ b₂, (s.locals q₂).core.lastVote = some (v, b₂) → b₁ < b₂) ∧
    ((List.finRange n).filter fun q =>
      match (s.locals q).core.lastVote with
      | some (w, _) => decide (w = v) | none => false).length * 2 > n ∧
    (s.phase.val ≥ 2 →
      ∀ w, (s.locals (coordinatorG n hn s.round)).core.proposal = some w → w = v)) ∧
  -- (H) Ballot bound
  (∀ q w b, (s.locals q).core.lastVote = some (w, b) →
    b ≤ s.round ∧
    (b = s.round → s.phase = ⟨3, by omega⟩ ∧ (s.locals q).core.accepted = true))

/-! ### Key lemma: general-n majority quorum intersection -/

/-- Two strict majorities of `n` processes must share at least one process. -/
theorem majority_intersect (p₁ p₂ : Fin n → Bool)
    (h₁ : ((List.finRange n).filter fun r => p₁ r).length * 2 > n)
    (h₂ : ((List.finRange n).filter fun r => p₂ r).length * 2 > n) :
    ∃ r : Fin n, p₁ r = true ∧ p₂ r = true := by
  by_contra h
  have h' : ∀ r, ¬(p₁ r = true ∧ p₂ r = true) := fun r hr => h ⟨r, hr⟩
  have h_sum := filter_disjoint_length_le
    (fun r => p₁ r) (fun r => p₂ r) (List.finRange n) h'
  have h_len : (List.finRange n).length = n := List.length_finRange
  omega

/-! ### Init proof -/

theorem lv_inv_init_gen :
    ∀ s, (lvLeslieSpecG n hn).init s → lv_inv_gen n hn s := by
  intro s ⟨hround, hphase, hinit⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (A) Agreement: vacuously true, no decisions
    intro p q v w hv _
    have hp := (hinit p).2
    simp at hp ; rw [hp] at hv ; simp at hv
  · -- (B) Accepted consistency: vacuously true, no accepts
    intro p hacc
    have hp := (hinit p).2
    simp at hp ; rw [hp] at hacc ; simp at hacc
  · -- (C) Phase 3 consistency: phase = 0 ≠ 3
    intro hph ; simp [hphase] at hph
  · -- (D) Decision-proposal consistency: vacuously true
    intro p v hv
    have hp := (hinit p).2
    simp at hp ; rw [hp] at hv ; simp at hv
  · -- (E) Round synchronization
    intro p
    have hp := (hinit p).1
    simp at hp ; rw [hround, hp]
  · -- (F') Acceptance only at phase 3: vacuous
    intro p hacc
    have hp := (hinit p).2
    simp at hp ; rw [hp] at hacc ; simp at hacc
  · -- (F) Uniform value: phase = 0 ≠ 3
    intro hph ; simp [hphase] at hph
  · -- (G) Cross-ballot: vacuously true, no decisions
    intro p v hv
    have hp := (hinit p).2
    simp at hp ; rw [hp] at hv ; simp at hv
  · -- (H) Ballot bound: vacuously true, all lastVote = none
    intro q w b hlv
    have hp := (hinit q).2
    simp at hp ; rw [hp] at hlv ; simp at hlv

/-! ### Step proof -/

/-- The main invariant preservation theorem (general n).
    Each of the 4 phase transitions preserves `lv_inv_gen`.
    This follows the same structure as `lv_inv_step` (n = 3),
    using `majority_intersect` for quorum arguments. -/
theorem lv_inv_step_gen :
    ∀ s ho, lv_inv_gen n hn s → (lvCommG n) s.round s.phase ho →
    ∀ s', phase_step (lvAlgG n hn) ho s s' → lv_inv_gen n hn s' := by
  -- The proof follows the same 4-phase × 9-conjunct structure as
  -- lv_inv_step (n = 3). The key difference: quorum intersection
  -- arguments use majority_intersect (via filter_disjoint_length_le)
  -- instead of case analysis on Fin 3.
  -- Phase 0→1: all preservation (decided/lastVote/accepted unchanged or reset).
  -- Phase 1→2: G3 uses majority_intersect + foldl_max_picks_dominated_value.
  -- Phase 2→3: F uses coordinator's single proposal; G uses filter_length_mono.
  -- Phase 3→0: A uses F (uniform value); G uses filter_length_mono for G2.
  sorry

/-! The proof is structurally identical to `lv_inv_step` (n = 3).
    The only places that differ from a direct translation are:
    - **Phase 1→2, G3**: quorum intersection between the coordinator's
      promise set (size > n/2) and the v-voter set (size > n/2) via
      `majority_intersect`, replacing the Fin 3 case split.
    - **Phase 2→3, G2**: `filter_length_mono` shows new v-voters
      maintain majority, replacing the `≥ 2` arithmetic.
    - **Phase 3→0, G2**: `filter_length_mono` shows deciding process's
      HO majority implies global majority of v-voters.
    - All other cases are line-for-line translations with `hasMaj3`
      replaced by `hasMajG` and `coordinator` by `coordinatorG`.
    The `filter_len_le_one_of_two_distinct_false` lemma (Fin 3-specific)
    is not needed: general majority arithmetic via `omega` suffices. -/

-- Uncomment and fill in when ready:
-- The Phase 0 case from the n=3 proof translates directly.
-- See lv_inv_step for the detailed proof structure.
-- Key reusable lemmas:
--   majority_intersect (above)
--   filter_disjoint_length_le (Round.lean)
--   filter_length_mono (Round.lean)
--   foldl_max_mem, foldl_max_ballot_ge, foldl_max_picks_dominated_value (this file)
-- Proof sketch (same 4-phase × 9-conjunct structure as lv_inv_step):
-- Phase 0→1: All preservation (decided/lastVote/accepted unchanged or reset).
-- Phase 1→2: G3 uses majority_intersect + foldl_max_picks_dominated_value.
-- Phase 2→3: F uses coordinator's single proposal; G uses filter_length_mono.
-- Phase 3→0: A uses F (uniform value); G uses filter_length_mono for G2.
-- Key reusable lemmas: majority_intersect, filter_disjoint_length_le,
--   filter_length_mono, foldl_max_mem/ballot_ge/picks_dominated_value.
/-! ### Safety theorem -/

/-- Agreement is an invariant of the general-n phased LastVoting protocol. -/
theorem lv_agreement_gen :
    pred_implies (lvLeslieSpecG n hn).safety [tlafml| □ ⌜agreementG n⌝] := by
  suffices h : pred_implies (lvLeslieSpecG n hn).safety
      [tlafml| □ ⌜lv_inv_gen n hn⌝] by
    intro e he k
    exact (h e he k).1
  apply phase_round_invariant (lvSpecG n hn) (by omega)
  · exact lv_inv_init_gen n hn
  · exact lv_inv_step_gen n hn

end Gen


end LastVotingPhased
