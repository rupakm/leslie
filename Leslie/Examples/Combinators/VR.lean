import Leslie.Examples.Combinators.QuorumSystem
import Leslie.Examples.Combinators.LockInvariant
import Leslie.Examples.Combinators.PhaseCombinator

/-! ## Viewstamped Replication Safety via Combinators

    Decomposes the VR safety argument into combinator applications:
    - `majorityQuorum` for commit and DVC quorums
    - `LockProperty` + `lock_unique` for commit uniqueness per view
    - `cross_phase_quorum_intersection` for view change safety

    **Normal operation**: Leader assigns op-numbers, replicates to replicas.
    An op is committed when a majority stores it.

    **View change**: Replicas send DoViewChange (log + view number) to new
    leader, who collects a majority and installs the most up-to-date log.

    **Agreement**: committed in view v1 -> overlap witness has it (quorum
    intersection) -> new leader has it (most-up-to-date) -> new view can
    only commit the same value (commit uniqueness).
-/

open TLA TLA.Combinator

namespace TLA.Combinator.VR

/-- Per-replica state in VR. -/
structure ReplicaState (Op : Type) where
  viewNumber : Nat
  log : Nat → Option Op
  commitNumber : Nat

/-- The quorum system used by VR: strict majority of `n` replicas. -/
abbrev vrQS (n : Nat) := majorityQuorum n

/-! ### Section 1: Commit Safety via LockProperty -/

/-- Lock property for VR commit: holders of `(i, v)` are replicas with
    `log[i] = some v`. -/
def commitLock (n : Nat) (Op : Type) [DecidableEq Op] :
    LockProperty n (ReplicaState Op) (Nat × Op) where
  qs := vrQS n
  holders := fun ⟨i, v⟩ locals j =>
    match (locals j).log i with
    | some u => decide (u = v)
    | none => false

/-- Value `v` is committed at op-number `i` when its holders form a quorum. -/
def isCommitted (n : Nat) {Op : Type} [DecidableEq Op]
    (locals : Fin n → ReplicaState Op) (i : Nat) (v : Op) : Prop :=
  (commitLock n Op).isLocked (i, v) locals

/-- For the same op-number, holders for distinct values are disjoint. -/
theorem commit_holders_disjoint {Op : Type} [DecidableEq Op]
    (n : Nat) (locals : Fin n → ReplicaState Op)
    (i : Nat) (v w : Op) (hne : v ≠ w) (j : Fin n) :
    ¬((commitLock n Op).holders (i, v) locals j = true ∧
      (commitLock n Op).holders (i, w) locals j = true) := by
  simp only [commitLock]
  intro ⟨h₁, h₂⟩
  match hlog : (locals j).log i with
  | none => simp [hlog] at h₁
  | some u =>
    simp [hlog] at h₁ h₂
    exact hne (h₁.symm.trans h₂)

/-- **Commit uniqueness**: if op `i` is committed with `v` and `w`, then
    `v = w`. Both commit quorums are majority quorums; by intersection,
    some replica k is in both; disjointness forces `v = w`. -/
theorem commit_unique {Op : Type} [DecidableEq Op]
    (n : Nat) (locals : Fin n → ReplicaState Op) (i : Nat)
    (v w : Op) (hv : isCommitted n locals i v) (hw : isCommitted n locals i w) :
    v = w := by
  by_contra hne
  obtain ⟨k, hk_v, hk_w⟩ := (vrQS n).intersection _ _ hv hw
  exact commit_holders_disjoint n locals i v w hne k ⟨hk_v, hk_w⟩

/-! ### Section 2: View Change Safety via Cross-Phase Quorum Intersection

    The commit quorum (old view) and DVC quorum (new view) are both majority
    quorums. By `cross_phase_quorum_intersection`, they share a member that
    witnessed the committed op and participates in the view change. -/

/-- **View change overlap**: some replica in the DVC quorum has the
    committed value. This is `cross_phase_quorum_intersection` applied to
    the commit quorum and DVC quorum. -/
theorem view_change_overlap {Op : Type} (n : Nat)
    (Q_commit Q_dvc : Fin n → Bool)
    (h_commit : (vrQS n).isQuorum Q_commit)
    (h_dvc : (vrQS n).isQuorum Q_dvc)
    (locals : Fin n → ReplicaState Op)
    (i : Nat) (v : Op)
    (h_has_value : ∀ j, Q_commit j = true → (locals j).log i = some v) :
    ∃ k, Q_dvc k = true ∧ (locals k).log i = some v := by
  obtain ⟨k, hk_dvc, hk_commit⟩ :=
    PhaseCombinator.cross_phase_quorum_intersection (vrQS n)
      Q_dvc Q_commit h_dvc h_commit
  exact ⟨k, hk_dvc, h_has_value k hk_commit⟩

/-- **Most-up-to-date selection**: the replica with the highest view number
    in the DVC quorum also has the committed value, by log monotonicity. -/
theorem most_up_to_date_has_committed {Op : Type} (n : Nat)
    (Q_dvc : Fin n → Bool) (locals : Fin n → ReplicaState Op)
    (i : Nat) (v : Op) (k : Fin n)
    (hk_dvc : Q_dvc k = true)
    (hk_val : (locals k).log i = some v)
    (h_log_mono : ∀ a b : Fin n, Q_dvc a = true → Q_dvc b = true →
      (locals a).viewNumber ≥ (locals b).viewNumber →
      (locals b).log i = some v → (locals a).log i = some v)
    (best : Fin n) (h_best_in : Q_dvc best = true)
    (h_best_max : ∀ j, Q_dvc j = true →
      (locals best).viewNumber ≥ (locals j).viewNumber) :
    (locals best).log i = some v :=
  h_log_mono best k h_best_in hk_dvc (h_best_max k hk_dvc) hk_val

/-! ### Section 3: Agreement Across Views

    Composing view_change_overlap + most_up_to_date_has_committed: the new
    leader's installed log has all committed ops from previous views. Any
    new commit at position `i` must agree with the inherited value. -/

/-- **Agreement**: if op `i` is committed with `v` in an old view and with
    `w` in a new view (after view change), then `v = w`. -/
theorem agreement {Op : Type} (n : Nat)
    (i : Nat) (v w : Op)
    (_view_old _view_new : Nat) (_h_view_lt : _view_old < _view_new)
    (locals_old : Fin n → ReplicaState Op)
    (Q_commit : Fin n → Bool)
    (h_commit_quorum : (vrQS n).isQuorum Q_commit)
    (h_has_v : ∀ j, Q_commit j = true → (locals_old j).log i = some v)
    (Q_dvc : Fin n → Bool)
    (h_dvc_quorum : (vrQS n).isQuorum Q_dvc)
    (h_log_mono : ∀ a b : Fin n, Q_dvc a = true → Q_dvc b = true →
      (locals_old a).viewNumber ≥ (locals_old b).viewNumber →
      (locals_old b).log i = some v → (locals_old a).log i = some v)
    (best : Fin n) (h_best_in : Q_dvc best = true)
    (h_best_max : ∀ j, Q_dvc j = true →
      (locals_old best).viewNumber ≥ (locals_old j).viewNumber)
    (locals_new : Fin n → ReplicaState Op)
    (Q_commit_new : Fin n → Bool)
    (_h_commit_new : (vrQS n).isQuorum Q_commit_new)
    (h_has_w : ∀ j, Q_commit_new j = true → (locals_new j).log i = some w)
    (h_new_from_leader : ∀ j, Q_commit_new j = true →
      (locals_new j).log i = (locals_old best).log i) :
    v = w := by
  -- Step 1: Quorum intersection gives overlap replica
  obtain ⟨k, hk_dvc, hk_val⟩ := view_change_overlap n Q_commit Q_dvc
    h_commit_quorum h_dvc_quorum locals_old i v h_has_v
  -- Step 2: The best (most up-to-date) replica also has the value
  have h_best_val := most_up_to_date_has_committed n Q_dvc locals_old i v
    k hk_dvc hk_val h_log_mono best h_best_in h_best_max
  -- Step 3: Any new-view commit quorum member has both v and w at position i
  obtain ⟨j, hj⟩ := exists_true_of_quorum _h_commit_new
  have h_w : (locals_new j).log i = some w := h_has_w j hj
  have h_v : (locals_new j).log i = some v := by
    rw [h_new_from_leader j hj]; exact h_best_val
  exact Option.some.inj (h_v.symm.trans h_w)

/-! ### Summary

    | Combinator                          | VR usage                          |
    |--------------------------------------|-----------------------------------|
    | `majorityQuorum` (QuorumSystem)      | Commit quorums, DVC quorums       |
    | `LockProperty` + `lock_unique`       | Commit uniqueness per view        |
    | `cross_phase_quorum_intersection`    | View change overlap witness       |

    VR-specific parts (not factored into combinators): log monotonicity
    and the most-up-to-date selection rule.
-/

end TLA.Combinator.VR
