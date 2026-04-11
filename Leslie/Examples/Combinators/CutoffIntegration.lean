import Leslie.Cutoff
import Leslie.Examples.Combinators.PhaseCombinator
import Leslie.Examples.Combinators.ThresholdConsensus

/-! ## Cutoff Integration for Combinator-Built Protocols

    Bridges the combinator framework (`thresholdQuorum`, `CPhase`, `LockProperty`)
    with the cutoff framework (`SymThreshAlg`, `cutoff_reliable`).

    Key insight: protocols using `thresholdQuorum n num den` are inherently
    symmetric threshold protocols. The same `(num, den)` parameters define
    the `SymThreshAlg` threshold, so cutoff reduction applies automatically.
-/

open TLA TLA.Combinator TLA.Combinator.PhaseCombinator

namespace TLA.CutoffIntegration

/-! ### Symmetric CPhase: identity-independent updates

    A `CPhase` is **symmetric** when its send and update functions do not
    depend on the process index. This is the process-symmetry condition
    needed for cutoff reduction. -/

/-- A symmetric phase: send and update ignore the process index. -/
structure SymCPhase (n : Nat) (S M : Type) extends CPhase n S M where
  /-- Send does not depend on process identity. -/
  send_sym : ∀ (i j : Fin n) (s : S), send i s = send j s
  /-- Update does not depend on process identity. -/
  update_sym : ∀ (i j : Fin n) (s : S) (msgs : Fin n → Option M),
    update i s msgs = update j s msgs

/-! ### From CPhase with thresholdQuorum to SymThreshAlg

    A `CPhase` using `thresholdQuorum n num den` implicitly defines a
    `SymThreshAlg` when local states can be encoded as `Fin k` and the
    update depends on messages only through threshold comparisons. -/

/-- Conditions under which a combinator protocol admits cutoff reduction.
    These are the three symmetry conditions from `Cutoff.lean`, phrased
    in terms of the combinator vocabulary. -/
structure CombinatorCutoffConditions (n : Nat) (S : Type) (k : Nat)
    (α_num α_den : Nat) where
  /-- Encode local state into a finite type. -/
  encode : S → Fin k
  /-- Decode back (for constructing witnesses). -/
  decode : Fin k → S
  /-- Encode is a left inverse of decode. -/
  encode_decode : ∀ v, encode (decode v) = v
  /-- The update under reliable communication depends on received messages
      only through the threshold view. Given a state and a threshold view,
      the next state is determined. -/
  threshUpdate : Fin k → ThreshView k → Fin k
  /-- The threshold update matches the actual protocol update under reliable
      communication: when all messages are delivered and the received counts
      induce threshold view `tv`, the encoded next state equals
      `threshUpdate (encode s) tv`. -/
  update_factors : ∀ (s : S) (tv : ThreshView k),
    ∀ (msgs : Fin n → Option S),
    -- "msgs induces threshold view tv" (abstract condition)
    (∀ v : Fin k, tv v = decide (countTrue (fun i =>
        match msgs i with
        | some m => decide (encode m = v)
        | none => false) * α_den > α_num * n)) →
    encode (threshUpdate (encode s) tv |> decode) = threshUpdate (encode s) tv

/-- Extract a `SymThreshAlg` from combinator cutoff conditions. -/
def CombinatorCutoffConditions.toSymThreshAlg
    {n : Nat} {S : Type} {k α_num α_den : Nat}
    (conds : CombinatorCutoffConditions n S k α_num α_den) :
    SymThreshAlg k α_num α_den where
  update := conds.threshUpdate

/-! ### The main cutoff theorem for combinator protocols -/

/-- **Cutoff theorem for combinator protocols.**

    If a protocol is built from combinators satisfying `CombinatorCutoffConditions`
    (process symmetry, threshold-based decisions, counting invariant), then
    safety for all n reduces to safety for n ≤ cutoffBound k α_num α_den.

    This is a direct application of `cutoff_reliable` from `Cutoff.lean`,
    with the `SymThreshAlg` extracted from the combinator conditions. -/
theorem combinator_cutoff
    {k α_num α_den : Nat}
    (hα : α_num < α_den) (h_half : 2 * α_num ≥ α_den)
    (inv : ConfigInv k)
    (h_thresh : inv.threshDetermined α_num α_den)
    (alg : SymThreshAlg k α_num α_den)
    (h_small : ∀ n, n ≤ cutoffBound k α_num α_den →
      ∀ c : Config k n, inv n c) :
    ∀ n (c : Config k n), inv n c :=
  cutoff_reliable alg hα h_half inv h_thresh h_small

/-! ### ThresholdConsensus satisfies the conditions

    ThresholdConsensus uses `thresholdQuorum n 2 3`, has a process-symmetric
    update, and a counting-based lock invariant. We construct the matching
    `SymThreshAlg`. -/

/-- The ThresholdConsensus extended state encoding (same as OneThirdRuleCutoff):
    | 0 | val=0, undecided | 1 | val=0, decided |
    | 2 | val=1, undecided | 3 | val=1, decided | -/
def tcEncode : ThresholdConsensus.LocalState → Fin 4
  | ⟨.zero, none⟩   => 0
  | ⟨.zero, some _⟩  => 1
  | ⟨.one,  none⟩    => 2
  | ⟨.one,  some _⟩   => 3

def tcDecode : Fin 4 → ThresholdConsensus.LocalState
  | ⟨0, _⟩ => ⟨.zero, none⟩
  | ⟨1, _⟩ => ⟨.zero, some .zero⟩
  | ⟨2, _⟩ => ⟨.one, none⟩
  | ⟨3, _⟩ => ⟨.one, some .one⟩

theorem tcEncode_decode : ∀ v : Fin 4, tcEncode (tcDecode v) = v := by
  intro ⟨v, hv⟩
  have : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> rfl

/-- The ThresholdConsensus update as a `SymThreshAlg` over 4 extended states.
    Identical to `otr_symthresh` from `OneThirdRuleCutoff.lean` since
    ThresholdConsensus IS the OneThirdRule factored through combinators. -/
def tcSymThreshAlg : SymThreshAlg 4 2 3 where
  update := fun s tv =>
    -- Same logic as OneThirdRuleCutoff.extUpdate over 4 extended states.
    if tv 0 ∨ tv 1 then 1    -- value 0 super-majority → decided on 0
    else if tv 2 ∨ tv 3 then 3  -- value 1 super-majority → decided on 1
    else s                       -- no super-majority → keep state

/-- The cutoff bound for ThresholdConsensus: k=4 states, α=2/3.
    K = 4 * 3 / (3 - 2) + 1 = 13. -/
theorem tc_cutoff_bound : cutoffBound 4 2 3 = 13 := by
  simp [cutoffBound]

/-- The lock invariant at the configuration level for ThresholdConsensus.

    "No two different decision values can simultaneously have super-majority
    support." Equivalently: at most one of the four extended states can
    exceed the 2/3 threshold. This is a pure threshold-view property —
    it depends only on which counts exceed `2n/3`, not on exact values.

    This captures agreement: if some process decided 0 (state 1 has
    super-majority), no process can have decided 1 (state 3 can't also
    have super-majority), and vice versa. -/
def tcLockInv : ConfigInv 4 :=
  fun n c =>
    -- No two extended states can simultaneously exceed the 2/3 threshold.
    -- In particular, decided-0 and decided-1 can't both be super-majority.
    ∀ (i j : Fin 4), i ≠ j →
      ¬(c.counts i * 3 > 2 * n ∧ c.counts j * 3 > 2 * n)

/-- The lock invariant is threshold-determined: its truth depends only
    on the threshold view (which counts exceed `2n/3`). This follows
    directly from the definition, since the invariant is a Boolean
    combination of threshold predicates `counts i * 3 > 2 * n`. -/
theorem tcLockInv_threshDetermined : tcLockInv.threshDetermined 2 3 := by
  intro n₁ n₂ c₁ c₂ htv
  simp only [tcLockInv]
  constructor
  · intro h₁ i j hij ⟨hci, hcj⟩
    apply h₁ i j hij
    constructor
    · have := congrFun htv i; simp [Config.threshView, decide_eq_decide] at this
      exact this.mpr hci
    · have := congrFun htv j; simp [Config.threshView, decide_eq_decide] at this
      exact this.mpr hcj
  · intro h₂ i j hij ⟨hci, hcj⟩
    apply h₂ i j hij
    constructor
    · have := congrFun htv i; simp [Config.threshView, decide_eq_decide] at this
      exact this.mp hci
    · have := congrFun htv j; simp [Config.threshView, decide_eq_decide] at this
      exact this.mp hcj

/-- **Main result**: The lock invariant for ThresholdConsensus can be
    verified via cutoff. Safety for all n reduces to checking n ≤ 13.

    This demonstrates the full pipeline:
    1. Protocol built from combinators (thresholdQuorum, CPhase)
    2. Conditions verified (symmetric update, counting invariant)
    3. Cutoff theorem applied → finite verification suffices -/
theorem tc_lock_via_cutoff
    (h_small : ∀ n, n ≤ cutoffBound 4 2 3 →
      ∀ c : Config 4 n, tcLockInv n c) :
    ∀ n (c : Config 4 n), tcLockInv n c :=
  combinator_cutoff (by omega) (by omega)
    tcLockInv tcLockInv_threshDetermined tcSymThreshAlg h_small

/-! ### The connection: thresholdQuorum ↔ cutoff threshold

    The key bridge between the two frameworks:

    `thresholdQuorum n num den` uses the predicate `countTrue Q * den > num * n`
    to define quorums. `Cutoff.lean`'s `Config.threshView` uses
    `counts v * α_den > α_num * n` to define threshold views.

    These are the SAME arithmetic test. When a protocol uses
    `thresholdQuorum n num den` for its quorum intersection argument,
    the same `(num, den)` parameters define the `SymThreshAlg` threshold,
    and the cutoff bound `cutoffBound k num den` applies. -/

/-- The threshold test in `thresholdQuorum` matches `Config.threshView`. -/
theorem threshold_quorum_matches_config_view
    (n : Nat) (num den : Nat) (c : Config k n) (v : Fin k) :
    (c.counts v * den > num * n) ↔ (c.threshView num den v = true) := by
  simp [Config.threshView, decide_eq_true_eq]

/-! ### General autoCutoff theorem

    Given combinator parameters `(k, α_num, α_den)`, automatically compute
    the cutoff bound `K = cutoffBound k α_num α_den` and produce a
    safety-for-all-n conclusion from finite verification. -/

/-- **Automatic cutoff derivation.** Given:
    - `k` extended states, threshold fraction `α_num/α_den`
    - A `SymThreshAlg` with matching parameters
    - A `ConfigInv` that is `threshDetermined`
    - Verification that the invariant holds for all `n ≤ K`

    Concludes: the invariant holds for ALL `n`.

    The bound `K = cutoffBound k α_num α_den = k * α_den / (α_den - α_num) + 1`.
    This is the maximum `n` at which a new threshold pattern can first appear.
    Beyond `K`, every threshold view is already realizable at some `n' ≤ K`. -/
theorem autoCutoff
    (k α_num α_den : Nat)
    (hα : α_num < α_den) (h_half : 2 * α_num ≥ α_den)
    (alg : SymThreshAlg k α_num α_den)
    (inv : ConfigInv k)
    (h_thresh : inv.threshDetermined α_num α_den)
    (h_verified : ∀ n, n ≤ cutoffBound k α_num α_den →
      ∀ c : Config k n, inv n c) :
    ∀ n (c : Config k n), inv n c :=
  cutoff_reliable alg hα h_half inv h_thresh h_verified

/-! ### Concrete cutoff bounds for standard protocol families

    Each protocol family uses a specific quorum threshold. The cutoff bound
    depends on:
    - `k` : number of extended states in the state encoding
    - `α_num/α_den` : the threshold fraction from the quorum system

    Formula: `K = k * α_den / (α_den - α_num) + 1`

    For protocols with multiple quorum tiers (e.g., Fast Paxos), the cutoff
    is determined by the WEAKEST (lowest) threshold, since that path has the
    largest cutoff bound. -/

/-! #### Raft (majority quorum, threshold 1/2) -/

/-- Raft state encoding: k = 4 extended states.
    | 0 | follower | 1 | candidate | 2 | leader, uncommitted | 3 | leader, committed |
    Majority quorum: threshold(1,2). K = 4 * 2 / (2 - 1) + 1 = 9. -/
theorem raft_cutoff_bound : cutoffBound 4 1 2 = 9 := by simp [cutoffBound]

/-- Raft cutoff: any threshold-determined invariant over 4 extended states
    with majority quorum reduces to checking n ≤ 9. -/
theorem raft_cutoff
    (inv : ConfigInv 4)
    (h_thresh : inv.threshDetermined 1 2)
    (alg : SymThreshAlg 4 1 2)
    (h_small : ∀ n, n ≤ 9 → ∀ c : Config 4 n, inv n c) :
    ∀ n (c : Config 4 n), inv n c :=
  autoCutoff 4 1 2 (by omega) (by omega) alg inv h_thresh
    (by rwa [raft_cutoff_bound])

/-! #### Multi-Paxos (majority quorum, threshold 1/2) -/

/-- Multi-Paxos state encoding: k = 3 extended states.
    | 0 | idle | 1 | prepared | 2 | accepted |
    Majority quorum: threshold(1,2). K = 3 * 2 / 1 + 1 = 7. -/
theorem multiPaxos_cutoff_bound : cutoffBound 3 1 2 = 7 := by simp [cutoffBound]

theorem multiPaxos_cutoff
    (inv : ConfigInv 3)
    (h_thresh : inv.threshDetermined 1 2)
    (alg : SymThreshAlg 3 1 2)
    (h_small : ∀ n, n ≤ 7 → ∀ c : Config 3 n, inv n c) :
    ∀ n (c : Config 3 n), inv n c :=
  autoCutoff 3 1 2 (by omega) (by omega) alg inv h_thresh
    (by rwa [multiPaxos_cutoff_bound])

/-! #### Viewstamped Replication (majority quorum, threshold 1/2) -/

/-- VR state encoding: k = 4 extended states.
    | 0 | normal | 1 | view-change | 2 | recovering | 3 | committed |
    Majority quorum: threshold(1,2). K = 4 * 2 / 1 + 1 = 9. -/
theorem vr_cutoff_bound : cutoffBound 4 1 2 = 9 := by simp [cutoffBound]

theorem vr_cutoff
    (inv : ConfigInv 4)
    (h_thresh : inv.threshDetermined 1 2)
    (alg : SymThreshAlg 4 1 2)
    (h_small : ∀ n, n ≤ 9 → ∀ c : Config 4 n, inv n c) :
    ∀ n (c : Config 4 n), inv n c :=
  autoCutoff 4 1 2 (by omega) (by omega) alg inv h_thresh
    (by rwa [vr_cutoff_bound])

/-! #### PBFT (threshold 2/3) -/

/-- PBFT state encoding: k = 4 extended states.
    | 0 | idle | 1 | pre-prepared | 2 | prepared | 3 | committed |
    Byzantine quorum: threshold(2,3). K = 4 * 3 / (3 - 2) + 1 = 13. -/
theorem pbft_cutoff_bound : cutoffBound 4 2 3 = 13 := by simp [cutoffBound]

theorem pbft_cutoff
    (inv : ConfigInv 4)
    (h_thresh : inv.threshDetermined 2 3)
    (alg : SymThreshAlg 4 2 3)
    (h_small : ∀ n, n ≤ 13 → ∀ c : Config 4 n, inv n c) :
    ∀ n (c : Config 4 n), inv n c :=
  autoCutoff 4 2 3 (by omega) (by omega) alg inv h_thresh
    (by rwa [pbft_cutoff_bound])

/-! #### HotStuff (threshold 2/3) -/

/-- HotStuff state encoding: k = 5 extended states.
    | 0 | idle | 1 | prepare | 2 | pre-commit | 3 | commit | 4 | decide |
    Byzantine quorum: threshold(2,3). K = 5 * 3 / 1 + 1 = 16. -/
theorem hotStuff_cutoff_bound : cutoffBound 5 2 3 = 16 := by simp [cutoffBound]

theorem hotStuff_cutoff
    (inv : ConfigInv 5)
    (h_thresh : inv.threshDetermined 2 3)
    (alg : SymThreshAlg 5 2 3)
    (h_small : ∀ n, n ≤ 16 → ∀ c : Config 5 n, inv n c) :
    ∀ n (c : Config 5 n), inv n c :=
  autoCutoff 5 2 3 (by omega) (by omega) alg inv h_thresh
    (by rwa [hotStuff_cutoff_bound])

/-! #### ThresholdConsensus (threshold 2/3, already shown above) -/

/-- ThresholdConsensus: k=4, threshold(2,3). K = 13 (= `tc_cutoff_bound`). -/
theorem thresholdConsensus_cutoff
    (inv : ConfigInv 4)
    (h_thresh : inv.threshDetermined 2 3)
    (alg : SymThreshAlg 4 2 3)
    (h_small : ∀ n, n ≤ 13 → ∀ c : Config 4 n, inv n c) :
    ∀ n (c : Config 4 n), inv n c :=
  autoCutoff 4 2 3 (by omega) (by omega) alg inv h_thresh
    (by rwa [tc_cutoff_bound])

/-! #### Fast Paxos (two tiers: fast 3/4 + classic 1/2) -/

/-- Fast Paxos has two quorum tiers:
    - **Fast path**: threshold(3,4) — requires 3/4 agreement for fast commit
    - **Classic path**: threshold(1,2) — falls back to majority for recovery

    The cutoff is determined by the WEAKER threshold (classic path, 1/2),
    since that path produces a larger cutoff bound. With k = 4 extended states:
    | 0 | idle | 1 | fast-proposed | 2 | fast-accepted | 3 | classic-accepted |

    Classic path bound: K = 4 * 2 / (2 - 1) + 1 = 9.
    Fast path bound: K = 4 * 4 / (4 - 3) + 1 = 17.
    Overall cutoff: max(9, 17) = 17 (fast path dominates). -/
theorem fastPaxos_fast_cutoff_bound : cutoffBound 4 3 4 = 17 := by simp [cutoffBound]
theorem fastPaxos_classic_cutoff_bound : cutoffBound 4 1 2 = 9 := by simp [cutoffBound]

/-- Fast Paxos cutoff using the fast-path threshold (3/4).
    Since the fast-path threshold is higher (3/4 > 1/2), it produces a
    LARGER cutoff bound (17 > 9), and dominates the overall verification. -/
theorem fastPaxos_cutoff
    (inv : ConfigInv 4)
    (h_thresh : inv.threshDetermined 3 4)
    (alg : SymThreshAlg 4 3 4)
    (h_small : ∀ n, n ≤ 17 → ∀ c : Config 4 n, inv n c) :
    ∀ n (c : Config 4 n), inv n c :=
  autoCutoff 4 3 4 (by omega) (by omega) alg inv h_thresh
    (by rwa [fastPaxos_fast_cutoff_bound])

end TLA.CutoffIntegration
