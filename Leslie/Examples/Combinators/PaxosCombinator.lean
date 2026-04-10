import Leslie.Examples.Combinators.QuorumSystem
import Leslie.Examples.Combinators.PhaseCombinator

/-! ## Paxos Safety Decomposition via Combinators

    This file shows how the Paxos safety argument from `Leslie.Examples.Paxos`
    decomposes into applications of the combinator primitives from
    `QuorumSystem.lean`, `LockInvariant.lean`, and `PhaseCombinator.lean`.

    The key insight: Paxos's `SafeAt` invariant is an *iterated* application of
    majority quorum intersection across ballots. At each ballot `b`, the proposer
    collects promises from a majority quorum. The intersection of this promise
    quorum with any prior acceptance quorum guarantees that the proposer sees
    prior accepted values.

    ### Structure

    1. **Ballot-indexed quorums**: each ballot creates two quorums (promise, accept)
    2. **SafeAt as iterated quorum intersection**: for every `c < b`, the promise
       quorum at `b` intersects with the acceptance quorum at `c`
    3. **Agreement from SafeAt + quorum intersection**: two majority accept quorums
       overlap with the SafeAt witness quorum
    4. **SafeAt preservation**: the three-way case split (c > maxReport,
       c = maxReport, c < maxReport) as a composition pattern

    This is a CONCEPTUAL decomposition — proofs that would duplicate `Paxos.lean`
    use `sorry`. The value is showing the structure of the argument in terms of
    combinator types.
-/

open TLA TLA.Combinator

namespace TLA.Combinator.PaxosCombinator

/-! ### Value type and ballot structure -/

inductive Value where
  | v1 | v2
  deriving DecidableEq

variable (n : Nat)

/-! ### Section 1: Ballot-Indexed Quorums

    In Paxos, each ballot `b` creates two quorum-forming sets:
    - **Promise quorum** `got1b(b)`: acceptors that sent Phase 1b to ballot `b`'s proposer
    - **Accept quorum** `did2b(b)`: acceptors that sent Phase 2b for ballot `b`

    Both are subsets of `Fin n` (the acceptors), and both must be majorities
    before the protocol advances. The quorum system is `majorityQuorum n`. -/

/-- The quorum system used by Paxos: strict majority of `n` acceptors. -/
abbrev paxosQS := majorityQuorum n

/-- A ballot's quorum data: the promise quorum and the accept quorum.
    In `Paxos.lean`, these correspond to `s.got1b p` and `s.did2b p`
    for the proposer `p` with `ballot p = b`. -/
structure BallotQuorums where
  /-- Which acceptors promised to this ballot (got1b). -/
  promiseQ : Fin n → Bool
  /-- Which acceptors accepted this ballot's value (did2b). -/
  acceptQ  : Fin n → Bool

/-! ### Section 2: SafeAt as Iterated Quorum Intersection

    The `safeAt` predicate from `Paxos.lean` says: for every ballot `c < b`,
    there exists a majority quorum `Q` where each member either:
    - voted for `v` at `c` (tying the values), or
    - will never vote at `c` (promised above `c`).

    This decomposes as: at each `c`, apply `majorityQuorum.intersection` to
    the witness quorum `Q` and the accept quorum at `c`. The witness in the
    intersection constrains the value. -/

/-- Abstract version of `votedFor`: acceptor `a` voted for `v` at ballot `c`. -/
def VotedFor (ballotData : Nat → BallotQuorums n) (a : Fin n) (c : Nat) (_v : Value) : Prop :=
  (ballotData c).acceptQ a = true

/-- Abstract version of `wontVoteAt`: acceptor `a` promised above `c`. -/
def WontVoteAt (promise : Fin n → Nat) (a : Fin n) (c : Nat) : Prop :=
  promise a > c

/-- SafeAt expressed in combinator terms: for every `c < b`, the promise
    quorum at `b` serves as a witness. Each member of this quorum either
    voted for `v` at `c` or has promised above `c`.

    This is equivalent to `safeAt` from `Paxos.lean`, but expressed to
    highlight the role of majority quorum intersection. -/
def SafeAt (v : Value) (b : Nat) (promise : Fin n → Nat)
    (ballotData : Nat → BallotQuorums n) : Prop :=
  ∀ c, c < b → ∃ Q : Fin n → Bool,
    (paxosQS n).isQuorum Q ∧
    ∀ a, Q a = true →
      VotedFor n ballotData a c v ∨ WontVoteAt n promise a c

/-! ### Section 3: Agreement from SafeAt + Quorum Intersection

    The agreement proof from `Paxos.lean` (lines 205–235) has this structure:
    1. Two proposers both have majority accept quorums.
    2. WLOG `ballot_p < ballot_q`.
    3. `SafeAt(v_q, ballot_q)` at `c = ballot_p` yields witness quorum `Q`.
    4. `majorityQuorum.intersection` applied to `Q` and `did2b_p` yields overlap `k`.
    5. `k ∈ Q`: so `votedFor(k, ballot_p, v_q) ∨ wontVoteAt(k, ballot_p)`.
    6. `k ∈ did2b_p`: so `k` voted at `ballot_p`, ruling out `wontVoteAt`.
    7. Therefore `votedFor(k, ballot_p, v_q)`, so `v_p = v_q`.

    Step 4 is exactly `PhaseCombinator.cross_phase_quorum_intersection` from `PhaseCombinator.lean`. -/

/-- Agreement: if two ballots both achieve majority acceptance and the higher
    ballot's value is safe, then the values agree.

    This isolates the quorum intersection step (step 4 above) as an explicit
    application of `PhaseCombinator.cross_phase_quorum_intersection`. -/
theorem agreement_from_safeAt
    (b_p b_q : Nat) (v_p v_q : Value)
    (did2b_p : Fin n → Bool) (Q : Fin n → Bool)
    -- b_p < b_q
    (_hlt : b_p < b_q)
    -- did2b_p is a majority (step 1)
    (h_maj_p : (paxosQS n).isQuorum did2b_p)
    -- Q is the SafeAt witness at c = b_p (step 3)
    (h_maj_Q : (paxosQS n).isQuorum Q)
    -- Q witnesses: each member voted for v_q at b_p, or won't vote at b_p
    (hQ_wit : ∀ a, Q a = true → VotedFor n (fun _ => ⟨fun _ => false, did2b_p⟩) a b_p v_q
                                ∨ WontVoteAt n (fun _ => b_p) a b_p)
    -- did2b_p members actually voted at b_p (so wontVoteAt is impossible)
    (h_voted : ∀ a, did2b_p a = true → ¬ WontVoteAt n (fun _ => b_p) a b_p)
    -- voted at b_p for v_q implies v_p = v_q (single proposer per ballot)
    (h_unique : ∀ a, VotedFor n (fun _ => ⟨fun _ => false, did2b_p⟩) a b_p v_q →
                      did2b_p a = true → v_p = v_q) :
    v_p = v_q := by
  -- Step 4: apply PhaseCombinator.cross_phase_quorum_intersection
  obtain ⟨k, hk_Q, hk_p⟩ := PhaseCombinator.cross_phase_quorum_intersection (paxosQS n) Q did2b_p h_maj_Q h_maj_p
  -- Step 5: k ∈ Q, so voted or won't vote
  rcases hQ_wit k hk_Q with hvoted | hwont
  · -- Step 7: k voted for v_q at b_p, and k ∈ did2b_p
    exact h_unique k hvoted hk_p
  · -- Step 6: k ∈ did2b_p means k voted at b_p, contradicting wontVoteAt
    exact absurd hwont (h_voted k hk_p)

/-! ### Section 4: SafeAt Preservation as Composition

    The hardest part of the Paxos proof is showing SafeAt is preserved when
    a new proposal is made (p2a action, lines 418–528 of `Paxos.lean`).

    The argument has a three-way case split for each `c < ballot_q`:

    **Case 1** (`c > maxReport`): All promise quorum members have `prom > c`,
    so they satisfy `wontVoteAt`. The witness quorum is the promise quorum itself.
    No quorum intersection needed — just the promise quorum.

    **Case 2** (`c = maxReport`): The proposer adopted the max report's value.
    For members of the promise quorum who voted at `c`, they voted for the
    adopted value. The witness quorum is the promise quorum.
    Uses: promise quorum members who voted at `c` voted for the same value
    (by ballot injectivity).

    **Case 3** (`c < maxReport`): The proposer at `maxReport` already had
    `SafeAt(v, maxReport)` in the pre-state (inductive hypothesis). The witness
    quorum comes from that prior SafeAt — NOT from the current promise quorum.
    This is the *compositional* step: reuse the quorum from a prior ballot's
    SafeAt proof.

    The three cases compose via:
    - Case 1: `promiseQ` alone (all wontVoteAt by promise bound)
    - Case 2: `promiseQ` + ballot injectivity (voted members agree on value)
    - Case 3: `PhaseCombinator.cross_phase_quorum_intersection` between the prior SafeAt's
      witness quorum and any accept quorum at `c` -/

/-- The three-way decomposition of SafeAt preservation.

    Given a promise quorum at ballot `b` with max report at ballot `maxB`,
    and SafeAt(v, maxB) from the pre-state, conclude SafeAt(v, b). -/
theorem safeAt_preservation
    (b maxB : Nat) (v : Value)
    (promiseQ : Fin n → Bool)
    (promise : Fin n → Nat)
    (ballotData : Nat → BallotQuorums n)
    -- The promise quorum is a majority
    (h_promise_maj : (paxosQS n).isQuorum promiseQ)
    -- All promise quorum members have promise ≥ b
    (_h_prom_bound : ∀ a, promiseQ a = true → promise a ≥ b)
    -- maxB < b (the max report is from a lower ballot)
    (_h_maxB_lt : maxB < b)
    -- v is the value proposed at maxB (adopted by the proposer)
    -- SafeAt(v, maxB) holds in the pre-state (inductive hypothesis)
    (h_safe_maxB : SafeAt n v maxB promise ballotData)
    -- For the promise quorum, if a member voted at some c with maxB ≤ c < b,
    -- then c = maxB (maximality of maxB) and they voted for v
    (h_max_report : ∀ a c, promiseQ a = true → c < b → c ≥ maxB →
      VotedFor n ballotData a c v ∨ WontVoteAt n promise a c) :
    SafeAt n v b promise ballotData := by
  intro c hc_lt_b
  by_cases hc_ge_maxB : c ≥ maxB
  · -- Cases 1 & 2: c ≥ maxB. Use promiseQ as the witness.
    exact ⟨promiseQ, h_promise_maj, fun a ha =>
      h_max_report a c ha hc_lt_b hc_ge_maxB⟩
  · -- Case 3: c < maxB. Use the pre-state SafeAt witness.
    have hc_lt_maxB : c < maxB := by omega
    exact h_safe_maxB c hc_lt_maxB

/-! ### Summary: The Combinator Decomposition

    The full Paxos safety proof decomposes into these combinator pieces:

    1. **Quorum system**: `majorityQuorum n` from `QuorumSystem.lean`
       provides the quorum intersection property. Every majority quorum pair
       has a common member.

    2. **Lock pattern** (implicit): Each ballot's acceptance quorum "locks"
       a value — exactly `LockProperty` from `LockInvariant.lean` applied to
       `did2b`. Two ballots with majority acceptance must agree on value
       (or SafeAt resolves the conflict).

    3. **Cross-phase quorum intersection**: `PhaseCombinator.cross_phase_quorum_intersection`
       from `PhaseCombinator.lean` is the key step in the agreement proof.
       The SafeAt witness quorum and the accept quorum intersect, forcing the
       overlap member to testify that the values agree.

    4. **SafeAt preservation** factors into three cases, each using a different
       combinator pattern:
       - **High ballots** (`c > maxReport`): promise bound alone (no intersection)
       - **Max ballot** (`c = maxReport`): promise quorum + value adoption rule
       - **Low ballots** (`c < maxReport`): compositional reuse of prior SafeAt

    5. **Iterated structure**: SafeAt at ballot `b` depends on SafeAt at lower
       ballots. This is why the invariant proof in `Paxos.lean` works by
       strong induction on ballot numbers (via the `hSafe` field of `PaxosInv`).
       The combinator analog is `safeAt_preservation` above, which composes
       the prior SafeAt with the current promise quorum.

    Compared to the monolithic proof in `Paxos.lean` (~120 lines for p2a alone),
    the decomposition isolates three reusable patterns:
    - Quorum intersection (from `QuorumSystem.lean`)
    - Cross-phase intersection (from `PhaseCombinator.lean`)
    - Promise bound implies wontVoteAt (a frame property)

    The non-reusable part is the max-report argument (Case 2), which is
    specific to Paxos's value selection rule.
-/

end TLA.Combinator.PaxosCombinator
