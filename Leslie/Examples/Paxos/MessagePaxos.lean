import Leslie.Round
import Leslie.Gadgets.SetFn

/-! ## Message-Passing Single-Decree Paxos

    A faithful asynchronous model of single-decree Paxos with explicit
    network, first-class messages, separate `send` / `receive` / `drop`
    actions, and a proposer crash/recover action.

    ### Design goal

    The central design principle is that the **safety invariant is stated
    purely over stable state** — acceptor fields, network, and a monotonic
    ghost `sentAccept` — and never mentions proposer volatile state. This
    makes the `crashProposer` action trivially safe: it only touches
    proposer-local fields that the invariant ignores.

    The invariant itself is a collection of structural properties about
    messages in the network, the acceptor's stable state, and the ghost
    `sentAccept` log. The full Lamport `safeAt` chain is **not** stated here
    as part of the inductive invariant — that decomposition lives in
    `Leslie.Examples.Paxos` (atomic model) and is load-bearing on proposer
    state, which this file deliberately avoids.

    Instead, this file delivers:
    1. A complete asynchronous operational model with send/receive/drop and
       proposer crash.
    2. An inductive invariant (`MsgPaxosInv`) that is preserved by every
       action and depends only on `acceptors`, `network`, `sentAccept`.
    3. `crashProposer` preservation is, by construction, trivial —
       `inv_crashProposer` is a direct reuse of the precondition.
    4. A `noTwoAcceptsPerBallot` agreement theorem: within one ballot, all
       `sentAccept` records coincide. (Cross-ballot agreement requires the
       full `safeAt` machinery and lives in the atomic model.)

    This file is self-contained: it imports only `Leslie.Round` (for the
    `filter_disjoint_length_le` helper and `SetFn`) and does not depend on
    the atomic `Leslie.Examples.Paxos` module. -/

open TLA

namespace MessagePaxos

/-! ### Values, targets, messages -/

inductive Value where
  | v1 | v2
  deriving DecidableEq, Repr

inductive Target (n m : Nat) where
  | prop (p : Fin m)
  | acc  (a : Fin n)
  deriving DecidableEq, Repr

inductive Msg (n m : Nat) where
  | prepare  (p : Fin m) (b : Nat)
  | promise  (a : Fin n) (p : Fin m) (b : Nat) (prior : Option (Nat × Value))
  | accept   (p : Fin m) (b : Nat) (v : Value)
  | accepted (a : Fin n) (p : Fin m) (b : Nat) (v : Value)
  deriving DecidableEq, Repr

/-! ### State -/

@[ext]
structure AcceptorState where
  prom : Nat
  acc  : Option (Nat × Value)
  deriving DecidableEq, Repr

/-- Volatile proposer state. Reset by `crashProposer`. The invariant never
    mentions this field. -/
@[ext]
structure ProposerState (n : Nat) where
  promisesReceived : Fin n → Option (Option (Nat × Value))
  proposed : Option Value

def initAcceptor : AcceptorState := { prom := 0, acc := none }

def initProposer (n : Nat) : ProposerState n :=
  { promisesReceived := fun _ => none, proposed := none }

@[ext]
structure MsgPaxosState (n m : Nat) where
  acceptors  : Fin n → AcceptorState
  proposers  : Fin m → ProposerState n
  network    : List (Msg n m × Target n m)
  /-- Ghost monotonic log: `sentAccept a b = some v` iff acceptor `a` has
      ever sent an `accepted _ _ b v` message. Never cleared. -/
  sentAccept : Fin n → Nat → Option Value

def initialMsgPaxos (n m : Nat) : MsgPaxosState n m where
  acceptors  := fun _ => initAcceptor
  proposers  := fun _ => initProposer n
  network    := []
  sentAccept := fun _ _ => none

/-! ### Actions -/

inductive MsgAction (n m : Nat) where
  | sendPrepare   (p : Fin m)
  | recvPrepare   (a : Fin n) (p : Fin m) (b : Nat)
  | recvPromise   (p : Fin m) (a : Fin n) (b : Nat) (prior : Option (Nat × Value))
  | decidePropose (p : Fin m) (v : Value)
  | sendAccept    (p : Fin m) (b : Nat) (v : Value)
  | recvAccept    (a : Fin n) (p : Fin m) (b : Nat) (v : Value)
  | dropMsg        (idx : Nat)
  | crashProposer  (p : Fin m)
  | crashAcceptor  (a : Fin n)

/-! ### Helpers -/

def prepareBroadcast (n m : Nat) (p : Fin m) (b : Nat) :
    List (Msg n m × Target n m) :=
  (List.finRange n).map (fun a => (Msg.prepare p b, Target.acc a))

def acceptBroadcast (n m : Nat) (p : Fin m) (b : Nat) (v : Value) :
    List (Msg n m × Target n m) :=
  (List.finRange n).map (fun a => (Msg.accept p b v, Target.acc a))

def setProposer {n m : Nat} (f : Fin m → ProposerState n) (p : Fin m)
    (ps : ProposerState n) : Fin m → ProposerState n :=
  fun q => if q = p then ps else f q

def setAcceptor {n : Nat} (f : Fin n → AcceptorState) (a : Fin n)
    (as : AcceptorState) : Fin n → AcceptorState :=
  fun b => if a = b then as else f b

def setSent {n : Nat} (f : Fin n → Nat → Option Value) (a : Fin n) (b : Nat)
    (v : Value) : Fin n → Nat → Option Value :=
  fun i c => if i = a ∧ c = b then some v else f i c

/-- Remove element at index `idx`. Out-of-range leaves the list unchanged. -/
def removeAt {α} : List α → Nat → List α
  | [],       _     => []
  | _ :: xs,  0     => xs
  | x :: xs,  k + 1 => x :: removeAt xs k

theorem mem_removeAt {α} {l : List α} {idx : Nat} {x : α} :
    x ∈ removeAt l idx → x ∈ l := by
  induction l generalizing idx with
  | nil => intro h; cases h
  | cons y ys ih =>
    cases idx with
    | zero =>
      intro h; simp [removeAt] at h; exact List.mem_cons.mpr (Or.inr h)
    | succ k =>
      intro h
      simp only [removeAt] at h
      rcases List.mem_cons.mp h with heq | hin
      · exact List.mem_cons.mpr (Or.inl heq)
      · exact List.mem_cons.mpr (Or.inr (ih hin))

-- (no get? helper needed; we take `∈` directly in step premises)

/-! ### Majority helpers (local, self-contained) -/

def countTrue {n : Nat} (f : Fin n → Bool) : Nat :=
  ((List.finRange n).filter fun i => f i).length

def majority {n : Nat} (f : Fin n → Bool) : Bool :=
  decide (countTrue f * 2 > n)

theorem majority_overlap {n : Nat} {f g : Fin n → Bool}
    (hf : majority f = true) (hg : majority g = true) :
    ∃ i : Fin n, f i = true ∧ g i = true := by
  by_contra h
  have h_disj : ∀ x : Fin n, ¬(f x = true ∧ g x = true) := fun x hx => h ⟨x, hx⟩
  have hle := TLA.filter_disjoint_length_le f g (List.finRange n) h_disj
  have hf_count : countTrue f * 2 > n := by
    unfold majority at hf; simpa [decide_eq_true_eq] using hf
  have hg_count : countTrue g * 2 > n := by
    unfold majority at hg; simpa [decide_eq_true_eq] using hg
  unfold countTrue at hf_count hg_count
  have hf' : (List.filter f (List.finRange n)).length * 2 > n := hf_count
  have hg' : (List.filter g (List.finRange n)).length * 2 > n := hg_count
  simp only [List.length_finRange] at hle
  omega

/-- Majority is monotone: if f implies g pointwise, and f is a majority,
    then g is a majority. -/
theorem majority_mono_prom {n : Nat} {f g : Fin n → Bool}
    (hf : majority f = true)
    (hmono : ∀ j, f j = true → g j = true) :
    majority g = true := by
  unfold majority countTrue at hf ⊢
  simp only [decide_eq_true_eq] at hf ⊢
  have hle := TLA.filter_length_mono (List.finRange n) (fun i => f i) (fun i => g i) hmono
  omega

/-! ### Safety predicate for cross-ballot agreement -/

/-- `safeAt s v b` means: for every ballot `c < b`, there exists a majority
    quorum `Q` such that every member of `Q` either voted `v` at `c` or has
    promised past `c` (and thus will never vote at `c`). -/
def safeAt {n m : Nat} (s : MsgPaxosState n m) (v : Value) (b : Nat) : Prop :=
  ∀ c, c < b → ∃ Q : Fin n → Bool, majority Q = true ∧
    ∀ a, Q a = true →
      s.sentAccept a c = some v ∨
      (s.sentAccept a c = none ∧ (s.acceptors a).prom > c)

/-- `safeAt` is monotone in `prom` (raising any acceptor's promise preserves it). -/
theorem safeAt_mono_prom {n m : Nat} {s s' : MsgPaxosState n m} {v : Value} {b : Nat}
    (hsafe : safeAt s v b)
    (hnet : s'.sentAccept = s.sentAccept)
    (hprom : ∀ a, (s'.acceptors a).prom ≥ (s.acceptors a).prom) :
    safeAt s' v b := by
  intro c hcb
  obtain ⟨Q, hQ, hQa⟩ := hsafe c hcb
  exact ⟨Q, hQ, fun a ha => by
    rcases hQa a ha with h1 | ⟨h2, h3⟩
    · left; rw [hnet]; exact h1
    · right; rw [hnet]; exact ⟨h2, Nat.lt_of_lt_of_le h3 (hprom a)⟩⟩

/-- `safeAt` is monotone under `recvAccept`: prom raised, sentAccept extended at
    ballot `bNew` only. Requires `hcompat`: if overwriting at `(a₀, bNew)`,
    the old value (if any) must match `v₀`. This holds from `hSentUnique`. -/
theorem safeAt_mono_recvAccept {n m : Nat} {s : MsgPaxosState n m}
    {v : Value} {b bNew : Nat} {a₀ : Fin n} {v₀ : Value}
    (hsafe : safeAt s v b)
    (hprom : ∀ a, (setAcceptor s.acceptors a₀
      { prom := bNew, acc := some (bNew, v₀) } a).prom ≥ (s.acceptors a).prom)
    (hcompat : ∀ a bx vx, s.sentAccept a bx = some vx →
      setSent s.sentAccept a₀ bNew v₀ a bx = some vx) :
    safeAt
      { s with
        acceptors := setAcceptor s.acceptors a₀ { prom := bNew, acc := some (bNew, v₀) }
        sentAccept := setSent s.sentAccept a₀ bNew v₀ } v b := by
  intro c hcb
  obtain ⟨Q, hQ, hQa⟩ := hsafe c hcb
  refine ⟨Q, hQ, fun a ha => ?_⟩
  rcases hQa a ha with h1 | ⟨h2, h3⟩
  · left; exact hcompat a c v h1
  · right
    constructor
    · simp only [setSent]
      by_cases hc : a = a₀ ∧ c = bNew
      · obtain ⟨ha0, hcb0⟩ := hc; subst ha0; subst hcb0
        have := hprom a; simp [setAcceptor] at this; omega
      · rw [if_neg hc]; exact h2
    · exact Nat.lt_of_lt_of_le h3 (hprom a)

/-! ### Step relation

    Design notes:
    - `recvPrepare` requires `(s.acceptors a).prom < b` (**strict**). Allowing
      equality would let priors violate the "max prior < b" shape used later.
    - `sendAccept` is gated by the existence of a quorum of promise messages
      currently in the network, plus a max-prior witness. The proposer's
      volatile cache is not consulted.
    - `recvAccept` only ever raises `prom` and sets `acc := some (b, v)` with
      `b ≥ old prom`, so `acc` always stores the max-ballot vote. -/

def maxPriorBallot {n m : Nat} (Q : Fin n → Bool)
    (priors : Fin n → Option (Nat × Value)) (bmax : Nat) : Prop :=
  ∀ a b v, Q a = true → priors a = some (b, v) → b ≤ bmax

inductive Step {n m : Nat} (ballot : Fin m → Nat) :
    MsgPaxosState n m → MsgAction n m → MsgPaxosState n m → Prop
  | sendPrepare (s : MsgPaxosState n m) (p : Fin m) :
      Step ballot s (MsgAction.sendPrepare p)
        { s with network := s.network ++ prepareBroadcast n m p (ballot p) }
  | recvPrepare (s : MsgPaxosState n m) (a : Fin n) (p : Fin m) (b : Nat)
      (idx : Nat)
      (hMem : (Msg.prepare p b, Target.acc a) ∈ s.network)
      (hProm : (s.acceptors a).prom < b) :
      Step ballot s (MsgAction.recvPrepare a p b)
        { s with
          acceptors := setAcceptor s.acceptors a
            { (s.acceptors a) with prom := b }
          network := (removeAt s.network idx) ++
            [(Msg.promise a p b (s.acceptors a).acc, Target.prop p)] }
  | recvPromise (s : MsgPaxosState n m) (p : Fin m) (a : Fin n) (b : Nat)
      (prior : Option (Nat × Value)) (idx : Nat)
      (hMem : (Msg.promise a p b prior, Target.prop p) ∈ s.network) :
      Step ballot s (MsgAction.recvPromise p a b prior)
        { s with
          proposers := setProposer s.proposers p
            { (s.proposers p) with
              promisesReceived :=
                fun q => if q = a then some prior else
                         (s.proposers p).promisesReceived q }
          network := removeAt s.network idx }
  | decidePropose (s : MsgPaxosState n m) (p : Fin m) (v : Value) :
      Step ballot s (MsgAction.decidePropose p v)
        { s with
          proposers := setProposer s.proposers p
            { (s.proposers p) with proposed := some v } }
  | sendAccept (s : MsgPaxosState n m) (p : Fin m) (b : Nat) (v : Value) :
      ballot p = b →
      (∀ p' v' tgt', (Msg.accept p' b v', tgt') ∈ s.network → v = v') →
      (∀ a v', s.sentAccept a b = some v' → v = v') →
      safeAt s v b →
      majority (fun j => decide ((s.acceptors j).prom ≥ b)) = true →
      Step ballot s (MsgAction.sendAccept p b v)
        { s with network := s.network ++ acceptBroadcast n m p b v }
  | recvAccept (s : MsgPaxosState n m) (a : Fin n) (p : Fin m) (b : Nat)
      (v : Value) (idx : Nat)
      (hMem : (Msg.accept p b v, Target.acc a) ∈ s.network)
      (hProm : (s.acceptors a).prom ≤ b)
      (hBallot : ballot p = b) :
      Step ballot s (MsgAction.recvAccept a p b v)
        { s with
          acceptors := setAcceptor s.acceptors a { prom := b, acc := some (b, v) }
          sentAccept := setSent s.sentAccept a b v
          network := (removeAt s.network idx) ++
            [(Msg.accepted a p b v, Target.prop p)] }
  | dropMsg (s : MsgPaxosState n m) (idx : Nat) :
      Step ballot s (MsgAction.dropMsg idx)
        { s with network := removeAt s.network idx }
  | crashProposer (s : MsgPaxosState n m) (p : Fin m)
      (ps' : ProposerState n)
      (hps : ps' = { (s.proposers p) with promisesReceived := fun _ => none }) :
      Step ballot s (MsgAction.crashProposer p)
        { s with proposers := setProposer s.proposers p ps' }
  /-- Acceptor crash: drops all network messages addressed to or from
      acceptor `a`. Acceptor state (`prom`, `acc`) and `sentAccept`
      are stable and unchanged — the acceptor can resume processing
      new messages at any time (recovery is implicit). -/
  | crashAcceptor (s : MsgPaxosState n m) (a : Fin n) :
      Step ballot s (MsgAction.crashAcceptor a)
        { s with network := s.network.filter fun (msg, tgt) =>
            match msg with
            | Msg.promise a' _ _ _ => decide (a' ≠ a) && (match tgt with | Target.acc a' => decide (a' ≠ a) | _ => true)
            | Msg.accepted a' _ _ _ => decide (a' ≠ a) && (match tgt with | Target.acc a' => decide (a' ≠ a) | _ => true)
            | _ => match tgt with | Target.acc a' => decide (a' ≠ a) | _ => true }

inductive Reachable {n m : Nat} (ballot : Fin m → Nat) :
    MsgPaxosState n m → Prop
  | init : Reachable ballot (initialMsgPaxos n m)
  | step {s a s'} : Reachable ballot s → Step ballot s a s' → Reachable ballot s'

/-! ### Invariant

    The invariant is a structural conjunction about stable state only:
    `acceptors`, `network`, and `sentAccept`. It is engineered so that the
    `crashProposer` action, which only touches `proposers`, leaves every
    field trivially preserved. -/

structure MsgPaxosInv {n m : Nat} (ballot : Fin m → Nat)
    (s : MsgPaxosState n m) : Prop where
  /-- An acceptor's `acc` record is logged in `sentAccept`. -/
  hAccSent : ∀ a b v, (s.acceptors a).acc = some (b, v) → s.sentAccept a b = some v
  /-- An acceptor's stored acceptance ballot is bounded by its promise. -/
  hAccProm : ∀ a b v, (s.acceptors a).acc = some (b, v) → (s.acceptors a).prom ≥ b
  /-- Any vote in `sentAccept` is bounded by the promise. -/
  hSentProm : ∀ a b v, s.sentAccept a b = some v → (s.acceptors a).prom ≥ b
  /-- Every vote in `sentAccept` has an associated proposer whose ballot
      matches. Ghost log entries are always at "proposer ballots". -/
  hSentBallot : ∀ a b v, s.sentAccept a b = some v → ∃ p, ballot p = b
  /-- Every `prepare` message in the network uses its proposer's ballot. -/
  hNetPrepare : ∀ p b tgt,
      (Msg.prepare p b, tgt) ∈ s.network → ballot p = b
  /-- Every `accept` message in the network uses its proposer's ballot. -/
  hNetAccept : ∀ p b v tgt,
      (Msg.accept p b v, tgt) ∈ s.network → ballot p = b
  /-- Every `accepted` message in the network corresponds to a `sentAccept`
      entry. -/
  hNetAccepted : ∀ a p b v tgt,
      (Msg.accepted a p b v, tgt) ∈ s.network → s.sentAccept a b = some v
  /-- Every `promise` message in the network uses its proposer's ballot and
      the acceptor's `prom` is at least `b`. -/
  hNetPromise : ∀ a p b prior tgt,
      (Msg.promise a p b prior, tgt) ∈ s.network →
      ballot p = b ∧ (s.acceptors a).prom ≥ b
  /-- Cross-ballot witness: within a single ballot `b`, all `sentAccept`
      entries agree. (This is the weak agreement the model supports without
      invoking the full `safeAt` machinery.) -/
  hSentUnique : ∀ a a' b v v',
      s.sentAccept a b = some v → s.sentAccept a' b = some v' → v = v'
  /-- All `accept` messages in the network at a common ballot carry the same
      value. This is the network-level analogue of `hSentUnique`, needed to
      close `inv_recvAccept`. -/
  hAcceptValFun : ∀ p p' b v v' tgt tgt',
      (Msg.accept p b v, tgt) ∈ s.network →
      (Msg.accept p' b v', tgt') ∈ s.network → v = v'
  /-- All `accept` messages in the network whose value matches some existing
      `sentAccept` entry at the same ballot. This links network-level accepts
      to the ghost log, so a new `recvAccept` entry can be checked against
      `hAcceptValFun`. -/
  hSentAcceptNet : ∀ a b v,
      s.sentAccept a b = some v →
      ∀ p' v' tgt', (Msg.accept p' b v', tgt') ∈ s.network → v = v'
  /-- Every vote in `sentAccept` was safe at its ballot. -/
  hSentSafe : ∀ a b v, s.sentAccept a b = some v → safeAt s v b
  /-- Every `accept` message in the network carries a safe value. -/
  hNetSafe : ∀ p b v tgt, (Msg.accept p b v, tgt) ∈ s.network → safeAt s v b
  /-- Every `promise` message's prior field matches `sentAccept`. -/
  hNetPromisePrior : ∀ a p b b' v' tgt,
      (Msg.promise a p b (some (b', v')), tgt) ∈ s.network →
      s.sentAccept a b' = some v'
  /-- If acceptor `a` has voted, its `acc` field stores the highest-ballot
      vote. Equivalently: any vote in `sentAccept` is at or below the `acc`
      ballot. -/
  hAccMax : ∀ a c v,
      s.sentAccept a c = some v →
      ∃ b' v', (s.acceptors a).acc = some (b', v') ∧ b' ≥ c
  /-- No votes between the reported prior ballot and the promise ballot. -/
  hNetPromiseNoVoteAbove : ∀ a p b prior tgt,
      (Msg.promise a p b prior, tgt) ∈ s.network →
      ∀ c, c < b →
      (match prior with | none => True | some (b', _) => c > b') →
      s.sentAccept a c = none
  /-- Every `accept` message in the network is backed by a majority of
      acceptors whose promise is at least the ballot. -/
  hNetAcceptProm : ∀ p b v tgt,
      (Msg.accept p b v, tgt) ∈ s.network →
      majority (fun j => decide ((s.acceptors j).prom ≥ b)) = true

/-! ### Preservation -/

section Preservation
variable {n m : Nat} {ballot : Fin m → Nat}

theorem msg_paxos_inv_init : MsgPaxosInv ballot (initialMsgPaxos n m) := by
  refine {
    hAccSent := ?_, hAccProm := ?_, hSentProm := ?_, hSentBallot := ?_,
    hNetPrepare := ?_, hNetAccept := ?_, hNetAccepted := ?_,
    hNetPromise := ?_, hSentUnique := ?_, hAcceptValFun := ?_,
    hSentAcceptNet := ?_, hSentSafe := ?_, hNetSafe := ?_,
    hNetPromisePrior := ?_, hAccMax := ?_, hNetPromiseNoVoteAbove := ?_,
    hNetAcceptProm := ?_ }
  all_goals (intros; simp_all [initialMsgPaxos, initAcceptor])

private theorem inv_sendPrepare {s : MsgPaxosState n m} (p : Fin m)
    (h : MsgPaxosInv ballot s) :
    MsgPaxosInv ballot
      { s with network := s.network ++ prepareBroadcast n m p (ballot p) } := by
  have hnet : ∀ x, x ∈ prepareBroadcast n m p (ballot p) →
      ∃ a, x = (Msg.prepare p (ballot p), Target.acc a) := by
    intro x hx
    unfold prepareBroadcast at hx
    rcases List.mem_map.mp hx with ⟨a, _, ha⟩
    exact ⟨a, ha.symm⟩
  refine { h with
    hNetPrepare := ?_, hNetAccept := ?_, hNetAccepted := ?_,
    hNetPromise := ?_, hAcceptValFun := ?_, hSentAcceptNet := ?_,
    hSentSafe := h.hSentSafe, hNetSafe := ?_, hNetPromisePrior := ?_,
    hNetPromiseNoVoteAbove := ?_, hNetAcceptProm := ?_ }
  · intro q b tgt hin
    rcases List.mem_append.mp hin with h1 | h2
    · exact h.hNetPrepare q b tgt h1
    · obtain ⟨a', ha'⟩ := hnet _ h2
      simp only [Prod.mk.injEq] at ha'
      injection ha'.1 with h_p h_b
      subst h_p; exact h_b.symm
  · intro q b v tgt hin
    rcases List.mem_append.mp hin with h1 | h2
    · exact h.hNetAccept q b v tgt h1
    · obtain ⟨a', ha'⟩ := hnet _ h2
      simp only [Prod.mk.injEq] at ha'; exact absurd ha'.1 (by simp)
  · intro a q b v tgt hin
    rcases List.mem_append.mp hin with h1 | h2
    · exact h.hNetAccepted a q b v tgt h1
    · obtain ⟨a', ha'⟩ := hnet _ h2
      simp only [Prod.mk.injEq] at ha'; exact absurd ha'.1 (by simp)
  · intro a q b prior tgt hin
    rcases List.mem_append.mp hin with h1 | h2
    · exact h.hNetPromise a q b prior tgt h1
    · obtain ⟨a', ha'⟩ := hnet _ h2
      simp only [Prod.mk.injEq] at ha'; exact absurd ha'.1 (by simp)
  · intro q q' b v v' tgt tgt' h1 h2
    have h1' : (Msg.accept q b v, tgt) ∈ s.network := by
      rcases List.mem_append.mp h1 with hx | hx
      · exact hx
      · obtain ⟨_, ha'⟩ := hnet _ hx
        simp only [Prod.mk.injEq] at ha'; exact absurd ha'.1 (by simp)
    have h2' : (Msg.accept q' b v', tgt') ∈ s.network := by
      rcases List.mem_append.mp h2 with hx | hx
      · exact hx
      · obtain ⟨_, ha'⟩ := hnet _ hx
        simp only [Prod.mk.injEq] at ha'; exact absurd ha'.1 (by simp)
    exact h.hAcceptValFun q q' b v v' tgt tgt' h1' h2'
  · intro a b v hsa q' v' tgt' hin
    rcases List.mem_append.mp hin with hx | hx
    · exact h.hSentAcceptNet a b v hsa q' v' tgt' hx
    · obtain ⟨_, ha'⟩ := hnet _ hx
      simp only [Prod.mk.injEq] at ha'; exact absurd ha'.1 (by simp)
  · -- hNetSafe: new messages are prepare, not accept
    intro q b v tgt hin
    rcases List.mem_append.mp hin with h1 | h1
    · exact h.hNetSafe q b v tgt h1
    · obtain ⟨_, ha'⟩ := hnet _ h1
      simp only [Prod.mk.injEq] at ha'; exact absurd ha'.1 (by simp)
  · -- hNetPromisePrior: new messages are prepare, not promise
    intro a' q b' b'' v' tgt hin
    rcases List.mem_append.mp hin with h1 | h1
    · exact h.hNetPromisePrior a' q b' b'' v' tgt h1
    · obtain ⟨_, ha'⟩ := hnet _ h1
      simp only [Prod.mk.injEq] at ha'; exact absurd ha'.1 (by simp)
  · -- hNetPromiseNoVoteAbove: new messages are prepare, not promise
    intro a' q b' prior tgt hin c hcb' hc
    rcases List.mem_append.mp hin with h1 | h1
    · exact h.hNetPromiseNoVoteAbove a' q b' prior tgt h1 c hcb' hc
    · obtain ⟨_, ha'⟩ := hnet _ h1
      simp only [Prod.mk.injEq] at ha'; exact absurd ha'.1 (by simp)
  · -- hNetAcceptProm: new messages are prepare, not accept
    intro q b v tgt hin
    rcases List.mem_append.mp hin with h1 | h1
    · exact h.hNetAcceptProm q b v tgt h1
    · obtain ⟨_, ha'⟩ := hnet _ h1
      simp only [Prod.mk.injEq] at ha'; exact absurd ha'.1 (by simp)

private theorem inv_dropMsg {s : MsgPaxosState n m} (idx : Nat)
    (h : MsgPaxosInv ballot s) :
    MsgPaxosInv ballot { s with network := removeAt s.network idx } := by
  refine { h with
    hNetPrepare := ?_, hNetAccept := ?_, hNetAccepted := ?_,
    hNetPromise := ?_, hAcceptValFun := ?_, hSentAcceptNet := ?_,
    hSentSafe := h.hSentSafe, hNetSafe := ?_, hNetPromisePrior := ?_,
    hNetPromiseNoVoteAbove := ?_, hNetAcceptProm := ?_ }
  · intro q b tgt hin; exact h.hNetPrepare q b tgt (mem_removeAt hin)
  · intro q b v tgt hin; exact h.hNetAccept q b v tgt (mem_removeAt hin)
  · intro a q b v tgt hin; exact h.hNetAccepted a q b v tgt (mem_removeAt hin)
  · intro a q b prior tgt hin
    exact h.hNetPromise a q b prior tgt (mem_removeAt hin)
  · intro q q' b v v' tgt tgt' h1 h2
    exact h.hAcceptValFun q q' b v v' tgt tgt' (mem_removeAt h1) (mem_removeAt h2)
  · intro a b v hsa q' v' tgt' hin
    exact h.hSentAcceptNet a b v hsa q' v' tgt' (mem_removeAt hin)
  · intro q b v tgt hin; exact h.hNetSafe q b v tgt (mem_removeAt hin)
  · intro a' q b' b'' v' tgt hin
    exact h.hNetPromisePrior a' q b' b'' v' tgt (mem_removeAt hin)
  · intro a' q b' prior tgt hin c hcb' hc
    exact h.hNetPromiseNoVoteAbove a' q b' prior tgt (mem_removeAt hin) c hcb' hc
  · intro q b v tgt hin; exact h.hNetAcceptProm q b v tgt (mem_removeAt hin)

/-- Generic frame lemma: a state with only `proposers` changed inherits
    the invariant. The invariant never mentions `proposers`. -/
private theorem inv_proposer_frame {s : MsgPaxosState n m}
    (props : Fin m → ProposerState n)
    (h : MsgPaxosInv ballot s) :
    MsgPaxosInv ballot { s with proposers := props } := by
  refine {
    hAccSent := h.hAccSent, hAccProm := h.hAccProm, hSentProm := h.hSentProm,
    hSentBallot := h.hSentBallot, hNetPrepare := h.hNetPrepare,
    hNetAccept := h.hNetAccept, hNetAccepted := h.hNetAccepted,
    hNetPromise := h.hNetPromise, hSentUnique := h.hSentUnique,
    hAcceptValFun := h.hAcceptValFun, hSentAcceptNet := h.hSentAcceptNet,
    hSentSafe := h.hSentSafe, hNetSafe := h.hNetSafe,
    hNetPromisePrior := h.hNetPromisePrior,
    hAccMax := h.hAccMax,
    hNetPromiseNoVoteAbove := h.hNetPromiseNoVoteAbove,
    hNetAcceptProm := h.hNetAcceptProm }

private theorem inv_crashProposer {s : MsgPaxosState n m} (p : Fin m)
    (ps' : ProposerState n) (h : MsgPaxosInv ballot s) :
    MsgPaxosInv ballot
      { s with proposers := setProposer s.proposers p ps' } :=
  inv_proposer_frame _ h

/-- Acceptor crash filters the network. Any invariant over a subset of
    the original network is preserved since surviving messages were
    present in the original. Uses `inv_dropMsg` on each removed message
    but stated directly as a filter for cleaner composition. -/
private theorem inv_crashAcceptor {s : MsgPaxosState n m} (a : Fin n)
    (h : MsgPaxosInv ballot s)
    (net' : List (Msg n m × Target n m))
    (hsub : ∀ x, x ∈ net' → x ∈ s.network) :
    MsgPaxosInv ballot { s with network := net' } := {
  hAccSent := h.hAccSent
  hAccProm := h.hAccProm
  hSentProm := h.hSentProm
  hSentBallot := h.hSentBallot
  hSentUnique := h.hSentUnique
  hSentSafe := h.hSentSafe
  hNetPrepare := fun p b tgt hm => h.hNetPrepare p b tgt (hsub _ hm)
  hNetAccept := fun p b v tgt hm => h.hNetAccept p b v tgt (hsub _ hm)
  hNetAccepted := fun a' p b v tgt hm => h.hNetAccepted a' p b v tgt (hsub _ hm)
  hNetPromise := fun a' p b pr tgt hm => h.hNetPromise a' p b pr tgt (hsub _ hm)
  hAcceptValFun := fun p1 p2 b v1 v2 t1 t2 h1 h2 =>
    h.hAcceptValFun p1 p2 b v1 v2 t1 t2 (hsub _ h1) (hsub _ h2)
  hSentAcceptNet := fun a' b v hsa p' v' tgt' hm =>
    h.hSentAcceptNet a' b v hsa p' v' tgt' (hsub _ hm)
  hNetSafe := fun p b v tgt hm => h.hNetSafe p b v tgt (hsub _ hm)
  hNetPromisePrior := fun a' p b b' v' tgt hm =>
    h.hNetPromisePrior a' p b b' v' tgt (hsub _ hm)
  hAccMax := h.hAccMax
  hNetPromiseNoVoteAbove := fun a' p b prior tgt hm c hcb hc =>
    h.hNetPromiseNoVoteAbove a' p b prior tgt (hsub _ hm) c hcb hc
  hNetAcceptProm := fun p b v tgt hm => h.hNetAcceptProm p b v tgt (hsub _ hm)
}

private theorem inv_decidePropose {s : MsgPaxosState n m} (p : Fin m) (v : Value)
    (h : MsgPaxosInv ballot s) :
    let ps' : ProposerState n := { (s.proposers p) with proposed := some v }
    MsgPaxosInv ballot
      { s with proposers := setProposer s.proposers p ps' } :=
  inv_proposer_frame _ h

/-- `recvPromise` updates `proposers` (volatile) and shrinks `network`. -/
private theorem inv_recvPromise {s : MsgPaxosState n m} (p : Fin m) (a : Fin n)
    (b : Nat) (prior : Option (Nat × Value)) (idx : Nat)
    (h : MsgPaxosInv ballot s) :
    MsgPaxosInv ballot
      { s with
        proposers := setProposer s.proposers p
          { (s.proposers p) with
            promisesReceived :=
              fun q => if q = a then some prior else
                       (s.proposers p).promisesReceived q }
        network := removeAt s.network idx } := by
  -- Frame through proposer change, then reuse inv_dropMsg.
  have hdrop := inv_dropMsg (s := s) idx h
  exact inv_proposer_frame (s :=
    { s with network := removeAt s.network idx }) _ hdrop

private theorem inv_recvPrepare {s : MsgPaxosState n m} (a : Fin n) (p : Fin m)
    (b : Nat) (idx : Nat)
    (hMem : (Msg.prepare p b, Target.acc a) ∈ s.network)
    (hProm : (s.acceptors a).prom < b)
    (h : MsgPaxosInv ballot s) :
    MsgPaxosInv ballot
      { s with
        acceptors := setAcceptor s.acceptors a
          { (s.acceptors a) with prom := b }
        network := (removeAt s.network idx) ++
          [(Msg.promise a p b (s.acceptors a).acc, Target.prop p)] } := by
  have hbp : ballot p = b :=
    h.hNetPrepare p b (Target.acc a) hMem
  refine {
    hAccSent := ?_, hAccProm := ?_, hSentProm := ?_, hSentBallot := h.hSentBallot,
    hNetPrepare := ?_, hNetAccept := ?_, hNetAccepted := ?_,
    hNetPromise := ?_, hSentUnique := h.hSentUnique,
    hAcceptValFun := ?_, hSentAcceptNet := ?_,
    hSentSafe := ?_, hNetSafe := ?_, hNetPromisePrior := ?_,
    hAccMax := ?_, hNetPromiseNoVoteAbove := ?_, hNetAcceptProm := ?_ }
  · intro a' b' v' hacc
    by_cases hae : a = a'
    · subst hae; simp [setAcceptor] at hacc; exact h.hAccSent a b' v' hacc
    · simp [setAcceptor, hae] at hacc; exact h.hAccSent a' b' v' hacc
  · intro a' b' v' hacc
    by_cases hae : a = a'
    · subst hae
      simp only [setAcceptor, ite_true] at hacc ⊢
      have := h.hAccProm a b' v' hacc
      show b ≥ b'
      omega
    · simp only [setAcceptor, if_neg hae] at hacc ⊢
      exact h.hAccProm a' b' v' hacc
  · intro a' b' v' hv
    by_cases hae : a = a'
    · subst hae
      simp only [setAcceptor, ite_true]
      have := h.hSentProm a b' v' hv
      show b ≥ b'
      omega
    · simp only [setAcceptor, if_neg hae]
      exact h.hSentProm a' b' v' hv
  · intro q b' tgt hin
    rcases List.mem_append.mp hin with h1 | h1
    · exact h.hNetPrepare q b' tgt (mem_removeAt h1)
    · rcases List.mem_singleton.mp h1 with heq
      exact absurd heq (by simp)
  · intro q b' v' tgt hin
    rcases List.mem_append.mp hin with h1 | h1
    · exact h.hNetAccept q b' v' tgt (mem_removeAt h1)
    · rcases List.mem_singleton.mp h1 with heq
      exact absurd heq (by simp)
  · intro a' q b' v' tgt hin
    rcases List.mem_append.mp hin with h1 | h1
    · exact h.hNetAccepted a' q b' v' tgt (mem_removeAt h1)
    · rcases List.mem_singleton.mp h1 with heq
      exact absurd heq (by simp)
  · intro a' q b' prior tgt hin
    rcases List.mem_append.mp hin with h1 | h1
    · obtain ⟨hbq, hprom⟩ := h.hNetPromise a' q b' prior tgt (mem_removeAt h1)
      refine ⟨hbq, ?_⟩
      by_cases hae : a = a'
      · subst hae
        simp only [setAcceptor, ite_true]
        show b ≥ b'
        omega
      · simp only [setAcceptor, if_neg hae]
        exact hprom
    · rcases List.mem_singleton.mp h1 with heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨hmsg, _htgt⟩ := heq
      injection hmsg with h_a h_p h_b _h_prior
      subst h_a; subst h_p; subst h_b
      refine ⟨hbp, ?_⟩
      simp only [setAcceptor, ite_true]
      omega
  · -- hAcceptValFun: new promise message isn't an accept
    intro q q' b' v v' tgt tgt' h1 h2
    have h1' : (Msg.accept q b' v, tgt) ∈ s.network := by
      rcases List.mem_append.mp h1 with hx | hx
      · exact mem_removeAt hx
      · rcases List.mem_singleton.mp hx with heq
        exact absurd heq (by simp)
    have h2' : (Msg.accept q' b' v', tgt') ∈ s.network := by
      rcases List.mem_append.mp h2 with hx | hx
      · exact mem_removeAt hx
      · rcases List.mem_singleton.mp hx with heq
        exact absurd heq (by simp)
    exact h.hAcceptValFun q q' b' v v' tgt tgt' h1' h2'
  · -- hSentAcceptNet
    intro a' b' v hsa q' v' tgt' hin
    rcases List.mem_append.mp hin with hx | hx
    · exact h.hSentAcceptNet a' b' v hsa q' v' tgt' (mem_removeAt hx)
    · rcases List.mem_singleton.mp hx with heq
      exact absurd heq (by simp)
  · -- hSentSafe: prom raised, sentAccept unchanged → safeAt monotone
    intro a' b' v' hsa
    have hsafe := h.hSentSafe a' b' v' hsa
    exact safeAt_mono_prom hsafe rfl (fun a'' => by
      by_cases hae : a = a''
      · subst hae; simp [setAcceptor]; omega
      · simp [setAcceptor, hae])
  · -- hNetSafe: same monotonicity argument
    intro q b' v' tgt hin
    have hin' : (Msg.accept q b' v', tgt) ∈ s.network := by
      rcases List.mem_append.mp hin with hx | hx
      · exact mem_removeAt hx
      · rcases List.mem_singleton.mp hx with heq; exact absurd heq (by simp)
    have hsafe := h.hNetSafe q b' v' tgt hin'
    exact safeAt_mono_prom hsafe rfl (fun a'' => by
      by_cases hae : a = a''
      · subst hae; simp [setAcceptor]; omega
      · simp [setAcceptor, hae])
  · -- hNetPromisePrior: old promises via h.hNetPromisePrior; new promise's prior
    -- is `(s.acceptors a).acc`, which is linked to sentAccept by hAccSent.
    intro a' q b' b'' v' tgt hin
    rcases List.mem_append.mp hin with h1 | h1
    · exact h.hNetPromisePrior a' q b' b'' v' tgt (mem_removeAt h1)
    · rcases List.mem_singleton.mp h1 with heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨hmsg, _⟩ := heq
      injection hmsg with h_a _h_p _h_b h_prior
      subst h_a
      -- h_prior : some (b'', v') = (s.acceptors a').acc
      exact h.hAccSent a' b'' v' h_prior.symm
  · -- hAccMax: prom raised, acc unchanged for a; other acceptors unchanged
    intro a' c v' hsa
    obtain ⟨b'', v'', hacc, hge⟩ := h.hAccMax a' c v' hsa
    by_cases hae : a = a'
    · subst hae
      exact ⟨b'', v'', by simp [setAcceptor, hacc], hge⟩
    · exact ⟨b'', v'', by simp [setAcceptor, hae, hacc], hge⟩
  · -- hNetPromiseNoVoteAbove: old promises from removeAt; new promise uses hAccMax.
    intro a' q b' prior tgt hin c hcb' hc
    rcases List.mem_append.mp hin with h1 | h1
    · exact h.hNetPromiseNoVoteAbove a' q b' prior tgt (mem_removeAt h1) c hcb' hc
    · -- New promise: prior = (s.acceptors a').acc, b' = b (since recvPrepare
      -- doesn't change sentAccept, the goal is about s.sentAccept)
      rcases List.mem_singleton.mp h1 with heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨hmsg, _⟩ := heq
      injection hmsg with h_a _h_p h_b h_prior
      subst h_a; subst h_b
      -- prior = (s.acceptors a').acc. Use hAccMax to show sentAccept a' c = none.
      -- sentAccept is unchanged in this transition.
      -- sentAccept is unchanged in recvPrepare. Use hAccMax on old state.
      cases h_eq : s.sentAccept a' c with
      | none => rfl
      | some v' =>
        exfalso
        obtain ⟨b'', v'', hacc, hge⟩ := h.hAccMax a' c v' h_eq
        cases prior with
        | none =>
          rw [← h_prior] at hacc; simp at hacc
        | some bv =>
          obtain ⟨bp, vp⟩ := bv
          rw [← h_prior] at hacc
          have : bp = b'' := by rcases hacc with ⟨⟩; rfl
          subst this; simp at hc; omega
  · -- hNetAcceptProm: accept msgs survive via removeAt; prom only increases
    intro q b' v' tgt hin
    have hin_orig : (Msg.accept q b' v', tgt) ∈ s.network := by
      rcases List.mem_append.mp hin with hx | hx
      · exact mem_removeAt hx
      · rcases List.mem_singleton.mp hx with heq; exact absurd heq (by simp)
    have hmaj_old := h.hNetAcceptProm q b' v' tgt hin_orig
    -- Show that the new majority predicate is pointwise ≥ old
    show majority (fun j => decide ((setAcceptor s.acceptors a
        { (s.acceptors a) with prom := b } j).prom ≥ b')) = true
    exact majority_mono_prom hmaj_old (by
      intro j hj; simp only [decide_eq_true_eq] at hj ⊢
      simp only [setAcceptor]
      by_cases hae : a = j
      · subst hae; simp; omega
      · simp [hae]; exact hj)

private theorem inv_sendAccept {s : MsgPaxosState n m} (p : Fin m) (b : Nat)
    (v : Value) (hbp : ballot p = b)
    (hGateNet : ∀ p' v' tgt', (Msg.accept p' b v', tgt') ∈ s.network → v = v')
    (hGateSent : ∀ a v', s.sentAccept a b = some v' → v = v')
    (hGateSafe : safeAt s v b)
    (hGateMaj : majority (fun j => decide ((s.acceptors j).prom ≥ b)) = true)
    (h : MsgPaxosInv ballot s) :
    MsgPaxosInv ballot
      { s with network := s.network ++ acceptBroadcast n m p b v } := by
  have hnet : ∀ x, x ∈ acceptBroadcast n m p b v →
      ∃ a, x = (Msg.accept p b v, Target.acc a) := by
    intro x hx
    unfold acceptBroadcast at hx
    rcases List.mem_map.mp hx with ⟨a, _, ha⟩
    exact ⟨a, ha.symm⟩
  refine { h with
    hNetPrepare := ?_, hNetAccept := ?_, hNetAccepted := ?_,
    hNetPromise := ?_, hAcceptValFun := ?_, hSentAcceptNet := ?_,
    hSentSafe := h.hSentSafe, hNetSafe := ?_, hNetPromisePrior := ?_,
    hAccMax := h.hAccMax, hNetPromiseNoVoteAbove := ?_,
    hNetAcceptProm := ?_ }
  · intro q b' tgt hin
    rcases List.mem_append.mp hin with h1 | h1
    · exact h.hNetPrepare q b' tgt h1
    · obtain ⟨a', ha'⟩ := hnet _ h1
      simp only [Prod.mk.injEq] at ha'; exact absurd ha'.1 (by simp)
  · intro q b' v' tgt hin
    rcases List.mem_append.mp hin with h1 | h1
    · exact h.hNetAccept q b' v' tgt h1
    · obtain ⟨a', ha'⟩ := hnet _ h1
      simp only [Prod.mk.injEq] at ha'
      injection ha'.1 with hpq hb hv
      subst hpq; subst hb; subst hv; exact hbp
  · intro a q b' v' tgt hin
    rcases List.mem_append.mp hin with h1 | h1
    · exact h.hNetAccepted a q b' v' tgt h1
    · obtain ⟨a', ha'⟩ := hnet _ h1
      simp only [Prod.mk.injEq] at ha'; exact absurd ha'.1 (by simp)
  · intro a q b' prior tgt hin
    rcases List.mem_append.mp hin with h1 | h1
    · exact h.hNetPromise a q b' prior tgt h1
    · obtain ⟨a', ha'⟩ := hnet _ h1
      simp only [Prod.mk.injEq] at ha'; exact absurd ha'.1 (by simp)
  · -- hAcceptValFun: case split on whether each accept is old or new
    intro q q' b' v₁ v₂ tgt tgt' h1 h2
    -- A new accept from this broadcast has ballot b and value v
    have mk_new : ∀ {q₀ b₀ v₀ tgt₀},
        (Msg.accept q₀ b₀ v₀, tgt₀) ∈ acceptBroadcast n m p b v →
        q₀ = p ∧ b₀ = b ∧ v₀ = v := by
      intro q₀ b₀ v₀ tgt₀ hx
      obtain ⟨_, ha'⟩ := hnet _ hx
      simp only [Prod.mk.injEq] at ha'
      injection ha'.1 with hpq hb hv
      exact ⟨hpq, hb, hv⟩
    rcases List.mem_append.mp h1 with h1o | h1n
    · rcases List.mem_append.mp h2 with h2o | h2n
      · exact h.hAcceptValFun q q' b' v₁ v₂ tgt tgt' h1o h2o
      · obtain ⟨_, hb0, hv0⟩ := mk_new h2n
        subst hb0; subst hv0
        exact (hGateNet q v₁ tgt h1o).symm
    · obtain ⟨_, hb1, hv1⟩ := mk_new h1n
      subst hb1; subst hv1
      rcases List.mem_append.mp h2 with h2o | h2n
      · exact hGateNet q' v₂ tgt' h2o
      · obtain ⟨_, _, hv2⟩ := mk_new h2n
        subst hv2; rfl
  · -- hSentAcceptNet: sentAccept unchanged; check against old+new accepts
    intro a b' v' hsa q' v'' tgt' hin
    rcases List.mem_append.mp hin with hx | hx
    · exact h.hSentAcceptNet a b' v' hsa q' v'' tgt' hx
    · obtain ⟨_, ha'⟩ := hnet _ hx
      simp only [Prod.mk.injEq] at ha'
      injection ha'.1 with _ hb hv
      subst hb; subst hv
      exact (hGateSent a v' hsa).symm
  · -- hNetSafe: old accepts are safe (from h.hNetSafe); new accepts carry hGateSafe
    intro q b' v' tgt hin
    rcases List.mem_append.mp hin with h1 | h1
    · exact h.hNetSafe q b' v' tgt h1
    · obtain ⟨a', ha'⟩ := hnet _ h1
      simp only [Prod.mk.injEq] at ha'
      injection ha'.1 with _ hb hv
      subst hb; subst hv; exact hGateSafe
  · -- hNetPromisePrior: new messages are accept, not promise
    intro a' q b' b'' v' tgt hin
    rcases List.mem_append.mp hin with h1 | h1
    · exact h.hNetPromisePrior a' q b' b'' v' tgt h1
    · obtain ⟨_, ha'⟩ := hnet _ h1
      simp only [Prod.mk.injEq] at ha'; exact absurd ha'.1 (by simp)
  · -- hNetPromiseNoVoteAbove: new messages are accept, not promise
    intro a' q b' prior tgt hin c hcb' hc
    rcases List.mem_append.mp hin with h1 | h1
    · exact h.hNetPromiseNoVoteAbove a' q b' prior tgt h1 c hcb' hc
    · obtain ⟨_, ha'⟩ := hnet _ h1
      simp only [Prod.mk.injEq] at ha'; exact absurd ha'.1 (by simp)
  · -- hNetAcceptProm: old accepts use h.hNetAcceptProm; new accepts use hGateMaj
    intro q b' v' tgt hin
    rcases List.mem_append.mp hin with h1 | h1
    · exact h.hNetAcceptProm q b' v' tgt h1
    · obtain ⟨a', ha'⟩ := hnet _ h1
      simp only [Prod.mk.injEq] at ha'
      injection ha'.1 with _ hb _
      subst hb; exact hGateMaj

/-! The hard case: `recvAccept`. Acceptor `a` consumes an `accept p b v`
    message. We re-establish every invariant clause using `hAcceptValFun`
    and `hSentAcceptNet` to resolve the cross-acceptor uniqueness obligation. -/

private theorem inv_recvAccept {s : MsgPaxosState n m} (a : Fin n) (p : Fin m)
    (b : Nat) (v : Value) (idx : Nat)
    (hMem : (Msg.accept p b v, Target.acc a) ∈ s.network)
    (hProm : (s.acceptors a).prom ≤ b)
    (hBallot : ballot p = b)
    (h : MsgPaxosInv ballot s) :
    MsgPaxosInv ballot
      { s with
        acceptors := setAcceptor s.acceptors a { prom := b, acc := some (b, v) }
        sentAccept := setSent s.sentAccept a b v
        network := (removeAt s.network idx) ++
          [(Msg.accepted a p b v, Target.prop p)] } := by
  refine {
    hAccSent := ?_, hAccProm := ?_, hSentProm := ?_, hSentBallot := ?_,
    hNetPrepare := ?_, hNetAccept := ?_, hNetAccepted := ?_,
    hNetPromise := ?_, hSentUnique := ?_,
    hAcceptValFun := ?_, hSentAcceptNet := ?_,
    hSentSafe := ?_, hNetSafe := ?_, hNetPromisePrior := ?_,
    hAccMax := ?_, hNetPromiseNoVoteAbove := ?_,
    hNetAcceptProm := ?_ }
  · -- hAccSent: new acc (b,v) at a, ghost sentAccept a b = some v
    intro a' b' v' hacc
    by_cases hae : a = a'
    · subst hae
      simp only [setAcceptor, ite_true] at hacc
      -- hacc : some (b, v) = some (b', v')
      have : b = b' ∧ v = v' := by
        rcases hacc with ⟨⟩; exact ⟨rfl, rfl⟩
      obtain ⟨hbeq, hveq⟩ := this
      subst hbeq; subst hveq
      simp [setSent]
    · simp only [setAcceptor, if_neg hae] at hacc
      have := h.hAccSent a' b' v' hacc
      simp only [setSent]
      by_cases hc : a' = a ∧ b' = b
      · obtain ⟨heq, _⟩ := hc; exact absurd heq.symm hae
      · simp [hc]; exact this
  · -- hAccProm
    intro a' b' v' hacc
    by_cases hae : a = a'
    · subst hae
      simp only [setAcceptor, ite_true] at hacc ⊢
      have : b = b' ∧ v = v' := by rcases hacc with ⟨⟩; exact ⟨rfl, rfl⟩
      obtain ⟨hbeq, _⟩ := this
      omega
    · simp only [setAcceptor, if_neg hae] at hacc ⊢
      exact h.hAccProm a' b' v' hacc
  · -- hSentProm
    intro a' b' v' hv
    simp only [setSent] at hv
    by_cases hc : a' = a ∧ b' = b
    · obtain ⟨heq1, heq2⟩ := hc
      subst heq1; subst heq2
      simp only [setAcceptor, ite_true]
      omega
    · rw [if_neg hc] at hv
      by_cases hae : a = a'
      · subst hae
        simp only [setAcceptor, ite_true]
        have := h.hSentProm a b' v' hv
        omega
      · simp only [setAcceptor, if_neg hae]
        exact h.hSentProm a' b' v' hv
  · -- hSentBallot
    intro a' b' v' hv
    simp only [setSent] at hv
    by_cases hc : a' = a ∧ b' = b
    · obtain ⟨_, heq2⟩ := hc
      subst heq2
      exact ⟨p, hBallot⟩
    · rw [if_neg hc] at hv
      exact h.hSentBallot a' b' v' hv
  · -- hNetPrepare
    intro q b' tgt hin
    rcases List.mem_append.mp hin with h1 | h1
    · exact h.hNetPrepare q b' tgt (mem_removeAt h1)
    · rcases List.mem_singleton.mp h1 with heq
      exact absurd heq (by simp)
  · -- hNetAccept
    intro q b' v' tgt hin
    rcases List.mem_append.mp hin with h1 | h1
    · exact h.hNetAccept q b' v' tgt (mem_removeAt h1)
    · rcases List.mem_singleton.mp h1 with heq
      exact absurd heq (by simp)
  · -- hNetAccepted: old ones via hNetAccepted; new entry: sentAccept updated
    intro a' q b' v' tgt hin
    simp only [setSent]
    rcases List.mem_append.mp hin with h1 | h1
    · have := h.hNetAccepted a' q b' v' tgt (mem_removeAt h1)
      by_cases hc : a' = a ∧ b' = b
      · obtain ⟨heq1, heq2⟩ := hc
        -- Rewrite `this` using heq1, heq2 without substituting variables out of scope.
        rw [heq1, heq2] at this
        have huniq : v = v' :=
          (h.hSentAcceptNet a b v' this p v (Target.acc a) hMem).symm
        rw [heq1, heq2, ← huniq]; simp
      · rw [if_neg hc]; exact this
    · rcases List.mem_singleton.mp h1 with heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨hmsg, _⟩ := heq
      injection hmsg with h_a h_p h_b h_v
      subst h_a; subst h_p; subst h_b; subst h_v
      simp
  · -- hNetPromise
    intro a' q b' prior tgt hin
    rcases List.mem_append.mp hin with h1 | h1
    · obtain ⟨hbq, hprom⟩ := h.hNetPromise a' q b' prior tgt (mem_removeAt h1)
      refine ⟨hbq, ?_⟩
      by_cases hae : a = a'
      · subst hae
        simp only [setAcceptor, ite_true]
        -- we need new prom ≥ b'; new prom = b; old prom ≥ b'; we have hProm : old ≤ b
        -- hprom : s.acceptors a.prom ≥ b'
        -- need b ≥ b'? Not necessarily...
        -- Actually the new prom field is b, and we need b ≥ b'. We know old prom ≥ b'
        -- and new prom = b ≥ old prom (since hProm : old ≤ b). So b ≥ b'.
        have : (s.acceptors a).prom ≥ b' := hprom
        omega
      · simp only [setAcceptor, if_neg hae]
        exact hprom
    · rcases List.mem_singleton.mp h1 with heq
      exact absurd heq (by simp)
  · -- hSentUnique: the crux
    intro a₁ a₂ b' v₁ v₂ hv1 hv2
    simp only [setSent] at hv1 hv2
    by_cases hc1 : a₁ = a ∧ b' = b
    · -- a₁ got the new entry, so v₁ = v
      rw [if_pos hc1] at hv1
      have hv1eq : v₁ = v := by rcases hv1 with ⟨⟩; rfl
      by_cases hc2 : a₂ = a ∧ b' = b
      · rw [if_pos hc2] at hv2
        have : v₂ = v := by rcases hv2 with ⟨⟩; rfl
        rw [hv1eq, this]
      · rw [if_neg hc2] at hv2
        -- hv2 : s.sentAccept a₂ b' = some v₂; hc1.2 : b' = b
        obtain ⟨_, hbb⟩ := hc1
        rw [hbb] at hv2
        have := h.hSentAcceptNet a₂ b v₂ hv2 p v (Target.acc a) hMem
        -- this : v = v₂; goal v₁ = v₂; hv1eq : v₁ = v
        rw [hv1eq]; exact this.symm
    · rw [if_neg hc1] at hv1
      by_cases hc2 : a₂ = a ∧ b' = b
      · rw [if_pos hc2] at hv2
        have hv2eq : v₂ = v := by rcases hv2 with ⟨⟩; rfl
        obtain ⟨_, hbb⟩ := hc2
        rw [hbb] at hv1
        have := h.hSentAcceptNet a₁ b v₁ hv1 p v (Target.acc a) hMem
        -- this : v = v₁; hv2eq : v₂ = v; goal v₁ = v₂
        rw [hv2eq]; exact this
      · rw [if_neg hc2] at hv2
        exact h.hSentUnique a₁ a₂ b' v₁ v₂ hv1 hv2
  · -- hAcceptValFun: network loses one accept, gains one accepted (not an accept)
    intro q q' b' v₁ v₂ tgt tgt' h1 h2
    have h1' : (Msg.accept q b' v₁, tgt) ∈ s.network := by
      rcases List.mem_append.mp h1 with hx | hx
      · exact mem_removeAt hx
      · rcases List.mem_singleton.mp hx with heq
        exact absurd heq (by simp)
    have h2' : (Msg.accept q' b' v₂, tgt') ∈ s.network := by
      rcases List.mem_append.mp h2 with hx | hx
      · exact mem_removeAt hx
      · rcases List.mem_singleton.mp hx with heq
        exact absurd heq (by simp)
    exact h.hAcceptValFun q q' b' v₁ v₂ tgt tgt' h1' h2'
  · -- hSentAcceptNet: need to show every accept in new network agrees with any
    -- sentAccept entry in new sentAccept.
    intro a' b' v' hsa q' v'' tgt' hin
    -- Extract original accept membership
    have hin_orig : (Msg.accept q' b' v'', tgt') ∈ s.network := by
      rcases List.mem_append.mp hin with hx | hx
      · exact mem_removeAt hx
      · rcases List.mem_singleton.mp hx with heq
        exact absurd heq (by simp)
    simp only [setSent] at hsa
    by_cases hc : a' = a ∧ b' = b
    · rw [if_pos hc] at hsa
      have hvv : v' = v := by rcases hsa with ⟨⟩; rfl
      obtain ⟨_, hbb⟩ := hc
      rw [hvv]
      have : (Msg.accept q' b v'', tgt') ∈ s.network := by rw [← hbb]; exact hin_orig
      exact h.hAcceptValFun p q' b v v'' (Target.acc a) tgt' hMem this
    · rw [if_neg hc] at hsa
      exact h.hSentAcceptNet a' b' v' hsa q' v'' tgt' hin_orig
  · -- hSentSafe: for old entries, use h.hSentSafe + monotonicity; for new entry,
    -- use h.hNetSafe on the accept message + monotonicity.
    have hprom_mono : ∀ a', (setAcceptor s.acceptors a { prom := b, acc := some (b, v) } a').prom
        ≥ (s.acceptors a').prom := by
      intro a'; by_cases hae : a = a'
      · subst hae; simp [setAcceptor]; omega
      · simp [setAcceptor, hae]
    have hcompat : ∀ a₁ bx vx, s.sentAccept a₁ bx = some vx →
        setSent s.sentAccept a b v a₁ bx = some vx := by
      intro a₁ bx vx hold
      simp only [setSent]
      by_cases hc : a₁ = a ∧ bx = b
      · obtain ⟨ha₁, hbx⟩ := hc
        rw [ha₁, hbx] at hold
        rw [if_pos ⟨ha₁, hbx⟩]
        congr 1; exact (h.hSentAcceptNet a b vx hold p v (Target.acc a) hMem).symm
      · rw [if_neg hc]; exact hold
    intro a' b' v' hsa
    simp only [setSent] at hsa
    by_cases hc : a' = a ∧ b' = b
    · -- New entry: sentAccept a b = some v
      rw [if_pos hc] at hsa
      have hveq : v' = v := by rcases hsa with ⟨⟩; rfl
      obtain ⟨haeq, hbeq⟩ := hc
      simp only [haeq, hbeq, hveq] at *
      exact safeAt_mono_recvAccept (h.hNetSafe p b v (Target.acc a) hMem) hprom_mono hcompat
    · -- Old entry
      rw [if_neg hc] at hsa
      exact safeAt_mono_recvAccept (h.hSentSafe a' b' v' hsa) hprom_mono hcompat
  · -- hNetSafe: old accepts use h.hNetSafe + mono; new message is `accepted`, not `accept`
    have hprom_mono : ∀ a', (setAcceptor s.acceptors a { prom := b, acc := some (b, v) } a').prom
        ≥ (s.acceptors a').prom := by
      intro a'; by_cases hae : a = a'
      · subst hae; simp [setAcceptor]; omega
      · simp [setAcceptor, hae]
    have hcompat : ∀ a₁ bx vx, s.sentAccept a₁ bx = some vx →
        setSent s.sentAccept a b v a₁ bx = some vx := by
      intro a₁ bx vx hold
      simp only [setSent]
      by_cases hc : a₁ = a ∧ bx = b
      · obtain ⟨ha₁, hbx⟩ := hc
        rw [ha₁, hbx] at hold
        rw [if_pos ⟨ha₁, hbx⟩]
        congr 1; exact (h.hSentAcceptNet a b vx hold p v (Target.acc a) hMem).symm
      · rw [if_neg hc]; exact hold
    intro q b' v' tgt hin
    have hin' : (Msg.accept q b' v', tgt) ∈ s.network := by
      rcases List.mem_append.mp hin with hx | hx
      · exact mem_removeAt hx
      · rcases List.mem_singleton.mp hx with heq; exact absurd heq (by simp)
    exact safeAt_mono_recvAccept (h.hNetSafe q b' v' tgt hin') hprom_mono hcompat
  · -- hNetPromisePrior: new message is `accepted` (not promise). Old promises from
    -- removeAt survive; their prior entries in sentAccept are preserved by setSent monotonicity.
    intro a' q b' b'' v' tgt hin
    rcases List.mem_append.mp hin with h1 | h1
    · -- Old promise survived removeAt
      have := h.hNetPromisePrior a' q b' b'' v' tgt (mem_removeAt h1)
      simp only [setSent]
      by_cases hc : a' = a ∧ b'' = b
      · obtain ⟨ha', hb''⟩ := hc
        rw [ha', hb''] at this
        rw [if_pos ⟨ha', hb''⟩]
        congr 1; exact (h.hSentAcceptNet a b v' this p v (Target.acc a) hMem).symm
      · rw [if_neg hc]; exact this
    · -- New message is `accepted`, not `promise`
      rcases List.mem_singleton.mp h1 with heq
      exact absurd heq (by simp)
  · -- hAccMax: new acc = (b, v) at a, new sentAccept extends with (a, b, v)
    intro a' c v' hsa
    simp only [setSent] at hsa
    by_cases hc : a' = a ∧ c = b
    · -- New entry: a' = a, c = b, v' = v
      obtain ⟨ha', hcb⟩ := hc; subst ha'; subst hcb
      exact ⟨c, v, by simp [setAcceptor], Nat.le_refl c⟩
    · -- Old entry
      rw [if_neg hc] at hsa
      obtain ⟨b'', v'', hacc, hge⟩ := h.hAccMax a' c v' hsa
      by_cases hae : a = a'
      · subst hae
        have hge' : b ≥ c := by
          have := h.hAccProm a b'' v'' hacc; omega
        refine ⟨b, v, ?_, hge'⟩
        simp [setAcceptor]
      · refine ⟨b'', v'', ?_, hge⟩
        simp [setAcceptor, hae, hacc]
  · -- hNetPromiseNoVoteAbove: surviving promises + setSent monotonicity
    intro a' q b' prior tgt hin c hcb' hc
    have hin_orig : (Msg.promise a' q b' prior, tgt) ∈ s.network := by
      rcases List.mem_append.mp hin with hx | hx
      · exact mem_removeAt hx
      · rcases List.mem_singleton.mp hx with heq; exact absurd heq (by simp)
    have hold := h.hNetPromiseNoVoteAbove a' q b' prior tgt hin_orig c hcb' hc
    simp only [setSent]
    by_cases hc2 : a' = a ∧ c = b
    · -- New sentAccept entry at (a, b). But c < b' ≤ promise ballot.
      -- And hNetPromise says prom a' ≥ b'. Also hProm says prom a ≤ b.
      -- If a' = a: b ≥ prom a ≥ b' (from hNetPromise). But c < b'. So c < b' ≤ b.
      -- And c = b from hc2. So c = b ≤ c < b'. Then b < b'. But also b ≥ b'. Contradiction.
      obtain ⟨ha', hcb⟩ := hc2; subst ha'; subst hcb
      obtain ⟨_, hprom_ge⟩ := h.hNetPromise a' q b' prior tgt hin_orig
      omega
    · rw [if_neg hc2]; exact hold
  · -- hNetAcceptProm: accept msgs survive via removeAt; prom only increases
    intro q b' v' tgt hin
    have hin_orig : (Msg.accept q b' v', tgt) ∈ s.network := by
      rcases List.mem_append.mp hin with hx | hx
      · exact mem_removeAt hx
      · rcases List.mem_singleton.mp hx with heq; exact absurd heq (by simp)
    have hmaj_old := h.hNetAcceptProm q b' v' tgt hin_orig
    show majority (fun j => decide ((setAcceptor s.acceptors a
        { prom := b, acc := some (b, v) } j).prom ≥ b')) = true
    exact majority_mono_prom hmaj_old (by
      intro j hj; simp only [decide_eq_true_eq] at hj ⊢
      simp only [setAcceptor]
      by_cases hja : a = j
      · subst hja; simp; omega
      · simp [hja]; exact hj)

end Preservation

/-! ### Closing remarks

    The invariant block above is preserved by `sendPrepare`, `dropMsg`,
    `recvPromise`, `crashProposer`, `decidePropose`, `recvPrepare`, and
    `sendAccept` (lemmas `inv_*` above). The `recvAccept` case requires
    an additional invariant clause (`hAcceptValFun`) stating that all
    `accept` messages at a common ballot share their value. Adding this
    to `MsgPaxosInv` would close `recvAccept` as well, at which point the
    full reachability theorem follows by straightforward induction.

    In this file we have:

    - A complete asynchronous message-passing Paxos model.
    - An inductive invariant depending only on stable state + ghost.
    - Preservation proofs for all actions that only manipulate
      network/proposers/acceptors *without* writing to `sentAccept`.
    - `inv_crashProposer` as a definitional reuse — the invariant never
      mentions `proposers`, so the proof is `h` itself.

    The `recvAccept` preservation is now closed using `hAcceptValFun` and
    `hSentAcceptNet`. A **within-ballot** agreement theorem follows directly.
    Cross-ballot agreement (if two different ballots both chose, the values
    agree) requires the full `safeAt`/quorum-intersection machinery and
    remains a follow-up. -/

/-! ### Reachability and within-ballot agreement -/

theorem msg_paxos_inv_reachable {n m : Nat} {ballot : Fin m → Nat}
    {s : MsgPaxosState n m} (hreach : Reachable ballot s) :
    MsgPaxosInv ballot s := by
  induction hreach with
  | init => exact msg_paxos_inv_init
  | step _hr hstep ih =>
    cases hstep with
    | sendPrepare p => exact inv_sendPrepare p ih
    | recvPrepare a p b idx hMem hProm =>
      exact inv_recvPrepare a p b idx hMem hProm ih
    | recvPromise p a b prior idx hMem =>
      exact inv_recvPromise p a b prior idx ih
    | decidePropose p v => exact inv_decidePropose p v ih
    | sendAccept p b v hbp hGateNet hGateSent hGateSafe hGateMaj =>
      exact inv_sendAccept p b v hbp hGateNet hGateSent hGateSafe hGateMaj ih
    | recvAccept a p b v idx hMem hProm hBallot =>
      exact inv_recvAccept a p b v idx hMem hProm hBallot ih
    | dropMsg idx => exact inv_dropMsg idx ih
    | crashProposer p ps' hps =>
      subst hps; exact inv_crashProposer p _ ih
    | crashAcceptor a =>
      exact inv_crashAcceptor a ih _ (fun x hx => (List.mem_filter.mp hx).1)

/-- **Within-ballot agreement** (partial agreement). Any two `sentAccept`
    entries at the same ballot agree on the value. This follows directly
    from `hSentUnique`. Cross-ballot agreement is left to a follow-up. -/
theorem within_ballot_agreement {n m : Nat} {ballot : Fin m → Nat}
    {s : MsgPaxosState n m} (hreach : Reachable ballot s)
    {a a' : Fin n} {b : Nat} {v v' : Value}
    (hv : s.sentAccept a b = some v)
    (hv' : s.sentAccept a' b = some v') :
    v = v' :=
  (msg_paxos_inv_reachable hreach).hSentUnique a a' b v v' hv hv'

/-! ### Cross-ballot agreement -/

/-- If a value `v'` is safe at ballot `b'`, and a majority has accepted `v` at
    some ballot `b < b'`, then `v' = v`. This is the core Lamport chain step:
    the safeAt witness quorum overlaps the choosing quorum. -/
theorem safeAt_chosen_agree {n m : Nat} {ballot : Fin m → Nat}
    {s : MsgPaxosState n m} (hinv : MsgPaxosInv ballot s)
    {v v' : Value} {b b' : Nat}
    (hlt : b < b')
    (hsafe : safeAt s v' b')
    (hmaj : majority (fun a => decide (s.sentAccept a b = some v)) = true) :
    v' = v := by
  -- safeAt at ballot b gives a quorum Q
  obtain ⟨Q, hQ, hQa⟩ := hsafe b hlt
  -- The choosing quorum overlaps Q
  obtain ⟨i, hi_Q, hi_chose⟩ := majority_overlap hQ hmaj
  -- The overlap acceptor voted v at b
  have hi_voted : s.sentAccept i b = some v := by
    simpa [decide_eq_true_eq] using hi_chose
  -- What does the safeAt quorum say about i?
  rcases hQa i hi_Q with h_voted | ⟨h_none, _⟩
  · -- i voted v' at b: by hSentUnique, v = v'
    exact hinv.hSentUnique i i b v' v h_voted hi_voted
  · -- i has sentAccept = none at b: contradicts hi_voted
    exact absurd hi_voted (by rw [h_none]; exact fun h => nomatch h)

/-- **Cross-ballot agreement (full agreement).** If value `v` is chosen
    (majority-accepted) at ballot `b`, and value `v'` is chosen at ballot `b'`,
    then `v = v'`. This holds regardless of whether `b = b'` or `b ≠ b'`. -/
theorem cross_ballot_agreement {n m : Nat} {ballot : Fin m → Nat}
    (h_inj : Function.Injective ballot)
    {s : MsgPaxosState n m} (hreach : Reachable ballot s) :
    ∀ b b' v v',
      majority (fun a => decide (s.sentAccept a b = some v)) = true →
      majority (fun a => decide (s.sentAccept a b' = some v')) = true →
      v = v' := by
  intro b b' v v' hmaj hmaj'
  have hinv := msg_paxos_inv_reachable hreach
  -- Get a witness vote for v at b and v' at b'
  obtain ⟨i, _, hi⟩ := majority_overlap hmaj hmaj
  have hiv : s.sentAccept i b = some v := by simpa [decide_eq_true_eq] using hi
  obtain ⟨j, _, hj⟩ := majority_overlap hmaj' hmaj'
  have hjv : s.sentAccept j b' = some v' := by simpa [decide_eq_true_eq] using hj
  -- Get safeAt from the invariant
  have hsafe_v := hinv.hSentSafe i b v hiv
  have hsafe_v' := hinv.hSentSafe j b' v' hjv
  -- Case split on b vs b'
  rcases Nat.lt_or_ge b b' with hlt | hge
  · -- b < b': v' is safe at b', choosing quorum at b forces v' = v
    exact (safeAt_chosen_agree hinv hlt hsafe_v' hmaj).symm
  · rcases Nat.lt_or_ge b' b with hlt' | hge'
    · -- b' < b: v is safe at b, choosing quorum at b' forces v = v'
      exact safeAt_chosen_agree hinv hlt' hsafe_v hmaj'
    · -- b = b': within-ballot agreement
      have hbeq : b = b' := Nat.le_antisymm hge' hge
      subst hbeq
      exact hinv.hSentUnique i j b v v' hiv hjv

/-! ### Promise-validity invariant and `sendAccept` gate derivation

    `PromiseInv` links proposer-local `promisesReceived` data back to stable
    state. It lives outside `MsgPaxosInv` because it references `proposers`
    (volatile). Crash preservation is trivial: `crashProposer` resets
    `promisesReceived` to `none`, making the hypothesis vacuously false. -/

/-- If proposer `p` has received a promise from acceptor `a`, then:
    (1) `a`'s promise is at least `ballot p`, and
    (2) any reported prior vote is logged in `sentAccept`, and
    (3) the acceptor has no vote between the reported prior ballot and `ballot p`. -/
structure PromiseInv {n m : Nat} (ballot : Fin m → Nat)
    (s : MsgPaxosState n m) : Prop where
  hPromProm : ∀ p a prior,
      (s.proposers p).promisesReceived a = some prior →
      (s.acceptors a).prom ≥ ballot p
  hPromPrior : ∀ p a b' v',
      (s.proposers p).promisesReceived a = some (some (b', v')) →
      s.sentAccept a b' = some v'
  hPromNoVoteAbove : ∀ p a prior,
      (s.proposers p).promisesReceived a = some prior →
      ∀ c, c < ballot p →
      (match prior with | none => True | some (b', _) => c > b') →
      s.sentAccept a c = none

theorem promise_inv_init {n m : Nat} {ballot : Fin m → Nat} :
    PromiseInv ballot (initialMsgPaxos n m) where
  hPromProm := by intro p a prior hp; simp [initialMsgPaxos, initProposer] at hp
  hPromPrior := by intro p a b' v' hp; simp [initialMsgPaxos, initProposer] at hp
  hPromNoVoteAbove := by intro p a prior hp; simp [initialMsgPaxos, initProposer] at hp

section PromisePreservation
variable {n m : Nat} {ballot : Fin m → Nat}

/-- Helper: PromiseInv is preserved when only the network changes. -/
private theorem promiseInv_net_frame {s : MsgPaxosState n m}
    (h : PromiseInv ballot s) (net' : List (Msg n m × Target n m)) :
    PromiseInv ballot { s with network := net' } :=
  ⟨h.hPromProm, h.hPromPrior, h.hPromNoVoteAbove⟩

private theorem promiseInv_recvPromise {s : MsgPaxosState n m} (p : Fin m)
    (a : Fin n) (b : Nat) (prior : Option (Nat × Value)) (idx : Nat)
    (hMem : (Msg.promise a p b prior, Target.prop p) ∈ s.network)
    (hinv : MsgPaxosInv ballot s)
    (h : PromiseInv ballot s) :
    PromiseInv ballot
      { s with
        proposers := setProposer s.proposers p
          { (s.proposers p) with
            promisesReceived :=
              fun q => if q = a then some prior else
                       (s.proposers p).promisesReceived q }
        network := removeAt s.network idx } := by
  obtain ⟨hbp, hprom⟩ := hinv.hNetPromise a p b prior (Target.prop p) hMem
  -- Helper: decode setProposer + if-then-else at (p', a')
  have decode : ∀ p' a' prior', (setProposer s.proposers p
      { (s.proposers p) with promisesReceived :=
          fun q => if q = a then some prior else (s.proposers p).promisesReceived q }
      p').promisesReceived a' = some prior' →
      (p' = p ∧ a' = a ∧ prior' = prior) ∨
      ((s.proposers p').promisesReceived a' = some prior') := by
    intro p' a' prior' hp'
    simp only [setProposer] at hp'
    by_cases hpe : p' = p
    · subst hpe; simp only [ite_true] at hp'
      by_cases hae : a' = a
      · subst hae; simp only [ite_true] at hp'
        left; exact ⟨rfl, rfl, by rcases hp' with ⟨⟩; rfl⟩
      · right; simp only [if_neg hae] at hp'; exact hp'
    · right; simp only [if_neg hpe] at hp'; exact hp'
  constructor
  · -- hPromProm
    intro p' a' prior' hp'
    rcases decode p' a' prior' hp' with ⟨hp_eq, ha_eq, _⟩ | hold
    · show (s.acceptors a').prom ≥ ballot p'
      rw [ha_eq, hp_eq, hbp]; exact hprom
    · exact h.hPromProm p' a' prior' hold
  · -- hPromPrior
    intro p' a' b' v' hp'
    rcases decode p' a' (some (b', v')) hp' with ⟨_, ha_eq, hpr_eq⟩ | hold
    · show s.sentAccept a' b' = some v'
      rw [ha_eq]; exact hinv.hNetPromisePrior a p b b' v' (Target.prop p)
        (by rw [hpr_eq]; exact hMem)
    · exact h.hPromPrior p' a' b' v' hold
  · -- hPromNoVoteAbove
    intro p' a' prior' hp' c hcbp' hc
    rcases decode p' a' prior' hp' with ⟨hp_eq, ha_eq, hpr_eq⟩ | hold
    · show s.sentAccept a' c = none
      rw [ha_eq]
      rw [hpr_eq] at hc
      exact hinv.hNetPromiseNoVoteAbove a p b prior (Target.prop p) hMem c
        (by rw [hp_eq] at hcbp'; rw [hbp] at hcbp'; exact hcbp') hc
    · exact h.hPromNoVoteAbove p' a' prior' hold c hcbp' hc

/-- PromiseInv for proposer-only changes: proposed field doesn't affect promises. -/
private theorem promiseInv_propose_frame {s : MsgPaxosState n m} (p : Fin m)
    (f : ProposerState n → ProposerState n)
    (hf : ∀ a, (f (s.proposers p)).promisesReceived a = (s.proposers p).promisesReceived a)
    (h : PromiseInv ballot s) :
    PromiseInv ballot
      { s with proposers := setProposer s.proposers p (f (s.proposers p)) } := by
  have decode : ∀ p' a' prior', (setProposer s.proposers p (f (s.proposers p))
      p').promisesReceived a' = some prior' →
      ((s.proposers p').promisesReceived a' = some prior') := by
    intro p' a' prior' hp'
    simp only [setProposer] at hp'
    by_cases hpe : p' = p
    · subst hpe; simp only [ite_true] at hp'; rw [hf] at hp'; exact hp'
    · simp only [if_neg hpe] at hp'; exact hp'
  constructor
  · intro p' a prior hp'; exact h.hPromProm p' a prior (decode p' a prior hp')
  · intro p' a b' v' hp'; exact h.hPromPrior p' a b' v' (decode p' a _ hp')
  · intro p' a prior hp' c hcbp' hc
    exact h.hPromNoVoteAbove p' a prior (decode p' a prior hp') c hcbp' hc

private theorem promiseInv_recvAccept {s : MsgPaxosState n m} (a : Fin n)
    (p : Fin m) (b : Nat) (v : Value) (idx : Nat)
    (hMem : (Msg.accept p b v, Target.acc a) ∈ s.network)
    (hProm : (s.acceptors a).prom ≤ b)
    (hBallot : ballot p = b)
    (hinv : MsgPaxosInv ballot s)
    (h : PromiseInv ballot s) :
    PromiseInv ballot
      { s with
        acceptors := setAcceptor s.acceptors a { prom := b, acc := some (b, v) }
        sentAccept := setSent s.sentAccept a b v
        network := (removeAt s.network idx) ++
          [(Msg.accepted a p b v, Target.prop p)] } := by
  constructor
  · -- hPromProm: prom only increases
    intro p' a' prior hp'
    have := h.hPromProm p' a' prior hp'
    by_cases hae : a = a'
    · subst hae; simp only [setAcceptor, ite_true]; omega
    · simp only [setAcceptor, if_neg hae]; exact this
  · -- hPromPrior: sentAccept only grows
    intro p' a' b' v' hp'
    have := h.hPromPrior p' a' b' v' hp'
    simp only [setSent]
    by_cases hc : a' = a ∧ b' = b
    · obtain ⟨ha', hb'⟩ := hc; rw [ha', hb'] at this
      rw [if_pos ⟨ha', hb'⟩]
      congr 1; exact (hinv.hSentAcceptNet a b v' this p v (Target.acc a) hMem).symm
    · rw [if_neg hc]; exact this
  · -- hPromNoVoteAbove: sentAccept only grows, new entry at ballot b ≥ ballot p'
    intro p' a' prior hp' c hcbp' hc
    have hold := h.hPromNoVoteAbove p' a' prior hp' c hcbp' hc
    simp only [setSent]
    by_cases hc2 : a' = a ∧ c = b
    · -- New entry at (a, b). We have c < ballot p'. And ballot p = b.
      -- From hPromProm, prom a' ≥ ballot p'. If a' = a, prom a ≥ ballot p'.
      -- But c = b and hProm : prom a ≤ b. So ballot p' ≤ prom a ≤ b = c.
      -- But c < ballot p'. Contradiction.
      obtain ⟨ha', hcb⟩ := hc2; subst ha'; subst hcb
      -- After subst: a' is the acceptor, c is the ballot. Goal: some v = none (contradiction)
      -- hPromProm gives prom a' ≥ ballot p', but hProm gives prom a' ≤ c < ballot p'
      have hge := h.hPromProm p' a' prior hp'
      omega
    · rw [if_neg hc2]; exact hold

private theorem promiseInv_recvPrepare {s : MsgPaxosState n m} (a : Fin n)
    (p : Fin m) (b : Nat) (idx : Nat)
    (hProm : (s.acceptors a).prom < b)
    (h : PromiseInv ballot s) :
    PromiseInv ballot
      { s with
        acceptors := setAcceptor s.acceptors a
          { (s.acceptors a) with prom := b }
        network := (removeAt s.network idx) ++
          [(Msg.promise a p b (s.acceptors a).acc, Target.prop p)] } := by
  constructor
  · intro p' a' prior hp'
    have := h.hPromProm p' a' prior hp'
    by_cases hae : a = a'
    · subst hae; simp only [setAcceptor, ite_true]; omega
    · simp only [setAcceptor, if_neg hae]; exact this
  · intro p' a' b' v' hp'
    exact h.hPromPrior p' a' b' v' hp'
  · intro p' a' prior hp' c hcbp' hc
    exact h.hPromNoVoteAbove p' a' prior hp' c hcbp' hc

private theorem promiseInv_crashProposer {s : MsgPaxosState n m} (p : Fin m)
    (h : PromiseInv ballot s) :
    let ps' : ProposerState n := { (s.proposers p) with promisesReceived := fun _ => none }
    PromiseInv ballot
      { s with proposers := setProposer s.proposers p ps' } := by
  constructor
  · intro p' a prior hp'
    simp only [setProposer] at hp'
    by_cases hpe : p' = p
    · subst hpe; simp at hp'
    · simp [hpe] at hp'; exact h.hPromProm p' a prior hp'
  · intro p' a b' v' hp'
    simp only [setProposer] at hp'
    by_cases hpe : p' = p
    · subst hpe; simp at hp'
    · simp [hpe] at hp'; exact h.hPromPrior p' a b' v' hp'
  · intro p' a prior hp' c hcbp' hc
    simp only [setProposer] at hp'
    by_cases hpe : p' = p
    · subst hpe; simp at hp'
    · simp [hpe] at hp'; exact h.hPromNoVoteAbove p' a prior hp' c hcbp' hc

end PromisePreservation

theorem promise_inv_reachable {n m : Nat} {ballot : Fin m → Nat}
    {s : MsgPaxosState n m} (hreach : Reachable ballot s) :
    PromiseInv ballot s := by
  induction hreach with
  | init => exact promise_inv_init
  | step _hr hstep ih =>
    have hinv_pre := msg_paxos_inv_reachable _hr
    cases hstep with
    | sendPrepare p => exact promiseInv_net_frame ih _
    | recvPrepare _ p b idx hMem hProm =>
      exact promiseInv_recvPrepare _ p b idx hProm ih
    | recvPromise p a b prior idx hMem =>
      exact promiseInv_recvPromise p a b prior idx hMem hinv_pre ih
    | decidePropose p v =>
      exact promiseInv_propose_frame p (fun ps => { ps with proposed := some v })
        (fun _ => rfl) ih
    | sendAccept p b v _ _ _ _ _ =>
      exact promiseInv_net_frame ih _
    | recvAccept a p b v idx hMem hProm hBallot =>
      exact promiseInv_recvAccept a p b v idx hMem hProm hBallot hinv_pre ih
    | dropMsg idx => exact promiseInv_net_frame ih _
    | crashProposer p ps' hps =>
      subst hps; exact promiseInv_crashProposer p ih
    | crashAcceptor a =>
      exact promiseInv_net_frame ih _

/-! ### `sendAccept` gate derivation

    A proposer that has collected a majority of promise responses and picks
    a value via max-vote automatically satisfies the `safeAt` gate.

    The proof splits ballots `c < b` into three ranges relative to `b_max`,
    the highest prior-vote ballot in the promise quorum:

    - `b_max < c < b`: all quorum members have `sentAccept a c = none`
      (by `hPromNoVoteAbove`), so the right disjunct (promised-past) works.
    - `c = b_max`: by max-vote, `v = v_max`; the voter has
      `sentAccept a c = some v`; non-voters use the right disjunct.
    - `c < b_max`: the vote at `b_max` was safe at `b_max`
      (by `hSentSafe`), which provides a quorum for `c`. -/

/-- The `safeAt` gate for `sendAccept` is derivable from a proposer's promise
    majority, the max-vote value, and the fact that `b_max` is the highest prior.
    The caller supplies `b_max`, `v_max`, and the maximality + witness evidence. -/
theorem sendAccept_gate_safeAt {n m : Nat} {ballot : Fin m → Nat}
    {s : MsgPaxosState n m}
    (hinv : MsgPaxosInv ballot s) (hpinv : PromiseInv ballot s)
    (p : Fin m) (v : Value) (b : Nat)
    (hbp : ballot p = b)
    (hmaj : majority (fun a => decide ((s.proposers p).promisesReceived a ≠ none)) = true)
    -- max-vote: caller provides the max prior ballot, its value, maximality evidence,
    -- and either "no priors" or "v = v_max" witness.
    (b_max : Nat)
    (hmax_bound : ∀ a' b'' v'',
        (s.proposers p).promisesReceived a' = some (some (b'', v'')) → b'' ≤ b_max)
    (hmax_wit : (∀ a, ∀ prior, (s.proposers p).promisesReceived a = some prior →
        prior = none) ∨
        (∃ a_max v_max, (s.proposers p).promisesReceived a_max = some (some (b_max, v_max)) ∧
         v = v_max)) :
    safeAt s v b := by
  intro c hcb
  let Q : Fin n → Bool := fun a => decide ((s.proposers p).promisesReceived a ≠ none)
  -- Handle the "all priors none" case: every quorum member has sentAccept = none
  -- at all ballots < b, so use the right disjunct for everyone.
  rcases hmax_wit with h_all_none | ⟨a_max, v_max, hpr_max, hveq⟩
  · refine ⟨Q, hmaj, fun a ha => ?_⟩
    have ha_some : (s.proposers p).promisesReceived a ≠ none := by
      simpa [Q, decide_eq_true_eq] using ha
    obtain ⟨prior, hprior⟩ := Option.ne_none_iff_exists'.mp ha_some
    have hprom_a : (s.acceptors a).prom ≥ b := hbp ▸ hpinv.hPromProm p a prior hprior
    have hpr_none : prior = none := h_all_none a prior hprior
    right; constructor
    · rw [hpr_none] at hprior
      exact hpinv.hPromNoVoteAbove p a none hprior c (hbp ▸ hcb) trivial
    · omega
  · -- There is a max prior witness.
    have hsa_max := hpinv.hPromPrior p a_max b_max v_max hpr_max
    -- Case split: is c above all prior ballots, or at/below some?
    by_cases h_above : c > b_max
    · -- c > b_max: every quorum member's prior ballot is < c.
      refine ⟨Q, hmaj, fun a ha => ?_⟩
      have ha_some : (s.proposers p).promisesReceived a ≠ none := by
        simpa [Q, decide_eq_true_eq] using ha
      obtain ⟨prior, hprior⟩ := Option.ne_none_iff_exists'.mp ha_some
      have hprom_a : (s.acceptors a).prom ≥ b := hbp ▸ hpinv.hPromProm p a prior hprior
      right; constructor
      · cases prior with
        | none => exact hpinv.hPromNoVoteAbove p a none hprior c (hbp ▸ hcb) trivial
        | some bv =>
          obtain ⟨b', v'⟩ := bv
          have : b' ≤ b_max := hmax_bound a b' v' hprior
          exact hpinv.hPromNoVoteAbove p a (some (b', v')) hprior c (hbp ▸ hcb) (by omega)
      · omega
    · -- c ≤ b_max: use either the promise quorum or safeAt from the max vote
      by_cases hc_eq : c = b_max
      · -- c = b_max: use the promise quorum directly
        refine ⟨Q, hmaj, fun a ha => ?_⟩
        have ha_some : (s.proposers p).promisesReceived a ≠ none := by
          simpa [Q, decide_eq_true_eq] using ha
        obtain ⟨prior, hprior⟩ := Option.ne_none_iff_exists'.mp ha_some
        have hprom_a : (s.acceptors a).prom ≥ b := hbp ▸ hpinv.hPromProm p a prior hprior
        cases prior with
        | none =>
          right
          exact ⟨hpinv.hPromNoVoteAbove p a none hprior c (hbp ▸ hcb) trivial, by omega⟩
        | some bv =>
          obtain ⟨bp, vp⟩ := bv
          have hbp_le : bp ≤ b_max := hmax_bound a bp vp hprior
          by_cases hcbp : c = bp
          · left; rw [hveq, hcbp]
            have hsa_a := hpinv.hPromPrior p a bp vp hprior
            have hbp_eq_bmax : bp = b_max := by omega
            rw [hbp_eq_bmax] at hsa_a ⊢
            have hvp_eq := hinv.hSentUnique a a_max b_max vp v_max hsa_a hsa_max
            rw [hvp_eq] at hsa_a; exact hsa_a
          · right
            exact ⟨hpinv.hPromNoVoteAbove p a (some (bp, vp)) hprior c (hbp ▸ hcb)
                     (by omega), by omega⟩
      · -- c < b_max: use safeAt from hSentSafe at b_max
        have hc_lt : c < b_max := by omega
        have hsafe_max := hinv.hSentSafe a_max b_max v_max hsa_max
        obtain ⟨Q', hQ', hQ'a⟩ := hsafe_max c hc_lt
        refine ⟨Q', hQ', fun a ha => ?_⟩
        rcases hQ'a a ha with h_voted | h_none
        · left; rw [hveq]; exact h_voted
        · right; exact h_none
