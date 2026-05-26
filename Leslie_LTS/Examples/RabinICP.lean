import Leslie_LTS.Framework
import Leslie_LTS.Framework.Adversary
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring


/-! # Rabin's Information Checking Protocol (ICP)

    Three processes: Dealer, Intermediary, Receiver.
    Security parameters: `p` (with `p > 0`) and `k` (a natural number).
    All arithmetic is in Z_p.
    The Dealer holds a secret `s : ZMod p`. The protocol has three phases:
    1. **Generation**: The Dealer generates 2k pairs `(b_i, y_i)` with `b_i ≠ 0`,
       computes `c_i = b_i * s + y_i`, sends all `(s, y_i)` to the Intermediary,
       and all `(b_i, c_i)` to the Receiver.
    2. **Verification**: The Intermediary selects k indices among the 2k, sends
       them to the Receiver. The Receiver responds with `(b_i, c_i)` for those
       indices. The Intermediary checks `c_i = b_i * s + y_i` for all selected.
    3. **Authentication**: The Intermediary sends all non-selected `(s, y_i)` to
       the Receiver. The Receiver accepts if at least one identity `c_i = b_i * s + y_i`
       holds among the non-selected indices.
-/

open LTS

namespace RabinICP

/-- Update a function at a single point. -/
def update {α : Type} {β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

/-! ### Parameters -/

variable (p : Nat) (k : Nat)

/-- Shorthand for the value type. -/
abbrev V (p : Nat) := ZMod p

/-! ### Process Identifiers -/

inductive Process where
  | Dealer
  | Intermediary
  | Receiver
  deriving DecidableEq, Repr

/-! ### Messages -/

/-- A pair of field elements. -/
abbrev Pair (p : Nat) := V p × V p

/-- Messages in the network buffer. All messages carry bulk data. -/
inductive Msg (p : Nat) (k : Nat) where
  /-- Dealer → Intermediary: all 2k pairs (s, y_i). -/
  | dealerToIntermediary (data : Fin (2 * k) → Pair p)
  /-- Dealer → Receiver: all 2k pairs (b_i, c_i). -/
  | dealerToReceiver (data : Fin (2 * k) → Pair p)
  /-- Intermediary → Receiver: the set of selected indices for verification. -/
  | verifyRequest (selected : Fin (2 * k) → Bool)
  /-- Receiver → Intermediary: verification responses (b_i, c_i) for all
      selected indices. -/
  | verifyResponse (data : Fin (2 * k) → Option (Pair p))
  /-- Intermediary → Receiver: authentication data (s, y_i) for all
      non-selected indices. -/
  | authData (data : Fin (2 * k) → Option (Pair p))

/-- The sender of a message. -/
def Msg.sender {p : Nat} {k : Nat} : Msg p k → Process
  | .dealerToIntermediary _ => .Dealer
  | .dealerToReceiver _     => .Dealer
  | .verifyRequest _        => .Intermediary
  | .verifyResponse _       => .Receiver
  | .authData _             => .Intermediary

/-- The receiver of a message. -/
def Msg.receiver {p : Nat} {k : Nat} : Msg p k → Process
  | .dealerToIntermediary _ => .Intermediary
  | .dealerToReceiver _     => .Receiver
  | .verifyRequest _        => .Receiver
  | .verifyResponse _       => .Intermediary
  | .authData _             => .Receiver

/-! ### Local States -/

structure DealerState where
  secret : Option (V p)
  pairs : Option (Fin (2 * k) → V p × V p)

structure IntermediaryState where
  received : Option (Fin (2 * k) → V p × V p)
  selected : Option (Fin (2 * k) → Bool)
  verifyResp : Option (Fin (2 * k) → Option (V p × V p))
  verified : Option Bool

structure ReceiverState where
  received : Option (Fin (2 * k) → V p × V p)
  selected : Option (Fin (2 * k) → Bool)
  authData : Option (Fin (2 * k) → Option (V p × V p))
  decision : Option Bool

/-! ### Global State -/

structure State where
  dealer : DealerState p k
  intermediary : IntermediaryState p k
  receiver : ReceiverState p k
  buffer : Msg p k → Prop
  corrupted : Process → Bool

/-! ### Labels -/

inductive Label where
  | corrupt (proc : Process)
  | input (s : V p)
  | generate (pairs : Fin (2 * k) → V p × V p)
  | send (m : Msg p k)
  | recv (m : Msg p k)
  | selectIndices (selected : Fin (2 * k) → Bool)
  | checkVerification (ok : Bool)
  | receiverDecide (result : Option (V p))

/-! ### Initial State -/

def initState : State p k where
  dealer := { secret := none, pairs := none }
  intermediary := {
    received := none, selected := none,
    verifyResp := none, verified := none }
  receiver := {
    received := none, selected := none,
    authData := none, decision := none }
  buffer := fun _ => False
  corrupted := fun _ => false

/-! ### Transition Relation -/

inductive step : State p k → Label p k → State p k → Prop where
  /-- Corrupt a process. -/
  | corrupt_step (st : State p k) (proc : Process) :
    st.corrupted proc = false →
    step st (.corrupt proc)
      { st with corrupted := update st.corrupted proc true }
  /-- A corrupted process can send any message that originates from it. -/
  | byzantine_step (st : State p k) (proc : Process) (m : Msg p k) :
    st.corrupted proc = true →
    Msg.sender m = proc →
    step st (.send m)
      { st with buffer := fun m' => st.buffer m' ∨ m' = m }
  /-- Dealer receives its secret input. -/
  | input_step (st : State p k) (s : V p) :
    st.dealer.secret = none →
    st.corrupted .Dealer = false →
    step st (.input s)
      { st with dealer := { st.dealer with secret := some s } }
  /-- Dealer generates all 2k pairs (b_i, y_i) at once, with each b_i ≠ 0. -/
  | generate_step (st : State p k) (pairs : Fin (2 * k) → V p × V p) :
    st.dealer.secret.isSome = true →
    st.dealer.pairs = none →
    (∀ i, (pairs i).1 ≠ 0) →
    st.corrupted .Dealer = false →
    step st (.generate pairs)
      { st with dealer := { st.dealer with pairs := some pairs } }
  /-- Dealer sends all (s, y_i) to Intermediary in bulk. -/
  | send_dealerToIntermediary (st : State p k) (s : V p)
    (pairs : Fin (2 * k) → V p × V p) :
    st.dealer.secret = some s →
    st.dealer.pairs = some pairs →
    st.corrupted .Dealer = false →
    step st (.send (.dealerToIntermediary (fun i => (s, (pairs i).2))))
      { st with buffer := fun m =>
          st.buffer m ∨ m = .dealerToIntermediary (fun i => (s, (pairs i).2)) }
  /-- Dealer sends all (b_i, c_i) to Receiver in bulk. -/
  | send_dealerToReceiver (st : State p k) (s : V p)
    (pairs : Fin (2 * k) → V p × V p) :
    st.dealer.secret = some s →
    st.dealer.pairs = some pairs →
    st.corrupted .Dealer = false →
    step st (.send (.dealerToReceiver (fun i =>
        ((pairs i).1, (pairs i).1 * s + (pairs i).2))))
      { st with buffer := fun m =>
          st.buffer m ∨ m = .dealerToReceiver (fun i =>
            ((pairs i).1, (pairs i).1 * s + (pairs i).2)) }
  /-- Intermediary receives all 2k pairs from Dealer. -/
  | recv_intermediary (st : State p k)
    (data : Fin (2 * k) → Pair p) :
    st.buffer (.dealerToIntermediary data) →
    st.intermediary.received = none →
    st.corrupted .Intermediary = false →
    step st (.recv (.dealerToIntermediary data))
      { st with
        buffer := fun m => st.buffer m ∧ m ≠ .dealerToIntermediary data
        intermediary := { st.intermediary with received := some data } }
  /-- Receiver receives all 2k pairs from Dealer. -/
  | recv_receiver_from_dealer (st : State p k)
    (data : Fin (2 * k) → Pair p) :
    st.buffer (.dealerToReceiver data) →
    st.receiver.received = none →
    st.corrupted .Receiver = false →
    step st (.recv (.dealerToReceiver data))
      { st with
        buffer := fun m => st.buffer m ∧ m ≠ .dealerToReceiver data
        receiver := { st.receiver with received := some data } }
  /-- Intermediary selects k indices for verification. -/
  | selectIndices_step (st : State p k) (selected : Fin (2 * k) → Bool) :
    st.intermediary.received.isSome = true →
    st.intermediary.selected = none →
    (List.filter selected (List.finRange (2 * k))).length = k →
    st.corrupted .Intermediary = false →
    step st (.selectIndices selected)
      { st with intermediary := { st.intermediary with selected := some selected } }
  /-- Intermediary sends verification request (all selected indices) to Receiver. -/
  | send_verifyRequest (st : State p k) (selected : Fin (2 * k) → Bool) :
    st.intermediary.selected = some selected →
    st.corrupted .Intermediary = false →
    step st (.send (.verifyRequest selected))
      { st with buffer := fun m => st.buffer m ∨ m = .verifyRequest selected }
  /-- Receiver receives verification request. -/
  | recv_verifyRequest (st : State p k) (selected : Fin (2 * k) → Bool) :
    st.buffer (.verifyRequest selected) →
    st.receiver.selected = none →
    st.corrupted .Receiver = false →
    step st (.recv (.verifyRequest selected))
      { st with
        buffer := fun m => st.buffer m ∧ m ≠ .verifyRequest selected
        receiver := { st.receiver with selected := some selected } }
  /-- Receiver sends verification responses for all selected indices in bulk. -/
  | send_verifyResponse (st : State p k)
    (selected : Fin (2 * k) → Bool)
    (data : Fin (2 * k) → V p × V p) :
    st.receiver.selected = some selected →
    st.receiver.received = some data →
    st.corrupted .Receiver = false →
    step st (.send (.verifyResponse (fun i =>
        if selected i then some (data i) else none)))
      { st with buffer := fun m =>
          st.buffer m ∨ m = .verifyResponse (fun i =>
            if selected i then some (data i) else none) }
  /-- Intermediary receives verification responses. -/
  | recv_verifyResponse (st : State p k)
    (resp : Fin (2 * k) → Option (Pair p)) :
    st.buffer (.verifyResponse resp) →
    st.intermediary.verifyResp = none →
    st.corrupted .Intermediary = false →
    step st (.recv (.verifyResponse resp))
      { st with
        buffer := fun m => st.buffer m ∧ m ≠ .verifyResponse resp
        intermediary := { st.intermediary with verifyResp := some resp } }
  /-- Intermediary checks all verification responses. -/
  | checkVerification_step (st : State p k)
    (selected : Fin (2 * k) → Bool)
    (intData : Fin (2 * k) → V p × V p)
    (resp : Fin (2 * k) → Option (V p × V p))
    (ok : Bool) :
    st.intermediary.selected = some selected →
    st.intermediary.received = some intData →
    st.intermediary.verifyResp = some resp →
    st.intermediary.verified = none →
    st.corrupted .Intermediary = false →
    (ok = true ↔ ∀ i, selected i = true →
      ∀ b c, resp i = some (b, c) →
        c = b * (intData i).1 + (intData i).2) →
    step st (.checkVerification ok)
      { st with intermediary := { st.intermediary with verified := some ok } }
  /-- Intermediary sends authentication data for all non-selected indices. -/
  | send_authData (st : State p k)
    (selected : Fin (2 * k) → Bool)
    (intData : Fin (2 * k) → V p × V p) :
    st.intermediary.selected = some selected →
    st.intermediary.received = some intData →
    st.intermediary.verified = some true →
    st.corrupted .Intermediary = false →
    step st (.send (.authData (fun i =>
        if selected i then none else some (intData i))))
      { st with buffer := fun m =>
          st.buffer m ∨ m = .authData (fun i =>
            if selected i then none else some (intData i)) }
  /-- Receiver receives authentication data. -/
  | recv_authData (st : State p k)
    (authMsg : Fin (2 * k) → Option (Pair p)) :
    st.buffer (.authData authMsg) →
    st.receiver.authData = none →
    st.corrupted .Receiver = false →
    step st (.recv (.authData authMsg))
      { st with
        buffer := fun m => st.buffer m ∧ m ≠ .authData authMsg
        receiver := { st.receiver with authData := some authMsg } }
  /-- Receiver checks authentication: the result is `some s` when at least one
      non-selected index satisfies `c_i = b_i * s + y_i`, carrying the
      authenticated secret value; `none` when no such index exists. -/
  | receiverDecide_step (st : State p k)
    (recvData : Fin (2 * k) → V p × V p)
    (authMsg : Fin (2 * k) → Option (V p × V p))
    (selected : Fin (2 * k) → Bool)
    (result : Option (V p)) :
    st.receiver.received = some recvData →
    st.receiver.authData = some authMsg →
    st.receiver.selected = some selected →
    st.corrupted .Receiver = false →
    (result.isSome = true ↔ ∃ i, selected i = false ∧
      ∃ s y, authMsg i = some (s, y) ∧
        (recvData i).2 = (recvData i).1 * s + y) →
    (∀ s_val, result = some s_val → ∃ i, selected i = false ∧
      ∃ y, authMsg i = some (s_val, y) ∧
        (recvData i).2 = (recvData i).1 * s_val + y) →
    step st (.receiverDecide result)
      { st with receiver := { st.receiver with decision := some result.isSome } }

/-! ### The LTS -/

def system : System (State p k) (Label p k) where
  init := fun st => st = initState p k
  step := step p k

/-! ### Adversary Model

    The adversary can see:
    - The full local state of all corrupted processes
    - Which messages are present in the buffer (but not their content)
    - The set of corrupted processes
    From labels, the adversary only sees the *kind* of action (which
    constructor), not the data it carries — unless the action involves
    a corrupted process, in which case the full data is visible through
    the state signal of that process.
-/

/-- The adversary's state observation. -/
structure StateSignal where
  corrupted : Process → Bool
  dealerState : Option (DealerState p k)
  intermediaryState : Option (IntermediaryState p k)
  receiverState : Option (ReceiverState p k)
  /-- Messages in the buffer sent by corrupted processes (full content visible). -/
  corruptedSent : Msg p k → Prop
  /-- Whether there are messages in the buffer sent by honest processes
      (presence only, no content). -/
  honestBufferOccupancy : Prop

/-- Observe the state: extract what the adversary can see. -/
def observeState (st : State p k) : StateSignal p k where
  corrupted := st.corrupted
  dealerState := if st.corrupted .Dealer then some st.dealer else none
  intermediaryState := if st.corrupted .Intermediary then some st.intermediary else none
  receiverState := if st.corrupted .Receiver then some st.receiver else none
  corruptedSent := fun m => st.buffer m ∧ st.corrupted m.sender = true
  honestBufferOccupancy := ∃ m, st.buffer m ∧ st.corrupted m.sender = false

/-- The kind of a label: the constructor tag without data. -/
inductive LabelKind where
  | corrupt
  | input
  | generate
  | send
  | recv
  | selectIndices
  | checkVerification
  | receiverDecide
  deriving DecidableEq, Repr

/-- The adversary's label observation: the kind of action, plus the full
    message content for send/recv of messages from corrupted senders.
    For honest process actions, only the kind is revealed. -/
inductive LabelSignal where
  /-- An action by an honest process: only the kind is visible. -/
  | honest (kind : LabelKind)
  /-- A corruption action: the adversary sees who is corrupted. -/
  | corrupt (proc : Process)
  /-- A send/recv involving a message from a corrupted sender:
      the adversary sees the full message. -/
  | corruptedMsg (kind : LabelKind) (m : Msg p k)

/-- Observe a label given the current state.
    The adversary sees the full message data only for send/recv actions
    involving messages from corrupted senders; otherwise just the kind. -/
def observeLabel (st : State p k) : Label p k → LabelSignal p k
  | .corrupt proc    => .corrupt proc
  | .input _         => .honest .input
  | .generate _      => .honest .generate
  | .send m          => if st.corrupted m.sender then .corruptedMsg .send m
                         else .honest .send
  | .recv m          => if st.corrupted m.sender then .corruptedMsg .recv m
                         else .honest .recv
  | .selectIndices _       => .honest .selectIndices
  | .checkVerification _   => .honest .checkVerification
  | .receiverDecide _      => .honest .receiverDecide

/-- The adversary's observation function. -/
def adversaryObs : LTS.Observation (State p k) (Label p k)
    (StateSignal p k) (LabelSignal p k) where
  observe_state := observeState p k
  observe_label := observeLabel p k

/-- The Rabin ICP adversary. -/
def adversary : PLTS.Adversary (State p k) (Label p k)
    (StateSignal p k) (LabelSignal p k) :=
  PLTS.Adversary.ofLTS (system p k) (adversaryObs p k)

/-! ### Validity Property

    If no process is corrupted, then verification succeeds and
    authentication returns the secret given as input to the dealer. -/

/-- Validity: if no process is corrupted, verification succeeds and
    authentication returns the secret given as input to the dealer. -/
def validity : LTS.Execution (State p k) (Label p k) → Prop :=
  fun e =>
    (∀ n proc, e.labels n ≠ .corrupt proc) →
    (∀ n ok, e.labels n = .checkVerification ok → ok = true) ∧
    (∀ n result, e.labels n = .receiverDecide result →
      ∃ m s, m < n ∧ e.labels m = .input s ∧ result = some s)

/-! ### Validity Proof

    The proof proceeds by establishing an inductive trace invariant that tracks
    the consistency of all protocol data with the dealer's original secret and
    pairs, under the assumption that no corruption has occurred.
    Key observations:
    1. All state fields are write-once (set from `none` to `some _` exactly once).
    2. When no corruption occurs, all buffer messages are placed by honest send
       steps and faithfully reflect the sender's local state.
    3. The algebraic identity `c_i = b_i * s + y_i` (by construction) ensures
       both verification and authentication succeed. -/

/-- The inductive trace invariant for validity. At each step `n`, assuming no
    corruption has occurred up to `n`, the protocol state is consistent. -/
private def validity_inv : TraceProp (State p k) (Label p k) :=
  fun e n =>
    (∀ j, j < n → ∀ proc, e.labels j ≠ Label.corrupt proc) →
    let s := e.states n
    -- (1) No corruption in state
    (∀ proc, s.corrupted proc = false) ∧
    -- (2) Dealer secret persistence
    (∀ sec, s.dealer.secret = some sec → ∃ m, m < n ∧ e.labels m = .input sec) ∧
    -- (3) Dealer pairs have non-zero first component
    (∀ pairs, s.dealer.pairs = some pairs → ∀ i, (pairs i).1 ≠ 0) ∧
    -- (4) Buffer DTI integrity
    (∀ data, s.buffer (.dealerToIntermediary data) →
      ∃ sec pairs, s.dealer.secret = some sec ∧ s.dealer.pairs = some pairs ∧
        data = fun i => (sec, (pairs i).2)) ∧
    -- (5) Buffer DTR integrity
    (∀ data, s.buffer (.dealerToReceiver data) →
      ∃ sec pairs, s.dealer.secret = some sec ∧ s.dealer.pairs = some pairs ∧
        data = fun i => ((pairs i).1, (pairs i).1 * sec + (pairs i).2)) ∧
    -- (6) Intermediary received consistent
    (∀ intData, s.intermediary.received = some intData →
      ∃ sec pairs, s.dealer.secret = some sec ∧ s.dealer.pairs = some pairs ∧
        intData = fun i => (sec, (pairs i).2)) ∧
    -- (7) Receiver received consistent
    (∀ recvData, s.receiver.received = some recvData →
      ∃ sec pairs, s.dealer.secret = some sec ∧ s.dealer.pairs = some pairs ∧
        recvData = fun i => ((pairs i).1, (pairs i).1 * sec + (pairs i).2)) ∧
    -- (8) Verify response buffer integrity
    (∀ resp, s.buffer (.verifyResponse resp) →
      ∃ recvData selected,
        s.receiver.received = some recvData ∧
        s.receiver.selected = some selected ∧
        resp = fun i => if selected i then some (recvData i) else none) ∧
    -- (9) Intermediary verifyResp consistent
    (∀ resp, s.intermediary.verifyResp = some resp →
      ∃ recvData selected,
        s.receiver.received = some recvData ∧
        s.receiver.selected = some selected ∧
        resp = fun i => if selected i then some (recvData i) else none) ∧
    -- (10) Auth data buffer integrity
    (∀ authMsg, s.buffer (.authData authMsg) →
      ∃ selected intData,
        s.intermediary.selected = some selected ∧
        s.intermediary.received = some intData ∧
        authMsg = fun i => if selected i then none else some (intData i)) ∧
    -- (11) Receiver authData consistent
    (∀ authMsg, s.receiver.authData = some authMsg →
      ∃ selected intData,
        s.intermediary.selected = some selected ∧
        s.intermediary.received = some intData ∧
        authMsg = fun i => if selected i then none else some (intData i)) ∧
    -- (12) Verify request buffer integrity
    (∀ sel, s.buffer (.verifyRequest sel) → s.intermediary.selected = some sel) ∧
    -- (13) Receiver selected consistent with intermediary
    (∀ rsel, s.receiver.selected = some rsel → s.intermediary.selected = some rsel) ∧
    -- (14) Selection count preserved
    (∀ sel, s.intermediary.selected = some sel →
      (List.filter sel (List.finRange (2 * k))).length = k)

private theorem validity_inv_init :
    ∀ e, (system p k).valid_exec e → validity_inv p k e 0 := by
  intro e ⟨hinit, _⟩ _
  rw [show e.states 0 = initState p k from hinit]
  simp only [initState]
  exact ⟨fun _ => trivial,
         fun _ h => by simp at h,
         fun _ h => by simp at h,
         fun _ h => absurd h (by simp),
         fun _ h => absurd h (by simp),
         fun _ h => by simp at h,
         fun _ h => by simp at h,
         fun _ h => absurd h (by simp),
         fun _ h => by simp at h,
         fun _ h => absurd h (by simp),
         fun _ h => by simp at h,
         fun _ h => absurd h (by simp),
         fun _ h => by simp at h,
         fun _ h => by simp at h⟩

private theorem validity_inv_step :
    ∀ e n, (system p k).valid_exec e →
      validity_inv p k e n → validity_inv p k e (n + 1) := by
  intro e n ⟨_, hsteps⟩ ih hnocorr
  have hnocorr_n : ∀ j, j < n → ∀ proc, e.labels j ≠ Label.corrupt proc := by
    intro j hj proc; exact hnocorr j (Nat.lt_succ_of_lt hj) proc
  have hnocorr_at_n : ∀ proc, e.labels n ≠ Label.corrupt proc := by
    intro proc; exact hnocorr n (Nat.lt_succ_self n) proc
  have hinv := ih hnocorr_n
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hinv
  have hstep := hsteps n
  simp only [system] at hstep
  generalize he_l : e.labels n = l at hstep hnocorr_at_n
  -- Helper: bump secret persistence witness from n to n+1
  have h2' : ∀ sec, (e.states n).dealer.secret = some sec →
      ∃ m, m < n + 1 ∧ e.labels m = .input sec := fun sec hsec => by
    obtain ⟨m, hm, hlm⟩ := h2 sec hsec; exact ⟨m, Nat.lt_succ_of_lt hm, hlm⟩
  generalize e.states (n + 1) = s' at hstep
  cases hstep with
  | corrupt_step _ => exact absurd rfl (hnocorr_at_n _)
  | byzantine_step _ _ =>
    rename_i proc _ hcorr _; exact absurd hcorr (by rw [h1 proc]; simp)
  | input_step =>
    rename_i sec hsecnone _; dsimp only
    refine ⟨h1, ?_, h3, ?_, ?_, ?_, ?_, h8, h9, h10, h11, h12, h13, h14⟩
    · intro sec' hsec'; cases hsec'; exact ⟨n, Nat.lt_succ_self n, he_l⟩
    · intro data hbuf; obtain ⟨_, _, hs, _⟩ := h4 data hbuf; simp [hsecnone] at hs
    · intro data hbuf; obtain ⟨_, _, hs, _⟩ := h5 data hbuf; simp [hsecnone] at hs
    · intro d hi; obtain ⟨_, _, hs, _⟩ := h6 d hi; simp [hsecnone] at hs
    · intro d hr; obtain ⟨_, _, hs, _⟩ := h7 d hr; simp [hsecnone] at hs
  | generate_step =>
    rename_i pairs' _ hpnone hnonzero _; dsimp only
    refine ⟨h1, ?_, ?_, ?_, ?_, ?_, ?_, h8, h9, h10, h11, h12, h13, h14⟩
    · exact h2'
    · intro pairs hp; cases hp; exact hnonzero
    · intro data hbuf; obtain ⟨_, _, _, hp, _⟩ := h4 data hbuf; simp [hpnone] at hp
    · intro data hbuf; obtain ⟨_, _, _, hp, _⟩ := h5 data hbuf; simp [hpnone] at hp
    · intro d hi; obtain ⟨_, _, _, hp, _⟩ := h6 d hi; simp [hpnone] at hp
    · intro d hr; obtain ⟨_, _, _, hp, _⟩ := h7 d hr; simp [hpnone] at hp
  | send_dealerToIntermediary =>
    rename_i sec pairs' hsec hpairs _; dsimp only
    refine ⟨h1, h2', h3, ?_, ?_, h6, h7, ?_, h9, ?_, h11, ?_, h13, h14⟩
    · intro data hbuf; rcases hbuf with hbuf | hbuf
      · exact h4 data hbuf
      · injection hbuf with hbuf; subst hbuf; exact ⟨sec, pairs', hsec, hpairs, rfl⟩
    · intro data hbuf; rcases hbuf with hbuf | hbuf
      · exact h5 data hbuf
      · injection hbuf
    · intro resp hbuf; rcases hbuf with hbuf | hbuf
      · exact h8 resp hbuf
      · injection hbuf
    · intro authMsg hbuf; rcases hbuf with hbuf | hbuf
      · exact h10 authMsg hbuf
      · injection hbuf
    · intro sel hbuf; rcases hbuf with hbuf | hbuf
      · exact h12 sel hbuf
      · injection hbuf
  | send_dealerToReceiver =>
    rename_i sec pairs' hsec hpairs _; dsimp only
    refine ⟨h1, h2', h3, ?_, ?_, h6, h7, ?_, h9, ?_, h11, ?_, h13, h14⟩
    · intro data hbuf; rcases hbuf with hbuf | hbuf
      · exact h4 data hbuf
      · injection hbuf
    · intro data hbuf; rcases hbuf with hbuf | hbuf
      · exact h5 data hbuf
      · injection hbuf with hbuf; subst hbuf; exact ⟨sec, pairs', hsec, hpairs, rfl⟩
    · intro resp hbuf; rcases hbuf with hbuf | hbuf
      · exact h8 resp hbuf
      · injection hbuf
    · intro authMsg hbuf; rcases hbuf with hbuf | hbuf
      · exact h10 authMsg hbuf
      · injection hbuf
    · intro sel hbuf; rcases hbuf with hbuf | hbuf
      · exact h12 sel hbuf
      · injection hbuf
  | recv_intermediary =>
    rename_i data hbuf_in hnone_int _; dsimp only
    -- intermediary.received changed; buffer shrinks
    refine ⟨h1, h2', h3, ?_, ?_, ?_, h7, ?_, h9, ?_, ?_, ?_, h13, h14⟩
    · intro data' hbuf; exact h4 data' hbuf.1
    · intro data' hbuf; exact h5 data' hbuf.1
    · intro intData hint; cases hint; exact h4 data hbuf_in
    · intro resp hbuf; exact h8 resp hbuf.1
    · intro authMsg hbuf; exfalso
      obtain ⟨_, _, _, hr, _⟩ := h10 authMsg hbuf.1; simp [hnone_int] at hr
    · intro authMsg ha; exfalso
      obtain ⟨_, _, _, hr, _⟩ := h11 authMsg ha; simp [hnone_int] at hr
    · intro sel hbuf; exact h12 sel hbuf.1
  | recv_receiver_from_dealer =>
    rename_i data hbuf_in hnone_rec _; dsimp only
    -- receiver.received changed; buffer shrinks
    refine ⟨h1, h2', h3, ?_, ?_, h6, ?_, ?_, ?_, ?_, h11, ?_, h13, h14⟩
    · intro data' hbuf; exact h4 data' hbuf.1
    · intro data' hbuf; exact h5 data' hbuf.1
    · intro recvData hrec; cases hrec; exact h5 data hbuf_in
    · intro resp hbuf; exfalso
      obtain ⟨_, _, hr, _⟩ := h8 resp hbuf.1; simp [hnone_rec] at hr
    · intro resp hr; exfalso
      obtain ⟨_, _, hrd, _⟩ := h9 resp hr; simp [hnone_rec] at hrd
    · intro authMsg hbuf; exact h10 authMsg hbuf.1
    · intro sel hbuf; exact h12 sel hbuf.1
  | selectIndices_step =>
    rename_i selected _ hnone_sel hcount _; dsimp only
    refine ⟨h1, h2', h3, h4, h5, h6, h7, h8, h9, ?_, ?_, ?_, ?_, ?_⟩
    · intro authMsg hbuf; exfalso
      obtain ⟨_, _, hs, _⟩ := h10 authMsg hbuf; simp [hnone_sel] at hs
    · intro authMsg ha; exfalso
      obtain ⟨_, _, hs, _⟩ := h11 authMsg ha; simp [hnone_sel] at hs
    · intro sel hbuf; exfalso; have := h12 sel hbuf; simp [hnone_sel] at this
    · intro rsel hr; exfalso; have := h13 rsel hr; simp [hnone_sel] at this
    · intro sel hs; cases hs; exact hcount
  | send_verifyRequest =>
    rename_i selected hsel _; dsimp only
    refine ⟨h1, h2', h3, ?_, ?_, h6, h7, ?_, h9, ?_, h11, ?_, h13, h14⟩
    · intro data hbuf; rcases hbuf with hbuf | hbuf
      · exact h4 data hbuf
      · injection hbuf
    · intro data hbuf; rcases hbuf with hbuf | hbuf
      · exact h5 data hbuf
      · injection hbuf
    · intro resp hbuf; rcases hbuf with hbuf | hbuf
      · exact h8 resp hbuf
      · injection hbuf
    · intro authMsg hbuf; rcases hbuf with hbuf | hbuf
      · exact h10 authMsg hbuf
      · injection hbuf
    · intro sel hbuf; rcases hbuf with hbuf | hbuf
      · exact h12 sel hbuf
      · injection hbuf with hbuf; subst hbuf; exact hsel
  | recv_verifyRequest =>
    rename_i selected hbuf_in hnone_rsel _; dsimp only
    -- receiver.selected changed from none to some selected; buffer shrinks
    refine ⟨h1, h2', h3, ?_, ?_, h6, h7, ?_, ?_, ?_, h11, ?_, ?_, h14⟩
    · intro data hbuf; exact h4 data hbuf.1
    · intro data hbuf; exact h5 data hbuf.1
    · -- verifyResponse buffer: references receiver.received (unchanged)
      -- + receiver.selected (changed)
      intro resp hbuf; exfalso
      obtain ⟨_, _, _, hs, _⟩ := h8 resp hbuf.1; simp [hnone_rsel] at hs
    · -- verifyResp: references receiver.selected (changed)
      intro resp hr; exfalso
      obtain ⟨_, _, _, hs, _⟩ := h9 resp hr; simp [hnone_rsel] at hs
    · intro authMsg hbuf; exact h10 authMsg hbuf.1
    · intro sel hbuf; exact h12 sel hbuf.1
    · intro rsel hr; cases hr; exact h12 selected hbuf_in
  | send_verifyResponse =>
    rename_i selected data hsel hrec _; dsimp only
    refine ⟨h1, h2', h3, ?_, ?_, h6, h7, ?_, h9, ?_, h11, ?_, h13, h14⟩
    · intro data' hbuf; rcases hbuf with hbuf | hbuf
      · exact h4 data' hbuf
      · injection hbuf
    · intro data' hbuf; rcases hbuf with hbuf | hbuf
      · exact h5 data' hbuf
      · injection hbuf
    · intro resp hbuf; rcases hbuf with hbuf | hbuf
      · exact h8 resp hbuf
      · injection hbuf with hbuf; subst hbuf; exact ⟨data, selected, hrec, hsel, rfl⟩
    · intro authMsg hbuf; rcases hbuf with hbuf | hbuf
      · exact h10 authMsg hbuf
      · injection hbuf
    · intro sel hbuf; rcases hbuf with hbuf | hbuf
      · exact h12 sel hbuf
      · injection hbuf
  | recv_verifyResponse =>
    rename_i resp hbuf_in hnone_vr _; dsimp only
    -- intermediary.verifyResp set; buffer shrinks
    refine ⟨h1, h2', h3, ?_, ?_, h6, h7, ?_, ?_, ?_, h11, ?_, h13, h14⟩
    · intro data hbuf; exact h4 data hbuf.1
    · intro data hbuf; exact h5 data hbuf.1
    · intro resp' hbuf; exact h8 resp' hbuf.1
    · intro resp' hr; cases hr; exact h8 resp hbuf_in
    · intro authMsg hbuf; exact h10 authMsg hbuf.1
    · intro sel hbuf; exact h12 sel hbuf.1
  | checkVerification_step =>
    rename_i selected intData resp ok hsel hint hresp _ _ _; dsimp only
    refine ⟨h1, h2', h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  | send_authData =>
    rename_i selected intData hsel hint _ _; dsimp only
    refine ⟨h1, h2', h3, ?_, ?_, h6, h7, ?_, h9, ?_, h11, ?_, h13, h14⟩
    · intro data hbuf; rcases hbuf with hbuf | hbuf
      · exact h4 data hbuf
      · injection hbuf
    · intro data hbuf; rcases hbuf with hbuf | hbuf
      · exact h5 data hbuf
      · injection hbuf
    · intro resp hbuf; rcases hbuf with hbuf | hbuf
      · exact h8 resp hbuf
      · injection hbuf
    · intro authMsg hbuf; rcases hbuf with hbuf | hbuf
      · exact h10 authMsg hbuf
      · injection hbuf with hbuf; subst hbuf; exact ⟨selected, intData, hsel, hint, rfl⟩
    · intro sel hbuf; rcases hbuf with hbuf | hbuf
      · exact h12 sel hbuf
      · injection hbuf
  | recv_authData =>
    rename_i authMsg hbuf_in hnone_auth _; dsimp only
    -- receiver.authData set; buffer shrinks
    refine ⟨h1, h2', h3, ?_, ?_, h6, h7, ?_, h9, ?_, ?_, ?_, h13, h14⟩
    · intro data hbuf; exact h4 data hbuf.1
    · intro data hbuf; exact h5 data hbuf.1
    · intro resp hbuf; exact h8 resp hbuf.1
    · intro authMsg' hbuf; exact h10 authMsg' hbuf.1
    · intro authMsg' ha; cases ha; exact h10 authMsg hbuf_in
    · intro sel hbuf; exact h12 sel hbuf.1
  | receiverDecide_step =>
    rename_i recvData authMsg selected result hrec hauth hsel _ _ _; dsimp only
    refine ⟨h1, h2', h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-- Extract preconditions from a checkVerification step. -/
private theorem checkVerification_preconditions
    (s s' : State p k) (ok : Bool)
    (hstep : step p k s (.checkVerification ok) s') :
    ∃ selected intData resp,
      s.intermediary.selected = some selected ∧
      s.intermediary.received = some intData ∧
      s.intermediary.verifyResp = some resp ∧
      s.intermediary.verified = none ∧
      s.corrupted .Intermediary = false ∧
      (ok = true ↔ ∀ i, selected i = true →
        ∀ b c, resp i = some (b, c) →
          c = b * (intData i).1 + (intData i).2) := by
  cases hstep
  case checkVerification_step =>
    rename_i selected intData resp hsel hint hresp hnone huncorr hiff
    exact ⟨selected, intData, resp, hsel, hint, hresp, hnone, huncorr, hiff⟩

/-- Extract preconditions from a receiverDecide step. -/
private theorem receiverDecide_preconditions
    (s s' : State p k) (result : Option (V p))
    (hstep : step p k s (.receiverDecide result) s') :
    ∃ recvData authMsg selected,
      s.receiver.received = some recvData ∧
      s.receiver.authData = some authMsg ∧
      s.receiver.selected = some selected ∧
      s.corrupted .Receiver = false ∧
      (result.isSome = true ↔ ∃ i, selected i = false ∧
        ∃ sv y, authMsg i = some (sv, y) ∧
          (recvData i).2 = (recvData i).1 * sv + y) ∧
      (∀ s_val, result = some s_val → ∃ i, selected i = false ∧
        ∃ y, authMsg i = some (s_val, y) ∧
          (recvData i).2 = (recvData i).1 * s_val + y) := by
  cases hstep
  case receiverDecide_step =>
    rename_i recvData authMsg selected hrec hauth hsel huncorr hisSome hresult
    exact ⟨recvData, authMsg, selected, hrec, hauth, hsel, huncorr, hisSome, hresult⟩

/-- Validity holds for all valid executions of the Rabin ICP system,
    provided k > 0 (so that authentication has at least one non-selected index). -/
theorem validity_holds (hk : k > 0) :
    ∀ e, (system p k).valid_exec e → validity p k e := by
  intro e hv hnocorrupt
  have hinv : ∀ n, validity_inv p k e n :=
    fun n => by
      induction n with
      | zero => exact validity_inv_init p k e hv
      | succ m ih => exact validity_inv_step p k e m hv ih
  constructor
  · -- Part 1: verification always succeeds
    intro n ok hlabel
    have hinv_n := hinv n
    have hnocorr_n : ∀ j, j < n → ∀ proc, e.labels j ≠ Label.corrupt proc :=
      fun j _ proc => hnocorrupt j proc
    obtain ⟨_, _, _, _, _, h6, h7, _, h9, _, _, _, _, _⟩ := hinv_n hnocorr_n
    have hstep := hv.2 n
    simp only [system] at hstep
    have hstep' : step p k (e.states n) (.checkVerification ok) (e.states (n + 1)) :=
      hlabel ▸ hstep
    obtain ⟨selected, intData, resp, hsel, hint, hresp, _, _, hiff⟩ :=
      checkVerification_preconditions p k _ _ _ hstep'
    -- Show the check condition is true, hence ok = true
    exact hiff.2 (fun i hsi b c hrespi => by
      obtain ⟨recvData, sel, hrec, hsel', hresp_eq⟩ := h9 resp hresp
      obtain ⟨sec, pairs, hsec, hpairs, hint_eq⟩ := h6 intData hint
      obtain ⟨sec', pairs', hsec', hpairs', hrec_eq⟩ := h7 recvData hrec
      -- Unify: dealer.secret and dealer.pairs are unique
      have heqs : sec = sec' := Option.some.inj (hsec ▸ hsec')
      have heqp : pairs = pairs' := Option.some.inj (hpairs ▸ hpairs')
      subst heqs heqp hrec_eq hresp_eq hint_eq
      -- hrespi: (if sel i = true then some (recvData i) else none) = some (b, c)
      simp only [Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hrespi
      -- hrespi should be: sel i = true ∧ recvData i = (b, c)
      obtain ⟨_, hb, hc⟩ := hrespi
      simp only at hb hc ⊢
      rw [← hb, ← hc])
  · -- Part 2: authentication returns the secret
    intro n result hlabel
    have hinv_n := hinv n
    have hnocorr_n : ∀ j, j < n → ∀ proc, e.labels j ≠ Label.corrupt proc :=
      fun j _ proc => hnocorrupt j proc
    obtain ⟨_, h2, _, _, _, h6, h7, _, _, _, h11, _, h13, h14⟩ := hinv_n hnocorr_n
    have hstep := hv.2 n
    simp only [system] at hstep
    have hstep' : step p k (e.states n) (.receiverDecide result) (e.states (n + 1)) :=
      hlabel ▸ hstep
    obtain ⟨recvData, authMsg, selected, hrec, hauth, hsel, _, hisSome, hresult⟩ :=
      receiverDecide_preconditions p k _ _ _ hstep'
    -- From h11: receiver.authData matches intermediary data
    obtain ⟨isel, intData, hisel, hint, hauth_eq⟩ := h11 authMsg hauth
    -- From h13: receiver.selected matches intermediary.selected
    have hsel_eq : selected = isel :=
      Option.some.inj ((h13 selected hsel).symm ▸ hisel)
    subst hsel_eq
    -- From h6: intermediary.received matches dealer
    obtain ⟨sec, pairs, hsec, hpairs, hint_eq⟩ := h6 intData hint
    -- From h7: receiver.received matches dealer
    obtain ⟨sec', pairs', hsec', hpairs', hrec_eq⟩ := h7 recvData hrec
    -- Unify sec/pairs
    have heqs : sec = sec' := Option.some.inj (hsec ▸ hsec')
    have heqp : pairs = pairs' := Option.some.inj (hpairs ▸ hpairs')
    subst heqs heqp hrec_eq hint_eq hauth_eq
    -- From h14: selection count = k, so with k > 0 there's a non-selected index
    have hcount := h14 selected hisel
    -- From h2: dealer secret was input in the past
    obtain ⟨m, hm, hlm⟩ := h2 sec hsec
    refine ⟨m, sec, hm, hlm, ?_⟩
    -- Show result = some sec
    -- First, there exists a non-selected index (since k > 0 and exactly k selected)
    have ⟨idx, hidx⟩ : ∃ i : Fin (2 * k), selected i = false := by
      -- If all are selected, filter length = 2k, contradicting hcount and hk
      suffices h : ¬ ∀ i : Fin (2 * k), selected i = true by
        obtain ⟨i, hi⟩ := Classical.not_forall.mp h
        exact ⟨i, Bool.eq_false_of_not_eq_true hi⟩
      intro hall
      have : (List.filter selected (List.finRange (2 * k))).length = 2 * k := by
        rw [List.filter_eq_self.mpr (by intro x _; exact hall x)]
        simp [List.length_finRange]
      omega
    -- result.isSome = true (there exists a valid authentication at idx)
    have hsome : result.isSome = true := hisSome.2
      ⟨idx, hidx, sec, (pairs idx).2, by simp [hidx], by simp⟩
    -- Extract the value from result
    match hres : result with
    | none => simp at hsome
    | some s_val =>
      -- From hresult: s_val appears in authMsg at some non-selected index
      obtain ⟨j, hj_sel, y, hj_auth, _⟩ := hresult s_val rfl
      -- authMsg j = if selected j then none else some (sec, (pairs j).2)
      simp only [hj_sel, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
        Prod.mk.injEq] at hj_auth
      -- hj_auth gives sec = s_val
      exact congrArg some hj_auth.1.symm

/-! ### Secrecy Property

    If the Dealer and the Intermediary are correct (not corrupted), and the
    authentication phase has not started (no authData messages have been sent),
    then the adversary cannot infer the secret. -/

/-- The trace property "the Dealer's secret is `s`": whenever the dealer's
    secret is defined, it equals `s`. Vacuously true if the secret is never set. -/
def secretIs (s : V p) : LTS.Execution (State p k) (Label p k) → Prop :=
  fun e => ∀ n s₀, (e.states n).dealer.secret = some s₀ → s₀ = s

/-- The execution condition: dealer and intermediary are honest, a secret
    has been input, and the authentication phase has not started. -/
def honestPreAuth : LTS.Execution (State p k) (Label p k) → Prop :=
  fun e =>
    -- The dealer has input a secret at some step
    (∃ n, observeLabel p k (e.states n) (e.labels n) = .honest .input) ∧
    -- At every step, dealer and intermediary are honest
    (∀ n, (e.states n).corrupted .Dealer = false ∧
          (e.states n).corrupted .Intermediary = false) ∧
    -- Authentication phase has not started
    (∀ n, (∀ (data : Fin (2 * k) → Option (Pair p)),
            ¬(e.states n).buffer (.authData data)) ∧
          (e.states n).receiver.authData = none)

/-- View-level version of `honestPreAuth`: the view is producible by
    a valid execution satisfying `honestPreAuth`. -/
def honestPreAuthView : Observation.ExecView (StateSignal p k) (LabelSignal p k) → Prop :=
  fun v => ∃ e, (PLTS.toLTS (adversary p k).sys).valid_exec e ∧
    (adversaryObs p k).view e = v ∧ honestPreAuth p k e

/-- `honestPreAuth` on a valid execution implies `honestPreAuthView` on its view. -/
theorem honestPreAuth_implies_view
    (e : LTS.Execution (State p k) (Label p k))
    (hvalid : (PLTS.toLTS (adversary p k).sys).valid_exec e)
    (hpre : honestPreAuth p k e) :
    honestPreAuthView p k ((adversaryObs p k).view e) :=
  ⟨e, hvalid, rfl, hpre⟩

/-! ### Secret Remap

    Given an execution with secret `s` and pairs `(b_i, y_i)`, we construct
    an execution with secret `s'` and pairs `(b_i, y'_i)` where
    `y'_i = y_i + b_i * (s - s')`. The key identity is:
      `b_i * s + y_i = b_i * s' + y'_i`
    so `c_i` values are unchanged. The remap only affects dealer-internal
    state and the dealerToIntermediary message. Everything else (DTR messages,
    buffer contents from non-dealer sources, receiver state, verification
    checks) flows through unchanged. -/

/-- Remap dealer pairs: `(b_i, y_i) ↦ (b_i, y_i + b_i * (s - s'))`. -/
def remapPairs (s s' : V p)
    (pairs : Fin (2 * k) → V p × V p) : Fin (2 * k) → V p × V p :=
  fun i => ((pairs i).1, (pairs i).2 + (pairs i).1 * (s - s'))

/-- Remap a DTI/auth data entry: `(s, y_i) ↦ (s', y'_i)` using dealer pairs for `b_i`. -/
def remapDTI (s s' : V p) (pairs : Fin (2 * k) → V p × V p)
    (data : Fin (2 * k) → Pair p) : Fin (2 * k) → Pair p :=
  fun i => (if (data i).1 = s then s' else (data i).1,
            (data i).2 + (pairs i).1 * (s - s'))

/-- Remap optional auth data entries: `some (s, y_i) ↦ some (s', y'_i)`. -/
def remapAuthData (s s' : V p) (pairs : Fin (2 * k) → V p × V p)
    (data : Fin (2 * k) → Option (Pair p)) : Fin (2 * k) → Option (Pair p) :=
  fun i => (data i).map (fun (x, y) => (if x = s then s' else x, y + (pairs i).1 * (s - s')))

/-- Remap a global state: replace secret `s` by `s'`, adjust dealer pairs,
    intermediary received data, and DTI messages in the buffer.
    - Dealer: `secret s → s'`, `pairs (b_i, y_i) → (b_i, y'_i)`
    - Intermediary received: `(s, y_i) → (s', y'_i)` (same transform as DTI message)
    - Buffer: DTI messages `(s, y_i) → (s', y'_i)`
    - Receiver, verification responses, verified, selected, corrupted: unchanged
      (receiver holds `c_i = b_i*s + y_i = b_i*s' + y'_i`, invariant) -/
def remapState (s s' : V p) (st : State p k) : State p k where
  dealer := {
    secret := if st.dealer.secret = some s then some s' else st.dealer.secret
    pairs := st.dealer.pairs.map (remapPairs p k s s')
  }
  intermediary := { st.intermediary with
    received := match st.dealer.pairs with
      | some pairs => st.intermediary.received.map (remapDTI p k s s' pairs)
      | none => st.intermediary.received
    verified := match st.intermediary.verified, st.intermediary.selected,
        st.intermediary.received, st.intermediary.verifyResp, st.dealer.pairs with
      | some _, some sel, some intData, some resp, some pairs =>
        let intData' := remapDTI p k s s' pairs intData
        let check : Fin (2 * k) → Bool := fun i =>
          if sel i then
            match resp i with
            | some (b, c) => decide (c = b * (intData' i).1 + (intData' i).2)
            | none => true
          else true
        some (List.finRange (2 * k) |>.all check)
      | v, _, _, _, _ => v
  }
  receiver := { st.receiver with
    authData := match st.dealer.pairs with
      | some pairs => st.receiver.authData.map (remapAuthData p k s s' pairs)
      | none => st.receiver.authData
  }
  buffer := fun m => match m, st.dealer.pairs with
    | .dealerToIntermediary data, some pairs =>
        ∃ orig, st.buffer (.dealerToIntermediary orig) ∧
          data = remapDTI p k s s' pairs orig
    | .authData data, some pairs =>
        ∃ orig, st.buffer (.authData orig) ∧
          data = remapAuthData p k s s' pairs orig
    | m, _ => st.buffer m
  corrupted := st.corrupted

/-- Remap a label: actions carrying secret-dependent data are transformed.
    - `input s` → `input s'`
    - `generate pairs` → `generate (remapPairs pairs)`
    - `send/recv (dealerToIntermediary _)` → remap `(s, y_i) → (s', y'_i)`
    - `send/recv (authData _)` → remap `some (s, y_i) → some (s', y'_i)`
    - All other labels unchanged (DTR carries `(b_i, c_i)` which is invariant). -/
def remapLabel (s s' : V p) (st : State p k) :
    Label p k → Label p k
  | .input s_val => .input (if s_val = s then s' else s_val)
  | .generate pairs => .generate (remapPairs p k s s' pairs)
  | .send (.dealerToIntermediary data) =>
      .send (.dealerToIntermediary (match st.dealer.pairs with
        | some pairs => remapDTI p k s s' pairs data
        | none => data))
  | .recv (.dealerToIntermediary data) =>
      .recv (.dealerToIntermediary (match st.dealer.pairs with
        | some pairs => remapDTI p k s s' pairs data
        | none => data))
  | .send (.authData data) =>
      .send (.authData (match st.dealer.pairs with
        | some pairs => remapAuthData p k s s' pairs data
        | none => data))
  | .recv (.authData data) =>
      .recv (.authData (match st.dealer.pairs with
        | some pairs => remapAuthData p k s s' pairs data
        | none => data))
  | .checkVerification _ =>
      .checkVerification (match st.intermediary.selected, st.intermediary.received,
          st.intermediary.verifyResp, st.dealer.pairs with
        | some sel, some intData, some resp, some pairs =>
          let intData' := remapDTI p k s s' pairs intData
          let check : Fin (2 * k) → Bool := fun i =>
            if sel i then
              match resp i with
              | some (b, c) => decide (c = b * (intData' i).1 + (intData' i).2)
              | none => true
            else true
          (List.finRange (2 * k)).all check
        | _, _, _, _ => false)
  | .receiverDecide result =>
      .receiverDecide (result.map (fun s_val => if s_val = s then s' else s_val))
  | l => l

/-! ### Remap Arithmetic

    Core arithmetic facts for the secret remap: the identity
    `b * s + y = b * s' + (y + b * (s - s'))`, round-trip and injectivity
    of `remapDTI`. -/

/-- Core arithmetic identity: `b * s + y = b * s' + (y + b * (s - s'))`. -/
theorem remap_identity (b y s s' : V p) :
    b * s' + (y + b * (s - s')) = b * s + y := by ring

/-- `remapDTI s' s` is the inverse of `remapDTI s s'` on data with first component `s`. -/
theorem remapDTI_inv (s s' : V p) (pairs : Fin (2 * k) → V p × V p)
    (data : Fin (2 * k) → Pair p) (hfst : ∀ i, (data i).1 = s) :
    remapDTI p k s' s pairs (remapDTI p k s s' pairs data) = data := by
  have add_left_cancel : ∀ (a b c : V p), a + b = a + c → b = c :=
    fun _ _ _ h => _root_.add_left_cancel h
  funext i; simp only [remapDTI]
  have hfi := hfst i
  have h1 : (if (if (data i).1 = s then s' else (data i).1) = s' then s
      else if (data i).1 = s then s' else (data i).1) = (data i).1 := by simp [hfi]
  -- Second component: use two instances of remap_identity + cancellation
  have hremap1 := remap_identity p (pairs i).1 (data i).2 s s'
  have hremap2 := remap_identity p (pairs i).1 ((data i).2 + (pairs i).1 * (s - s')) s' s
  have h2 : (data i).2 + (pairs i).1 * (s - s') + (pairs i).1 * (s' - s) = (data i).2 :=
    add_left_cancel ((pairs i).1 * s) _ _ (hremap2.trans hremap1)
  change (_, _) = data i; rw [h1, h2]

/-- `remapDTI s s'` is injective on data with first component `s`. -/
theorem remapDTI_injective (s s' : V p) (pairs : Fin (2 * k) → V p × V p)
    (a b : Fin (2 * k) → Pair p) (ha : ∀ i, (a i).1 = s) (hb : ∀ i, (b i).1 = s)
    (h : remapDTI p k s s' pairs a = remapDTI p k s s' pairs b) : a = b := by
  have := congrArg (remapDTI p k s' s pairs) h
  rw [remapDTI_inv p k s s' pairs a ha, remapDTI_inv p k s s' pairs b hb] at this
  exact this

/-! ### Utilities -/

/-- When p ≥ 2, for any value there exists a different value. -/
theorem exists_ne (hp2 : p ≥ 2) (s : V p) : ∃ s' : V p, s' ≠ s := by
  haveI : Fact (1 < p) := ⟨by omega⟩
  by_cases hs : s = 0
  · exact ⟨1, by rw [hs]; exact zero_ne_one.symm⟩
  · exact ⟨0, fun h => hs h.symm⟩

/-! ### Execution Invariants

    State invariants proved by induction over valid executions.
    Each follows the pattern: prove a step-level preservation lemma,
    then lift to the execution by induction on step count. -/

/-- Execution invariant: DTI messages in the buffer imply dealer pairs are set.
    This holds because `send_dealerToIntermediary` (the only step adding DTI messages
    when the dealer is honest) requires `dealer.pairs = some pairs`. -/
theorem exec_inv_buf_dti
    (e : LTS.Execution (State p k) (Label p k))
    (hvalid : (system p k).valid_exec e)
    (hhonest : ∀ n, (e.states n).corrupted .Dealer = false) :
    ∀ n data, (e.states n).buffer (.dealerToIntermediary data) →
      (e.states n).dealer.pairs ≠ none := by
  -- Prove contrapositive: pairs = none → no DTI in buffer
  suffices hinv : ∀ n, (e.states n).dealer.pairs = none →
      ∀ data, ¬(e.states n).buffer (.dealerToIntermediary data) by
    intro n data hbuf hpairs; exact hinv n hpairs data hbuf
  -- Step-level preservation of P(st) := pairs = none → no DTI in buffer
  have hstep_pres : ∀ st l st', step p k st l st' →
      st.corrupted .Dealer = false →
      (st.dealer.pairs = none → ∀ data, ¬st.buffer (.dealerToIntermediary data)) →
      (st'.dealer.pairs = none → ∀ data, ¬st'.buffer (.dealerToIntermediary data)) := by
    intro st l st' hs hcorr hP hpairs' data hbuf'
    cases hs with
    | generate_step _ _ _ _ => simp at hpairs'
    | send_dealerToIntermediary _ _ _ hpairs _ => simp [hpairs] at hpairs'
    | send_dealerToReceiver _ _ _ hpairs _ => simp [hpairs] at hpairs'
    | byzantine_step proc _ hcorr_proc hsender =>
      cases hbuf' with
      | inl h => exact hP hpairs' data h
      | inr h =>
        rw [← h] at hsender; simp only [Msg.sender] at hsender
        rw [← hsender] at hcorr_proc; rw [hcorr] at hcorr_proc
        exact absurd hcorr_proc nofun
    | _ =>
      exact hP hpairs' data
        (by first | exact hbuf' | exact hbuf'.1 | exact hbuf'.elim id nofun)
  -- Induction
  intro n; induction n with
  | zero =>
    have hinit := hvalid.1; simp only [system] at hinit; rw [hinit]
    intro _ _ hbuf; exact hbuf
  | succ n ih =>
    exact hstep_pres _ _ _ (hvalid.2 n) (hhonest n) ih

/-- Execution invariant: intermediary received requires dealer pairs to be set.
    This holds because `recv_intermediary` consumes a DTI message from the buffer,
    which can only exist after `send_dealerToIntermediary` (which requires pairs). -/
theorem exec_inv_recv_pairs
    (e : LTS.Execution (State p k) (Label p k))
    (hvalid : (system p k).valid_exec e)
    (hhonest : ∀ n, (e.states n).corrupted .Dealer = false) :
    ∀ n, (e.states n).dealer.pairs = none →
      (e.states n).intermediary.received = none := by
  -- Step-level: P(st) = (pairs = none → received = none) is preserved
  -- recv_intermediary sets received but needs DTI in buffer, which needs pairs ≠ none
  have hstep_pres : ∀ st l st', step p k st l st' →
      st.corrupted .Dealer = false →
      (st.dealer.pairs = none → ∀ data, ¬st.buffer (.dealerToIntermediary data)) →
      (st.dealer.pairs = none → st.intermediary.received = none) →
      (st'.dealer.pairs = none → st'.intermediary.received = none) := by
    intro st l st' hs hcorr hno_dti hP hpairs'
    cases hs with
    | generate_step _ _ _ _ => simp at hpairs'
    | send_dealerToIntermediary _ _ _ hpairs _ => simp [hpairs] at hpairs'
    | send_dealerToReceiver _ _ _ hpairs _ => simp [hpairs] at hpairs'
    | recv_intermediary _ hbuf _ _ =>
      -- needs DTI in buffer, but pairs = none → no DTI
      exact absurd hbuf (hno_dti hpairs' _)
    | _ => exact hP hpairs'
  -- Also need the buf_dti invariant for the step
  have hbuf_inv := exec_inv_buf_dti p k e hvalid hhonest
  intro n; induction n with
  | zero =>
    have hinit := hvalid.1; simp only [system] at hinit; rw [hinit]
    intro _; rfl
  | succ n ih =>
    have hno_dti : (e.states n).dealer.pairs = none →
        ∀ data, ¬(e.states n).buffer (.dealerToIntermediary data) := by
      intro hp data hbuf; exact hbuf_inv n data hbuf hp
    exact hstep_pres _ _ _ (hvalid.2 n) (hhonest n) hno_dti ih

/-- Execution invariant: if `verified` is set, then `selected`, `received`,
    `verifyResp`, and `dealer.pairs` are all set. -/
theorem exec_inv_verified
    (e : LTS.Execution (State p k) (Label p k))
    (hvalid : (system p k).valid_exec e)
    (hhonest : ∀ n, (e.states n).corrupted .Dealer = false) :
    ∀ n, (e.states n).intermediary.verified ≠ none →
      (e.states n).intermediary.selected ≠ none ∧
      (e.states n).intermediary.received ≠ none ∧
      (e.states n).intermediary.verifyResp ≠ none ∧
      (e.states n).dealer.pairs ≠ none := by
  -- Step-level: verified ≠ none → selected, received, verifyResp ≠ none
  have hstep_Q : ∀ st l st', step p k st l st' →
      (st.intermediary.verified ≠ none →
        st.intermediary.selected ≠ none ∧ st.intermediary.received ≠ none ∧
        st.intermediary.verifyResp ≠ none) →
      (st'.intermediary.verified ≠ none →
        st'.intermediary.selected ≠ none ∧ st'.intermediary.received ≠ none ∧
        st'.intermediary.verifyResp ≠ none) := by
    intro st l st' hs hQ hv'
    cases hs with
    | checkVerification_step _ _ _ _ hsel hrecv hresp _ _ _ =>
      exact ⟨by rw [hsel]; exact nofun, by rw [hrecv]; exact nofun, by rw [hresp]; exact nofun⟩
    | selectIndices_step _ _ _ _ _ =>
      obtain ⟨_, hr, hv⟩ := hQ hv'; exact ⟨nofun, hr, hv⟩
    | recv_intermediary _ _ _ _ =>
      obtain ⟨hs, _, hv⟩ := hQ hv'; exact ⟨hs, nofun, hv⟩
    | recv_verifyResponse _ _ _ _ =>
      obtain ⟨hs, hr, _⟩ := hQ hv'; exact ⟨hs, hr, nofun⟩
    | _ => exact hQ hv'
  -- Lift to execution by induction
  have hQ_exec : ∀ n, (e.states n).intermediary.verified ≠ none →
      (e.states n).intermediary.selected ≠ none ∧
      (e.states n).intermediary.received ≠ none ∧
      (e.states n).intermediary.verifyResp ≠ none := by
    intro n; induction n with
    | zero =>
      have hinit := hvalid.1; simp only [system] at hinit; rw [hinit]
      intro h; exact absurd rfl h
    | succ n ih => exact hstep_Q _ _ _ (hvalid.2 n) ih
  -- Combine with exec_inv_recv_pairs for pairs ≠ none
  have hrecv_pairs := exec_inv_recv_pairs p k e hvalid hhonest
  intro n hv
  obtain ⟨hs, hr, hvr⟩ := hQ_exec n hv
  exact ⟨hs, hr, hvr, fun hpairs => hr (hrecv_pairs n hpairs)⟩

/-- Execution invariant: DTI messages in the buffer have first component equal
    to the dealer's secret. This holds because `send_dealerToIntermediary` sends
    `(s, y_i)` and no other honest step adds DTI messages. -/
theorem exec_inv_buf_fst
    (e : LTS.Execution (State p k) (Label p k))
    (hvalid : (system p k).valid_exec e)
    (hhonest : ∀ n, (e.states n).corrupted .Dealer = false ∧
                     (e.states n).corrupted .Intermediary = false)
    (hsecret : secretIs p k s₀ e) :
    ∀ n data, (e.states n).buffer (.dealerToIntermediary data) →
      (e.states n).dealer.pairs ≠ none →
      ∀ i, (data i).1 = s₀ := by
  -- Step-level preservation
  have hstep_pres : ∀ st l st', step p k st l st' →
      st.corrupted .Dealer = false →
      (∀ sv, st.dealer.secret = some sv → sv = s₀) →
      (st.dealer.pairs = none → ∀ data, ¬st.buffer (.dealerToIntermediary data)) →
      (∀ data, st.buffer (.dealerToIntermediary data) →
        st.dealer.pairs ≠ none → ∀ i, (data i).1 = s₀) →
      (∀ data, st'.buffer (.dealerToIntermediary data) →
        st'.dealer.pairs ≠ none → ∀ i, (data i).1 = s₀) := by
    intro st l st' hs hcorr hsec_st hno_dti hP data hbuf' hpairs' i
    cases hs with
    | send_dealerToIntermediary sv pairs_val hsec hpairs _ =>
      cases hbuf' with
      | inl h => exact hP data h (by rw [hpairs]; exact nofun) i
      | inr h =>
        have := congrFun (Msg.dealerToIntermediary.inj h) i
        simp only at this; rw [this]; exact hsec_st sv hsec
    | generate_step _ _ hnone _ =>
      exact absurd hbuf' (hno_dti hnone data)
    | byzantine_step proc _ hcorr_proc hsender =>
      cases hbuf' with
      | inl h => exact hP data h hpairs' i
      | inr h =>
        rw [← h] at hsender; simp only [Msg.sender] at hsender
        rw [← hsender] at hcorr_proc; rw [hcorr] at hcorr_proc; exact absurd hcorr_proc nofun
    | _ =>
      exact hP data
        (by first | exact hbuf' | exact hbuf'.1 | exact hbuf'.elim id nofun) hpairs' i
  -- Induction
  intro n; induction n with
  | zero =>
    have hinit := hvalid.1; simp only [system] at hinit; rw [hinit]
    intro _ hbuf; exact absurd hbuf id
  | succ n ih =>
    have hbuf_dti_n := exec_inv_buf_dti p k e hvalid (fun m => (hhonest m).1)
    exact hstep_pres _ _ _ (hvalid.2 n) (hhonest n).1 (hsecret n)
      (fun hp data hbuf => hbuf_dti_n n data hbuf hp) ih

/-! ### Buffer heq helpers

    Common proof patterns for buffer extensionality in `remapState_preserves_step`.
    When the buffer modification adds/removes a non-DTI, non-authData message,
    the DTI/authData pushforward sub-goals follow one of two patterns. -/

section BufHeq
/-- Close DTI/authData sub-goals when buffer adds a non-DTI/authData message. -/
macro "buf_heq_add" : tactic =>
  `(tactic| all_goals (split <;> first
    | exact propext ⟨fun h => h.elim Or.inl nofun, fun h => h.elim Or.inl nofun⟩
    | exact propext ⟨
        fun ⟨o, hb, he⟩ => Or.inl ⟨o, hb.elim id nofun, he⟩,
        fun h => h.elim (fun ⟨o, hb, he⟩ => ⟨o, Or.inl hb, he⟩) nofun⟩))

/-- Close DTI/authData sub-goals when buffer removes a non-DTI/authData message. -/
macro "buf_heq_remove" : tactic =>
  `(tactic| all_goals (split <;> first
    | exact propext ⟨fun h => ⟨h.1, nofun⟩, fun h => ⟨h.1, nofun⟩⟩
    | exact propext ⟨
        fun ⟨o, ⟨hb, _⟩, he⟩ => ⟨⟨o, hb, he⟩, nofun⟩,
        fun ⟨⟨o, hb, he⟩, _⟩ => ⟨o, ⟨hb, nofun⟩, he⟩⟩))

/-- Full buffer heq for add: unfold, split by Msg, close trivial cases, apply add pattern. -/
macro "buf_heq_full_add" : tactic =>
  `(tactic| (simp only [remapState]; congr 1; funext m; cases m <;> (try rfl); buf_heq_add))

/-- Full buffer heq for remove: unfold, split by Msg, close trivial cases, apply remove pattern. -/
macro "buf_heq_full_remove" : tactic =>
  `(tactic| (simp only [remapState]; congr 1; funext m; cases m <;> (try rfl); buf_heq_remove))
end BufHeq

/-! ### Step Preservation

    The core simulation lemma: each step of the original execution is
    preserved by the secret remap, under honesty and invariant hypotheses. -/

/-- Each step of the original execution is preserved by the remap, given
    dealer/intermediary honesty and standard execution invariants. -/
theorem remapState_preserves_step
    (s s' : V p) (st st' : State p k) (l : Label p k)
    (hstep : step p k st l st')
    (hhon : st.corrupted .Dealer = false ∧ st.corrupted .Intermediary = false)
    (hhon' : st'.corrupted .Dealer = false ∧ st'.corrupted .Intermediary = false)
    (hsec_inv : st.dealer.secret = some s ∨ st.dealer.secret = none)
    (hsec_inv' : st'.dealer.secret = some s ∨ st'.dealer.secret = none)
    -- DTI messages in the buffer have first component = s
    (hbuf_fst : ∀ data, st.buffer (.dealerToIntermediary data) →
      st.dealer.pairs ≠ none → ∀ i, (data i).1 = s)
    (hbuf_fst' : ∀ data, st'.buffer (.dealerToIntermediary data) →
      st'.dealer.pairs ≠ none → ∀ i, (data i).1 = s)
    -- If verification happened, all fields feeding into the verified remap are set
    (hverif_inv : st.intermediary.verified ≠ none →
      st.intermediary.selected ≠ none ∧
      st.intermediary.received ≠ none ∧
      st.intermediary.verifyResp ≠ none ∧
      st.dealer.pairs ≠ none)
    -- DTI in buffer implies pairs are set
    (hbuf_dti : ∀ data, st.buffer (.dealerToIntermediary data) →
      st.dealer.pairs ≠ none)
    -- Intermediary received requires pairs
    (hrecv_inv : st.dealer.pairs = none → st.intermediary.received = none)
    -- Authentication phase has not started
    (hauth : ∀ data, ¬st.buffer (.authData data))
    (hauth' : ∀ data, ¬st'.buffer (.authData data))
    (hauth_recv : st.receiver.authData = none) :
    step p k (remapState p k s s' st) (remapLabel p k s s' st l)
      (remapState p k s s' st') := by
  obtain ⟨hhon_d, hhon_i⟩ := hhon
  obtain ⟨hhon'_d, hhon'_i⟩ := hhon'
  cases hstep
  -- Contradiction cases: honest dealer/intermediary can't be corrupted
  case send_authData => exfalso; exact hauth' _ (Or.inr rfl)
  case recv_authData => exfalso; rename_i hbuf_msg _ _; exact hauth _ hbuf_msg
  case receiverDecide_step =>
    exfalso; rename_i _ h_recv_auth _ _ _ _; simp [hauth_recv] at h_recv_auth
  -- Corruption: only Receiver can be corrupted
  case corrupt_step proc hcorr =>
    cases proc with
    | Dealer => simp [update] at hhon'_d
    | Intermediary => simp [update] at hhon'_i
    | Receiver =>
      simp only [remapState, remapLabel]
      exact step.corrupt_step _ _ hcorr
  -- Byzantine: only Receiver, only verifyResponse
  case byzantine_step proc m hcorr hsend =>
    cases proc with
    | Dealer => exact absurd hcorr (by simp [hhon_d])
    | Intermediary => exact absurd hcorr (by simp [hhon_i])
    | Receiver =>
      cases m with
      | dealerToIntermediary | dealerToReceiver | verifyRequest | authData =>
        simp [Msg.sender] at hsend
      | verifyResponse data =>
        have heq : remapState p k s s'
            { st with buffer := fun m' => st.buffer m' ∨ m' = .verifyResponse data } =
          { remapState p k s s' st with
            buffer := fun m' =>
              (remapState p k s s' st).buffer m' ∨ m' = .verifyResponse data } := by
          buf_heq_full_add
        simp only [remapLabel]
        rw [heq]
        exact step.byzantine_step _ _ _ hcorr hsend
  -- Input / generate: dealer-only changes
  case input_step sv hnone hcorr =>
    have heq : remapState p k s s' { st with dealer := { st.dealer with secret := some sv } } =
      { remapState p k s s' st with
        dealer := { (remapState p k s s' st).dealer with
          secret := some (if sv = s then s' else sv) } } := by
      simp only [remapState]
      congr 1; congr 1
      split <;> split <;> first | rfl | (rename_i h1 h2; simp [h2] at h1)
    simp only [remapLabel]
    rw [heq]
    exact step.input_step _ _
      (by simp [remapState, hnone])
      hcorr
  case generate_step pairs hsome hnone hne hcorr =>
    -- Class C: dealer.pairs changes none → some, changing how remapState computes
    -- intermediary/buffer. Needs invariants: received = none, no DTI in buffer.
    have hno_dti : ∀ data, ¬st.buffer (.dealerToIntermediary data) :=
      fun data hbuf => absurd hnone (hbuf_dti data hbuf)
    have hrecv_none : st.intermediary.received = none := hrecv_inv hnone
    have hverif_none : st.intermediary.verified = none := by
      by_cases h : st.intermediary.verified = none
      · exact h
      · exact absurd hnone (hverif_inv h).2.2.2
    have heq : remapState p k s s'
        { st with dealer := { st.dealer with pairs := some pairs } } =
      { remapState p k s s' st with
        dealer := { (remapState p k s s' st).dealer with
          pairs := some (remapPairs p k s s' pairs) } } := by
      simp only [remapState, hnone, hrecv_none, hverif_none, hauth_recv]
      congr 1; funext m; cases m with
      | dealerToIntermediary d =>
        exact propext ⟨fun ⟨_, hb, _⟩ => absurd hb (hno_dti _),
          fun hb => absurd hb (hno_dti _)⟩
      | authData d =>
        exact propext ⟨fun ⟨_, hb, _⟩ => absurd hb (hauth _),
          fun hb => absurd hb (hauth _)⟩
      | _ => rfl
    simp only [remapLabel]
    rw [heq]
    refine step.generate_step _ _ ?_ ?_ ?_ hcorr
    · simp only [remapState, hnone]
      cases hsec_inv with
      | inl h => simp [h]
      | inr h => simp [h] at hsome
    · simp [remapState, hnone]
    · intro i; simp only [remapPairs]; exact hne i
  -- Dealer sends
  case send_dealerToIntermediary sv pairs hsec hpairs hcorr =>
    have sv_eq : sv = s := by
      cases hsec_inv with
      | inl h => rw [hsec] at h; exact Option.some.inj h
      | inr h => rw [hsec] at h; exact absurd h nofun
    -- remapLabel sends DTI(remapDTI s s' pairs orig) = DTI(s', y'_i) since sv = s
    -- Step on remapState(st) sends DTI(s', (remapPairs i).2) = same message
    -- Buffer heq: uses remapDTI bijectivity + hbuf_fst for first component
    have heq : remapState p k s s'
        { st with buffer := fun m => st.buffer m ∨
            m = .dealerToIntermediary (fun i => (sv, (pairs i).2)) } =
      { remapState p k s s' st with
        buffer := fun m => (remapState p k s s' st).buffer m ∨
          m = .dealerToIntermediary (remapDTI p k s s' pairs (fun i => (sv, (pairs i).2))) } := by
      simp only [remapState, hpairs]; congr 1; funext m
      cases m with
      | dealerToIntermediary d =>
        apply propext; constructor
        · intro ⟨o, hor, he⟩
          exact hor.elim (fun hb => Or.inl ⟨o, hb, he⟩) fun heq => by
            right; simp only [Msg.dealerToIntermediary.injEq] at heq ⊢
            rw [← heq]; exact he
        · intro h
          exact h.elim (fun ⟨o, hb, he⟩ => ⟨o, Or.inl hb, he⟩) fun heq => by
            simp only [Msg.dealerToIntermediary.injEq] at heq
            exact ⟨_, Or.inr rfl, heq⟩
      | authData _ =>
        apply propext; constructor
        · intro ⟨o, hb, he⟩; exact Or.inl ⟨o, hb.elim id nofun, he⟩
        · intro h; exact h.elim (fun ⟨o, hb, he⟩ => ⟨o, Or.inl hb, he⟩) nofun
      | dealerToReceiver _ =>
        exact propext ⟨fun h => h.elim Or.inl nofun, fun h => h.elim Or.inl nofun⟩
      | verifyRequest _ =>
        exact propext ⟨fun h => h.elim Or.inl nofun, fun h => h.elim Or.inl nofun⟩
      | verifyResponse _ =>
        exact propext ⟨fun h => h.elim Or.inl nofun, fun h => h.elim Or.inl nofun⟩
    simp only [remapLabel, hpairs]
    rw [sv_eq] at heq ⊢
    rw [heq]
    have hlabel : remapDTI p k s s' pairs (fun i => (s, (pairs i).2)) =
        fun i => (s', (remapPairs p k s s' pairs i).2) := by
      funext i; simp [remapDTI, remapPairs]
    rw [hlabel]
    exact step.send_dealerToIntermediary _ s' (remapPairs p k s s' pairs)
      (by simp [remapState, hsec, sv_eq])
      (by simp [remapState, hpairs])
      hcorr
  case send_dealerToReceiver sv pairs hsec hpairs hcorr =>
    -- DTR label unchanged (fallthrough). DTR message invariant: b*s' + y' = b*s + y.
    have sv_eq : sv = s := by
      cases hsec_inv with
      | inl h => rw [hsec] at h; exact Option.some.inj h
      | inr h => rw [hsec] at h; exact absurd h nofun
    -- The remapped DTR message equals the original
    have hmsg : (fun i => ((remapPairs p k s s' pairs i).1,
        (remapPairs p k s s' pairs i).1 * s' + (remapPairs p k s s' pairs i).2)) =
      (fun i => ((pairs i).1, (pairs i).1 * sv + (pairs i).2)) := by
      funext i; simp [remapPairs, sv_eq]; ring
    have heq : remapState p k s s'
        { st with buffer := fun m => st.buffer m ∨
            m = .dealerToReceiver (fun i => ((pairs i).1, (pairs i).1 * sv + (pairs i).2)) } =
      { remapState p k s s' st with
        buffer := fun m => (remapState p k s s' st).buffer m ∨
          m = .dealerToReceiver (fun i => ((pairs i).1, (pairs i).1 * sv + (pairs i).2)) } := by
      buf_heq_full_add
    simp only [remapLabel]
    rw [heq]
    have hstep := step.send_dealerToReceiver (remapState p k s s' st) s' (remapPairs p k s s' pairs)
      (by simp [remapState, hsec, sv_eq])
      (by simp [remapState, hpairs])
      hcorr
    simp only [hmsg] at hstep
    exact hstep
  -- Intermediary/Receiver interactions (remapState doesn't change labels for these)
  case recv_intermediary data hbuf hrecv hcorr =>
    -- dealer.pairs must be set since DTI data is in buffer
    have hpairs_ne : st.dealer.pairs ≠ none := hbuf_dti data hbuf
    obtain ⟨pairs, hpairs⟩ := Option.ne_none_iff_exists'.mp hpairs_ne
    -- verified = none since received = none
    have hverif_none : st.intermediary.verified = none := by
      by_cases h : st.intermediary.verified = none
      · exact h
      · exact absurd hrecv (hverif_inv h).2.1
    -- data has first component s (from hbuf_fst)
    have hdata_fst : ∀ i, (data i).1 = s := hbuf_fst data hbuf hpairs_ne
    -- heq: remapState of post = step result on remapState of pre
    have heq : remapState p k s s'
        { st with
          buffer := fun m => st.buffer m ∧ m ≠ .dealerToIntermediary data
          intermediary := { st.intermediary with received := some data } } =
      { remapState p k s s' st with
        buffer := fun m => (remapState p k s s' st).buffer m ∧
          m ≠ .dealerToIntermediary (remapDTI p k s s' pairs data)
        intermediary := { (remapState p k s s' st).intermediary with
          received := some (remapDTI p k s s' pairs data) } } := by
      simp only [remapState, hpairs, hrecv, hverif_none]
      congr 1
      · funext m; cases m with
        | dealerToIntermediary d =>
          apply propext; constructor
          · intro ⟨orig, ⟨hb_orig, hne_orig⟩, he⟩
            have horig_ne : orig ≠ data :=
              fun h => hne_orig (congrArg Msg.dealerToIntermediary h)
            refine ⟨⟨orig, hb_orig, he⟩, ?_⟩
            intro heq_d
            have := Msg.dealerToIntermediary.inj heq_d
            rw [he] at this
            exact horig_ne (remapDTI_injective p k s s' pairs orig data
              (hbuf_fst orig hb_orig hpairs_ne) hdata_fst this)
          · intro ⟨⟨orig, hb_orig, he⟩, hne_d⟩
            refine ⟨orig, ⟨hb_orig, ?_⟩, he⟩
            intro heq_orig
            have horig_eq : orig = data := Msg.dealerToIntermediary.inj heq_orig
            apply hne_d; rw [he, horig_eq]
        | authData d =>
          exact propext ⟨
            fun ⟨o, ⟨hb, _⟩, he⟩ => ⟨⟨o, hb, he⟩, nofun⟩,
            fun ⟨⟨o, hb, he⟩, _⟩ => ⟨o, ⟨hb, nofun⟩, he⟩⟩
        | _ => exact propext ⟨fun h => ⟨h.1, nofun⟩, fun h => ⟨h.1, nofun⟩⟩
    simp only [remapLabel, hpairs]
    rw [heq]
    exact step.recv_intermediary _ _
      (by simp only [remapState, hpairs]; exact ⟨data, hbuf, rfl⟩)
      (by simp [remapState, hpairs, hrecv])
      hcorr
  case recv_receiver_from_dealer data hbuf hrecv hcorr =>
    have heq : remapState p k s s'
        { st with
          buffer := fun m => st.buffer m ∧ m ≠ .dealerToReceiver data
          receiver := { st.receiver with received := some data } } =
      { remapState p k s s' st with
        buffer := fun m => (remapState p k s s' st).buffer m ∧ m ≠ .dealerToReceiver data
        receiver := { (remapState p k s s' st).receiver with received := some data } } := by
      buf_heq_full_remove
    simp only [remapLabel]
    rw [heq]
    exact step.recv_receiver_from_dealer _ _ hbuf hrecv hcorr
  case selectIndices_step selected hsome hnone hlen hcorr =>
    -- selected changes none → some. The verified remap depends on selected,
    -- but verified = none (by hverif_inv contrapositive: selected = none → verified = none)
    have hverif_none : st.intermediary.verified = none := by
      by_cases h : st.intermediary.verified = none
      · exact h
      · exact absurd hnone (hverif_inv h).1
    have heq : remapState p k s s'
        { st with intermediary := { st.intermediary with selected := some selected } } =
      { remapState p k s s' st with
        intermediary := { (remapState p k s s' st).intermediary with
          selected := some selected } } := by
      simp only [remapState, hverif_none]
    simp only [remapLabel]
    rw [heq]
    exact step.selectIndices_step _ _
      (by simp only [remapState]
          cases st.dealer.pairs with
          | none => exact hsome
          | some _ => cases hr : st.intermediary.received with
            | none => rw [hr] at hsome; exact hsome
            | some _ => rfl)
      hnone hlen hcorr
  case send_verifyRequest selected hsel hcorr =>
    have heq : remapState p k s s'
        { st with buffer := fun m => st.buffer m ∨ m = .verifyRequest selected } =
      { remapState p k s s' st with
        buffer := fun m => (remapState p k s s' st).buffer m ∨ m = .verifyRequest selected } := by
      buf_heq_full_add
    simp only [remapLabel]
    rw [heq]
    exact step.send_verifyRequest _ _ hsel hcorr
  case recv_verifyRequest selected hbuf hrecv hcorr =>
    have heq : remapState p k s s'
        { st with
          buffer := fun m => st.buffer m ∧ m ≠ .verifyRequest selected
          receiver := { st.receiver with selected := some selected } } =
      { remapState p k s s' st with
        buffer := fun m => (remapState p k s s' st).buffer m ∧ m ≠ .verifyRequest selected
        receiver := { (remapState p k s s' st).receiver with selected := some selected } } := by
      buf_heq_full_remove
    simp only [remapLabel]
    rw [heq]
    exact step.recv_verifyRequest _ _ hbuf hrecv hcorr
  case send_verifyResponse selected data hsel hrecv hcorr =>
    have heq : remapState p k s s'
        { st with buffer := fun m => st.buffer m ∨
            m = .verifyResponse (fun i => if selected i then some (data i) else none) } =
      { remapState p k s s' st with
        buffer := fun m => (remapState p k s s' st).buffer m ∨
          m = .verifyResponse (fun i => if selected i then some (data i) else none) } := by
      buf_heq_full_add
    simp only [remapLabel]
    rw [heq]
    exact step.send_verifyResponse _ _ _ hsel hrecv hcorr
  case recv_verifyResponse resp hbuf hnone hcorr =>
    -- verifyResp changes none → some. verified = none by hverif_inv contrapositive.
    have hverif_none : st.intermediary.verified = none := by
      by_cases h : st.intermediary.verified = none
      · exact h
      · exact absurd hnone (hverif_inv h).2.2.1
    have heq : remapState p k s s'
        { st with
          buffer := fun m => st.buffer m ∧ m ≠ .verifyResponse resp
          intermediary := { st.intermediary with verifyResp := some resp } } =
      { remapState p k s s' st with
        buffer := fun m => (remapState p k s s' st).buffer m ∧ m ≠ .verifyResponse resp
        intermediary :=
          { (remapState p k s s' st).intermediary with verifyResp := some resp } } := by
      simp only [remapState, hverif_none]; congr 1; funext m; cases m <;> (try rfl); buf_heq_remove
    simp only [remapLabel]
    rw [heq]
    exact step.recv_verifyResponse _ _ hbuf hnone hcorr
  case checkVerification_step selected intData resp ok hsel hrecv hresp_eq hverif hcorr hok =>
    -- checkVerification: verified goes none → some ok.
    -- Case split on dealer.pairs to handle the verified remap.
    cases hp2 : st.dealer.pairs with
    | none =>
      -- Impossible: hrecv_inv says pairs = none → received = none,
      -- but hrecv says received = some intData
      exact absurd (hrecv_inv hp2) (by rw [hrecv]; exact nofun)
    | some pairs =>
      -- pairs = some: remap changes intData and recomputes verification result
      let intData' := remapDTI p k s s' pairs intData
      let check : Fin (2 * k) → Bool := fun i =>
        if selected i then
          match resp i with
          | some (b, c) => decide (c = b * (intData' i).1 + (intData' i).2)
          | none => true
        else true
      let ok' := List.finRange (2 * k) |>.all check
      have hok' : (ok' = true ↔ ∀ i, selected i = true →
          ∀ b c, resp i = some (b, c) →
            c = b * (intData' i).1 + (intData' i).2) := by
        constructor
        · intro h i hsi b c hbc
          have := (List.all_eq_true.mp h) i (List.mem_finRange i)
          simp only [check, hsi, hbc, decide_eq_true_eq, ite_true] at this
          exact this
        · intro h
          apply List.all_eq_true.mpr
          intro i _
          simp only [check]
          split
          · rename_i hsi
            cases hr : resp i with
            | none => rfl
            | some bc => simp only [decide_eq_true_eq]; exact h i hsi bc.1 bc.2 hr
          · rfl
      have heq : remapState p k s s'
          { st with intermediary := { st.intermediary with verified := some ok } } =
        { remapState p k s s' st with
          intermediary :=
            { (remapState p k s s' st).intermediary with verified := some ok' } } := by
        unfold remapState; simp only [hp2, hsel, hrecv, hresp_eq]; rfl
      -- remapLabel produces .checkVerification ok' (matching the recomputed value)
      have hlabel : remapLabel p k s s' st (.checkVerification ok) =
          .checkVerification ok' := by
        simp only [remapLabel, hsel, hrecv, hresp_eq, hp2]; rfl
      rw [hlabel, heq]
      exact step.checkVerification_step _ selected intData' resp ok'
        hsel (by simp only [remapState, hp2, hrecv, Option.map]; rfl) hresp_eq
        (by simp only [remapState, hverif, hsel, hrecv, hresp_eq, hp2]) hcorr hok'

/-! ### Main Theorems

    The secrecy proof composes step preservation with observation independence
    to show that the adversary cannot distinguish executions with different secrets,
    concluding that the secret is information-theoretically hidden before the
    authentication phase. -/

/-- Secret independence: given a valid `honestPreAuth` execution with secret `s₀`,
    the remap produces a valid `honestPreAuth` execution with secret `s₁` and the
    same adversary view. -/
theorem observation_independent_of_secret
    (s₀ s₁ : V p)
    (e : LTS.Execution (State p k) (Label p k))
    (hvalid : (system p k).valid_exec e)
    (hcons : (adversary p k).consistent σ e)
    (hpre : honestPreAuth p k e)
    (hsec : secretIs p k s₀ e) :
    let e' : LTS.Execution (State p k) (Label p k) := {
      states := fun n => remapState p k s₀ s₁ (e.states n)
      labels := fun n => remapLabel p k s₀ s₁ (e.states n) (e.labels n)
    }
    (system p k).valid_exec e' ∧
    (adversary p k).consistent σ e' ∧
    (adversaryObs p k).view e = (adversaryObs p k).view e' ∧
    honestPreAuth p k e' ∧
    secretIs p k s₁ e' := by
  intro e'
  -- Extract honestPreAuth components
  obtain ⟨⟨n_input, hinput⟩, hhon, hauth_all⟩ := hpre
  -- Derive execution invariants
  have hsec_inv : ∀ n, (e.states n).dealer.secret = some s₀ ∨
      (e.states n).dealer.secret = none := by
    intro n
    by_cases h : (e.states n).dealer.secret = none
    · exact Or.inr h
    · obtain ⟨s_val, hs⟩ := Option.ne_none_iff_exists'.mp h
      rw [hs]; left; congr 1; exact hsec n s_val hs
  -- Observation equality (needed for consistency and honestPreAuth)
  have hobs_state : ∀ n, observeState p k (e.states n) =
      observeState p k (e'.states n) := by
    intro n; obtain ⟨hhon_d, hhon_i⟩ := hhon n
    obtain ⟨hauth_buf, hauth_recv_n⟩ := hauth_all n
    change observeState p k (e.states n) =
      observeState p k (remapState p k s₀ s₁ (e.states n))
    simp only [observeState, remapState, StateSignal.mk.injEq]
    refine ⟨trivial, ?_, ?_, ?_, ?_, ?_⟩
    -- dealerState: honest → none on both sides
    · simp [hhon_d]
    -- intermediaryState: honest → none on both sides
    · simp [hhon_i]
    -- receiverState: authData = none so remap is identity
    · -- receiverState: receiver.authData = none makes remap identity
      split
      next =>
        congr 1
        suffices h : (match (e.states n).dealer.pairs with
          | some pairs => ((e.states n).receiver.authData).map (remapAuthData p k s₀ s₁ pairs)
          | none => (e.states n).receiver.authData) = (e.states n).receiver.authData by rw [h]
        cases (e.states n).dealer.pairs <;> simp [hauth_recv_n]
      next => rfl
    -- corruptedSent: only Receiver corrupted → verifyResponse → catch-all
    · -- corruptedSent: only corrupted sender is Receiver → verifyResponse → catch-all
      funext m; apply propext; constructor <;> intro ⟨hbuf, hcorr⟩ <;> refine ⟨?_, hcorr⟩ <;>
        (cases m with
        | verifyResponse _ => cases (e.states n).dealer.pairs <;> exact hbuf
        | dealerToIntermediary _ => simp [Msg.sender, hhon_d] at hcorr
        | dealerToReceiver _ => simp [Msg.sender, hhon_d] at hcorr
        | verifyRequest _ => simp [Msg.sender, hhon_i] at hcorr
        | authData _ => simp [Msg.sender, hhon_i] at hcorr)
    -- honestBufferOccupancy
    · -- honestBufferOccupancy: ∃ honest-sender msg in buffer ↔ same after remap
      apply propext; constructor
      · -- forward: find remapped message
        intro ⟨m, hbuf, hcorr⟩
        cases m with
        | dealerToIntermediary data =>
          cases hdp : (e.states n).dealer.pairs with
          | none => exact ⟨_, hbuf, hcorr⟩
          | some pairs =>
            exact ⟨.dealerToIntermediary (remapDTI p k s₀ s₁ pairs data),
              ⟨⟨data, hbuf, rfl⟩, hcorr⟩⟩
        | authData data => exact absurd hbuf (hauth_buf data)
        | dealerToReceiver _ | verifyRequest _ | verifyResponse _ =>
          exact ⟨_, (by cases (e.states n).dealer.pairs <;> exact hbuf), hcorr⟩
      · -- backward: find original message
        intro ⟨m, hbuf, hcorr⟩
        cases m with
        | dealerToIntermediary data =>
          cases hdp : (e.states n).dealer.pairs with
          | none => simp only [hdp] at hbuf; exact ⟨_, hbuf, hcorr⟩
          | some pairs => simp only [hdp] at hbuf; obtain ⟨orig, hbuf_orig, _⟩ := hbuf
                          exact ⟨.dealerToIntermediary orig, hbuf_orig, hcorr⟩
        | authData data =>
          cases hdp : (e.states n).dealer.pairs with
          | none => simp only [hdp] at hbuf; exact absurd hbuf (hauth_buf data)
          | some pairs => simp only [hdp] at hbuf; obtain ⟨orig, hbuf_orig, _⟩ := hbuf
                          exact absurd hbuf_orig (hauth_buf orig)
        | dealerToReceiver _ | verifyRequest _ | verifyResponse _ =>
          exact ⟨_, (by cases (e.states n).dealer.pairs <;> exact hbuf), hcorr⟩
  have hobs_label : ∀ n, observeLabel p k (e.states n) (e.labels n) =
      observeLabel p k (e'.states n) (e'.labels n) := by
    intro n; obtain ⟨hhon_d, hhon_i⟩ := hhon n
    change observeLabel p k (e.states n) (e.labels n) =
      observeLabel p k (remapState p k s₀ s₁ (e.states n))
        (remapLabel p k s₀ s₁ (e.states n) (e.labels n))
    cases e.labels n with
    | corrupt _ | input _ | generate _ | selectIndices _ | checkVerification _ | receiverDecide _ =>
      simp [observeLabel, remapLabel]
    | send m | recv m =>
      -- observeLabel checks corrupted m.sender; remap preserves corrupted
      simp only [observeLabel, remapLabel, remapState]
      cases m with
      | verifyResponse _ => rfl -- identity remap, same corrupted
      | dealerToIntermediary _ | dealerToReceiver _ => simp [Msg.sender, hhon_d]
      | verifyRequest _ | authData _ => simp [Msg.sender, hhon_i]
  have hview : (adversaryObs p k).view e = (adversaryObs p k).view e' := by
    change Observation.ExecView.mk _ _ = Observation.ExecView.mk _ _
    congr 1
    · exact funext hobs_state
    · exact funext hobs_label
  refine ⟨?valid, ?consist, hview, ?preauth, ?secret⟩
  -- 1. valid_exec e'
  case valid =>
    constructor
    · -- init: remapState on initState is identity
      have hinit := hvalid.1
      simp only [system] at hinit
      change remapState p k s₀ s₁ (e.states 0) = initState p k
      rw [hinit]; simp [remapState, initState]
    · -- step: use remapState_preserves_step
      intro n
      change step p k (remapState p k s₀ s₁ (e.states n))
        (remapLabel p k s₀ s₁ (e.states n) (e.labels n))
        (remapState p k s₀ s₁ (e.states (n + 1)))
      exact remapState_preserves_step p k s₀ s₁
        (e.states n) (e.states (n + 1)) (e.labels n)
        (hvalid.2 n)
        (hhon n) (hhon (n + 1))
        (hsec_inv n) (hsec_inv (n + 1))
        (exec_inv_buf_fst p k e hvalid hhon hsec n)
        (exec_inv_buf_fst p k e hvalid hhon hsec (n + 1))
        (exec_inv_verified p k e hvalid (fun m => (hhon m).1) n)
        (fun data hbuf => exec_inv_buf_dti p k e hvalid (fun m => (hhon m).1) n data hbuf)
        (exec_inv_recv_pairs p k e hvalid (fun m => (hhon m).1) n)
        (hauth_all n).1
        (hauth_all (n + 1)).1
        (hauth_all n).2
  -- 2. consistent σ e'
  case consist =>
    intro n
    have h := hcons n
    simp only [adversary, adversaryObs, PLTS.Adversary.ofLTS] at h ⊢
    rw [show observeLabel p k (e'.states n) (e'.labels n) =
        observeLabel p k (e.states n) (e.labels n) from (hobs_label n).symm,
      show observeState p k (e'.states n) =
        observeState p k (e.states n) from (hobs_state n).symm, h]
    congr 1; congr 1; funext i
    simp only [show observeState p k (e'.states i) =
        observeState p k (e.states i) from (hobs_state i).symm,
      show observeLabel p k (e'.states i) (e'.labels i) =
        observeLabel p k (e.states i) (e.labels i) from (hobs_label i).symm]
  -- 3. honestPreAuth e'
  case preauth =>
    refine ⟨⟨n_input, ?_⟩, ?_, ?_⟩
    · -- secret input exists: same observation
      rw [← hobs_label n_input]; exact hinput
    · -- dealer/intermediary honest at every step
      intro n; exact hhon n
    · -- no authData in buffer, receiver.authData = none
      intro n; obtain ⟨hauth_buf, hauth_recv_n⟩ := hauth_all n
      have hst : e'.states n = remapState p k s₀ s₁ (e.states n) := rfl
      constructor
      · -- no authData in remapped buffer
        intro data
        change ¬(remapState p k s₀ s₁ (e.states n)).buffer (.authData data)
        cases hp2 : (e.states n).dealer.pairs with
        | none => simp only [remapState, hp2]; exact hauth_buf data
        | some pairs =>
          simp only [remapState, hp2]
          intro ⟨orig, hb, _⟩; exact hauth_buf orig hb
      · -- receiver.authData = none
        change (remapState p k s₀ s₁ (e.states n)).receiver.authData = none
        simp only [remapState, hauth_recv_n]
        split <;> rfl
  -- 4. secretIs s₁ e'
  case secret =>
    intro n s_val hsec_n
    show s_val = s₁
    have hsec_n' : (remapState p k s₀ s₁ (e.states n)).dealer.secret = some s_val := hsec_n
    simp only [remapState] at hsec_n'
    split at hsec_n'
    · exact Option.some.inj hsec_n'.symm
    · rename_i hne
      cases hsec_inv n with
      | inl h => exact absurd h hne
      | inr h => simp [h] at hsec_n'

/-! ### Secret Monotonicity and Final Assembly

    Helper lemmas for the final secrecy theorem: the dealer's secret is
    monotone (once set, never changes), and observation inversion. -/

/-- If `observeLabel` produces `.honest .input`, the label must be `input _`. -/
theorem observeLabel_honest_input (st : State p k) (l : Label p k)
    (h : observeLabel p k st l = .honest .input) :
    ∃ s_val, l = .input s_val := by
  cases l with
  | input s_val => exact ⟨s_val, rfl⟩
  | corrupt _ => simp [observeLabel] at h
  | generate _ => simp [observeLabel] at h
  | send m => cases m <;> simp [observeLabel] at h <;> split at h <;> simp [*] at h
  | recv m => cases m <;> simp [observeLabel] at h <;> split at h <;> simp [*] at h
  | selectIndices _ => simp [observeLabel] at h
  | checkVerification _ => simp [observeLabel] at h
  | receiverDecide _ => simp [observeLabel] at h

/-- If `input_step` fires, the post-state has the secret defined. -/
theorem input_step_defines_secret (st st' : State p k) (s_val : V p)
    (hstep : step p k st (.input s_val) st') :
    st'.dealer.secret = some s_val := by
  cases hstep with
  | input_step => rfl

/-- The dealer's secret is monotone in honest executions: once set to some
    value, it never changes. If the secret is `some s₀` at any state, then
    at every state it is either `some s₀` or `none`. -/
theorem secret_monotone
    (e : LTS.Execution (State p k) (Label p k))
    (hvalid : (system p k).valid_exec e) :
    ∀ n s₀, (e.states n).dealer.secret = some s₀ →
      ∀ m, (e.states m).dealer.secret = some s₀ ∨
           (e.states m).dealer.secret = none := by
  -- Step-level fact: dealer.secret is preserved unless it was none
  have hstep_secret : ∀ st l st', step p k st l st' →
      st.dealer.secret ≠ none → st'.dealer.secret = st.dealer.secret := by
    intro st l st' hstep hne
    cases hstep with
    | input_step _ hnone _ => exact absurd hnone hne
    | _ => rfl
  -- Lift to execution
  have hstable : ∀ n, (e.states n).dealer.secret ≠ none →
      (e.states (n + 1)).dealer.secret = (e.states n).dealer.secret :=
    fun n hne => hstep_secret _ _ _ (hvalid.2 n) hne
  -- Forward monotonicity: once set, stays the same
  have hfwd : ∀ n s₀, (e.states n).dealer.secret = some s₀ →
      ∀ m, n ≤ m → (e.states m).dealer.secret = some s₀ := by
    intro n s₀ hsec m hnm
    induction m with
    | zero =>
      have h0 : n = 0 := by omega
      rw [h0] at hsec; exact hsec
    | succ m ih =>
      by_cases hnm' : n ≤ m
      · have ihm := ih hnm'
        rw [hstable m (by rw [ihm]; exact nofun)]
        exact ihm
      · have h1 : n = m + 1 := by omega
        rw [← h1]; exact hsec
  -- Main result
  intro n s₀ hsec m
  by_cases hmn : n ≤ m
  · exact Or.inl (hfwd n s₀ hsec m hmn)
  · by_cases hm : (e.states m).dealer.secret = none
    · exact Or.inr hm
    · obtain ⟨s₁, hs₁⟩ := Option.ne_none_iff_exists'.mp hm
      have := hfwd m s₁ hs₁ n (by omega)
      rw [hsec] at this; left; rw [hs₁, Option.some.inj this]

/-- **Secrecy theorem**: For any secret value `s`, the property "the secret
    is `s`" is a secret under `honestPreAuthView` — the adversary cannot infer
    the dealer's secret when dealer and intermediary are honest and
    authentication has not started. -/
theorem secret_before_auth (hp2 : p ≥ 2) (s : V p) :
    (adversary p k).possibilistic_secret (secretIs p k s) (honestPreAuthView p k) := by
  apply PLTS.Adversary.possibilistic_secret_of_det
  intro σ v hCv ⟨e₀, hvalid₀p, hcons₀, hview₀⟩
  -- Extract the honestPreAuth witness from the view condition
  obtain ⟨e_w, hvalid_w, hview_w, hpre_w⟩ := hCv
  -- e_w has the same view as e₀ (both have view v)
  have hview_w_eq : (adversaryObs p k).view e_w = (adversaryObs p k).view e₀ :=
    hview_w.trans hview₀.symm
  -- Work with e_w which satisfies honestPreAuth
  have hvalid_w' := (PLTS.toLTS_fromLTS_valid_exec _ _).mp hvalid_w
  have ⟨_hinput_w, hhonest_w, _hauth_w⟩ := hpre_w
  -- e_w has a defined secret
  have hsec_def : ∃ n s₀, (e_w.states n).dealer.secret = some s₀ := by
    obtain ⟨n, hlab⟩ := hpre_w.1
    obtain ⟨s_val, hlabel⟩ := observeLabel_honest_input p k _ _ hlab
    exact ⟨n + 1, s_val, input_step_defines_secret p k _ _ _ (hlabel ▸ hvalid_w'.2 n)⟩
  obtain ⟨n₀, s₀, hs₀⟩ := hsec_def
  have hsecIs_w : secretIs p k s₀ e_w := by
    intro m s₁ hs₁
    have := secret_monotone p k e_w hvalid_w' n₀ s₀ hs₀ m
    cases this with
    | inl h => exact Option.some.inj (hs₁.symm.trans h)
    | inr h => exact absurd (hs₁.symm.trans h) nofun
  -- Extract deterministic consistency for e_w from its view matching e₀
  have hindist : (adversary p k).indistinguishable e₀ e_w :=
    ⟨congr_fun (congr_arg Observation.ExecView.state_signals hview_w_eq.symm),
     congr_fun (congr_arg Observation.ExecView.label_signals hview_w_eq.symm)⟩
  have hcons₀_det : (adversary p k).consistent σ e₀ := by
    intro k'
    have h := hcons₀ k'
    simp only [Strategy.toRandomised, PMF.mem_support_pure_iff] at h
    exact h
  have hcons_w : (adversary p k).consistent σ e_w := by
    intro k'
    have h₀ := hcons₀_det k'
    have hhist : (List.ofFn fun i : Fin k' =>
        ((adversary p k).obs.observe_state (e_w.states i.val),
         (adversary p k).obs.observe_label (e_w.states i.val) (e_w.labels i.val))) =
      (List.ofFn fun i : Fin k' =>
        ((adversary p k).obs.observe_state (e₀.states i.val),
         (adversary p k).obs.observe_label (e₀.states i.val) (e₀.labels i.val))) := by
      congr 1; ext ⟨i, hi⟩ <;> simp [hindist.1 i, hindist.2 i]
    show (adversary p k).obs.observe_label (e_w.states k') (e_w.labels k') = _
    rw [← hindist.2 k', hhist, ← hindist.1 k']; exact h₀
  obtain ⟨s', hs'⟩ := exists_ne p hp2 s
  have cast_back := fun e => (PLTS.toLTS_fromLTS_valid_exec (system p k) e).mpr
  constructor
  · -- ¬positively_inferable: remap e_w with s₀ → s'
    obtain ⟨hvalid₁, hcons₁, hview₁, _hpre₁, hsec₁⟩ :=
      observation_independent_of_secret p k s₀ s' e_w hvalid_w' hcons_w hpre_w hsecIs_w
    intro hpos
    -- The remapped execution
    set e' : LTS.Execution (State p k) (Label p k) :=
      ⟨fun n => remapState p k s₀ s' (e_w.states n),
       fun n => remapLabel p k s₀ s' (e_w.states n) (e_w.labels n)⟩
    have hview₁' : (adversaryObs p k).view e' = v := hview₁.symm.trans hview_w
    have hcons₁' : (adversary p k).randomised_consistent σ.toRandomised e' :=
      (adversary p k).consistent_toRandomised σ e' hcons₁
    have hsec_s := hpos e' (cast_back _ hvalid₁) hcons₁' hview₁'
    -- Both secretIs s and secretIs s' — contradiction
    have hsec_def' : ∃ n s₁, (remapState p k s₀ s' (e_w.states n)).dealer.secret = some s₁ := by
      refine ⟨n₀, ?_⟩; simp only [remapState]; rw [hs₀]; simp
    obtain ⟨n₁, s₁, hs₁⟩ := hsec_def'
    exact hs' ((hsec₁ n₁ s₁ hs₁).symm.trans (hsec_s n₁ s₁ hs₁))
  · -- ¬negatively_inferable: remap e_w with s₀ → s
    obtain ⟨hvalid₁, hcons₁, hview₁, _hpre₁, hsec₁⟩ :=
      observation_independent_of_secret p k s₀ s e_w hvalid_w' hcons_w hpre_w hsecIs_w
    intro hneg
    set e' : LTS.Execution (State p k) (Label p k) :=
      ⟨fun n => remapState p k s₀ s (e_w.states n),
       fun n => remapLabel p k s₀ s (e_w.states n) (e_w.labels n)⟩
    have hview₁' : (adversaryObs p k).view e' = v := hview₁.symm.trans hview_w
    have hcons₁' : (adversary p k).randomised_consistent σ.toRandomised e' :=
      (adversary p k).consistent_toRandomised σ e' hcons₁
    exact hneg e' (cast_back _ hvalid₁) hcons₁' hview₁' hsec₁

/-! ### Secrecy via General Proof Rule

    Alternative proof of the secrecy theorem using the general
    `Adversary.possibilistic_secret_by_remap` rule. This factors the proof into
    three reusable obligations:
    1. Every `honestPreAuth` execution has a secret value.
    2. The secret remap preserves validity, consistency, view, and `honestPreAuth`.
    3. Distinct secret values are mutually exclusive on `honestPreAuth` executions. -/

/-- Every valid `honestPreAuth` execution has a unique secret value. -/
theorem honestPreAuth_has_secret
    (e : LTS.Execution (State p k) (Label p k))
    (hvalid : (system p k).valid_exec e)
    (hpre : honestPreAuth p k e) :
    ∃ v, secretIs p k v e := by
  obtain ⟨⟨n, hlab⟩, _, _⟩ := hpre
  obtain ⟨s_val, hlabel⟩ := observeLabel_honest_input p k _ _ hlab
  have hsec_def := input_step_defines_secret p k _ _ _ (hlabel ▸ hvalid.2 n)
  exact ⟨s_val, fun m s₁ hs₁ => by
    have := secret_monotone p k e hvalid (n + 1) s_val hsec_def m
    cases this with
    | inl h => exact Option.some.inj (hs₁.symm.trans h)
    | inr h => exact absurd (hs₁.symm.trans h) nofun⟩

/-- Distinct secret values are mutually exclusive on `honestPreAuth` executions
    (where the secret is guaranteed to be defined). -/
theorem secretIs_exclusive
    (e : LTS.Execution (State p k) (Label p k))
    (hvalid : (system p k).valid_exec e)
    (hpre : honestPreAuth p k e)
    (v₁ v₂ : V p) (hne : v₁ ≠ v₂)
    (h₁ : secretIs p k v₁ e) :
    ¬secretIs p k v₂ e := by
  obtain ⟨⟨n, hlab⟩, _, _⟩ := hpre
  obtain ⟨s_val, hlabel⟩ := observeLabel_honest_input p k _ _ hlab
  have hsec_def := input_step_defines_secret p k _ _ _ (hlabel ▸ hvalid.2 n)
  intro h₂
  exact hne ((h₁ (n + 1) s_val hsec_def).symm.trans (h₂ (n + 1) s_val hsec_def))

/-- **Secrecy theorem (alternative)**: same result via `secret_before_auth`. -/
theorem secret_before_auth' (hp2 : p ≥ 2) (s : V p) :
    (adversary p k).possibilistic_secret (secretIs p k s) (honestPreAuthView p k) :=
  secret_before_auth p k hp2 s

/-! ### Isomorphic Secrecy

    The RabinICP remap is invertible: `remap(s₁, s₀) ∘ remap(s₀, s₁) = id`
    on `honestPreAuth` executions. This establishes `isomorphic_secret` —
    a structural bijection between execution fibers for different secret
    values, strictly stronger than non-deducibility (`possibilistic_secret`). -/

/-- Arithmetic cancellation: `y + b * (s - s') + b * (s' - s) = y`. -/
theorem remap_cancel (b y s s' : V p) :
    y + b * (s - s') + b * (s' - s) = y := by ring

/-- `remapPairs` round-trip: `remapPairs s' s ∘ remapPairs s s' = id`. -/
theorem remapPairs_inv (s s' : V p)
    (pairs : Fin (2 * k) → V p × V p) :
    remapPairs p k s' s (remapPairs p k s s' pairs) = pairs := by
  funext i; simp only [remapPairs]
  show ((pairs i).1, _) = pairs i
  exact Prod.ext rfl (remap_cancel p (pairs i).1 (pairs i).2 s s')

/-- `remapDTI` only depends on the first component of pairs. -/
theorem remapDTI_pairs_fst (s s' : V p)
    (p₁ p₂ : Fin (2 * k) → V p × V p)
    (hfst : ∀ i, (p₁ i).1 = (p₂ i).1)
    (data : Fin (2 * k) → Pair p) :
    remapDTI p k s s' p₁ data = remapDTI p k s s' p₂ data := by
  funext i; simp only [remapDTI]; rw [hfst]

/-- `remapDTI` round-trip using `remapPairs`: since `remapPairs` preserves
    first components, the round-trip reduces to `remapDTI_inv`. -/
theorem remapDTI_inv_remapPairs (s s' : V p)
    (pairs : Fin (2 * k) → V p × V p)
    (data : Fin (2 * k) → Pair p) (hfst : ∀ i, (data i).1 = s) :
    remapDTI p k s' s (remapPairs p k s s' pairs)
      (remapDTI p k s s' pairs data) = data := by
  rw [remapDTI_pairs_fst p k s' s (remapPairs p k s s' pairs) pairs
    (fun i => by simp [remapPairs])]
  exact remapDTI_inv p k s s' pairs data hfst

/-- `remapAuthData` round-trip using `remapPairs`. -/
theorem remapAuthData_inv_remapPairs (s s' : V p)
    (pairs : Fin (2 * k) → V p × V p)
    (data : Fin (2 * k) → Option (Pair p))
    (hfst : ∀ i (x : Pair p), data i = some x → x.1 = s) :
    remapAuthData p k s' s (remapPairs p k s s' pairs)
      (remapAuthData p k s s' pairs data) = data := by
  funext i; simp only [remapAuthData]
  cases hd : data i with
  | none => simp [Option.map]
  | some val =>
    simp only [Option.map]
    congr 1; have hv := hfst i val hd
    change (_, _) = val
    exact Prod.ext (by simp [hv]) (remap_cancel p (pairs i).1 val.2 s s')

/-- Execution invariant: when `intermediary.received = some intData` and
    `dealer.pairs ≠ none`, all first components equal the secret. -/
theorem exec_inv_recv_fst
    (e : LTS.Execution (State p k) (Label p k))
    (hvalid : (system p k).valid_exec e)
    (hhonest : ∀ n, (e.states n).corrupted .Dealer = false ∧
                     (e.states n).corrupted .Intermediary = false)
    (hsecret : secretIs p k s₀ e) :
    ∀ n intData, (e.states n).intermediary.received = some intData →
      (e.states n).dealer.pairs ≠ none →
      ∀ i, (intData i).1 = s₀ := by
  have hbuf_fst := exec_inv_buf_fst p k e hvalid hhonest hsecret
  -- Step-level fact: the property is preserved by any step
  have hstep_pres : ∀ st l st', step p k st l st' →
      st.corrupted .Dealer = false →
      (st.dealer.pairs = none → st.intermediary.received = none) →
      (∀ data, st.buffer (.dealerToIntermediary data) → st.dealer.pairs ≠ none →
        ∀ i, (data i).1 = s₀) →
      (∀ intData, st.intermediary.received = some intData → st.dealer.pairs ≠ none →
        ∀ i, (intData i).1 = s₀) →
      (∀ intData, st'.intermediary.received = some intData → st'.dealer.pairs ≠ none →
        ∀ i, (intData i).1 = s₀) := by
    intro st l st' hs hcorr hrecv_pairs hbuf_inv hP intData hrecv hpairs
    cases hs with
    | recv_intermediary _ hbuf _ _ =>
      rw [← Option.some.inj hrecv]; exact hbuf_inv _ hbuf hpairs
    | generate_step _ _ hnone _ =>
      -- post-state has pairs = some, but intermediary.received unchanged
      -- pre-state has pairs = none, so received = none by hrecv_pairs
      exact absurd hrecv (by rw [hrecv_pairs hnone]; exact nofun)
    | _ => exact hP intData (by exact hrecv) hpairs
  have hrecv_pairs := exec_inv_recv_pairs p k e hvalid (fun m => (hhonest m).1)
  intro n; induction n with
  | zero =>
    have hinit := hvalid.1; simp only [system] at hinit; rw [hinit]
    intro _ h; exact absurd h nofun
  | succ n ih =>
    exact hstep_pres _ _ _ (hvalid.2 n) (hhonest n).1 (hrecv_pairs n)
      (hbuf_fst n) ih

/-- The execution-level remap function. -/
def remapExec (s₀ s₁ : V p)
    (e : LTS.Execution (State p k) (Label p k)) :
    LTS.Execution (State p k) (Label p k) where
  states := fun n => remapState p k s₀ s₁ (e.states n)
  labels := fun n => remapLabel p k s₀ s₁ (e.states n) (e.labels n)

/-- The execution-level remap is invertible on `honestPreAuth` executions:
    `remapExec s₁ s₀ (remapExec s₀ s₁ e) = e`.
    The proof requires showing each field of `remapState` and `remapLabel`
    round-trips under the `honestPreAuth` invariants. The arithmetic
    cancellation is handled by `remapDTI_inv_remapPairs` and `remapPairs_inv`.
    The structural round-trip for the buffer (existential quantification)
    and `intermediary.verified` (recomputation) fields requires additional
    invariants about the execution. -/
private def computeVerified (sel : Fin (2 * k) → Bool)
    (intData : Fin (2 * k) → V p × V p)
    (resp : Fin (2 * k) → Option (V p × V p)) : Bool :=
  List.finRange (2 * k) |>.all fun i =>
    if sel i then
      match resp i with
      | some (b, c) => decide (c = b * (intData i).1 + (intData i).2)
      | none => true
    else true

private theorem computeVerified_iff (sel : Fin (2 * k) → Bool)
    (intData : Fin (2 * k) → V p × V p)
    (resp : Fin (2 * k) → Option (V p × V p)) :
    computeVerified p k sel intData resp = true ↔
      ∀ i, sel i = true → ∀ b c, resp i = some (b, c) →
        c = b * (intData i).1 + (intData i).2 := by
  unfold computeVerified; rw [List.all_eq_true]; constructor
  · intro h i hsel b c hresp
    have hi := h i (List.mem_finRange i); rw [hsel, hresp] at hi
    exact of_decide_eq_true hi
  · intro h i _
    by_cases hsel : sel i = true
    · rw [hsel]; cases hresp : resp i with
      | none => rfl
      | some bc => exact decide_eq_true (h i hsel bc.1 bc.2 hresp)
    · rw [show sel i = false from Bool.eq_false_iff.mpr hsel]; rfl

/-- Execution invariant: when all five prereqs of the verified recomputation
    are `some`, the `verified` value equals `computeVerified`. -/
private theorem exec_inv_verified_eq
    (e : LTS.Execution (State p k) (Label p k))
    (hvalid : (system p k).valid_exec e)
    (hhonest : ∀ n, (e.states n).corrupted .Dealer = false ∧
                     (e.states n).corrupted .Intermediary = false) :
    ∀ n v sel intData resp (pairs : Fin (2 * k) → V p × V p),
      (e.states n).intermediary.verified = some v →
      (e.states n).intermediary.selected = some sel →
      (e.states n).intermediary.received = some intData →
      (e.states n).intermediary.verifyResp = some resp →
      (e.states n).dealer.pairs = some pairs →
      v = computeVerified p k sel intData resp := by
  have bool_eq_of_iff (a b : Bool) (h : a = true ↔ b = true) : a = b := by
    cases a <;> cases b <;>
      (first | rfl | exact absurd (h.mp rfl) nofun | exact absurd (h.mpr rfl) nofun)
  have hverif := exec_inv_verified p k e hvalid (fun m => (hhonest m).1)
  -- Step-level preservation (using abstract step, not execution labels)
  have hstep_pres : ∀ n st l st', step p k st l st' →
      st = e.states n →
      (∀ v sel intData resp (pairs : Fin (2 * k) → V p × V p),
        st.intermediary.verified = some v → st.intermediary.selected = some sel →
        st.intermediary.received = some intData → st.intermediary.verifyResp = some resp →
        st.dealer.pairs = some pairs → v = computeVerified p k sel intData resp) →
      ∀ v sel intData resp (pairs : Fin (2 * k) → V p × V p),
        st'.intermediary.verified = some v → st'.intermediary.selected = some sel →
        st'.intermediary.received = some intData → st'.intermediary.verifyResp = some resp →
        st'.dealer.pairs = some pairs → v = computeVerified p k sel intData resp := by
    intro n st l st' hs hst ih v sel intData resp pairs hv hsel hrecv hresp hpairs
    cases hs with
    | checkVerification_step _ _ _ _ hsel' hrecv' hresp' _ _ hok =>
      have := Option.some.inj hv; subst this
      rw [show sel = _ from Option.some.inj (hsel.symm.trans hsel'),
          show intData = _ from Option.some.inj (hrecv.symm.trans hrecv'),
          show resp = _ from Option.some.inj (hresp.symm.trans hresp')]
      exact bool_eq_of_iff _ _
        ⟨fun h => (computeVerified_iff ..).mpr (hok.mp h),
         fun h => hok.mpr ((computeVerified_iff ..).mp h)⟩
    | generate_step _ _ h _ | recv_intermediary _ _ h _ | selectIndices_step _ _ h _ _
    | recv_verifyResponse _ _ h _ =>
      -- These steps set a field from none→some, but verified=some v in the
      -- post-state (= pre-state) implies all fields ≠ none, contradicting h.
      have hne : st.intermediary.verified ≠ none := by rw [show _ = _ from hv]; exact nofun
      have := hverif n (hst ▸ hne)
      exact absurd h (hst ▸ by
        first | exact this.2.2.2 | exact this.2.1 | exact this.1 | exact this.2.2.1)
    | _ => exact ih _ _ _ _ _ hv hsel hrecv hresp hpairs
  intro n; induction n with
  | zero =>
    have := hvalid.1; simp only [system] at this
    rw [this]; intro _ _ _ _ _ h; exact absurd h nofun
  | succ n ih => exact hstep_pres n _ _ _ (hvalid.2 n) rfl ih

/-- Sending a DTI message implies the data has first component equal to the secret
    and dealer.pairs is some. -/
private theorem send_dti_data_fst (st st' : State p k) (s₀ : V p)
    (data : Fin (2 * k) → Pair p)
    (hstep : step p k st (.send (.dealerToIntermediary data)) st')
    (hhon_d : st.corrupted .Dealer = false)
    (hsec_inv : st.dealer.secret = some s₀ ∨ st.dealer.secret = none) :
    (∀ i, (data i).1 = s₀) ∧ st.dealer.pairs ≠ none := by
  cases hstep with
  | send_dealerToIntermediary s pairs hs hpairs _ =>
    refine ⟨fun i => ?_, by rw [hpairs]; exact nofun⟩
    simp; exact Option.some.inj
      (hsec_inv.elim (hs.symm.trans ·) (by rw [·] at hs; exact absurd hs nofun))
  | byzantine_step proc _ hcorr hsender =>
    simp only [Msg.sender] at hsender
    rw [← hsender] at hcorr; exact absurd hcorr (by simp [hhon_d])

/-- Sending authData adds it to the buffer. -/
private theorem send_authData_buf (st st' : State p k)
    (data : Fin (2 * k) → Option (Pair p))
    (hstep : step p k st (.send (.authData data)) st') :
    st'.buffer (.authData data) := by
  cases hstep with
  | send_authData => exact Or.inr rfl
  | byzantine_step => exact Or.inr rfl

/-- Receiving authData sets receiver.authData. -/
private theorem recv_authData_sets (st st' : State p k)
    (data : Fin (2 * k) → Option (Pair p))
    (hstep : step p k st (.recv (.authData data)) st') :
    st'.receiver.authData = some data := by
  cases hstep with
  | recv_authData => rfl

/-- The receiverDecide step requires authData to be some. -/
private theorem receiverDecide_requires_authData (st st' : State p k)
    (result : Option (V p))
    (hstep : step p k st (.receiverDecide result) st') :
    st.receiver.authData ≠ none := by
  cases hstep with
  | receiverDecide_step _ _ _ _ _ h _ _ _ _ => rw [h]; exact nofun

/-- Extract fields and the iff from a checkVerification step. -/
private theorem checkVerification_step_extract (st st' : State p k)
    (ok : Bool)
    (hstep : step p k st (.checkVerification ok) st') :
    ∃ sel intData resp,
      st.intermediary.selected = some sel ∧
      st.intermediary.received = some intData ∧
      st.intermediary.verifyResp = some resp ∧
      (ok = true ↔ ∀ i, sel i = true → ∀ b c, resp i = some (b, c) →
        c = b * (intData i).1 + (intData i).2) := by
  cases hstep with
  | checkVerification_step _ _ _ _ hs hr hvr _ _ hok => exact ⟨_, _, _, hs, hr, hvr, hok⟩

/-- Receiving DTI data: the data was in the pre-state buffer. -/
private theorem recv_dti_from_buf (st st' : State p k)
    (data : Fin (2 * k) → Pair p)
    (hstep : step p k st (.recv (.dealerToIntermediary data)) st') :
    st.buffer (.dealerToIntermediary data) := by
  cases hstep with
  | recv_intermediary _ hbuf _ _ => exact hbuf


/-- The state-level remap is its own inverse under the execution invariants. -/
private theorem remapState_inv (st : State p k)
    (hsec_inv : st.dealer.secret = some s₀ ∨ st.dealer.secret = none)
    (hrecv_fst : ∀ intData, st.intermediary.received = some intData →
      st.dealer.pairs ≠ none → ∀ i, (intData i).1 = s₀)
    (hno_auth_buf : ∀ data, ¬st.buffer (.authData data))
    (hauth_none : st.receiver.authData = none)
    (hbuf_fst : ∀ data, st.buffer (.dealerToIntermediary data) →
      st.dealer.pairs ≠ none → ∀ i, (data i).1 = s₀)
    (hverified_eq : ∀ v sel intData resp (pairs : Fin (2 * k) → V p × V p),
      st.intermediary.verified = some v →
      st.intermediary.selected = some sel →
      st.intermediary.received = some intData →
      st.intermediary.verifyResp = some resp →
      st.dealer.pairs = some pairs →
      v = computeVerified p k sel intData resp) :
    remapState p k s₁ s₀ (remapState p k s₀ s₁ st) = st := by
  have hir : (remapState p k s₁ s₀ (remapState p k s₀ s₁ st)).intermediary.received =
      st.intermediary.received := by
    simp only [remapState]
    cases hprs : st.dealer.pairs with
    | none => simp [Option.map]
    | some ps =>
      simp only [Option.map]; cases hrecv : st.intermediary.received with
      | none => simp
      | some intData =>
        simp only [Option.some.injEq]; exact remapDTI_inv_remapPairs p k s₀ s₁ ps intData
          (hrecv_fst intData hrecv (by rw [hprs]; exact nofun))
  have hiv : (remapState p k s₁ s₀ (remapState p k s₀ s₁ st)).intermediary.verified =
      st.intermediary.verified := by
    simp only [remapState]
    -- The verified field is recomputed only when all five prereqs are some.
    -- When any is none, the match falls through and verified is preserved.
    cases hprs : st.dealer.pairs with
    | none => cases st.intermediary.verified <;> cases st.intermediary.selected <;>
        cases st.intermediary.received <;> cases st.intermediary.verifyResp <;> simp
    | some ps =>
      match hv : st.intermediary.verified, hs : st.intermediary.selected,
          hr : st.intermediary.received, hvr : st.intermediary.verifyResp with
      | some v, some sel, some intData, some resp =>
        change some (computeVerified p k sel
          (remapDTI p k s₁ s₀ (remapPairs p k s₀ s₁ ps)
            (remapDTI p k s₀ s₁ ps intData)) resp) = some v
        rw [remapDTI_inv_remapPairs p k s₀ s₁ ps intData
          (hrecv_fst intData hr (by rw [hprs]; exact nofun))]
        congr 1; exact (hverified_eq v sel intData resp ps hv hs hr hvr hprs).symm
      | none, _, _, _ | _, none, _, _ | _, _, none, _ | _, _, _, none => simp
  have hbuf : (remapState p k s₁ s₀ (remapState p k s₀ s₁ st)).buffer =
      st.buffer := by
    simp only [remapState]; funext m
    cases m with
    | dealerToIntermediary data =>
      cases hprs : st.dealer.pairs with
      | none => rfl
      | some ps =>
        simp only [Option.map]; apply propext; constructor
        · rintro ⟨orig, ⟨orig₁, hb, rfl⟩, hdata⟩
          rw [remapDTI_inv_remapPairs p k s₀ s₁ ps orig₁
            (hbuf_fst orig₁ hb (by rw [hprs]; exact nofun))] at hdata
          rw [hdata]; exact hb
        · intro hb
          exact ⟨remapDTI p k s₀ s₁ ps data, ⟨data, hb, rfl⟩,
            (remapDTI_inv_remapPairs p k s₀ s₁ ps data
              (hbuf_fst data hb (by rw [hprs]; exact nofun))).symm⟩
    | authData data =>
      cases st.dealer.pairs with
      | none => rfl
      | some _ => exact propext ⟨fun ⟨_, ⟨o, hb, _⟩, _⟩ => absurd hb (hno_auth_buf o),
          fun h => absurd h (hno_auth_buf data)⟩
    | _ => rfl
  -- Combine field equalities into state equality
  exact State.mk.injEq .. |>.mpr
    ⟨DealerState.mk.injEq .. |>.mpr
       ⟨by simp only [remapState]; cases hsec_inv with | inl h => simp [h] | inr h => simp [h],
        by simp only [remapState]; cases st.dealer.pairs with
           | none => simp [Option.map] | some ps => simp [Option.map, remapPairs_inv]⟩,
     IntermediaryState.mk.injEq .. |>.mpr ⟨hir, by simp [remapState], by simp [remapState], hiv⟩,
     ReceiverState.mk.injEq .. |>.mpr
       ⟨by simp [remapState], by simp [remapState],
        by simp only [remapState, hauth_none]; cases st.dealer.pairs <;> simp [Option.map],
        by simp [remapState]⟩,
     hbuf, by simp [remapState]⟩

theorem remapExec_inv
    (e : LTS.Execution (State p k) (Label p k))
    (hvalid : (system p k).valid_exec e)
    (hpre : honestPreAuth p k e)
    (hsec : secretIs p k s₀ e) :
    remapExec p k s₁ s₀ (remapExec p k s₀ s₁ e) = e := by
  -- Extract honestPreAuth components
  obtain ⟨_, hhon, hauth_all⟩ := hpre
  -- Derive execution-level invariants
  have hsec_inv : ∀ n, (e.states n).dealer.secret = some s₀ ∨
      (e.states n).dealer.secret = none := by
    intro n; by_cases h : (e.states n).dealer.secret = none
    · exact Or.inr h
    · obtain ⟨s_val, hs⟩ := Option.ne_none_iff_exists'.mp h
      rw [hs]; left; congr 1; exact hsec n s_val hs
  have hbuf_fst := exec_inv_buf_fst p k e hvalid hhon hsec
  have hrecv_fst := exec_inv_recv_fst p k e hvalid hhon hsec
  have hverified_eq := exec_inv_verified_eq p k e hvalid hhon
  apply Execution.ext <;> funext n <;> simp only [remapExec]
  -- ═══ STATES ═══
  · exact remapState_inv p k (e.states n) (hsec_inv n) (hrecv_fst n)
      ((hauth_all n).1) ((hauth_all n).2) (hbuf_fst n) (hverified_eq n)
  -- ═══ LABELS ═══
  · cases hl : e.labels n with
    | corrupt proc => simp [remapLabel]
    | input s_val =>
      simp only [remapLabel]
      have : s_val = s₀ :=
        hsec (n + 1) s_val (input_step_defines_secret p k _ _ _ (hl ▸ hvalid.2 n))
      simp [this]
    | generate new_pairs =>
      simp only [remapLabel]
      congr 1; exact remapPairs_inv p k s₀ s₁ new_pairs
    | send m =>
      cases m with
      | dealerToIntermediary data =>
        simp only [remapLabel, remapState]
        cases hp_eq : (e.states n).dealer.pairs with
        | none =>
          -- send_dti requires pairs ≠ none
          exact absurd hp_eq (send_dti_data_fst p k _ _ s₀ data
            (hl ▸ hvalid.2 n) (hhon n).1 (hsec_inv n)).2
        | some ps =>
          simp only [Option.map, Label.send.injEq, Msg.dealerToIntermediary.injEq]
          exact remapDTI_inv_remapPairs p k s₀ s₁ ps data
            (send_dti_data_fst p k _ _ s₀ data (hl ▸ hvalid.2 n)
              (hhon n).1 (hsec_inv n)).1
      | authData data =>
        exact absurd (send_authData_buf p k _ _ data (hl ▸ hvalid.2 n))
          ((hauth_all (n + 1)).1 data)
      | _ => simp [remapLabel]
    | recv m =>
      cases m with
      | dealerToIntermediary data =>
        simp only [remapLabel, remapState]
        cases hp_eq : (e.states n).dealer.pairs with
        | none => simp [Option.map]
        | some ps =>
          simp only [Option.map, Label.recv.injEq, Msg.dealerToIntermediary.injEq]
          exact remapDTI_inv_remapPairs p k s₀ s₁ ps data
            (hbuf_fst n data (recv_dti_from_buf p k _ _ data (hl ▸ hvalid.2 n))
              (by rw [hp_eq]; exact nofun))
      | authData data =>
        exact absurd (recv_authData_sets p k _ _ data (hl ▸ hvalid.2 n))
          (by rw [(hauth_all (n + 1)).2]; exact nofun)
      | _ => simp [remapLabel]
    | selectIndices _ => simp [remapLabel]
    | checkVerification ok =>
      -- Extract fields and iff from the step (using helper to avoid dep. elim.)
      obtain ⟨sel, intD, resp, hsel_eq, hrec_eq, hvr_eq, hok_iff⟩ :=
        checkVerification_step_extract p k _ _ ok (hl ▸ hvalid.2 n)
      have hp_ne : (e.states n).dealer.pairs ≠ none :=
        fun h => absurd (exec_inv_recv_pairs p k e hvalid
          (fun m => (hhon m).1) n h) (by rw [hrec_eq]; exact nofun)
      obtain ⟨ps, hp_eq⟩ := Option.ne_none_iff_exists'.mp hp_ne
      have hfst := hrecv_fst n intD hrec_eq (by rw [hp_eq]; exact nofun)
      -- Double remap gives back intD
      have hinv := remapDTI_inv_remapPairs p k s₀ s₁ ps intD hfst
      -- ok = computeVerified sel intD resp
      have hok_cv : ok = computeVerified p k sel intD resp :=
        Bool.eq_iff_iff.mpr
          (hok_iff.trans (computeVerified_iff p k sel intD resp).symm)
      simp only [remapLabel, remapState, hsel_eq, hrec_eq, hvr_eq, hp_eq, Option.map]
      change Label.checkVerification _ = Label.checkVerification ok
      congr 1
      rw [hinv]
      exact hok_cv.symm
    | receiverDecide result =>
      -- Unreachable: receiverDecide requires authData = some, but honestPreAuth has authData = none
      exact absurd (receiverDecide_requires_authData p k _ _ result (hl ▸ hvalid.2 n))
        (by rw [(hauth_all n).2]; exact nofun)

/-- **Isomorphic secrecy** for Rabin's ICP: the remap is a
    view-preserving bijection between execution fibers.
    The preservation and view-invariance properties follow from
    `observation_independent_of_secret`. The invertibility follows from
    `remapExec_inv`, which shows the arithmetic remap is its own inverse
    (up to swapping the secret values). -/
theorem isomorphic_secret_ICP :
    (adversary p k).isomorphic_secret (secretIs p k) (honestPreAuth p k) := by
  have cv := fun e => (PLTS.toLTS_fromLTS_valid_exec (system p k) e).mp
  have cv' := fun e => (PLTS.toLTS_fromLTS_valid_exec (system p k) e).mpr
  exact (adversary p k).isomorphic_secret_by_remap
    (secretIs p k) (honestPreAuth p k) (remapExec p k)
    (fun v₁ v₂ e σ hval hcons hC hsec =>
      let ⟨hv, hc, hw, hC', hs⟩ :=
        observation_independent_of_secret p k v₁ v₂ e (cv e hval) hcons hC hsec
      ⟨cv' _ hv, hc, hw, hC', hs⟩)
    (fun v₁ v₂ e hval hC hsec =>
      remapExec_inv p k e (cv e hval) hC hsec)

end RabinICP
