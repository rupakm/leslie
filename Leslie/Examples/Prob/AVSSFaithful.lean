/-
Canetti-Rabin asynchronous verified secret sharing: faithful spec skeleton.

This file starts the CR-faithful model promised by
`AVSS-MODEL-NOTES.md` §17.  It intentionally does not mutate
`Leslie.Examples.Prob.AVSS.avssSpec`; the existing file remains the
threshold-faithful regression baseline.

The key difference from `AVSS.lean` is operational: echo and ready
traffic carries value/certificate content.  Receivers validate echo
values against their own column polynomial, and ready/output gates are
scoped to one candidate payload.  The commitment proof is left to a
later PR, where the candidate-scoped evidence should consume the
standard quorum-intersection bound.
-/

import Leslie.Examples.Prob.AVSS
import Leslie.Prob.Action
import Leslie.Prob.PMF
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma

namespace Leslie.Examples.Prob.AVSSFaithful

open Leslie.Prob

variable {n t : Nat} {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## Payloads and certificates -/

/-- Dealer payload sent to one party: row polynomial `f(alpha_p, y)`
and column polynomial `f(x, alpha_p)`.  A corrupt dealer may choose
these payloads independently for different parties. -/
structure DealerPayload (t : Nat) (F : Type*) where
  rowPoly : Fin (t + 1) -> F
  colPoly : Fin (t + 1) -> F
deriving DecidableEq

/-- Value-bearing echo from `sender` to `receiver`.

The intended honest value is the sender row evaluated at the receiver
point.  The receiver validates this same value against its own column
polynomial at the sender point. -/
structure EchoMsg (n t : Nat) (F : Type*) where
  sender : Fin n
  receiver : Fin n
  senderPayload : DealerPayload t F
  value : F
deriving DecidableEq

/-- Candidate-scoped ready certificate.

`supporters` records the senders whose validated echo evidence supports
the receiver's candidate payload.  Later commitment proofs should use
two such certificates plus quorum intersection to force agreement. -/
structure ReadyCert (n t : Nat) (F : Type*) where
  candidate : DealerPayload t F
  supporters : Finset (Fin n)
deriving DecidableEq

/-- Candidate-scoped ready message. -/
structure ReadyMsg (n t : Nat) (F : Type*) where
  sender : Fin n
  receiver : Fin n
  cert : ReadyCert n t F
deriving DecidableEq

namespace DealerPayload

/-- Canonical payload for an honest dealer at party `p`. -/
def ofCoeffs (partyPoint : Fin n -> F)
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F) (p : Fin n) :
    DealerPayload t F :=
  { rowPoly := AVSS.rowPolyOfDealer partyPoint coeffs p
    colPoly := AVSS.colPolyOfDealer partyPoint coeffs p }

end DealerPayload

/-! ## Local and global state -/

/-- Per-party state for the faithful AVSS skeleton.

The local evidence fields are deliberately value-bearing:

* `acceptedEchoes` stores validated echo messages, not just sender IDs.
* `readyReceived` stores candidate-scoped ready messages.
* `readySent` records the candidate certificates already broadcast by
  this party.
-/
structure LocalState (n t : Nat) (F : Type*) where
  delivered : Option (DealerPayload t F)
  echoedTo : Finset (Fin n)
  acceptedEchoes : Finset (EchoMsg n t F)
  readyReceived : Finset (ReadyMsg n t F)
  readySent : Finset (ReadyCert n t F)
  output : Option F
deriving DecidableEq

namespace LocalState

/-- Empty local state. -/
def init (n t : Nat) (F : Type*) : LocalState n t F :=
  { delivered := none
    echoedTo := ∅
    acceptedEchoes := ∅
    readyReceived := ∅
    readySent := ∅
    output := none }

end LocalState

/-- Global state for the faithful AVSS skeleton. -/
structure State (n t : Nat) (F : Type*) where
  partyPoint : Fin n -> F
  secret : F
  local_ : Fin n -> LocalState n t F
  corrupted : Finset (Fin n)
  dealerHonest : Bool
  dealerSent : Fin n -> Bool
  dealerCommit : Fin n -> DealerPayload t F
  inflightDeliveries : Finset (Fin n)
  inflightCorruptDeliveries : Finset (Fin n)
  inflightEchoes : Finset (EchoMsg n t F)
  inflightReady : Finset (ReadyMsg n t F)
deriving DecidableEq

namespace State

/-- A party is honest iff it is outside the static corruption set. -/
def isHonest (s : State n t F) (p : Fin n) : Prop :=
  p ∉ s.corrupted

instance (s : State n t F) (p : Fin n) : Decidable (s.isHonest p) :=
  inferInstanceAs (Decidable (p ∉ s.corrupted))

end State

/-! ## Initial states -/

/-- Initial-state predicate for the faithful skeleton.

For honest dealers, every per-party commitment is the canonical
row+column payload from the sampled bivariate polynomial.  For corrupt
dealers, the per-party commitments are intentionally unconstrained. -/
def initPred (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F) (s : State n t F) : Prop :=
  (∀ p, s.local_ p = LocalState.init n t F) ∧
  s.secret = sec ∧
  s.corrupted = corr ∧
  s.dealerSent = (fun _ => false) ∧
  s.inflightDeliveries = ∅ ∧
  s.inflightCorruptDeliveries = ∅ ∧
  s.inflightEchoes = ∅ ∧
  s.inflightReady = ∅ ∧
  (s.dealerHonest = true ->
    coeffs 0 0 = sec ∧
    ∀ p, s.dealerCommit p = DealerPayload.ofCoeffs s.partyPoint coeffs p)

/-! ## Evidence predicates -/

/-- Echo validation at receiver `p` for candidate payload `candidate`.

The echo must be addressed to `p`; its value must agree with the
sender's row at `p`'s point and with `candidate`'s column at the
sender's point. -/
def validEchoFor (partyPoint : Fin n -> F) (p : Fin n)
    (candidate : DealerPayload t F) (msg : EchoMsg n t F) : Prop :=
  msg.receiver = p ∧
  msg.value = AVSS.evalRowPoly msg.senderPayload.rowPoly (partyPoint p) ∧
  msg.value = AVSS.evalRowPoly candidate.colPoly (partyPoint msg.sender)

/-- The local echo set contains evidence from every listed supporter. -/
def echoCertSupported (s : State n t F) (p : Fin n)
    (cert : ReadyCert n t F) : Prop :=
  ∀ q, q ∈ cert.supporters ->
    ∃ msg ∈ (s.local_ p).acceptedEchoes,
      msg.sender = q ∧ validEchoFor s.partyPoint p cert.candidate msg

/-- The local ready set contains one ready message from every listed
supporter for the same candidate payload. -/
def readyCertSupported (s : State n t F) (p : Fin n)
    (cert : ReadyCert n t F) : Prop :=
  ∀ q, q ∈ cert.supporters ->
    ∃ msg ∈ (s.local_ p).readyReceived,
      msg.sender = q ∧ msg.cert.candidate = cert.candidate

/-! ## Actions and transitions -/

/-- Faithful AVSS protocol actions. -/
inductive Action (n t : Nat) (F : Type*)
  | dealerShareTo (p : Fin n)
  | partyDeliver (p : Fin n)
  | partyCorruptDeliver (p : Fin n)
  | partyEchoSend (sender receiver : Fin n)
  | partyEchoReceive (msg : EchoMsg n t F)
  | partyReady (p : Fin n) (cert : ReadyCert n t F)
  | partyAmplify (p : Fin n) (cert : ReadyCert n t F)
  | partyReceiveReady (msg : ReadyMsg n t F)
  | partyOutput (p : Fin n) (cert : ReadyCert n t F)
deriving DecidableEq

/-- Functional update for one party's local state. -/
def setLocal (s : State n t F) (p : Fin n) (ls : LocalState n t F) :
    State n t F :=
  { s with local_ := fun q => if q = p then ls else s.local_ q }

omit [Field F] [Fintype F] [DecidableEq F] in
@[simp] theorem setLocal_local_self (s : State n t F) (p : Fin n)
    (ls : LocalState n t F) :
    (setLocal s p ls).local_ p = ls := by
  simp [setLocal]

omit [Field F] [Fintype F] [DecidableEq F] in
@[simp] theorem setLocal_local_ne (s : State n t F) (p q : Fin n)
    (ls : LocalState n t F) (h : q ≠ p) :
    (setLocal s p ls).local_ q = s.local_ q := by
  simp [setLocal, h]

/-- Deterministic next-state function.  Gates are enforced separately;
failed gates return `s` through `ProbActionSpec.step = none`, not here. -/
def step (a : Action n t F) (s : State n t F) : State n t F :=
  match a with
  | .dealerShareTo p =>
      { s with
        dealerSent := Function.update s.dealerSent p true
        inflightDeliveries :=
          if p ∉ s.corrupted then insert p s.inflightDeliveries
          else s.inflightDeliveries
        inflightCorruptDeliveries :=
          if p ∈ s.corrupted then insert p s.inflightCorruptDeliveries
          else s.inflightCorruptDeliveries }
  | .partyDeliver p =>
      let ls' : LocalState n t F := { s.local_ p with delivered := some (s.dealerCommit p) }
      let s' := setLocal s p ls'
      { s' with inflightDeliveries := s.inflightDeliveries.erase p }
  | .partyCorruptDeliver p =>
      let ls' : LocalState n t F := { s.local_ p with delivered := some (s.dealerCommit p) }
      let s' := setLocal s p ls'
      { s' with inflightCorruptDeliveries := s.inflightCorruptDeliveries.erase p }
  | .partyEchoSend q p =>
      let payload := (s.local_ q).delivered.getD (s.dealerCommit q)
      let msg : EchoMsg n t F :=
        { sender := q
          receiver := p
          senderPayload := payload
          value := AVSS.evalRowPoly payload.rowPoly (s.partyPoint p) }
      let ls' : LocalState n t F :=
        { s.local_ q with echoedTo := insert p (s.local_ q).echoedTo }
      let s' := setLocal s q ls'
      { s' with inflightEchoes := insert msg s.inflightEchoes }
  | .partyEchoReceive msg =>
      let p := msg.receiver
      let ls' : LocalState n t F :=
        { s.local_ p with acceptedEchoes := insert msg (s.local_ p).acceptedEchoes }
      let s' := setLocal s p ls'
      { s' with inflightEchoes := s.inflightEchoes.erase msg }
  | .partyReady p cert =>
      let ls' : LocalState n t F :=
        { s.local_ p with readySent := insert cert (s.local_ p).readySent }
      let s' := setLocal s p ls'
      { s' with
        inflightReady :=
          s.inflightReady ∪
            (Finset.univ : Finset (Fin n)).image
              (fun r => ({ sender := p, receiver := r, cert := cert } : ReadyMsg n t F)) }
  | .partyAmplify p cert =>
      let ls' : LocalState n t F :=
        { s.local_ p with readySent := insert cert (s.local_ p).readySent }
      let s' := setLocal s p ls'
      { s' with
        inflightReady :=
          s.inflightReady ∪
            (Finset.univ : Finset (Fin n)).image
              (fun r => ({ sender := p, receiver := r, cert := cert } : ReadyMsg n t F)) }
  | .partyReceiveReady msg =>
      let p := msg.receiver
      let ls' : LocalState n t F :=
        { s.local_ p with readyReceived := insert msg (s.local_ p).readyReceived }
      let s' := setLocal s p ls'
      { s' with inflightReady := s.inflightReady.erase msg }
  | .partyOutput p cert =>
      let ls' : LocalState n t F :=
        { s.local_ p with output := some (AVSS.evalRowPoly cert.candidate.rowPoly 0) }
      setLocal s p ls'

/-- Gates for the faithful skeleton.

The send/receive thresholds are candidate-scoped: ready and output
actions carry the certificate they are using, and the gate checks that
the local evidence supports that same candidate. -/
def gate (a : Action n t F) (s : State n t F) : Prop :=
  match a with
  | .dealerShareTo p =>
      s.dealerSent p = false
  | .partyDeliver p =>
      s.dealerSent p = true ∧ p ∉ s.corrupted ∧ p ∈ s.inflightDeliveries ∧
        (s.local_ p).delivered = none
  | .partyCorruptDeliver p =>
      s.dealerSent p = true ∧ p ∈ s.corrupted ∧
        p ∈ s.inflightCorruptDeliveries ∧ (s.local_ p).delivered = none
  | .partyEchoSend q p =>
      (s.local_ q).delivered.isSome ∧ p ∉ (s.local_ q).echoedTo
  | .partyEchoReceive msg =>
      msg ∈ s.inflightEchoes ∧
        ∃ candidate, (s.local_ msg.receiver).delivered = some candidate ∧
          validEchoFor s.partyPoint msg.receiver candidate msg ∧
          msg ∉ (s.local_ msg.receiver).acceptedEchoes
  | .partyReady p cert =>
      (s.local_ p).delivered = some cert.candidate ∧
        cert ∉ (s.local_ p).readySent ∧
        cert.supporters.card ≥ n - t ∧
        echoCertSupported s p cert
  | .partyAmplify p cert =>
      cert ∉ (s.local_ p).readySent ∧
        cert.supporters.card ≥ t + 1 ∧
        readyCertSupported s p cert
  | .partyReceiveReady msg =>
      msg ∈ s.inflightReady ∧ msg ∉ (s.local_ msg.receiver).readyReceived
  | .partyOutput p cert =>
      p ∉ s.corrupted ∧ (s.local_ p).output = none ∧
        (s.local_ p).delivered = some cert.candidate ∧
        cert.supporters.card ≥ n - t ∧
        readyCertSupported s p cert

/-! ## Spec -/

/-- Faithful AVSS probabilistic spec skeleton.  Randomness lives in the
initial measure; all protocol actions are deterministic. -/
noncomputable def spec (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F) :
    ProbActionSpec (State n t F) (Action n t F) where
  init := initPred sec corr coeffs
  actions := fun a =>
    { gate := gate a
      effect := fun s _ => PMF.pure (step a s) }

omit [Fintype F] in
@[simp] theorem spec_step_pure (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F)
    (a : Action n t F) (s : State n t F) (h : gate a s) :
    (spec (t := t) sec corr coeffs).step a s = some (PMF.pure (step a s)) :=
  ProbActionSpec.step_eq_some h

omit [Fintype F] in
theorem spec_step_none (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F)
    (a : Action n t F) (s : State n t F) (h : ¬ gate a s) :
    (spec (t := t) sec corr coeffs).step a s = none :=
  ProbActionSpec.step_eq_none h

/-! ## Measurability and finiteness -/

section Instances

instance : MeasurableSpace (DealerPayload t F) := ⊤
instance : MeasurableSingletonClass (DealerPayload t F) := ⟨fun _ => trivial⟩
instance : MeasurableSpace (EchoMsg n t F) := ⊤
instance : MeasurableSingletonClass (EchoMsg n t F) := ⟨fun _ => trivial⟩
instance : MeasurableSpace (ReadyCert n t F) := ⊤
instance : MeasurableSingletonClass (ReadyCert n t F) := ⟨fun _ => trivial⟩
instance : MeasurableSpace (ReadyMsg n t F) := ⊤
instance : MeasurableSingletonClass (ReadyMsg n t F) := ⟨fun _ => trivial⟩
instance : MeasurableSpace (LocalState n t F) := ⊤
instance : MeasurableSingletonClass (LocalState n t F) := ⟨fun _ => trivial⟩
instance : MeasurableSpace (State n t F) := ⊤
instance : MeasurableSingletonClass (State n t F) := ⟨fun _ => trivial⟩
instance : MeasurableSpace (Action n t F) := ⊤
instance : MeasurableSingletonClass (Action n t F) := ⟨fun _ => trivial⟩

noncomputable instance : Fintype (DealerPayload t F) := by
  classical
  exact Fintype.ofEquiv ((Fin (t + 1) -> F) × (Fin (t + 1) -> F))
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun p => (p.rowPoly, p.colPoly)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance : Countable (DealerPayload t F) := Finite.to_countable

noncomputable instance : Fintype (EchoMsg n t F) := by
  classical
  exact Fintype.ofEquiv (Fin n × Fin n × DealerPayload t F × F)
    { toFun := fun x =>
        ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
      invFun := fun msg =>
        (msg.sender, msg.receiver, msg.senderPayload, msg.value)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance : Countable (EchoMsg n t F) := Finite.to_countable

noncomputable instance : Fintype (ReadyCert n t F) := by
  classical
  exact Fintype.ofEquiv (DealerPayload t F × Finset (Fin n))
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun cert => (cert.candidate, cert.supporters)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance : Countable (ReadyCert n t F) := Finite.to_countable

noncomputable instance : Fintype (ReadyMsg n t F) := by
  classical
  exact Fintype.ofEquiv (Fin n × Fin n × ReadyCert n t F)
    { toFun := fun x => ⟨x.1, x.2.1, x.2.2⟩
      invFun := fun msg => (msg.sender, msg.receiver, msg.cert)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance : Countable (ReadyMsg n t F) := Finite.to_countable

noncomputable instance : Fintype (LocalState n t F) := by
  classical
  exact Fintype.ofEquiv
    (Option (DealerPayload t F) × Finset (Fin n) × Finset (EchoMsg n t F) ×
      Finset (ReadyMsg n t F) × Finset (ReadyCert n t F) × Option F)
    { toFun := fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
        x.2.2.2.2.2⟩
      invFun := fun ls =>
        (ls.delivered, ls.echoedTo, ls.acceptedEchoes, ls.readyReceived,
          ls.readySent, ls.output)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance : Countable (LocalState n t F) := Finite.to_countable

noncomputable instance : Fintype (State n t F) := by
  classical
  exact Fintype.ofEquiv
    ((Fin n -> F) × F × (Fin n -> LocalState n t F) × Finset (Fin n) × Bool ×
      (Fin n -> Bool) × (Fin n -> DealerPayload t F) × Finset (Fin n) ×
      Finset (Fin n) × Finset (EchoMsg n t F) × Finset (ReadyMsg n t F))
    { toFun := fun x =>
        ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1,
          x.2.2.2.2.2.1, x.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.1,
          x.2.2.2.2.2.2.2.2.1, x.2.2.2.2.2.2.2.2.2.1,
          x.2.2.2.2.2.2.2.2.2.2⟩
      invFun := fun s =>
        (s.partyPoint, s.secret, s.local_, s.corrupted, s.dealerHonest,
          s.dealerSent, s.dealerCommit, s.inflightDeliveries,
          s.inflightCorruptDeliveries, s.inflightEchoes, s.inflightReady)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance : Countable (State n t F) := Finite.to_countable

noncomputable instance : Fintype (Action n t F) := by
  classical
  exact Fintype.ofEquiv
    (Fin n ⊕ Fin n ⊕ Fin n ⊕ (Fin n × Fin n) ⊕ EchoMsg n t F ⊕
      (Fin n × ReadyCert n t F) ⊕ (Fin n × ReadyCert n t F) ⊕
      ReadyMsg n t F ⊕ (Fin n × ReadyCert n t F))
    { toFun := fun
        | .inl p => .dealerShareTo p
        | .inr (.inl p) => .partyDeliver p
        | .inr (.inr (.inl p)) => .partyCorruptDeliver p
        | .inr (.inr (.inr (.inl x))) => .partyEchoSend x.1 x.2
        | .inr (.inr (.inr (.inr (.inl msg)))) => .partyEchoReceive msg
        | .inr (.inr (.inr (.inr (.inr (.inl x))))) => .partyReady x.1 x.2
        | .inr (.inr (.inr (.inr (.inr (.inr (.inl x)))))) =>
            .partyAmplify x.1 x.2
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl msg))))))) =>
            .partyReceiveReady msg
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr x))))))) =>
            .partyOutput x.1 x.2
      invFun := fun
        | .dealerShareTo p => .inl p
        | .partyDeliver p => .inr (.inl p)
        | .partyCorruptDeliver p => .inr (.inr (.inl p))
        | .partyEchoSend q p => .inr (.inr (.inr (.inl (q, p))))
        | .partyEchoReceive msg => .inr (.inr (.inr (.inr (.inl msg))))
        | .partyReady p cert => .inr (.inr (.inr (.inr (.inr (.inl (p, cert))))))
        | .partyAmplify p cert =>
            .inr (.inr (.inr (.inr (.inr (.inr (.inl (p, cert)))))))
        | .partyReceiveReady msg =>
            .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl msg)))))))
        | .partyOutput p cert =>
            .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (p, cert))))))))
      left_inv := fun
        | .inl _ => rfl
        | .inr (.inl _) => rfl
        | .inr (.inr (.inl _)) => rfl
        | .inr (.inr (.inr (.inl _))) => rfl
        | .inr (.inr (.inr (.inr (.inl _)))) => rfl
        | .inr (.inr (.inr (.inr (.inr (.inl _))))) => rfl
        | .inr (.inr (.inr (.inr (.inr (.inr (.inl _)))))) => rfl
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl _))))))) => rfl
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr _))))))) => rfl
      right_inv := fun
        | .dealerShareTo _ => rfl
        | .partyDeliver _ => rfl
        | .partyCorruptDeliver _ => rfl
        | .partyEchoSend _ _ => rfl
        | .partyEchoReceive _ => rfl
        | .partyReady _ _ => rfl
        | .partyAmplify _ _ => rfl
        | .partyReceiveReady _ => rfl
        | .partyOutput _ _ => rfl }

instance : Countable (Action n t F) := Finite.to_countable

end Instances

end Leslie.Examples.Prob.AVSSFaithful
