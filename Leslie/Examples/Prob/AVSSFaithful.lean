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

/-! ## State-frame lemmas for `step`

These mirror the pattern in `Leslie.Examples.Prob.AVSS`
(`avssStep_partyPoint_invariant`, `avssStep_corrupted_invariant`,
etc.).  Most fields are preserved by every action; the only
field-level monotone update is `dealerSent` under `dealerShareTo`. -/

omit [Fintype F] in
/-- `partyPoint` is preserved by every `step` action. -/
theorem step_partyPoint_invariant (a : Action n t F) (s : State n t F) :
    (step a s).partyPoint = s.partyPoint := by
  cases a <;> simp [step, setLocal]

omit [Fintype F] in
/-- `secret` is preserved by every `step` action. -/
theorem step_secret_invariant (a : Action n t F) (s : State n t F) :
    (step a s).secret = s.secret := by
  cases a <;> simp [step, setLocal]

omit [Fintype F] in
/-- `corrupted` is preserved by every `step` action. -/
theorem step_corrupted_invariant (a : Action n t F) (s : State n t F) :
    (step a s).corrupted = s.corrupted := by
  cases a <;> simp [step, setLocal]

omit [Fintype F] in
/-- `dealerHonest` is preserved by every `step` action. -/
theorem step_dealerHonest_invariant (a : Action n t F) (s : State n t F) :
    (step a s).dealerHonest = s.dealerHonest := by
  cases a <;> simp [step, setLocal]

omit [Fintype F] in
/-- `dealerCommit` is preserved by every `step` action.  The per-party
commitments are pinned at init (canonically for honest dealer, freely
for corrupt dealer) and never modified afterwards. -/
theorem step_dealerCommit_invariant (a : Action n t F) (s : State n t F) :
    (step a s).dealerCommit = s.dealerCommit := by
  cases a <;> simp [step, setLocal]

omit [Fintype F] in
/-- Frame: `dealerSent p` is unchanged by any action other than
`dealerShareTo p`. -/
theorem step_dealerSent_self_unless (a : Action n t F) (s : State n t F)
    (p : Fin n) (h_not_share : a ≠ .dealerShareTo p) :
    (step a s).dealerSent p = s.dealerSent p := by
  cases a with
  | dealerShareTo q =>
    have hpq : p ≠ q := fun heq => h_not_share (heq ▸ rfl)
    show (step (.dealerShareTo q) s).dealerSent p = s.dealerSent p
    simp [step, Function.update_of_ne hpq]
  | partyDeliver q => simp [step, setLocal]
  | partyCorruptDeliver q => simp [step, setLocal]
  | partyEchoSend q r => simp [step, setLocal]
  | partyEchoReceive msg => simp [step, setLocal]
  | partyReady q cert => simp [step, setLocal]
  | partyAmplify q cert => simp [step, setLocal]
  | partyReceiveReady msg => simp [step, setLocal]
  | partyOutput q cert => simp [step, setLocal]

omit [Fintype F] in
/-- After `dealerShareTo p`, `dealerSent p = true`. -/
theorem step_dealerSent_set_after (s : State n t F) (p : Fin n) :
    (step (.dealerShareTo p) s).dealerSent p = true := by
  show (step (.dealerShareTo p) s).dealerSent p = true
  simp [step, Function.update_self]

omit [Fintype F] in
/-- Monotonicity: `dealerSent p = true` is preserved by every action. -/
theorem step_dealerSent_monotone (a : Action n t F) (s : State n t F)
    (p : Fin n) (h_pre : s.dealerSent p = true) :
    (step a s).dealerSent p = true := by
  by_cases h : a = .dealerShareTo p
  · subst h; exact step_dealerSent_set_after s p
  · rw [step_dealerSent_self_unless a s p h]; exact h_pre

/-! ## Initial-state-predicate properties

These extract individual facts pinned by `initPred`.  They are pure
projections — no induction or step reasoning. -/

omit [Fintype F] [DecidableEq F] in
/-- `initPred` does not constrain `partyPoint`: any value is permitted. -/
theorem initPred_partyPoint_arbitrary (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F) (s : State n t F)
    (h : initPred sec corr coeffs s) (pp : Fin n -> F) :
    initPred sec corr coeffs { s with partyPoint := pp } ∨
      initPred sec corr coeffs s := Or.inr h

omit [Fintype F] [DecidableEq F] in
/-- Under honest dealer, `initPred` pins every per-party commitment to
the canonical row+column payload. -/
theorem initPred_dealerCommit_honest (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F) (s : State n t F)
    (h : initPred sec corr coeffs s) (hh : s.dealerHonest = true) (p : Fin n) :
    s.dealerCommit p = DealerPayload.ofCoeffs s.partyPoint coeffs p :=
  (h.2.2.2.2.2.2.2.2 hh).2 p

omit [Fintype F] [DecidableEq F] in
/-- `initPred` pins the corruption set. -/
theorem initPred_corrupted (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F) (s : State n t F)
    (h : initPred sec corr coeffs s) :
    s.corrupted = corr := h.2.2.1

omit [Fintype F] [DecidableEq F] in
/-- `initPred` pins the secret. -/
theorem initPred_secret (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F) (s : State n t F)
    (h : initPred sec corr coeffs s) :
    s.secret = sec := h.2.1

omit [Fintype F] [DecidableEq F] in
/-- `initPred` pins `dealerSent` to the constant-`false` function. -/
theorem initPred_dealerSent_init (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F) (s : State n t F)
    (h : initPred sec corr coeffs s) (p : Fin n) :
    s.dealerSent p = false := by
  have hfn : s.dealerSent = (fun _ => false) := h.2.2.2.1
  simp [hfn]

/-! ## Phase-1 invariants

Three simple invariants with init + preservation lemmas.  These are
the foundation for the queue / flight / freshness invariants in
Step 2 and the substantive cryptographic invariants later. -/

/-- Honest-dealer commitment invariant: under an honest dealer, every
per-party commitment is the canonical bivariate payload at that party
point.  Trivially preserved (both `dealerCommit` and `partyPoint` are
pinned by `step`). -/
def honestDealerCommitInv
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F) (s : State n t F) : Prop :=
  s.dealerHonest = true ->
    ∀ p, s.dealerCommit p = DealerPayload.ofCoeffs s.partyPoint coeffs p

omit [Fintype F] [DecidableEq F] in
/-- Honest-dealer commitment holds at init. -/
theorem honestDealerCommitInv_init (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F) (s : State n t F)
    (h : initPred sec corr coeffs s) :
    honestDealerCommitInv coeffs s := fun hh =>
  (h.2.2.2.2.2.2.2.2 hh).2

omit [Fintype F] in
/-- Honest-dealer commitment is preserved by every `step` action. -/
theorem honestDealerCommitInv_preserve
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F)
    (a : Action n t F) (s : State n t F)
    (h : honestDealerCommitInv coeffs s) :
    honestDealerCommitInv coeffs (step a s) := by
  intro hh p
  rw [step_dealerCommit_invariant, step_partyPoint_invariant]
  apply h
  rw [step_dealerHonest_invariant] at hh
  exact hh

/-- Delivered-implies-dealer-sent invariant: a party with a delivered
payload must have been served by `dealerShareTo`.  Preserved by the
`partyDeliver` and `partyCorruptDeliver` gates (each requires
`dealerSent p = true`); other actions don't change `delivered`. -/
def deliveredImpliesDealerSent (s : State n t F) : Prop :=
  ∀ p, (s.local_ p).delivered.isSome -> s.dealerSent p = true

omit [Fintype F] [DecidableEq F] in
/-- Vacuously true at init: no party is delivered. -/
theorem deliveredImpliesDealerSent_init (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F) (s : State n t F)
    (h : initPred sec corr coeffs s) :
    deliveredImpliesDealerSent s := by
  intro p hd
  have hloc : s.local_ p = LocalState.init n t F := h.1 p
  rw [hloc] at hd
  simp [LocalState.init] at hd

omit [Fintype F] in
/-- Preservation: any action that introduces a delivered payload at `p`
is gated by `dealerSent p = true`; other actions don't change
`delivered` and `dealerSent` is monotone. -/
theorem deliveredImpliesDealerSent_preserve
    (a : Action n t F) (s : State n t F)
    (hgate : gate a s) (h : deliveredImpliesDealerSent s) :
    deliveredImpliesDealerSent (step a s) := by
  intro p hd
  cases a with
  | dealerShareTo q =>
    -- step doesn't touch local_; reduce to old `delivered` + monotonicity
    have hloc : (step (.dealerShareTo q) s).local_ p = s.local_ p := by
      simp [step, setLocal]
    rw [hloc] at hd
    exact step_dealerSent_monotone _ _ _ (h p hd)
  | partyDeliver q =>
    by_cases hpq : p = q
    · subst hpq
      -- gate gives dealerSent p = true; step preserves dealerSent on this branch
      have hsent : s.dealerSent p = true := hgate.1
      have : (step (.partyDeliver p) s).dealerSent p = s.dealerSent p := by
        simp [step, setLocal]
      rw [this]; exact hsent
    · have hloc : (step (.partyDeliver q) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpq]
      rw [hloc] at hd
      have hpre : s.dealerSent p = true := h p hd
      have : (step (.partyDeliver q) s).dealerSent p = s.dealerSent p := by
        simp [step, setLocal]
      rw [this]; exact hpre
  | partyCorruptDeliver q =>
    by_cases hpq : p = q
    · subst hpq
      have hsent : s.dealerSent p = true := hgate.1
      have : (step (.partyCorruptDeliver p) s).dealerSent p = s.dealerSent p := by
        simp [step, setLocal]
      rw [this]; exact hsent
    · have hloc : (step (.partyCorruptDeliver q) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpq]
      rw [hloc] at hd
      have hpre : s.dealerSent p = true := h p hd
      have : (step (.partyCorruptDeliver q) s).dealerSent p = s.dealerSent p := by
        simp [step, setLocal]
      rw [this]; exact hpre
  | partyEchoSend q r =>
    -- step only updates echoedTo on q's local state; delivered untouched
    have hd' : (s.local_ p).delivered.isSome := by
      by_cases hpq : p = q
      · subst hpq
        have : (step (.partyEchoSend p r) s).local_ p =
            { s.local_ p with echoedTo := insert r (s.local_ p).echoedTo } := by
          simp [step, setLocal]
        rw [this] at hd; exact hd
      · have : (step (.partyEchoSend q r) s).local_ p = s.local_ p := by
          simp [step, setLocal, hpq]
        rw [this] at hd; exact hd
    have hpre : s.dealerSent p = true := h p hd'
    have : (step (.partyEchoSend q r) s).dealerSent p = s.dealerSent p := by
      simp [step, setLocal]
    rw [this]; exact hpre
  | partyEchoReceive msg =>
    have hd' : (s.local_ p).delivered.isSome := by
      by_cases hpq : p = msg.receiver
      · rw [hpq] at hd ⊢
        have : (step (.partyEchoReceive msg) s).local_ msg.receiver =
            { s.local_ msg.receiver with
              acceptedEchoes :=
                insert msg (s.local_ msg.receiver).acceptedEchoes } := by
          simp [step, setLocal]
        rw [this] at hd; exact hd
      · have : (step (.partyEchoReceive msg) s).local_ p = s.local_ p := by
          simp [step, setLocal, hpq]
        rw [this] at hd; exact hd
    have hpre : s.dealerSent p = true := h p hd'
    have : (step (.partyEchoReceive msg) s).dealerSent p = s.dealerSent p := by
      simp [step, setLocal]
    rw [this]; exact hpre
  | partyReady q cert =>
    have hd' : (s.local_ p).delivered.isSome := by
      by_cases hpq : p = q
      · subst hpq
        have : (step (.partyReady p cert) s).local_ p =
            { s.local_ p with readySent := insert cert (s.local_ p).readySent } := by
          simp [step, setLocal]
        rw [this] at hd; exact hd
      · have : (step (.partyReady q cert) s).local_ p = s.local_ p := by
          simp [step, setLocal, hpq]
        rw [this] at hd; exact hd
    have hpre : s.dealerSent p = true := h p hd'
    have : (step (.partyReady q cert) s).dealerSent p = s.dealerSent p := by
      simp [step, setLocal]
    rw [this]; exact hpre
  | partyAmplify q cert =>
    have hd' : (s.local_ p).delivered.isSome := by
      by_cases hpq : p = q
      · subst hpq
        have : (step (.partyAmplify p cert) s).local_ p =
            { s.local_ p with readySent := insert cert (s.local_ p).readySent } := by
          simp [step, setLocal]
        rw [this] at hd; exact hd
      · have : (step (.partyAmplify q cert) s).local_ p = s.local_ p := by
          simp [step, setLocal, hpq]
        rw [this] at hd; exact hd
    have hpre : s.dealerSent p = true := h p hd'
    have : (step (.partyAmplify q cert) s).dealerSent p = s.dealerSent p := by
      simp [step, setLocal]
    rw [this]; exact hpre
  | partyReceiveReady msg =>
    have hd' : (s.local_ p).delivered.isSome := by
      by_cases hpq : p = msg.receiver
      · rw [hpq] at hd ⊢
        have : (step (.partyReceiveReady msg) s).local_ msg.receiver =
            { s.local_ msg.receiver with
              readyReceived :=
                insert msg (s.local_ msg.receiver).readyReceived } := by
          simp [step, setLocal]
        rw [this] at hd; exact hd
      · have : (step (.partyReceiveReady msg) s).local_ p = s.local_ p := by
          simp [step, setLocal, hpq]
        rw [this] at hd; exact hd
    have hpre : s.dealerSent p = true := h p hd'
    have : (step (.partyReceiveReady msg) s).dealerSent p = s.dealerSent p := by
      simp [step, setLocal]
    rw [this]; exact hpre
  | partyOutput q cert =>
    have hd' : (s.local_ p).delivered.isSome := by
      by_cases hpq : p = q
      · subst hpq
        have : (step (.partyOutput p cert) s).local_ p =
            { s.local_ p with
              output := some (AVSS.evalRowPoly cert.candidate.rowPoly 0) } := by
          simp [step, setLocal]
        rw [this] at hd; exact hd
      · have : (step (.partyOutput q cert) s).local_ p = s.local_ p := by
          simp [step, setLocal, hpq]
        rw [this] at hd; exact hd
    have hpre : s.dealerSent p = true := h p hd'
    have : (step (.partyOutput q cert) s).dealerSent p = s.dealerSent p := by
      simp [step, setLocal]
    rw [this]; exact hpre

/-- Echoed-implies-delivered invariant: if party `p` has marked party
`q` as echoed-to, then `p` has a delivered payload (the gate of
`partyEchoSend p q` requires `delivered.isSome`). -/
def echoedToImpliesDelivered (s : State n t F) : Prop :=
  ∀ p q, q ∈ (s.local_ p).echoedTo -> (s.local_ p).delivered.isSome

omit [Fintype F] [DecidableEq F] in
/-- Vacuously true at init: every `echoedTo` is empty. -/
theorem echoedToImpliesDelivered_init (sec : F) (corr : Finset (Fin n))
    (coeffs : Fin (t + 1) -> Fin (t + 1) -> F) (s : State n t F)
    (h : initPred sec corr coeffs s) :
    echoedToImpliesDelivered s := by
  intro p q hq
  have hloc : s.local_ p = LocalState.init n t F := h.1 p
  rw [hloc] at hq
  simp [LocalState.init] at hq

omit [Fintype F] in
/-- Preservation: only `partyEchoSend` extends `echoedTo`, and its
gate provides the required `delivered.isSome`.  Other actions either
leave `local_ p` alone or extend non-`echoedTo` and non-`delivered`
fields. -/
theorem echoedToImpliesDelivered_preserve
    (a : Action n t F) (s : State n t F)
    (hgate : gate a s) (h : echoedToImpliesDelivered s) :
    echoedToImpliesDelivered (step a s) := by
  intro p q hq
  cases a with
  | dealerShareTo r =>
    have hloc : (step (.dealerShareTo r) s).local_ p = s.local_ p := by
      simp [step, setLocal]
    rw [hloc] at hq ⊢
    exact h p q hq
  | partyDeliver r =>
    -- delivered becomes some at r; echoedTo unchanged at r
    by_cases hpr : p = r
    · subst hpr
      have hloc : (step (.partyDeliver p) s).local_ p =
          { s.local_ p with delivered := some (s.dealerCommit p) } := by
        simp [step, setLocal]
      rw [hloc] at hq ⊢
      simp at hq ⊢
    · have hloc : (step (.partyDeliver r) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpr]
      rw [hloc] at hq ⊢
      exact h p q hq
  | partyCorruptDeliver r =>
    by_cases hpr : p = r
    · subst hpr
      have hloc : (step (.partyCorruptDeliver p) s).local_ p =
          { s.local_ p with delivered := some (s.dealerCommit p) } := by
        simp [step, setLocal]
      rw [hloc] at hq ⊢
      simp at hq ⊢
    · have hloc : (step (.partyCorruptDeliver r) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpr]
      rw [hloc] at hq ⊢
      exact h p q hq
  | partyEchoSend r r' =>
    by_cases hpr : p = r
    · subst hpr
      have hloc : (step (.partyEchoSend p r') s).local_ p =
          { s.local_ p with echoedTo := insert r' (s.local_ p).echoedTo } := by
        simp [step, setLocal]
      rw [hloc] at hq ⊢
      -- gate says s.local_ p has delivered.isSome
      exact hgate.1
    · have hloc : (step (.partyEchoSend r r') s).local_ p = s.local_ p := by
        simp [step, setLocal, hpr]
      rw [hloc] at hq ⊢
      exact h p q hq
  | partyEchoReceive msg =>
    by_cases hpr : p = msg.receiver
    · rw [hpr] at hq ⊢
      have hloc : (step (.partyEchoReceive msg) s).local_ msg.receiver =
          { s.local_ msg.receiver with
            acceptedEchoes :=
              insert msg (s.local_ msg.receiver).acceptedEchoes } := by
        simp [step, setLocal]
      rw [hloc] at hq ⊢
      exact h msg.receiver q hq
    · have hloc : (step (.partyEchoReceive msg) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpr]
      rw [hloc] at hq ⊢
      exact h p q hq
  | partyReady r cert =>
    by_cases hpr : p = r
    · subst hpr
      have hloc : (step (.partyReady p cert) s).local_ p =
          { s.local_ p with readySent := insert cert (s.local_ p).readySent } := by
        simp [step, setLocal]
      rw [hloc] at hq ⊢
      exact h p q hq
    · have hloc : (step (.partyReady r cert) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpr]
      rw [hloc] at hq ⊢
      exact h p q hq
  | partyAmplify r cert =>
    by_cases hpr : p = r
    · subst hpr
      have hloc : (step (.partyAmplify p cert) s).local_ p =
          { s.local_ p with readySent := insert cert (s.local_ p).readySent } := by
        simp [step, setLocal]
      rw [hloc] at hq ⊢
      exact h p q hq
    · have hloc : (step (.partyAmplify r cert) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpr]
      rw [hloc] at hq ⊢
      exact h p q hq
  | partyReceiveReady msg =>
    by_cases hpr : p = msg.receiver
    · rw [hpr] at hq ⊢
      have hloc : (step (.partyReceiveReady msg) s).local_ msg.receiver =
          { s.local_ msg.receiver with
            readyReceived :=
              insert msg (s.local_ msg.receiver).readyReceived } := by
        simp [step, setLocal]
      rw [hloc] at hq ⊢
      exact h msg.receiver q hq
    · have hloc : (step (.partyReceiveReady msg) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpr]
      rw [hloc] at hq ⊢
      exact h p q hq
  | partyOutput r cert =>
    by_cases hpr : p = r
    · subst hpr
      have hloc : (step (.partyOutput p cert) s).local_ p =
          { s.local_ p with
            output := some (AVSS.evalRowPoly cert.candidate.rowPoly 0) } := by
        simp [step, setLocal]
      rw [hloc] at hq ⊢
      exact h p q hq
    · have hloc : (step (.partyOutput r cert) s).local_ p = s.local_ p := by
        simp [step, setLocal, hpr]
      rw [hloc] at hq ⊢
      exact h p q hq

end Leslie.Examples.Prob.AVSSFaithful
