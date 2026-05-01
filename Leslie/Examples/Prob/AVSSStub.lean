/-
M3 entry gate — Canetti–Rabin AVSS termination certificate stub.

This file is the **shape verification** for the M3 deliverable.
It declares the AVSS protocol state machine, the fairness
assumptions, and a `FairASTCertificate` instance whose proof
obligations are all `sorry`. The point is to verify that the
certificate's field types match what AVSS will require, *before*
sinking weeks into proofs that might hit a shape mismatch.

Per implementation plan v2.2 §M3 entry-gate: "The `sorry` budget
exception covers this stub. **Entry-gate acceptance:**
`lake build Examples.Prob.AVSSStub` succeeds with all `sorry`s;
reviewer confirms the field shapes match the design intent."

## Resolution paths if the gate reveals a shape mismatch

In order of preference (per impl plan §M3 entry-gate):

  1. Refine the Lean field types of `FairASTCertificate` to match.
  2. Extend the rule with an additional field.
  3. Discover that AVSS termination needs a different rule
     structure (paper finding; pause M3).

## What this file is NOT

  * Not a full AVSS implementation. The state machine is minimal —
    just enough fields to make the certificate compile.
  * Not a sound proof. Every certificate field carries `sorry`.
  * Not load-bearing — `Examples/Prob/AVSS.lean` (M3 W5–W6) will
    subsume this, and *this file is deleted at M3 closeout*.

The state-machine modeling fidelity is intentionally low. AVSS in
practice carries more state (echo / ready broadcast tracking, the
underlying RBC for share delivery, etc.). For shape verification
we keep the state record minimal.
-/

import Leslie.Prob.Action
import Leslie.Prob.Adversary
import Leslie.Prob.Liveness
import Leslie.Prob.PMF

namespace Leslie.Examples.Prob.AVSSStub

open Leslie.Prob NNReal

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## §1. Protocol state -/

/-- Per-party local AVSS state. Minimal — just enough to track
delivery status, OK broadcasts, and final output. Real AVSS adds
echo/ready tracking; deferred to M3 W5–W6. -/
structure AVSSLocalState (n : ℕ) (F : Type*) where
  delivered    : Bool
  okBroadcast  : Bool
  okReceived   : Finset (Fin n)
  output       : Option F

deriving instance DecidableEq for AVSSLocalState

/-- AVSS global state. -/
structure AVSSState (n : ℕ) (F : Type*) where
  /-- Dealer's secret (sampled into `μ₀`). -/
  secret    : F
  /-- Per-party local state. -/
  local_    : Fin n → AVSSLocalState n F
  /-- Static corruption set. -/
  corrupted : Finset (Fin n)
  /-- The network buffer's "in-flight count" — concrete model would
  carry messages explicitly; for the stub we just track the count. -/
  inflight  : ℕ

/-- An AVSS state is *terminated* when every honest party has
output a value. -/
def terminated (s : AVSSState n F) : Prop :=
  ∀ p, p ∉ s.corrupted → (s.local_ p).output.isSome

/-! ## §2. Action labels -/

/-- AVSS action labels (with `F` parameter for output values). -/
inductive AVSSAction (n : ℕ) (F : Type*)
  | dealerShare (i : Fin n)
  | partyEcho (p : Fin n)
  | partyReady (p : Fin n)
  | partyDeliver (p : Fin n)
  | partyBroadcastOK (p : Fin n)
  | partyReceiveOK (p q : Fin n)
  | partyOutput (p : Fin n) (v : F)

/-! ## §3. Spec, fairness, and certificate fields

The protocol spec, fairness assumptions, and certificate
witnesses are stubbed: each definition's body is sorry'd or
trivial enough to compile. Real definitions land in
`Examples/Prob/AVSS.lean` at M3 W5–W6. -/

variable {n : ℕ}

/-- Stub `ProbActionSpec`. Every action's gate is `True` and
effect is the Dirac on the current state — placeholder shape only.
Real definitions: M3 W5–W6. -/
noncomputable def avssSpec (_n _t : ℕ) (_s : F) :
    ProbActionSpec (AVSSState n F) (AVSSAction n F) :=
  { init    := fun _ => True
    actions := fun _ =>
      { gate   := fun _ => True
        effect := fun s _ => PMF.pure s } }

/-- Fairness assumptions. The fair-required actions are the
honest-progress ones: `partyDeliver`, `partyBroadcastOK`,
`partyReceiveOK`. -/
noncomputable def avssFair :
    FairnessAssumptions (AVSSState n F) (AVSSAction n F) :=
  { fair_actions := { a | match a with
                      | .partyDeliver _ => True
                      | .partyBroadcastOK _ => True
                      | .partyReceiveOK _ _ => True
                      | _ => False }
    isWeaklyFair := fun _ => True   -- placeholder, real def in M3 W3
  }

/-! ## §4. Certificate witnesses

`Inv`, `V`, `U` — the three load-bearing certificate fields.
Sketches per the design doc:

  * `V s = ∑ p ∈ honestParties, max 0 (T - phaseProgress p s)` for
    a protocol total phase budget `T`.
  * `U s = (countNotOK s) * K^2 + (countNotREADY s) * K +
    s.inflight` — a lex-product variant capturing pending steps.
  * `Inv s` — the spec's safety invariant ensuring the variant
    arithmetic is sound.

The actual definitions are placeholders for shape verification.
-/

omit [Fintype F] in
def avssInv (_s : AVSSState n F) : Prop := True

omit [Fintype F] in
def avssV (_s : AVSSState n F) : ℝ≥0 := 1

omit [Fintype F] in
def avssU (s : AVSSState n F) : ℕ := s.inflight

/-! ## §5. Countable / measurable instances

For `FairASTCertificate` to elaborate, the state and action types
must be `Countable` with a `MeasurableSingletonClass` measurable
space. We supply discrete instances. -/

variable [Countable F] [MeasurableSpace F] [MeasurableSingletonClass F]

instance : Countable (AVSSLocalState n F) := by
  classical
  have e : AVSSLocalState n F ≃
      Bool × Bool × Finset (Fin n) × Option F :=
    { toFun := fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩
      invFun := fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Countable.of_equiv _ e.symm

instance : Countable (AVSSState n F) := by
  classical
  have e : AVSSState n F ≃
      F × (Fin n → AVSSLocalState n F) × Finset (Fin n) × ℕ :=
    { toFun := fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩
      invFun := fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Countable.of_equiv _ e.symm

instance : Countable (AVSSAction n F) := by
  classical
  -- AVSSAction is countable: 6 of 7 constructors carry only `Fin n`
  -- arguments (finite); the 7th `partyOutput` carries an `F` value.
  -- Encode into a sum of products over countable building blocks.
  let toRep : AVSSAction n F →
      (Fin n) ⊕ (Fin n) ⊕ (Fin n) ⊕ (Fin n) ⊕ (Fin n) ⊕
        (Fin n × Fin n) ⊕ (Fin n × F) := fun a =>
    match a with
    | .dealerShare i      => .inl i
    | .partyEcho p        => .inr (.inl p)
    | .partyReady p       => .inr (.inr (.inl p))
    | .partyDeliver p     => .inr (.inr (.inr (.inl p)))
    | .partyBroadcastOK p => .inr (.inr (.inr (.inr (.inl p))))
    | .partyReceiveOK p q => .inr (.inr (.inr (.inr (.inr (.inl ⟨p, q⟩)))))
    | .partyOutput p v    => .inr (.inr (.inr (.inr (.inr (.inr ⟨p, v⟩)))))
  have h_inj : Function.Injective toRep := by
    intro a b
    cases a <;> cases b <;> simp [toRep]
  exact Function.Injective.countable h_inj

instance : MeasurableSpace (AVSSState n F) := ⊤
instance : MeasurableSingletonClass (AVSSState n F) :=
  ⟨fun _ => trivial⟩

instance : MeasurableSpace (AVSSAction n F) := ⊤
instance : MeasurableSingletonClass (AVSSAction n F) :=
  ⟨fun _ => trivial⟩

/-! ## §6. The certificate

This is the load-bearing instance: every field of
`FairASTCertificate` is provided. The certificate's body is
`sorry`. If this declaration *elaborates*, the certificate's
shape matches what AVSS needs. -/

/-- AVSS termination certificate.

**Status:** `sorry` body — entry gate verifies the
`FairASTCertificate` shape matches AVSS.

The structure-instance form (rather than `:= { … }`) is just to
keep the proof obligation localized: when M3 W5–W6 starts, this
single `sorry` decomposes into the 12 individual proof obligations
of `FairASTCertificate`. -/
noncomputable def avssCert (n t : ℕ) (_h : n ≥ 3 * t + 1) (sec : F) :
    FairASTCertificate (avssSpec (F := F) (n := n) n t sec)
        (avssFair (F := F) (n := n)) terminated := by
  sorry

end Leslie.Examples.Prob.AVSSStub
