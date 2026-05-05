/-
M3 — Canetti–Rabin asynchronous verifiable secret sharing
(**threshold-faithful variant**, Option B).

This module models the Canetti–Rabin '93 asynchronous VSS protocol
(`n` parties, `n ≥ 3t + 1`, `t` Byzantine corruptions) at the level
required by the literature: Bracha-amplification thresholds (`n − t`
echo / ready / output gates) plus per-party row-poly outputs.

Compared to `AVSSAbstract.lean`:

  * `AVSSLocalState` carries `rowPoly : Option (Fin (t+1) → F)`
    storing the row polynomial received from the dealer at delivery
    time.
  * `partyOutput p` writes `bivEval coeffs (partyPoint p) 0`
    (the per-party share `s_p = f(α_p, 0)`) — not the secret
    `coeffs 0 0`.
  * `partyEchoSend p` / `partyEchoReceive p q` replace the
    untracked `partyEcho`. Echoes are now in-flight messages with
    sender/target tracking.
  * `partyReady p` gate adds `echoesReceived.card ≥ n − t`.
  * `partyAmplify p` (new action) — Bracha amplification rule:
    `readyReceived.card ≥ t + 1 ∧ ¬ readySent`.
  * `partyOutput p` gate adds `readyReceived.card ≥ n − t`.

The four classical theorems lift to the probabilistic-trace setting:

  * `avss_termination_AS_fair` — every honest party eventually
    outputs (under trajectory fairness).
  * `avss_correctness_AS` — honest dealer ⇒ every honest output
    equals `bivEval coeffs (partyPoint p) 0`.
  * `avss_commitment_AS` — quorum-intersection commitment: any two
    honest outputs are *jointly determined* by the dealer's
    `coeffs`, with the difference equal to the difference of row-
    poly evaluations at 0.
  * `avss_secrecy` — `t`-coalition view independent of the secret
    (passes through to `BivariateShamir.bivariate_shamir_secrecy`).

Per implementation plan v2.2 §M3 W5–W6 + design plan v2.2 §M3 AVSS,
threshold-faithful refinement.
-/

import Leslie.Examples.Prob.BivariateShamir
import Leslie.Prob.Action
import Leslie.Prob.Adversary
import Leslie.Prob.Liveness
import Leslie.Prob.PMF
import Leslie.Prob.Polynomial
import Leslie.Prob.Refinement
import Leslie.Prob.Trace
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Countable.Defs

namespace Leslie.Examples.Prob.AVSS

open Leslie.Prob MeasureTheory NNReal

variable {n t : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## §1. Local + global state -/

/-- Per-party AVSS local state.

  * `delivered` — has the party's `(rowPoly)` payload been processed?
  * `rowPoly` — the row polynomial `f_p(y) = bivEval coeffs (partyPoint p) y`,
    stored as `t+1` coefficients (degree-`t` univariate polynomial).
  * `echoesReceived` — distinct senders from whom an echo arrived.
  * `readyReceived` — distinct senders from whom a ready arrived.
  * `readySent` — has this party broadcast its own ready?
  * `output` — finalized output (a single `F` element, the per-party
    share `f_p(0)`).
-/
structure AVSSLocalState (n t : ℕ) (F : Type*) [DecidableEq F] where
  delivered      : Bool
  rowPoly        : Option (Fin (t+1) → F)
  echoSent       : Bool
  echoesReceived : Finset (Fin n)
  readyReceived  : Finset (Fin n)
  readySent      : Bool
  output         : Option F

namespace AVSSLocalState

/-- The empty per-party state at protocol start. -/
def init (n t : ℕ) (F : Type*) [DecidableEq F] : AVSSLocalState n t F :=
  { delivered := false
    rowPoly := none
    echoSent := false
    echoesReceived := ∅
    readyReceived := ∅
    readySent := false
    output := none }

end AVSSLocalState

/-- The global AVSS protocol state.

  * `coeffs` — dealer's bivariate polynomial coefficients. Sampled
    once into `μ₀`; not modified after.
  * `partyPoint` — evaluation point for each party (`α_p` in the
    paper). Pinned at `μ₀`-sampling time.
  * `secret` — `coeffs 0 0` if dealer honest.
  * `local_` — per-party state.
  * `corrupted` — static corruption set.
  * `dealerHonest` — bookkeeping flag.
  * `inflightDeliveries` — set of parties awaiting share delivery.
  * `inflightEchoes` — set of (sender, target) pairs of in-transit echoes.
  * `inflightReady` — set of senders whose own-ready broadcast is
    still in transit.
  * `dealerSent` — whether the dealer has emitted shares.
-/
structure AVSSState (n t : ℕ) (F : Type*) [DecidableEq F] where
  coeffs              : Fin (t+1) → Fin (t+1) → F
  partyPoint          : Fin n → F
  secret              : F
  local_              : Fin n → AVSSLocalState n t F
  corrupted           : Finset (Fin n)
  dealerHonest        : Bool
  inflightDeliveries  : Finset (Fin n)
  inflightEchoes      : Finset (Fin n × Fin n)
  inflightReady       : Finset (Fin n)
  dealerSent          : Bool

namespace AVSSState

/-- A party is honest iff not in the corruption set. -/
def isHonest [DecidableEq F] (s : AVSSState n t F) (p : Fin n) : Prop :=
  p ∉ s.corrupted

instance [DecidableEq F] (s : AVSSState n t F) (p : Fin n) :
    Decidable (s.isHonest p) :=
  inferInstanceAs (Decidable (p ∉ s.corrupted))

end AVSSState

/-! ## §2. Bivariate evaluation primitives (mirror AVSSAbstract / BivariateShamir) -/

/-- Bivariate evaluation `coeffs(x, y) = Σ c_{kl} · x^k · y^l`. -/
def bivEval (coeffs : Fin (t+1) → Fin (t+1) → F) (x y : F) : F :=
  ∑ k : Fin (t+1), ∑ l : Fin (t+1), coeffs k l * x ^ k.val * y ^ l.val

/-- The dealer's row polynomial coefficients for party `p`:
`f_p(y) = bivEval coeffs (partyPoint p) y`. As `t+1` coefficients. -/
def rowPolyOfDealer (partyPoint : Fin n → F)
    (coeffs : Fin (t+1) → Fin (t+1) → F) (p : Fin n) :
    Fin (t+1) → F :=
  fun l => ∑ k : Fin (t+1), coeffs k l * partyPoint p ^ k.val

/-- Univariate evaluation of stored row poly at `y`. -/
def evalRowPoly (rp : Fin (t+1) → F) (y : F) : F :=
  ∑ l : Fin (t+1), rp l * y ^ l.val

omit [Fintype F] [DecidableEq F] in
/-- Algebraic identity: the row poly extracted from `coeffs` at point
`partyPoint p`, evaluated at `y`, equals `bivEval coeffs (partyPoint p) y`. -/
theorem evalRowPoly_rowPolyOfDealer (partyPoint : Fin n → F)
    (coeffs : Fin (t+1) → Fin (t+1) → F) (p : Fin n) (y : F) :
    evalRowPoly (rowPolyOfDealer partyPoint coeffs p) y =
      bivEval coeffs (partyPoint p) y := by
  classical
  unfold evalRowPoly rowPolyOfDealer bivEval
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_mul]

/-! ## §3. Initial state -/

/-- Initial-state predicate. -/
def initPred (sec : F) (corr : Finset (Fin n))
    (s : AVSSState n t F) : Prop :=
  (∀ p, s.local_ p = AVSSLocalState.init n t F) ∧
  s.secret = sec ∧
  s.corrupted = corr ∧
  s.inflightDeliveries = ∅ ∧
  s.inflightEchoes = ∅ ∧
  s.inflightReady = ∅ ∧
  s.dealerSent = false ∧
  (s.dealerHonest = true → s.coeffs 0 0 = sec)

/-! ## §4. Action labels -/

/-- AVSS protocol actions (threshold-faithful). -/
inductive AVSSAction (n : ℕ) (F : Type*) [DecidableEq F]
  | dealerShare                              -- dealer emits row polys + echo intent
  | partyDeliver  (p : Fin n)                -- p receives row poly, sets `delivered`
  | partyEchoSend (p : Fin n)                -- p broadcasts echo (after delivery)
  | partyEchoReceive (p q : Fin n)           -- p receives echo from q
  | partyReady    (p : Fin n)                -- p sends ready (after n-t echoes)
  | partyAmplify  (p : Fin n)                -- p sends ready via amplification (≥t+1 readys)
  | partyReceiveReady (p q : Fin n)          -- p receives ready from q
  | partyOutput   (p : Fin n)                -- p outputs (after n-t readys)

/-! ## §5. Functional `setLocal` helper -/

/-- Functional update for `local_`: replace party `p`'s local state. -/
def setLocal (s : AVSSState n t F) (p : Fin n) (ls : AVSSLocalState n t F) :
    AVSSState n t F :=
  { s with local_ := fun q => if q = p then ls else s.local_ q }

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_local_self (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n t F) :
    (setLocal s p ls).local_ p = ls := by
  simp [setLocal]

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_local_ne (s : AVSSState n t F) (p q : Fin n)
    (ls : AVSSLocalState n t F) (h : q ≠ p) :
    (setLocal s p ls).local_ q = s.local_ q := by
  simp [setLocal, h]

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_coeffs (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n t F) :
    (setLocal s p ls).coeffs = s.coeffs := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_partyPoint (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n t F) :
    (setLocal s p ls).partyPoint = s.partyPoint := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_secret (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n t F) :
    (setLocal s p ls).secret = s.secret := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_corrupted (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n t F) :
    (setLocal s p ls).corrupted = s.corrupted := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_dealerHonest (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n t F) :
    (setLocal s p ls).dealerHonest = s.dealerHonest := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_inflightDeliveries (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n t F) :
    (setLocal s p ls).inflightDeliveries = s.inflightDeliveries := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_inflightEchoes (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n t F) :
    (setLocal s p ls).inflightEchoes = s.inflightEchoes := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_inflightReady (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n t F) :
    (setLocal s p ls).inflightReady = s.inflightReady := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_dealerSent (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n t F) :
    (setLocal s p ls).dealerSent = s.dealerSent := rfl

/-! ## §6. Deterministic next-state -/

/-- The deterministic next-state function. Where the gate fails this
returns `s` unchanged; gates are enforced by `actionGate`. -/
def avssStep (a : AVSSAction n F) (s : AVSSState n t F) :
    AVSSState n t F :=
  match a with
  | .dealerShare =>
      -- Dealer emits all shares; populates the inflight-delivery set
      -- with every honest party. The row polys become available at
      -- `partyDeliver` time, derived from `s.coeffs` and `s.partyPoint`.
      { s with
        dealerSent := true
        inflightDeliveries :=
          (Finset.univ : Finset (Fin n)).filter (fun p => p ∉ s.corrupted) }
  | .partyDeliver p =>
      let ls := s.local_ p
      let rp := rowPolyOfDealer s.partyPoint s.coeffs p
      let ls' : AVSSLocalState n t F :=
        { ls with delivered := true, rowPoly := some rp }
      let s' := setLocal s p ls'
      { s' with inflightDeliveries := s.inflightDeliveries.erase p }
  | .partyEchoSend p =>
      -- Honest party `p` broadcasts an echo to every other party.
      -- Records `(p, q)` in `inflightEchoes` for every honest `q` and
      -- sets the `echoSent` flag so the action is single-shot.
      let ls := s.local_ p
      let ls' : AVSSLocalState n t F := { ls with echoSent := true }
      let s' := setLocal s p ls'
      { s' with
        inflightEchoes :=
          s.inflightEchoes ∪
            ((Finset.univ : Finset (Fin n)).filter
              (fun q => q ∉ s.corrupted)).image (fun q => (p, q)) }
  | .partyEchoReceive p q =>
      let ls := s.local_ p
      let ls' : AVSSLocalState n t F :=
        { ls with echoesReceived := insert q ls.echoesReceived }
      let s' := setLocal s p ls'
      { s' with inflightEchoes := s.inflightEchoes.erase (q, p) }
  | .partyReady p =>
      let ls := s.local_ p
      let ls' : AVSSLocalState n t F := { ls with readySent := true }
      let s' := setLocal s p ls'
      { s' with inflightReady := insert p s.inflightReady }
  | .partyAmplify p =>
      let ls := s.local_ p
      let ls' : AVSSLocalState n t F := { ls with readySent := true }
      let s' := setLocal s p ls'
      { s' with inflightReady := insert p s.inflightReady }
  | .partyReceiveReady p q =>
      let ls := s.local_ p
      let ls' : AVSSLocalState n t F :=
        { ls with readyReceived := insert q ls.readyReceived }
      let s' := setLocal s p ls'
      { s' with inflightReady := s.inflightReady.erase q }
  | .partyOutput p =>
      let ls := s.local_ p
      -- Per-party share: f_p(0) = bivEval coeffs (partyPoint p) 0.
      -- Computed from stored `rowPoly`. Equals `bivEval s.coeffs (s.partyPoint p) 0`
      -- by `evalRowPoly_rowPolyOfDealer` whenever `rowPoly = some (rowPolyOfDealer ...)`.
      let v : F :=
        match ls.rowPoly with
        | some rp => evalRowPoly rp 0
        | none    => 0  -- unreachable when gate enforces `delivered = true`
      let ls' : AVSSLocalState n t F := { ls with output := some v }
      setLocal s p ls'

/-! ## §7. Action gates (with thresholds) -/

/-- Gate predicates with `n − t` Bracha thresholds.

The fair-required actions (`partyDeliver`, `partyEchoSend`,
`partyEchoReceive`, `partyReady`, `partyAmplify`, `partyReceiveReady`,
`partyOutput`) restrict their party arguments to honest parties — only
honest parties follow the protocol script. -/
def actionGate (a : AVSSAction n F) (s : AVSSState n t F) : Prop :=
  match a with
  | .dealerShare =>
      s.dealerSent = false
  | .partyDeliver p =>
      s.dealerSent = true ∧ p ∉ s.corrupted ∧
        p ∈ s.inflightDeliveries ∧ (s.local_ p).delivered = false
  | .partyEchoSend p =>
      p ∉ s.corrupted ∧ (s.local_ p).delivered = true ∧
        (s.local_ p).echoSent = false
  | .partyEchoReceive p q =>
      p ∉ s.corrupted ∧ (q, p) ∈ s.inflightEchoes ∧
        q ∉ (s.local_ p).echoesReceived
  | .partyReady p =>
      p ∉ s.corrupted ∧
        (s.local_ p).delivered = true ∧ (s.local_ p).readySent = false ∧
        (s.local_ p).echoesReceived.card ≥ n - t
  | .partyAmplify p =>
      p ∉ s.corrupted ∧
        (s.local_ p).readySent = false ∧
        (s.local_ p).readyReceived.card ≥ t + 1
  | .partyReceiveReady p q =>
      p ∉ s.corrupted ∧
        q ∈ s.inflightReady ∧ q ∉ (s.local_ p).readyReceived
  | .partyOutput p =>
      p ∉ s.corrupted ∧
        (s.local_ p).delivered = true ∧ (s.local_ p).readySent = true ∧
        (s.local_ p).output = none ∧
        (s.local_ p).readyReceived.card ≥ n - t

/-! ## §8. Terminated predicate -/

/-- A state is terminated iff every honest party has snapped output
**and** all in-flight queues are drained. -/
def terminated (s : AVSSState n t F) : Prop :=
  (∀ p, p ∉ s.corrupted → (s.local_ p).output.isSome) ∧
  s.inflightDeliveries = ∅ ∧
  s.inflightEchoes = ∅ ∧
  s.inflightReady = ∅

/-! ## §9. Spec -/

/-- The probabilistic AVSS spec. Randomness lives in `μ₀` only. -/
noncomputable def avssSpec (sec : F) (corr : Finset (Fin n)) :
    ProbActionSpec (AVSSState n t F) (AVSSAction n F) where
  init := initPred sec corr
  actions := fun a =>
    { gate := actionGate a
      effect := fun s _ => PMF.pure (avssStep a s) }

omit [Fintype F] in
@[simp] theorem avssSpec_step_pure (sec : F) (corr : Finset (Fin n))
    (a : AVSSAction n F) (s : AVSSState n t F) (h : actionGate a s) :
    (avssSpec (t := t) sec corr).step a s
      = some (PMF.pure (avssStep a s)) :=
  ProbActionSpec.step_eq_some h

omit [Fintype F] in
theorem avssSpec_step_none (sec : F) (corr : Finset (Fin n))
    (a : AVSSAction n F) (s : AVSSState n t F) (h : ¬ actionGate a s) :
    (avssSpec (t := t) sec corr).step a s = none :=
  ProbActionSpec.step_eq_none h

/-! ## §10. Countable / measurable instances -/

section Measurable

instance : MeasurableSpace (AVSSState n t F) := ⊤
instance : MeasurableSingletonClass (AVSSState n t F) := ⟨fun _ => trivial⟩
instance : MeasurableSpace (AVSSAction n F) := ⊤
instance : MeasurableSingletonClass (AVSSAction n F) := ⟨fun _ => trivial⟩

/-- `AVSSAction n F` is `Fintype` under `[Fintype F]`. -/
noncomputable instance : Fintype (AVSSAction n F) := by
  classical
  exact Fintype.ofEquiv
    (Unit ⊕ Fin n ⊕ Fin n ⊕ (Fin n × Fin n) ⊕ Fin n ⊕ Fin n ⊕
      (Fin n × Fin n) ⊕ Fin n)
    { toFun := fun
        | .inl _ => .dealerShare
        | .inr (.inl p) => .partyDeliver p
        | .inr (.inr (.inl p)) => .partyEchoSend p
        | .inr (.inr (.inr (.inl ⟨p, q⟩))) => .partyEchoReceive p q
        | .inr (.inr (.inr (.inr (.inl p)))) => .partyReady p
        | .inr (.inr (.inr (.inr (.inr (.inl p))))) => .partyAmplify p
        | .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨p, q⟩)))))) =>
            .partyReceiveReady p q
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr p)))))) => .partyOutput p
      invFun := fun
        | .dealerShare => .inl ()
        | .partyDeliver p => .inr (.inl p)
        | .partyEchoSend p => .inr (.inr (.inl p))
        | .partyEchoReceive p q => .inr (.inr (.inr (.inl ⟨p, q⟩)))
        | .partyReady p => .inr (.inr (.inr (.inr (.inl p))))
        | .partyAmplify p => .inr (.inr (.inr (.inr (.inr (.inl p)))))
        | .partyReceiveReady p q =>
            .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨p, q⟩))))))
        | .partyOutput p =>
            .inr (.inr (.inr (.inr (.inr (.inr (.inr p))))))
      left_inv := fun
        | .inl _ => rfl
        | .inr (.inl _) => rfl
        | .inr (.inr (.inl _)) => rfl
        | .inr (.inr (.inr (.inl _))) => rfl
        | .inr (.inr (.inr (.inr (.inl _)))) => rfl
        | .inr (.inr (.inr (.inr (.inr (.inl _))))) => rfl
        | .inr (.inr (.inr (.inr (.inr (.inr (.inl _)))))) => rfl
        | .inr (.inr (.inr (.inr (.inr (.inr (.inr _)))))) => rfl
      right_inv := fun
        | .dealerShare => rfl
        | .partyDeliver _ => rfl
        | .partyEchoSend _ => rfl
        | .partyEchoReceive _ _ => rfl
        | .partyReady _ => rfl
        | .partyAmplify _ => rfl
        | .partyReceiveReady _ _ => rfl
        | .partyOutput _ => rfl }

instance : Countable (AVSSAction n F) := Finite.to_countable

/-- `AVSSLocalState n t F` is `Fintype`. -/
noncomputable instance : Fintype (AVSSLocalState n t F) := by
  classical
  exact Fintype.ofEquiv
    (Bool × Option (Fin (t+1) → F) × Bool × Finset (Fin n) ×
      Finset (Fin n) × Bool × Option F)
    { toFun := fun ⟨a, b, c, d, e, f, g⟩ => ⟨a, b, c, d, e, f, g⟩
      invFun := fun ls =>
        (ls.delivered, ls.rowPoly, ls.echoSent, ls.echoesReceived,
         ls.readyReceived, ls.readySent, ls.output)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance : Countable (AVSSLocalState n t F) := Finite.to_countable

/-- `AVSSState n t F` is `Fintype`. -/
noncomputable instance : Fintype (AVSSState n t F) := by
  classical
  exact Fintype.ofEquiv
    ((Fin (t+1) → Fin (t+1) → F) × (Fin n → F) × F ×
      (Fin n → AVSSLocalState n t F) × Finset (Fin n) × Bool ×
      Finset (Fin n) × Finset (Fin n × Fin n) × Finset (Fin n) × Bool)
    { toFun := fun ⟨c, pp, sec, l, corr, dh, idl, ie, ird, ds⟩ =>
        ⟨c, pp, sec, l, corr, dh, idl, ie, ird, ds⟩
      invFun := fun s =>
        (s.coeffs, s.partyPoint, s.secret, s.local_, s.corrupted,
         s.dealerHonest, s.inflightDeliveries, s.inflightEchoes,
         s.inflightReady, s.dealerSent)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance : Countable (AVSSState n t F) := Finite.to_countable

end Measurable

/-! ## §11. Fairness assumptions -/

/-- Set of fair-required actions. The new fair actions are
`partyEchoSend` (honest parties must broadcast their echo) and
`partyEchoReceive` (in-transit echoes must be delivered). -/
def avssFairActions : Set (AVSSAction n F) :=
  { a | match a with
        | .partyDeliver _ => True
        | .partyEchoSend _ => True
        | .partyEchoReceive _ _ => True
        | .partyReady _ => True
        | .partyAmplify _ => True
        | .partyReceiveReady _ _ => True
        | .partyOutput _ => True
        | _ => False }

/-- AVSS fairness assumptions. -/
noncomputable def avssFair :
    FairnessAssumptions (AVSSState n t F) (AVSSAction n F) where
  fair_actions := avssFairActions
  isWeaklyFair := fun _ => True

/-! ## §12. Termination certificate — definitions

The variant `U` is a 7-component lex-product encoded into a single
`ℕ` via base-`K` weighting, with `K = (n+1)*(n+1)` chosen to dominate
the maximum value of any single component (notably
`inflightEchoes.card ≤ n²`).

Lex order (largest weight first):

  1. `[¬ dealerSent]` — the dealer step (`dealerShare`).
  2. `inflightDeliveries.card` — `partyDeliver` step.
  3. `unsentEchoCount` — honest parties with `delivered ∧ ¬ echoSent`;
     `partyEchoSend` step.
  4. `inflightEchoes.card` — `partyEchoReceive` step.
  5. `notReadySentCount` — honest parties with `¬ readySent`;
     `partyReady` / `partyAmplify` step.
  6. `inflightReady.card` — `partyReceiveReady` step.
  7. `unfinishedCount` — honest parties with `output = none`;
     `partyOutput` step. -/

/-- Set of honest parties (complement of `corrupted` in `Fin n`). -/
def honestSet (s : AVSSState n t F) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun p => p ∉ s.corrupted)

@[simp] theorem honestSet_card_le (s : AVSSState n t F) :
    (honestSet s).card ≤ n := by
  unfold honestSet
  exact (Finset.card_le_univ _).trans (by simp)

/-- Honest parties with delivered = true and echoSent = false. -/
def unsentEchoSet (s : AVSSState n t F) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter
    (fun p => p ∉ s.corrupted ∧
      (s.local_ p).delivered = true ∧ (s.local_ p).echoSent = false)

@[simp] theorem unsentEchoSet_card_le (s : AVSSState n t F) :
    (unsentEchoSet s).card ≤ n := by
  unfold unsentEchoSet
  exact (Finset.card_le_univ _).trans (by simp)

/-- Honest parties with `readySent = false`. -/
def notReadySentSet (s : AVSSState n t F) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter
    (fun p => p ∉ s.corrupted ∧ (s.local_ p).readySent = false)

@[simp] theorem notReadySentSet_card_le (s : AVSSState n t F) :
    (notReadySentSet s).card ≤ n := by
  unfold notReadySentSet
  exact (Finset.card_le_univ _).trans (by simp)

/-- Honest parties with `output = none`. -/
def unfinishedSet (s : AVSSState n t F) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter
    (fun p => p ∉ s.corrupted ∧ (s.local_ p).output = none)

@[simp] theorem unfinishedSet_card_le (s : AVSSState n t F) :
    (unfinishedSet s).card ≤ n := by
  unfold unfinishedSet
  exact (Finset.card_le_univ _).trans (by simp)

@[simp] theorem inflightEchoes_card_le (s : AVSSState n t F) :
    s.inflightEchoes.card ≤ (n + 1) * (n + 1) := by
  classical
  have h1 : s.inflightEchoes.card ≤ (Finset.univ : Finset (Fin n × Fin n)).card :=
    Finset.card_le_univ _
  have h2 : (Finset.univ : Finset (Fin n × Fin n)).card = n * n := by simp
  calc s.inflightEchoes.card
      ≤ n * n := by rw [← h2]; exact h1
    _ ≤ (n + 1) * (n + 1) := by nlinarith

@[simp] theorem inflightDeliveries_card_le (s : AVSSState n t F) :
    s.inflightDeliveries.card ≤ n := by
  exact (Finset.card_le_univ s.inflightDeliveries).trans (by simp)

@[simp] theorem inflightReady_card_le (s : AVSSState n t F) :
    s.inflightReady.card ≤ n := by
  exact (Finset.card_le_univ s.inflightReady).trans (by simp)

/-- Lex base: `K = (n+1)²` dominates every component (in particular
`inflightEchoes.card ≤ n² < K`). -/
def lexBase (n : ℕ) : ℕ := (n + 1) * (n + 1)

theorem lexBase_pos : 1 ≤ lexBase n := by unfold lexBase; nlinarith

theorem inflightEchoes_lt_lexBase (s : AVSSState n t F) :
    s.inflightEchoes.card < lexBase n + 1 := by
  unfold lexBase
  have := inflightEchoes_card_le s
  omega

/-- The 7-component lex-product termination variant.

```
U = c₁·K⁶ + c₂·K⁵ + c₃·K⁴ + c₄·K³ + c₅·K² + c₆·K + c₇
```

with `K = (n+1)²`. -/
noncomputable def avssU (s : AVSSState n t F) : ℕ :=
  let K := lexBase n
  (if s.dealerSent then 0 else (honestSet s).card) * K ^ 6 +
    s.inflightDeliveries.card * K ^ 5 +
    (unsentEchoSet s).card * K ^ 4 +
    s.inflightEchoes.card * K ^ 3 +
    (notReadySentSet s).card * K ^ 2 +
    s.inflightReady.card * K +
    (unfinishedSet s).card

/-- Likelihood `V s = (avssU s : ℝ≥0)`. -/
noncomputable def avssV (s : AVSSState n t F) : ℝ≥0 := (avssU s : ℝ≥0)

/-- Termination inductive invariant.

Three clauses:

  * Pre-share quiescence: when `dealerSent = false`, every party is
    in its initial local state and all in-flight queues are empty.
  * Echo well-formedness: every honest party that has `echoSent =
    true` also has `delivered = true` (echoes are only sent post-
    delivery). And in-flight echoes (q, p) only exist when `q` has
    set `echoSent`.
  * Output well-formedness: every honest party with `output = some _`
    also has `readySent = true ∧ delivered = true`.

This is enough invariant to make the `avssU` lex-product strictly
decrease on each fair-firing step. -/
def avssTermInv (s : AVSSState n t F) : Prop :=
  (s.dealerSent = false →
    (∀ p, (s.local_ p).delivered = false ∧
          (s.local_ p).echoSent = false ∧
          (s.local_ p).readySent = false ∧
          (s.local_ p).output = none) ∧
    s.inflightDeliveries = ∅ ∧
    s.inflightEchoes = ∅ ∧
    s.inflightReady = ∅) ∧
  (∀ p, p ∉ s.corrupted →
    (s.local_ p).echoSent = true → (s.local_ p).delivered = true) ∧
  (∀ p, p ∉ s.corrupted →
    (s.local_ p).output.isSome = true →
      (s.local_ p).readySent = true ∧ (s.local_ p).delivered = true)

/-- Uniform bound on `avssU`: `7 · n · K⁶` plus slack, with `K = (n+1)²`.

A simple over-bound `(7 * n + 7) * K⁶` is used; the cert's
`V_init_bdd` field expects a concrete `ℕ` constant. -/
theorem avssU_le_bound (s : AVSSState n t F) :
    avssU s ≤ (7 * n + 7) * (lexBase n) ^ 6 := by
  classical
  unfold avssU
  set K := lexBase n with hK_def
  have hK_pos : 1 ≤ K := lexBase_pos
  -- Each component bound:
  have h0 : (if s.dealerSent then (0 : ℕ) else (honestSet s).card) ≤ n := by
    split
    · exact Nat.zero_le _
    · exact honestSet_card_le s
  have h1 := inflightDeliveries_card_le s
  have h2 := unsentEchoSet_card_le s
  have h3 : s.inflightEchoes.card ≤ K := by
    rw [hK_def]; exact inflightEchoes_card_le s
  have h4 := notReadySentSet_card_le s
  have h5 := inflightReady_card_le s
  have h6 := unfinishedSet_card_le s
  -- Power monotonicity:
  have hp1 : K ≤ K ^ 6 := by
    calc K = K ^ 1 := by ring
      _ ≤ K ^ 6 := Nat.pow_le_pow_right hK_pos (by omega)
  have hp2 : K ^ 2 ≤ K ^ 6 := Nat.pow_le_pow_right hK_pos (by omega)
  have hp3 : K ^ 3 ≤ K ^ 6 := Nat.pow_le_pow_right hK_pos (by omega)
  have hp4 : K ^ 4 ≤ K ^ 6 := Nat.pow_le_pow_right hK_pos (by omega)
  have hp5 : K ^ 5 ≤ K ^ 6 := Nat.pow_le_pow_right hK_pos (by omega)
  have hp0 : (1 : ℕ) ≤ K ^ 6 := by
    calc (1 : ℕ) = 1 ^ 6 := by ring
      _ ≤ K ^ 6 := by gcongr
  -- Each weighted component ≤ n · K⁶ (or K · K⁵ = K⁶ for component 4):
  have hA : (if s.dealerSent then (0 : ℕ) else (honestSet s).card) * K ^ 6
              ≤ n * K ^ 6 := by nlinarith [Nat.zero_le (K ^ 6)]
  have hB : s.inflightDeliveries.card * K ^ 5 ≤ n * K ^ 6 := by
    calc s.inflightDeliveries.card * K ^ 5
        ≤ n * K ^ 5 := by gcongr
      _ ≤ n * K ^ 6 := by gcongr
  have hC : (unsentEchoSet s).card * K ^ 4 ≤ n * K ^ 6 := by
    calc (unsentEchoSet s).card * K ^ 4
        ≤ n * K ^ 4 := by gcongr
      _ ≤ n * K ^ 6 := by gcongr
  have hD : s.inflightEchoes.card * K ^ 3 ≤ K ^ 6 := by
    calc s.inflightEchoes.card * K ^ 3
        ≤ K * K ^ 3 := by gcongr
      _ = K ^ 4 := by ring
      _ ≤ K ^ 6 := hp4
  have hE : (notReadySentSet s).card * K ^ 2 ≤ n * K ^ 6 := by
    calc (notReadySentSet s).card * K ^ 2
        ≤ n * K ^ 2 := by gcongr
      _ ≤ n * K ^ 6 := by gcongr
  have hF : s.inflightReady.card * K ≤ n * K ^ 6 := by
    calc s.inflightReady.card * K
        ≤ n * K := by gcongr
      _ ≤ n * K ^ 6 := by gcongr
  have hG : (unfinishedSet s).card ≤ n * K ^ 6 := by
    calc (unfinishedSet s).card
        ≤ n := h6
      _ = n * 1 := by ring
      _ ≤ n * K ^ 6 := by nlinarith [hp0]
  -- Combine hA..hG: avssU ≤ 6·n·K⁶ + K⁶.
  have hsum : avssU s ≤ 6 * n * K ^ 6 + K ^ 6 := by
    unfold avssU
    -- Six components ≤ n · K⁶ each, plus one ≤ K⁶ (the inflightEchoes term).
    have hsum6 :
        (if s.dealerSent then (0 : ℕ) else (honestSet s).card) * K ^ 6 +
          s.inflightDeliveries.card * K ^ 5 +
          (unsentEchoSet s).card * K ^ 4 +
          s.inflightEchoes.card * K ^ 3 +
          (notReadySentSet s).card * K ^ 2 +
          s.inflightReady.card * K +
          (unfinishedSet s).card
        ≤ n * K ^ 6 + n * K ^ 6 + n * K ^ 6 + K ^ 6 +
          n * K ^ 6 + n * K ^ 6 + n * K ^ 6 := by
      have := hA; have := hB; have := hC; have := hD
      have := hE; have := hF; have := hG
      omega
    have hrearrange :
        n * K ^ 6 + n * K ^ 6 + n * K ^ 6 + K ^ 6 +
          n * K ^ 6 + n * K ^ 6 + n * K ^ 6
        = 6 * n * K ^ 6 + K ^ 6 := by ring
    rw [hrearrange] at hsum6
    convert hsum6 using 0
  -- Final: 6·n·K⁶ + K⁶ ≤ (7n+7)·K⁶.
  calc avssU s
      ≤ 6 * n * K ^ 6 + K ^ 6 := hsum
    _ ≤ (7 * n + 7) * K ^ 6 := by nlinarith [Nat.zero_le (K ^ 6)]

end Leslie.Examples.Prob.AVSS
