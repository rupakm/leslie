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
**and** echoed, **and** all in-flight queues are drained. The
`echoSent = true` requirement ensures the variant `avssU` reaches
`0` at terminated states — without it an honest party could output
via `partyAmplify` (which only requires `readyReceived ≥ t + 1`)
without ever echoing, leaving `unsentEchoSet` nonempty. -/
def terminated (s : AVSSState n t F) : Prop :=
  (∀ p, p ∉ s.corrupted → (s.local_ p).output.isSome) ∧
  (∀ p, p ∉ s.corrupted → (s.local_ p).echoSent = true) ∧
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
    in its initial local state (all 7 fields = `AVSSLocalState.init`)
    and all three in-flight queues are empty. The full-init form is
    needed to rule out `partyAmplify`'s `readyReceived.card ≥ t + 1`
    gate: if pre-state has `dealerSent = false`, then any honest
    party's `readyReceived` is `∅`, so the gate is infeasible.
  * Echo well-formedness: every honest party that has `echoSent =
    true` also has `delivered = true` (echoes are only sent post-
    delivery).
  * Output well-formedness: every honest party with `output = some _`
    also has `readySent = true ∧ delivered = true`.

This is enough invariant to make the `avssU` lex-product strictly
decrease on each fair-firing step. -/
def avssTermInv (s : AVSSState n t F) : Prop :=
  (s.dealerSent = false →
    (∀ p, s.local_ p = AVSSLocalState.init n t F) ∧
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

/-! ### Inductive invariant — step preservation (Phase 2b) -/

omit [Fintype F] in
/-- `avssTermInv` is preserved by every gated action.

For clause 1 (`dealerSent = false → quiescence`): every action either
flips `dealerSent` to `true` (`dealerShare`) or has its gate falsified
by the strengthened pre-share clause (`s.local_ p = init` plus empty
in-flight queues). The new `partyAmplify` action would otherwise
threaten the invariant — its `readyReceived.card ≥ t + 1` gate is
ruled out because `init.readyReceived = ∅`.

For clauses 2 (`echoSent → delivered`) and 3 (`output.isSome →
readySent ∧ delivered`): the only actions that can establish either
antecedent are `partyEchoSend` and `partyOutput`, whose gates already
guarantee the consequent. Other actions either don't touch the
relevant fields or don't shift them in a problematic direction. -/
theorem avssTermInv_step
    (a : AVSSAction n F) (s : AVSSState n t F)
    (h : actionGate a s) (hinv : avssTermInv s)
    (s' : AVSSState n t F)
    (hs' : s' ∈ (PMF.pure (avssStep a s)).support) :
    avssTermInv s' := by
  classical
  -- Pure step: `s' = avssStep a s`.
  have hs_eq : s' = avssStep a s := by
    have hsupp : (PMF.pure (avssStep a s)).support = {avssStep a s} :=
      PMF.support_pure _
    rw [hsupp] at hs'
    simpa using hs'
  subst hs_eq
  obtain ⟨hpre, hecho, hout⟩ := hinv
  refine ⟨?_, ?_, ?_⟩
  -- ===== Clause 1: dealerSent post = false → all-init + queues empty post =====
  · intro hds'
    cases a with
    | dealerShare =>
        simp [avssStep] at hds'
    | partyDeliver p =>
        have hpre_ds : s.dealerSent = true := h.1
        simp [avssStep, setLocal] at hds'
        rw [hpre_ds] at hds'
        cases hds'
    | partyEchoSend p =>
        have hpre_ds : s.dealerSent = false := by
          simpa [avssStep, setLocal] using hds'
        have hi := hpre hpre_ds
        have hp_init : s.local_ p = AVSSLocalState.init n t F := hi.1 p
        have hgate_del : (s.local_ p).delivered = true := h.2.1
        rw [hp_init] at hgate_del
        simp [AVSSLocalState.init] at hgate_del
    | partyEchoReceive p q =>
        have hpre_ds : s.dealerSent = false := by
          simpa [avssStep, setLocal] using hds'
        have hi := hpre hpre_ds
        have hgate_in : (q, p) ∈ s.inflightEchoes := h.2.1
        rw [hi.2.2.1] at hgate_in
        exact absurd hgate_in (Finset.notMem_empty _)
    | partyReady p =>
        have hpre_ds : s.dealerSent = false := by
          simpa [avssStep, setLocal] using hds'
        have hi := hpre hpre_ds
        have hp_init : s.local_ p = AVSSLocalState.init n t F := hi.1 p
        have hgate_del : (s.local_ p).delivered = true := h.2.1
        rw [hp_init] at hgate_del
        simp [AVSSLocalState.init] at hgate_del
    | partyAmplify p =>
        have hpre_ds : s.dealerSent = false := by
          simpa [avssStep, setLocal] using hds'
        have hi := hpre hpre_ds
        have hp_init : s.local_ p = AVSSLocalState.init n t F := hi.1 p
        have hgate_rr : (s.local_ p).readyReceived.card ≥ t + 1 := h.2.2
        rw [hp_init] at hgate_rr
        simp [AVSSLocalState.init] at hgate_rr
    | partyReceiveReady p q =>
        have hpre_ds : s.dealerSent = false := by
          simpa [avssStep, setLocal] using hds'
        have hi := hpre hpre_ds
        have hgate_in : q ∈ s.inflightReady := h.2.1
        rw [hi.2.2.2] at hgate_in
        exact absurd hgate_in (Finset.notMem_empty _)
    | partyOutput p =>
        have hpre_ds : s.dealerSent = false := by
          simpa [avssStep, setLocal] using hds'
        have hi := hpre hpre_ds
        have hp_init : s.local_ p = AVSSLocalState.init n t F := hi.1 p
        have hgate_del : (s.local_ p).delivered = true := h.2.1
        rw [hp_init] at hgate_del
        simp [AVSSLocalState.init] at hgate_del
  -- ===== Clause 2: ∀ honest p, echoSent post = true → delivered post = true =====
  · intro p hp hes
    cases a with
    | dealerShare =>
        -- `dealerShare` doesn't touch any party's local state.
        simp only [avssStep] at hes ⊢
        exact hecho p hp hes
    | partyDeliver q =>
        simp only [avssStep] at hes ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hes ⊢
        -- Goal closed by `rw`: post `delivered := true` is rfl.
        · rw [setLocal_local_ne _ _ _ _ hpq] at hes ⊢
          exact hecho p hp hes
    | partyEchoSend q =>
        simp only [avssStep] at hes ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hes ⊢
          -- Post echoSent = true (set), post delivered = pre delivered.
          -- Gate: pre delivered = true (= h.2.1).
          simp
          exact h.2.1
        · rw [setLocal_local_ne _ _ _ _ hpq] at hes ⊢
          exact hecho p hp hes
    | partyEchoReceive q r =>
        simp only [avssStep] at hes ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hes ⊢
          simp at hes ⊢
          exact hecho p hp hes
        · rw [setLocal_local_ne _ _ _ _ hpq] at hes ⊢
          exact hecho p hp hes
    | partyReady q =>
        simp only [avssStep] at hes ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hes ⊢
          simp at hes ⊢
          exact hecho p hp hes
        · rw [setLocal_local_ne _ _ _ _ hpq] at hes ⊢
          exact hecho p hp hes
    | partyAmplify q =>
        simp only [avssStep] at hes ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hes ⊢
          simp at hes ⊢
          exact hecho p hp hes
        · rw [setLocal_local_ne _ _ _ _ hpq] at hes ⊢
          exact hecho p hp hes
    | partyReceiveReady q r =>
        simp only [avssStep] at hes ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hes ⊢
          simp at hes ⊢
          exact hecho p hp hes
        · rw [setLocal_local_ne _ _ _ _ hpq] at hes ⊢
          exact hecho p hp hes
    | partyOutput q =>
        simp only [avssStep] at hes ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hes ⊢
          simp at hes ⊢
          exact hecho p hp hes
        · rw [setLocal_local_ne _ _ _ _ hpq] at hes ⊢
          exact hecho p hp hes
  -- ===== Clause 3: ∀ honest p, output.isSome = true → readySent ∧ delivered =====
  · intro p hp hsome
    cases a with
    | dealerShare =>
        simp only [avssStep] at hsome ⊢
        exact hout p hp hsome
    | partyDeliver q =>
        simp only [avssStep] at hsome ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hsome ⊢
          -- Post sets delivered := true, output unchanged.
          -- After simp: goal becomes `(s.local_ p).readySent = true`.
          simp at hsome ⊢
          exact (hout p hp hsome).1
        · rw [setLocal_local_ne _ _ _ _ hpq] at hsome ⊢
          exact hout p hp hsome
    | partyEchoSend q =>
        simp only [avssStep] at hsome ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hsome ⊢
          simp at hsome ⊢
          exact hout p hp hsome
        · rw [setLocal_local_ne _ _ _ _ hpq] at hsome ⊢
          exact hout p hp hsome
    | partyEchoReceive q r =>
        simp only [avssStep] at hsome ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hsome ⊢
          simp at hsome ⊢
          exact hout p hp hsome
        · rw [setLocal_local_ne _ _ _ _ hpq] at hsome ⊢
          exact hout p hp hsome
    | partyReady q =>
        simp only [avssStep] at hsome ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hsome ⊢
          -- Post sets readySent := true; output unchanged.
          -- After simp: goal becomes `(s.local_ p).delivered = true`.
          simp at hsome ⊢
          exact (hout p hp hsome).2
        · rw [setLocal_local_ne _ _ _ _ hpq] at hsome ⊢
          exact hout p hp hsome
    | partyAmplify q =>
        simp only [avssStep] at hsome ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hsome ⊢
          -- Same shape as partyReady: post readySent := true.
          simp at hsome ⊢
          exact (hout p hp hsome).2
        · rw [setLocal_local_ne _ _ _ _ hpq] at hsome ⊢
          exact hout p hp hsome
    | partyReceiveReady q r =>
        simp only [avssStep] at hsome ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hsome ⊢
          simp at hsome ⊢
          exact hout p hp hsome
        · rw [setLocal_local_ne _ _ _ _ hpq] at hsome ⊢
          exact hout p hp hsome
    | partyOutput q =>
        simp only [avssStep] at hsome ⊢
        by_cases hpq : p = q
        · subst hpq
          rw [setLocal_local_self] at hsome ⊢
          -- Post output := some _, readySent and delivered unchanged.
          -- Gate: pre readySent = true ∧ pre delivered = true.
          simp
          exact ⟨h.2.2.1, h.2.1⟩
        · rw [setLocal_local_ne _ _ _ _ hpq] at hsome ⊢
          exact hout p hp hsome
/-! ### Variant strict-decrease per fair action (Phase 2c)

Each fair action decreases `avssU` by at least 1 under the inductive
invariant. The lex weighting (`K = (n+1)²`) is chosen so each component's
weighted contribution dominates the next component's max increase. -/

omit [Fintype F] in
/-- Helper: under `avssTermInv s` and any positive `Fin n` cardinality
witness in a queue or local field, the dealer must have shared. -/
private theorem dealerSent_true_of_inflight
    {s : AVSSState n t F} (hinv : avssTermInv s)
    (h : s.inflightDeliveries ≠ ∅ ∨ s.inflightEchoes ≠ ∅ ∨ s.inflightReady ≠ ∅) :
    s.dealerSent = true := by
  by_contra hbad
  have hf : s.dealerSent = false := by
    cases h_ds : s.dealerSent with
    | true => exact absurd h_ds hbad
    | false => rfl
  have hi := hinv.1 hf
  rcases h with h₁ | h₂ | h₃
  · exact h₁ hi.2.1
  · exact h₂ hi.2.2.1
  · exact h₃ hi.2.2.2

omit [Fintype F] in
/-- Helper: under `avssTermInv s`, if any honest party has a non-init
local state, the dealer must have shared. -/
private theorem dealerSent_true_of_local
    {s : AVSSState n t F} (hinv : avssTermInv s) {p : Fin n}
    (h : s.local_ p ≠ AVSSLocalState.init n t F) :
    s.dealerSent = true := by
  by_contra hbad
  have hf : s.dealerSent = false := by
    cases h_ds : s.dealerSent with
    | true => exact absurd h_ds hbad
    | false => rfl
  exact h ((hinv.1 hf).1 p)

omit [Fintype F] in
/-- `partyOutput` step: avssU strictly decreases by 1.
The only changed component is `unfinishedSet.card` (decreases by 1). -/
theorem avssU_step_partyOutput_lt (s : AVSSState n t F) (p : Fin n)
    (hgate : actionGate (AVSSAction.partyOutput p) s)
    (hinv : avssTermInv s) :
    avssU (avssStep (AVSSAction.partyOutput p) s) + 1 ≤ avssU s := by
  classical
  obtain ⟨hphon, hdel_t, _, hout_none, _⟩ := hgate
  have hds_pre : s.dealerSent = true := by
    apply dealerSent_true_of_local hinv (p := p)
    intro hp
    rw [hp] at hdel_t
    simp [AVSSLocalState.init] at hdel_t
  -- Frame.
  have hds : (avssStep (AVSSAction.partyOutput p) s).dealerSent =
      s.dealerSent := by simp [avssStep, setLocal]
  have hcorr : (avssStep (AVSSAction.partyOutput p) s).corrupted =
      s.corrupted := by simp [avssStep, setLocal]
  have hifd : (avssStep (AVSSAction.partyOutput p) s).inflightDeliveries =
      s.inflightDeliveries := by simp [avssStep]
  have hifr : (avssStep (AVSSAction.partyOutput p) s).inflightReady =
      s.inflightReady := by simp [avssStep]
  have hife : (avssStep (AVSSAction.partyOutput p) s).inflightEchoes =
      s.inflightEchoes := by simp [avssStep]
  -- Per-party: only output_p flips none → some _.
  have hdel : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyOutput p) s).local_ x).delivered =
        (s.local_ x).delivered := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hes : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyOutput p) s).local_ x).echoSent =
        (s.local_ x).echoSent := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hrs : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyOutput p) s).local_ x).readySent =
        (s.local_ x).readySent := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hout_p_some :
      ((avssStep (AVSSAction.partyOutput p) s).local_ p).output ≠ none := by
    simp [avssStep]
  have hout_ne : ∀ x : Fin n, x ≠ p →
      ((avssStep (AVSSAction.partyOutput p) s).local_ x).output =
        (s.local_ x).output := by
    intro x hxp
    simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  -- Set equalities.
  have hH : honestSet (avssStep (AVSSAction.partyOutput p) s) =
      honestSet s := by
    apply Finset.ext; intro x
    simp only [honestSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr]
  have huss : unsentEchoSet (avssStep (AVSSAction.partyOutput p) s) =
      unsentEchoSet s := by
    apply Finset.ext; intro x
    simp only [unsentEchoSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hdel x, hes x]
  have hnrs : notReadySentSet (avssStep (AVSSAction.partyOutput p) s) =
      notReadySentSet s := by
    apply Finset.ext; intro x
    simp only [notReadySentSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hrs x]
  -- unfinishedSet post = unfinishedSet pre.erase p.
  have hp_in_unfin : p ∈ unfinishedSet s := by
    simp only [unfinishedSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hphon, hout_none⟩
  have hunfin_post : unfinishedSet (avssStep (AVSSAction.partyOutput p) s) =
      (unfinishedSet s).erase p := by
    apply Finset.ext; intro x
    simp only [unfinishedSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    rw [hcorr]
    by_cases hxp : x = p
    · subst hxp
      simp [hout_p_some]
    · rw [hout_ne x hxp]
      simp [hxp]
  have hunfin_card :
      (unfinishedSet (avssStep (AVSSAction.partyOutput p) s)).card =
      (unfinishedSet s).card - 1 := by
    rw [hunfin_post, Finset.card_erase_of_mem hp_in_unfin]
  have hunfin_pos : 1 ≤ (unfinishedSet s).card :=
    Finset.card_pos.mpr ⟨p, hp_in_unfin⟩
  unfold avssU
  rw [hds, hifd, hife, hifr, huss, hnrs, hunfin_card, hds_pre]
  simp only [if_true, zero_mul, Nat.zero_add]
  omega

omit [Fintype F] in
/-- `partyReceiveReady` step: avssU strictly decreases by `K`. -/
theorem avssU_step_partyReceiveReady_lt (s : AVSSState n t F) (p q : Fin n)
    (hgate : actionGate (AVSSAction.partyReceiveReady p q) s)
    (hinv : avssTermInv s) :
    avssU (avssStep (AVSSAction.partyReceiveReady p q) s) + 1 ≤ avssU s := by
  classical
  obtain ⟨_, hqin, _⟩ := hgate
  have hds_pre : s.dealerSent = true :=
    dealerSent_true_of_inflight hinv
      (Or.inr (Or.inr (fun heq => by rw [heq] at hqin
                                     exact absurd hqin (Finset.notMem_empty _))))
  -- Frame.
  have hds : (avssStep (AVSSAction.partyReceiveReady p q) s).dealerSent =
      s.dealerSent := by simp [avssStep, setLocal]
  have hcorr : (avssStep (AVSSAction.partyReceiveReady p q) s).corrupted =
      s.corrupted := by simp [avssStep, setLocal]
  have hifd : (avssStep (AVSSAction.partyReceiveReady p q) s).inflightDeliveries =
      s.inflightDeliveries := by simp [avssStep]
  have hife : (avssStep (AVSSAction.partyReceiveReady p q) s).inflightEchoes =
      s.inflightEchoes := by simp [avssStep]
  have hifr : (avssStep (AVSSAction.partyReceiveReady p q) s).inflightReady =
      s.inflightReady.erase q := by simp [avssStep]
  -- Per-party: only readyReceived_p changes (not in U).
  have hdel : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyReceiveReady p q) s).local_ x).delivered =
        (s.local_ x).delivered := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hes : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyReceiveReady p q) s).local_ x).echoSent =
        (s.local_ x).echoSent := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hrs : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyReceiveReady p q) s).local_ x).readySent =
        (s.local_ x).readySent := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hout : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyReceiveReady p q) s).local_ x).output =
        (s.local_ x).output := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  -- Set equalities.
  have huss : unsentEchoSet (avssStep (AVSSAction.partyReceiveReady p q) s) =
      unsentEchoSet s := by
    apply Finset.ext; intro x
    simp only [unsentEchoSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hdel x, hes x]
  have hnrs : notReadySentSet (avssStep (AVSSAction.partyReceiveReady p q) s) =
      notReadySentSet s := by
    apply Finset.ext; intro x
    simp only [notReadySentSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hrs x]
  have hunfin : unfinishedSet (avssStep (AVSSAction.partyReceiveReady p q) s) =
      unfinishedSet s := by
    apply Finset.ext; intro x
    simp only [unfinishedSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hout x]
  have hifr_card :
      (s.inflightReady.erase q).card = s.inflightReady.card - 1 :=
    Finset.card_erase_of_mem hqin
  have hifr_pos : 1 ≤ s.inflightReady.card :=
    Finset.card_pos.mpr ⟨q, hqin⟩
  have hK_pos : 1 ≤ lexBase n := lexBase_pos
  unfold avssU
  rw [hds, hifd, hife, hifr, huss, hnrs, hunfin, hifr_card, hds_pre]
  simp only [if_true, zero_mul, Nat.zero_add]
  -- Goal: ifd*K^5 + uss*K^4 + ife*K^3 + nrs*K^2 + (ifr-1)*K + unfin + 1
  --     ≤ ifd*K^5 + uss*K^4 + ife*K^3 + nrs*K^2 + ifr*K + unfin
  -- ⟺ (ifr - 1)*K + 1 ≤ ifr*K, given ifr ≥ 1.
  have h_split : (s.inflightReady.card - 1) * lexBase n + lexBase n =
      s.inflightReady.card * lexBase n := by
    have : s.inflightReady.card - 1 + 1 = s.inflightReady.card :=
      Nat.sub_add_cancel hifr_pos
    calc (s.inflightReady.card - 1) * lexBase n + lexBase n
        = ((s.inflightReady.card - 1) + 1) * lexBase n := by ring
      _ = s.inflightReady.card * lexBase n := by rw [this]
  nlinarith [h_split, hK_pos]

omit [Fintype F] in
/-- `partyReady` step: avssU strictly decreases.  c5 (notReadySent) drops
by 1 (loses K²); c6 (inflightReady) gains at most 1 (gains K). Net ≥ K(K-1)
which is ≥ 1 for K ≥ 2 (i.e., n ≥ 1, which holds since `p : Fin n`). -/
theorem avssU_step_partyReady_lt (s : AVSSState n t F) (p : Fin n)
    (hgate : actionGate (AVSSAction.partyReady p) s)
    (hinv : avssTermInv s) :
    avssU (avssStep (AVSSAction.partyReady p) s) + 1 ≤ avssU s := by
  classical
  obtain ⟨hphon, hdel_t, hrsf, _⟩ := hgate
  have hds_pre : s.dealerSent = true := by
    apply dealerSent_true_of_local hinv (p := p)
    intro hp
    rw [hp] at hdel_t
    simp [AVSSLocalState.init] at hdel_t
  -- n ≥ 1 from p : Fin n.
  have hn_pos : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; exact p.elim0
    · exact hn
  have hK_ge : 4 ≤ lexBase n := by unfold lexBase; nlinarith
  -- Frame.
  have hds : (avssStep (AVSSAction.partyReady p) s).dealerSent =
      s.dealerSent := by simp [avssStep, setLocal]
  have hcorr : (avssStep (AVSSAction.partyReady p) s).corrupted =
      s.corrupted := by simp [avssStep, setLocal]
  have hifd : (avssStep (AVSSAction.partyReady p) s).inflightDeliveries =
      s.inflightDeliveries := by simp [avssStep]
  have hife : (avssStep (AVSSAction.partyReady p) s).inflightEchoes =
      s.inflightEchoes := by simp [avssStep]
  have hifr : (avssStep (AVSSAction.partyReady p) s).inflightReady =
      insert p s.inflightReady := by simp [avssStep]
  -- Per-party: only readySent_p flips false → true.
  have hdel : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyReady p) s).local_ x).delivered =
        (s.local_ x).delivered := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hes : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyReady p) s).local_ x).echoSent =
        (s.local_ x).echoSent := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hrs_p : ((avssStep (AVSSAction.partyReady p) s).local_ p).readySent = true := by
    simp [avssStep]
  have hrs_ne : ∀ x : Fin n, x ≠ p →
      ((avssStep (AVSSAction.partyReady p) s).local_ x).readySent =
        (s.local_ x).readySent := by
    intro x hxp
    simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hout : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyReady p) s).local_ x).output =
        (s.local_ x).output := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  -- Set equalities.
  have huss : unsentEchoSet (avssStep (AVSSAction.partyReady p) s) =
      unsentEchoSet s := by
    apply Finset.ext; intro x
    simp only [unsentEchoSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hdel x, hes x]
  have hunfin : unfinishedSet (avssStep (AVSSAction.partyReady p) s) =
      unfinishedSet s := by
    apply Finset.ext; intro x
    simp only [unfinishedSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hout x]
  -- notReadySent post = pre.erase p.
  have hp_in_nrs : p ∈ notReadySentSet s := by
    simp only [notReadySentSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hphon, hrsf⟩
  have hnrs_post : notReadySentSet (avssStep (AVSSAction.partyReady p) s) =
      (notReadySentSet s).erase p := by
    apply Finset.ext; intro x
    simp only [notReadySentSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    rw [hcorr]
    by_cases hxp : x = p
    · subst hxp; simp [hrs_p]
    · rw [hrs_ne x hxp]; simp [hxp]
  have hnrs_card :
      (notReadySentSet (avssStep (AVSSAction.partyReady p) s)).card =
      (notReadySentSet s).card - 1 := by
    rw [hnrs_post, Finset.card_erase_of_mem hp_in_nrs]
  have hnrs_pos : 1 ≤ (notReadySentSet s).card :=
    Finset.card_pos.mpr ⟨p, hp_in_nrs⟩
  have hifr_card_le :
      (insert p s.inflightReady).card ≤ s.inflightReady.card + 1 :=
    Finset.card_insert_le _ _
  unfold avssU
  rw [hds, hifd, hife, hifr, huss, hnrs_card, hunfin, hds_pre]
  simp only [if_true, zero_mul, Nat.zero_add]
  -- Set abbreviations.
  set K := lexBase n with hK_def
  set nrs := (notReadySentSet s).card
  set ifr := s.inflightReady.card
  -- Goal: ... + (nrs - 1) * K^2 + (insert p ifr).card * K + ... + 1
  --     ≤ ... + nrs * K^2 + ifr * K + ...
  -- Cancel common: (nrs-1)*K^2 + (insert p ifr).card*K + 1 ≤ nrs*K^2 + ifr*K
  -- Substitute nrs*K^2 = (nrs-1)*K^2 + K^2; suffices: K^2 ≥ (insert p ifr).card*K - ifr*K + 1
  -- Insert: |insert p ifr| ≤ ifr + 1, so |insert p ifr|*K - ifr*K ≤ K. So K^2 ≥ K + 1.
  -- For K ≥ 4: K^2 ≥ 16 ≥ 5 ≥ K + 1 = 5. ✓ (with margin for K = 4)
  have h_nrs_split : (nrs - 1) * K^2 + K^2 = nrs * K^2 := by
    have : nrs - 1 + 1 = nrs := Nat.sub_add_cancel hnrs_pos
    calc (nrs - 1) * K^2 + K^2 = ((nrs - 1) + 1) * K^2 := by ring
      _ = nrs * K^2 := by rw [this]
  have h_K2_ge : K^2 ≥ K + 1 := by nlinarith [hK_ge]
  nlinarith [h_nrs_split, h_K2_ge, hifr_card_le, hK_ge, hnrs_pos]

omit [Fintype F] in
/-- `partyAmplify` step: avssU strictly decreases.  Same shape as
`partyReady`: c5 (notReadySent) drops by 1; c6 (inflightReady) gains at
most 1.  Net K² - K ≥ 1. -/
theorem avssU_step_partyAmplify_lt (s : AVSSState n t F) (p : Fin n)
    (hgate : actionGate (AVSSAction.partyAmplify p) s)
    (hinv : avssTermInv s) :
    avssU (avssStep (AVSSAction.partyAmplify p) s) + 1 ≤ avssU s := by
  classical
  obtain ⟨hphon, hrsf, hrr_t⟩ := hgate
  have hds_pre : s.dealerSent = true := by
    apply dealerSent_true_of_local hinv (p := p)
    intro hp
    rw [hp] at hrr_t
    simp [AVSSLocalState.init] at hrr_t
  have hn_pos : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; exact p.elim0
    · exact hn
  have hK_ge : 4 ≤ lexBase n := by unfold lexBase; nlinarith
  -- Frame (analogous to partyReady).
  have hds : (avssStep (AVSSAction.partyAmplify p) s).dealerSent =
      s.dealerSent := by simp [avssStep, setLocal]
  have hcorr : (avssStep (AVSSAction.partyAmplify p) s).corrupted =
      s.corrupted := by simp [avssStep, setLocal]
  have hifd : (avssStep (AVSSAction.partyAmplify p) s).inflightDeliveries =
      s.inflightDeliveries := by simp [avssStep]
  have hife : (avssStep (AVSSAction.partyAmplify p) s).inflightEchoes =
      s.inflightEchoes := by simp [avssStep]
  have hifr : (avssStep (AVSSAction.partyAmplify p) s).inflightReady =
      insert p s.inflightReady := by simp [avssStep]
  have hdel : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyAmplify p) s).local_ x).delivered =
        (s.local_ x).delivered := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hes : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyAmplify p) s).local_ x).echoSent =
        (s.local_ x).echoSent := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hrs_p :
      ((avssStep (AVSSAction.partyAmplify p) s).local_ p).readySent = true := by
    simp [avssStep]
  have hrs_ne : ∀ x : Fin n, x ≠ p →
      ((avssStep (AVSSAction.partyAmplify p) s).local_ x).readySent =
        (s.local_ x).readySent := by
    intro x hxp
    simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hout : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyAmplify p) s).local_ x).output =
        (s.local_ x).output := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have huss : unsentEchoSet (avssStep (AVSSAction.partyAmplify p) s) =
      unsentEchoSet s := by
    apply Finset.ext; intro x
    simp only [unsentEchoSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hdel x, hes x]
  have hunfin : unfinishedSet (avssStep (AVSSAction.partyAmplify p) s) =
      unfinishedSet s := by
    apply Finset.ext; intro x
    simp only [unfinishedSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hout x]
  have hp_in_nrs : p ∈ notReadySentSet s := by
    simp only [notReadySentSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hphon, hrsf⟩
  have hnrs_post : notReadySentSet (avssStep (AVSSAction.partyAmplify p) s) =
      (notReadySentSet s).erase p := by
    apply Finset.ext; intro x
    simp only [notReadySentSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    rw [hcorr]
    by_cases hxp : x = p
    · subst hxp; simp [hrs_p]
    · rw [hrs_ne x hxp]; simp [hxp]
  have hnrs_card :
      (notReadySentSet (avssStep (AVSSAction.partyAmplify p) s)).card =
      (notReadySentSet s).card - 1 := by
    rw [hnrs_post, Finset.card_erase_of_mem hp_in_nrs]
  have hnrs_pos : 1 ≤ (notReadySentSet s).card :=
    Finset.card_pos.mpr ⟨p, hp_in_nrs⟩
  have hifr_card_le :
      (insert p s.inflightReady).card ≤ s.inflightReady.card + 1 :=
    Finset.card_insert_le _ _
  unfold avssU
  rw [hds, hifd, hife, hifr, huss, hnrs_card, hunfin, hds_pre]
  simp only [if_true, zero_mul, Nat.zero_add]
  set K := lexBase n with hK_def
  set nrs := (notReadySentSet s).card
  set ifr := s.inflightReady.card
  have h_nrs_split : (nrs - 1) * K^2 + K^2 = nrs * K^2 := by
    have : nrs - 1 + 1 = nrs := Nat.sub_add_cancel hnrs_pos
    calc (nrs - 1) * K^2 + K^2 = ((nrs - 1) + 1) * K^2 := by ring
      _ = nrs * K^2 := by rw [this]
  have h_K2_ge : K^2 ≥ K + 1 := by nlinarith [hK_ge]
  nlinarith [h_nrs_split, h_K2_ge, hifr_card_le, hK_ge, hnrs_pos]

omit [Fintype F] in
/-- `partyEchoReceive` step: avssU strictly decreases by `K³`. -/
theorem avssU_step_partyEchoReceive_lt (s : AVSSState n t F) (p q : Fin n)
    (hgate : actionGate (AVSSAction.partyEchoReceive p q) s)
    (hinv : avssTermInv s) :
    avssU (avssStep (AVSSAction.partyEchoReceive p q) s) + 1 ≤ avssU s := by
  classical
  obtain ⟨_, hqp_in, _⟩ := hgate
  have hds_pre : s.dealerSent = true :=
    dealerSent_true_of_inflight hinv
      (Or.inr (Or.inl (fun heq => by rw [heq] at hqp_in
                                     exact absurd hqp_in (Finset.notMem_empty _))))
  have hK_pos : 1 ≤ lexBase n := lexBase_pos
  -- Frame.
  have hds : (avssStep (AVSSAction.partyEchoReceive p q) s).dealerSent =
      s.dealerSent := by simp [avssStep, setLocal]
  have hcorr : (avssStep (AVSSAction.partyEchoReceive p q) s).corrupted =
      s.corrupted := by simp [avssStep, setLocal]
  have hifd : (avssStep (AVSSAction.partyEchoReceive p q) s).inflightDeliveries =
      s.inflightDeliveries := by simp [avssStep]
  have hife : (avssStep (AVSSAction.partyEchoReceive p q) s).inflightEchoes =
      s.inflightEchoes.erase (q, p) := by simp [avssStep]
  have hifr : (avssStep (AVSSAction.partyEchoReceive p q) s).inflightReady =
      s.inflightReady := by simp [avssStep]
  -- Per-party: only echoesReceived_p changes (not in U).
  have hdel : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyEchoReceive p q) s).local_ x).delivered =
        (s.local_ x).delivered := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hes : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyEchoReceive p q) s).local_ x).echoSent =
        (s.local_ x).echoSent := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hrs : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyEchoReceive p q) s).local_ x).readySent =
        (s.local_ x).readySent := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hout : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyEchoReceive p q) s).local_ x).output =
        (s.local_ x).output := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have huss : unsentEchoSet (avssStep (AVSSAction.partyEchoReceive p q) s) =
      unsentEchoSet s := by
    apply Finset.ext; intro x
    simp only [unsentEchoSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hdel x, hes x]
  have hnrs : notReadySentSet (avssStep (AVSSAction.partyEchoReceive p q) s) =
      notReadySentSet s := by
    apply Finset.ext; intro x
    simp only [notReadySentSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hrs x]
  have hunfin : unfinishedSet (avssStep (AVSSAction.partyEchoReceive p q) s) =
      unfinishedSet s := by
    apply Finset.ext; intro x
    simp only [unfinishedSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hout x]
  have hife_card :
      (s.inflightEchoes.erase (q, p)).card = s.inflightEchoes.card - 1 :=
    Finset.card_erase_of_mem hqp_in
  have hife_pos : 1 ≤ s.inflightEchoes.card :=
    Finset.card_pos.mpr ⟨(q, p), hqp_in⟩
  unfold avssU
  rw [hds, hifd, hife, hifr, huss, hnrs, hunfin, hife_card, hds_pre]
  simp only [if_true, zero_mul, Nat.zero_add]
  set K := lexBase n with hK_def
  -- Goal: ... + (ife - 1)*K^3 + ... + 1 ≤ ... + ife*K^3 + ...
  have h_split : (s.inflightEchoes.card - 1) * K^3 + K^3 =
      s.inflightEchoes.card * K^3 := by
    have : s.inflightEchoes.card - 1 + 1 = s.inflightEchoes.card :=
      Nat.sub_add_cancel hife_pos
    calc (s.inflightEchoes.card - 1) * K^3 + K^3
        = ((s.inflightEchoes.card - 1) + 1) * K^3 := by ring
      _ = s.inflightEchoes.card * K^3 := by rw [this]
  have hK3_pos : 1 ≤ K^3 := Nat.one_le_pow _ _ hK_pos
  nlinarith [h_split, hK3_pos]

omit [Fintype F] in
/-- `partyDeliver` step: avssU strictly decreases.  c2 (inflightDeliveries)
drops by 1 (loses K⁵); c3 (unsentEchoSet) gains 1 (gains K⁴) — `p` was
not in `unsentEchoSet` pre (delivered=false) but joins post (delivered=true,
echoSent=false from inv clause 2 contrapositive). Net ≥ K⁴(K-1) ≥ 1. -/
theorem avssU_step_partyDeliver_lt (s : AVSSState n t F) (p : Fin n)
    (hgate : actionGate (AVSSAction.partyDeliver p) s)
    (hinv : avssTermInv s) :
    avssU (avssStep (AVSSAction.partyDeliver p) s) + 1 ≤ avssU s := by
  classical
  obtain ⟨hds_pre, hphon, hpin, hdel_f⟩ := hgate
  have hn_pos : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; exact p.elim0
    · exact hn
  have hK_ge : 4 ≤ lexBase n := by unfold lexBase; nlinarith
  -- Pre echoSent at p = false (from inv clause 2 contrapositive).
  have hes_pre_p : (s.local_ p).echoSent = false := by
    by_contra hbad
    have hes_t : (s.local_ p).echoSent = true := by
      cases h : (s.local_ p).echoSent with
      | true => rfl
      | false => exact absurd h hbad
    have := hinv.2.1 p hphon hes_t
    rw [this] at hdel_f; cases hdel_f
  -- Frame.
  have hds : (avssStep (AVSSAction.partyDeliver p) s).dealerSent =
      s.dealerSent := by simp [avssStep, setLocal]
  have hcorr : (avssStep (AVSSAction.partyDeliver p) s).corrupted =
      s.corrupted := by simp [avssStep, setLocal]
  have hifd : (avssStep (AVSSAction.partyDeliver p) s).inflightDeliveries =
      s.inflightDeliveries.erase p := by simp [avssStep]
  have hife : (avssStep (AVSSAction.partyDeliver p) s).inflightEchoes =
      s.inflightEchoes := by simp [avssStep]
  have hifr : (avssStep (AVSSAction.partyDeliver p) s).inflightReady =
      s.inflightReady := by simp [avssStep]
  -- Per-party: only delivered_p (false→true) and rowPoly_p change.
  have hdel_p :
      ((avssStep (AVSSAction.partyDeliver p) s).local_ p).delivered = true := by
    simp [avssStep]
  have hdel_ne : ∀ x : Fin n, x ≠ p →
      ((avssStep (AVSSAction.partyDeliver p) s).local_ x).delivered =
        (s.local_ x).delivered := by
    intro x hxp
    simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hes_p :
      ((avssStep (AVSSAction.partyDeliver p) s).local_ p).echoSent =
        (s.local_ p).echoSent := by
    simp [avssStep]
  have hes_ne : ∀ x : Fin n, x ≠ p →
      ((avssStep (AVSSAction.partyDeliver p) s).local_ x).echoSent =
        (s.local_ x).echoSent := by
    intro x hxp
    simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hrs : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyDeliver p) s).local_ x).readySent =
        (s.local_ x).readySent := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hout : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyDeliver p) s).local_ x).output =
        (s.local_ x).output := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  -- Set equalities.
  have hnrs : notReadySentSet (avssStep (AVSSAction.partyDeliver p) s) =
      notReadySentSet s := by
    apply Finset.ext; intro x
    simp only [notReadySentSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hrs x]
  have hunfin : unfinishedSet (avssStep (AVSSAction.partyDeliver p) s) =
      unfinishedSet s := by
    apply Finset.ext; intro x
    simp only [unfinishedSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hout x]
  -- p ∉ unsentEchoSet pre (delivered=false), p ∈ unsentEchoSet post.
  have hp_notin_uss_pre : p ∉ unsentEchoSet s := by
    simp only [unsentEchoSet, Finset.mem_filter, Finset.mem_univ, true_and]
    intro ⟨_, hd, _⟩
    rw [hd] at hdel_f; cases hdel_f
  have hp_in_uss_post : p ∈ unsentEchoSet (avssStep (AVSSAction.partyDeliver p) s) := by
    simp only [unsentEchoSet, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, hdel_p, ?_⟩
    · rw [hcorr]; exact hphon
    · rw [hes_p]; exact hes_pre_p
  -- unsentEchoSet post = insert p (unsentEchoSet pre).
  have huss_post :
      unsentEchoSet (avssStep (AVSSAction.partyDeliver p) s) =
      insert p (unsentEchoSet s) := by
    apply Finset.ext; intro x
    simp only [unsentEchoSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    rw [hcorr]
    by_cases hxp : x = p
    · subst hxp
      rw [hdel_p, hes_p, hes_pre_p]
      simp [hphon]
    · rw [hdel_ne x hxp, hes_ne x hxp]
      constructor
      · intro h; right; exact h
      · rintro (heq | h)
        · exact absurd heq hxp
        · exact h
  have huss_card :
      (unsentEchoSet (avssStep (AVSSAction.partyDeliver p) s)).card =
      (unsentEchoSet s).card + 1 := by
    rw [huss_post]
    exact Finset.card_insert_of_notMem hp_notin_uss_pre
  -- inflightDeliveries.erase card.
  have hifd_card :
      (s.inflightDeliveries.erase p).card = s.inflightDeliveries.card - 1 :=
    Finset.card_erase_of_mem hpin
  have hifd_pos : 1 ≤ s.inflightDeliveries.card :=
    Finset.card_pos.mpr ⟨p, hpin⟩
  unfold avssU
  rw [hds, hifd, hife, hifr, huss_card, hnrs, hunfin, hifd_card, hds_pre]
  simp only [if_true, zero_mul, Nat.zero_add]
  set K := lexBase n with hK_def
  set ifd := s.inflightDeliveries.card
  set uss := (unsentEchoSet s).card
  -- Goal: (ifd - 1)*K^5 + (uss + 1)*K^4 + ... + 1 ≤ ifd*K^5 + uss*K^4 + ...
  -- ⟺ (ifd-1)*K^5 + uss*K^4 + K^4 + 1 ≤ ifd*K^5 + uss*K^4
  -- ⟺ (ifd-1)*K^5 + K^4 + 1 ≤ ifd*K^5
  -- Substitute ifd*K^5 = (ifd-1)*K^5 + K^5: K^4 + 1 ≤ K^5 = K * K^4.
  -- For K ≥ 2, K * K^4 ≥ 2 * K^4 = K^4 + K^4 ≥ K^4 + 1. ✓
  have h_ifd_split : (ifd - 1) * K^5 + K^5 = ifd * K^5 := by
    have : ifd - 1 + 1 = ifd := Nat.sub_add_cancel hifd_pos
    calc (ifd - 1) * K^5 + K^5 = ((ifd - 1) + 1) * K^5 := by ring
      _ = ifd * K^5 := by rw [this]
  have h_K4_pos : 1 ≤ K^4 := Nat.one_le_pow _ _ (by omega)
  have h_K5_ge : K^5 ≥ K^4 + 1 := by
    calc K^5 = K * K^4 := by ring
      _ ≥ 2 * K^4 := by nlinarith [h_K4_pos, hK_ge]
      _ = K^4 + K^4 := by ring
      _ ≥ K^4 + 1 := by omega
  nlinarith [h_ifd_split, h_K5_ge, hK_ge, hifd_pos]

omit [Fintype F] in
/-- `partyEchoSend` step: avssU strictly decreases.  c3 (unsentEchoSet)
drops by 1 (loses K⁴); c4 (inflightEchoes) gains at most `n` (gains
≤ n·K³). The lex weight K = (n+1)² is chosen exactly so K⁴ > n·K³. -/
theorem avssU_step_partyEchoSend_lt (s : AVSSState n t F) (p : Fin n)
    (hgate : actionGate (AVSSAction.partyEchoSend p) s)
    (hinv : avssTermInv s) :
    avssU (avssStep (AVSSAction.partyEchoSend p) s) + 1 ≤ avssU s := by
  classical
  obtain ⟨hphon, hdel_t, hesf⟩ := hgate
  have hds_pre : s.dealerSent = true := by
    apply dealerSent_true_of_local hinv (p := p)
    intro hp
    rw [hp] at hdel_t
    simp [AVSSLocalState.init] at hdel_t
  have hn_pos : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; exact p.elim0
    · exact hn
  have hK_def_eq : lexBase n = (n + 1) * (n + 1) := rfl
  have hK_ge : 4 ≤ lexBase n := by unfold lexBase; nlinarith
  have hK_gt_n : lexBase n > n := by unfold lexBase; nlinarith
  -- Frame.
  have hds : (avssStep (AVSSAction.partyEchoSend p) s).dealerSent =
      s.dealerSent := by simp [avssStep, setLocal]
  have hcorr : (avssStep (AVSSAction.partyEchoSend p) s).corrupted =
      s.corrupted := by simp [avssStep, setLocal]
  have hifd : (avssStep (AVSSAction.partyEchoSend p) s).inflightDeliveries =
      s.inflightDeliveries := by simp [avssStep]
  have hife : (avssStep (AVSSAction.partyEchoSend p) s).inflightEchoes =
      s.inflightEchoes ∪
        ((Finset.univ : Finset (Fin n)).filter
          (fun q => q ∉ s.corrupted)).image (fun q => (p, q)) := by
    simp [avssStep]
  have hifr : (avssStep (AVSSAction.partyEchoSend p) s).inflightReady =
      s.inflightReady := by simp [avssStep]
  -- Per-party: only echoSent_p flips false→true.
  have hdel : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyEchoSend p) s).local_ x).delivered =
        (s.local_ x).delivered := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hes_p :
      ((avssStep (AVSSAction.partyEchoSend p) s).local_ p).echoSent = true := by
    simp [avssStep]
  have hes_ne : ∀ x : Fin n, x ≠ p →
      ((avssStep (AVSSAction.partyEchoSend p) s).local_ x).echoSent =
        (s.local_ x).echoSent := by
    intro x hxp
    simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hrs : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyEchoSend p) s).local_ x).readySent =
        (s.local_ x).readySent := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  have hout : ∀ x : Fin n,
      ((avssStep (AVSSAction.partyEchoSend p) s).local_ x).output =
        (s.local_ x).output := by
    intro x
    by_cases hxp : x = p
    · subst hxp; simp [avssStep]
    · simp [avssStep, setLocal_local_ne _ _ _ _ hxp]
  -- Set equalities.
  have hnrs : notReadySentSet (avssStep (AVSSAction.partyEchoSend p) s) =
      notReadySentSet s := by
    apply Finset.ext; intro x
    simp only [notReadySentSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hrs x]
  have hunfin : unfinishedSet (avssStep (AVSSAction.partyEchoSend p) s) =
      unfinishedSet s := by
    apply Finset.ext; intro x
    simp only [unfinishedSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hout x]
  -- p ∈ unsentEchoSet pre, p ∉ unsentEchoSet post.
  have hp_in_uss_pre : p ∈ unsentEchoSet s := by
    simp only [unsentEchoSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hphon, hdel_t, hesf⟩
  have huss_post :
      unsentEchoSet (avssStep (AVSSAction.partyEchoSend p) s) =
      (unsentEchoSet s).erase p := by
    apply Finset.ext; intro x
    simp only [unsentEchoSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    rw [hcorr]
    by_cases hxp : x = p
    · subst hxp
      rw [hdel x, hes_p]
      simp
    · rw [hdel x, hes_ne x hxp]; simp [hxp]
  have huss_card :
      (unsentEchoSet (avssStep (AVSSAction.partyEchoSend p) s)).card =
      (unsentEchoSet s).card - 1 := by
    rw [huss_post, Finset.card_erase_of_mem hp_in_uss_pre]
  have huss_pos : 1 ≤ (unsentEchoSet s).card :=
    Finset.card_pos.mpr ⟨p, hp_in_uss_pre⟩
  -- inflightEchoes card bound: post ≤ pre + n.
  have hife_card_le :
      (s.inflightEchoes ∪
        ((Finset.univ : Finset (Fin n)).filter
          (fun q => q ∉ s.corrupted)).image (fun q => (p, q))).card
        ≤ s.inflightEchoes.card + n := by
    calc (s.inflightEchoes ∪
            ((Finset.univ : Finset (Fin n)).filter
              (fun q => q ∉ s.corrupted)).image (fun q => (p, q))).card
        ≤ s.inflightEchoes.card +
            (((Finset.univ : Finset (Fin n)).filter
              (fun q => q ∉ s.corrupted)).image (fun q => (p, q))).card :=
          Finset.card_union_le _ _
      _ ≤ s.inflightEchoes.card +
            ((Finset.univ : Finset (Fin n)).filter
              (fun q => q ∉ s.corrupted)).card := by
          gcongr; exact Finset.card_image_le
      _ ≤ s.inflightEchoes.card + (Finset.univ : Finset (Fin n)).card := by
          apply Nat.add_le_add_left; exact Finset.card_le_univ _
      _ = s.inflightEchoes.card + n := by simp
  unfold avssU
  rw [hds, hifd, hife, hifr, huss_card, hnrs, hunfin, hds_pre]
  simp only [if_true, zero_mul, Nat.zero_add]
  set K := lexBase n with hK_def
  set uss := (unsentEchoSet s).card
  set ife_pre := s.inflightEchoes.card
  -- Goal: ifd*K^5 + (uss-1)*K^4 + ife_post*K^3 + nrs*K^2 + ifr*K + unfin + 1
  --     ≤ ifd*K^5 + uss*K^4 + ife_pre*K^3 + nrs*K^2 + ifr*K + unfin
  -- Cancel and substitute uss*K^4 = (uss-1)*K^4 + K^4:
  -- ife_post*K^3 + 1 ≤ K^4 + ife_pre*K^3
  -- Use ife_post ≤ ife_pre + n: ife_pre*K^3 + n*K^3 + 1 ≤ K^4 + ife_pre*K^3
  -- ⟺ n*K^3 + 1 ≤ K^4 = K * K^3
  -- ⟺ n*K^3 + 1 ≤ K * K^3 ⟺ (K - n)*K^3 ≥ 1 (with K ≥ n+1).
  have h_uss_split : (uss - 1) * K^4 + K^4 = uss * K^4 := by
    have : uss - 1 + 1 = uss := Nat.sub_add_cancel huss_pos
    calc (uss - 1) * K^4 + K^4 = ((uss - 1) + 1) * K^4 := by ring
      _ = uss * K^4 := by rw [this]
  have hK3_pos : 1 ≤ K^3 := Nat.one_le_pow _ _ (by omega)
  -- Key bound: K^4 ≥ n * K^3 + 1, i.e., (K - n) * K^3 ≥ 1.
  have h_K4_ge : K^4 ≥ n * K^3 + 1 := by
    have hKn1 : K ≥ n + 1 := by
      rw [hK_def]; unfold lexBase; nlinarith
    have h1 : K^4 = K * K^3 := by ring
    have h2 : K * K^3 ≥ (n + 1) * K^3 := by nlinarith [hK3_pos, hKn1]
    nlinarith [hK3_pos, h1, h2]
  nlinarith [h_uss_split, h_K4_ge, hife_card_le, huss_pos, hK3_pos, hK_ge]

omit [Fintype F] in
/-- `dealerShare` step: avssU does not increase. The dealer step shifts
the unshared-dealer mass from c1 (K⁶) to c2 (K⁵), strictly dropping
unless `honestSet` is empty. -/
theorem avssU_step_dealerShare_le (s : AVSSState n t F)
    (hgate : actionGate (AVSSAction.dealerShare) s)
    (hinv : avssTermInv s) :
    avssU (avssStep (AVSSAction.dealerShare) s) ≤ avssU s := by
  classical
  have hds_pre : s.dealerSent = false := hgate
  have hi := hinv.1 hds_pre
  obtain ⟨hloc_init, hifd_emp, hife_emp, hifr_emp⟩ := hi
  have hK_pos : 1 ≤ lexBase n := lexBase_pos
  -- Frame.
  have hds_post : (avssStep (AVSSAction.dealerShare) s).dealerSent = true := by
    simp [avssStep]
  have hcorr : (avssStep (AVSSAction.dealerShare) s).corrupted =
      s.corrupted := by simp [avssStep]
  have hifd_post : (avssStep (AVSSAction.dealerShare) s).inflightDeliveries =
      (Finset.univ : Finset (Fin n)).filter (fun p => p ∉ s.corrupted) := by
    simp [avssStep]
  have hife_post : (avssStep (AVSSAction.dealerShare) s).inflightEchoes =
      s.inflightEchoes := by simp [avssStep]
  have hifr_post : (avssStep (AVSSAction.dealerShare) s).inflightReady =
      s.inflightReady := by simp [avssStep]
  have hloc_post : ∀ x : Fin n,
      (avssStep (AVSSAction.dealerShare) s).local_ x = s.local_ x := by
    intro x; simp [avssStep]
  -- Set equalities.
  have hH : honestSet (avssStep (AVSSAction.dealerShare) s) = honestSet s := by
    apply Finset.ext; intro x
    simp only [honestSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr]
  have huss : unsentEchoSet (avssStep (AVSSAction.dealerShare) s) =
      unsentEchoSet s := by
    apply Finset.ext; intro x
    simp only [unsentEchoSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hloc_post x]
  have hnrs : notReadySentSet (avssStep (AVSSAction.dealerShare) s) =
      notReadySentSet s := by
    apply Finset.ext; intro x
    simp only [notReadySentSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hloc_post x]
  have hunfin : unfinishedSet (avssStep (AVSSAction.dealerShare) s) =
      unfinishedSet s := by
    apply Finset.ext; intro x
    simp only [unfinishedSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcorr, hloc_post x]
  -- Pre-state queue cards = 0; post inflightDeliveries = honestSet.
  have hifd_pre_card : s.inflightDeliveries.card = 0 := by
    rw [hifd_emp]; rfl
  have hife_pre_card : s.inflightEchoes.card = 0 := by
    rw [hife_emp]; rfl
  have hifr_pre_card : s.inflightReady.card = 0 := by
    rw [hifr_emp]; rfl
  have hifd_post_eq_H :
      (avssStep (AVSSAction.dealerShare) s).inflightDeliveries = honestSet s := by
    rw [hifd_post]; rfl
  have hifd_post_card :
      ((avssStep (AVSSAction.dealerShare) s).inflightDeliveries).card =
      (honestSet s).card := by rw [hifd_post_eq_H]
  unfold avssU
  rw [hds_post, hife_post, hifr_post, hH, huss, hnrs, hunfin,
      hifd_post_card, hds_pre, hifd_pre_card, hife_pre_card, hifr_pre_card]
  simp only [Bool.false_eq_true, if_false, if_true, zero_mul, Nat.zero_add,
    Nat.add_zero]
  set K := lexBase n with hK_def
  set h := (honestSet s).card
  -- Goal: h * K^5 + uss*K^4 + nrs*K^2 + unfin ≤ h * K^6 + uss*K^4 + nrs*K^2 + unfin
  -- ⟺ h*K^5 ≤ h*K^6, follows from K^5 ≤ K^6.
  have hK5_le : K^5 ≤ K^6 := Nat.pow_le_pow_right hK_pos (by omega)
  have h_mul : h * K^5 ≤ h * K^6 := Nat.mul_le_mul_left h hK5_le
  linarith [h_mul]

omit [Fintype F] in
/-- Composite ≤: every gated action keeps avssU non-increasing. -/
theorem avssU_step_le (a : AVSSAction n F) (s : AVSSState n t F)
    (h : actionGate a s) (hinv : avssTermInv s) :
    avssU (avssStep a s) ≤ avssU s := by
  cases a with
  | dealerShare => exact avssU_step_dealerShare_le s h hinv
  | partyDeliver p =>
      have := avssU_step_partyDeliver_lt s p h hinv; omega
  | partyEchoSend p =>
      have := avssU_step_partyEchoSend_lt s p h hinv; omega
  | partyEchoReceive p q =>
      have := avssU_step_partyEchoReceive_lt s p q h hinv; omega
  | partyReady p =>
      have := avssU_step_partyReady_lt s p h hinv; omega
  | partyAmplify p =>
      have := avssU_step_partyAmplify_lt s p h hinv; omega
  | partyReceiveReady p q =>
      have := avssU_step_partyReceiveReady_lt s p q h hinv; omega
  | partyOutput p =>
      have := avssU_step_partyOutput_lt s p h hinv; omega

omit [Fintype F] in
/-- For every fair-firing action, avssU strictly decreases. -/
theorem avssU_step_lt_of_fair (a : AVSSAction n F) (s : AVSSState n t F)
    (h : actionGate a s) (hfair : a ∈ avssFairActions)
    (hinv : avssTermInv s) :
    avssU (avssStep a s) < avssU s := by
  cases a with
  | dealerShare => simp [avssFairActions] at hfair
  | partyDeliver p =>
      have := avssU_step_partyDeliver_lt s p h hinv; omega
  | partyEchoSend p =>
      have := avssU_step_partyEchoSend_lt s p h hinv; omega
  | partyEchoReceive p q =>
      have := avssU_step_partyEchoReceive_lt s p q h hinv; omega
  | partyReady p =>
      have := avssU_step_partyReady_lt s p h hinv; omega
  | partyAmplify p =>
      have := avssU_step_partyAmplify_lt s p h hinv; omega
  | partyReceiveReady p q =>
      have := avssU_step_partyReceiveReady_lt s p q h hinv; omega
  | partyOutput p =>
      have := avssU_step_partyOutput_lt s p h hinv; omega


/-! ### Phase 2d: variant value at terminated and at non-terminated states -/

omit [Fintype F] in
/-- Under `avssTermInv s` and `terminated s`, `avssU s = 0`. -/
theorem avssU_eq_zero_of_terminated (s : AVSSState n t F)
    (hinv : avssTermInv s) (ht : terminated s) :
    avssU s = 0 := by
  classical
  unfold avssU
  obtain ⟨ht_out, ht_echo, ht_ifd, ht_ife, ht_ifr⟩ := ht
  -- c2, c4, c6 = 0 from queues = ∅.
  have hifd_card : s.inflightDeliveries.card = 0 := by rw [ht_ifd]; rfl
  have hife_card : s.inflightEchoes.card = 0 := by rw [ht_ife]; rfl
  have hifr_card : s.inflightReady.card = 0 := by rw [ht_ifr]; rfl
  -- c7 = 0 from `unfinishedSet = ∅`.
  have hunfin : (unfinishedSet s).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro p _ ⟨hp_h, hp_none⟩
    have := ht_out p hp_h
    rw [hp_none] at this
    simp at this
  -- c3 = 0 from `unsentEchoSet = ∅` via `ht_echo`.
  have huss : (unsentEchoSet s).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro p _ ⟨hp_h, _, hp_es⟩
    have := ht_echo p hp_h
    rw [this] at hp_es
    cases hp_es
  -- c5 = 0 from inv clause 3 (output.isSome → readySent) + ht_out.
  have hnrs : (notReadySentSet s).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro p _ ⟨hp_h, hp_nrs⟩
    have hsome : (s.local_ p).output.isSome = true := ht_out p hp_h
    have := (hinv.2.2 p hp_h hsome).1
    rw [this] at hp_nrs
    cases hp_nrs
  -- c1 = 0: dealerSent = true OR honestSet = ∅.
  have hdom : (if s.dealerSent then (0 : ℕ) else (honestSet s).card) = 0 := by
    by_cases hds : s.dealerSent = true
    · simp [hds]
    · have hds' : s.dealerSent = false := by
        cases h_ds : s.dealerSent with
        | true => exact absurd h_ds hds
        | false => rfl
      have hi := hinv.1 hds'
      have hne : honestSet s = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro p hp
        have hp_h : p ∉ s.corrupted := by
          simp [honestSet, Finset.mem_filter] at hp; exact hp
        have hp_init := hi.1 p
        have hp_out_init : (s.local_ p).output = none := by
          rw [hp_init]; rfl
        have hp_some : (s.local_ p).output.isSome = true := ht_out p hp_h
        rw [hp_out_init] at hp_some
        simp at hp_some
      simp [hds', hne]
  rw [hdom, hifd_card, huss, hife_card, hnrs, hifr_card, hunfin]
  ring

omit [Fintype F] in
/-- `V_term` field: under `Inv` and `terminated`, `avssV s = 0`. -/
theorem avssCert_V_term (s : AVSSState n t F)
    (hinv : avssTermInv s) (ht : terminated s) :
    avssV s = 0 := by
  show (avssU s : ℝ≥0) = 0
  rw [avssU_eq_zero_of_terminated s hinv ht]
  simp

omit [Fintype F] in
/-- `U_term` field: under `Inv` and `terminated`, `avssU s = 0`. -/
theorem avssCert_U_term (s : AVSSState n t F)
    (hinv : avssTermInv s) (ht : terminated s) :
    avssU s = 0 :=
  avssU_eq_zero_of_terminated s hinv ht

omit [Fintype F] in
/-- `V_pos` field: at non-terminated states, `avssV s > 0`. -/
theorem avssCert_V_pos (s : AVSSState n t F)
    (hinv : avssTermInv s) (hnt : ¬ terminated s) :
    0 < avssV s := by
  show 0 < (avssU s : ℝ≥0)
  classical
  by_contra hcon
  push_neg at hcon
  have hU0_real : (avssU s : ℝ≥0) = 0 := le_antisymm hcon (zero_le _)
  have hU0 : avssU s = 0 := by exact_mod_cast hU0_real
  unfold avssU at hU0
  -- Decompose the sum of nonnegative ℕ-terms.  Each term must be 0.
  have hK_pos : 1 ≤ lexBase n := lexBase_pos
  obtain ⟨hU0', hunfin_t⟩ := Nat.add_eq_zero.mp hU0
  obtain ⟨hU0', hifr_t⟩ := Nat.add_eq_zero.mp hU0'
  obtain ⟨hU0', hnrs_t⟩ := Nat.add_eq_zero.mp hU0'
  obtain ⟨hU0', hife_t⟩ := Nat.add_eq_zero.mp hU0'
  obtain ⟨hU0', huss_t⟩ := Nat.add_eq_zero.mp hU0'
  obtain ⟨_hdom_t, hifd_t⟩ := Nat.add_eq_zero.mp hU0'
  -- For each `t * K^k = 0` with `K^k ≥ 1`, deduce `t = 0`.
  have hifd_card : s.inflightDeliveries.card = 0 := by
    rcases Nat.mul_eq_zero.mp hifd_t with h | h
    · exact h
    · have : 1 ≤ lexBase n ^ 5 := Nat.one_le_pow _ _ hK_pos; omega
  have huss_card : (unsentEchoSet s).card = 0 := by
    rcases Nat.mul_eq_zero.mp huss_t with h | h
    · exact h
    · have : 1 ≤ lexBase n ^ 4 := Nat.one_le_pow _ _ hK_pos; omega
  have hife_card : s.inflightEchoes.card = 0 := by
    rcases Nat.mul_eq_zero.mp hife_t with h | h
    · exact h
    · have : 1 ≤ lexBase n ^ 3 := Nat.one_le_pow _ _ hK_pos; omega
  have hnrs_card : (notReadySentSet s).card = 0 := by
    rcases Nat.mul_eq_zero.mp hnrs_t with h | h
    · exact h
    · have : 1 ≤ lexBase n ^ 2 := Nat.one_le_pow _ _ hK_pos; omega
  have hifr_card : s.inflightReady.card = 0 := by
    rcases Nat.mul_eq_zero.mp hifr_t with h | h
    · exact h
    · omega
  have hunfin_card : (unfinishedSet s).card = 0 := hunfin_t
  -- Now derive `terminated`.
  have hifd_emp : s.inflightDeliveries = ∅ := Finset.card_eq_zero.mp hifd_card
  have hife_emp : s.inflightEchoes = ∅ := Finset.card_eq_zero.mp hife_card
  have hifr_emp : s.inflightReady = ∅ := Finset.card_eq_zero.mp hifr_card
  have hunfin_emp : unfinishedSet s = ∅ := Finset.card_eq_zero.mp hunfin_card
  have huss_emp : unsentEchoSet s = ∅ := Finset.card_eq_zero.mp huss_card
  have h_out : ∀ p, p ∉ s.corrupted → (s.local_ p).output.isSome := by
    intro p hp
    by_contra hnone
    have hp_in : p ∈ unfinishedSet s := by
      simp only [unfinishedSet, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hp, ?_⟩
      cases h_o : (s.local_ p).output with
      | none => rfl
      | some _ => simp [h_o] at hnone
    rw [hunfin_emp] at hp_in
    exact (Finset.notMem_empty _) hp_in
  have h_echo : ∀ p, p ∉ s.corrupted → (s.local_ p).echoSent = true := by
    intro p hp
    by_contra hbad
    have hes : (s.local_ p).echoSent = false := by
      cases h_es : (s.local_ p).echoSent with
      | true => exact absurd h_es hbad
      | false => rfl
    -- Need delivered = true to put p in unsentEchoSet.
    have hsome := h_out p hp
    have hdel : (s.local_ p).delivered = true := (hinv.2.2 p hp hsome).2
    have hp_in : p ∈ unsentEchoSet s := by
      simp only [unsentEchoSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hp, hdel, hes⟩
    rw [huss_emp] at hp_in
    exact (Finset.notMem_empty _) hp_in
  exact hnt ⟨h_out, h_echo, hifd_emp, hife_emp, hifr_emp⟩

/-! ### Phase 2d: FairASTCertificate instance -/

/-- The 12-field `FairASTCertificate` instance for AVSS. The variant
analysis is built from the per-action lemmas: `V_super` from
`avssU_step_le`, `V_super_fair` and `U_dec_prob` from
`avssU_step_lt_of_fair`. The Dirac kernel collapses every
supermartingale tsum to a single term, reducing the variant analysis
to a `ℕ`-arithmetic exercise. -/
noncomputable def avssCert (sec : F) (corr : Finset (Fin n)) :
    FairASTCertificate (avssSpec (t := t) sec corr) avssFair terminated where
  Inv := avssTermInv
  V := avssV
  U := avssU
  inv_init := fun s hinit => by
    obtain ⟨hloc, _, _, hidl, hie, hird, _, _⟩ := hinit
    refine ⟨?_, ?_, ?_⟩
    · intro _
      refine ⟨hloc, hidl, hie, hird⟩
    · intro p _ hes
      rw [hloc p] at hes
      simp [AVSSLocalState.init] at hes
    · intro p _ hsome
      rw [hloc p] at hsome
      simp [AVSSLocalState.init] at hsome
  inv_step := avssTermInv_step
  V_term := avssCert_V_term
  V_pos := avssCert_V_pos
  V_super := fun a s h hinv _hnt => by
    classical
    have heff : ((avssSpec (t := t) sec corr).actions a).effect s h
                = PMF.pure (avssStep a s) := rfl
    rw [heff]
    rw [tsum_eq_single (avssStep a s)]
    · rw [PMF.pure_apply, if_pos rfl, one_mul]
      have h_le : avssU (avssStep a s) ≤ avssU s := avssU_step_le a s h hinv
      have : avssV (avssStep a s) ≤ avssV s := by
        show (avssU (avssStep a s) : ℝ≥0) ≤ (avssU s : ℝ≥0)
        exact_mod_cast h_le
      exact_mod_cast this
    · intro b hb
      rw [PMF.pure_apply, if_neg hb, zero_mul]
  V_super_fair := fun a s h hfair hinv _hnt => by
    classical
    have heff : ((avssSpec (t := t) sec corr).actions a).effect s h
                = PMF.pure (avssStep a s) := rfl
    rw [heff]
    rw [tsum_eq_single (avssStep a s)]
    · rw [PMF.pure_apply, if_pos rfl, one_mul]
      have hfair' : a ∈ avssFairActions := hfair
      have hlt : avssU (avssStep a s) < avssU s :=
        avssU_step_lt_of_fair a s h hfair' hinv
      have : avssV (avssStep a s) < avssV s := by
        show (avssU (avssStep a s) : ℝ≥0) < (avssU s : ℝ≥0)
        exact_mod_cast hlt
      exact_mod_cast this
    · intro b hb
      rw [PMF.pure_apply, if_neg hb, zero_mul]
  U_term := avssCert_U_term
  U_dec_det := fun a s h hfair hinv _hnt s' hs' => by
    classical
    have heff : ((avssSpec (t := t) sec corr).actions a).effect s h
                = PMF.pure (avssStep a s) := rfl
    rw [heff] at hs'
    rw [PMF.support_pure] at hs'
    have hs_eq : s' = avssStep a s := by simpa using hs'
    subst hs_eq
    left
    have hfair' : a ∈ avssFairActions := hfair
    exact avssU_step_lt_of_fair a s h hfair' hinv
  U_bdd_subl := fun _ =>
    ⟨(7 * n + 7) * (lexBase n) ^ 6, fun s _ _ => avssU_le_bound s⟩
  U_dec_prob := fun _ => by
    refine ⟨1, by norm_num, fun a s h hfair hinv _hnt _ => ?_⟩
    classical
    have heff : ((avssSpec (t := t) sec corr).actions a).effect s h
                = PMF.pure (avssStep a s) := rfl
    rw [heff]
    rw [tsum_eq_single (avssStep a s)]
    · rw [PMF.pure_apply, if_pos rfl, one_mul]
      have hfair' : a ∈ avssFairActions := hfair
      have hlt : avssU (avssStep a s) < avssU s :=
        avssU_step_lt_of_fair a s h hfair' hinv
      rw [if_pos hlt]
      simp
    · intro b hb
      rw [PMF.pure_apply, if_neg hb, zero_mul]
  V_init_bdd :=
    ⟨(((7 * n + 7) * (lexBase n) ^ 6 : ℕ) : ℝ≥0), fun s _ => by
      show ((avssU s : ℝ≥0)) ≤ (((7 * n + 7) * (lexBase n) ^ 6 : ℕ) : ℝ≥0)
      exact_mod_cast avssU_le_bound s⟩

/-! ## §13. Termination theorems (Phase 3) -/

/-- Termination as `AlmostDiamond` under a trajectory-fair adversary,
discharged via `FairASTCertificate.sound`.  Every fair execution
almost-surely reaches a terminated state (every honest party has
output, echoed, and all queues are drained). -/
theorem avss_termination_AS_fair
    (sec : F) (corr : Finset (Fin n))
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr s)
    (A : Leslie.Prob.TrajectoryFairAdversary
            (avssSpec (t := t) sec corr) avssFair μ₀)
    (h_U_mono : FairASTCertificate.TrajectoryUMono
        (avssSpec (t := t) sec corr) avssFair
        (avssCert (t := t) sec corr) μ₀ A.toFair)
    (h_U_strict : ∀ N : ℕ, FairASTCertificate.TrajectoryFairStrictDecrease
        (avssSpec (t := t) sec corr) avssFair
        (avssCert (t := t) sec corr) μ₀ A.toFair N) :
    AlmostDiamond (avssSpec (t := t) sec corr) A.toAdversary μ₀ terminated := by
  have h_init' : ∀ᵐ s ∂μ₀, (avssCert (t := t) sec corr).Inv s := by
    filter_upwards [h_init] with s hs
    exact (avssCert (t := t) sec corr).inv_init s hs
  exact FairASTCertificate.sound
    (avssCert (t := t) sec corr) μ₀ h_init' A.toFair A.progress
    h_U_mono h_U_strict

/-- Trajectory-form termination via the deterministic monotone
specialisation `pi_n_AST_fair_with_progress_det`.  Equivalent in
conclusion to `avss_termination_AS_fair`; this variant is exposed for
callers that prefer the explicit deterministic-descent route. -/
theorem avss_termination_AS_fair_traj
    (sec : F) (corr : Finset (Fin n))
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr s)
    (A : Leslie.Prob.TrajectoryFairAdversary
            (avssSpec (t := t) sec corr) avssFair μ₀)
    (h_U_mono : FairASTCertificate.TrajectoryUMono
        (avssSpec (t := t) sec corr) avssFair
        (avssCert (t := t) sec corr) μ₀ A.toFair)
    (h_U_strict : ∀ N : ℕ, FairASTCertificate.TrajectoryFairStrictDecrease
        (avssSpec (t := t) sec corr) avssFair
        (avssCert (t := t) sec corr) μ₀ A.toFair N) :
    AlmostDiamond (avssSpec (t := t) sec corr) A.toAdversary μ₀ terminated := by
  have h_init_inv : ∀ᵐ s ∂μ₀, (avssCert (t := t) sec corr).Inv s := by
    filter_upwards [h_init] with s hs
    exact (avssCert (t := t) sec corr).inv_init s hs
  set cert := avssCert (t := t) sec corr with hcertdef
  unfold AlmostDiamond
  have hbounded_or_unbounded :
      ∀ ω : Trace (AVSSState n t F) (AVSSAction n F),
        (∃ N : ℕ, ∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0)) ∨
        (∀ N : ℕ, ¬ (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0))) := by
    intro ω
    by_cases h : ∃ N : ℕ, ∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0)
    · exact .inl h
    · refine .inr ?_
      intro N hbnd
      exact h ⟨N, hbnd⟩
  have h_inf_null :
      ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr) A.toAdversary μ₀),
      ¬ (∀ N : ℕ, ¬ (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0))) := by
    rw [ae_iff]
    have heq :
        {a : Trace (AVSSState n t F) (AVSSAction n F) |
            ¬ ¬ ∀ N : ℕ, ¬ (∀ n, cert.V (a n).1 ≤ (N : ℝ≥0))} =
        {ω : Trace (AVSSState n t F) (AVSSAction n F) |
            ∀ N : ℕ, ¬ (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0))} := by
      ext ω; simp
    rw [heq]
    exact FairASTCertificate.pi_infty_zero_fair cert μ₀ h_init_inv A.toFair
  have h_each_N : ∀ N : ℕ,
      ∀ᵐ ω ∂(traceDist (avssSpec (t := t) sec corr) A.toAdversary μ₀),
        (∀ n, cert.V (ω n).1 ≤ (N : ℝ≥0)) → ∃ n, terminated (ω n).1 :=
    fun N => FairASTCertificate.pi_n_AST_fair_with_progress_det
      cert μ₀ h_init_inv A.toFair A.progress N h_U_mono (h_U_strict N)
  rw [← MeasureTheory.ae_all_iff] at h_each_N
  filter_upwards [h_each_N, h_inf_null] with ω hN h_inf
  rcases hbounded_or_unbounded ω with ⟨N, hbnd⟩ | hunb
  · exact hN N hbnd
  · exact absurd hunb h_inf

/-! ## §14. Honest-dealer correctness invariant

For honest dealer, every honest party that has stored a row poly
(`rowPoly = some rp`) has the *correct* row poly:
`rp = rowPolyOfDealer s.partyPoint s.coeffs p`.  Combined with the
fact that `partyOutput`'s effect computes `evalRowPoly rp 0`, this
gives every honest output equal to `bivEval coeffs (partyPoint p) 0`
(the per-party share). -/

/-- The honest-dealer correctness invariant. -/
def honestDealerInv (s : AVSSState n t F) : Prop :=
  s.dealerHonest = true →
    (∀ p, p ∉ s.corrupted →
      (s.local_ p).delivered = true →
        (s.local_ p).rowPoly =
          some (rowPolyOfDealer s.partyPoint s.coeffs p)) ∧
    (∀ p, p ∉ s.corrupted →
      ∀ v, (s.local_ p).output = some v →
        v = bivEval s.coeffs (s.partyPoint p) 0)

omit [Fintype F] in
theorem initPred_honestDealerInv (sec : F) (corr : Finset (Fin n))
    (s : AVSSState n t F) (h : initPred sec corr s) :
    honestDealerInv s := by
  intro _
  obtain ⟨hloc, _⟩ := h
  refine ⟨?_, ?_⟩
  · intro p _ hd
    rw [hloc p] at hd
    simp [AVSSLocalState.init] at hd
  · intro p _ v hv
    rw [hloc p] at hv
    simp [AVSSLocalState.init] at hv

set_option maxHeartbeats 800000 in
omit [Fintype F] in
/-- `honestDealerInv` is preserved by every gated action.  The hard
case is `partyOutput`: at the gate, `delivered = true` ensures
`rowPoly = some (rowPolyOfDealer ...)` (clause 1, pre); the output
value `evalRowPoly rp 0` then equals `bivEval coeffs (partyPoint p) 0`
by `evalRowPoly_rowPolyOfDealer`. -/
theorem avssStep_preserves_honestDealerInv
    (a : AVSSAction n F) (s : AVSSState n t F)
    (hgate : actionGate a s) (hinv : honestDealerInv s) :
    honestDealerInv (avssStep a s) := by
  intro hh
  -- `dealerHonest` is preserved by every action.
  have hh_pre : s.dealerHonest = true := by
    cases a <;> simp [avssStep, setLocal] at hh <;> exact hh
  obtain ⟨h_rp_correct, h_out_correct⟩ := hinv hh_pre
  refine ⟨?_, ?_⟩
  -- Clause 1: ∀ honest p, post delivered → post rowPoly = some rowPolyOfDealer
  · intro p hp hd_post
    cases a with
    | dealerShare =>
        simp [avssStep] at hd_post ⊢
        exact h_rp_correct p hp hd_post
    | partyDeliver q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hd_post ⊢
          exact h_rp_correct p hp hd_post
    | partyEchoSend q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hd_post ⊢
          exact h_rp_correct p hp hd_post
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hd_post ⊢
          exact h_rp_correct p hp hd_post
    | partyEchoReceive q r =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hd_post ⊢
          exact h_rp_correct p hp hd_post
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hd_post ⊢
          exact h_rp_correct p hp hd_post
    | partyReady q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hd_post ⊢
          exact h_rp_correct p hp hd_post
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hd_post ⊢
          exact h_rp_correct p hp hd_post
    | partyAmplify q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hd_post ⊢
          exact h_rp_correct p hp hd_post
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hd_post ⊢
          exact h_rp_correct p hp hd_post
    | partyReceiveReady q r =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hd_post ⊢
          exact h_rp_correct p hp hd_post
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hd_post ⊢
          exact h_rp_correct p hp hd_post
    | partyOutput q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hd_post ⊢
          exact h_rp_correct p hp hd_post
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hd_post ⊢
          exact h_rp_correct p hp hd_post
  -- Clause 2: ∀ honest p, post output = some v → v = bivEval coeffs (partyPoint p) 0
  · intro p hp v hv
    cases a with
    | dealerShare =>
        simp [avssStep] at hv
        exact h_out_correct p hp v hv
    | partyDeliver q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hv
          exact h_out_correct p hp v hv
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hv
          exact h_out_correct p hp v hv
    | partyEchoSend q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hv
          exact h_out_correct p hp v hv
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hv
          exact h_out_correct p hp v hv
    | partyEchoReceive q r =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hv
          exact h_out_correct p hp v hv
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hv
          exact h_out_correct p hp v hv
    | partyReady q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hv
          exact h_out_correct p hp v hv
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hv
          exact h_out_correct p hp v hv
    | partyAmplify q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hv
          exact h_out_correct p hp v hv
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hv
          exact h_out_correct p hp v hv
    | partyReceiveReady q r =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hv
          exact h_out_correct p hp v hv
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hv
          exact h_out_correct p hp v hv
    | partyOutput q =>
        -- The hard case: post output_q = some (evalRowPoly rp 0) where
        -- rp = pre rowPoly q.  By gate (delivered=true) and clause 1,
        -- pre rowPoly q = some (rowPolyOfDealer ...).  So
        -- v = evalRowPoly (rowPolyOfDealer ...) 0 = bivEval coeffs ... 0.
        have hcoeffs : (avssStep (AVSSAction.partyOutput q) s).coeffs = s.coeffs := by
          simp [avssStep, setLocal]
        have hpartyPoint :
            (avssStep (AVSSAction.partyOutput q) s).partyPoint = s.partyPoint := by
          simp [avssStep, setLocal]
        rw [hcoeffs, hpartyPoint]
        by_cases hpq : p = q
        · subst hpq
          obtain ⟨_, hd_q, _, _, _⟩ := hgate
          have hrp_pre : (s.local_ p).rowPoly =
              some (rowPolyOfDealer s.partyPoint s.coeffs p) :=
            h_rp_correct p hp hd_q
          simp [avssStep, setLocal_local_self, hrp_pre] at hv
          rw [← hv]
          exact evalRowPoly_rowPolyOfDealer s.partyPoint s.coeffs p 0
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hv
          exact h_out_correct p hp v hv

/-! ### Honest-dealer correctness as `AlmostBox` -/

set_option maxHeartbeats 800000 in
/-- Honest-dealer correctness, lifted to `AlmostBox`.  For an honest
dealer, every honest output equals the per-party share
`bivEval coeffs (partyPoint p) 0`.  Tolerates *any* adversary
(demonic or fair). -/
theorem avss_correctness_AS
    (sec : F) (corr : Finset (Fin n))
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr s)
    (A : Adversary (AVSSState n t F) (AVSSAction n F)) :
    AlmostBox (avssSpec (t := t) sec corr) A μ₀
      (fun s => s.dealerHonest = true →
        ∀ p, p ∉ s.corrupted →
          ∀ v, (s.local_ p).output = some v →
            v = bivEval s.coeffs (s.partyPoint p) 0) := by
  have h_pure : ∀ (a : AVSSAction n F) (s : AVSSState n t F)
      (h : ((avssSpec (t := t) sec corr).actions a).gate s),
      ((avssSpec (t := t) sec corr).actions a).effect s h
        = PMF.pure (avssStep a s) :=
    fun _ _ _ => rfl
  have h_init' : ∀ᵐ s ∂μ₀, honestDealerInv s := by
    filter_upwards [h_init] with s hs
    exact initPred_honestDealerInv sec corr s hs
  have h_inv : AlmostBox (avssSpec (t := t) sec corr) A μ₀ honestDealerInv :=
    AlmostBox_of_pure_inductive
      honestDealerInv
      (fun a s => avssStep a s)
      h_pure
      (fun a s hgate hinv =>
        avssStep_preserves_honestDealerInv a s hgate hinv)
      μ₀ h_init' A
  unfold AlmostBox at h_inv ⊢
  filter_upwards [h_inv] with ω hinv k hh p hp v hv
  exact (hinv k hh).2 p hp v hv

/-! ## §15. Output-determined invariant (commitment proxy)

Even with a corrupt dealer, every honest output (when set) equals
`bivEval s.coeffs (s.partyPoint p) 0` — the per-party share derived
from the dealer's bivariate polynomial.  In our model `s.coeffs` is
a single global field that the protocol distributes to honest parties
via `partyDeliver`'s effect (which writes the *correct* row poly
`rowPolyOfDealer s.partyPoint s.coeffs p`); a corrupt dealer cannot
deliver inconsistent row polys to honest parties because the model
abstracts the dealer's distribution as a single-step action.

The full Bracha-faithful commitment story (with the disjunction "all
honest outputs jointly consistent *or* dealer exposed") requires
explicit modeling of dealer-to-party messages and is left to the
next refinement layer. -/

/-- Commitment invariant: every honest output, when set, equals the
per-party share derived from `s.coeffs` and `s.partyPoint`. -/
def outputDeterminedInv (s : AVSSState n t F) : Prop :=
  (∀ p, p ∉ s.corrupted →
    (s.local_ p).delivered = true →
      (s.local_ p).rowPoly =
        some (rowPolyOfDealer s.partyPoint s.coeffs p)) ∧
  (∀ p, p ∉ s.corrupted →
    ∀ v, (s.local_ p).output = some v →
      v = bivEval s.coeffs (s.partyPoint p) 0)

omit [Fintype F] in
theorem initPred_outputDeterminedInv (sec : F) (corr : Finset (Fin n))
    (s : AVSSState n t F) (h : initPred sec corr s) :
    outputDeterminedInv s := by
  obtain ⟨hloc, _⟩ := h
  refine ⟨?_, ?_⟩
  · intro p _ hd
    rw [hloc p] at hd
    simp [AVSSLocalState.init] at hd
  · intro p _ v hv
    rw [hloc p] at hv
    simp [AVSSLocalState.init] at hv

set_option maxHeartbeats 800000 in
omit [Fintype F] in
/-- `outputDeterminedInv` is preserved by every gated action.  Same
case analysis as `avssStep_preserves_honestDealerInv` minus the
`dealerHonest = true` condition. -/
theorem avssStep_preserves_outputDeterminedInv
    (a : AVSSAction n F) (s : AVSSState n t F)
    (hgate : actionGate a s) (hinv : outputDeterminedInv s) :
    outputDeterminedInv (avssStep a s) := by
  obtain ⟨h_rp_correct, h_out_correct⟩ := hinv
  refine ⟨?_, ?_⟩
  · intro p hp hd_post
    cases a with
    | dealerShare =>
        simp [avssStep] at hd_post ⊢
        exact h_rp_correct p hp hd_post
    | partyDeliver q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self]
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hd_post ⊢
          exact h_rp_correct p hp hd_post
    | partyEchoSend q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hd_post ⊢
          exact h_rp_correct p hp hd_post
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hd_post ⊢
          exact h_rp_correct p hp hd_post
    | partyEchoReceive q r =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hd_post ⊢
          exact h_rp_correct p hp hd_post
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hd_post ⊢
          exact h_rp_correct p hp hd_post
    | partyReady q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hd_post ⊢
          exact h_rp_correct p hp hd_post
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hd_post ⊢
          exact h_rp_correct p hp hd_post
    | partyAmplify q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hd_post ⊢
          exact h_rp_correct p hp hd_post
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hd_post ⊢
          exact h_rp_correct p hp hd_post
    | partyReceiveReady q r =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hd_post ⊢
          exact h_rp_correct p hp hd_post
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hd_post ⊢
          exact h_rp_correct p hp hd_post
    | partyOutput q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hd_post ⊢
          exact h_rp_correct p hp hd_post
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hd_post ⊢
          exact h_rp_correct p hp hd_post
  · intro p hp v hv
    cases a with
    | dealerShare =>
        simp [avssStep] at hv
        exact h_out_correct p hp v hv
    | partyDeliver q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hv
          exact h_out_correct p hp v hv
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hv
          exact h_out_correct p hp v hv
    | partyEchoSend q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hv
          exact h_out_correct p hp v hv
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hv
          exact h_out_correct p hp v hv
    | partyEchoReceive q r =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hv
          exact h_out_correct p hp v hv
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hv
          exact h_out_correct p hp v hv
    | partyReady q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hv
          exact h_out_correct p hp v hv
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hv
          exact h_out_correct p hp v hv
    | partyAmplify q =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hv
          exact h_out_correct p hp v hv
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hv
          exact h_out_correct p hp v hv
    | partyReceiveReady q r =>
        by_cases hpq : p = q
        · subst hpq
          simp [avssStep, setLocal_local_self] at hv
          exact h_out_correct p hp v hv
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hv
          exact h_out_correct p hp v hv
    | partyOutput q =>
        have hcoeffs : (avssStep (AVSSAction.partyOutput q) s).coeffs = s.coeffs := by
          simp [avssStep, setLocal]
        have hpartyPoint :
            (avssStep (AVSSAction.partyOutput q) s).partyPoint = s.partyPoint := by
          simp [avssStep, setLocal]
        rw [hcoeffs, hpartyPoint]
        by_cases hpq : p = q
        · subst hpq
          obtain ⟨_, hd_q, _, _, _⟩ := hgate
          have hrp_pre : (s.local_ p).rowPoly =
              some (rowPolyOfDealer s.partyPoint s.coeffs p) :=
            h_rp_correct p hp hd_q
          simp [avssStep, setLocal_local_self, hrp_pre] at hv
          rw [← hv]
          exact evalRowPoly_rowPolyOfDealer s.partyPoint s.coeffs p 0
        · simp [avssStep, setLocal_local_ne _ _ _ _ hpq] at hv
          exact h_out_correct p hp v hv

set_option maxHeartbeats 800000 in
/-- Commitment as `AlmostBox`: even with corrupt dealer, every honest
output equals the per-party share `bivEval coeffs (partyPoint p) 0`.

This implies the user-facing commitment property: any two honest
outputs `vp`, `vq` are jointly consistent — both are determined by
the same (possibly corrupt) `s.coeffs`. -/
theorem avss_commitment_AS
    (sec : F) (corr : Finset (Fin n))
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr s)
    (A : Adversary (AVSSState n t F) (AVSSAction n F)) :
    AlmostBox (avssSpec (t := t) sec corr) A μ₀ outputDeterminedInv := by
  have h_pure : ∀ (a : AVSSAction n F) (s : AVSSState n t F)
      (h : ((avssSpec (t := t) sec corr).actions a).gate s),
      ((avssSpec (t := t) sec corr).actions a).effect s h
        = PMF.pure (avssStep a s) :=
    fun _ _ _ => rfl
  have h_init' : ∀ᵐ s ∂μ₀, outputDeterminedInv s := by
    filter_upwards [h_init] with s hs
    exact initPred_outputDeterminedInv sec corr s hs
  exact AlmostBox_of_pure_inductive
    outputDeterminedInv
    (fun a s => avssStep a s)
    h_pure
    (fun a s hgate hinv =>
      avssStep_preserves_outputDeterminedInv a s hgate hinv)
    μ₀ h_init' A

/-! ## §16. Quorum intersection (combinatorial)

Any two `n - t` quorums on `n` parties with at most `t` corrupt
parties intersect in at least `n - 3 t` honest parties.  For `n ≥
3 t + 1` this is ≥ 1 (so any two output-quorums share at least
one honest party); for `n ≥ 4 t + 1` this is ≥ `t + 1` (the classic
Bracha intersection bound). -/

omit [Field F] [Fintype F] [DecidableEq F] in
/-- Two `n - t` subsets of `Fin n`, with at most `t` of `Fin n`
corrupt, intersect in at least `n - 3 t` honest parties. -/
theorem quorum_intersection_card
    (corr Q₁ Q₂ : Finset (Fin n))
    (h_corr : corr.card ≤ t)
    (h_Q1 : n - t ≤ Q₁.card)
    (h_Q2 : n - t ≤ Q₂.card) :
    n - 3 * t ≤ ((Q₁ ∩ Q₂) \ corr).card := by
  classical
  have h_union_le_n : (Q₁ ∪ Q₂).card ≤ n := by
    calc (Q₁ ∪ Q₂).card
        ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
      _ = n := by simp
  have hadd : (Q₁ ∩ Q₂).card + (Q₁ ∪ Q₂).card = Q₁.card + Q₂.card :=
    Finset.card_inter_add_card_union Q₁ Q₂
  have h_inter : n - 2 * t ≤ (Q₁ ∩ Q₂).card := by omega
  have h_sdiff : (Q₁ ∩ Q₂).card - corr.card ≤ ((Q₁ ∩ Q₂) \ corr).card :=
    Finset.le_card_sdiff corr (Q₁ ∩ Q₂)
  omega

/-! ## §16.5 Reconstruction (Option C)

Given any subset `S` of `t + 1` honest parties whose `partyPoint`s are
distinct (in particular, distinct in `F`), Lagrange interpolation at
`0` of their per-party shares recovers the dealer's secret.

Algebraic core: the univariate polynomial `g(x) = bivEval coeffs x 0`
has degree ≤ `t`. We have `t + 1` evaluations at distinct points (the
honest parties' shares).  Mathlib's `Lagrange.eq_interpolate_of_eval_eq`
identifies `g` with its Lagrange interpolant; evaluating at `0`
recovers `coeffs 0 0`. -/

/-- The univariate polynomial whose evaluation at `partyPoint p`
equals the per-party share `bivEval coeffs (partyPoint p) 0`.

Concretely `g(x) = Σ_k coeffs k 0 · x^k`: a degree-`≤ t` polynomial
in `F[x]` carrying the dealer's column-0 coefficients. -/
noncomputable def reconstructPoly (coeffs : Fin (t+1) → Fin (t+1) → F) :
    Polynomial F :=
  ∑ k : Fin (t+1), Polynomial.C (coeffs k 0) * Polynomial.X ^ k.val

omit [Fintype F] [DecidableEq F] in
theorem reconstructPoly_eval (coeffs : Fin (t+1) → Fin (t+1) → F) (x : F) :
    (reconstructPoly coeffs).eval x = bivEval coeffs x 0 := by
  classical
  unfold reconstructPoly bivEval
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  -- Goal: coeffs k 0 * x ^ k.val = ∑ l, coeffs k l * x ^ k.val * 0 ^ l.val
  symm
  rw [Finset.sum_eq_single (0 : Fin (t+1))]
  · simp
  · intros l _ hl
    have hl_pos : 0 < l.val := Nat.pos_of_ne_zero (fun h => hl (Fin.ext h))
    rw [zero_pow (Nat.pos_iff_ne_zero.mp hl_pos)]
    ring
  · intro h; exact absurd (Finset.mem_univ _) h

omit [Fintype F] [DecidableEq F] in
theorem reconstructPoly_eval_zero (coeffs : Fin (t+1) → Fin (t+1) → F) :
    (reconstructPoly coeffs).eval 0 = coeffs 0 0 := by
  classical
  rw [reconstructPoly_eval]
  unfold bivEval
  rw [Finset.sum_eq_single (0 : Fin (t+1))]
  · rw [Finset.sum_eq_single (0 : Fin (t+1))]
    · simp
    · intros l _ hl
      have hl_pos : 0 < l.val := Nat.pos_of_ne_zero (fun h => hl (Fin.ext h))
      rw [zero_pow (Nat.pos_iff_ne_zero.mp hl_pos)]
      ring
    · intro h; exact absurd (Finset.mem_univ _) h
  · intros k _ hk
    have hk_pos : 0 < k.val := Nat.pos_of_ne_zero (fun h => hk (Fin.ext h))
    rw [zero_pow (Nat.pos_iff_ne_zero.mp hk_pos)]
    simp
  · intro h; exact absurd (Finset.mem_univ _) h

omit [Fintype F] [DecidableEq F] in
theorem reconstructPoly_natDegree_le (coeffs : Fin (t+1) → Fin (t+1) → F) :
    (reconstructPoly coeffs).natDegree ≤ t := by
  classical
  unfold reconstructPoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k _
  calc (Polynomial.C (coeffs k 0) * Polynomial.X^k.val).natDegree
      ≤ k.val := Polynomial.natDegree_C_mul_X_pow_le _ _
    _ ≤ t := Nat.le_of_lt_succ k.is_lt

omit [Fintype F] [DecidableEq F] in
theorem reconstructPoly_degree_lt (coeffs : Fin (t+1) → Fin (t+1) → F) :
    (reconstructPoly coeffs).degree < (t + 1 : ℕ) := by
  classical
  by_cases hp : reconstructPoly coeffs = 0
  · rw [hp, Polynomial.degree_zero]
    exact_mod_cast WithBot.bot_lt_coe (t + 1)
  · rw [Polynomial.degree_eq_natDegree hp]
    exact_mod_cast Nat.lt_succ_of_le (reconstructPoly_natDegree_le coeffs)

/-- AVSS reconstruction: given any `t + 1` honest parties with
distinct `partyPoint`s and outputs set, Lagrange interpolation at `0`
of their outputs recovers `coeffs 0 0` (= the secret, when the dealer
is honest). Tolerates corrupt dealer — the LHS is `s.coeffs 0 0`,
not `sec`. -/
theorem avss_reconstruction
    (s : AVSSState n t F)
    (hinv : outputDeterminedInv s)
    (S : Finset (Fin n))
    (h_size : S.card = t + 1)
    (h_inj : Set.InjOn s.partyPoint S)
    (h_honest : ∀ p ∈ S, p ∉ s.corrupted)
    (h_outs : ∀ p ∈ S, (s.local_ p).output.isSome) :
    s.coeffs 0 0 =
      Polynomial.eval 0
        (Lagrange.interpolate S s.partyPoint
          (fun p => Option.getD (s.local_ p).output 0)) := by
  classical
  -- The reconstruction polynomial g matches all honest output values.
  set g := reconstructPoly s.coeffs with hg_def
  have hg_eval : ∀ p ∈ S,
      g.eval (s.partyPoint p) = Option.getD (s.local_ p).output 0 := by
    intro p hp
    rw [reconstructPoly_eval]
    have hp_some := h_outs p hp
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hp_some
    have hv_eq : v = bivEval s.coeffs (s.partyPoint p) 0 :=
      hinv.2 p (h_honest p hp) v hv
    rw [hv]
    simp [hv_eq]
  -- Degree bound.
  have hg_deg : g.degree < S.card := by
    rw [h_size]
    exact reconstructPoly_degree_lt s.coeffs
  -- Identify g with its Lagrange interpolant.
  have hg_interp : g = Lagrange.interpolate S s.partyPoint
      (fun p => Option.getD (s.local_ p).output 0) :=
    Lagrange.eq_interpolate_of_eval_eq
      (fun p => Option.getD (s.local_ p).output 0) h_inj hg_deg hg_eval
  -- Evaluate both sides at 0.
  rw [← hg_interp, reconstructPoly_eval_zero]

/-! ## §17. Secrecy

Direct passthrough to `BivariateShamir.bivariate_shamir_secrecy`.
The post-deal grid view at any `t`-coalition is independent of the
secret. This is the **grid form** — option (b) in the SyncVSS brief,
the same form `bivariate_evals_uniform` directly delivers. The full
**row + column** view secrecy (a strict generalisation) is the
`+200 LOC` polynomial-manipulation step explicitly deferred in
`SyncVSS.lean §10`; we inherit the same deferral here. -/

/-- AVSS coalition-view secrecy (grid form). -/
theorem avss_secrecy (partyPoint : Fin n → F)
    (h_nz_pp : ∀ i, partyPoint i ≠ 0)
    (h_F : t + 1 ≤ Fintype.card F)
    (C D : BivariateShamir.Coalition n t) (sec sec' : F) :
    (Leslie.Prob.Polynomial.uniformBivariateWithFixedZero t t sec).map
        (fun f => fun (i : C.val) (j : D.val) =>
          some ((f.eval (Polynomial.C (partyPoint i.val))).eval
            (partyPoint j.val)))
      =
    (Leslie.Prob.Polynomial.uniformBivariateWithFixedZero t t sec').map
        (fun f => fun (i : C.val) (j : D.val) =>
          some ((f.eval (Polynomial.C (partyPoint i.val))).eval
            (partyPoint j.val))) :=
  BivariateShamir.bivariate_shamir_secrecy partyPoint h_nz_pp h_F C D sec sec'

end Leslie.Examples.Prob.AVSS
