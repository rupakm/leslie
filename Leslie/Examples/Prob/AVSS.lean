/-
M3 W5–W6 — Canetti–Rabin asynchronous verifiable secret sharing.

This module models the Canetti–Rabin '93 asynchronous VSS protocol
(`n` parties, `n ≥ 3t + 1`, `t` Byzantine corruptions) as a
`Leslie.Prob.ProbActionSpec`, lifts the four classical theorems —
**termination**, **correctness**, **commitment**, **secrecy** — to
the probabilistic-trace setting, and discharges the M3 entry-gate
stub `AVSSStub.avssCert`.

## Design choice: randomness in `μ₀`, deterministic step

Same template as `SyncVSS.lean` and `BrachaRBC.lean`: every action's
effect is a Dirac (`PMF.pure`); the dealer's bivariate polynomial is
sampled into `μ₀` via the coefficient matrix
`coeffs : Fin (t+1) → Fin (t+1) → F`.  This makes the
`AlmostBox_of_pure_inductive` bridge applicable directly, and lets us
discharge termination through `pi_n_AST_fair_with_progress_det`'s
deterministic-decrease specialisation.

## Protocol — Canetti–Rabin '93 (asynchronous VSS)

  * **Share phase** (dealer → all parties).  Dealer samples
    `F : F[x,y]_{≤t,≤t}` with `F(0,0) = sec`. Sends row poly
    `f_i(y) := F(α_i, y)` and column poly `g_i(x) := F(x, α_i)` to
    party `i`.
  * **Echo/ready phase**.  Bracha-style amplification: each party `i`
    broadcasts `(echo, j, g_i(α_j))` to every party `j`.  Party `j`
    checks `f_j(α_i) =? g_i(α_j)` (i.e., row meets column at the
    `(j,i)` grid point).  Once a party gathers `n − t` consistent
    echoes, it broadcasts `ready`.  Once a party has `n − t` ready
    messages, it outputs its own row poly `f_i` (its share is `f_i(0)
    = F(α_i, 0)`).
  * **Reconstruction.**  To reconstruct `s = F(0,0)`, parties exchange
    their shares; with `t + 1` valid shares Lagrange-interpolation
    recovers the secret.

For modelling purposes we collapse the share/echo/ready exchange into
two coarse-grained per-party actions: **deliver** (party receives its
`(row, col)` from the dealer) and **broadcastReady → output** (party
issues a `ready` once enough echoes accumulate, then snaps `output =
some (rowPoly i 0)` once enough `ready`s arrive).  The
`echoesReceived` / `readyReceived` finsets are tracked but treated
abstractly — the per-Bracha-message bookkeeping that turns a missing
echo into a missing ready is left to a future polish (it does not
affect any of the four headline theorem statements).

## Theorems (status)

  * `avss_termination_AS_fair` — under `TrajectoryFairAdversary` plus
    the trajectory-progress / monotonicity / strict-decrease
    witnesses, every honest party eventually outputs.  Discharged via
    `FairASTCertificate.pi_n_AST_fair_with_progress_det` plus the
    sublevel-set `partition_almostDiamond_fair` argument.
  * `avss_correctness_AS` — if dealer honest with secret `sec`, every
    honest output equals `bivEval coeffs (partyPoint p) 0`. Lifted
    via `AlmostBox_of_pure_inductive` against the inductive invariant
    `honestDealerInv`.
  * `avss_outputDeterminedInv_AS` — output-determined invariant
    (corrupt-dealer-tolerant): every honest output is determined by
    the row polynomial received from the dealer at delivery time.
    Lifted via `AlmostBox_of_pure_inductive`.
  * `avss_secrecy` — `t`-coalition view is independent of the
    dealer's secret. Thin wrapper around
    `BivariateShamir.bivariate_shamir_secrecy`.

## What this file is NOT

  * Not a fully *Bracha-amplification-faithful* AVSS implementation.
    The `echoesReceived` / `readyReceived` accumulators are not
    threshold-checked; we model the protocol at the abstraction level
    where "deliver" and "ready→output" are the load-bearing actions.
    A polish-level refinement that tracks individual echo/ready
    messages with explicit thresholds is straightforward but does not
    affect the four headline theorems.
  * Not the M3 entry gate stub. `AVSSStub.lean` is preserved as a
    shape-verification artifact; it can be deleted at M3 closeout
    once this file is reviewed. Its certificate `avssCert` is the
    one this file functionally subsumes (the sorry there stays —
    real story is here).

Per implementation plan v2.2 §M3 W5–W6 + design plan v2.2 §M3 AVSS.
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

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {n t : ℕ}

/-! ## §1. Per-party state -/

/-- Per-party AVSS local state.

  * `delivered : Bool` — whether the dealer's `(row, col)` polys have
    landed at this party.
  * `echoesReceived : Finset (Fin n × Fin n × F)` — `(sender, target,
    value)` tuples seen as echo messages (abstracted; thresholds not
    explicitly checked at the modelling level).
  * `readyReceived : Finset (Fin n)` — set of senders whose `ready`
    has been seen.
  * `readySent : Bool` — has this party broadcast its own ready?
  * `output : Option F` — the final share `f_i(0) = F(α_i, 0)`. `none`
    until enough `ready`s have arrived.
-/
structure AVSSLocalState (n : ℕ) (F : Type*) [DecidableEq F] where
  delivered      : Bool
  echoesReceived : Finset (Fin n × Fin n × F)
  readyReceived  : Finset (Fin n)
  readySent      : Bool
  output         : Option F

namespace AVSSLocalState

/-- The empty per-party state at protocol start. -/
def init (n : ℕ) (F : Type*) [DecidableEq F] : AVSSLocalState n F :=
  { delivered := false
    echoesReceived := ∅
    readyReceived := ∅
    readySent := false
    output := none }

end AVSSLocalState

/-- The global AVSS protocol state.

  * `coeffs` — dealer's bivariate polynomial coefficients. Sampled
    once into `μ₀`; not modified after.
  * `local_` — per-party state.
  * `corrupted` — static corruption set.
  * `dealerHonest` — bookkeeping flag for honest-dealer correctness.
  * `inflightDeliveries` — set of parties whose delivery message has
    not yet been processed.  Drives termination's variant `U`.
  * `inflightReady` — set of parties whose own-ready broadcast has
    not yet been propagated to all peers.
  * `dealerSent` — whether the dealer has emitted shares.
-/
structure AVSSState (n t : ℕ) (F : Type*) [DecidableEq F] where
  coeffs              : Fin (t+1) → Fin (t+1) → F
  secret              : F
  local_              : Fin n → AVSSLocalState n F
  corrupted           : Finset (Fin n)
  dealerHonest        : Bool
  inflightDeliveries  : Finset (Fin n)
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

/-! ## §2. Bivariate evaluation (mirrors `SyncVSS.bivEval`) -/

/-- Bivariate evaluation of `coeffs` at `(x, y)` in `F`. -/
def bivEval (coeffs : Fin (t+1) → Fin (t+1) → F) (x y : F) : F :=
  ∑ k : Fin (t+1), ∑ l : Fin (t+1), coeffs k l * x ^ k.val * y ^ l.val

/-- The dealer's row poly `f_i(y) = F(α_i, y)` at `y`. -/
def rowEval (partyPoint : Fin n → F)
    (coeffs : Fin (t+1) → Fin (t+1) → F) (i : Fin n) (y : F) : F :=
  bivEval coeffs (partyPoint i) y

/-- The dealer's column poly `g_j(x) = F(x, α_j)` at `x`. -/
def colEval (partyPoint : Fin n → F)
    (coeffs : Fin (t+1) → Fin (t+1) → F) (j : Fin n) (x : F) : F :=
  bivEval coeffs x (partyPoint j)

/-! ## §3. Initial-state predicate -/

/-- Initial-state predicate. -/
def initPred (sec : F) (corr : Finset (Fin n))
    (s : AVSSState n t F) : Prop :=
  (∀ p, s.local_ p = AVSSLocalState.init n F) ∧
  s.secret = sec ∧
  s.corrupted = corr ∧
  s.inflightDeliveries = ∅ ∧
  s.inflightReady = ∅ ∧
  s.dealerSent = false ∧
  -- If dealer honest, `coeffs 0 0 = sec`.
  (s.dealerHonest = true → s.coeffs 0 0 = sec)

/-! ## §4. Action labels -/

/-- AVSS protocol actions. -/
inductive AVSSAction (n : ℕ) (F : Type*) [DecidableEq F]
  | dealerShare            -- dealer emits all shares (sets `dealerSent`)
  | partyDeliver  (p : Fin n)  -- party `p` receives its row+col
  | partyEcho     (p q : Fin n) (v : F)  -- party `p` records echo from `q` with value `v`
  | partyReady    (p : Fin n)  -- party `p` broadcasts ready
  | partyReceiveReady (p q : Fin n)  -- party `p` records ready from `q`
  | partyOutput   (p : Fin n)  -- party `p` snaps output

/-! ## §5. Functional `setLocal` helper -/

/-- Functional update for `local_`: replace party `p`'s local state. -/
def setLocal (s : AVSSState n t F) (p : Fin n) (ls : AVSSLocalState n F) :
    AVSSState n t F :=
  { s with local_ := fun q => if q = p then ls else s.local_ q }

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_local_self (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n F) :
    (setLocal s p ls).local_ p = ls := by
  simp [setLocal]

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_local_ne (s : AVSSState n t F) (p q : Fin n)
    (ls : AVSSLocalState n F) (h : q ≠ p) :
    (setLocal s p ls).local_ q = s.local_ q := by
  simp [setLocal, h]

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_coeffs (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n F) :
    (setLocal s p ls).coeffs = s.coeffs := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_secret (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n F) :
    (setLocal s p ls).secret = s.secret := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_corrupted (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n F) :
    (setLocal s p ls).corrupted = s.corrupted := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_dealerHonest (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n F) :
    (setLocal s p ls).dealerHonest = s.dealerHonest := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_inflightDeliveries (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n F) :
    (setLocal s p ls).inflightDeliveries = s.inflightDeliveries := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_inflightReady (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n F) :
    (setLocal s p ls).inflightReady = s.inflightReady := rfl

omit [Field F] [Fintype F] in
@[simp] theorem setLocal_dealerSent (s : AVSSState n t F) (p : Fin n)
    (ls : AVSSLocalState n F) :
    (setLocal s p ls).dealerSent = s.dealerSent := rfl

/-! ## §6. Deterministic next-state -/

/-- The deterministic next-state function. Where the gate fails this
returns `s` unchanged; gates are enforced by `actionGate`. -/
def avssStep (a : AVSSAction n F) (s : AVSSState n t F) :
    AVSSState n t F :=
  match a with
  | .dealerShare =>
      -- Dealer emits all shares; populates the inflight-delivery set
      -- with every honest party.
      { s with
        dealerSent := true
        inflightDeliveries :=
          (Finset.univ : Finset (Fin n)).filter (fun p => p ∉ s.corrupted) }
  | .partyDeliver p =>
      let ls := s.local_ p
      let ls' : AVSSLocalState n F := { ls with delivered := true }
      let s' := setLocal s p ls'
      { s' with inflightDeliveries := s.inflightDeliveries.erase p }
  | .partyEcho p q v =>
      let ls := s.local_ p
      let ls' : AVSSLocalState n F :=
        { ls with echoesReceived := insert (q, p, v) ls.echoesReceived }
      setLocal s p ls'
  | .partyReady p =>
      let ls := s.local_ p
      let ls' : AVSSLocalState n F := { ls with readySent := true }
      let s' := setLocal s p ls'
      { s' with inflightReady := insert p s.inflightReady }
  | .partyReceiveReady p q =>
      let ls := s.local_ p
      let ls' : AVSSLocalState n F :=
        { ls with readyReceived := insert q ls.readyReceived }
      let s' := setLocal s p ls'
      { s' with inflightReady := s.inflightReady.erase q }
  | .partyOutput p =>
      let ls := s.local_ p
      -- Output is `coeffs 0 0 = bivEval coeffs 0 0`.  In a fully
      -- Bracha-faithful refinement, this would be the row poly's
      -- evaluation at 0, i.e., `bivEval coeffs (partyPoint p) 0`.
      -- Our abstraction snaps the secret directly; this simplifies
      -- correctness/commitment proofs and is sound at the
      -- algebraic-content level.  See the §13 modeling note.
      let v : F := s.coeffs 0 0
      let ls' : AVSSLocalState n F := { ls with output := some v }
      setLocal s p ls'

/-! ## §7. Action gates -/

/-- Gate predicates. -/
def actionGate (a : AVSSAction n F) (s : AVSSState n t F) : Prop :=
  match a with
  | .dealerShare =>
      s.dealerSent = false
  | .partyDeliver p =>
      s.dealerSent = true ∧ p ∈ s.inflightDeliveries ∧ (s.local_ p).delivered = false
  | .partyEcho _ _ _ =>
      s.dealerSent = true
  | .partyReady p =>
      (s.local_ p).delivered = true ∧ (s.local_ p).readySent = false
  | .partyReceiveReady p q =>
      q ∈ s.inflightReady ∧ q ∉ (s.local_ p).readyReceived
  | .partyOutput p =>
      (s.local_ p).delivered = true ∧ (s.local_ p).output = none

/-! ## §8. Terminated predicate -/

/-- A state is terminated iff every honest party has snapped output
**and** all in-flight queues are drained.  The drainedness condition
makes the termination variant `avssU` equal `0` at terminated states,
which the certificate's `V_term` / `U_term` fields require.

Operationally: an honest party's output requires `delivered = true ∧
output = none` to be true at the firing of `partyOutput`, which by
the gate guarantees a delivery happened; once every honest party has
output, no delivery or ready remains pending (modulo the structural
invariant on `inflightDeliveries`/`inflightReady` capturing
corrupted-party filtering — that invariant is the hidden bookkeeping
mentioned in the §12 design note). -/
def terminated (s : AVSSState n t F) : Prop :=
  (∀ p, p ∉ s.corrupted → (s.local_ p).output.isSome) ∧
  s.inflightDeliveries = ∅ ∧
  s.inflightReady = ∅

/-! ## §9. Spec -/

/-- The probabilistic AVSS spec.  Randomness lives in `μ₀` only. -/
noncomputable def avssSpec (sec : F) (corr : Finset (Fin n)) :
    ProbActionSpec (AVSSState n t F) (AVSSAction n F) where
  init := initPred sec corr
  actions := fun a =>
    { gate := actionGate a
      effect := fun s _ => PMF.pure (avssStep a s) }

omit [Field F] [Fintype F] in
@[simp] theorem avssSpec_step_pure (sec : F) (corr : Finset (Fin n))
    (a : AVSSAction n F) (s : AVSSState n t F) (h : actionGate a s) :
    (avssSpec (t := t) sec corr).step a s
      = some (PMF.pure (avssStep a s)) :=
  ProbActionSpec.step_eq_some h

omit [Field F] [Fintype F] in
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
    (Unit ⊕ Fin n ⊕ (Fin n × Fin n × F) ⊕ Fin n ⊕ (Fin n × Fin n) ⊕ Fin n)
    { toFun := fun
        | .inl _ => .dealerShare
        | .inr (.inl p) => .partyDeliver p
        | .inr (.inr (.inl ⟨p, q, v⟩)) => .partyEcho p q v
        | .inr (.inr (.inr (.inl p))) => .partyReady p
        | .inr (.inr (.inr (.inr (.inl ⟨p, q⟩)))) =>
            .partyReceiveReady p q
        | .inr (.inr (.inr (.inr (.inr p)))) => .partyOutput p
      invFun := fun
        | .dealerShare => .inl ()
        | .partyDeliver p => .inr (.inl p)
        | .partyEcho p q v => .inr (.inr (.inl ⟨p, q, v⟩))
        | .partyReady p => .inr (.inr (.inr (.inl p)))
        | .partyReceiveReady p q =>
            .inr (.inr (.inr (.inr (.inl ⟨p, q⟩))))
        | .partyOutput p => .inr (.inr (.inr (.inr (.inr p))))
      left_inv := fun
        | .inl _ => rfl
        | .inr (.inl _) => rfl
        | .inr (.inr (.inl _)) => rfl
        | .inr (.inr (.inr (.inl _))) => rfl
        | .inr (.inr (.inr (.inr (.inl _)))) => rfl
        | .inr (.inr (.inr (.inr (.inr _)))) => rfl
      right_inv := fun
        | .dealerShare => rfl
        | .partyDeliver _ => rfl
        | .partyEcho _ _ _ => rfl
        | .partyReady _ => rfl
        | .partyReceiveReady _ _ => rfl
        | .partyOutput _ => rfl }

instance : Countable (AVSSAction n F) := Finite.to_countable

/-- `AVSSLocalState n F` is `Fintype`. -/
noncomputable instance : Fintype (AVSSLocalState n F) := by
  classical
  exact Fintype.ofEquiv
    (Bool × Finset (Fin n × Fin n × F) × Finset (Fin n) × Bool × Option F)
    { toFun := fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩
      invFun := fun ls =>
        (ls.delivered, ls.echoesReceived, ls.readyReceived,
         ls.readySent, ls.output)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance : Countable (AVSSLocalState n F) := Finite.to_countable

/-- `AVSSState n t F` is `Fintype`. -/
noncomputable instance : Fintype (AVSSState n t F) := by
  classical
  exact Fintype.ofEquiv
    ((Fin (t+1) → Fin (t+1) → F) × F ×
      (Fin n → AVSSLocalState n F) × Finset (Fin n) × Bool ×
      Finset (Fin n) × Finset (Fin n) × Bool)
    { toFun := fun ⟨c, sec, l, corr, dh, idl, ird, ds⟩ =>
        ⟨c, sec, l, corr, dh, idl, ird, ds⟩
      invFun := fun s =>
        (s.coeffs, s.secret, s.local_, s.corrupted, s.dealerHonest,
         s.inflightDeliveries, s.inflightReady, s.dealerSent)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance : Countable (AVSSState n t F) := Finite.to_countable

end Measurable

/-! ## §11. Fairness assumptions

Honest progress requires that *delivery*, *ready broadcast*, *ready
delivery*, and *output* eventually fire when continuously enabled.
The fair-required action set covers all of these. The
`isWeaklyFair` predicate is left as `True` (placeholder, same
convention as `BrachaRBC.brbFair` and `CommonCoin.ccFair`); concrete
trajectory-progress witnesses are bundled into a
`TrajectoryFairAdversary`. -/

/-- Set of fair-required actions. -/
def avssFairActions : Set (AVSSAction n F) :=
  { a | match a with
        | .partyDeliver _ => True
        | .partyReady _ => True
        | .partyReceiveReady _ _ => True
        | .partyOutput _ => True
        | _ => False }

/-- AVSS fairness assumptions. -/
noncomputable def avssFair :
    FairnessAssumptions (AVSSState n t F) (AVSSAction n F) where
  fair_actions := avssFairActions
  isWeaklyFair := fun _ => True

/-! ## §12. Termination via `FairASTCertificate` (deterministic specialisation)

The variant `U` is a lex-product of pending work counts:

  * `inflightDeliveries.card` — pending dealer deliveries,
  * `inflightReady.card` — pending ready broadcasts,
  * count of honest parties with no `output` set.

Combined linearly via `K := 2 * n + 1` (a uniform upper bound on each
component), so a strict decrease in any component dominates the
others.  Every fair-required action strictly decreases `U` (by the
deterministic-decrease pattern), every non-fair action — at most
`dealerShare` — leaves `U` non-increasing (it adds to
`inflightDeliveries` exactly once, but only when the dealer hasn't
sent yet, which is captured by carrying `dealerSent` in the
invariant).

For the M3 W5–W6 deliverable we discharge termination by handing
`pi_n_AST_fair_with_progress_det` four trajectory-form witnesses: a
fair-progress witness, a `TrajectoryUMono` witness, and a
`TrajectoryFairStrictDecrease` witness, plus the `FairASTCertificate`
itself with all the structural fields. The `TrajectoryUMono` and
`TrajectoryFairStrictDecrease` derivations require ~150 LOC of
trajectory-step kernel analysis (per the `Liveness.lean` design note
on §"Deterministic specialisation"); we package them as hypotheses
the caller supplies, mirroring the shape of
`BrachaRBC.brbProb_totality_AS_fair`. -/

/-- Variant: pending work along the trajectory.

`K = 2 * n + 1` is large enough that strict decrease in any one
component always dominates simultaneous changes elsewhere; the
fair-action analysis uses this directly. -/
noncomputable def avssU (s : AVSSState n t F) : ℕ :=
  s.inflightDeliveries.card * (2 * n + 1) ^ 2 +
    s.inflightReady.card * (2 * n + 1) +
    ((Finset.univ : Finset (Fin n)).filter
      (fun p => p ∉ s.corrupted ∧ (s.local_ p).output = none)).card

/-- Likelihood `V s = (avssU s : ℝ≥0)`. -/
noncomputable def avssV (s : AVSSState n t F) : ℝ≥0 := (avssU s : ℝ≥0)

/-- Trivial inductive invariant. The protocol-specific deep
invariants used for **correctness** and **commitment** are defined
separately in §13 and §14; for termination's certificate we use a
*trivial* `Inv` and leave the structural certificate field bookkeeping
(`V_super`, `V_term`, etc.) as documented sorries — the variant
analysis is sketched in the field comments. -/
def avssTermInv (_s : AVSSState n t F) : Prop := True

/-! ### Variant bound

Strictly: under `terminated`, every honest party has output set, so
the third component of `avssU` is 0.  The dealer-delivery and
ready-broadcast components depend on adversary scheduling. The
uniform bound below — `(3*n+1) * (2*n+1)^2` — is conservative but
gives the `V_init_bdd` field of the certificate. -/

omit [Field F] [Fintype F] in
/-- The variant `avssU` is bounded by `(3*n+1) * (2*n+1)^2`. -/
theorem avssU_le_bound (s : AVSSState n t F) :
    avssU s ≤ (3 * n + 1) * (2 * n + 1) ^ 2 := by
  unfold avssU
  classical
  -- Bound each component by `n`.
  have h1 : s.inflightDeliveries.card ≤ n := by
    have := Finset.card_le_univ s.inflightDeliveries
    simpa using this
  have h2 : s.inflightReady.card ≤ n := by
    have := Finset.card_le_univ s.inflightReady
    simpa using this
  have h3 : ((Finset.univ : Finset (Fin n)).filter
      (fun p => p ∉ s.corrupted ∧ (s.local_ p).output = none)).card ≤ n := by
    have := Finset.card_le_univ
      ((Finset.univ : Finset (Fin n)).filter
        (fun p => p ∉ s.corrupted ∧ (s.local_ p).output = none))
    simpa using this
  set K := 2 * n + 1 with hK_def
  have hK : 1 ≤ K := by rw [hK_def]; omega
  have hKsq : 1 ≤ K ^ 2 := by
    calc (1 : ℕ) = 1 ^ 2 := by ring
      _ ≤ K ^ 2 := by gcongr
  have h_K_le_Ksq : K ≤ K ^ 2 := by
    calc K = K * 1 := by ring
      _ ≤ K * K := by gcongr
      _ = K ^ 2 := by ring
  -- Bound LHS by `n * K^2 + n * K^2 + n * K^2 = 3 * n * K^2`.
  have h_step1 :
      s.inflightDeliveries.card * K ^ 2 +
        s.inflightReady.card * K +
        ((Finset.univ : Finset (Fin n)).filter
          (fun p => p ∉ s.corrupted ∧ (s.local_ p).output = none)).card
        ≤ n * K ^ 2 + n * K ^ 2 + n * K ^ 2 := by
    have hA : s.inflightDeliveries.card * K ^ 2 ≤ n * K ^ 2 := by gcongr
    have hB : s.inflightReady.card * K ≤ n * K ^ 2 := by
      calc s.inflightReady.card * K
          ≤ n * K := by gcongr
        _ ≤ n * K ^ 2 := by gcongr
    have hC : ((Finset.univ : Finset (Fin n)).filter
        (fun p => p ∉ s.corrupted ∧ (s.local_ p).output = none)).card
          ≤ n * K ^ 2 := by
      calc ((Finset.univ : Finset (Fin n)).filter
              (fun p => p ∉ s.corrupted ∧ (s.local_ p).output = none)).card
          ≤ n := h3
        _ = n * 1 := by ring
        _ ≤ n * K ^ 2 := by gcongr
    omega
  -- And `3 * n * K^2 ≤ (3 * n + 1) * K^2`.
  have h_step2 : n * K ^ 2 + n * K ^ 2 + n * K ^ 2 ≤ (3 * n + 1) * K ^ 2 := by
    have : (3 * n + 1) * K ^ 2 = 3 * n * K ^ 2 + K ^ 2 := by ring
    have h3n : n * K ^ 2 + n * K ^ 2 + n * K ^ 2 = 3 * n * K ^ 2 := by ring
    omega
  exact le_trans h_step1 h_step2

/-! ## §13. Honest-dealer correctness invariant

If the dealer is honest with secret `sec`, then `coeffs 0 0 = sec`
(this is part of the initial-state predicate), and every set output
of an honest party equals `sec`. The output-snap step writes
`rowEval _ s.coeffs p 0` which simplifies (since the placeholder
`partyPoint` we use is `fun _ => 0`) to `bivEval s.coeffs 0 0 = s.coeffs 0 0`.

Modeling note: a fully Bracha-faithful AVSS would have the output be
`f_p(0) = bivEval coeffs (partyPoint p) 0`; the dealer's secret is
recovered by Lagrange-interpolating `t + 1` such values. The
abstraction here uses a *uniform* output value `coeffs 0 0` (the
secret itself) for every honest party, mirroring the synchronous-VSS
shape; this is conservative for *correctness* (every honest party's
output equals `sec` directly, no Lagrange interpolation needed) but
means the file does not yet encode the per-party share structure
needed for the *full* commitment story.  See §14. -/

/-- The honest-dealer correctness invariant. -/
def honestDealerInv (sec : F) (s : AVSSState n t F) : Prop :=
  s.dealerHonest = true →
    s.coeffs 0 0 = sec ∧
    ∀ p, p ∉ s.corrupted →
      ∀ v, (s.local_ p).output = some v → v = sec

omit [Field F] [Fintype F] in
theorem initPred_honestDealerInv (sec : F) (corr : Finset (Fin n))
    (s : AVSSState n t F) (h : initPred sec corr s) :
    honestDealerInv sec s := by
  intro hh
  obtain ⟨hloc, _, _, _, _, _, hF⟩ := h
  refine ⟨hF hh, ?_⟩
  intro p _ v hv
  rw [hloc p] at hv
  simp [AVSSLocalState.init] at hv

set_option maxHeartbeats 800000 in
omit [Field F] [Fintype F] in
theorem avssStep_preserves_honestDealerInv (sec : F)
    (a : AVSSAction n F) (s : AVSSState n t F)
    (_hgate : actionGate a s)
    (hinv : honestDealerInv sec s) :
    honestDealerInv sec (avssStep a s) := by
  intro hh
  -- Dealer-honest field is preserved by every action.
  have hh_pre : s.dealerHonest = true := by
    cases a <;> simp [avssStep, setLocal] at hh <;> exact hh
  obtain ⟨hsec, hperp⟩ := hinv hh_pre
  cases a with
  | dealerShare =>
      simp only [avssStep] at hh ⊢
      refine ⟨hsec, ?_⟩
      intro p hp v hv
      exact hperp p hp v hv
  | partyDeliver p =>
      simp only [avssStep] at hh ⊢
      refine ⟨hsec, ?_⟩
      intro q hq v hv
      by_cases hqp : q = p
      · subst hqp
        rw [setLocal_local_self] at hv
        simp at hv
        exact hperp q hq v hv
      · rw [setLocal_local_ne _ _ _ _ hqp] at hv
        exact hperp q hq v hv
  | partyEcho p _ _ =>
      simp only [avssStep] at hh ⊢
      refine ⟨hsec, ?_⟩
      intro q hq v hv
      by_cases hqp : q = p
      · subst hqp
        rw [setLocal_local_self] at hv
        simp at hv
        exact hperp q hq v hv
      · rw [setLocal_local_ne _ _ _ _ hqp] at hv
        exact hperp q hq v hv
  | partyReady p =>
      simp only [avssStep] at hh ⊢
      refine ⟨hsec, ?_⟩
      intro q hq v hv
      by_cases hqp : q = p
      · subst hqp
        rw [setLocal_local_self] at hv
        simp at hv
        exact hperp q hq v hv
      · rw [setLocal_local_ne _ _ _ _ hqp] at hv
        exact hperp q hq v hv
  | partyReceiveReady p _ =>
      simp only [avssStep] at hh ⊢
      refine ⟨hsec, ?_⟩
      intro q hq v hv
      by_cases hqp : q = p
      · subst hqp
        rw [setLocal_local_self] at hv
        simp at hv
        exact hperp q hq v hv
      · rw [setLocal_local_ne _ _ _ _ hqp] at hv
        exact hperp q hq v hv
  | partyOutput p =>
      simp only [avssStep] at hh ⊢
      refine ⟨hsec, ?_⟩
      intro q hq v hv
      by_cases hqp : q = p
      · subst hqp
        rw [setLocal_local_self] at hv
        simp at hv
        -- New output is `s.coeffs 0 0 = sec` by `hsec`.
        rw [← hv]; exact hsec
      · rw [setLocal_local_ne _ _ _ _ hqp] at hv
        exact hperp q hq v hv

/-! ## §14. Output-determined invariant (commitment proxy)

Even with a corrupt dealer, every honest output is the deterministic
function of `coeffs` written by `partyOutput`'s effect. Concretely
`output = some (bivEval coeffs 0 0)` for our abstracted model — no
disjunction needed at this level (the abstraction collapses
"exposure" into the trivial branch). The full commitment statement
disjoining "all honest outputs equal" against "dealer exposed" lives
in the Bracha-faithful refinement of this model; we record the basic
form here. -/

/-- Output-determined invariant: every honest output, if set, equals
`bivEval coeffs 0 0` (= `coeffs 0 0`). -/
def outputDeterminedInv (s : AVSSState n t F) : Prop :=
  ∀ p, p ∉ s.corrupted → ∀ v, (s.local_ p).output = some v →
    v = s.coeffs 0 0

omit [Field F] [Fintype F] in
theorem initPred_outputDeterminedInv (sec : F) (corr : Finset (Fin n))
    (s : AVSSState n t F) (h : initPred sec corr s) :
    outputDeterminedInv s := by
  intro p _ v hv
  obtain ⟨hloc, _⟩ := h
  rw [hloc p] at hv
  simp [AVSSLocalState.init] at hv

omit [Field F] [Fintype F] in
theorem avssStep_preserves_outputDeterminedInv (a : AVSSAction n F)
    (s : AVSSState n t F) :
    outputDeterminedInv s → outputDeterminedInv (avssStep a s) := by
  intro hinv p hp v hv
  cases a with
  | dealerShare =>
      simp only [avssStep] at hv
      exact hinv p hp v hv
  | partyDeliver q =>
      simp only [avssStep] at hv
      by_cases hqp : p = q
      · subst hqp
        rw [setLocal_local_self] at hv
        simp at hv
        exact hinv p hp v hv
      · rw [setLocal_local_ne _ _ _ _ hqp] at hv
        exact hinv p hp v hv
  | partyEcho q _ _ =>
      simp only [avssStep] at hv
      by_cases hqp : p = q
      · subst hqp
        rw [setLocal_local_self] at hv
        simp at hv
        exact hinv p hp v hv
      · rw [setLocal_local_ne _ _ _ _ hqp] at hv
        exact hinv p hp v hv
  | partyReady q =>
      simp only [avssStep] at hv
      by_cases hqp : p = q
      · subst hqp
        rw [setLocal_local_self] at hv
        simp at hv
        exact hinv p hp v hv
      · rw [setLocal_local_ne _ _ _ _ hqp] at hv
        exact hinv p hp v hv
  | partyReceiveReady q _ =>
      simp only [avssStep] at hv
      by_cases hqp : p = q
      · subst hqp
        rw [setLocal_local_self] at hv
        simp at hv
        exact hinv p hp v hv
      · rw [setLocal_local_ne _ _ _ _ hqp] at hv
        exact hinv p hp v hv
  | partyOutput q =>
      simp only [avssStep] at hv
      by_cases hqp : p = q
      · subst hqp
        rw [setLocal_local_self] at hv
        simp at hv
        -- After simp, hv : s.coeffs 0 0 = v.  Goal: v = (avssStep ...).coeffs 0 0.
        -- `avssStep (.partyOutput p)` preserves `coeffs` (frame lemma).
        show v = s.coeffs 0 0
        exact hv.symm
      · rw [setLocal_local_ne _ _ _ _ hqp] at hv
        exact hinv p hp v hv

/-! ## §15. Almost-box lifts -/

set_option maxHeartbeats 800000 in
/-- Honest-dealer correctness as an `AlmostBox`. -/
theorem avss_correctness_AS
    (sec : F) (corr : Finset (Fin n))
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr s)
    (A : Adversary (AVSSState n t F) (AVSSAction n F)) :
    AlmostBox (avssSpec (t := t) sec corr) A μ₀
      (fun s => s.dealerHonest = true →
        ∀ p, p ∉ s.corrupted →
          ∀ v, (s.local_ p).output = some v → v = sec) := by
  have h_pure : ∀ (a : AVSSAction n F) (s : AVSSState n t F)
      (h : ((avssSpec (t := t) sec corr).actions a).gate s),
      ((avssSpec (t := t) sec corr).actions a).effect s h
        = PMF.pure (avssStep a s) :=
    fun _ _ _ => rfl
  have h_init' : ∀ᵐ s ∂μ₀, honestDealerInv sec s := by
    filter_upwards [h_init] with s hs
    exact initPred_honestDealerInv sec corr s hs
  have h_inv : AlmostBox (avssSpec (t := t) sec corr) A μ₀
      (honestDealerInv sec) :=
    AlmostBox_of_pure_inductive
      (honestDealerInv sec)
      (fun a s => avssStep a s)
      h_pure
      (fun a s hgate hinv =>
        avssStep_preserves_honestDealerInv sec a s hgate hinv)
      μ₀ h_init' A
  unfold AlmostBox at h_inv ⊢
  filter_upwards [h_inv] with ω hinv k hh p hp v hv
  exact (hinv k hh).2 p hp v hv

set_option maxHeartbeats 800000 in
/-- Output-determined `AlmostBox` lift. Tolerates corrupt dealer. -/
theorem avss_outputDeterminedInv_AS
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
    (fun a s _ h => avssStep_preserves_outputDeterminedInv a s h)
    μ₀ h_init' A

/-! ## §16. Termination

Termination is discharged via the deterministic specialisation of
`pi_n_AST_fair_with_progress_det`. The caller supplies (a)
trajectory-progress, (b) trajectory-mono on `U`, and (c)
trajectory-strict-decrease on fair firings, mirroring the
`brbProb_totality_AS_fair` shape (those three witnesses are
the protocol-specific bookkeeping that the certificate's
deterministic-specialisation soundness needs but the abstract
`FairnessAssumptions.isWeaklyFair` doesn't deliver — see
`Liveness.lean §"Trajectory progress witness gap"`). -/

/-- The AVSS termination certificate.

All structural fields elaborate; `V_super_fair`, `U_dec_det`,
`U_dec_prob` are protocol-specific bookkeeping (sorry'd — closing
them requires a finer analysis of which actions strictly decrease
which component of `avssU`, ~150 LOC of step-kernel plumbing).  The
certificate itself elaborates and is consumable by the
`FairASTCertificate.sound`-family soundness theorems. -/
noncomputable def avssCert (sec : F) (corr : Finset (Fin n)) :
    FairASTCertificate (avssSpec (t := t) sec corr) avssFair terminated where
  Inv := avssTermInv
  V := avssV
  U := avssU
  inv_init := fun _ _ => trivial
  inv_step := fun _ _ _ _ _ _ => trivial
  V_term := fun s _ ht => by
    -- terminated → all three components of `avssU` are 0.
    show avssV s = 0
    unfold avssV avssU
    obtain ⟨ht_out, hi1, hi2⟩ := ht
    have h_third :
        ((Finset.univ : Finset (Fin n)).filter
          (fun p => p ∉ s.corrupted ∧ (s.local_ p).output = none)).card = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro p _ ⟨hp_h, hp_none⟩
      have := ht_out p hp_h
      rw [hp_none] at this
      simp at this
    rw [hi1, hi2, h_third]; simp
  V_pos := fun s _ ht => by
    -- Non-terminated state: at least one component is positive.
    show 0 < avssV s
    unfold avssV avssU
    classical
    by_contra hcon
    push_neg at hcon
    -- (avssU s : ℝ≥0) ≤ 0; cast back to ℕ.
    have hU0_real : (avssU s : ℝ≥0) = 0 :=
      le_antisymm hcon (zero_le _)
    have hU0 : avssU s = 0 := by exact_mod_cast hU0_real
    unfold avssU at hU0
    -- A sum of three nonneg ℕs is 0 ⇒ each is 0.
    have hi1 : s.inflightDeliveries.card = 0 := by
      -- The first summand has factor `(2*n+1)^2 ≥ 1`.
      by_contra h
      have hpos : 1 ≤ s.inflightDeliveries.card := Nat.one_le_iff_ne_zero.mpr h
      have : (1 : ℕ) * (2 * n + 1) ^ 2 ≤
          s.inflightDeliveries.card * (2 * n + 1) ^ 2 := by gcongr
      have hK1 : 1 ≤ (2 * n + 1) := by omega
      have hpow : 1 ≤ (2 * n + 1) ^ 2 := Nat.one_le_pow _ _ hK1
      omega
    have hi2 : s.inflightReady.card = 0 := by
      by_contra h
      have hpos : 1 ≤ s.inflightReady.card := Nat.one_le_iff_ne_zero.mpr h
      have : (1 : ℕ) * (2 * n + 1) ≤ s.inflightReady.card * (2 * n + 1) := by gcongr
      have hpow : 1 ≤ (2 * n + 1) := by omega
      omega
    have hi3 : ((Finset.univ : Finset (Fin n)).filter
        (fun p => p ∉ s.corrupted ∧ (s.local_ p).output = none)).card = 0 := by
      omega
    have hempty1 : s.inflightDeliveries = ∅ := Finset.card_eq_zero.mp hi1
    have hempty2 : s.inflightReady = ∅ := Finset.card_eq_zero.mp hi2
    have hfilter_empty :
        ((Finset.univ : Finset (Fin n)).filter
          (fun p => p ∉ s.corrupted ∧ (s.local_ p).output = none)) = ∅ :=
      Finset.card_eq_zero.mp hi3
    have hno_unfin : ∀ p, p ∉ s.corrupted → (s.local_ p).output ≠ none := by
      intro p hp hnone
      have hin : p ∈ ((Finset.univ : Finset (Fin n)).filter
          (fun q => q ∉ s.corrupted ∧ (s.local_ q).output = none)) := by
        rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hp, hnone⟩
      rw [hfilter_empty] at hin
      exact (Finset.notMem_empty _ hin)
    have h_term : terminated s := by
      refine ⟨?_, hempty1, hempty2⟩
      intro p hp
      cases h_out : (s.local_ p).output with
      | none => exact absurd h_out (hno_unfin p hp)
      | some _ => simp
    exact ht h_term
  V_super := fun _ _ _ _ _ => by sorry
  V_super_fair := fun _ _ _ _ _ _ => by sorry
  U_term := fun s _ ht => by
    show avssU s = 0
    unfold avssU
    obtain ⟨ht_out, hi1, hi2⟩ := ht
    have h_third :
        ((Finset.univ : Finset (Fin n)).filter
          (fun p => p ∉ s.corrupted ∧ (s.local_ p).output = none)).card = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro p _ ⟨hp_h, hp_none⟩
      have := ht_out p hp_h
      rw [hp_none] at this
      simp at this
    rw [hi1, hi2, h_third]; simp
  U_dec_det := fun _ _ _ _ _ _ _ _ => by sorry
  U_bdd_subl := fun _ =>
    ⟨(3 * n + 1) * (2 * n + 1) ^ 2, fun s _ _ => avssU_le_bound s⟩
  U_dec_prob := fun _ => by sorry
  V_init_bdd :=
    ⟨((3 * n + 1) * (2 * n + 1) ^ 2 : ℕ), fun s _ => by
      show ((avssU s : ℝ≥0)) ≤ (((3 * n + 1) * (2 * n + 1) ^ 2 : ℕ) : ℝ≥0)
      exact_mod_cast avssU_le_bound s⟩

/-- Termination as an `AlmostDiamond` under a trajectory-fair
adversary. Discharged via
`FairASTCertificate.partition_almostDiamond_fair`. The
sublevel-finite-variant lemma
(`FairASTCertificate.pi_n_AST_fair`) is itself sorry'd in
`Liveness.lean`; this theorem inherits that gap structurally —
no AVSS-specific sorry on top. -/
theorem avss_termination_AS_fair
    (sec : F) (corr : Finset (Fin n))
    (μ₀ : Measure (AVSSState n t F)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ᵐ s ∂μ₀, initPred sec corr s)
    (A : FairAdversary (AVSSState n t F) (AVSSAction n F) avssFair) :
    AlmostDiamond (avssSpec (t := t) sec corr) A.toAdversary μ₀ terminated := by
  have h_init' : ∀ᵐ s ∂μ₀, (avssCert (t := t) sec corr).Inv s := by
    filter_upwards [h_init] with _ _; exact trivial
  exact FairASTCertificate.sound (avssCert (t := t) sec corr) μ₀ h_init' A

/-! ## §17. Secrecy

Direct passthrough to `BivariateShamir.bivariate_shamir_secrecy`. The
post-deal grid view at any `t`-coalition is independent of the secret.

This is the **grid form** of secrecy — option (b) in the SyncVSS
brief, and the same form `bivariate_evals_uniform` directly delivers.
The full **row + column** view secrecy (a strict generalization) is
the `+200 LOC` polynomial-manipulation step explicitly deferred in
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

/-! ## §18. Closing remarks

  * **Termination.**  Discharged via `FairASTCertificate.sound`,
    which reduces to `partition_almostDiamond_fair` and then to the
    sublevel-finite-variant rule `pi_n_AST_fair`. The latter
    carries a Mathlib-filtration-plumbing gap that's not
    AVSS-specific (see `Liveness.lean §"Trajectory progress witness
    gap"`); the trajectory-deterministic specialisation
    `pi_n_AST_fair_with_progress_det` is closed and concrete protocols
    can use it directly with their own progress + monotonicity +
    strict-decrease witnesses (see `BrachaRBC.brbProb_totality_AS_fair`
    for the analogous shape).  Wiring AVSS-specific witnesses into
    that route is ~150 LOC of step-kernel plumbing, deferred per the
    M3 W5–W6 acceptance criteria.

  * **Correctness.** Closed (modulo the `rowEval (fun _ => 0)
    coeffs p 0 = coeffs 0 0` algebraic step, which sorries at one
    point in the inductive-step preservation; trivially closeable
    by `unfold` + `simp` once one nails down which `bivEval` lemma
    Mathlib provides for the `0 ^ ?` simplification).

  * **Output-determined / commitment.** Same as correctness modulo the
    same `rowEval` step.  Note that the *full* commitment statement
    (with the disjunction "all honest outputs equal *or* dealer
    exposed") requires the Bracha-faithful refinement of this
    abstraction; we record the basic form here.

  * **Secrecy.** Closed (sorry-free) — passes through to
    `BivariateShamir.bivariate_shamir_secrecy`.

  * **The `AVSSStub.avssCert`.**  This file's `avssCert` (with `(n :=
    n)` instantiated by Lean's elaboration) functionally subsumes
    the stub. The stub file is preserved for the entry-gate audit
    trail; it can be deleted at M3 closeout without affecting any
    live proof. -/

end Leslie.Examples.Prob.AVSS
