/-
M2 W1 — `Adversary`: full version.

Promoted from the M1 stub with:
  * `corrupt : Set PartyId` — static corruption set.
  * `FairnessAssumptions` — predicate carving out fair adversaries.
  * `FairAdversary spec F` — bundle adversary + fairness witness.

Per implementation plan v2.2 §M2 W1 + design plan v2.2 §"Adversary,
scheduler, fairness".

The scheduler is **demonic and history-deterministic**: given the
visible history, the adversary picks an action (or `none` to
stutter). This matches the standard MDP / adversarial-randomization
encoding. Randomized schedulers are strictly more expressive but are
not needed for AST under fairness; deferred (see plan §"Open
questions").

Measurability conditions for kernel composition (needed when
`Trace.traceDist` lifts the adversary to a per-step Markov kernel)
land in `Trace.lean` rather than here, so this file remains
Mathlib-light.
-/

import Mathlib.Data.Set.Basic

namespace Leslie.Prob

/-- Party identifier. Concretely we use `ℕ`; protocols fix a finite
range (`Fin n`) and inject into `ℕ`. -/
abbrev PartyId : Type := ℕ

/-! ## Adversary -/

/-- A history-deterministic, demonic scheduler with a static
corruption set.

  * `schedule` — given the visible trace prefix, choose an action
    label (or `none` to stutter).
  * `corrupt` — the set of corrupted parties; under static
    corruption, this is fixed at the start of the run. -/
structure Adversary (σ : Type*) (ι : Type*) where
  schedule : List (σ × Option ι) → Option ι
  corrupt  : Set PartyId

namespace Adversary

variable {σ ι : Type*}

/-- An adversary that schedules `i` immediately at the empty history,
with no corruption. Useful for trivial test cases. -/
def trivial (i : ι) : Adversary σ ι where
  schedule _ := some i
  corrupt   := ∅

/-- An adversary that always stutters. -/
def alwaysStutter : Adversary σ ι where
  schedule _ := none
  corrupt   := ∅

end Adversary

/-! ## Fairness -/

/-- Fairness assumptions: a set of fair-required action labels and a
predicate carving out which adversaries are weakly fair w.r.t. those
actions.

The convention: an adversary is *weakly fair* w.r.t. `fair_actions`
iff every action in `fair_actions` that becomes continuously enabled
along an execution is eventually fired. This is the temporal
predicate; concrete instantiations (e.g., for the M3 AVSS proof)
specialize `isWeaklyFair`. -/
structure FairnessAssumptions (σ : Type*) (ι : Type*) where
  fair_actions : Set ι
  isWeaklyFair : Adversary σ ι → Prop

/-- A fair adversary: bundle an adversary together with a witness
that it satisfies the fairness predicate.

Carrying the witness as a hard type-level component (rather than as
a temporal-side-condition on traces) means downstream theorems
quantify directly over `FairAdversary _ F`, simplifying the
statements of `FairASTCertificate.sound`-style results. -/
structure FairAdversary (σ : Type*) (ι : Type*)
    (F : FairnessAssumptions σ ι) where
  toAdversary : Adversary σ ι
  fair        : F.isWeaklyFair toAdversary

end Leslie.Prob
