/-
M1 W2 — `Adversary` stub.

A history-deterministic, demonic scheduler: given the visible
history, pick an action to fire (or `none` to stutter).

This is the *minimal* version sufficient for M1. The full M2 W1
version adds:

  * `corrupt : Set PartyId` — static corruption set.
  * `FairnessAssumptions` — predicate carving out fair adversaries.
  * `FairAdversary spec F` — bundle adversary + fairness witness.
  * Measurability conditions for composition with `Kernel.trajMeasure`.

Per implementation plan v2.2 §M1 W2 days 1-3.
-/

namespace Leslie.Prob

/-- A history-deterministic adversary: from the visible trace prefix,
return either an action label or `none` (stutter step). The history
shape is `List (σ × Option ι)` — an alternating sequence of states
and labels of fired actions (with `none` for stutter steps). -/
structure Adversary (σ : Type _) (ι : Type _) where
  schedule : List (σ × Option ι) → Option ι

end Leslie.Prob
