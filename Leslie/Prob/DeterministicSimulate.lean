/-
M3 Phase 10.1 — `DeterministicProbActionSpec` and the generic
`simulate*` machinery.

A *deterministic* probabilistic spec is one whose every per-step
effect is `PMF.pure (step a s)`: all randomness lives in `μ₀`
(the initial measure).  AVSS, BrachaRBC, SyncVSS, and AVSSAbstract
all fit this pattern.  Common-coin / random-oracle protocols do not.

Phase 10's plan (`AVSS-MODEL-NOTES.md` §14) promotes the inductive
AE-bridge from `AVSS.lean` §19.2 to a meta-theorem; this file is the
data foundation:

  * `DeterministicProbActionSpec` — the deterministic spec record.
  * `toProbActionSpec` — the adapter wrapping each step in `PMF.pure`.
  * `simulateNext` / `simulateRev` / `simulateTrace` — the generic
    deterministic simulation, taking a plain `Adversary σ ι` and
    reading only `D.gate`, `D.step`, and `A.schedule`.

Plus the structural simp lemmas (`_length`, `_ne_nil`, `_succ_eq`,
`_head_eq`, `_zero`) that PR 10.2 will use to prove the AE-bridge.

The shape mirrors the existing AVSS-specific definitions in
`AVSS.lean` §19.2 (`avssSimulateNext`, `avssSimulateRev`,
`avssSimulateTrace`); PR 10.3 will collapse those to one-line
instantiations of the generic versions.

No `traceDist` reasoning here — that's PR 10.2.  No measurability
typeclasses — they are imposed only at `Trace.traceDist` call sites
(matching `Action.lean` and `Adversary.lean`).
-/

import Leslie.Prob.Action
import Leslie.Prob.Adversary

namespace Leslie.Prob

/-! ## DeterministicProbActionSpec -/

/-- A deterministic state-machine spec: every action's effect is
`PMF.pure (step a s)`.  Strict subclass of `ProbActionSpec` covering
all protocols whose only randomness lives in `μ₀`.

Mirrors `ProbActionSpec` minus the per-action `PMF` — the generic
`toProbActionSpec` adapter wraps each `step a s` in `PMF.pure`. -/
structure DeterministicProbActionSpec (σ : Type*) (ι : Type*) where
  /-- Initial-state predicate (inherited verbatim by `toProbActionSpec`). -/
  init : σ → Prop
  /-- Per-action gate, mirroring `ProbGatedAction.gate`. -/
  gate : ι → σ → Prop
  /-- Per-action deterministic next-state.  `toProbActionSpec` lifts this
  to `PMF.pure (step a s)`. -/
  step : ι → σ → σ

namespace DeterministicProbActionSpec

variable {σ ι : Type*}

/-! ### Adapter to `ProbActionSpec`

Wrap each deterministic `step` in `PMF.pure` to obtain a
`ProbActionSpec`.  Three definitional simp lemmas expose the
projections so downstream proofs can rewrite freely. -/

/-- Lift a deterministic spec to a `ProbActionSpec` by wrapping each
step in `PMF.pure`. -/
noncomputable def toProbActionSpec (D : DeterministicProbActionSpec σ ι) :
    ProbActionSpec σ ι where
  init    := D.init
  actions := fun a =>
    { gate   := D.gate a
      effect := fun s _ => PMF.pure (D.step a s) }

@[simp] theorem toProbActionSpec_init (D : DeterministicProbActionSpec σ ι) :
    D.toProbActionSpec.init = D.init := rfl

@[simp] theorem toProbActionSpec_actions_gate
    (D : DeterministicProbActionSpec σ ι) (a : ι) (s : σ) :
    (D.toProbActionSpec.actions a).gate s = D.gate a s := rfl

@[simp] theorem toProbActionSpec_actions_effect
    (D : DeterministicProbActionSpec σ ι) (a : ι) (s : σ)
    (h : D.gate a s) :
    (D.toProbActionSpec.actions a).effect s h = PMF.pure (D.step a s) := rfl

end DeterministicProbActionSpec

/-! ## Generic deterministic simulation

Mirrors `AVSS.lean` §19.2's `avssSimulateNext` / `avssSimulateRev` /
`avssSimulateTrace` but reads only the deterministic spec's `gate`
and `step`, and the plain `Adversary.schedule`.  PR 10.3 will rewrite
the AVSS-specific versions as one-line wrappers of these. -/

section Simulate

open Classical

variable {σ ι : Type*}

/-- One step of the deterministic simulation, given the previous
reverse-order prefix.  If the prefix's head fires the schedule's
chosen action and that action's gate holds, apply `D.step`; otherwise
stutter at the current state.

The `fallback` argument plugs the unreachable `prev = []` case for
Lean totality; under the `simulateRev` recursion below the prefix is
always non-empty (`simulateRev_ne_nil`). -/
noncomputable def simulateNext
    (D : DeterministicProbActionSpec σ ι) (A : Adversary σ ι)
    (fallback : σ) (prev : List (σ × Option ι)) : σ × Option ι :=
  let s_k : σ := (prev.head?.map Prod.fst).getD fallback
  match A.schedule prev.reverse with
  | none   => (s_k, (none : Option ι))
  | some i =>
      if D.gate i s_k then (D.step i s_k, some i)
      else (s_k, (none : Option ι))

/-- Reverse-order simulated trace prefix at step `k`.  Returns a list
of length `k+1` ordered as `[step k, step k-1, …, step 0]`. -/
noncomputable def simulateRev
    (D : DeterministicProbActionSpec σ ι) (A : Adversary σ ι)
    (s_0 : σ) : ℕ → List (σ × Option ι)
  | 0     => [(s_0, (none : Option ι))]
  | (k+1) =>
    let prev := simulateRev D A s_0 k
    simulateNext D A s_0 prev :: prev

/-- The simulated trace at step `k`: extract the head of the
reverse-order prefix list. -/
noncomputable def simulateTrace
    (D : DeterministicProbActionSpec σ ι) (A : Adversary σ ι)
    (s_0 : σ) (k : ℕ) : σ × Option ι :=
  match simulateRev D A s_0 k with
  | []     => (s_0, (none : Option ι))  -- unreachable; see `simulateRev_ne_nil`
  | x :: _ => x

/-! ### Structural simp lemmas

These mirror the AVSS-specific lemmas (`avssSimulateRev_length`,
`avssSimulateRev_ne_nil`, `avssSimulateTrace_zero`,
`avssSimulateTrace_succ_eq`, `avssSimulateRev_head_eq`) in
`AVSS.lean` §19.2.  Proofs are by definitional reduction or short
induction on `k`. -/

theorem simulateRev_length
    (D : DeterministicProbActionSpec σ ι) (A : Adversary σ ι)
    (s_0 : σ) (k : ℕ) :
    (simulateRev D A s_0 k).length = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [simulateRev, ih]

theorem simulateRev_ne_nil
    (D : DeterministicProbActionSpec σ ι) (A : Adversary σ ι)
    (s_0 : σ) (k : ℕ) :
    simulateRev D A s_0 k ≠ [] := by
  intro h
  have := simulateRev_length D A s_0 k
  rw [h] at this; simp at this

theorem simulateRev_succ
    (D : DeterministicProbActionSpec σ ι) (A : Adversary σ ι)
    (s_0 : σ) (k : ℕ) :
    simulateRev D A s_0 (k+1) =
      simulateNext D A s_0 (simulateRev D A s_0 k) ::
        simulateRev D A s_0 k := rfl

@[simp] theorem simulateTrace_zero
    (D : DeterministicProbActionSpec σ ι) (A : Adversary σ ι)
    (s_0 : σ) :
    simulateTrace D A s_0 0 = (s_0, (none : Option ι)) := rfl

@[simp] theorem simulateTrace_zero_fst
    (D : DeterministicProbActionSpec σ ι) (A : Adversary σ ι)
    (s_0 : σ) :
    (simulateTrace D A s_0 0).1 = s_0 := rfl

@[simp] theorem simulateTrace_zero_snd
    (D : DeterministicProbActionSpec σ ι) (A : Adversary σ ι)
    (s_0 : σ) :
    (simulateTrace D A s_0 0).2 = (none : Option ι) := rfl

/-- Successor-step structural identity: the state-action pair at step
`k+1` equals `simulateNext` applied to the reverse-order prefix at
step `k`. -/
theorem simulateTrace_succ_eq
    (D : DeterministicProbActionSpec σ ι) (A : Adversary σ ι)
    (s_0 : σ) (k : ℕ) :
    simulateTrace D A s_0 (k+1) =
      simulateNext D A s_0 (simulateRev D A s_0 k) := by
  simp [simulateTrace, simulateRev]

/-- The state at step `k` of the simulate equals the head of the
reverse-prefix list (when nonempty). -/
theorem simulateRev_head_eq
    (D : DeterministicProbActionSpec σ ι) (A : Adversary σ ι)
    (s_0 : σ) (k : ℕ) :
    (simulateRev D A s_0 k).head?.map Prod.fst =
      some (simulateTrace D A s_0 k).1 := by
  unfold simulateTrace
  cases h : simulateRev D A s_0 k with
  | nil       => exact absurd h (simulateRev_ne_nil D A s_0 k)
  | cons x xs => simp

end Simulate

end Leslie.Prob
