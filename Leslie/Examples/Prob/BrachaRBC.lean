/-
M2 W3 — Bracha Reliable Broadcast as a `ProbActionSpec`.

This module models the Bracha Byzantine Reliable Broadcast protocol
(`n` parties, ≤ `f` Byzantine faults, `n > 3f`) as a
`Leslie.Prob.ProbActionSpec` and states its three classical safety/
liveness properties on top of `AlmostBox` / `AlmostDiamond` against
`traceDist`.

Because Bracha is fully deterministic, every `effect` is a Dirac
(`PMF.pure`) on the deterministic next-state. The randomized layer
is therefore "vacuous" for this protocol — the exercise is to nail
down the `Adversary` / `Trace` / corruption modeling end-to-end
against a real distributed protocol, so the same top-level
statements port cleanly when later protocols (AVSS, common coin)
actually flip coins.

## Status (M2 W3 polish)

  * §1 `brbStep` — a deterministic next-state function mirroring
    every case of the protocol. **Closed.**
  * §2 `brbProb` — the probabilistic spec built from `brbStep`
    via `PMF.pure`. **Closed (definitional).**
  * §3 `brbProb_step_pure` — bridge lemma: each step is a Dirac on
    `brbStep`. **Closed.**
  * §4 `brbProb_fires_iff` — bridge expressing that an enabled
    action's next-state is uniquely `brbStep`. **Closed.**
  * §5 `brbProb_budget_AS` — corruption budget invariant lifted to
    `AlmostBox`. **Carries one `sorry`** on the trace-AE step (the
    `traceDist`-support → step-relation bridge, which is not yet
    pinned down in `Leslie/Prob/Refinement.lean`). The structural
    side (deterministic step preserves the budget) IS closed in §5.1.
  * §6 `brbProb_validity_AS`, §7 `brbProb_agreement_AS`,
    §8 `brbProb_totality_AS_fair` — same shape as §5; each carries
    a `sorry` for the same reason and a TODO. The interesting
    safety / liveness contents are already proved deterministically
    in `Leslie/Examples/ByzantineReliableBroadcast.lean` upstream.

## Deviation from the brief

The brief asks to `import Leslie.Examples.ByzantineReliableBroadcast`
and `open ByzantineReliableBroadcast` to reuse types verbatim.
**That file currently has 24 pre-existing compile errors** in its
liveness section (lines 1611+), all `rw` failures stemming from a
`Nat` simp-normal-form change in the upgrade to Lean 4.27.0 / mathlib
v4.27.0 (e.g. `0 + (k'+1)` is now normalized to `k'+1+0` instead of
`0 + (k'+1)`, breaking ~20 explicit `rw [show 0 + ... = ... from …]`
forms in `stable_or_corrupt`, `voted_stable`, `*_stable`,
`vote_msg_tracking`, `wf_*`, etc.). Since the brief restricts edits
to `Leslie/Examples/Prob/BrachaRBC.lean`, and the broken section
prevents the Bracha file from being imported at all, I redeclare
the protocol types and helpers verbatim in this file, with attribution
comments pointing to the upstream definitions.

The redeclared declarations are:
  * `MsgType`, `Message`, `LocalState`, `State`, `Action`
    (structurally identical to upstream).
  * `isCorrect`, `countEchoRecv`, `countVoteRecv`, `echoThreshold`,
    `voteThreshold`, `returnThreshold`, `LocalState.init`.
  * The `brbStep` deterministic next-state function (§1, new).
  * The probabilistic spec `brbProb` (§2, new).

The brief's `brb` (relational) and the deterministic safety
proofs `brb_validity`, `brb_agreement`, `totality`, `brb_inv`,
`brb_inv_init`, `brb_inv_step`, `brb_fairness` are *not*
redeclared here: the trace-AE-bridge gap means we wouldn't be
able to use them anyway (§5–§8 sorry on the bridge step,
the deterministic content is left to a future M2 W4 / M3 W1
generic lemma in `Leslie/Prob/Refinement.lean`).

Once the upstream `ByzantineReliableBroadcast.lean` is repaired
(which is a 1-line-per-error mechanical fix — change
`0 + (k' + 1)` to `k' + 1 + 0` in each broken `rw`), this file
should be migrated to `import Leslie.Examples.ByzantineReliableBroadcast`
and the local redeclarations removed.

## Typeclass setup

To run `traceDist` on `(State n Value, Action n Value)` we need
both types `Countable` plus a `MeasurableSpace` /
`MeasurableSingletonClass`. The `State` carries function-valued
fields like `Fin n → LocalState n Value`, `Message n Value → Bool`,
and a `Value → Bool` field on `LocalState` (`voted`); these are not
countable when `Value` is arbitrary. We therefore add
`[Fintype Value]` (alongside `[DecidableEq Value]`) on theorems that
use `traceDist` / `AlmostBox` / `AlmostDiamond`. Concrete uses in
M3+ instantiate with `Value = Fin k`, so this is non-binding.

Per implementation plan v2.2 §M2 W3 + design plan v2.2
§"Probabilistic refinement on a real protocol".
-/

import Leslie.Prob.Action
import Leslie.Prob.Adversary
import Leslie.Prob.Trace
import Leslie.Prob.Refinement
import Leslie.Prob.PMF
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Countable.Defs

namespace Leslie.Prob.Examples.BrachaRBC

open Leslie.Prob MeasureTheory

/-! ## §0. Protocol types (local redeclaration)

Mirror of `Leslie.Examples.ByzantineReliableBroadcast` types — see
the file header for why we redeclare here. -/

/-- Message type: `init`, `echo`, or `vote`. -/
inductive MsgType where
  | init | echo | vote
  deriving DecidableEq, Fintype

/-- A point-to-point message in the network buffer. -/
structure Message (n : Nat) (Value : Type) where
  src : Fin n
  dst : Fin n
  type : MsgType
  val : Value
  deriving DecidableEq

/-- Per-process local state. -/
structure LocalState (n : Nat) (Value : Type) where
  /-- `sent dst t v = true` iff this process has sent message (t, v) to dst. -/
  sent : Fin n → MsgType → Value → Bool
  /-- Value received via SEND from the designated sender (at most one). -/
  sendRecv : Option Value
  /-- Received ECHO(v) from process j (one per source per value). -/
  echoRecv : Fin n → Value → Bool
  /-- Received VOTE(v) from process j (one per source per value). -/
  voteRecv : Fin n → Value → Bool
  /-- Value echoed (at most one). -/
  echoed : Option Value
  /-- `voted v = true` iff this process has voted for value v. -/
  voted : Value → Bool
  /-- Value returned (at most one). -/
  returned : Option Value

/-- Global state: per-process local states, network buffer, list of
corrupted processes. -/
structure State (n : Nat) (Value : Type) where
  local_ : Fin n → LocalState n Value
  buffer : Message n Value → Bool
  corrupted : List (Fin n)

/-- Action labels. -/
inductive Action (n : Nat) (Value : Type) where
  | corrupt (i : Fin n)
  | send (src dst : Fin n) (t : MsgType) (v : Value)
  | recv (src dst : Fin n) (t : MsgType) (v : Value)
  | doReturn (i : Fin n) (v : Value)

variable (n f : Nat) (Value : Type) [DecidableEq Value]

/-- A process is *correct* iff it is not in the corrupted list. -/
def isCorrect (s : State n Value) (p : Fin n) : Prop := p ∉ s.corrupted

/-- Count distinct sources from which ECHO(v) was received. -/
def countEchoRecv (ls : LocalState n Value) (v : Value) : Nat :=
  (List.finRange n).filter (ls.echoRecv · v) |>.length

/-- Count distinct sources from which VOTE(v) was received. -/
def countVoteRecv (ls : LocalState n Value) (v : Value) : Nat :=
  (List.finRange n).filter (ls.voteRecv · v) |>.length

def echoThreshold : Nat := n - f
def voteThreshold : Nat := f + 1
def returnThreshold : Nat := n - f

/-- Default initial local state: empty/none/false everywhere. -/
def LocalState.init : LocalState n Value where
  sent := fun _ _ _ => false
  sendRecv := none
  echoRecv := fun _ _ => false
  voteRecv := fun _ _ => false
  echoed := none
  voted := fun _ => false
  returned := none

/-! ## §1. Deterministic next-state function `brbStep`

Each branch mirrors the relational `transition` field of the
deterministic `brb` `ActionSpec`. Where the gate is unmet, this
function is allowed to return arbitrary garbage (`s` itself —
i.e. a stutter); the spec's `gate` field hides those branches. -/

/-- The deterministic next-state function: given an `Action n Value`
and a pre-state `s`, return the unique post-state defined by the
deterministic relational transition of Bracha BRB.

The `sender` parameter is used by the `recv` case to gate
acceptance of `init` messages; `val` is unused at the next-state
level (it appears only in the gate of `send (.init …)` to enforce
"sender carries `val`"). -/
def brbStep (sender : Fin n) (_val : Value)
    (a : Action n Value) (s : State n Value) : State n Value :=
  match a with
  | .corrupt i =>
      { s with corrupted := i :: s.corrupted }
  | .send src dst t mv =>
      let msg : Message n Value := ⟨src, dst, t, mv⟩
      { s with
        buffer := fun m => if m = msg then true else s.buffer m
        local_ := fun p => if p = src then
          { s.local_ src with
            sent := fun d t' w =>
              if d = dst ∧ t' = t ∧ w = mv then true
              else (s.local_ src).sent d t' w
            echoed := match t with
              | .echo => if src ∉ s.corrupted then some mv
                         else (s.local_ src).echoed
              | _ => (s.local_ src).echoed
            voted := match t with
              | .vote => if src ∉ s.corrupted
                then fun w => if w = mv then true else (s.local_ src).voted w
                else (s.local_ src).voted
              | _ => (s.local_ src).voted }
          else s.local_ p }
  | .recv src dst t mv =>
      let msg : Message n Value := ⟨src, dst, t, mv⟩
      let ls := s.local_ dst
      { s with
        buffer := fun m => if m = msg then false else s.buffer m
        local_ := fun p => if p = dst then
          match t with
          | .init =>
              if src = sender ∧ ls.sendRecv = none
              then { ls with sendRecv := some mv }
              else ls
          | .echo =>
              if ls.echoRecv src mv = false
              then { ls with
                echoRecv := fun q w =>
                  if q = src ∧ w = mv then true else ls.echoRecv q w }
              else ls
          | .vote =>
              if ls.voteRecv src mv = false
              then { ls with
                voteRecv := fun q w =>
                  if q = src ∧ w = mv then true else ls.voteRecv q w }
              else ls
          else s.local_ p }
  | .doReturn i mv =>
      { s with
        local_ := fun p => if p = i
          then { s.local_ i with returned := some mv }
          else s.local_ p }

/-! ## Action gates

The same gate predicates as `(brb n f Value sender val).actions a` —
inlined so we don't need to import the relational spec. -/

/-- The gate predicate for action `a` in state `s`. Identical to
`((brb n f Value sender val).actions a).gate s` upstream. -/
def actionGate (sender : Fin n) (val : Value)
    (a : Action n Value) (s : State n Value) : Prop :=
  match a with
  | .corrupt i =>
      isCorrect n Value s i ∧ s.corrupted.length + 1 ≤ f
  | .send src dst t mv =>
      src ∈ s.corrupted ∨
      (isCorrect n Value s src ∧ (s.local_ src).sent dst t mv = false ∧
        match t with
        | .init => src = sender ∧ mv = val
        | .echo =>
            (s.local_ src).echoed = some mv
            ∨ ((s.local_ src).echoed = none ∧ (s.local_ src).sendRecv = some mv)
        | .vote =>
            (s.local_ src).voted mv = true ∨
            countEchoRecv n Value (s.local_ src) mv ≥ echoThreshold n f ∨
            countVoteRecv n Value (s.local_ src) mv ≥ voteThreshold f)
  | .recv src dst t mv =>
      s.buffer ⟨src, dst, t, mv⟩ = true
  | .doReturn i mv =>
      isCorrect n Value s i ∧
      (s.local_ i).returned = none ∧
      countVoteRecv n Value (s.local_ i) mv ≥ returnThreshold n f

/-- The initial-state predicate: empty local states, empty buffer,
no corruptions. Identical to `(brb …).init` upstream. -/
def initPred (s : State n Value) : Prop :=
  (∀ p, s.local_ p = LocalState.init n Value) ∧
  (∀ m, s.buffer m = false) ∧
  s.corrupted = []

/-! ## §2. Probabilistic spec `brbProb`

Every `effect` is a Dirac on `brbStep`; the gate is the deterministic
gate from §0. -/

/-- The probabilistic Bracha BRB spec. -/
noncomputable def brbProb (sender : Fin n) (val : Value) :
    ProbActionSpec (State n Value) (Action n Value) where
  init := initPred n Value
  actions := fun a =>
    { gate := actionGate n f Value sender val a
      effect := fun s _ => PMF.pure (brbStep n Value sender val a s) }

/-! ## §3. Bridge lemma: step is a Dirac on `brbStep` -/

/-- When the gate holds, `(brbProb …).step a s` is `some (PMF.pure …)`. -/
@[simp] theorem brbProb_step_pure
    (sender : Fin n) (val : Value)
    (a : Action n Value) (s : State n Value)
    (h : actionGate n f Value sender val a s) :
    (brbProb n f Value sender val).step a s
      = some (PMF.pure (brbStep n Value sender val a s)) :=
  ProbActionSpec.step_eq_some h

/-- When the gate fails, `(brbProb …).step a s = none`. -/
theorem brbProb_step_none
    (sender : Fin n) (val : Value)
    (a : Action n Value) (s : State n Value)
    (h : ¬ actionGate n f Value sender val a s) :
    (brbProb n f Value sender val).step a s = none :=
  ProbActionSpec.step_eq_none h

/-! ## §4. Bridge: gate-determined uniqueness of `brbStep`

When the gate holds, `brbStep` is the unique post-state. Stated as
a ↔ to mirror the relational `fires` shape on the deterministic
side: `((brb …).actions a).fires s s'` would be exactly
`actionGate ∧ s' = brbStep …`. -/

theorem brbProb_fires_iff
    (sender : Fin n) (val : Value)
    (a : Action n Value) (s s' : State n Value) :
    (actionGate n f Value sender val a s ∧
      s' = brbStep n Value sender val a s) ↔
    (∃ μ, (brbProb n f Value sender val).step a s = some μ ∧
      μ = PMF.pure s') := by
  constructor
  · rintro ⟨hg, rfl⟩
    exact ⟨_, brbProb_step_pure n f Value sender val a s hg, rfl⟩
  · rintro ⟨μ, hstep, hμ⟩
    -- `step a s` is `some (PMF.pure (brbStep …))` iff gate holds.
    -- Otherwise it is `none`. Extract the gate by case analysis.
    by_cases hg : actionGate n f Value sender val a s
    · refine ⟨hg, ?_⟩
      have hstep' := brbProb_step_pure n f Value sender val a s hg
      rw [hstep] at hstep'
      have hμ' : μ = PMF.pure (brbStep n Value sender val a s) := by
        injection hstep'
      have hpure : PMF.pure s' = PMF.pure (brbStep n Value sender val a s) :=
        hμ.symm.trans hμ'
      -- `PMF.pure` is injective on its argument.
      have hsupp := congrArg (fun p : PMF (State n Value) => p.support) hpure
      simp [PMF.support_pure] at hsupp
      exact hsupp
    · exfalso
      have hnone := brbProb_step_none n f Value sender val a s hg
      rw [hnone] at hstep
      exact Option.some_ne_none μ hstep.symm

/-! ## §5. Corruption-budget invariant (AlmostBox formulation)

The deterministic step preserves `corrupted.length ≤ f` whenever the
gate holds. We lift this to an `AlmostBox` statement on the
probabilistic trace.

**Typeclass scope.** Lifting requires `Countable (State n Value)`
and `Countable (Action n Value)` (plus a `MeasurableSingletonClass`).
We add `[Fintype Value]` to make `LocalState n Value` and the
function-valued fields finite (hence countable). The discrete
σ-algebra (`⊤`) supplies a `MeasurableSingletonClass` for free. -/

section AlmostBox

variable [Fintype Value]

-- Discrete `MeasurableSpace` / `MeasurableSingletonClass` /
-- `Countable` instances on the protocol's state / action carriers.
-- With `Fintype Value` plus `DecidableEq Value`, both types are
-- inductively built from finite/countable components.

instance : MeasurableSpace (State n Value) := ⊤
instance : MeasurableSingletonClass (State n Value) := ⟨fun _ => trivial⟩
instance : MeasurableSpace (Action n Value) := ⊤
instance : MeasurableSingletonClass (Action n Value) := ⟨fun _ => trivial⟩

/-- `Action n Value` is `Fintype` via the obvious sum-of-products
encoding. With `[Fintype Value]` (and `[DecidableEq Value]` from
the outer scope), `Fintype` follows. `Countable` is then derived
via `Fintype.toCountable`. -/
noncomputable instance : Fintype (Action n Value) := by
  classical
  exact Fintype.ofEquiv
    (Fin n ⊕ (Fin n × Fin n × MsgType × Value)
      ⊕ (Fin n × Fin n × MsgType × Value) ⊕ (Fin n × Value))
    { toFun := fun
        | .inl i => .corrupt i
        | .inr (.inl ⟨src, dst, t, v⟩) => .send src dst t v
        | .inr (.inr (.inl ⟨src, dst, t, v⟩)) => .recv src dst t v
        | .inr (.inr (.inr ⟨i, v⟩)) => .doReturn i v
      invFun := fun
        | .corrupt i => .inl i
        | .send src dst t v => .inr (.inl ⟨src, dst, t, v⟩)
        | .recv src dst t v => .inr (.inr (.inl ⟨src, dst, t, v⟩))
        | .doReturn i v => .inr (.inr (.inr ⟨i, v⟩))
      left_inv := fun
        | .inl _ => rfl
        | .inr (.inl _) => rfl
        | .inr (.inr (.inl _)) => rfl
        | .inr (.inr (.inr _)) => rfl
      right_inv := fun
        | .corrupt _ => rfl
        | .send _ _ _ _ => rfl
        | .recv _ _ _ _ => rfl
        | .doReturn _ _ => rfl }

instance : Countable (Action n Value) := Finite.to_countable

/-- `Message n Value` is `Fintype`: a 4-field record with finite
fields under `[Fintype Value]`. -/
noncomputable instance : Fintype (Message n Value) := by
  classical
  exact Fintype.ofEquiv (Fin n × Fin n × MsgType × Value)
    { toFun := fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩
      invFun := fun m => ⟨m.src, m.dst, m.type, m.val⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- `LocalState n Value` is `Fintype`: a 7-fold record, every field
finite under `[Fintype Value]`. -/
noncomputable instance : Fintype (LocalState n Value) := by
  classical
  exact Fintype.ofEquiv
    ((Fin n → MsgType → Value → Bool) × Option Value
      × (Fin n → Value → Bool) × (Fin n → Value → Bool)
      × Option Value × (Value → Bool) × Option Value)
    { toFun := fun ⟨a, b, c, d, e, f, g⟩ =>
        ⟨a, b, c, d, e, f, g⟩
      invFun := fun ls =>
        (ls.sent, ls.sendRecv, ls.echoRecv, ls.voteRecv,
         ls.echoed, ls.voted, ls.returned)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- `State n Value` is `Countable`. `local_` and `buffer` are
finite-domain functions into finite types (hence `Fintype` and
`Countable`); `corrupted` is a `List (Fin n)` (countable). -/
instance : Countable (State n Value) := by
  classical
  let e : ((Fin n → LocalState n Value) × (Message n Value → Bool)
            × List (Fin n)) ≃ State n Value :=
    { toFun := fun p => ⟨p.1, p.2.1, p.2.2⟩
      invFun := fun s => (s.local_, s.buffer, s.corrupted)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Countable.of_equiv _ e

/-! ### §5.1 Deterministic budget preservation

A pure-step lemma: `actionGate` plus `corrupted.length ≤ f` implies
`(brbStep a s).corrupted.length ≤ f`. -/

omit [Fintype Value] in
theorem brbStep_preserves_budget
    (sender : Fin n) (val : Value)
    (a : Action n Value) (s : State n Value)
    (hgate  : actionGate n f Value sender val a s)
    (hbudget : s.corrupted.length ≤ f) :
    (brbStep n Value sender val a s).corrupted.length ≤ f := by
  cases a with
  | corrupt i =>
      -- gate forces `corrupted.length + 1 ≤ f`.
      simp only [brbStep, List.length_cons]
      have : s.corrupted.length + 1 ≤ f := hgate.2
      omega
  | send src dst t mv =>
      -- send doesn't touch `corrupted`.
      simp only [brbStep]
      exact hbudget
  | recv src dst t mv =>
      simp only [brbStep]
      exact hbudget
  | doReturn i mv =>
      simp only [brbStep]
      exact hbudget

omit [DecidableEq Value] [Fintype Value] in
/-- The initial-state predicate implies the budget invariant.
Trivial: `corrupted = []`. -/
theorem initPred_budget
    (s : State n Value) (h : initPred n Value s) :
    s.corrupted.length ≤ f := by
  have : s.corrupted = [] := h.2.2
  simp [this]

/-! ### §5.2 AlmostBox lift -/

/-- Corruption-budget AlmostBox invariant on the probabilistic
trace. Initial measure is concentrated on `initPred` states (i.e.,
`brbProb`-init states); `initPred_budget` gives the budget at step
0, and `brbStep_preserves_budget` gives the inductive step.

**Sorry note (M2 W3 polish).** The remaining gap is the standard
"trace measure → almost-sure invariant under deterministic step
kernel" lemma: under our `stepKernel`, a deterministic effect
(`PMF.pure`) commutes with the kernel pushforward, so an inductive
property of `brbStep` lifts to an `AlmostBox` on the trace. This
generic bridge is not yet implemented in
`Leslie/Prob/Refinement.lean`. The expected shape is

```
AlmostBox_of_pure_inductive
    (h_init : ∀ s, μ₀ {s} ≠ 0 → P s)
    (h_pure : ∀ a s h, (spec.actions a).effect s h = PMF.pure (det_step a s))
    (h_step : ∀ a s, (spec.actions a).gate s → P s → P (det_step a s)) :
  AlmostBox spec A μ₀ P
```

Once that lemma is added, this proof is one line. -/
theorem brbProb_budget_AS
    (sender : Fin n) (val : Value)
    (μ₀ : Measure (State n Value)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ s, μ₀ {s} ≠ 0 → initPred n Value s)
    (A : Adversary (State n Value) (Action n Value)) :
    AlmostBox (brbProb n f Value sender val) A μ₀
      (fun s => s.corrupted.length ≤ f) := by
  -- The deterministic ingredients are already here:
  --   * `initPred_budget` gives the budget at every initial state.
  --   * `brbStep_preserves_budget` gives the inductive step.
  -- The missing piece is the trace-measure lift; see file header.
  sorry

/-! ## §6. Validity (AlmostBox formulation)

Validity = "if the sender is correct, no honest party returns a
value other than `val`". The deterministic content is upstream
`brb_validity` (in `Leslie/Examples/ByzantineReliableBroadcast.lean`).
For the probabilistic side we constrain the adversary's `corrupt`
set to exclude `sender` (this matches the deterministic hypothesis
`□⌜ isCorrect sender ⌝`). -/

/-- Validity, lifted to an `AlmostBox` on the probabilistic trace.

**Sorry note.** Same gap as `brbProb_budget_AS`: the trace-AE
bridge from a deterministic-step inductive invariant to
`AlmostBox`. -/
theorem brbProb_validity_AS
    (sender : Fin n) (val : Value)
    (μ₀ : Measure (State n Value)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ s, μ₀ {s} ≠ 0 → initPred n Value s)
    (A : Adversary (State n Value) (Action n Value))
    (_h_sender_honest : (sender.val : PartyId) ∉ A.corrupt) :
    AlmostBox (brbProb n f Value sender val) A μ₀
      (fun s => isCorrect n Value s sender →
        ∀ p v, isCorrect n Value s p →
          (s.local_ p).returned = some v → v = val) := by
  -- TODO(M2 W3 polish): close via `AlmostBox_of_pure_inductive` plus
  -- the deterministic invariant from upstream `brb_inv`
  -- (conjunct 6: `local_consistent` under `isCorrect sender`).
  sorry

/-! ## §7. Agreement (AlmostBox formulation)

Agreement = "any two honest returners return the same value". -/

/-- The agreement state predicate, mirroring upstream `agreement`. -/
def agreementPred (s : State n Value) : Prop :=
  ∀ p q vp vq,
    isCorrect n Value s p → isCorrect n Value s q →
    (s.local_ p).returned = some vp → (s.local_ q).returned = some vq →
    vp = vq

/-- Agreement, lifted to an `AlmostBox` on the probabilistic trace.

**Sorry note.** Same trace-AE bridge gap. The deterministic content
is upstream `brb_agreement`, threaded through `brb_inv` conjuncts
7–9 plus the echo-quorum-intersection lemma. -/
theorem brbProb_agreement_AS
    (sender : Fin n) (val : Value)
    (_hn : n > 3 * f)
    (μ₀ : Measure (State n Value)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ s, μ₀ {s} ≠ 0 → initPred n Value s)
    (A : Adversary (State n Value) (Action n Value)) :
    AlmostBox (brbProb n f Value sender val) A μ₀
      (agreementPred n Value) := by
  -- TODO(M2 W3 polish): close via the same `AlmostBox_of_pure_inductive`
  -- bridge against the upstream invariant `brb_inv` (conjuncts 7–9
  -- imply agreement directly, as in upstream `brb_agreement`).
  sorry

/-! ## §8. Totality (AlmostDiamond formulation, fair adversary)

Totality = "if any honest party returns, every honest party
eventually returns". This is a liveness property; the
deterministic counterpart is upstream `totality` under
`brb_fairness`.

We package fairness probabilistically: `FairAdversary` carries a
`FairnessAssumptions` witness; the concrete fairness predicate
matching `brb_fairness` is a translation of "every action that is
continuously enabled fires eventually" into an AE-trace statement. -/

/-- A placeholder fairness-assumption record matching upstream
`brb_fairness`. The real definition translates the deterministic
`□◇` over the next relation into an AE-trace
`∀ᵐ ω, ∀ i, (continuously enabled → fires)` condition.

For M2 W3 we leave this as a stub: any adversary trivially
satisfies it. The right body lands in M3 alongside the AVSS
liveness proof, where the same shape is needed to lift `wf_*`
lemmas. -/
def brbFair (_sender : Fin n) (_val : Value) :
    FairnessAssumptions (State n Value) (Action n Value) where
  fair_actions := Set.univ
  isWeaklyFair := fun _ => True

/-- Totality, lifted to an `AlmostDiamond` on the probabilistic
trace, under a fair adversary.

**Sorry note.** Liveness lifting is more delicate than safety: the
deterministic upstream `totality` has the form `(∃ p, returned p =
some v) ↝ (returned r ≠ none ∨ ¬ isCorrect r)`, a `↝` (leads-to)
between two state predicates. The AE-trace counterpart is
"AE, `(∃ n, P (ω n)) → (∃ m ≥ n, Q (ω m))`" on `traceDist`. The
right `Refinement` lemma to bridge this from the deterministic
`pred_implies` is the M2 W4 / M3 W1 task — currently deferred. -/
theorem brbProb_totality_AS_fair
    (sender : Fin n) (val : Value)
    (_hn : n > 3 * f)
    (μ₀ : Measure (State n Value)) [IsProbabilityMeasure μ₀]
    (h_init : ∀ s, μ₀ {s} ≠ 0 → initPred n Value s)
    (A : FairAdversary (State n Value) (Action n Value)
            (brbFair n Value sender val))
    (r : Fin n) (v : Value)
    (_h_someone_returned :
      AlmostDiamond (brbProb n f Value sender val) A.toAdversary μ₀
        (fun s => ∃ p, (s.local_ p).returned = some v)) :
    AlmostDiamond (brbProb n f Value sender val) A.toAdversary μ₀
      (fun s => (s.local_ r).returned ≠ none ∨ ¬ isCorrect n Value s r) := by
  -- TODO(M2 W3 polish): close via a generic `AlmostDiamond_of_leads_to`
  -- bridge against upstream `totality` + `brb_fairness`.
  sorry

end AlmostBox

end Leslie.Prob.Examples.BrachaRBC
