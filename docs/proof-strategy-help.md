# Proof Strategy Guide for Leslie

This document captures lessons from building invariant proofs for distributed protocols in Leslie.
The patterns here apply whenever you need to prove `invariant` holds for all reachable states of a
parameterized transition system.

---

## The Core Proof Structure

Every reachability proof has three pieces:

```
1. Reachable n s    (inductive definition)
2. strongInv_init   (invariant holds initially)
3. strongInv_step   (invariant preserved by every transition)
   └── for each action A: strongInv_preserved_A
```

The difficulty lives entirely in step 3. Everything below is about making step 3 tractable.

---

## Pattern 1: Frame Lemmas

**The problem**: Most invariant components are trivially preserved by most actions because the
action doesn't touch the relevant state fields. But without explicit frame lemmas, every sub-goal
requires a manual proof even when the answer is "nothing changed".

**The fix**: For each action, prove *what it does not change* as a single reusable lemma.

```lean
-- Define what each action modifies as a structure equality
lemma sendReqS_frame {s s' : MState n} {i : Fin n}
    (h : s' = { s with chan1 := setFn s.chan1 i { (s.chan1 i) with cmd := .reqS } }) :
    s'.cache = s.cache ∧ s'.chan2 = s.chan2 ∧ s'.chan3 = s.chan3 ∧
    s'.invSet = s.invSet ∧ s'.shrSet = s.shrSet ∧ s'.exGntd = s.exGntd ∧
    s'.curCmd = s.curCmd ∧ s'.memData = s.memData ∧ s'.auxData = s.auxData := by
  subst h; simp [setFn]
```

Then any invariant component that only reads `{cache, chan2, chan3, ...}` is discharged by:

```lean
exact ⟨..., by rw [(sendReqS_frame h).1, (sendReqS_frame h).2.1, ...]; exact hcomp, ...⟩
```

Or better, annotate each frame lemma as `@[simp]` so that `simp [sendReqS_frame h]` closes all
trivially-preserved components at once.

**Impact**: For an M-action × N-component proof matrix, frame lemmas can reduce the number of
hand-written proofs from M×N to roughly M + (non-trivial sub-goals), often a 5–10× reduction.

---

## Pattern 2: Hierarchical Invariant Decomposition

**The problem**: A flat conjunction of N unrelated predicates forces you to maintain all N
components in every action proof, even when an action only affects one group.

**The fix**: Group invariant components by which state fields they read. An action that only
modifies `chan1` trivially preserves every group that doesn't read `chan1`.

```lean
-- Group by read-set
def channelCoherence n s : Prop :=
  -- predicates that only read chan2 and chan3
  grantExcludesInvAck n s ∧ gntSExcludesInvAck n s ∧
  invAckClearsGrant n s ∧ chan3IsInvAck n s

def cacheBookkeeping n s : Prop :=
  -- predicates that only read cache, shrSet, exGntd
  exclusiveSelfClean n s ∧ cacheInShrSet n s

def controlCoherence n s : Prop :=
  -- predicates that read curCmd, invSet, exGntd
  invRequiresNonEmpty n s ∧ invClearsInvSet n s ∧ invSetImpliesClean n s

def fullInvariant n s : Prop :=
  coreInvariant n s ∧ channelCoherence n s ∧
  cacheBookkeeping n s ∧ controlCoherence n s
```

Then prove group-level frame theorems:
```lean
lemma channelCoherence_preserved_of_chan2_chan3_eq
    (h2 : s'.chan2 = s.chan2) (h3 : s'.chan3 = s.chan3)
    (hc : channelCoherence n s) : channelCoherence n s' := by
  simp_all [channelCoherence, grantExcludesInvAck, ...]
```

This reduces the M×N matrix to roughly M × (number of groups) for trivial cases.

---

## Pattern 3: Factored Action Predicates

**The problem**: When `next` is an existential over a large `match`, proof contexts become unwieldy.
Unfolding `next` leaves you deep inside nested match arms, making it hard to reuse lemmas.

**The fix**: Define each action as its own named predicate, then `next` is a disjunction:

```lean
def SendReqS (s s' : MState n) (i : Fin n) : Prop :=
  (s.chan1 i).cmd = .empty ∧ (s.cache i).state = .I ∧
  s' = { s with chan1 := setFn s.chan1 i { (s.chan1 i) with cmd := .reqS } }

def Next n s s' : Prop :=
  (∃ i, SendReqS s s' i) ∨ (∃ i, SendReqE s s' i) ∨ ...
```

Benefits:
- Each `strongInv_preserved_A` takes `SendReqS s s' i` as a clean typed hypothesis
- The assembly proof `strongInv_step` is a single `rcases` on the disjunction
- Frame lemmas are stated once per action predicate, reused everywhere

---

## Pattern 4: Automation with Aesop

Register group-level preservation lemmas as `aesop` rules so the trivial layer is fully automated:

```lean
@[aesop safe apply]
lemma channelCoherence_preserved_chan1_only
    (hframe : s'.chan2 = s.chan2 ∧ s'.chan3 = s.chan3)
    (hc : channelCoherence n s) : channelCoherence n s' := ...

@[aesop safe apply]
lemma cacheBookkeeping_preserved_chan_only
    (hframe : s'.cache = s.cache ∧ s'.shrSet = s.shrSet ∧ s'.exGntd = s.exGntd)
    (hb : cacheBookkeeping n s) : cacheBookkeeping n s' := ...
```

Then for simple actions: `aesop [sendReqS_frame h]` closes the entire preservation proof.

---

## Recommended File Layout

For any non-trivial protocol proof, split across files by concern:

```
Protocol/
  Model.lean          -- State, actions (as named predicates), Next, Spec
                      -- No proofs. This is the spec layer.
  FrameLemmas.lean    -- For each action: what fields change and what don't
                      -- All @[simp]. These are purely structural.
  Invariant.lean      -- Invariant definition, decomposed into groups
                      -- coreInvariant, channelCoherence, etc.
  InitProof.lean      -- fullInvariant holds for init states
  StepProof.lean      -- fullInvariant preserved by Next
                      -- Imports FrameLemmas; trivial cases close by simp
  Theorem.lean        -- Reachable, main safety theorem, derived corollaries
```

Benefits:
- `StepProof.lean` stays small because frame lemmas handle the bulk
- Each file fits comfortably in a context window
- Model changes only require updating `Model.lean` + the directly affected proofs
- The non-trivial proof content (the actual invariant reasoning) is concentrated
  in a small part of `StepProof.lean`, easy to audit

---

## The Key Mental Model

Think of each action as having a **modification footprint** (which fields it writes) and each
invariant component as having a **read footprint** (which fields it reads). Preservation is:

```
footprint(action) ∩ footprint(invariant_component) = ∅  →  trivially preserved
```

The goal of proof infrastructure is to make this disjointness check mechanical. Frame lemmas
encode the action footprint; grouping encodes the invariant footprint. Once both are explicit,
automation handles the trivial cases and only the non-trivial interactions remain.

In a well-structured protocol proof, the non-trivial interactions should be ~10–20% of the
total obligations. If you're hand-proving more than that, there's missing infrastructure.
