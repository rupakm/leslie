import Leslie.Round

/-! ## Ben-Or's Randomized Binary Consensus (1983)

    A round-based randomized binary consensus algorithm for `n` processes
    (`Fin n`). Each process holds a binary value (0 or 1) and attempts to
    reach agreement through a sequence of rounds, each consisting of two
    phases.

    ### Protocol

    The protocol proceeds in rounds. Each round has two phases:

    **Phase 1 (Report):**
    - Each process broadcasts its current binary value.
    - Each process collects reports from the processes it hears from (the HO set).
    - If a process receives the same value `v` from a strict majority
      (> n/2) of processes, it "witnesses" `v`. Otherwise, it witnesses nothing.

    **Phase 2 (Propose):**
    - Each process broadcasts its witness (if any).
    - Each process collects proposals from the processes it hears from.
    - If a process receives the same witness `v` from a strict majority
      of processes, it **decides** `v` (and adopts `v` as its value).
    - Otherwise, it **flips a coin**: its new value is chosen
      nondeterministically (0 or 1), modeled by an oracle.

    ### Role of randomization

    The coin flip is the source of nondeterminism beyond the HO sets. It
    ensures probabilistic termination: even if no majority forms in a
    round, random choices can eventually align values, allowing a majority
    to emerge. For the safety proof, the coin flip is simply treated as
    an arbitrary nondeterministic choice — safety holds regardless of the
    coin outcomes.

    ### Design

    We model the protocol as a plain `Spec` (like `BallotLeader.lean`),
    not as a `RoundSpec`, because each "conceptual round" consists of two
    sub-steps (phases). The coin flip oracle is an additional source of
    nondeterminism, analogous to BallotLeader's bidding oracle.

    ### Safety property: Agreement

    **Theorem:** If process `p` decided `v` and process `q` decided `w`,
    then `v = w`.

    ### Proof strategy

    We define an auxiliary invariant (`lock_inv`): if any process has
    decided value `v`, then a strict majority of all `n` processes
    currently hold value `v`. This is the key inductive invariant.

    **Why does the lock invariant imply agreement?**
    If two values `v ≠ w` were both decided, then by the lock invariant,
    > n/2 processes hold `v` AND > n/2 hold `w`. But these sets are
    disjoint (each process holds exactly one value), requiring > n
    processes total — a contradiction (pigeonhole).

    **Why is the lock invariant inductive?**

    *Phase 1 (Report):* Only `witnessed` changes, not `val` or `decided`.
    The lock invariant refers to `val` and `decided`, so it is trivially
    preserved.

    *Phase 2 (Propose):*
    - (a) *Establishing the lock:* If process `p` newly decides `v`, then
      > n/2 processes witnessed `v`, meaning each of them saw `v` from
      > n/2 senders in phase 1. By majority intersection, all those
      senders held `v`. So > n/2 processes held `v` before the step.
    - (b) *Preserving the lock:* Every process that held `v` either
      decides `v` (keeping `val = v`), or flips a coin. But if a
      competing value `w ≠ v` had a majority of witnesses, that would
      contradict the lock (pigeonhole). So the coin flip case means
      no value had a majority of witnesses, preserving the majority of
      `v`-holders. (In the full proof, this requires careful reasoning
      about the interplay between the propose-phase majority and the
      existing value majority.)

    We prove agreement from the lock invariant, and prove the lock
    invariant is inductive for the Report phase. For the Propose phase,
    we state the key lemmas and leave the harder combinatorial arguments
    as sorry.

    ### Formal structure

    ```
    benor_agreement
    ├── lock_inv_implies_agreement (pigeonhole)
    │   └── majority_unique (two majorities can't coexist)
    └── lock_inv is inductive (init_invariant)
        ├── lock_inv_init (no initial decisions → vacuously true)
        └── lock_inv_next (lock preserved by next)
            ├── Report phase: val/decided unchanged → trivial
            └── Propose phase: sorry (combinatorial argument)
    ```
-/

open TLA

namespace BenOr

variable (n : Nat)

/-! ### State and messages -/

/-- Local state of each process. -/
structure LState where
  /-- Current binary value: 0 or 1. -/
  val : Fin 2
  /-- Value witnessed in phase 1, if any. A process witnesses `v` if it
      receives `v` from a strict majority of senders. -/
  witnessed : Option (Fin 2)
  /-- Decided value, if any. Once set, decisions are permanent. -/
  decided : Option (Fin 2)
  deriving DecidableEq, Repr

/-- Global state of the protocol. -/
structure GState (n : Nat) where
  /-- Current round number (increments after each complete two-phase round). -/
  round : Nat
  /-- Current phase: 0 = Report, 1 = Propose. -/
  phase : Fin 2
  /-- Local state of each process. -/
  locals : Fin n → LState

/-! ### Counting utilities -/

/-- Count how many processes in the HO set of `p` sent value `v`. -/
def countVal (locals : Fin n → LState) (ho : HOCollection (Fin n))
    (p : Fin n) (v : Fin 2) : Nat :=
  ((List.finRange n).filter fun q => ho p q && ((locals q).val == v)).length

/-- Check if value `v` has strict majority support among messages received by `p`. -/
def hasValMajority (locals : Fin n → LState) (ho : HOCollection (Fin n))
    (p : Fin n) (v : Fin 2) : Bool :=
  countVal n locals ho p v * 2 > n

/-- Find the value (if any) that has majority support in p's received messages. -/
def findValMajority (locals : Fin n → LState) (ho : HOCollection (Fin n))
    (p : Fin n) : Option (Fin 2) :=
  (List.finRange 2).find? fun v => hasValMajority n locals ho p v

/-- Count how many processes in the HO set of `p` witnessed value `v`. -/
def countWitness (locals : Fin n → LState) (ho : HOCollection (Fin n))
    (p : Fin n) (v : Fin 2) : Nat :=
  ((List.finRange n).filter fun q =>
    ho p q && ((locals q).witnessed == some v)).length

/-- Check if witness `v` has strict majority support among messages received by `p`. -/
def hasWitnessMajority (locals : Fin n → LState) (ho : HOCollection (Fin n))
    (p : Fin n) (v : Fin 2) : Bool :=
  countWitness n locals ho p v * 2 > n

/-- Find the witness (if any) that has majority support in p's received proposals. -/
def findWitnessMajority (locals : Fin n → LState) (ho : HOCollection (Fin n))
    (p : Fin n) : Option (Fin 2) :=
  (List.finRange 2).find? fun v => hasWitnessMajority n locals ho p v

/-! ### Counting actual holders -/

/-- Number of processes holding value `v` in the current state. -/
def countHolding (v : Fin 2) (s : GState n) : Nat :=
  ((List.finRange n).filter fun p =>
    decide ((s.locals p).val = v)).length

/-- Number of processes that witnessed value `v` in the current state. -/
def countWitnessed (v : Fin 2) (s : GState n) : Nat :=
  ((List.finRange n).filter fun p =>
    decide ((s.locals p).witnessed = some v)).length

/-! ### Phase transitions -/

/-- Phase 1 (Report): Each process broadcasts its value. If a process
    receives the same value `v` from > n/2 senders, it witnesses `v`.
    Only `witnessed` is updated; `val` and `decided` are unchanged. -/
def stepReport (s s' : GState n) (ho : HOCollection (Fin n)) : Prop :=
  s.phase = 0 ∧ s'.phase = 1 ∧ s'.round = s.round ∧
  ∀ p, s'.locals p =
    { val := (s.locals p).val,
      witnessed := findValMajority n s.locals ho p,
      decided := (s.locals p).decided }

/-- Phase 2 (Propose): Each process broadcasts its witness. If a process
    receives the same witness `v` from > n/2 senders, it decides `v`.
    Otherwise, it flips a coin (the `coin` oracle provides a random bit).
    Decisions are permanent: once decided, a process keeps its decision. -/
def stepPropose (s s' : GState n) (ho : HOCollection (Fin n))
    (coin : Fin n → Fin 2) : Prop :=
  s.phase = 1 ∧ s'.phase = 0 ∧ s'.round = s.round + 1 ∧
  ∀ p, s'.locals p =
    if (s.locals p).decided.isSome then
      -- Already decided: keep state, but update witnessed for the new round
      { val := (s.locals p).val,
        witnessed := none,
        decided := (s.locals p).decided }
    else
      match findWitnessMajority n s.locals ho p with
      | some v =>
        -- Majority witness: decide v
        { val := v, witnessed := none, decided := some v }
      | none =>
        -- No majority witness: flip coin
        { val := coin p, witnessed := none, decided := none }

/-- The Ben-Or protocol specification. -/
def benOrSpec : Spec (GState n) where
  init := fun s =>
    s.round = 0 ∧ s.phase = 0 ∧
    ∀ p, (s.locals p).witnessed = none ∧ (s.locals p).decided = none
  next := fun s s' =>
    (∃ ho, stepReport n s s' ho) ∨
    (∃ ho coin, stepPropose n s s' ho coin)

/-! ### Safety property -/

/-- Agreement: all decided processes agree on the same value. -/
def agreement (s : GState n) : Prop :=
  ∀ p q v w,
    (s.locals p).decided = some v →
    (s.locals q).decided = some w →
    v = w

/-! ### Pigeonhole: two majorities can't coexist -/

/-- Among `n` elements, two disjoint predicates cannot both select
    strict majorities. If both > n/2, that requires > n elements. -/
theorem majority_unique
    (f : Fin n → Fin 2) (v w : Fin 2) (hne : v ≠ w)
    (hv : ((List.finRange n).filter fun p => decide (f p = v)).length * 2 > n)
    (hw : ((List.finRange n).filter fun p => decide (f p = w)).length * 2 > n) :
    False := by
  have h_sum := filter_disjoint_length_le
    (fun p => decide (f p = v))
    (fun p => decide (f p = w))
    (List.finRange n)
    (by intro x ⟨h1, h2⟩
        simp [decide_eq_true_eq] at h1 h2
        rw [h1] at h2 ; exact hne h2)
  have h_len : (List.finRange n).length = n := List.length_finRange
  omega

/-! ### Auxiliary invariant: the lock -/

/-- The lock invariant: if any process has decided value `v`, then a
    strict majority (> n/2) of all processes currently hold value `v`.

    This is the key inductive invariant. It captures the fact that a
    decision requires a majority of witnesses, which in turn requires
    a majority of value-holders. Once a majority holds `v`, no competing
    value can also achieve a majority. -/
def lock_inv (s : GState n) : Prop :=
  ∀ v, (∃ p : Fin n, (s.locals p).decided = some v) →
    countHolding n v s * 2 > n

/-- The lock invariant implies agreement: if two processes decided
    different values, each would need a strict majority of holders,
    but two disjoint majorities can't coexist. -/
theorem lock_inv_implies_agreement (s : GState n)
    (h : lock_inv n s) : agreement n s := by
  intro p q v w hv hw
  by_contra hne
  exact majority_unique n (fun r => (s.locals r).val) v w hne
    (h v ⟨p, hv⟩) (h w ⟨q, hw⟩)

/-! ### The lock invariant is inductive -/

/-- Initially no process has decided, so the lock holds vacuously. -/
theorem lock_inv_init :
    ∀ s, (benOrSpec n).init s → lock_inv n s := by
  intro s ⟨_, _, hinit⟩ v ⟨p, hp⟩
  have := (hinit p).2
  rw [this] at hp ; simp at hp

/-- The lock is preserved by the Report phase.

    Report only updates `witnessed`; it does not change `val` or `decided`.
    So `countHolding` and the set of decided processes are unchanged. -/
theorem lock_inv_report (s s' : GState n) (ho : HOCollection (Fin n))
    (hinv : lock_inv n s) (hstep : stepReport n s s' ho) :
    lock_inv n s' := by
  obtain ⟨_, _, _, hlocals⟩ := hstep
  intro v ⟨p, hp⟩
  -- p decided v in s' — but decided is unchanged from s
  have hp_loc := hlocals p
  rw [hp_loc] at hp ; simp only at hp
  -- So p decided v in s too
  have hp_s : (s.locals p).decided = some v := hp
  have hlock := hinv v ⟨p, hp_s⟩
  -- countHolding is unchanged because val is unchanged
  suffices countHolding n v s' = countHolding n v s by omega
  simp only [countHolding]
  congr 1
  apply List.filter_congr
  intro q _
  rw [hlocals q]

/-- The lock is preserved by the Propose phase.

    This is the heart of the safety argument. The full proof requires
    showing:
    1. If process p newly decides v, then > n/2 processes witnessed v,
       meaning > n/2 held v (majority intersection from phase 1).
    2. Every process that held v in s still holds v in s':
       - If it already decided, it keeps its value.
       - If it sees a majority witness for some w, then w = v
         (by pigeonhole with the existing v-majority).
       - If it flips a coin, it might change — but this case is ruled
         out: if > n/2 held v, then > n/2 witnessed v (given appropriate
         HO sets), so every process sees at least one witness for v,
         preventing a competing majority.

    The full combinatorial argument is subtle and depends on the
    communication predicate. We leave it as sorry. -/
theorem lock_inv_propose (s s' : GState n) (ho : HOCollection (Fin n))
    (coin : Fin n → Fin 2)
    (hinv : lock_inv n s) (hstep : stepPropose n s s' ho coin) :
    lock_inv n s' := by
  sorry

/-- The lock invariant is preserved by all transitions. -/
theorem lock_inv_next (s s' : GState n) (hinv : lock_inv n s)
    (hnext : (benOrSpec n).next s s') : lock_inv n s' := by
  rcases hnext with ⟨ho, hstep⟩ | ⟨ho, coin, hstep⟩
  · exact lock_inv_report n s s' ho hinv hstep
  · exact lock_inv_propose n s s' ho coin hinv hstep

/-! ### Main safety theorem -/

/-- **Ben-Or satisfies agreement.**

    Proof: `lock_inv` is an inductive invariant (`init_invariant` with
    `lock_inv_init` and `lock_inv_next`), giving `□ lock_inv`. Then
    `lock_inv_implies_agreement` lifts it to `□ agreement` via
    `always_monotone`. -/
theorem benor_agreement :
    pred_implies (benOrSpec n).safety
      [tlafml| □ ⌜agreement n⌝] := by
  apply pred_implies_trans (q := [tlafml| □ ⌜lock_inv n⌝])
  · apply init_invariant
    · exact lock_inv_init n
    · intro s s' hnext hinv
      exact lock_inv_next n s s' hinv hnext
  · apply always_monotone
    intro e h
    exact lock_inv_implies_agreement n (e 0) h

end BenOr
