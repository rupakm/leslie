import Leslie.Examples.UtilityByzantine

set_option linter.unnecessarySeqFocus false

/-! # Binding Crusader Agreement

  Binding Crusader Agreement for `n` processes with at most `f` Byzantine
  faults, where `n > 3f`.

  Each process starts with a binary input (0 or 1). The protocol produces
  a decision in {0, 1, ⊥} satisfying:
  - **Validity**: If all correct processes have input b, then every correct
    process that decides, decides b.
  - **Agreement**: No correct process decides 0 and no other correct process
    decides 1. (⊥ is compatible with both.)

  The global state is composed of:
  - A **local state** per process (receipts, approval, echo/vote/decision)
  - A **message buffer** (pending messages in transit)
  - A **list of corrupted** processes

  ## Protocol
  1. Each process sends init(input) to all.
  2. On receiving f+1 init(b) (and not yet sent init(b)): send init(b) to all.
     (Input amplification.)
  3. On receiving n−f init(b): b is "approved". If not yet echoed: echo(b) to all.
  4. When both 0 and 1 are approved: send vote(⊥) to all.
  5. On receiving n−f echo(b): send vote(b) to all.
  6. On receiving n−f vote(b): decide b.
  7. When both 0 and 1 approved and received n−f vote: decide ⊥.
  8. A process decides at most once.

  Byzantine processes can inject arbitrary messages into the network.

  ## Proof architecture

  The file proves three top-level safety properties:

  - `bca_agreement` — no two correct processes decide opposite binary values.
  - `bca_validity`  — under unanimous input, every correct decision matches.
  - `bca_binding`   — once any correct process has decided, there is a fixed
    `b ∈ {0,1}` that no correct process will ever decide.

  All three follow from inductive invariants on the global state:

  1. `bca_inv` (10 conjuncts: budget, echo/vote traces, decision backing,
     vote agreement, echo backing, echo witness, conditional unanimity).
     Used for `bca_agreement` and `bca_validity`.

  2. `bound_inv` (8 conjuncts B1–B8) tracks a *ghost* field `boundValue`.
     `boundValue` records the protocol's "committed" outcome:
       - `none`           : nothing committed yet,
       - `some (some b)`  : binary value `b` committed,
       - `some none`      : ⊥ committed.
     `boundValue` is updated by `computeBound` after every transition: it
     becomes `some none` once enough ⊥-votes are seen, and `some (some b)`
     once enough binary `b`-votes are seen. Together with the invariant
     conjuncts B1–B8 it proves binding by ruling out conflicting decisions
     across the trace (`bound_binary_monotone` + `bca_binding`).

  ## File layout

  - State / messages / actions (lines ~40–310): basic protocol structure.
  - `bca` `ActionSpec` (~165): the four kinds of action with gates and
    transitions.
  - `bca_inv` (~373) and its proofs `bca_inv_init` / `bca_inv_step` (~430).
  - `bca_agreement` and `bca_validity` (~1748–1808): immediate corollaries
    of `bca_inv`.
  - `bound_inv` (~1848) and its (large) inductive proof
    `bound_inv_step` (~2160), structured as one block per action.
  - `bound_binary_monotone` (~3489) and the final `bca_binding` (~3540).
-/

open TLA

namespace BindingCrusaderAgreement

/-! ### Messages -/

inductive MsgType where
  | init | echo | vote
  deriving DecidableEq

variable (T : Type)

/-- Values in the protocol: binary or ⊥.
    Represented as Option T: some b for binary, none for ⊥. -/
abbrev Val (T : Type) := Option T

structure Message (n : Nat) where
  src : Fin n
  dst : Fin n
  type : MsgType
  val : Val T
  deriving DecidableEq

/-! ### Local state -/

structure LocalState (n : Nat) where
  /-- Process's own input (set once at initialisation). -/
  input : Option T
  /-- `sent dst t v = true` iff this process has sent message (t, v) to dst. -/
  sent : Fin n → MsgType → Val T → Bool
  /-- Received init(b) from process j. -/
  initRecv : Fin n → T → Bool
  /-- Whether value b is approved (received ≥ n−f init(b)). -/
  approved : T → Bool
  /-- Value echoed (at most one). -/
  echoed : Option T
  /-- Received echo(b) from process j. -/
  echoRecv : Fin n → T → Bool
  /-- `voted v = true` iff this process has sent vote(v). -/
  voted : Val T → Bool
  /-- Received vote(v) from process j. -/
  voteRecv : Fin n → Val T → Bool
  /-- Decision (at most one). -/
  decided : Option (Val T)

/-! ### Global state -/

structure State (n : Nat) where
  /-- Per-process local state. -/
  local_ : Fin n → LocalState T n
  /-- Network buffer: pending messages in transit. -/
  buffer : Message T n → Bool
  /-- List of corrupted (Byzantine) processes. -/
  corrupted : List (Fin n)
  /-- **Ghost**: the "bound value" used to prove binding. Monotone:
      once set, frozen. `none` = undefined; `some (some b)` = bound to
      binary `b`; `some none` = bound to ⊥. Set by threshold crossings
      (see `computeBound`). Not observed by any action. -/
  boundValue : Option (Val T)

/-! ### Actions -/

inductive Action (n : Nat) where
  | corrupt (i : Fin n)
  | send (src dst : Fin n) (t : MsgType) (v : Val T)
  | recv (src dst : Fin n) (t : MsgType) (v : Val T)
  | decide (i : Fin n) (v : Val T)
  | set_input (i : Fin n) (v : T)

/-! ### Helpers -/

variable (n f : Nat)

def isCorrect (s : State T n) (p : Fin n) : Prop := p ∉ s.corrupted

/-- Count of distinct sources from which init(b) was received. -/
def countInitRecv (ls : LocalState T n) (b : T) : Nat :=
  (List.finRange n).filter (ls.initRecv · b) |>.length

/-- Count of distinct sources from which echo(b) was received. -/
def countEchoRecv (ls : LocalState T n) (b : T) : Nat :=
  (List.finRange n).filter (ls.echoRecv · b) |>.length

/-- Count of distinct sources from which vote(v) was received. -/
def countVoteRecv (ls : LocalState T n) (v : Val T) : Nat :=
  (List.finRange n).filter (ls.voteRecv · v) |>.length

/-- Count of distinct sources from which any vote in `vals` was received. -/
def countAnyVoteRecv (ls : LocalState T n) (vals : List (Val T)) : Nat :=
  (List.finRange n).filter (fun q =>
    vals.any (fun v => ls.voteRecv q v)) |>.length

def amplifyThreshold : Nat := f + 1
def approveThreshold : Nat := n - f
def echoThreshold : Nat := n - f
def returnThreshold : Nat := n - f

/-- Number of correct processes that have voted `v`. -/
def correctVoteCount (s : State T n) (v : Val T) : Nat :=
  ((List.finRange n).filter (fun p =>
    decide (p ∉ s.corrupted) && (s.local_ p).voted v)).length

/-- Find a value `v` such that `|corrupted| + correctVoteCount(some v) > f`. -/
def findBoundValue (s : State T n) : Option T :=
  (List.finRange n).findSome? fun p =>
    match (s.local_ p).echoed with
    | some v =>
      if s.corrupted.length + correctVoteCount T n s (some v) > f then some v else none
    | none => none

/-- Ghost update rule for the bound value.
    - `some none` (⊥) is frozen.
    - `some (some b)` (binary) can still be upgraded to `some none` (⊥) if the
      ⊥ threshold is crossed, but never to the opposite binary value.
    - `none` can become anything: ⊥ if `|corrupted| + correct ⊥-voters > 2f`,
      otherwise a binary value `b` if `|corrupted| + correct b-voters > f`. -/
def computeBound (s : State T n) : Option (Val T) :=
  if s.corrupted.length + correctVoteCount T n s none > 2 * f then some none
  else match s.boundValue with
    | some bv => some bv
    | none =>
      match findBoundValue T n f s with
      | some v => some (some v)
      | none => none

/-- Default initial local state: everything empty/none/false. -/
def LocalState.init : LocalState T n where
  input := none
  sent := fun _ _ _ => false
  initRecv := fun _ _ => false
  approved := fun _ => false
  echoed := none
  echoRecv := fun _ _ => false
  voted := fun _ => false
  voteRecv := fun _ _ => false
  decided := none

/-! ### Specification -/

-- The action spec, `bca_inv`, and the initial-state proof all need
-- `DecidableEq T` (e.g. to compare `Option T` values in gate/transition
-- `if w = mv` tests). Scoped via a section so the purely structural
-- helpers below don't auto-bind an unused `[DecidableEq T]` instance.
section SpecAndInvDef
variable [DecidableEq T]

/-- Binding Crusader Agreement specification. -/
def bca : ActionSpec (State T n) (Action T n) where
  init := fun s =>
    (∀ p, s.local_ p = LocalState.init T n) ∧
    (∀ m, s.buffer m = false) ∧
    s.corrupted = [] ∧
    s.boundValue = none
  actions := fun
    --
    -- === Adversary action ===
    --
    | .corrupt i => {
        gate := fun s =>
          isCorrect T n s i ∧
          s.corrupted.length + 1 ≤ f
        transition := fun s s' =>
          let s₀ : State T n := { s with corrupted := i :: s.corrupted }
          s' = { s₀ with boundValue := computeBound T n f s₀ }
      }
    --
    -- === Send action ===
    --
    -- Byzantine processes can send any message at any time.
    -- Correct processes must follow the protocol:
    --   INIT: send init(input) initially, or init(b) on f+1 amplification
    --   ECHO: triggered by approval of b. A correct process echoes the
    --         same value `b` to *every* destination, but never echoes a
    --         second binary value (single-value, multi-destination).
    --   VOTE: triggered by n−f echoes for b, or both approved (vote ⊥).
    --         Same single-value, multi-destination semantics.
    --
    | .send src dst t mv => {
        gate := fun s =>
          src ∈ s.corrupted ∨
          (isCorrect T n s src ∧ (s.local_ src).sent dst t mv = false ∧
            match t with
            | .init =>
              -- Init(b): own input, or amplification (f+1 init(b) received)
              match mv with
              | some b =>
                (s.local_ src).input = some b ∨
                countInitRecv T n (s.local_ src) b ≥ amplifyThreshold f
              | none => False  -- init messages carry binary values only
            | .echo =>
              -- Echo(b): b is approved and either no value has been echoed
              -- yet, or the same value `b` was echoed previously (so this
              -- is a re-fire to a different destination).
              match mv with
              | some b =>
                (s.local_ src).approved b = true ∧
                ((s.local_ src).echoed = none ∨ (s.local_ src).echoed = some b)
              | none => False  -- echo messages carry binary values only
            | .vote =>
              -- Vote(v): every previous vote (if any) was for the same v.
              -- This permits multi-destination broadcast of the same value
              -- while still forbidding voting two distinct values.
              (∀ w, (s.local_ src).voted w = true → w = mv) ∧
              match mv with
              | some b =>
                countEchoRecv T n (s.local_ src) b ≥ echoThreshold n f
              | none =>
                ∃ v₁ v₂, v₁ ≠ v₂ ∧ (s.local_ src).approved v₁ = true ∧
                  (s.local_ src).approved v₂ = true)
        transition := fun s s' =>
          let msg : Message T n := ⟨src, dst, t, mv⟩
          let s₀ : State T n := { s with
            buffer := fun m => if m = msg then true else s.buffer m
            local_ := fun p => if p = src then
              { s.local_ src with
                sent := fun d t' w => if d = dst ∧ t' = t ∧ w = mv then true
                  else (s.local_ src).sent d t' w
                echoed := match t with
                  | .echo => match mv with
                    | some b => if src ∉ s.corrupted then some b
                                else (s.local_ src).echoed
                    | none => (s.local_ src).echoed
                  | _ => (s.local_ src).echoed
                voted := match t with
                  | .vote => if src ∉ s.corrupted
                    then fun w => if w = mv then true else (s.local_ src).voted w
                    else (s.local_ src).voted
                  | _ => (s.local_ src).voted }
              else s.local_ p }
          s' = { s₀ with boundValue := computeBound T n f s₀ }
      }
    --
    -- === Receive action ===
    --
    | .recv src dst t mv => {
        gate := fun s =>
          s.buffer ⟨src, dst, t, mv⟩ = true
        transition := fun s s' =>
          let msg : Message T n := ⟨src, dst, t, mv⟩
          let ls := s.local_ dst
          let s₀ : State T n := { s with
            buffer := fun m => if m = msg then false else s.buffer m
            local_ := fun p => if p = dst then
              match t with
              | .init =>
                match mv with
                | some b =>
                  if ls.initRecv src b = false
                  then { ls with
                    initRecv := fun q w => if q = src ∧ w = b then true
                      else ls.initRecv q w
                    -- Auto-approve if threshold reached
                    approved := fun w => if w = b ∧
                      countInitRecv T n ls b + 1 ≥ approveThreshold n f
                      then true else ls.approved w }
                  else ls
                | none => ls  -- ignore ⊥ init messages
              | .echo =>
                match mv with
                | some b =>
                  if ls.echoRecv src b = false
                  then { ls with
                    echoRecv := fun q w => if q = src ∧ w = b then true
                      else ls.echoRecv q w }
                  else ls
                | none => ls  -- ignore ⊥ echo messages
              | .vote =>
                if ls.voteRecv src mv = false
                then { ls with
                  voteRecv := fun q w => if q = src ∧ w = mv then true
                    else ls.voteRecv q w }
                else ls
              else s.local_ p }
          s' = { s₀ with boundValue := computeBound T n f s₀ }
      }
    --
    -- === Decide action ===
    --
    -- Correct process decides v once it has sufficient votes.
    -- Decide b (binary): ≥ n−f vote(b) received.
    -- Decide ⊥: both approved and ≥ n−f votes (any value) received.
    --
    | .decide i mv => {
        gate := fun s =>
          isCorrect T n s i ∧
          (s.local_ i).decided = none ∧
          match mv with
          | some b =>
            countVoteRecv T n (s.local_ i) (some b) ≥ returnThreshold n f
          | none =>
            (∃ v₁ v₂, v₁ ≠ v₂ ∧ (s.local_ i).approved v₁ = true ∧
              (s.local_ i).approved v₂ = true) ∧
            ∃ (vals : List (Val T)),
              countAnyVoteRecv T n (s.local_ i) vals ≥ returnThreshold n f
        transition := fun s s' =>
          let s₀ : State T n := { s with
            local_ := fun p => if p = i
              then { s.local_ i with decided := some mv }
              else s.local_ p }
          s' = { s₀ with boundValue := computeBound T n f s₀ }
      }
    | .set_input i v => {
        gate := fun s =>
          (s.local_ i).input = none
        transition := fun s s' =>
          s' = { s with
            local_ := fun p => if p = i
              then { s.local_ i with input := some v }
              else s.local_ p }
      }

/-! ### Safety properties -/

/-- **Agreement**: if a correct process decides some v and some w, then v = w. -/
def agreement (s : State T n) : Prop :=
  ∀ p q v w,
    isCorrect T n s p → isCorrect T n s q →
    (s.local_ p).decided = some (some v) →
    (s.local_ q).decided = some (some w) →
    v = w

/-- **Validity**: if every process is either corrupted, has no input yet,
    or has input `v`, then every process has either not decided or
    decided `some v`. This is the composition-friendly form: corrupted
    processes and processes whose input hasn't been set are excluded
    from the unanimity condition. -/
def validity (v : T) (s : State T n) : Prop :=
  (∀ p, ¬isCorrect T n s p ∨ (s.local_ p).input = none ∨ (s.local_ p).input = some v) →
  ∀ p, (s.local_ p).decided = none ∨ (s.local_ p).decided = some (some v)

/-- **Binding**: once any correct process has decided, there exists a fixed
    b : T such that no correct process ever decides some (some v) with v ≠ b. -/
def binding : pred (State T n) :=
  fun e => (∃ k p v, isCorrect T n (e k) p ∧ (e k |>.local_ p).decided = some v) →
  ∃ b : T, ∀ k q v, isCorrect T n (e k) q → (e k |>.local_ q).decided = some (some v) → v = b

/-! ### Inductive invariant

    We prove **agreement** and **validity** from a single invariant `bca_inv`.
-/

/-- Local consistency with value `v`: a process's echo, vote, approval,
    and decision are all consistent with `v`. Init messages are excluded
    because a process legitimately sends `init(b)` for its own input `b`,
    which may differ from `v`. -/
def local_consistent (v : T) (ls : LocalState T n) : Prop :=
  (∀ dst t w, ls.sent dst t w = true → match t with
    | .init => True  -- init excluded: process sends its own input
    | .echo => w = some v
    | .vote => w = some v ∨ w = none) ∧
  (∀ w, ls.echoed = some w → w = v) ∧
  (∀ w, ls.voted (some w) = true → w = v) ∧
  (∀ w, w ≠ v → ls.approved w = false) ∧
  (∀ w, ls.decided = some w → w = some v)

/-- Buffer consistency with value `v`: all pending echo and vote messages
    from correct processes carry `v`. Init messages are excluded. -/
def buffer_consistent (v : T) (s : State T n) : Prop :=
  ∀ m, s.buffer m = true → isCorrect T n s m.src → match m.type with
    | .init => True  -- init excluded
    | .echo => m.val = some v
    | .vote => m.val = some v ∨ m.val = none

/-- The inductive invariant for BCA safety. Conjuncts:
    1. **Budget**: at most f processes corrupted
    2. **Echo trace**: echoRecv reflects echoed values of correct processes
    3. **Buffer echo trace**: pending ECHO messages reflect echoed values
    4. **Vote trace (binary)**: voteRecv(some b) reflects voted values of correct processes
    5. **Buffer vote trace (binary)**: pending VOTE(some b) messages reflect voted values
    6. **Conditional** (for validity): if all correct inputs are b, local states
       and buffer carry b
    7. **Decision backing**: decided(some b) → ≥ n−f vote(some b) sources
    8. **Vote agreement (binary)**: all binary votes from correct processes agree
    9. **Echo backing**: every correct binary vote is backed by ≥ n−f echo sources
    10. **Echo witness**: if any correct process voted(some b), some process has
        ≥ n−f echo receipts for b -/
def bca_inv (s : State T n) : Prop :=
  -- 1. Budget
  s.corrupted.length ≤ f ∧
  -- 2. Echo trace
  (∀ p q (b : T), isCorrect T n s p →
    (s.local_ q).echoRecv p b = true → (s.local_ p).echoed = some b) ∧
  -- 3. Buffer echo trace
  (∀ p dst (b : T), isCorrect T n s p →
    s.buffer ⟨p, dst, .echo, some b⟩ = true → (s.local_ p).echoed = some b) ∧
  -- 4. Vote trace (binary)
  (∀ p q (b : T), isCorrect T n s q →
    (s.local_ p).voteRecv q (some b) = true → (s.local_ q).voted (some b) = true) ∧
  -- 5. Buffer vote trace (binary)
  (∀ p dst (b : T), isCorrect T n s p →
    s.buffer ⟨p, dst, .vote, some b⟩ = true → (s.local_ p).voted (some b) = true) ∧
  -- 6. (removed — subsumed by conjuncts 13–15)
  -- 7. Decision backing
  (∀ p (b : T), (s.local_ p).decided = some (some b) →
    countVoteRecv T n (s.local_ p) (some b) ≥ returnThreshold n f) ∧
  -- 8. Vote agreement (binary): all correct binary votes are for the same value
  (∀ p q (b₁ b₂ : T), isCorrect T n s p → isCorrect T n s q →
    (s.local_ p).voted (some b₁) = true → (s.local_ q).voted (some b₂) = true → b₁ = b₂) ∧
  -- 9. Echo backing: correct binary vote → ≥ n−f echo sources
  (∀ p (b : T), isCorrect T n s p →
    (s.local_ p).voted (some b) = true →
    countEchoRecv T n (s.local_ p) b ≥ echoThreshold n f) ∧
  -- 10. Echo witness: if any correct voted(some b), some process has ≥ n−f echo receipts
  (∀ (b : T), (∃ p, isCorrect T n s p ∧ (s.local_ p).voted (some b) = true) →
    ∃ q, countEchoRecv T n (s.local_ q) b ≥ echoThreshold n f) ∧
  -- 11. Count ↔ approved: approved b iff countInitRecv b ≥ approveThreshold.
  --     Guarded by n > f so the threshold is positive.
  (n > f → ∀ p (b : T), (s.local_ p).approved b = true ↔
    countInitRecv T n (s.local_ p) b ≥ approveThreshold n f) ∧
  -- 12. Echoed → approved: if a correct process has echoed b, then it approved b.
  (∀ p (b : T), isCorrect T n s p → (s.local_ p).echoed = some b →
    (s.local_ p).approved b = true) ∧
  -- 13. Init recv trace: if p received init(v) from correct q, then q has
  --     input v or q amplified (received f+1 init(v) messages).
  (∀ p q (v : T), isCorrect T n s q → (s.local_ p).initRecv q v = true →
    (s.local_ q).input = some v ∨ countInitRecv T n (s.local_ q) v ≥ amplifyThreshold f) ∧
  -- 14. Init buffer trace: same for pending init messages in the buffer.
  (∀ q p (v : T), isCorrect T n s q → s.buffer ⟨q, p, .init, some v⟩ = true →
    (s.local_ q).input = some v ∨ countInitRecv T n (s.local_ q) v ≥ amplifyThreshold f) ∧
  -- 15. Init amplification support: if a correct process has received
  --     ≥ f+1 init(v) without having input v, then ≥ f+1 processes are
  --     corrupted or have input v. This survives corruption (monotone).
  (∀ q (v : T), isCorrect T n s q →
    countInitRecv T n (s.local_ q) v ≥ amplifyThreshold f →
    (s.local_ q).input ≠ some v →
    ((List.finRange n).filter (fun r =>
      decide (r ∈ s.corrupted) || decide ((s.local_ r).input = some v))).length ≥ f + 1) ∧
  -- 16. Bot decision backing: decided ⊥ implies two distinct approved values.
  (∀ p, (s.local_ p).decided = some none →
    ∃ v₁ v₂, v₁ ≠ v₂ ∧ (s.local_ p).approved v₁ = true ∧ (s.local_ p).approved v₂ = true)

/-! ### Invariant proofs

  Two parts:
  - `bca_inv_init`: every initial state satisfies the invariant — most
    conjuncts are vacuous since nothing has been sent, voted, or decided.
  - `bca_inv_step`: every action preserves the invariant. The proof is a
    big case split on the action (`corrupt`, `send`, `recv`, `decide`),
    refined by `t : MsgType` and `mv : Val` for `send`/`recv`. Each leaf
    discharges all 10 conjuncts of `bca_inv` for the post-state.
-/

/-- Echo quorum intersection specialized to BCA's state. -/
private theorem bca_echo_quorum_intersection {n f : Nat} (hn : n > 3 * f)
    (s : State T n) (p1 p2 : Fin n) (v w : T)
    (hbudget : s.corrupted.length ≤ f)
    (hetrace : ∀ p q (b : T), isCorrect T n s p →
      (s.local_ q).echoRecv p b = true → (s.local_ p).echoed = some b)
    (hv : countEchoRecv T n (s.local_ p1) v ≥ echoThreshold n f)
    (hw : countEchoRecv T n (s.local_ p2) w ≥ echoThreshold n f) :
    v = w :=
  _root_.echo_quorum_intersection hn v w p1 p2
    (fun p q b => (s.local_ p).echoRecv q b)
    (fun p => (s.local_ p).echoed)
    s.corrupted hbudget hetrace hv hw

-- All conjuncts vacuously true: sent/voted/echoRecv/voteRecv all false,
-- buffer empty, decided = none.
theorem bca_inv_init :
    ∀ s, (bca T n f).init s → bca_inv T n f s := by
  intro s ⟨hlocal, hbuf, hcorr⟩
  refine ⟨by simp [hcorr], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p q b _ h ; simp [hlocal, LocalState.init] at h
  · intro p dst b _ h ; simp [hbuf] at h
  · intro p q b _ h ; simp [hlocal, LocalState.init] at h
  · intro p dst b _ h ; simp [hbuf] at h
  · intro p b h ; simp [hlocal, LocalState.init] at h
  · intro p q b₁ b₂ _ _ hvp _ ; simp [hlocal, LocalState.init] at hvp
  · intro p b _ hvp ; simp [hlocal, LocalState.init] at hvp
  · intro b ⟨p, _, hvp⟩ ; simp [hlocal, LocalState.init] at hvp
  · -- 11. count ↔ approved: both false in init state
    intro _ p b ; constructor
    · intro h ; simp [hlocal, LocalState.init] at h
    · intro hcnt
      have h0 : countInitRecv T n (s.local_ p) b = 0 := by
        simp [hlocal, LocalState.init, countInitRecv]
      rw [h0] at hcnt ; unfold approveThreshold at hcnt ; omega
  · -- 12. echoed → approved: vacuous, echoed = none in init
    intro p b _ h ; simp [hlocal, LocalState.init] at h
  · -- 13. init recv trace: vacuous, initRecv all false in init
    intro p q v _ h ; simp [hlocal, LocalState.init] at h
  · -- 14. init buffer trace: vacuous, buffer empty in init
    intro q p v _ h ; simp [hbuf] at h
  · -- 15. init amplification support: vacuous, countInitRecv = 0 in init
    intro q v _ hcnt
    have h0 : countInitRecv T n (s.local_ q) v = 0 := by
      simp [hlocal, LocalState.init, countInitRecv]
    rw [h0] at hcnt ; unfold amplifyThreshold at hcnt ; omega
  · -- 16. bot decision backing: vacuous, decided = none in init
    intro p h ; simp [hlocal, LocalState.init] at h

/- Inductive step: every BCA action preserves `bca_inv`.

   The proof case-splits on `action`:
   - `corrupt i`  — adds `i` to the corrupted list. Most invariants are
     monotone in `corrupted`; the budget conjunct uses the gate
     `|corrupted| + 1 ≤ f`.
   - `send src dst t mv` — extends the message buffer and (if `src` is
     correct) extends `src`'s `sent`/`echoed`/`voted` fields. The trace
     and backing conjuncts use the gate's threshold conditions; vote
     agreement uses `echo_quorum_intersection`.
   - `recv src dst t mv` — bumps the receiver's `*Recv` field and may
     also flip `approved` for init. Echo/vote traces are restored from
     `bca_inv`'s buffer-trace conjuncts.
   - `decide i mv` — only changes `decided`; all conjuncts unrelated to
     `decided` are unchanged, and decision backing comes from the gate.
-/

/-- Recv preserves input at every process. -/
private theorem recv_input_eq (s : State T n) (src dst : Fin n) (t : MsgType) (mv : Val T) (q : Fin n) :
    (if q = dst then
      match t with
      | .init => match mv with
        | some b => if (s.local_ dst).initRecv src b = false then
            { (s.local_ dst) with
              initRecv := fun q' w => if q' = src ∧ w = b then true else (s.local_ dst).initRecv q' w
              approved := fun w => if w = b ∧ countInitRecv T n (s.local_ dst) b + 1 ≥ approveThreshold n f
                then true else (s.local_ dst).approved w }
          else s.local_ dst
        | none => s.local_ dst
      | .echo => match mv with
        | some b => if (s.local_ dst).echoRecv src b = false then
            { (s.local_ dst) with
              echoRecv := fun q' w => if q' = src ∧ w = b then true else (s.local_ dst).echoRecv q' w }
          else s.local_ dst
        | none => s.local_ dst
      | .vote => if (s.local_ dst).voteRecv src mv = false then
          { (s.local_ dst) with
            voteRecv := fun q' w => if q' = src ∧ w = mv then true else (s.local_ dst).voteRecv q' w }
        else s.local_ dst
    else s.local_ q).input = (s.local_ q).input := by
  by_cases hqdst : q = dst
  · subst hqdst ; cases t <;> (try cases mv) <;> simp <;> (try split) <;> simp
  · simp [hqdst]

set_option maxHeartbeats 800000 in
theorem bca_inv_step (hn : n > 3 * f) :
    ∀ s s', (∃ i, ((bca T n f).actions i).fires s s') →
    bca_inv T n f s → bca_inv T n f s' := by
  intro s s' ⟨action, hfire⟩ ⟨hbudget, hetrace, hbet, hvtrace, hbvt,
     hvback, hvagree, hecho_back, hecho_wit, hcount_app, hecho_app,
     hinit_trace, hinit_buf_trace, hinit_amp, hbot_back⟩
  simp [bca, GatedAction.fires] at hfire
  obtain ⟨hgate, htrans⟩ := hfire
  cases action with
  | corrupt i =>
    subst htrans
    have hcw : ∀ q, isCorrect T n { s with corrupted := i :: s.corrupted } q →
        isCorrect T n s q := fun q hq h => hq (List.mem_cons_of_mem i h)
    exact ⟨by simp [List.length_cons] ; exact hgate.2,
      fun p q b hp h => hetrace p q b (hcw p hp) h,
      fun p d b hp h => hbet p d b (hcw p hp) h,
      fun p q b hp h => hvtrace p q b (hcw q hp) h,
      fun p d b hp h => hbvt p d b (hcw p hp) h,
      fun p b h => hvback p b h,
      fun p q b₁ b₂ hp hq h1 h2 => hvagree p q b₁ b₂ (hcw p hp) (hcw q hq) h1 h2,
      fun p b hp h => hecho_back p b (hcw p hp) h,
      fun b ⟨p, hp, h⟩ => hecho_wit b ⟨p, hcw p hp, h⟩,
      fun hnf p b => hcount_app hnf p b,
      fun p b hp h => hecho_app p b (hcw p hp) h,
      fun p q v hp h => hinit_trace p q v (hcw q hp) h,
      fun q p v hp h => hinit_buf_trace q p v (hcw q hp) h,
      fun q v hp hcnt hne => by
        -- Count is monotone: adding i to corrupted grows the filter.
        have hold := hinit_amp q v (hcw q hp) hcnt hne
        apply Nat.le_trans hold ; apply filter_length_mono
        intro r hr
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hr ⊢
        rcases hr with hmem | hinp
        · exact Or.inl (List.mem_cons_of_mem i hmem)
        · exact Or.inr hinp,
      fun p h => hbot_back p h⟩
  | send src dst t mv =>
    subst htrans
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hbudget -- 1. budget
    · -- 2. echo trace: echoRecv unchanged; echoed may change at src for echo
      intro p q b hp h
      have h' : (s.local_ q).echoRecv p b = true := by
        by_cases hq : q = src
        · simp [hq] at h ; rw [hq]; exact h
        · simp [hq] at h ; exact h
      have hold := hetrace p q b hp h'
      by_cases hpsrc : p = src
      · subst hpsrc ; cases t with
        | init => simp ; exact hold
        | vote => by_cases hc : p ∈ s.corrupted <;> simp [hc] <;> exact hold
        | echo =>
          by_cases hc : p ∈ s.corrupted
          · exact absurd hc hp
          · simp [hc] ; cases mv with
            | none => exact hold
            | some bv =>
              rcases hgate with hmem | ⟨_, _, _, hech⟩
              · exact absurd hmem hp
              · rcases hech with hnone | hsome
                · rw [hold] at hnone ; exact absurd hnone (by simp)
                · rw [hold] at hsome ; injection hsome with hbv ; rw [hbv]
      · simp [hpsrc] ; exact hold
    · -- 3. buffer echo trace
      intro p d b hp hbuf ; simp at hbuf
      rcases hbuf with ⟨rfl, rfl, rfl, rfl⟩ | hold
      · by_cases hc : p ∈ s.corrupted
        · exact absurd hc hp
        · simp [hc]
      · have := hbet p d b hp hold
        by_cases hpsrc : p = src
        · subst hpsrc ; cases t with
          | init => simp ; exact this
          | vote => by_cases hc : p ∈ s.corrupted <;> simp [hc] <;> exact this
          | echo =>
            by_cases hc : p ∈ s.corrupted
            · exact absurd hc hp
            · cases mv with
              | none => simp; exact this
              | some bv =>
                rcases hgate with hmem | ⟨_, _, _, hech⟩
                · exact absurd hmem hp
                · rcases hech with hnone | hsome
                  · rw [this] at hnone ; exact absurd hnone (by simp)
                  · rw [this] at hsome ; injection hsome with hbv
                    simp [hbv, hc]
        · simp [hpsrc] ; exact this
    · -- 4. vote trace: voteRecv unchanged; voted changes at src for vote
      intro p q b hp h
      have h' : (s.local_ p).voteRecv q (some b) = true := by
        by_cases hp' : p = src
        · rw [hp'] ; simp [hp'] at h ; exact h
        · simp [hp'] at h ; exact h
      have hold := hvtrace p q b hp h'
      by_cases hqsrc : q = src
      · subst hqsrc ; cases t with
        | init | echo => simp ; exact hold
        | vote =>
          by_cases hc : q ∈ s.corrupted
          · simp [hc] ; exact hold
          · simp [hc] ; by_cases hv : (some b : Val T) = mv <;> simp [hv, hold]
      · simp [hqsrc] ; exact hold
    · -- 5. buffer vote trace: new msg or old
      intro p d b hp hbuf ; simp at hbuf
      rcases hbuf with ⟨rfl, rfl, rfl, rfl⟩ | hold
      · -- new msg: must be vote type with some b
        by_cases hc : p ∈ s.corrupted
        · exact absurd hc hp
        · simp [hc]
      · have := hbvt p d b hp hold
        by_cases hpsrc : p = src
        · subst hpsrc ; cases t with
          | init => simp ; exact this
          | echo =>
            by_cases hc : p ∈ s.corrupted
            · simp [hc] ; exact this
            · cases mv with
              | none => simp; exact this
              | some bv =>
                -- gate: echoed = none, but if p already voted, need voted preserved
                -- voted unchanged by echo send for correct p
                simp [hc] ; exact this
          | vote =>
            by_cases hc : p ∈ s.corrupted
            · simp [hc] ; exact this
            · simp [hc] ; by_cases hv : (some b : Val T) = mv <;> simp [hv, this]
        · simp [hpsrc] ; exact this
    · -- 7. decision backing: decided/voteRecv unchanged by send
      intro p b hdec
      by_cases hpsrc : p = src
      · subst hpsrc ; simp at hdec ⊢ ; exact hvback p b hdec
      · simp [hpsrc] at hdec ⊢ ; exact hvback p b hdec
    · -- 8. vote agreement: new binary vote at src must agree with old votes
      intro p q b₁ b₂ hp hq h1 h2
      -- Extract old voted or detect new vote
      -- Case 1: new vote from src with gate giving echo count
      -- Case 2: old votes → use old hvagree
      -- For p:
      have h1_cases : (p = src ∧ some b₁ = mv ∧ t = .vote ∧ p ∉ s.corrupted) ∨
          (s.local_ p).voted (some b₁) = true := by
        by_cases hpsrc : p = src
        · subst hpsrc ; cases t with
          | init => right ; simp at h1 ; exact h1
          | echo => right ; simp at h1 ; exact h1
          | vote =>
            by_cases hc : p ∈ s.corrupted
            · right ; simp [hc] at h1 ; exact h1
            · simp [hc] at h1
              rcases h1 with rfl | hold
              · left ; exact ⟨rfl, rfl, rfl, hc⟩
              · right ; exact hold
        · right ; simp [hpsrc] at h1 ; exact h1
      have h2_cases : (q = src ∧ some b₂ = mv ∧ t = .vote ∧ q ∉ s.corrupted) ∨
          (s.local_ q).voted (some b₂) = true := by
        by_cases hqsrc : q = src
        · subst hqsrc ; cases t with
          | init => right ; simp at h2 ; exact h2
          | echo => right ; simp at h2 ; exact h2
          | vote =>
            by_cases hc : q ∈ s.corrupted
            · right ; simp [hc] at h2 ; exact h2
            · simp [hc] at h2
              rcases h2 with rfl | hold
              · left ; exact ⟨rfl, rfl, rfl, hc⟩
              · right ; exact hold
        · right ; simp [hqsrc] at h2 ; exact h2
      -- Four sub-cases
      rcases h1_cases with ⟨rfl, hmv1, ht1, hc1⟩ | h1_old
      · rcases h2_cases with ⟨hq_eq, hmv2, _, _⟩ | h2_old
        · -- Both new votes: same src, so b₁ = b₂ from mv
          rw [← hmv1] at hmv2 ; injection hmv2 with heq ; exact heq.symm
        · -- p = src new, q old. Need b₁ = b₂.
          subst ht1
          -- gate: corrupt src (contradicts hc1) or echo count for b₁
          rcases hgate with hmem | ⟨_, _, _, hecho⟩
          · exact absurd hmem hc1
          · -- mv = some b₁, gate uses some b₁ branch
            rw [← hmv1] at hecho ; simp at hecho
            exact bca_echo_quorum_intersection (T := T) hn s p q b₁ b₂ hbudget hetrace hecho
              (hecho_back q b₂ hq h2_old)
      · rcases h2_cases with ⟨rfl, hmv2, ht2, hc2⟩ | h2_old
        · -- p old, q = src new. Symmetric.
          subst ht2
          rcases hgate with hmem | ⟨_, _, _, hecho⟩
          · exact absurd hmem hc2
          · rw [← hmv2] at hecho ; simp at hecho
            exact bca_echo_quorum_intersection (T := T) hn s p q b₁ b₂ hbudget hetrace
              (hecho_back p b₁ hp h1_old) hecho
        · -- Both old
          exact hvagree p q b₁ b₂ hp hq h1_old h2_old
    · -- 9. echo backing: correct voted(some b) → n-f echo(b)
      intro p b hp hvp
      -- Extract old voted or new voted
      by_cases hpsrc : p = src
      · subst hpsrc
        cases t with
        | init => simp at hvp ⊢ ; exact hecho_back p b hp hvp
        | echo => simp at hvp ⊢ ; exact hecho_back p b hp hvp
        | vote =>
          -- voted may change: new or old
          simp at hvp
          by_cases hc : p ∈ s.corrupted
          · exact absurd hc hp
          · simp [hc] at hvp
            rcases hvp with ⟨rfl, rfl⟩ | hold
            · -- new vote(some b): gate gives echo count
              simp [hc] at hgate
              simp only [countEchoRecv] ; simp ; exact hgate.2.2.2
            · -- old vote: IH
              have := hecho_back p b hp hold
              simp only [countEchoRecv] at this ⊢ ; simp ; exact this
      · simp [hpsrc] at hvp ⊢ ; exact hecho_back p b hp hvp
    · -- 10. echo witness
      intro b ⟨p, hp, hvp⟩
      by_cases hpsrc : p = src
      · subst hpsrc
        cases t with
        | init => simp at hvp ; obtain ⟨q, hq⟩ := hecho_wit b ⟨p, hp, hvp⟩
                  refine ⟨q, ?_⟩
                  simp only [countEchoRecv] at hq ⊢
                  by_cases h : q = p
                  · subst h ; simpa using hq
                  · simpa [h] using hq
        | echo => simp at hvp ; obtain ⟨q, hq⟩ := hecho_wit b ⟨p, hp, hvp⟩
                  refine ⟨q, ?_⟩
                  simp only [countEchoRecv] at hq ⊢
                  by_cases h : q = p
                  · subst h ; simpa using hq
                  · simpa [h] using hq
        | vote =>
          simp at hvp
          by_cases hc : p ∈ s.corrupted
          · exact absurd hc hp
          · simp [hc] at hvp
            rcases hvp with ⟨rfl, rfl⟩ | hold
            · -- new vote: src is echo witness (gate gives count)
              simp [hc] at hgate
              exact ⟨p, by simp only [countEchoRecv] ; simp ; exact hgate.2.2.2⟩
            · obtain ⟨q, hq⟩ := hecho_wit b ⟨p, hp, hold⟩
              refine ⟨q, ?_⟩
              simp only [countEchoRecv] at hq ⊢
              by_cases h : q = p
              · subst h ; simpa using hq
              · simpa [h] using hq
      · simp [hpsrc] at hvp
        obtain ⟨q, hq⟩ := hecho_wit b ⟨p, hp, hvp⟩
        refine ⟨q, ?_⟩
        simp only [countEchoRecv] at hq ⊢
        by_cases h : q = src
        · subst h ; simpa using hq
        · simpa [h] using hq
    · -- 11. count ↔ approved: send doesn't touch initRecv or approved
      intro hnf p b ; constructor
      · -- approved → count: extract pre-state approved, use iff
        intro happ
        have happ' : (s.local_ p).approved b = true := by
          by_cases hpsrc : p = src <;> simpa [hpsrc] using happ
        have := (hcount_app hnf p b).mp happ'
        unfold countInitRecv at this ⊢
        by_cases hpsrc : p = src
        · subst hpsrc ; simpa using this
        · simpa [hpsrc] using this
      · -- count → approved: extract pre-state count, use iff
        intro hcnt
        have hcnt' : countInitRecv T n (s.local_ p) b ≥ approveThreshold n f := by
          unfold countInitRecv at hcnt ⊢
          by_cases hpsrc : p = src
          · subst hpsrc ; cases t <;> simpa using hcnt
          · simpa [hpsrc] using hcnt
        have happ_old := (hcount_app hnf p b).mpr hcnt'
        by_cases hpsrc : p = src
        · subst hpsrc ; cases t <;> simpa using happ_old
        · simpa [hpsrc] using happ_old
    · -- 12. echoed → approved: echoed may change at src for echo send
      intro p b hp hech
      by_cases hpsrc : p = src
      · subst hpsrc ; cases t with
        | init => simp at hech ⊢ ; exact hecho_app p b hp hech
        | vote =>
          by_cases hc : p ∈ s.corrupted
          · exact absurd hc hp
          · simp [hc] at hech ⊢ ; exact hecho_app p b hp hech
        | echo =>
          by_cases hc : p ∈ s.corrupted
          · exact absurd hc hp
          · simp [hc] at hech ⊢ ; cases mv with
            | none => exact hecho_app p b hp hech
            | some bv =>
              injection hech with hech ; subst hech
              rcases hgate with hmem | ⟨_, _, hg⟩
              · exact absurd hmem hp
              · simp at hg ; exact hg.1
      · simp [hpsrc] at hech ⊢ ; exact hecho_app p b hp hech
    · -- 13. init recv trace: initRecv unchanged by send; conclusion fields unchanged
      intro p q v hcorr hirecv
      have hirecv' : (s.local_ p).initRecv q v = true := by
        by_cases hpsrc : p = src
        · subst hpsrc ; simp at hirecv ; exact hirecv
        · simp [hpsrc] at hirecv ; exact hirecv
      rcases hinit_trace p q v hcorr hirecv' with hinp | hamp
      · left ; by_cases hqsrc : q = src
        · subst hqsrc ; simp ; exact hinp
        · simp [hqsrc] ; exact hinp
      · right ; unfold countInitRecv at hamp ⊢
        by_cases hqsrc : q = src
        · subst hqsrc ; simpa using hamp
        · simpa [hqsrc] using hamp
    · -- 14. init buffer trace: new init msg or old
      intro q p v hcorr hbuf
      simp at hbuf
      rcases hbuf with ⟨rfl, rfl, rfl, rfl⟩ | hold
      · -- New message: gate gives input=v or amplification
        rcases hgate with hmem | ⟨_, _, hg⟩
        · exact absurd hmem hcorr
        · -- hg is the init gate condition (after match reduction)
          simp at hg
          rcases hg with hinp | hamp
          · left ; simp ; exact hinp
          · right ; unfold countInitRecv ; simp ; exact hamp
      · -- Old buffer message
        rcases hinit_buf_trace q p v hcorr hold with hinp | hamp
        · left ; by_cases hqsrc : q = src
          · subst hqsrc ; simp ; exact hinp
          · simp [hqsrc] ; exact hinp
        · right ; unfold countInitRecv at hamp ⊢
          by_cases hqsrc : q = src
          · subst hqsrc ; simpa using hamp
          · simpa [hqsrc] using hamp
    · -- 15. init amplification support: countInitRecv and input unchanged by send
      intro q v hcorr hcnt hne
      -- Extract pre-state values (initRecv and input unchanged by send)
      have hcnt' : countInitRecv T n (s.local_ q) v ≥ amplifyThreshold f := by
        unfold countInitRecv at hcnt ⊢
        by_cases hqsrc : q = src <;> simpa [hqsrc] using hcnt
      have hne' : (s.local_ q).input ≠ some v := by
        by_cases hqsrc : q = src <;> simpa [hqsrc] using hne
      -- Use IH and transfer filter
      have hold := hinit_amp q v hcorr hcnt' hne'
      apply Nat.le_trans hold ; apply filter_length_mono
      intro r hr ; simp only [Bool.or_eq_true, decide_eq_true_eq] at hr ⊢
      rcases hr with hmem | hinp
      · exact Or.inl hmem
      · right ; by_cases hrsrc : r = src
        · subst hrsrc ; simp ; exact hinp
        · simp [hrsrc] ; exact hinp
    · -- 16. bot decision backing: decided/approved unchanged by send
      intro p h
      have h' : (s.local_ p).decided = some none := by
        by_cases hpsrc : p = src
        · subst hpsrc ; simp at h ; exact h
        · simp [hpsrc] at h ; exact h
      obtain ⟨v₁, v₂, hne, h1, h2⟩ := hbot_back p h'
      refine ⟨v₁, v₂, hne, ?_, ?_⟩
      · by_cases hpsrc : p = src
        · subst hpsrc ; simp ; exact h1
        · simp [hpsrc] ; exact h1
      · by_cases hpsrc : p = src
        · subst hpsrc ; simp ; exact h2
        · simp [hpsrc] ; exact h2
  | recv src dst t mv =>
    subst htrans
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hbudget -- 1. budget
    · -- 2. echo trace: echoRecv may grow at dst; echoed unchanged by recv
      intro p q b hp h
      by_cases hq : q = dst
      · rw [hq] at h ; cases t with
        | init => cases mv with
          | some bv =>
            by_cases hc : (s.local_ dst).initRecv src bv = false
            · -- echoRecv unchanged by init recv; echoed unchanged
              simp [hc] at h
              have hold := hetrace p dst b hp (hq ▸ h)
              by_cases hpdst : p = dst
              · rw [hpdst] at hold ; simp [hpdst, hc] ; exact hold
              · simp [hpdst] ; exact hold
            · -- state unchanged at dst
              simp [hc] at h
              have hold := hetrace p dst b hp (hq ▸ h)
              by_cases hpdst : p = dst
              · rw [hpdst] at hold ; simp [hpdst, hc] ; exact hold
              · simp [hpdst] ; exact hold
          | none =>
            simp at h
            have hold := hetrace p dst b hp (hq ▸ h)
            by_cases hpdst : p = dst
            · rw [hpdst] at hold ; simp [hpdst] ; exact hold
            · simp [hpdst] ; exact hold
        | echo => cases mv with
          | some bv =>
            by_cases hc : (s.local_ dst).echoRecv src bv = false
            · -- NEW echoRecv entry possible
              simp [hc] at h
              rcases h with ⟨rfl, rfl⟩ | hold
              · -- new entry (src→p, bv→b): use buffer echo trace
                have hechoed := hbet p dst b hp hgate
                by_cases hpdst : p = dst
                · rw [hpdst] at hechoed
                  simp only [apply_ite LocalState.echoed, hpdst, ite_true, ite_self]
                  exact hechoed
                · simp [hpdst] ; exact hechoed
              · -- old entry
                have hechoed := hetrace p dst b hp (hq ▸ hold)
                by_cases hpdst : p = dst
                · rw [hpdst] at hechoed ; simp [hpdst, hc] ; exact hechoed
                · simp [hpdst] ; exact hechoed
            · -- state unchanged at dst
              simp [hc] at h
              have hold := hetrace p dst b hp (hq ▸ h)
              by_cases hpdst : p = dst
              · rw [hpdst] at hold ; simp [hpdst, hc] ; exact hold
              · simp [hpdst] ; exact hold
          | none =>
            simp at h
            have hold := hetrace p dst b hp (hq ▸ h)
            by_cases hpdst : p = dst
            · rw [hpdst] at hold ; simp [hpdst] ; exact hold
            · simp [hpdst] ; exact hold
        | vote =>
          by_cases hc : (s.local_ dst).voteRecv src mv = false
          · simp [hc] at h
            have hold := hetrace p dst b hp (hq ▸ h)
            by_cases hpdst : p = dst
            · rw [hpdst] at hold ; simp [hpdst, hc] ; exact hold
            · simp [hpdst] ; exact hold
          · simp [hc] at h
            have hold := hetrace p dst b hp (hq ▸ h)
            by_cases hpdst : p = dst
            · rw [hpdst] at hold ; simp [hpdst, hc] ; exact hold
            · simp [hpdst] ; exact hold
      · -- q ≠ dst: echoRecv unchanged at q, echoed unchanged at p
        simp [hq] at h
        have hold := hetrace p q b hp h
        by_cases hpdst : p = dst
        · rw [hpdst] at hold ; cases t with
          | init => cases mv with
            | some bv =>
              by_cases hc : (s.local_ dst).initRecv src bv = false
              · simp [hpdst, hc] ; exact hold
              · simp [hpdst, hc] ; exact hold
            | none => simp [hpdst] ; exact hold
          | echo => cases mv with
            | some bv =>
              by_cases hc : (s.local_ dst).echoRecv src bv = false
              · simp [hpdst, hc] ; exact hold
              · simp [hpdst, hc] ; exact hold
            | none => simp [hpdst] ; exact hold
          | vote =>
            by_cases hc : (s.local_ dst).voteRecv src mv = false
            · simp [hpdst, hc] ; exact hold
            · simp [hpdst, hc] ; exact hold
        · simp [hpdst] ; exact hold
    · -- 3. buffer echo trace: buffer shrinks, echoed unchanged
      intro p d b hp hbuf ; simp only [] at hbuf
      have hbuf' : s.buffer ⟨p, d, .echo, some b⟩ = true := by
        by_cases hm : (⟨p, d, .echo, some b⟩ : Message T n) = ⟨src, dst, t, mv⟩
        · obtain ⟨rfl, rfl, rfl, rfl⟩ := Message.mk.inj hm ; exact hgate
        · simp [hm] at hbuf ; exact hbuf
      have hold := hbet p d b hp hbuf'
      by_cases hpdst : p = dst
      · rw [hpdst] at hold ⊢ ; cases t with
        | init => cases mv with
          | some bv => by_cases hc : (s.local_ dst).initRecv src bv = false <;> simp [hc] <;> exact hold
          | none => simp ; exact hold
        | echo => cases mv with
          | some bv => by_cases hc : (s.local_ dst).echoRecv src bv = false <;> simp [hc] <;> exact hold
          | none => simp ; exact hold
        | vote => by_cases hc : (s.local_ dst).voteRecv src mv = false <;> simp [hc] <;> exact hold
      · simp [hpdst] ; exact hold
    · -- 4. vote trace: voteRecv may grow at dst; voted unchanged
      intro p q b hp h
      by_cases hpdst : p = dst
      · rw [hpdst] at h ; cases t with
        | init => cases mv with
          | some bv =>
            by_cases hc : (s.local_ dst).initRecv src bv = false <;> simp [hc] at h <;>
              (have hold := hvtrace dst q b hp h
               by_cases hqdst : q = dst
               · rw [hqdst] at hold ⊢ ; simp [hc] ; exact hold
               · simp [hqdst] ; exact hold)
          | none =>
            simp at h
            have hold := hvtrace dst q b hp h
            by_cases hqdst : q = dst
            · rw [hqdst] at hold ⊢ ; simp ; exact hold
            · simp [hqdst] ; exact hold
        | echo => cases mv with
          | some bv =>
            by_cases hc : (s.local_ dst).echoRecv src bv = false <;> simp [hc] at h <;>
              (have hold := hvtrace dst q b hp h
               by_cases hqdst : q = dst
               · rw [hqdst] at hold ⊢ ; simp [hc] ; exact hold
               · simp [hqdst] ; exact hold)
          | none =>
            simp at h
            have hold := hvtrace dst q b hp h
            by_cases hqdst : q = dst
            · rw [hqdst] at hold ⊢ ; simp ; exact hold
            · simp [hqdst] ; exact hold
        | vote =>
          by_cases hc : (s.local_ dst).voteRecv src mv = false
          · simp [hc] at h
            rcases h with ⟨rfl, rfl⟩ | hold
            · have hvoted := hbvt q dst b hp hgate
              by_cases hqdst : q = dst
              · rw [hqdst] at hvoted ⊢
                simp only [apply_ite LocalState.voted, ite_self] ; exact hvoted
              · simp [hqdst] ; exact hvoted
            · have hold := hvtrace dst q b hp hold
              by_cases hqdst : q = dst
              · rw [hqdst] at hold ⊢ ; simp [hc] ; exact hold
              · simp [hqdst] ; exact hold
          · simp [hc] at h
            have hold := hvtrace dst q b hp h
            by_cases hqdst : q = dst
            · rw [hqdst] at hold ⊢ ; simp [hc] ; exact hold
            · simp [hqdst] ; exact hold
      · simp [hpdst] at h
        have hold := hvtrace p q b hp h
        by_cases hqdst : q = dst
        · rw [hqdst] at hold ⊢ ; cases t with
          | init => cases mv with
            | some bv =>
              by_cases hc : (s.local_ dst).initRecv src bv = false <;>
                simp only [apply_ite LocalState.voted, hc, ite_self] <;> exact hold
            | none => simp ; exact hold
          | echo => cases mv with
            | some bv =>
              by_cases hc : (s.local_ dst).echoRecv src bv = false <;>
                simp only [apply_ite LocalState.voted, hc, ite_self] <;> exact hold
            | none => simp ; exact hold
          | vote =>
            by_cases hc : (s.local_ dst).voteRecv src mv = false <;>
              simp only [apply_ite LocalState.voted, hc, ite_self] <;> exact hold
        · simp [hqdst] ; exact hold
    · -- 5. buffer vote trace: buffer shrinks, voted unchanged
      intro p d b hp hbuf ; simp only [] at hbuf
      have hbuf' : s.buffer ⟨p, d, .vote, some b⟩ = true := by
        by_cases hm : (⟨p, d, .vote, some b⟩ : Message T n) = ⟨src, dst, t, mv⟩
        · obtain ⟨rfl, rfl, rfl, rfl⟩ := Message.mk.inj hm ; exact hgate
        · simp [hm] at hbuf ; exact hbuf
      have hold := hbvt p d b hp hbuf'
      by_cases hpdst : p = dst
      · rw [hpdst] at hold ⊢ ; cases t with
        | init => cases mv with
          | some bv =>
            by_cases hc : (s.local_ dst).initRecv src bv = false <;>
              simp only [apply_ite LocalState.voted, hc, ite_self] <;> exact hold
          | none => simp ; exact hold
        | echo => cases mv with
          | some bv =>
            by_cases hc : (s.local_ dst).echoRecv src bv = false <;>
              simp only [apply_ite LocalState.voted, hc, ite_self] <;> exact hold
          | none => simp ; exact hold
        | vote =>
          by_cases hc : (s.local_ dst).voteRecv src mv = false <;>
            simp only [apply_ite LocalState.voted, hc, ite_self] <;> exact hold
      · simp [hpdst] ; exact hold
    · -- 7. decision backing: decided unchanged, voteRecv monotone
      intro p b hdec
      have hdec' : (s.local_ p).decided = some (some b) := by
        by_cases hpdst : p = dst
        · rw [hpdst] at hdec ⊢ ; cases t with
          | init => cases mv with
            | some bv => by_cases hc : (s.local_ dst).initRecv src bv = false <;> simp [hc] at hdec <;> exact hdec
            | none => simp at hdec ; exact hdec
          | echo => cases mv with
            | some bv => by_cases hc : (s.local_ dst).echoRecv src bv = false <;> simp [hc] at hdec <;> exact hdec
            | none => simp at hdec ; exact hdec
          | vote => by_cases hc : (s.local_ dst).voteRecv src mv = false <;> simp [hc] at hdec <;> exact hdec
        · simp [hpdst] at hdec ; exact hdec
      have hold := hvback p b hdec'
      simp only [countVoteRecv] at hold ⊢
      apply Nat.le_trans hold ; apply filter_length_mono ; intro q hq
      by_cases hpdst : p = dst
      · rw [hpdst] at hq ⊢ ; cases t with
        | init => cases mv with
          | some bv => by_cases hc : (s.local_ dst).initRecv src bv = false <;> simp [hc] <;> exact hq
          | none => simp ; exact hq
        | echo => cases mv with
          | some bv => by_cases hc : (s.local_ dst).echoRecv src bv = false <;> simp [hc] <;> exact hq
          | none => simp ; exact hq
        | vote =>
          by_cases hc : (s.local_ dst).voteRecv src mv = false
          · simp [hc]
            by_cases hqv : q = src ∧ (some b : Val T) = mv
            · obtain ⟨rfl, rfl⟩ := hqv ; simp
            · simp [hqv] ; exact hq
          · simp [hc] ; exact hq
      · simp [hpdst] ; exact hq
    · -- 8. vote agreement: voted unchanged by recv
      intro p q b₁ b₂ hp hq h1 h2
      have h1' : (s.local_ p).voted (some b₁) = true := by
        by_cases h : p = dst
        · subst h ; cases t with
          | init => cases mv with
            | some _ => dsimp only [] at h1 ; simp only [apply_ite LocalState.voted, ite_self] at h1 ; exact h1
            | none => dsimp only [] at h1 ; simp only [apply_ite LocalState.voted] at h1 ; exact h1
          | echo => cases mv with
            | some _ => dsimp only [] at h1 ; simp only [apply_ite LocalState.voted, ite_self] at h1 ; exact h1
            | none => dsimp only [] at h1 ; simp only [ite_self] at h1 ; exact h1
          | vote => dsimp only [] at h1 ; simp only [apply_ite LocalState.voted, ite_self] at h1 ; exact h1
        · simp [h] at h1 ; exact h1
      have h2' : (s.local_ q).voted (some b₂) = true := by
        by_cases h : q = dst
        · subst h ; cases t with
          | init => cases mv with
            | some _ => dsimp only [] at h2 ; simp only [apply_ite LocalState.voted, ite_self] at h2 ; exact h2
            | none => dsimp only [] at h2 ; simp only [apply_ite LocalState.voted] at h2 ; exact h2
          | echo => cases mv with
            | some _ => dsimp only [] at h2 ; simp only [apply_ite LocalState.voted, ite_self] at h2 ; exact h2
            | none => dsimp only [] at h2 ; simp only [ite_self] at h2 ; exact h2
          | vote => dsimp only [] at h2 ; simp only [apply_ite LocalState.voted, ite_self] at h2 ; exact h2
        · simp [h] at h2 ; exact h2
      exact hvagree p q b₁ b₂ hp hq h1' h2'
    · -- 9. echo backing: voted unchanged, echoRecv may grow
      intro p b hp hvp
      -- Extract old voted
      have hvp' : (s.local_ p).voted (some b) = true := by
        by_cases h : p = dst
        · subst h ; cases t with
          | init => cases mv with
            | some bv => dsimp only [] at hvp ; simp only [apply_ite LocalState.voted, ite_self] at hvp ; exact hvp
            | none => dsimp only [] at hvp ; simp only [apply_ite LocalState.voted] at hvp ; exact hvp
          | echo => cases mv with
            | some bv => dsimp only [] at hvp ; simp only [apply_ite LocalState.voted, ite_self] at hvp ; exact hvp
            | none => dsimp only [] at hvp ; simp only [ite_self] at hvp ; exact hvp
          | vote => dsimp only [] at hvp ; simp only [apply_ite LocalState.voted, ite_self] at hvp ; exact hvp
        · simp [h] at hvp ; exact hvp
      have hold := hecho_back p b hp hvp'
      -- echoRecv monotone: count in new state ≥ count in old state
      simp only [countEchoRecv] at hold ⊢
      apply Nat.le_trans hold ; apply filter_length_mono ; intro q hq
      by_cases h : p = dst
      · subst h ; cases t with
        | init => cases mv with
          | some bv => dsimp only [] ; simp only [apply_ite LocalState.echoRecv, ite_self] ; exact hq
          | none => dsimp only [] ; simp only [apply_ite LocalState.echoRecv] ; exact hq
        | echo => cases mv with
          | some bv => dsimp only [] ; simp only [apply_ite LocalState.echoRecv]
                       split
                       · split
                         · dsimp only []
                           show (decide (q = src) && decide (b = bv) ||
                                (s.local_ p).echoRecv q b) = true
                           simp [hq]
                         · exact hq
                       · exact hq
          | none => dsimp only [] ; simp only [ite_self] ; exact hq
        | vote => dsimp only [] ; simp only [apply_ite LocalState.echoRecv, ite_self] ; exact hq
      · simp [h] ; exact hq
    · -- 10. echo witness: voted unchanged, echoRecv monotone → old witness persists
      intro b ⟨p, hp, hvp⟩
      have hvp' : (s.local_ p).voted (some b) = true := by
        by_cases h : p = dst
        · subst h ; cases t with
          | init => cases mv with
            | some bv => dsimp only [] at hvp ; simp only [apply_ite LocalState.voted, ite_self] at hvp ; exact hvp
            | none => dsimp only [] at hvp ; simp only [apply_ite LocalState.voted] at hvp ; exact hvp
          | echo => cases mv with
            | some bv => dsimp only [] at hvp ; simp only [apply_ite LocalState.voted, ite_self] at hvp ; exact hvp
            | none => dsimp only [] at hvp ; simp only [ite_self] at hvp ; exact hvp
          | vote => dsimp only [] at hvp ; simp only [apply_ite LocalState.voted, ite_self] at hvp ; exact hvp
        · simp [h] at hvp ; exact hvp
      obtain ⟨q, hq⟩ := hecho_wit b ⟨p, hp, hvp'⟩
      refine ⟨q, ?_⟩ ; simp only [countEchoRecv] at hq ⊢
      apply Nat.le_trans hq ; apply filter_length_mono ; intro r hr
      by_cases h : q = dst
      · subst h ; cases t with
        | init => cases mv with
          | some bv => dsimp only [] ; simp only [apply_ite LocalState.echoRecv, ite_self] ; exact hr
          | none => dsimp only [] ; simp only [apply_ite LocalState.echoRecv] ; exact hr
        | echo => cases mv with
          | some bv => dsimp only [] ; simp only [apply_ite LocalState.echoRecv]
                       split
                       · split
                         · dsimp only []
                           show (decide (r = src) && decide (b = bv) ||
                                (s.local_ q).echoRecv r b) = true
                           simp [hr]
                         · exact hr
                       · exact hr
          | none => dsimp only [] ; simp only [ite_self] ; exact hr
        | vote => dsimp only [] ; simp only [apply_ite LocalState.echoRecv, ite_self] ; exact hr
      · simp [h] ; exact hr
    · -- 11. count ↔ approved (recv case)
      intro hnf p b ; constructor
      · -- approved → count: simplify goal to reduce post-state to pre-state
        intro happ ; by_cases hpdst : p = dst
        · subst hpdst ; cases t with
          | echo => cases mv with
            | none => simp at happ ⊢ ; exact (hcount_app hnf p b).mp happ
            | some bv =>
              by_cases hc : (s.local_ p).echoRecv src bv = false
              · simp [hc] at happ ⊢ ; exact (hcount_app hnf p b).mp happ
              · simp [hc] at happ ⊢ ; exact (hcount_app hnf p b).mp happ
          | vote =>
            by_cases hc : (s.local_ p).voteRecv src mv = false
            · simp [hc] at happ ⊢ ; exact (hcount_app hnf p b).mp happ
            · simp [hc] at happ ⊢ ; exact (hcount_app hnf p b).mp happ
          | init => cases mv with
            | none => simp at happ ⊢ ; exact (hcount_app hnf p b).mp happ
            | some bv =>
              by_cases halready : (s.local_ p).initRecv src bv = false
              · simp [halready] at happ
                rcases happ with ⟨rfl, hthresh⟩ | happ_old
                · -- threshold just crossed: new count = old + 1 ≥ threshold
                  unfold countInitRecv ; simp only [ite_true]
                  rw [if_pos halready]
                  simp only [decide_true, Bool.and_true]
                  have := filter_succ_of_new (fun q => (s.local_ p).initRecv q b) src halready
                  rw [this] ; exact hthresh
                · -- old approved: count monotone (initRecv only grows)
                  have hold := (hcount_app hnf p b).mp happ_old
                  unfold countInitRecv at hold ⊢ ; simp only [ite_true]
                  rw [if_pos halready]
                  apply Nat.le_trans hold ; apply filter_length_mono
                  intro r hr ; simp [hr]
              · simp [halready] at happ ⊢ ; exact (hcount_app hnf p b).mp happ
        · simp [hpdst] at happ ⊢ ; exact (hcount_app hnf p b).mp happ
      · -- count → approved
        intro hcnt ; by_cases hpdst : p = dst
        · subst hpdst ; cases t with
        | echo =>
          -- echo recv: initRecv and approved unchanged at p
          cases mv with
          | none =>
            simp only [if_true] at hcnt ⊢
            exact (hcount_app hnf p b).mpr hcnt
          | some bv =>
            simp only [if_true] at hcnt ⊢
            by_cases hifr : (s.local_ p).echoRecv src bv = false
            · rw [if_pos hifr] at hcnt ⊢
              exact (hcount_app hnf p b).mpr hcnt
            · rw [if_neg hifr] at hcnt ⊢
              exact (hcount_app hnf p b).mpr hcnt
        | vote =>
          -- vote recv: initRecv and approved unchanged at p
          simp only [if_true] at hcnt ⊢
          by_cases hifr : (s.local_ p).voteRecv src mv = false
          · rw [if_pos hifr] at hcnt ⊢
            exact (hcount_app hnf p b).mpr hcnt
          · rw [if_neg hifr] at hcnt ⊢
            exact (hcount_app hnf p b).mpr hcnt
        | init =>
          cases mv with
          | none =>
            simp only [if_true] at hcnt ⊢
            exact (hcount_app hnf p b).mpr hcnt
          | some bv =>
            simp only [if_true] at hcnt ⊢
            by_cases halready : (s.local_ p).initRecv src bv = false
            · rw [if_pos halready] at hcnt ⊢
              -- New local at p: initRecv updated for (src, bv), approved possibly flipped.
              by_cases hbeq : b = bv
              · -- b = bv: count grew by 1, approved set if threshold crossed
                subst hbeq
                show (decide (b = b) && decide (approveThreshold n f ≤
                    countInitRecv T n (s.local_ p) b + 1) || (s.local_ p).approved b) = true
                simp only [decide_true, Bool.true_and]
                -- Compute new count = old count + 1
                have hcnt_grow : countInitRecv T n (s.local_ p) b + 1 ≥ approveThreshold n f := by
                  have heq : ((List.finRange n).filter
                      (fun q => decide (q = src) || (s.local_ p).initRecv q b)).length =
                      countInitRecv T n (s.local_ p) b + 1 :=
                    filter_succ_of_new (fun q => (s.local_ p).initRecv q b) src halready
                  unfold countInitRecv at hcnt
                  simp only [decide_true, Bool.and_true] at hcnt
                  rw [heq] at hcnt
                  omega
                have : decide (approveThreshold n f ≤ countInitRecv T n (s.local_ p) b + 1) = true := by
                  simp [hcnt_grow]
                rw [this] ; simp
              · -- b ≠ bv: count and approved for b unchanged
                show (decide (b = bv) && decide (approveThreshold n f ≤
                    countInitRecv T n (s.local_ p) bv + 1) || (s.local_ p).approved b) = true
                have hbeq_false : decide (b = bv) = false := by simp [hbeq]
                rw [hbeq_false] ; simp
                -- Reduce new count b to old count b
                have hcnt' : countInitRecv T n (s.local_ p) b ≥ approveThreshold n f := by
                  have heq : ((List.finRange n).filter
                      (fun q => decide (q = src) && decide (b = bv) || (s.local_ p).initRecv q b)).length =
                      countInitRecv T n (s.local_ p) b := by
                    unfold countInitRecv
                    congr 1
                    apply List.filter_congr
                    intro q _
                    show (decide (q = src) && decide (b = bv) || (s.local_ p).initRecv q b) =
                         (s.local_ p).initRecv q b
                    rw [hbeq_false] ; simp
                  unfold countInitRecv at hcnt
                  simp only [hbeq_false, Bool.and_false, Bool.false_or] at hcnt
                  exact hcnt
                exact (hcount_app hnf p b).mpr hcnt'
            · rw [if_neg halready] at hcnt ⊢
              exact (hcount_app hnf p b).mpr hcnt
        · -- p ≠ dst: local state at p unchanged
          simp [hpdst] at hcnt ⊢
          exact (hcount_app hnf p b).mpr hcnt
    · -- 12. echoed → approved: echoed unchanged by recv, approved monotone
      intro p b hp hech
      by_cases hpdst : p = dst
      · subst hpdst
        -- echoed unchanged at dst by recv. approved may grow but not shrink.
        have hech' : (s.local_ p).echoed = some b := by
          cases t <;> (try cases mv) <;> simp at hech <;>
            (try split at hech) <;> (try simp at hech) <;> exact hech
        have happ := hecho_app p b hp hech'
        -- approved is monotone: old true stays true
        cases t with
        | echo => cases mv with
          | none => simpa using happ
          | some bv =>
            by_cases hc : (s.local_ p).echoRecv src bv = false
            · simp [hc] ; exact happ
            · simp [hc] ; exact happ
        | vote =>
          by_cases hc : (s.local_ p).voteRecv src mv = false
          · simp [hc] ; exact happ
          · simp [hc] ; exact happ
        | init => cases mv with
          | none => simpa using happ
          | some bv =>
            by_cases halready : (s.local_ p).initRecv src bv = false
            · simp [halready]
              -- approved may have been set for bv. But we need approved b.
              -- If b = bv: either it was already true or threshold just crossed → true either way
              -- If b ≠ bv: approved b unchanged
              by_cases hbeq : b = bv
              · subst hbeq ; simp ; exact Or.inr happ
              · simp [hbeq] ; exact happ
            · simp [halready] ; exact happ
      · simp [hpdst] at hech ⊢ ; exact hecho_app p b hp hech
    · -- 13. init recv trace: source q's input preserved, countInitRecv monotone
      intro p q v hcorr hirecv
      -- Step 1: get pre-state conclusion (input=v or amplified)
      have hpre : (s.local_ q).input = some v ∨
          countInitRecv T n (s.local_ q) v ≥ amplifyThreshold f := by
        -- Extract old initRecv or new entry (p=dst, q=src, v=bv for init recv)
        by_cases hpdst : p = dst
        · subst hpdst
          cases t with
          | echo => cases mv with
            | none => simp at hirecv ; exact hinit_trace p q v hcorr hirecv
            | some bv =>
              by_cases hc : (s.local_ p).echoRecv src bv = false
              · simp [hc] at hirecv ; exact hinit_trace p q v hcorr hirecv
              · simp [hc] at hirecv ; exact hinit_trace p q v hcorr hirecv
          | vote =>
            by_cases hc : (s.local_ p).voteRecv src mv = false
            · simp [hc] at hirecv ; exact hinit_trace p q v hcorr hirecv
            · simp [hc] at hirecv ; exact hinit_trace p q v hcorr hirecv
          | init => cases mv with
            | none => simp at hirecv ; exact hinit_trace p q v hcorr hirecv
            | some bv =>
              by_cases halready : (s.local_ p).initRecv src bv = false
              · simp [halready] at hirecv
                rcases hirecv with ⟨rfl, rfl⟩ | hold
                · exact hinit_buf_trace q p v hcorr hgate
                · exact hinit_trace p q v hcorr hold
              · simp [halready] at hirecv ; exact hinit_trace p q v hcorr hirecv
        · simp [hpdst] at hirecv ; exact hinit_trace p q v hcorr hirecv
      -- Step 2: transfer pre-state conclusion to post-state
      -- input preserved: by_cases q = dst, simp through the struct
      -- Transfer conclusion to post-state by simplifying the goal.
      -- q's input and countInitRecv only differ from pre-state when q = dst.
      rcases hpre with hinp | hamp
      · left ; by_cases hqdst : q = dst
        · subst hqdst ; cases t with
          | init => cases mv with
            | none => simp ; exact hinp
            | some bv =>
              by_cases hc : (s.local_ q).initRecv src bv = false
              · simp [hc] ; exact hinp
              · simp [hc] ; exact hinp
          | echo => cases mv with
            | none => simp ; exact hinp
            | some bv =>
              by_cases hc : (s.local_ q).echoRecv src bv = false
              · simp [hc] ; exact hinp
              · simp [hc] ; exact hinp
          | vote =>
            by_cases hc : (s.local_ q).voteRecv src mv = false
            · simp [hc] ; exact hinp
            · simp [hc] ; exact hinp
        · simp [hqdst] ; exact hinp
      · right ; by_cases hqdst : q = dst
        · subst hqdst ; unfold countInitRecv at hamp ⊢
          apply Nat.le_trans hamp ; apply filter_length_mono
          intro r hr ; cases t with
          | init => cases mv with
            | none => simp ; exact hr
            | some bv =>
              simp only [ite_true]
              by_cases hc : (s.local_ q).initRecv src bv = false
              · rw [if_pos hc] ; simp [hr]
              · rw [if_neg hc] ; exact hr
          | echo => cases mv with
            | none => simp ; exact hr
            | some bv =>
              simp only [ite_true]
              by_cases hc : (s.local_ q).echoRecv src bv = false
              · rw [if_pos hc] ; exact hr
              · rw [if_neg hc] ; exact hr
          | vote =>
            simp only [ite_true]
            by_cases hc : (s.local_ q).voteRecv src mv = false
            · rw [if_pos hc] ; exact hr
            · rw [if_neg hc] ; exact hr
        · simp [hqdst] ; exact hamp
    · -- 14. init buffer trace: buffer shrinks; source fields unchanged
      intro q p v hcorr hbuf
      simp at hbuf
      have hpre := hinit_buf_trace q p v hcorr hbuf.2
      rcases hpre with hinp | hamp
      · left ; by_cases hqdst : q = dst
        · subst hqdst ; cases t with
          | init => cases mv with
            | none => simp ; exact hinp
            | some bv =>
              by_cases hc : (s.local_ q).initRecv src bv = false
              · simp [hc] ; exact hinp
              · simp [hc] ; exact hinp
          | echo => cases mv with
            | none => simp ; exact hinp
            | some bv =>
              by_cases hc : (s.local_ q).echoRecv src bv = false
              · simp [hc] ; exact hinp
              · simp [hc] ; exact hinp
          | vote =>
            by_cases hc : (s.local_ q).voteRecv src mv = false
            · simp [hc] ; exact hinp
            · simp [hc] ; exact hinp
        · simp [hqdst] ; exact hinp
      · right ; by_cases hqdst : q = dst
        · subst hqdst ; unfold countInitRecv at hamp ⊢
          apply Nat.le_trans hamp ; apply filter_length_mono
          intro r hr ; cases t with
          | init => cases mv with
            | none => simp ; exact hr
            | some bv =>
              simp only [ite_true]
              by_cases hc : (s.local_ q).initRecv src bv = false
              · rw [if_pos hc] ; simp [hr]
              · rw [if_neg hc] ; exact hr
          | echo => cases mv with
            | none => simp ; exact hr
            | some bv =>
              simp only [ite_true]
              by_cases hc : (s.local_ q).echoRecv src bv = false
              · rw [if_pos hc] ; exact hr
              · rw [if_neg hc] ; exact hr
          | vote =>
            simp only [ite_true]
            by_cases hc : (s.local_ q).voteRecv src mv = false
            · rw [if_pos hc] ; exact hr
            · rw [if_neg hc] ; exact hr
        · simp [hqdst] ; exact hamp
    · -- 15. init amplification support: sent/input unchanged, countInitRecv may grow at dst
      intro q v hcorr hcnt hne
      -- Transfer: reduce goal to s-filter via recv_input_eq
      suffices hsuff : ((List.finRange n).filter (fun r =>
          decide (r ∈ s.corrupted) || decide ((s.local_ r).input = some v))).length ≥ f + 1 by
        apply Nat.le_trans hsuff ; apply filter_length_mono
        intro r hr ; simp only [Bool.or_eq_true, decide_eq_true_eq] at hr ⊢
        rcases hr with hmem | hinp
        · exact Or.inl hmem
        · right ; rw [← recv_input_eq T n f s src dst t mv r] at hinp
          by_cases hrdst : r = dst <;> simp [hrdst] at hinp ⊢ <;> exact hinp
      -- Extract pre-state countInitRecv and input for q
      have hne' : (s.local_ q).input ≠ some v := by
        by_cases hqdst : q = dst
        · subst hqdst
          cases t <;> (try cases mv) <;> simp at hne <;>
            (try split at hne) <;> (try simp at hne) <;> exact hne
        · simp [hqdst] at hne ; exact hne
      -- For q ≠ dst or non-init recv: countInitRecv unchanged → use hinit_amp IH.
      -- For q = dst, init recv of (some v) with new source: post count = old + 1.
      -- If old ≥ f+1: use hinit_amp IH. If old = f: use the counting argument
      -- on the f+1 post-state sources directly.
      -- Handle the hard case first: q = dst, init recv, v = bv, new source.
      by_cases hhard : q = dst ∧ t = .init ∧ (∃ bv, mv = some bv ∧ v = bv ∧
          (s.local_ dst).initRecv src bv = false)
      · -- Hard case: threshold crossing at dst for value v
        obtain ⟨rfl, rfl, bv, rfl, rfl, halready⟩ := hhard
        simp [halready, countInitRecv] at hcnt
        -- hcnt: f+1 ≤ |{r : r = src ∨ old initRecv q r v}| (post-state sources).
        -- For each source r: corrupted ∨ input=v ∨ amplified (by traces).
        -- If any is a correct amplifier: hinit_amp gives filter ≥ f+1 directly.
        -- If all in corrupted ∪ input=v: filter_length_mono gives ≥ f+1.
        -- Check: does every post-state source land in corrupted ∪ input=v?
        by_cases hall : ∀ r, (decide (r = src) || (s.local_ q).initRecv r v) = true →
            (decide (r ∈ s.corrupted) || decide ((s.local_ r).input = some v)) = true
        · -- All sources in filter → filter_length_mono
          apply Nat.le_trans hcnt ; apply filter_length_mono ; exact hall
        · -- Some source r NOT in filter: r is correct with input ≠ v
          have ⟨r, hr_src, hr_not⟩ : ∃ r, (decide (r = src) || (s.local_ q).initRecv r v) = true ∧
              (decide (r ∈ s.corrupted) || decide ((s.local_ r).input = some v)) = false := by
            by_contra h
            apply hall ; intro r hr
            by_contra hc
            exact h ⟨r, hr, Bool.not_eq_true _ |>.mp hc⟩
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hr_src
          have hr_corr : r ∉ s.corrupted := by
            intro h ; simp [h] at hr_not
          have hr_ne : (s.local_ r).input ≠ some v := by
            intro h ; simp [h, hr_corr] at hr_not
          -- r is correct with input ≠ v. By trace: r amplified.
          rcases hr_src with rfl | hr_old
          · -- r = src: by hinit_buf_trace, input=v (contradicts hr_ne) or amplified
            rcases hinit_buf_trace r q v hr_corr hgate with hinp | hamp
            · exact absurd hinp hr_ne
            · exact hinit_amp r v hr_corr hamp hr_ne
          · -- r is old initRecv source: by hinit_trace, input=v or amplified
            rcases hinit_trace q r v hr_corr hr_old with hinp | hamp
            · exact absurd hinp hr_ne
            · exact hinit_amp r v hr_corr hamp hr_ne
      · -- Easy case: countInitRecv unchanged or v ≠ bv → old count ≥ f+1
        have hcnt_old : countInitRecv T n (s.local_ q) v ≥ amplifyThreshold f := by
          by_cases hqdst : q = dst
          · subst hqdst
            cases t with
            | echo => cases mv <;> simp [countInitRecv] at hcnt <;>
                (try split at hcnt) <;> exact hcnt
            | vote => simp [countInitRecv] at hcnt
                      by_cases hc : (s.local_ q).voteRecv src mv = false <;>
                        simp [hc] at hcnt <;> exact hcnt
            | init => cases mv with
              | none => simp [countInitRecv] at hcnt ; exact hcnt
              | some bv =>
                by_cases halready : (s.local_ q).initRecv src bv = false
                · simp [halready, countInitRecv] at hcnt
                  by_cases hveq : v = bv
                  · exfalso ; exact hhard ⟨rfl, rfl, bv, rfl, hveq, halready⟩
                  · unfold countInitRecv
                    apply Nat.le_trans hcnt ; apply filter_length_mono
                    intro r hr
                    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hr
                    rcases hr with ⟨_, hvbv⟩ | hold
                    · exact absurd hvbv hveq
                    · exact hold
                · simp [halready, countInitRecv] at hcnt ; exact hcnt
          · simp [hqdst, countInitRecv] at hcnt ; exact hcnt
        exact hinit_amp q v hcorr hcnt_old hne'
    · -- 16. bot decision backing: decided unchanged by recv, approved monotone
      intro p h
      -- Extract old decided (unchanged by recv)
      have h' : (s.local_ p).decided = some none := by
        by_cases hpdst : p = dst
        · subst hpdst ; cases t <;> (try cases mv) <;> simp at h <;>
            (try split at h) <;> (try simp at h) <;> exact h
        · simp [hpdst] at h ; exact h
      obtain ⟨v₁, v₂, hne, h1, h2⟩ := hbot_back p h'
      -- Transfer approved (monotone at dst for init recv, unchanged otherwise)
      refine ⟨v₁, v₂, hne, ?_, ?_⟩ <;> by_cases hpdst : p = dst
      · subst hpdst ; cases t with
        | echo => cases mv with
          | none => simp ; exact h1
          | some bv =>
            by_cases hc : (s.local_ p).echoRecv src bv = false
            · simp [hc] ; exact h1
            · simp [hc] ; exact h1
        | vote =>
          by_cases hc : (s.local_ p).voteRecv src mv = false
          · simp [hc] ; exact h1
          · simp [hc] ; exact h1
        | init => cases mv with
          | none => simp ; exact h1
          | some bv =>
            by_cases halready : (s.local_ p).initRecv src bv = false
            · simp [halready] ; exact Or.inr h1
            · simp [halready] ; exact h1
      · simp [hpdst] ; exact h1
      · subst hpdst ; cases t with
        | echo => cases mv with
          | none => simp ; exact h2
          | some bv =>
            by_cases hc : (s.local_ p).echoRecv src bv = false
            · simp [hc] ; exact h2
            · simp [hc] ; exact h2
        | vote =>
          by_cases hc : (s.local_ p).voteRecv src mv = false
          · simp [hc] ; exact h2
          · simp [hc] ; exact h2
        | init => cases mv with
          | none => simp ; exact h2
          | some bv =>
            by_cases halready : (s.local_ p).initRecv src bv = false
            · simp [halready] ; exact Or.inr h2
            · simp [halready] ; exact h2
      · simp [hpdst] ; exact h2
  | decide i mv =>
    subst htrans
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hbudget -- 1. budget
    · -- 2. echo trace: echoRecv/echoed unchanged
      intro p q b hp h
      have hq' : (s.local_ q).echoRecv p b = true := by
        by_cases hq : q = i
        · rw [hq] ; simp [hq] at h ; exact h
        · simp [hq] at h ; exact h
      have h' := hetrace p q b hp hq'
      by_cases hp' : p = i
      · rw [hp'] ; simp ; rw [← hp'] ; exact h'
      · simp [hp'] ; exact h'
    · -- 3. buffer echo trace: buffer unchanged
      intro p d b hp h ; have h' := hbet p d b hp h
      by_cases hp' : p = i
      · rw [hp'] ; simp ; rw [← hp'] ; exact h'
      · simp [hp'] ; exact h'
    · -- 4. vote trace: voteRecv/voted unchanged
      intro p q b hp h
      have hp'' : (s.local_ p).voteRecv q (some b) = true := by
        by_cases hp' : p = i
        · rw [hp'] ; simp [hp'] at h ; exact h
        · simp [hp'] at h ; exact h
      have h' := hvtrace p q b hp hp''
      by_cases hq : q = i
      · rw [hq] ; simp ; rw [← hq] ; exact h'
      · simp [hq] ; exact h'
    · -- 5. buffer vote trace: buffer unchanged
      intro p d b hp h ; have h' := hbvt p d b hp h
      by_cases hp' : p = i
      · rw [hp'] ; simp ; rw [← hp'] ; exact h'
      · simp [hp'] ; exact h'
    · -- 7. decision backing
      intro p b hdec ; by_cases hpi : p = i
      · subst hpi ; simp at hdec ; subst hdec ; simp ; exact hgate.2.2
      · simp [hpi] at hdec ⊢ ; exact hvback p b hdec
    · -- 8. vote agreement: voted unchanged
      intro p q b₁ b₂ hp hq h1 h2
      have h1' : (s.local_ p).voted (some b₁) = true := by
        by_cases h : p = i
        · rw [h] ; simp [h] at h1 ; exact h1
        · simp [h] at h1 ; exact h1
      have h2' : (s.local_ q).voted (some b₂) = true := by
        by_cases h : q = i
        · rw [h] ; simp [h] at h2 ; exact h2
        · simp [h] at h2 ; exact h2
      exact hvagree p q b₁ b₂ hp hq h1' h2'
    · -- 9. echo backing: voted/echoRecv unchanged
      intro p b hp hvp
      have hvp' : (s.local_ p).voted (some b) = true := by
        by_cases h : p = i
        · rw [h] ; simp [h] at hvp ; exact hvp
        · simp [h] at hvp ; exact hvp
      have h' := hecho_back p b hp hvp'
      simp only [countEchoRecv] at h' ⊢
      by_cases hpi : p = i
      · rw [hpi] ; simp ; rw [← hpi] ; exact h'
      · simp [hpi] ; exact h'
    · -- 10. echo witness: voted unchanged
      intro b ⟨p, hp, hvp⟩
      have hvp' : (s.local_ p).voted (some b) = true := by
        by_cases h : p = i
        · rw [h] ; simp [h] at hvp ; exact hvp
        · simp [h] at hvp ; exact hvp
      obtain ⟨q, hq⟩ := hecho_wit b ⟨p, hp, hvp'⟩
      refine ⟨q, ?_⟩ ; simp only [countEchoRecv] at hq ⊢
      by_cases h : q = i
      · rw [h] ; simp ; rw [← h] ; exact hq
      · simp [h] ; exact hq
    · -- 11. count ↔ approved: decide doesn't touch initRecv or approved
      intro hnf p b ; constructor
      · intro happ
        have happ' : (s.local_ p).approved b = true := by
          by_cases hpi : p = i
          · subst hpi ; simpa using happ
          · simpa [hpi] using happ
        have := (hcount_app hnf p b).mp happ'
        unfold countInitRecv at this ⊢
        by_cases hpi : p = i
        · subst hpi ; simpa using this
        · simpa [hpi] using this
      · intro hcnt
        have hcnt' : countInitRecv T n (s.local_ p) b ≥ approveThreshold n f := by
          unfold countInitRecv at hcnt ⊢
          by_cases hpi : p = i
          · subst hpi ; simpa using hcnt
          · simpa [hpi] using hcnt
        have happ_old := (hcount_app hnf p b).mpr hcnt'
        by_cases hpi : p = i
        · subst hpi ; simpa using happ_old
        · simpa [hpi] using happ_old
    · -- 12. echoed → approved: both unchanged by decide
      intro p b hp hech
      have hech' : (s.local_ p).echoed = some b := by
        by_cases hpi : p = i
        · rw [hpi] ; simp [hpi] at hech ; exact hech
        · simp [hpi] at hech ; exact hech
      have happ := hecho_app p b hp hech'
      by_cases hpi : p = i
      · rw [hpi] ; simp ; rw [← hpi] ; exact happ
      · simp [hpi] ; exact happ
    · -- 13. init recv trace: initRecv/input/countInitRecv unchanged by decide
      intro p q v hcorr hirecv
      have hirecv' : (s.local_ p).initRecv q v = true := by
        by_cases hpi : p = i
        · subst hpi ; simp at hirecv ; exact hirecv
        · simp [hpi] at hirecv ; exact hirecv
      rcases hinit_trace p q v hcorr hirecv' with hinp | hamp
      · left ; by_cases hqi : q = i
        · subst hqi ; simp ; exact hinp
        · simp [hqi] ; exact hinp
      · right ; unfold countInitRecv at hamp ⊢
        by_cases hqi : q = i
        · subst hqi ; simpa using hamp
        · simpa [hqi] using hamp
    · -- 14. init buffer trace: buffer unchanged by decide
      intro q p v hcorr hbuf
      rcases hinit_buf_trace q p v hcorr hbuf with hinp | hamp
      · left ; by_cases hqi : q = i
        · subst hqi ; simp ; exact hinp
        · simp [hqi] ; exact hinp
      · right ; unfold countInitRecv at hamp ⊢
        by_cases hqi : q = i
        · subst hqi ; simpa using hamp
        · simpa [hqi] using hamp
    · -- 15. init amplification support: sent/countInitRecv/input unchanged by decide
      intro q v hcorr hcnt hne
      have hcnt' : countInitRecv T n (s.local_ q) v ≥ amplifyThreshold f := by
        unfold countInitRecv at hcnt ⊢
        by_cases hqi : q = i <;> simpa [hqi] using hcnt
      have hne' : (s.local_ q).input ≠ some v := by
        by_cases hqi : q = i <;> simpa [hqi] using hne
      have hold := hinit_amp q v hcorr hcnt' hne'
      apply Nat.le_trans hold ; apply filter_length_mono
      intro r hr ; simp only [Bool.or_eq_true, decide_eq_true_eq] at hr ⊢
      rcases hr with hmem | hinp
      · exact Or.inl hmem
      · right ; by_cases hri : r = i
        · subst hri ; simp ; exact hinp
        · simp [hri] ; exact hinp
    · -- 16. bot decision backing: decide sets decided at i
      intro p h
      by_cases hpi : p = i
      · -- p = i: old decided = none (gate), new decided = some mv = some none → mv = none.
        -- Gate for ⊥: two approved values. approved unchanged by decide.
        -- Use hbot_back on the pre-state... but pre-state has decided = none ≠ some none.
        -- Instead, extract the gate info directly.
        -- The gate (after simp) gives: isCorrect ∧ decided = none ∧ (match mv ...).
        -- For mv = none: ∃ v₁ v₂, v₁ ≠ v₂ ∧ approved v₁ ∧ approved v₂.
        subst hpi ; simp at h
        -- h : mv = none. Extract gate info for mv = none.
        have hgate' : ∃ v₁ v₂, v₁ ≠ v₂ ∧ (s.local_ p).approved v₁ = true ∧
            (s.local_ p).approved v₂ = true := by
          simp at hgate ; rcases hgate with ⟨_, _, hg⟩
          rcases mv with _ | b
          · exact hg.1
          · simp at h
        obtain ⟨v₁, v₂, hne, h1, h2⟩ := hgate'
        exact ⟨v₁, v₂, hne, by simp ; exact h1, by simp ; exact h2⟩
      · simp [hpi] at h
        obtain ⟨v₁, v₂, hne, h1, h2⟩ := hbot_back p h
        exact ⟨v₁, v₂, hne, by simp [hpi] ; exact h1, by simp [hpi] ; exact h2⟩
  | set_input i w =>
    subst htrans
    -- set_input only changes `input` at process i. All other fields are unchanged.
    refine ⟨hbudget, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- 2. echo trace: echoRecv/echoed unchanged
      intro p q b hp h
      have hq' : (s.local_ q).echoRecv p b = true := by
        by_cases hq : q = i
        · rw [hq] ; simp [hq] at h ; exact h
        · simp [hq] at h ; exact h
      have hp' : (s.local_ p).echoed = some b := hetrace p q b hp hq'
      by_cases hpi : p = i
      · rw [hpi] ; simp ; rw [← hpi] ; exact hp'
      · simp [hpi] ; exact hp'
    · -- 3. buffer echo trace: buffer/echoed unchanged
      intro p d b hp h
      have hp' := hbet p d b hp h
      by_cases hpi : p = i
      · rw [hpi] ; simp ; rw [← hpi] ; exact hp'
      · simp [hpi] ; exact hp'
    · -- 4. vote trace: voteRecv/voted unchanged
      intro p q b hp h
      have hq' : (s.local_ p).voteRecv q (some b) = true := by
        by_cases hpi : p = i
        · rw [hpi] ; simp [hpi] at h ; exact h
        · simp [hpi] at h ; exact h
      have hv' := hvtrace p q b hp hq'
      by_cases hqi : q = i
      · rw [hqi] ; simp ; rw [← hqi] ; exact hv'
      · simp [hqi] ; exact hv'
    · -- 5. buffer vote trace: buffer/voted unchanged
      intro p d b hp h
      have hp' := hbvt p d b hp h
      by_cases hpi : p = i
      · rw [hpi] ; simp ; rw [← hpi] ; exact hp'
      · simp [hpi] ; exact hp'
    · -- 7. decision backing: decided unchanged
      intro p b h
      have h' : (s.local_ p).decided = some (some b) := by
        by_cases hpi : p = i
        · rw [hpi] ; simp [hpi] at h ; exact h
        · simp [hpi] at h ; exact h
      have hback := hvback p b h'
      by_cases hpi : p = i
      · rw [hpi] ; simp ; rw [← hpi] ; exact hback
      · simp [hpi] ; exact hback
    · -- 8. vote agreement: voted unchanged
      intro p q b₁ b₂ hp hq h1 h2
      have h1' : (s.local_ p).voted (some b₁) = true := by
        by_cases hpi : p = i
        · rw [hpi] ; simp [hpi] at h1 ; exact h1
        · simp [hpi] at h1 ; exact h1
      have h2' : (s.local_ q).voted (some b₂) = true := by
        by_cases hqi : q = i
        · rw [hqi] ; simp [hqi] at h2 ; exact h2
        · simp [hqi] at h2 ; exact h2
      exact hvagree p q b₁ b₂ hp hq h1' h2'
    · -- 9. echo backing: voted/echoRecv unchanged
      intro p b hp hvp
      have hvp' : (s.local_ p).voted (some b) = true := by
        by_cases hpi : p = i
        · rw [hpi] ; simp [hpi] at hvp ; exact hvp
        · simp [hpi] at hvp ; exact hvp
      have h' := hecho_back p b hp hvp'
      simp only [countEchoRecv] at h' ⊢
      by_cases hpi : p = i
      · rw [hpi] ; simp ; rw [← hpi] ; exact h'
      · simp [hpi] ; exact h'
    · -- 10. echo witness: voted unchanged
      intro b ⟨p, hp, hvp⟩
      have hvp' : (s.local_ p).voted (some b) = true := by
        by_cases hpi : p = i
        · rw [hpi] ; simp [hpi] at hvp ; exact hvp
        · simp [hpi] at hvp ; exact hvp
      obtain ⟨q, hq⟩ := hecho_wit b ⟨p, hp, hvp'⟩
      refine ⟨q, ?_⟩ ; simp only [countEchoRecv] at hq ⊢
      by_cases hqi : q = i
      · rw [hqi] ; simp ; rw [← hqi] ; exact hq
      · simp [hqi] ; exact hq
    · -- 11. count ↔ approved: initRecv/approved unchanged by set_input
      intro hnf p b ; constructor
      · intro happ
        have happ' : (s.local_ p).approved b = true := by
          by_cases hpi : p = i
          · rw [hpi] ; simp [hpi] at happ ; exact happ
          · simp [hpi] at happ ; exact happ
        have := (hcount_app hnf p b).mp happ'
        unfold countInitRecv at this ⊢
        by_cases hpi : p = i
        · rw [hpi] ; simp ; rw [← hpi] ; exact this
        · simp [hpi] ; exact this
      · intro hcnt
        have hcnt' : countInitRecv T n (s.local_ p) b ≥ approveThreshold n f := by
          unfold countInitRecv at hcnt ⊢
          by_cases hpi : p = i
          · rw [hpi] ; simp [hpi] at hcnt ; exact hcnt
          · simp [hpi] at hcnt ; exact hcnt
        have happ_old := (hcount_app hnf p b).mpr hcnt'
        by_cases hpi : p = i
        · rw [hpi] ; simp ; rw [← hpi] ; exact happ_old
        · simp [hpi] ; exact happ_old
    · -- 12. echoed → approved: both unchanged by set_input
      intro p b hp hech
      have hech' : (s.local_ p).echoed = some b := by
        by_cases hpi : p = i
        · rw [hpi] ; simp [hpi] at hech ; exact hech
        · simp [hpi] at hech ; exact hech
      have happ := hecho_app p b hp hech'
      by_cases hpi : p = i
      · rw [hpi] ; simp ; rw [← hpi] ; exact happ
      · simp [hpi] ; exact happ
    · -- 13. init recv trace: initRecv unchanged; input may change at i
      intro p q v hcorr hirecv
      have hirecv' : (s.local_ p).initRecv q v = true := by
        by_cases hpi : p = i
        · subst hpi ; simp at hirecv ; exact hirecv
        · simp [hpi] at hirecv ; exact hirecv
      rcases hinit_trace p q v hcorr hirecv' with hinp | hamp
      · -- input=v at q in pre-state. If q ≠ i: unchanged. If q = i: old input was none.
        by_cases hqi : q = i
        · -- q = i: old input = none (gate). But hinp says input = some v. Contradiction.
          subst hqi ; simp at hgate ; rw [hgate] at hinp ; exact absurd hinp (by simp)
        · left ; simp [hqi] ; exact hinp
      · -- amplified: countInitRecv unchanged
        right ; unfold countInitRecv at hamp ⊢
        by_cases hqi : q = i
        · subst hqi ; simpa using hamp
        · simpa [hqi] using hamp
    · -- 14. init buffer trace: buffer unchanged by set_input
      intro q p v hcorr hbuf
      rcases hinit_buf_trace q p v hcorr hbuf with hinp | hamp
      · by_cases hqi : q = i
        · subst hqi ; simp at hgate ; rw [hgate] at hinp ; exact absurd hinp (by simp)
        · left ; simp [hqi] ; exact hinp
      · right ; unfold countInitRecv at hamp ⊢
        by_cases hqi : q = i
        · subst hqi ; simpa using hamp
        · simpa [hqi] using hamp
    · -- 15. init amplification support: sent/countInitRecv unchanged; filter may grow
      intro q v hcorr hcnt hne
      have hcnt' : countInitRecv T n (s.local_ q) v ≥ amplifyThreshold f := by
        unfold countInitRecv at hcnt ⊢
        by_cases hqi : q = i
        · subst hqi ; simpa using hcnt
        · simpa [hqi] using hcnt
      have hne' : (s.local_ q).input ≠ some v := by
        by_cases hqi : q = i
        · subst hqi ; simp at hgate ; rw [hgate] ; simp
        · simp [hqi] at hne ; exact hne
      have hold := hinit_amp q v hcorr hcnt' hne'
      apply Nat.le_trans hold ; apply filter_length_mono
      intro r hr ; simp only [Bool.or_eq_true, decide_eq_true_eq] at hr ⊢
      rcases hr with hmem | hinp
      · exact Or.inl hmem
      · right ; by_cases hri : r = i
        · subst hri ; simp at hgate ; rw [hgate] at hinp ; exact absurd hinp (by simp)
        · simp [hri] ; exact hinp
    · -- 16. bot decision backing: decided/approved unchanged by set_input
      intro p h
      have h' : (s.local_ p).decided = some none := by
        by_cases hpi : p = i
        · subst hpi ; simp at h ; exact h
        · simp [hpi] at h ; exact h
      obtain ⟨v₁, v₂, hne, h1, h2⟩ := hbot_back p h'
      refine ⟨v₁, v₂, hne, ?_, ?_⟩
      · by_cases hpi : p = i
        · subst hpi ; simp ; exact h1
        · simp [hpi] ; exact h1
      · by_cases hpi : p = i
        · subst hpi ; simp ; exact h2
        · simp [hpi] ; exact h2

/-! ### Agreement -/

/-! ### Core lemmas: invariant implies agreement/validity -/

private theorem agreement_of_bca_inv (hn : n > 3 * f)
    (s : State T n) (hinv : bca_inv T n f s) : agreement T n s := by
  obtain ⟨hbudget, _, _, hvtrace, _, hvback, hvagree, _, _, _, _, _, _, _⟩ := hinv
  intro p q v w hp hq hdecp hdecq
  have hvp := hvback p v hdecp
  have hvq := hvback q w hdecq
  have hgt_p : s.corrupted.length < countVoteRecv T n (s.local_ p) (some v) :=
    calc s.corrupted.length ≤ f := hbudget
      _ < n - f := by omega
      _ ≤ _ := hvp
  obtain ⟨rp, hrp_vote, hrp_corr⟩ := pigeonhole_filter
    (s.local_ p |>.voteRecv · (some v)) s.corrupted hgt_p
  have hgt_q : s.corrupted.length < countVoteRecv T n (s.local_ q) (some w) :=
    calc s.corrupted.length ≤ f := hbudget
      _ < n - f := by omega
      _ ≤ _ := hvq
  obtain ⟨rq, hrq_vote, hrq_corr⟩ := pigeonhole_filter
    (s.local_ q |>.voteRecv · (some w)) s.corrupted hgt_q
  exact hvagree rp rq v w hrp_corr hrq_corr
    (hvtrace p rp v hrp_corr hrp_vote) (hvtrace q rq w hrq_corr hrq_vote)

private theorem validity_of_bca_inv (hn : n > 3 * f)
    (s : State T n) (hinv : bca_inv T n f s) (v : T) : validity T n v s := by
  obtain ⟨hbudget, hetrace, _, hvtrace, _, hvback, hvagree,
    hecho_back, _, hcount_app, hecho_app, hinit_trace, _, hinit_amp, hbot_back⟩ := hinv
  intro hall p
  -- Helper: under the validity antecedent, if a correct process has
  -- countInitRecv w ≥ f+1 and input ≠ w, then w = v.
  -- Proof: conjunct 15 gives |corrupted ∪ input=w| ≥ f+1. Under hall,
  -- correct processes have input ∈ {none, v}. If w ≠ v, no correct has
  -- input=w, so |corrupted ∪ input=w| = |corrupted| ≤ f < f+1. ⊥.
  have amplified_is_v : ∀ q (w : T), isCorrect T n s q →
      countInitRecv T n (s.local_ q) w ≥ amplifyThreshold f →
      w = v := by
    intro q w hcorr hamp
    by_contra hwv
    by_cases hinp : (s.local_ q).input = some w
    · -- q correct with input = w. But hall says input ∈ {none, v}. w ≠ v. ⊥.
      rcases hall q with hncorr | hnone | hv
      · exact absurd hncorr (by simp [isCorrect] ; exact hcorr)
      · rw [hnone] at hinp ; exact absurd hinp (by simp)
      · rw [hv] at hinp ; exact hwv (Option.some.inj hinp).symm
    · -- q correct with input ≠ w. conjunct 15 gives count ≥ f+1.
      have hsup := hinit_amp q w hcorr hamp hinp
      -- Under hall, |corrupted ∪ input=w| ≤ |corrupted| (no correct has input=w since w≠v).
      have : ((List.finRange n).filter (fun r =>
          decide (r ∈ s.corrupted) || decide ((s.local_ r).input = some w))).length ≤ f := by
        calc ((List.finRange n).filter (fun r =>
                decide (r ∈ s.corrupted) || decide ((s.local_ r).input = some w))).length
            ≤ ((List.finRange n).filter (fun r => decide (r ∈ s.corrupted))).length := by
              apply filter_length_mono ; intro r hr
              simp only [Bool.or_eq_true, decide_eq_true_eq] at hr
              rcases hr with hmem | hinpr
              · simp [hmem]
              · rcases hall r with hncorr | hnone | hv
                · simp [isCorrect] at hncorr ; simp [hncorr]
                · rw [hnone] at hinpr ; exact absurd hinpr (by simp)
                · exfalso ; rw [hv] at hinpr ; exact hwv (Option.some.inj hinpr).symm
          _ ≤ s.corrupted.length := filter_mem_le s.corrupted
          _ ≤ f := hbudget
      omega
  cases hdec : (s.local_ p).decided with
  | none => exact Or.inl rfl
  | some w =>
    cases w with
    | some v' =>
      -- Binary decision: backtrack to find approved v', then show v' = v.
      right
      have hvp := hvback p v' hdec
      have hgt : s.corrupted.length < countVoteRecv T n (s.local_ p) (some v') :=
        calc s.corrupted.length ≤ f := hbudget
          _ < n - f := by omega
          _ ≤ _ := hvp
      obtain ⟨r, hr_vote, hr_corr⟩ := pigeonhole_filter
        (s.local_ p |>.voteRecv · (some v')) s.corrupted hgt
      have hr_voted := hvtrace p r v' hr_corr hr_vote
      -- r is correct and voted v'. By echo backing: echo quorum for v'.
      have hr_echo := hecho_back r v' hr_corr hr_voted
      -- Among echo quorum, find correct echoer.
      have hgt2 : s.corrupted.length < countEchoRecv T n (s.local_ r) v' :=
        calc s.corrupted.length ≤ f := hbudget
          _ < n - f := by omega
          _ ≤ _ := hr_echo
      obtain ⟨e, he_echo, he_corr⟩ := pigeonhole_filter
        (s.local_ r |>.echoRecv · v') s.corrupted hgt2
      -- e is correct, echoRecv r e v' = true. By echo trace: e.echoed = some v'.
      have he_echoed := hetrace e r v' he_corr he_echo
      -- By conjunct 12: e.approved v' = true.
      have he_app := hecho_app e v' he_corr he_echoed
      -- By conjunct 11 (iff): approved v' → countInitRecv ≥ approveThreshold ≥ f+1.
      have he_cnt := (hcount_app (by omega : n > f) e v').mp he_app
      have he_amp : countInitRecv T n (s.local_ e) v' ≥ amplifyThreshold f := by
        simp only [approveThreshold, amplifyThreshold] at he_cnt ⊢ ; omega
      -- By amplified_is_v: v' = v.
      exact congrArg _ (congrArg _ (amplified_is_v e v' he_corr he_amp))
    | none =>
      -- ⊥ decision: by conjunct 16, two distinct approved values exist.
      -- By conjunct 11 (iff), each has countInitRecv ≥ approveThreshold ≥ f+1.
      -- By amplified_is_v, both must equal v. Contradicts distinctness.
      -- Helper: approved w at ANY process → w = v (under validity antecedent).
      -- approved w → countInitRecv ≥ n-f > f. By pigeonhole, ≥ 1 correct
      -- initRecv source. That source has input=w or amplified. Under hall
      -- with w ≠ v: no correct input=w. If amplified: hinit_amp gives
      -- |corrupted ∪ input=w| ≥ f+1, but under hall this ≤ f. Contradiction.
      -- So w = v. Same argument works for any p (not just correct).
      have approved_is_v : ∀ (w : T), (s.local_ p).approved w = true → w = v := by
        intro w happ
        have hcnt := (hcount_app (by omega : n > f) p w).mp happ
        -- countInitRecv p w ≥ n-f > f. Pigeonhole: correct initRecv source.
        have hgt : s.corrupted.length < countInitRecv T n (s.local_ p) w :=
          calc s.corrupted.length ≤ f := hbudget
            _ < n - f := by omega
            _ ≤ _ := hcnt
        obtain ⟨r, hr_recv, hr_corr⟩ := pigeonhole_filter
          (s.local_ p |>.initRecv · w) s.corrupted hgt
        rcases hinit_trace p r w hr_corr hr_recv with hinp | hamp
        · -- r correct with input = w. Under hall: w = v.
          rcases hall r with hncorr | hnone | hv
          · exact absurd hncorr (by simp [isCorrect] ; exact hr_corr)
          · rw [hnone] at hinp ; exact absurd hinp (by simp)
          · rw [hv] at hinp ; exact (Option.some.inj hinp).symm
        · -- r correct and amplified. Use amplified_is_v on r.
          exact amplified_is_v r w hr_corr hamp
      exfalso
      obtain ⟨v₁, v₂, hne, h1, h2⟩ := hbot_back p hdec
      exact hne ((approved_is_v v₁ h1).trans (approved_is_v v₂ h2).symm)

/-! ### Safety and safety-stutter versions

    All four properties (`agreement`, `validity` × `safety`, `safety_stutter`)
    follow from `bca_inv` via the core lemmas above. -/

/-- The inductive invariant `bca_inv` holds under `safety_stutter`. -/
theorem bca_inv_stutter (hn : n > 3 * f) :
    pred_implies (bca T n f).toSpec.safety_stutter
      [tlafml| □ ⌜ bca_inv T n f ⌝] :=
  (bca T n f).toSpec.invariant_under_safety_stutter
    (bca_inv_init T n f)
    (fun s s' hn' hi => bca_inv_step T n f hn s s' hn' hi)

theorem bca_agreement (hn : n > 3 * f) :
    pred_implies (bca T n f).safety
      [tlafml| □ ⌜ agreement T n ⌝] := by
  intro e hsafety k
  have hinv := init_invariant
    (bca_inv_init T n f)
    (fun s s' hn' hi => bca_inv_step T n f hn s s' hn' hi)
    e hsafety
  exact agreement_of_bca_inv T n f hn _ (hinv k)

theorem bca_validity (hn : n > 3 * f) (v : T) :
    pred_implies (bca T n f).safety
      [tlafml| □ ⌜ validity T n v ⌝] := by
  intro e hsafety k
  have hinv := init_invariant
    (bca_inv_init T n f)
    (fun s s' hn' hi => bca_inv_step T n f hn s s' hn' hi)
    e hsafety
  exact validity_of_bca_inv T n f hn _ (hinv k) v

theorem bca_agreement_stutter (hn : n > 3 * f) :
    pred_implies (bca T n f).toSpec.safety_stutter
      [tlafml| □ ⌜ agreement T n ⌝] := by
  intro e hsafety k
  exact agreement_of_bca_inv T n f hn _ (bca_inv_stutter T n f hn e hsafety k)

theorem bca_validity_stutter (hn : n > 3 * f) (v : T) :
    pred_implies (bca T n f).toSpec.safety_stutter
      [tlafml| □ ⌜ validity T n v ⌝] := by
  intro e hsafety k
  exact validity_of_bca_inv T n f hn _ (bca_inv_stutter T n f hn e hsafety k) v

/-! ### Binding -/

/-- Bound invariant (ghost). -/
def bound_inv (s : State T n) : Prop :=
  (∀ p (v : T), isCorrect T n s p → (s.local_ p).decided = some (some v) →
    s.boundValue = some (some v) ∨ s.boundValue = some none) ∧
  (s.boundValue = some none →
    ∀ p (v : T), isCorrect T n s p → (s.local_ p).decided ≠ some (some v)) ∧
  (∀ (v₀ : T), s.boundValue = some (some v₀) →
    ∀ p (w : T), isCorrect T n s p → w ≠ v₀ → (s.local_ p).voted (some w) = false) ∧
  (∀ (v₀ : T), s.boundValue = some (some v₀) →
    ∃ p, countEchoRecv T n (s.local_ p) v₀ ≥ echoThreshold n f) ∧
  (s.boundValue = computeBound T n f s) ∧
  (∀ p, isCorrect T n s p → ∀ v₁ v₂, (s.local_ p).voted v₁ = true →
    (s.local_ p).voted v₂ = true → v₁ = v₂) ∧
  s.corrupted.Nodup ∧
  (s.boundValue = some none →
    s.corrupted.length + correctVoteCount T n s none > 2 * f)

theorem bound_inv_init :
    ∀ s, (bca T n f).init s → bound_inv T n f s := by
  intro s ⟨hlocal, hbuf, hcorr, hbv⟩
  have hl : ∀ p, (s.local_ p).decided = none ∧
      (s.local_ p).voted = (fun _ => false) ∧ (s.local_ p).echoed = none := by
    intro p ; simp [hlocal, LocalState.init]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p v _ hdec ; rw [(hl p).1] at hdec ; exact absurd hdec (by simp)
  · intro h ; rw [hbv] at h ; exact absurd h (by simp)
  · intro v₀ h ; rw [hbv] at h ; exact absurd h (by simp)
  · intro v₀ h ; rw [hbv] at h ; exact absurd h (by simp)
  · rw [hbv] ; unfold computeBound
    have hf : ∀ v, correctVoteCount T n s v = 0 := fun v => by
      simp [correctVoteCount, hlocal, LocalState.init]
    have hfb : findBoundValue T n f s = none := by
      unfold findBoundValue ; simp [hlocal, LocalState.init]
    simp [hf, hcorr, hbv, hfb]
  · intro p _ v₁ v₂ h ; simp [(hl p).2.1] at h
  · rw [hcorr] ; exact List.nodup_nil
  · intro h ; rw [hbv] at h ; exact absurd h (by simp)

end SpecAndInvDef

theorem findBoundValue_spec (s : State T n) (v : T)
    (h : findBoundValue T n f s = some v) :
    s.corrupted.length + correctVoteCount T n s (some v) > f := by
  unfold findBoundValue at h
  -- Scan through processes to find the one that produced the value
  have : ∀ (l : List (Fin n)), l.findSome? (fun p =>
      match (s.local_ p).echoed with
      | some w => if s.corrupted.length + correctVoteCount T n s (some w) > f then some w else none
      | none => none) = some v →
    s.corrupted.length + correctVoteCount T n s (some v) > f := by
    intro l
    induction l with
    | nil => simp
    | cons p ps ih =>
      intro h
      simp only [List.findSome?_cons] at h
      by_cases hfp : ((fun p => match (s.local_ p).echoed with
          | some w => if s.corrupted.length + correctVoteCount T n s (some w) > f then some w else none
          | none => none) p).isSome
      · match hech : (s.local_ p).echoed with
        | some w =>
          simp only [hech] at h
          by_cases hcnt : s.corrupted.length + correctVoteCount T n s (some w) > f
          · rw [if_pos hcnt] at h ; exact Option.some.inj h ▸ hcnt
          · rw [if_neg hcnt] at h ; exact ih h
        | none => simp [hech] at hfp
      · simp at hfp ; rw [hfp] at h ; exact ih h
  exact this _ h

theorem computeBound_preserves_binary (s : State T n) (b₀ : T) :
    s.boundValue = some (some b₀) →
    computeBound T n f s = some (some b₀) ∨ computeBound T n f s = some none := by
  intro h ; unfold computeBound
  split
  · right ; rfl
  · simp [h]

theorem computeBound_preserves_bot (s : State T n) :
    s.boundValue = some none → computeBound T n f s = some none := by
  intro h ; unfold computeBound
  split
  · rfl
  · simp [h]

theorem computeBound_idempotent (s : State T n) :
    computeBound T n f { s with boundValue := computeBound T n f s } = computeBound T n f s := by
  -- correctVoteCount and findBoundValue don't read boundValue, so changing
  -- it doesn't affect the thresholds.
  have hcvc_eq : ∀ bv v,
      correctVoteCount T n ({ s with boundValue := bv } : State T n) v
      = correctVoteCount T n s v := fun _ _ => rfl
  have hfbv_eq : ∀ bv,
      findBoundValue T n f ({ s with boundValue := bv } : State T n)
      = findBoundValue T n f s := fun _ => rfl
  by_cases hbot : s.corrupted.length + correctVoteCount T n s none > 2 * f
  · -- Case: bot threshold crossed → computeBound s = some none
    have hX : computeBound T n f s = some none := by
      unfold computeBound ; simp [hbot]
    rw [hX] ; unfold computeBound ; simp [hcvc_eq, hbot]
  · -- Case: bot threshold NOT crossed
    cases hbv : s.boundValue with
    | some bv =>
      have hX : computeBound T n f s = some bv := by
        unfold computeBound ; simp [hbot, hbv]
      rw [hX] ; unfold computeBound ; simp [hcvc_eq, hbot]
    | none =>
      cases hfbv : findBoundValue T n f s with
      | some v =>
        have hX : computeBound T n f s = some (some v) := by
          unfold computeBound ; simp [hbot, hbv, hfbv]
        rw [hX] ; unfold computeBound ; simp [hcvc_eq, hbot]
      | none =>
        have hX : computeBound T n f s = none := by
          unfold computeBound ; simp [hbot, hbv, hfbv]
        rw [hX] ; unfold computeBound ; simp [hcvc_eq, hbot, hfbv_eq, hfbv]

-- Helper: if computeBound s = some (some v₀), then either boundValue was already
-- some (some v₀), or boundValue was none and the threshold for v₀ was crossed
-- (findBoundValue found v₀).
private theorem computeBound_eq_some_some (s : State T n) (v₀ : T)
    (h : computeBound T n f s = some (some v₀)) :
    s.boundValue = some (some v₀) ∨
    (s.boundValue = none ∧
     s.corrupted.length + correctVoteCount T n s (some v₀) > f) := by
  unfold computeBound at h
  by_cases hbot : s.corrupted.length + correctVoteCount T n s none > 2 * f
  · rw [if_pos hbot] at h ; exact absurd h (by simp)
  · rw [if_neg hbot] at h
    match hbv : s.boundValue with
    | some (some v') => rw [hbv] at h ; left ; simp at h ; rw [h]
    | some none => rw [hbv] at h ; exact absurd h (by simp)
    | none =>
      rw [hbv] at h
      right ; refine ⟨rfl, ?_⟩
      cases hfbv : findBoundValue T n f s with
      | some v =>
        rw [hfbv] at h ; simp at h ; rw [← h]
        exact findBoundValue_spec T n f s v hfbv
      | none => rw [hfbv] at h ; exact absurd h (by simp)

-- Helper: if computeBound s = some none, either old bound was some none or
-- the ⊥ threshold crossed.
private theorem computeBound_eq_some_none (s : State T n)
    (h : computeBound T n f s = some none) :
    s.boundValue = some none ∨
    s.corrupted.length + correctVoteCount T n s none > 2 * f := by
  unfold computeBound at h
  by_cases hbot : s.corrupted.length + correctVoteCount T n s none > 2 * f
  · right ; exact hbot
  · rw [if_neg hbot] at h
    match hbv : s.boundValue with
    | some (some _) => rw [hbv] at h ; exact absurd h (by simp)
    | some none => left ; rfl
    | none =>
      rw [hbv] at h
      cases hfbv : findBoundValue T n f s with
      | some v => rw [hfbv] at h ; exact absurd h (by simp)
      | none => rw [hfbv] at h ; exact absurd h (by simp)

-- Helper: if computeBound s = none, then boundValue = none and findBoundValue = none.
private theorem computeBound_eq_none (s : State T n)
    (h : computeBound T n f s = none) :
    s.boundValue = none ∧ findBoundValue T n f s = none := by
  unfold computeBound at h
  by_cases hbot : s.corrupted.length + correctVoteCount T n s none > 2 * f
  · rw [if_pos hbot] at h ; exact absurd h (by simp)
  · rw [if_neg hbot] at h
    cases hbv : s.boundValue with
    | some bv => rw [hbv] at h ; exact absurd h (by simp)
    | none =>
      rw [hbv] at h
      cases hfbv : findBoundValue T n f s with
      | some v => rw [hfbv] at h ; exact absurd h (by simp)
      | none => exact ⟨rfl, rfl⟩

-- Congruence for computeBound: if corrupted, voted, echoed, and boundValue agree,
-- then computeBound agrees.
private theorem computeBound_congr' {s s' : State T n}
    (hc : s'.corrupted = s.corrupted)
    (hv : ∀ p v, (s'.local_ p).voted v = (s.local_ p).voted v)
    (he : ∀ p, (s'.local_ p).echoed = (s.local_ p).echoed)
    (hbv : s'.boundValue = s.boundValue) :
    computeBound T n f s' = computeBound T n f s := by
  have hcvc : ∀ v, correctVoteCount T n s' v = correctVoteCount T n s v := by
    intro v ; simp only [correctVoteCount, hc]
    congr 1 ; apply List.filter_congr ; intro p _ ; simp [hv p v]
  have hfbv : findBoundValue T n f s' = findBoundValue T n f s := by
    simp only [findBoundValue, hc]
    congr 1 ; funext p ; simp [he p, hcvc]
  unfold computeBound ; simp only [hc, hcvc, hbv, hfbv]

-- Helper: if cvc(some v₀) > f and there's a correct voter, findBoundValue finds something.
-- Actually: if cvc(some v₀) > f and the echoed process exists (from echo back chain),
-- then findBoundValue ≠ none. We capture this as a contradiction tool.
private theorem findBoundValue_ne_none_of_threshold
    (hn : n > 3 * f) (s : State T n)
    (v₀ : T) (hthresh : s.corrupted.length + correctVoteCount T n s (some v₀) > f)
    (hbudget : s.corrupted.length ≤ f)
    (hetrace : ∀ p q (b : T), isCorrect T n s p →
      (s.local_ q).echoRecv p b = true → (s.local_ p).echoed = some b)
    (hecho_back : ∀ p (b : T), isCorrect T n s p →
      (s.local_ p).voted (some b) = true →
      countEchoRecv T n (s.local_ p) b ≥ echoThreshold n f) :
    findBoundValue T n f s ≠ none := by
  -- There's at least 1 correct voter for v₀
  have hcvc_pos : correctVoteCount T n s (some v₀) ≥ 1 := by omega
  obtain ⟨voter, hvoter_mem⟩ := List.exists_mem_of_length_pos (by
    unfold correctVoteCount at hcvc_pos ; omega :
    0 < ((List.finRange n).filter (fun q =>
      decide (q ∉ s.corrupted) && (s.local_ q).voted (some v₀))).length)
  rw [List.mem_filter] at hvoter_mem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hvoter_mem
  have hvoter_corr := hvoter_mem.2.1
  have hvoter_voted := hvoter_mem.2.2
  have hvoter_echo := hecho_back voter v₀ hvoter_corr hvoter_voted
  -- voter has echo quorum for v₀, so there's a correct process that echoed v₀
  have hgt : s.corrupted.length < countEchoRecv T n (s.local_ voter) v₀ := by
    unfold echoThreshold at hvoter_echo ; omega
  obtain ⟨src_e, hsrc_echo, hsrc_corr⟩ := pigeonhole_filter
    ((s.local_ voter).echoRecv · v₀) s.corrupted hgt
  have hsrc_echoed := hetrace src_e voter v₀ hsrc_corr hsrc_echo
  -- Now findBoundValue checks src_e and finds it
  intro hfbv
  unfold findBoundValue at hfbv
  rw [List.findSome?_eq_none_iff] at hfbv
  have := hfbv src_e (List.mem_finRange src_e)
  simp [hsrc_echoed, hthresh] at this

-- Pigeonhole from decision backing
private theorem correct_voters_of_decision (s : State T n) (p : Fin n) (b : T)
    (hvtrace : ∀ p q (b : T), isCorrect T n s q → (s.local_ p).voteRecv q (some b) = true →
      (s.local_ q).voted (some b) = true)
    (hcount : countVoteRecv T n (s.local_ p) (some b) ≥ n - f) :
    correctVoteCount T n s (some b) ≥ n - f - s.corrupted.length := by
  have hsub : n - f ≤ ((List.finRange n).filter (fun q =>
      decide (q ∉ s.corrupted) && (s.local_ q).voted (some b))).length +
      s.corrupted.length := by
    calc n - f ≤ countVoteRecv T n (s.local_ p) (some b) := hcount
      _ = ((List.finRange n).filter (fun q => (s.local_ p).voteRecv q (some b))).length := rfl
      _ ≤ ((List.finRange n).filter (fun q =>
            decide (q ∉ s.corrupted) && (s.local_ q).voted (some b))).length +
          ((List.finRange n).filter (fun q =>
            (s.local_ p).voteRecv q (some b) && decide (q ∈ s.corrupted))).length := by
        have hsplit := filter_split (fun q => (s.local_ p).voteRecv q (some b))
          (fun q => decide (q ∈ s.corrupted)) (List.finRange n)
        -- hsplit: |filter P| = |filter (P ∧ Q)| + |filter (P ∧ ¬Q)|
        -- where Q = corrupted. Goal: |filter P| ≤ |correct ∧ voted| + |P ∧ Q|
        -- Since |P ∧ ¬Q| ≤ |correct ∧ voted| (via hvtrace), this follows.
        have hle_not_corr : ((List.finRange n).filter (fun q =>
            (s.local_ p).voteRecv q (some b) && !decide (q ∈ s.corrupted))).length ≤
          ((List.finRange n).filter (fun q =>
            decide (q ∉ s.corrupted) && (s.local_ q).voted (some b))).length := by
          apply filter_length_mono ; intro q hq
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
            decide_eq_false_iff_not] at hq ⊢
          exact ⟨hq.2, hvtrace p q b hq.2 hq.1⟩
        omega
      _ ≤ _ := by
        apply Nat.add_le_add_left
        calc ((List.finRange n).filter (fun q =>
                (s.local_ p).voteRecv q (some b) && decide (q ∈ s.corrupted))).length
            ≤ ((List.finRange n).filter (fun q => decide (q ∈ s.corrupted))).length :=
              filter_and_le _ _ _
          _ ≤ s.corrupted.length := filter_mem_le s.corrupted
  unfold correctVoteCount ; omega

-- Vote-once disjoint: binary and ⊥ correct voters are bounded
private theorem vote_once_disjoint (s : State T n)
    (hB6 : ∀ p, isCorrect T n s p → ∀ v₁ v₂,
      (s.local_ p).voted v₁ = true → (s.local_ p).voted v₂ = true → v₁ = v₂)
    (hB7 : s.corrupted.Nodup) (hbnd : s.corrupted.length ≤ n) (b : T) :
    correctVoteCount T n s (some b) + correctVoteCount T n s none ≤ n - s.corrupted.length := by
  simp only [correctVoteCount]
  -- The voted-b and voted-none filters are disjoint subsets of "correct" processes
  let P := fun q : Fin n => decide (q ∉ s.corrupted) && (s.local_ q).voted (some b)
  let Q := fun q : Fin n => decide (q ∉ s.corrupted) && (s.local_ q).voted none
  let R := fun q : Fin n => decide (q ∉ s.corrupted)
  -- Reduce the goal
  show ((List.finRange n).filter P).length + ((List.finRange n).filter Q).length
      ≤ n - s.corrupted.length
  -- P ∨ Q → R (both are subsets of correct)
  have hor : ∀ q, P q = true ∨ Q q = true → R q = true := by
    intro q h ; simp only [P, Q, R, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h
  -- P ∧ Q is impossible (vote-once)
  have hdisj : ∀ q, P q = true → Q q = true → False := by
    intro q hp hq
    simp only [P, Q, Bool.and_eq_true, decide_eq_true_eq] at hp hq
    have := hB6 q hp.1 (some b) none hp.2 hq.2
    exact absurd this (by simp)
  -- |filter (P ∨ Q)| ≤ |filter R| and |filter (P ∨ Q)| ≥ |filter P| + |filter Q| - overlap = |filter P| + |filter Q| (disjoint)
  -- Actually we use: |filter P| + |filter Q| ≤ |filter R| via the OR subadditivity + disjointness
  have hle : ((List.finRange n).filter P).length + ((List.finRange n).filter Q).length ≤
      ((List.finRange n).filter R).length := by
    have hor_le := filter_or_le P Q (List.finRange n)
    have hmono : ((List.finRange n).filter (fun q => P q || Q q)).length ≤
        ((List.finRange n).filter R).length := by
      apply filter_length_mono ; intro q hq
      simp only [Bool.or_eq_true] at hq ; exact hor q hq
    -- Need: |filter P| + |filter Q| = |filter (P ∨ Q)| (disjoint)
    -- Actually filter_or_le gives ≤. We need =. Use filter_split on (P ∨ Q) with P.
    have hsplit := filter_split (fun q => P q || Q q) P (List.finRange n)
    -- |filter (P ∨ Q)| = |filter ((P ∨ Q) ∧ P)| + |filter ((P ∨ Q) ∧ ¬P)|
    -- |filter ((P ∨ Q) ∧ P)| = |filter P| (since P → P ∨ Q)
    have h1 : ((List.finRange n).filter (fun q => (P q || Q q) && P q)).length =
        ((List.finRange n).filter P).length := by
      congr 1 ; apply List.filter_congr ; intro q _
      cases hp : P q <;> simp
    -- |filter ((P ∨ Q) ∧ ¬P)| = |filter (Q ∧ ¬P)|, and Q ∧ ¬P = Q (by disjointness)
    have h2 : ((List.finRange n).filter (fun q => (P q || Q q) && !P q)).length =
        ((List.finRange n).filter Q).length := by
      congr 1 ; apply List.filter_congr ; intro q _
      cases hp : P q <;> cases hq : Q q <;> simp
      · exact hdisj q hp hq
    omega
  -- |filter R| + |corrupted| ≥ n, hence |filter R| ≤ n - |corrupted|
  -- Using filter_split on identity with R/¬R
  have hcorr_bound : n = ((List.finRange n).filter R).length +
      ((List.finRange n).filter (fun x => !R x)).length := by
    have hsplit2 := filter_split (fun _ : Fin n => true) R (List.finRange n)
    have : (List.finRange n).filter (fun _ : Fin n => true) = List.finRange n :=
      List.filter_eq_self.mpr (fun _ _ => rfl)
    rw [this, List.length_finRange] at hsplit2
    rw [show (List.finRange n).filter (fun x => true && R x) = (List.finRange n).filter R from
      by apply List.filter_congr ; intro x _ ; simp] at hsplit2
    rw [show (List.finRange n).filter (fun x => true && !R x) = (List.finRange n).filter (fun x => !R x) from
      by apply List.filter_congr ; intro x _ ; simp] at hsplit2
    omega
  have hneg_eq : ((List.finRange n).filter (fun x => !R x)).length = s.corrupted.length := by
    have h1 : ∀ x ∈ (List.finRange n).filter (fun x => !R x), x ∈ s.corrupted := by
      intro x hx ; rw [List.mem_filter] at hx
      by_contra habs
      have : R x = true := by simp only [R] ; exact decide_eq_true_eq.mpr habs
      simp [this] at hx
    have h2 : ∀ x ∈ s.corrupted, x ∈ (List.finRange n).filter (fun x => !R x) := by
      intro x hx ; rw [List.mem_filter]
      exact ⟨List.mem_finRange x, by simp [R, decide_eq_true_eq] ; exact hx⟩
    exact Nat.le_antisymm
      (nodup_sub_length ((finRange_nodup n).sublist List.filter_sublist) h1)
      (nodup_sub_length hB7 h2)
  omega

-- Extract a correct voter from corrupt threshold crossing
private theorem corrupt_extract_voter (s : State T n) (i : Fin n)
    (v₀ : T) (bv : Option (Val T))
    (hbudget_new : s.corrupted.length + 1 ≤ f)
    (hthresh : s.corrupted.length + 1 + correctVoteCount T n
      ({ s with corrupted := i :: s.corrupted, boundValue := bv } : State T n)
      (some v₀) > f) :
    ∃ q, isCorrect T n s q ∧ (s.local_ q).voted (some v₀) = true := by
  have hcvc_pos : correctVoteCount T n
      ({ s with corrupted := i :: s.corrupted, boundValue := bv } : State T n)
      (some v₀) ≥ 1 := by omega
  have hlen_pos : 0 < ((List.finRange n).filter (fun p =>
      decide (p ∉ (i :: s.corrupted)) && (s.local_ p).voted (some v₀))).length := by
    unfold correctVoteCount at hcvc_pos ; exact Nat.lt_of_lt_of_le (by omega) hcvc_pos
  obtain ⟨q, hq⟩ := List.exists_mem_of_length_pos hlen_pos
  rw [List.mem_filter] at hq
  have hpred := hq.2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpred
  have hni : q ∉ (i :: s.corrupted) := hpred.1
  rw [List.mem_cons] at hni
  have hcorr : q ∉ s.corrupted := fun h => hni (Or.inr h)
  exact ⟨q, hcorr, hpred.2⟩

-- The `bound_inv_step` proof and its helpers need `DecidableEq T` (via
-- `bca`'s action spec). `bound_inv_congr` and `correctVoteCount_with_bv`
-- bind `[DecidableEq T]` explicitly in their signatures for historical
-- reasons, but we still scope the section to pick it up for the rest.
/-- Helper for the echo correct-src old-echoed=none case: echoed changes at `src`,
    but everything else (voted, decided, echoRecv, corrupted) is unchanged or monotone. -/
private theorem bound_inv_of_echoed_changed (s s' : State T n)
    (hbudget : s.corrupted.length ≤ f)
    (hc : s'.corrupted = s.corrupted)
    (hv : ∀ p v, (s'.local_ p).voted v = (s.local_ p).voted v)
    (hd : ∀ p, (s'.local_ p).decided = (s.local_ p).decided)
    (he : ∀ p q b, (s.local_ p).echoRecv q b = true → (s'.local_ p).echoRecv q b = true)
    (hbv : s'.boundValue = computeBound T n f { s' with boundValue := s.boundValue })
    (hvagree : ∀ p q (v w : T), isCorrect T n s p → isCorrect T n s q →
      (s.local_ p).voted (some v) = true → (s.local_ q).voted (some w) = true → v = w)
    (hecho_back : ∀ p v, isCorrect T n s p →
      (s.local_ p).voted (some v) = true → countEchoRecv T n (s.local_ p) v ≥ echoThreshold n f)
    (hbvinv : bound_inv T n f s) : bound_inv T n f s' := by
  obtain ⟨hB1, hB2, hB3, hB4, hB5, hB6, hB7, hB8⟩ := hbvinv
  -- Let σ_pre := { s' with boundValue := s.boundValue }. It has the same
  -- voted/corrupted as s (so cvc(σ_pre) = cvc(s)) but `s.boundValue` as its
  -- bound. `hbv` says `s'.boundValue = computeBound σ_pre`.
  have hcvc : ∀ (bv : Option (Val T)) (v : Val T),
      correctVoteCount T n ({ s' with boundValue := bv } : State T n) v
      = correctVoteCount T n s v := by
    intro bv v
    simp only [correctVoteCount]
    show ((List.finRange n).filter (fun q => decide (q ∉ s'.corrupted) &&
        (s'.local_ q).voted v)).length = _
    rw [hc]
    apply congrArg
    apply List.filter_congr
    intro q _
    rw [hv q v]
  -- corrupted of σ_pre (defeq to s'.corrupted, provably = s.corrupted)
  have hpre_c : ({ s' with boundValue := s.boundValue } : State T n).corrupted = s.corrupted := hc
  -- isCorrect transfers
  have hic : ∀ p, isCorrect T n s' p ↔ isCorrect T n s p := by
    intro p ; unfold isCorrect ; rw [hc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- B1
    intro p v hcp hdec
    have hcp' : isCorrect T n s p := (hic p).mp hcp
    have hdec' : (s.local_ p).decided = some (some v) := by rw [← hd] ; exact hdec
    rcases hB1 p v hcp' hdec' with hold_b | hold_bot
    · rw [hbv]
      have hpre_bv : ({ s' with boundValue := s.boundValue } : State T n).boundValue = some (some v) := hold_b
      exact computeBound_preserves_binary T n f _ v hpre_bv
    · rw [hbv]
      have hpre_bv : ({ s' with boundValue := s.boundValue } : State T n).boundValue = some none := hold_bot
      exact Or.inr (computeBound_preserves_bot T n f _ hpre_bv)
  · -- B2
    intro hnb p v hcp hdec
    have hcp' : isCorrect T n s p := (hic p).mp hcp
    have hdec' : (s.local_ p).decided = some (some v) := by rw [← hd] ; exact hdec
    have hcomp_pre : computeBound T n f ({ s' with boundValue := s.boundValue } : State T n) = some none :=
      hbv.symm.trans hnb
    rcases computeBound_eq_some_none T n f _ hcomp_pre with h_pre_bot | h_thresh_pre
    · exact hB2 h_pre_bot p v hcp' hdec'
    · -- bot threshold crossed on σ_pre transfers to s
      have h_thresh_s : s.corrupted.length + correctVoteCount T n s none > 2 * f := by
        rw [← hcvc s.boundValue none, ← hpre_c] ; exact h_thresh_pre
      have hcomp_s : computeBound T n f s = some none := by unfold computeBound ; simp [h_thresh_s]
      exact hB2 (hB5.trans hcomp_s) p v hcp' hdec'
  · -- B3
    intro v₀ hnb p w hcp hne
    have hcp' : isCorrect T n s p := (hic p).mp hcp
    rw [hv p (some w)]
    have hcomp_pre : computeBound T n f ({ s' with boundValue := s.boundValue } : State T n) = some (some v₀) :=
      hbv.symm.trans hnb
    rcases computeBound_eq_some_some T n f _ v₀ hcomp_pre with h_pre_same | ⟨_, h_thresh_pre⟩
    · exact hB3 v₀ h_pre_same p w hcp' hne
    · -- threshold crossed on σ_pre → correct voter for v₀ exists; contradict via hvagree
      have h_thresh_s : s.corrupted.length + correctVoteCount T n s (some v₀) > f := by
        rw [← hcvc s.boundValue (some v₀), ← hpre_c] ; exact h_thresh_pre
      have hcvc_s : correctVoteCount T n s (some v₀) ≥ 1 := by omega
      have hlen_pos : 0 < ((List.finRange n).filter (fun q =>
          decide (q ∉ s.corrupted) && (s.local_ q).voted (some v₀))).length := by
        unfold correctVoteCount at hcvc_s ; omega
      obtain ⟨r, hr⟩ := List.exists_mem_of_length_pos hlen_pos
      rw [List.mem_filter] at hr
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
      by_contra hvoted_w
      have hvoted_w' : (s.local_ p).voted (some w) = true := by
        cases hh : (s.local_ p).voted (some w) with
        | true => rfl
        | false => exact absurd hh hvoted_w
      exact hne (hvagree r p v₀ w hr.2.1 hcp' hr.2.2 hvoted_w').symm
  · -- B4
    intro v₀ hnb
    have hcomp_pre : computeBound T n f ({ s' with boundValue := s.boundValue } : State T n) = some (some v₀) :=
      hbv.symm.trans hnb
    rcases computeBound_eq_some_some T n f _ v₀ hcomp_pre with h_pre_same | ⟨_, h_thresh_pre⟩
    · obtain ⟨q, hq⟩ := hB4 v₀ h_pre_same
      refine ⟨q, ?_⟩
      have hmono : countEchoRecv T n (s.local_ q) v₀ ≤ countEchoRecv T n (s'.local_ q) v₀ := by
        simp only [countEchoRecv]
        apply filter_length_mono ; intro r hr ; exact he q r v₀ hr
      omega
    · -- threshold crossed: find correct voter and lift via hecho_back + he
      have h_thresh_s : s.corrupted.length + correctVoteCount T n s (some v₀) > f := by
        rw [← hcvc s.boundValue (some v₀), ← hpre_c] ; exact h_thresh_pre
      have hcvc_s : correctVoteCount T n s (some v₀) ≥ 1 := by omega
      have hlen_pos : 0 < ((List.finRange n).filter (fun q =>
          decide (q ∉ s.corrupted) && (s.local_ q).voted (some v₀))).length := by
        unfold correctVoteCount at hcvc_s ; omega
      obtain ⟨r, hr⟩ := List.exists_mem_of_length_pos hlen_pos
      rw [List.mem_filter] at hr
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
      have hecho_r := hecho_back r v₀ hr.2.1 hr.2.2
      refine ⟨r, ?_⟩
      have hmono : countEchoRecv T n (s.local_ r) v₀ ≤ countEchoRecv T n (s'.local_ r) v₀ := by
        simp only [countEchoRecv]
        apply filter_length_mono ; intro x hx ; exact he r x v₀ hx
      omega
  · -- B5: idempotency via hbv
    rw [hbv]
    symm
    -- Goal: computeBound s' = computeBound σ_pre
    have key : s' = ({ ({ s' with boundValue := s.boundValue } : State T n) with
        boundValue := computeBound T n f ({ s' with boundValue := s.boundValue } : State T n) } :
      State T n) := by
      rw [← hbv]
    rw [key]
    exact computeBound_idempotent T n f _
  · -- B6
    intro p hcp v₁ v₂ hv1 hv2
    have hcp' : isCorrect T n s p := (hic p).mp hcp
    rw [hv p v₁] at hv1
    rw [hv p v₂] at hv2
    exact hB6 p hcp' v₁ v₂ hv1 hv2
  · -- B7
    rw [hc] ; exact hB7
  · -- B8: cvc(none) preserved
    intro hnb
    rw [show s'.corrupted = s.corrupted from hc, hcvc s'.boundValue none]
    have hcomp_pre : computeBound T n f ({ s' with boundValue := s.boundValue } : State T n) = some none :=
      hbv.symm.trans hnb
    rcases computeBound_eq_some_none T n f _ hcomp_pre with h_pre_bot | h_thresh_pre
    · exact hB8 h_pre_bot
    · rw [← hcvc s.boundValue none, ← hpre_c] ; exact h_thresh_pre

/-- Helper for vote(none) at correct src: voted changes at src only for value `none`. -/
private theorem bound_inv_of_vote_none_at_src (s s' : State T n)
    (hn : n > 3 * f) (hbudget : s.corrupted.length ≤ f)
    (src : Fin n)
    (hsrc_corr : src ∉ s.corrupted)
    (hgate_voted_only : ∀ w, (s.local_ src).voted w = true → w = none)
    (hc : s'.corrupted = s.corrupted)
    (hv_src : ∀ w, (s'.local_ src).voted w = (if w = none then true else (s.local_ src).voted w))
    (hv_other : ∀ p w, p ≠ src → (s'.local_ p).voted w = (s.local_ p).voted w)
    (hd : ∀ p, (s'.local_ p).decided = (s.local_ p).decided)
    (he : ∀ p q b, (s.local_ p).echoRecv q b = true → (s'.local_ p).echoRecv q b = true)
    (hbv : s'.boundValue = computeBound T n f { s' with boundValue := s.boundValue })
    (hetrace : ∀ p q (b : T), isCorrect T n s p →
      (s.local_ q).echoRecv p b = true → (s.local_ p).echoed = some b)
    (hvback : ∀ p (v : T),
      (s.local_ p).decided = some (some v) →
      countVoteRecv T n (s.local_ p) (some v) ≥ returnThreshold n f)
    (hvtrace : ∀ p q (b : T), isCorrect T n s q →
      (s.local_ p).voteRecv q (some b) = true → (s.local_ q).voted (some b) = true)
    (hecho_back : ∀ p v, isCorrect T n s p →
      (s.local_ p).voted (some v) = true → countEchoRecv T n (s.local_ p) v ≥ echoThreshold n f)
    (hbvinv : bound_inv T n f s) : bound_inv T n f s' := by
  obtain ⟨hB1, hB2, hB3, hB4, hB5, hB6, hB7, hB8⟩ := hbvinv
  have hpre_c : ({ s' with boundValue := s.boundValue } : State T n).corrupted = s.corrupted := hc
  have hold_not_voted : ∀ w, w ≠ none → (s.local_ src).voted w = false := by
    intro w hne
    cases h : (s.local_ src).voted w
    · rfl
    · exact absurd (hgate_voted_only w h) hne
  -- cvc(s', some v) = cvc(s, some v) for all v (src didn't vote any some)
  have hcvc_bin : ∀ (v : T),
      correctVoteCount T n ({ s' with boundValue := s.boundValue } : State T n) (some v)
      = correctVoteCount T n s (some v) := by
    intro v
    simp only [correctVoteCount]
    show ((List.finRange n).filter (fun q =>
        decide (q ∉ s'.corrupted) && (s'.local_ q).voted (some v))).length = _
    rw [hc]
    apply congrArg ; apply List.filter_congr ; intro q _
    by_cases hqsrc : q = src
    · subst hqsrc ; simp [hsrc_corr, hv_src, hold_not_voted (some v) (by simp)]
    · rw [hv_other q (some v) hqsrc]
  -- cvc(s', none) ≥ cvc(s, none) (possibly increases by 1 if src voted)
  have hcvc_none_ge : correctVoteCount T n s none
      ≤ correctVoteCount T n ({ s' with boundValue := s.boundValue } : State T n) none := by
    simp only [correctVoteCount]
    show _ ≤ ((List.finRange n).filter (fun q =>
        decide (q ∉ s'.corrupted) && (s'.local_ q).voted none)).length
    apply filter_length_mono ; intro q hq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hq ⊢
    refine ⟨hc ▸ hq.1, ?_⟩
    by_cases hqsrc : q = src
    · subst hqsrc ; rw [hv_src] ; simp
    · rw [hv_other q none hqsrc] ; exact hq.2
  have hic : ∀ p, isCorrect T n s' p ↔ isCorrect T n s p := by
    intro p ; unfold isCorrect ; rw [hc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- B1
    intro p v hcp hdec
    have hcp' : isCorrect T n s p := (hic p).mp hcp
    have hdec' : (s.local_ p).decided = some (some v) := by rw [← hd] ; exact hdec
    rcases hB1 p v hcp' hdec' with hold_b | hold_bot
    · rw [hbv] ; exact computeBound_preserves_binary T n f _ v hold_b
    · rw [hbv] ; exact Or.inr (computeBound_preserves_bot T n f _ hold_bot)
  · -- B2
    intro hnb p v hcp hdec
    have hcp' : isCorrect T n s p := (hic p).mp hcp
    have hdec' : (s.local_ p).decided = some (some v) := by rw [← hd] ; exact hdec
    have hcomp_pre : computeBound T n f ({ s' with boundValue := s.boundValue } : State T n) = some none :=
      hbv.symm.trans hnb
    rcases hB1 p v hcp' hdec' with hold_b | hold_bot
    · rcases computeBound_eq_some_none T n f _ hcomp_pre with h_pre_bot | h_thresh_pre
      · exact hB2 h_pre_bot p v hcp' hdec'
      · -- bot crossed on σ_pre; use vote_once_disjoint on σ_pre to bound cvc_pre(some v)
        exfalso
        let sInter := ({ s' with boundValue := s.boundValue } : State T n)
        -- B6 at sInter: (s'.local_ p).voted unchanged or ∈ {none, original}
        have hB6_new : ∀ p, isCorrect T n sInter p →
            ∀ v₁ v₂, (sInter.local_ p).voted v₁ = true →
              (sInter.local_ p).voted v₂ = true → v₁ = v₂ := by
          intro q hq w1 w2 hw1 hw2
          have hq' : isCorrect T n s q := by
            unfold isCorrect at hq ⊢
            rw [show sInter.corrupted = s.corrupted from hc] at hq
            exact hq
          by_cases hqsrc : q = src
          · rw [hqsrc] at hw1 hw2
            rw [show (sInter.local_ src).voted = (s'.local_ src).voted from rfl] at hw1 hw2
            rw [hv_src] at hw1 hw2
            by_cases hw1n : w1 = none
            · by_cases hw2n : w2 = none
              · rw [hw1n, hw2n]
              · rw [if_neg hw2n] at hw2
                have := hgate_voted_only w2 hw2
                rw [hw1n, this]
            · rw [if_neg hw1n] at hw1
              have hh1 := hgate_voted_only w1 hw1
              by_cases hw2n : w2 = none
              · rw [hw2n, hh1]
              · rw [if_neg hw2n] at hw2
                exact hB6 src hsrc_corr w1 w2 hw1 hw2
          · rw [show (sInter.local_ q).voted = (s'.local_ q).voted from rfl] at hw1 hw2
            rw [hv_other q w1 hqsrc] at hw1
            rw [hv_other q w2 hqsrc] at hw2
            exact hB6 q hq' w1 w2 hw1 hw2
        have hB7_new : sInter.corrupted.Nodup := by
          rw [show sInter.corrupted = s.corrupted from hc] ; exact hB7
        have hdisj := vote_once_disjoint (T := T) n sInter hB6_new hB7_new
          (by rw [show sInter.corrupted = s.corrupted from hc] ; omega) v
        rw [hcvc_bin v] at hdisj
        have hsInter_corr : sInter.corrupted = s.corrupted := hc
        rw [hsInter_corr] at hdisj
        have hthresh' : s.corrupted.length + correctVoteCount T n sInter none > 2 * f := by
          have : sInter.corrupted.length = s.corrupted.length := by rw [hsInter_corr]
          rw [← this] ; exact h_thresh_pre
        have hvtrace_p : ∀ p q (b : T), isCorrect T n s q →
            (s.local_ p).voteRecv q (some b) = true → (s.local_ q).voted (some b) = true :=
          fun p q b hq hvr => hvtrace p q b hq hvr
        have hcnt_backing := hvback p v hdec'
        have hcvc_b_ge := correct_voters_of_decision (T := T) n f s p v hvtrace_p hcnt_backing
        omega
    · exact hB2 hold_bot p v hcp' hdec'
  · -- B3
    intro v₀ hnb p w hcp hne
    have hcp' : isCorrect T n s p := (hic p).mp hcp
    have hcomp_pre : computeBound T n f ({ s' with boundValue := s.boundValue } : State T n) = some (some v₀) :=
      hbv.symm.trans hnb
    rcases computeBound_eq_some_some T n f _ v₀ hcomp_pre with h_pre_same | ⟨h_pre_none, h_thresh_pre⟩
    · -- σ_pre.bv = s.bv = some (some v₀)
      have hs_bv : s.boundValue = some (some v₀) := h_pre_same
      by_cases hpsrc : p = src
      · rw [hpsrc, hv_src]
        rw [if_neg (by simp : (some w : Val T) ≠ none)]
        exact hB3 v₀ hs_bv src w hsrc_corr hne
      · rw [hv_other p (some w) hpsrc]
        exact hB3 v₀ hs_bv p w hcp' hne
    · -- σ_pre.bv = none, threshold crossed. cvc(some v₀) unchanged. Contradiction via findBoundValue.
      exfalso
      have hs_none : s.boundValue = none := h_pre_none
      have h_cvc_v0 : correctVoteCount T n ({ s' with boundValue := s.boundValue } : State T n) (some v₀)
          = correctVoteCount T n s (some v₀) := hcvc_bin v₀
      have h_thresh_s : s.corrupted.length + correctVoteCount T n s (some v₀) > f := by
        rw [← h_cvc_v0, ← hpre_c] ; exact h_thresh_pre
      have ⟨_, hfbv_none⟩ := computeBound_eq_none T n f s (hB5.symm.trans hs_none)
      exact findBoundValue_ne_none_of_threshold T n f hn s v₀ h_thresh_s hbudget hetrace hecho_back hfbv_none
  · -- B4
    intro v₀ hnb
    have hcomp_pre : computeBound T n f ({ s' with boundValue := s.boundValue } : State T n) = some (some v₀) :=
      hbv.symm.trans hnb
    rcases computeBound_eq_some_some T n f _ v₀ hcomp_pre with h_pre_same | ⟨h_pre_none, h_thresh_pre⟩
    · obtain ⟨q, hq⟩ := hB4 v₀ h_pre_same
      refine ⟨q, ?_⟩
      have hmono : countEchoRecv T n (s.local_ q) v₀ ≤ countEchoRecv T n (s'.local_ q) v₀ := by
        simp only [countEchoRecv]
        apply filter_length_mono ; intro r hr ; exact he q r v₀ hr
      omega
    · exfalso
      have hs_none : s.boundValue = none := h_pre_none
      have h_cvc_v0 : correctVoteCount T n ({ s' with boundValue := s.boundValue } : State T n) (some v₀)
          = correctVoteCount T n s (some v₀) := hcvc_bin v₀
      have h_thresh_s : s.corrupted.length + correctVoteCount T n s (some v₀) > f := by
        rw [← h_cvc_v0, ← hpre_c] ; exact h_thresh_pre
      have ⟨_, hfbv_none⟩ := computeBound_eq_none T n f s (hB5.symm.trans hs_none)
      exact findBoundValue_ne_none_of_threshold T n f hn s v₀ h_thresh_s hbudget hetrace hecho_back hfbv_none
  · -- B5
    rw [hbv]
    symm
    have key : s' = ({ ({ s' with boundValue := s.boundValue } : State T n) with
        boundValue := computeBound T n f ({ s' with boundValue := s.boundValue } : State T n) } :
      State T n) := by
      rw [← hbv]
    rw [key]
    exact computeBound_idempotent T n f _
  · -- B6
    intro p hcp v₁ v₂ hv1 hv2
    have hcp' : isCorrect T n s p := (hic p).mp hcp
    by_cases hpsrc : p = src
    · rw [hpsrc, hv_src] at hv1
      rw [hpsrc, hv_src] at hv2
      by_cases hv1n : v₁ = none
      · by_cases hv2n : v₂ = none
        · rw [hv1n, hv2n]
        · rw [if_neg hv2n] at hv2
          have := hgate_voted_only v₂ hv2
          rw [hv1n, this]
      · rw [if_neg hv1n] at hv1
        have hv1_eq := hgate_voted_only v₁ hv1
        by_cases hv2n : v₂ = none
        · rw [hv2n, hv1_eq]
        · rw [if_neg hv2n] at hv2
          exact hB6 src hsrc_corr v₁ v₂ hv1 hv2
    · rw [hv_other p v₁ hpsrc] at hv1
      rw [hv_other p v₂ hpsrc] at hv2
      exact hB6 p hcp' v₁ v₂ hv1 hv2
  · -- B7
    rw [hc] ; exact hB7
  · -- B8: cvc(none) possibly increased. s.corrupted.length + cvc(s', none) ≥ s.corrupted.length + cvc(s, none)
    intro hnb
    rw [show s'.corrupted = s.corrupted from hc]
    have hcomp_pre : computeBound T n f ({ s' with boundValue := s.boundValue } : State T n) = some none :=
      hbv.symm.trans hnb
    rcases computeBound_eq_some_none T n f _ hcomp_pre with h_pre_bot | h_thresh_pre
    · -- σ_pre.bv = s.bv = some none. Use hB8 and cvc monotonicity.
      have hs_bot : s.boundValue = some none := h_pre_bot
      have hB8_s := hB8 hs_bot
      -- cvc(s', none) = correctVoteCount T n ({s' with bv := s'.bv} ...) = ... we need ≥ cvc(s, none)
      have : correctVoteCount T n s none ≤ correctVoteCount T n s' none := by
        have h1 := hcvc_none_ge
        have h2 : correctVoteCount T n ({ s' with boundValue := s.boundValue } : State T n) none
            = correctVoteCount T n s' none := by
          simp only [correctVoteCount]
        rw [h2] at h1 ; exact h1
      omega
    · -- threshold crossed on σ_pre
      have h_cvc_eq : correctVoteCount T n ({ s' with boundValue := s.boundValue } : State T n) none
          = correctVoteCount T n s' none := by
        simp only [correctVoteCount]
      rw [h_cvc_eq] at h_thresh_pre
      have hpre_c_eq : ({ s' with boundValue := s.boundValue } : State T n).corrupted = s'.corrupted := rfl
      rw [hpre_c_eq] at h_thresh_pre
      rw [show s'.corrupted = s.corrupted from hc] at h_thresh_pre
      exact h_thresh_pre

section BoundStep
variable [DecidableEq T]

-- bound_inv_congr: transfer bound_inv along a congruence.
private theorem bound_inv_congr {T : Type} [DecidableEq T] {n f : Nat} {s s' : State T n}
    (hc : s'.corrupted = s.corrupted)
    (hv : ∀ p v, (s'.local_ p).voted v = (s.local_ p).voted v)
    (hd : ∀ p v, (s'.local_ p).decided = v ↔ (s.local_ p).decided = v)
    (he : ∀ p q b, (s.local_ p).echoRecv q b = true → (s'.local_ p).echoRecv q b = true)
    (hech : ∀ p, (s'.local_ p).echoed = (s.local_ p).echoed)
    (hbv : s'.boundValue = s.boundValue)
    (hbvinv : bound_inv T n f s) : bound_inv T n f s' := by
  obtain ⟨hB1, hB2, hB3, hB4, hB5, hB6, hB7, hB8⟩ := hbvinv
  have hic : ∀ p, isCorrect T n s' p = isCorrect T n s p := fun p => by
    unfold isCorrect ; rw [hc]
  have hcmon : ∀ p b, countEchoRecv T n (s.local_ p) b ≤ countEchoRecv T n (s'.local_ p) b := by
    intro p b ; apply filter_length_mono ; intro q hq ; exact he p q b hq
  have hcvc_eq : ∀ v, correctVoteCount T n s' v = correctVoteCount T n s v := by
    intro v ; simp only [correctVoteCount, hc]
    apply congrArg ; apply List.filter_congr ; intro q _ ; simp [hv q v]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p b hcp hdec
    have hcp' : isCorrect T n s p := (hic p) ▸ hcp
    have hdec' : (s.local_ p).decided = some (some b) := (hd p _).mp hdec
    rw [hbv] ; exact hB1 p b hcp' hdec'
  · intro hbv' p b hcp
    rw [hbv] at hbv'
    have hcp' : isCorrect T n s p := (hic p) ▸ hcp
    have := hB2 hbv' p b hcp'
    intro hdec ; exact this ((hd p _).mp hdec)
  · intro v₀ hbv' p w hcp hne
    rw [hbv] at hbv'
    have hcp' : isCorrect T n s p := (hic p) ▸ hcp
    rw [hv p (some w)] ; exact hB3 v₀ hbv' p w hcp' hne
  · intro v₀ hbv'
    rw [hbv] at hbv'
    obtain ⟨p, hp⟩ := hB4 v₀ hbv'
    exact ⟨p, Nat.le_trans hp (hcmon p v₀)⟩
  · have hcb := computeBound_congr' (T := T) (n := n) (f := f) hc hv hech hbv
    rw [hbv, hcb, hB5]
  · intro p hcp v₁ v₂ hv1 hv2
    have hcp' : isCorrect T n s p := (hic p) ▸ hcp
    rw [hv p v₁] at hv1 ; rw [hv p v₂] at hv2
    exact hB6 p hcp' v₁ v₂ hv1 hv2
  · rw [hc] ; exact hB7
  · intro hbv' ; rw [hbv] at hbv' ; rw [hc, hcvc_eq] ; exact hB8 hbv'

-- correctVoteCount ignores boundValue
private theorem correctVoteCount_with_bv {T : Type} [DecidableEq T] {n : Nat} (s : State T n) (bv : Option (Val T)) (v : Val T) :
    correctVoteCount T n ({ s with boundValue := bv } : State T n) v = correctVoteCount T n s v := rfl

private theorem bound_inv_of_voted_unchanged (s s' : State T n)
    (hc : s'.corrupted = s.corrupted)
    (hv : ∀ p v, (s'.local_ p).voted v = (s.local_ p).voted v)
    (hd : ∀ p, (s'.local_ p).decided = (s.local_ p).decided)
    (he : ∀ p q b, (s.local_ p).echoRecv q b = true → (s'.local_ p).echoRecv q b = true)
    (hech : ∀ p, (s'.local_ p).echoed = (s.local_ p).echoed)
    (hbv : s'.boundValue = computeBound T n f { s' with boundValue := s.boundValue })
    (hbvinv : bound_inv T n f s) : bound_inv T n f s' := by
  have hcb : s'.boundValue = s.boundValue := by
    have h1 := computeBound_congr' (T := T) (n := n) (f := f)
      (s := s) (s' := { s' with boundValue := s.boundValue })
      hc hv hech rfl
    rw [hbv, h1, hbvinv.2.2.2.2.1]
  exact bound_inv_congr hc hv (fun p v => by rw [hd]) he hech hcb hbvinv

/-- Helper for vote(some b) at correct src: voted changes at src only for value `some b`. -/
private theorem bound_inv_of_vote_some_at_src (s s' : State T n)
    (hn : n > 3 * f) (hbudget : s.corrupted.length ≤ f)
    (src : Fin n) (new_b : T)
    (hsrc_corr : src ∉ s.corrupted)
    (hgate_voted_only : ∀ w, (s.local_ src).voted w = true → w = some new_b)
    (hecho_src : echoThreshold n f ≤ countEchoRecv T n (s.local_ src) new_b)
    (hc : s'.corrupted = s.corrupted)
    (hv_src : ∀ w, (s'.local_ src).voted w = (if w = some new_b then true else (s.local_ src).voted w))
    (hv_other : ∀ p w, p ≠ src → (s'.local_ p).voted w = (s.local_ p).voted w)
    (hd : ∀ p, (s'.local_ p).decided = (s.local_ p).decided)
    (he : ∀ p q b, (s.local_ p).echoRecv q b = true → (s'.local_ p).echoRecv q b = true)
    (hbv : s'.boundValue = computeBound T n f { s' with boundValue := s.boundValue })
    (hetrace : ∀ p q (b : T), isCorrect T n s p →
      (s.local_ q).echoRecv p b = true → (s.local_ p).echoed = some b)
    (hecho_back : ∀ p v, isCorrect T n s p →
      (s.local_ p).voted (some v) = true → countEchoRecv T n (s.local_ p) v ≥ echoThreshold n f)
    (hbvinv : bound_inv T n f s) : bound_inv T n f s' := by
  obtain ⟨hB1, hB2, hB3, hB4, hB5, hB6, hB7, hB8⟩ := hbvinv
  have hpre_c : ({ s' with boundValue := s.boundValue } : State T n).corrupted = s.corrupted := hc
  -- hold_not_voted: at src, any value other than some new_b was not voted before
  have hold_not_voted : ∀ w, w ≠ some new_b → (s.local_ src).voted w = false := by
    intro w hne
    cases h : (s.local_ src).voted w
    · rfl
    · exact absurd (hgate_voted_only w h) hne
  -- cvc(s', v) = cvc(s, v) for v ≠ some new_b
  have hcvc_other : ∀ (v : Val T), v ≠ some new_b →
      correctVoteCount T n ({ s' with boundValue := s.boundValue } : State T n) v
      = correctVoteCount T n s v := by
    intro v hne
    simp only [correctVoteCount]
    show ((List.finRange n).filter (fun q =>
        decide (q ∉ s'.corrupted) && (s'.local_ q).voted v)).length = _
    rw [hc]
    apply congrArg
    apply List.filter_congr
    intro q _
    by_cases hqsrc : q = src
    · subst hqsrc
      simp [hsrc_corr, hold_not_voted v hne, hv_src, hne]
    · rw [hv_other q v hqsrc]
  -- hno_opp: no correct process voted (some w) with w ≠ new_b (uses echo quorum intersection)
  have hno_opp : ∀ q, q ∉ s.corrupted → ∀ (w : T), w ≠ new_b →
      (s.local_ q).voted (some w) = false := by
    intro q hq w' hne'
    by_contra hv
    have hv' : (s.local_ q).voted (some w') = true := by
      cases h : (s.local_ q).voted (some w') with
      | true => rfl
      | false => exact absurd h hv
    have hecho_q := hecho_back q w' hq hv'
    exact absurd (bca_echo_quorum_intersection (T := T) hn s src q new_b w' hbudget hetrace hecho_src hecho_q) (Ne.symm hne')
  -- isCorrect transfers
  have hic : ∀ p, isCorrect T n s' p ↔ isCorrect T n s p := by
    intro p ; unfold isCorrect ; rw [hc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- B1: decided unchanged
    intro p v hcp hdec
    have hcp' : isCorrect T n s p := (hic p).mp hcp
    have hdec' : (s.local_ p).decided = some (some v) := by rw [← hd] ; exact hdec
    rcases hB1 p v hcp' hdec' with hold_b | hold_bot
    · rw [hbv] ; exact computeBound_preserves_binary T n f _ v hold_b
    · rw [hbv] ; exact Or.inr (computeBound_preserves_bot T n f _ hold_bot)
  · -- B2
    intro hnb p v hcp hdec
    have hcp' : isCorrect T n s p := (hic p).mp hcp
    have hdec' : (s.local_ p).decided = some (some v) := by rw [← hd] ; exact hdec
    have hcomp_pre : computeBound T n f ({ s' with boundValue := s.boundValue } : State T n) = some none :=
      hbv.symm.trans hnb
    rcases computeBound_eq_some_none T n f _ hcomp_pre with h_pre_bot | h_thresh_pre
    · exact hB2 h_pre_bot p v hcp' hdec'
    · -- threshold crossed on σ_pre → crossed on s (cvc(none) unchanged)
      have h_cvc_none : correctVoteCount T n ({ s' with boundValue := s.boundValue } : State T n) none
          = correctVoteCount T n s none := hcvc_other none (by simp)
      have h_thresh_s : s.corrupted.length + correctVoteCount T n s none > 2 * f := by
        rw [← h_cvc_none, ← hpre_c] ; exact h_thresh_pre
      have hcomp_s : computeBound T n f s = some none := by unfold computeBound ; simp [h_thresh_s]
      have hs_bv : s.boundValue = some none := hB5.trans hcomp_s
      exact hB2 hs_bv p v hcp' hdec'
  · -- B3
    intro v₀ hnb p w hcp hne
    have hcp' : isCorrect T n s p := (hic p).mp hcp
    have hcomp_pre : computeBound T n f ({ s' with boundValue := s.boundValue } : State T n) = some (some v₀) :=
      hbv.symm.trans hnb
    -- Case split: is v₀ = new_b or not?
    by_cases hvb : v₀ = new_b
    · -- v₀ = new_b: then w ≠ new_b.
      by_cases hpsrc : p = src
      · rw [hpsrc, hv_src]
        have hwne : (some w : Val T) ≠ some new_b := by
          intro h ; apply hne ; rw [hvb] ; exact Option.some.inj h
        rw [if_neg hwne]
        exact hno_opp src hsrc_corr w (fun h => hne (hvb.trans h.symm).symm)
      · rw [hv_other p (some w) hpsrc]
        exact hno_opp p hcp' w (fun h => hne (hvb.trans h.symm).symm)
    · -- v₀ ≠ new_b
      rcases computeBound_eq_some_some T n f _ v₀ hcomp_pre with h_pre_same | ⟨h_pre_none, h_thresh_pre⟩
      · have hpre_same_s : s.boundValue = some (some v₀) := h_pre_same
        by_cases hpsrc : p = src
        · rw [hpsrc, hv_src]
          by_cases hwb : w = new_b
          · -- w = new_b: some w = some new_b → if true => contradiction with hB4
            rw [if_pos (congrArg some hwb)]
            exfalso
            obtain ⟨q_wit, hq_wit⟩ := hB4 v₀ hpre_same_s
            have := bca_echo_quorum_intersection (T := T) hn s q_wit src v₀ new_b hbudget hetrace hq_wit hecho_src
            -- this: v₀ = new_b. Contradicts hvb.
            exact hvb this
          · rw [if_neg (fun h => hwb (Option.some.inj h))]
            exact hB3 v₀ hpre_same_s src w hsrc_corr hne
        · rw [hv_other p (some w) hpsrc]
          exact hB3 v₀ hpre_same_s p w hcp' hne
      · -- σ_pre.bv = none (so s.boundValue = none) but cvc(some v₀) > f via σ_pre.
        -- cvc(σ_pre, some v₀) = cvc(s, some v₀) since v₀ ≠ new_b
        exfalso
        have h_cvc_v0 : correctVoteCount T n ({ s' with boundValue := s.boundValue } : State T n) (some v₀)
            = correctVoteCount T n s (some v₀) := hcvc_other (some v₀) (fun h => hvb (Option.some.inj h))
        have h_thresh_s : s.corrupted.length + correctVoteCount T n s (some v₀) > f := by
          rw [← h_cvc_v0, ← hpre_c] ; exact h_thresh_pre
        have hs_none : s.boundValue = none := h_pre_none
        have ⟨_, hfbv_none⟩ := computeBound_eq_none T n f s (hB5.symm.trans hs_none)
        exact findBoundValue_ne_none_of_threshold T n f hn s v₀ h_thresh_s hbudget hetrace hecho_back hfbv_none
  · -- B4
    intro v₀ hnb
    have hcomp_pre : computeBound T n f ({ s' with boundValue := s.boundValue } : State T n) = some (some v₀) :=
      hbv.symm.trans hnb
    rcases computeBound_eq_some_some T n f _ v₀ hcomp_pre with h_pre_same | ⟨h_pre_none, h_thresh_pre⟩
    · obtain ⟨q, hq⟩ := hB4 v₀ h_pre_same
      refine ⟨q, ?_⟩
      have hmono : countEchoRecv T n (s.local_ q) v₀ ≤ countEchoRecv T n (s'.local_ q) v₀ := by
        simp only [countEchoRecv]
        apply filter_length_mono ; intro r hr ; exact he q r v₀ hr
      omega
    · -- Newly set. If v₀ = new_b, use src. Else contradiction.
      by_cases hvb : v₀ = new_b
      · subst hvb
        refine ⟨src, ?_⟩
        have hmono : countEchoRecv T n (s.local_ src) v₀ ≤ countEchoRecv T n (s'.local_ src) v₀ := by
          simp only [countEchoRecv]
          apply filter_length_mono ; intro r hr ; exact he src r v₀ hr
        omega
      · exfalso
        have h_cvc_v0 : correctVoteCount T n ({ s' with boundValue := s.boundValue } : State T n) (some v₀)
            = correctVoteCount T n s (some v₀) := hcvc_other (some v₀) (fun h => hvb (Option.some.inj h))
        have h_thresh_s : s.corrupted.length + correctVoteCount T n s (some v₀) > f := by
          rw [← h_cvc_v0, ← hpre_c] ; exact h_thresh_pre
        have hs_none : s.boundValue = none := h_pre_none
        have ⟨_, hfbv_none⟩ := computeBound_eq_none T n f s (hB5.symm.trans hs_none)
        exact findBoundValue_ne_none_of_threshold T n f hn s v₀ h_thresh_s hbudget hetrace hecho_back hfbv_none
  · -- B5
    rw [hbv]
    symm
    have key : s' = ({ ({ s' with boundValue := s.boundValue } : State T n) with
        boundValue := computeBound T n f ({ s' with boundValue := s.boundValue } : State T n) } :
      State T n) := by
      rw [← hbv]
    rw [key]
    exact computeBound_idempotent T n f _
  · -- B6: vote-once at post-state
    intro p hcp v₁ v₂ hv1 hv2
    have hcp' : isCorrect T n s p := (hic p).mp hcp
    by_cases hpsrc : p = src
    · rw [hpsrc, hv_src] at hv1
      rw [hpsrc, hv_src] at hv2
      by_cases hv1b : v₁ = some new_b
      · by_cases hv2b : v₂ = some new_b
        · rw [hv1b, hv2b]
        · rw [if_neg hv2b] at hv2
          have := hgate_voted_only v₂ hv2
          rw [hv1b, this]
      · rw [if_neg hv1b] at hv1
        have hv1_eq := hgate_voted_only v₁ hv1
        by_cases hv2b : v₂ = some new_b
        · rw [hv2b, hv1_eq]
        · rw [if_neg hv2b] at hv2
          exact hB6 src hsrc_corr v₁ v₂ hv1 hv2
    · rw [hv_other p v₁ hpsrc] at hv1
      rw [hv_other p v₂ hpsrc] at hv2
      exact hB6 p hcp' v₁ v₂ hv1 hv2
  · -- B7
    rw [hc] ; exact hB7
  · -- B8
    intro hnb
    rw [show s'.corrupted = s.corrupted from hc]
    have h_cvc_none : correctVoteCount T n s' none = correctVoteCount T n s none := by
      have := hcvc_other none (by simp)
      exact this
    rw [h_cvc_none]
    have hcomp_pre : computeBound T n f ({ s' with boundValue := s.boundValue } : State T n) = some none :=
      hbv.symm.trans hnb
    rcases computeBound_eq_some_none T n f _ hcomp_pre with h_pre_bot | h_thresh_pre
    · exact hB8 h_pre_bot
    · rw [← hcvc_other none (by simp), ← hpre_c] ; exact h_thresh_pre

set_option maxHeartbeats 800000 in
theorem bound_inv_step (hn : n > 3 * f) :
    ∀ s s', (∃ i, ((bca T n f).actions i).fires s s') →
    bca_inv T n f s → bound_inv T n f s → bound_inv T n f s' := by
  intro s s' ⟨action, hfire⟩ hbcainv hbvinv
  obtain ⟨hbudget, hetrace, _, hvtrace, _, hvback, hvagree, hecho_back, _, _, _, _, _, _, _⟩ := hbcainv
  cases action with
  | corrupt i =>
    simp [bca, GatedAction.fires] at hfire
    obtain ⟨hgate, htrans⟩ := hfire
    subst htrans
    obtain ⟨hB1, hB2, hB3, hB4, hB5, hB6, hB7, hB8⟩ := hbvinv
    have hi_corr : i ∉ s.corrupted := hgate.1
    have hbudget_new : s.corrupted.length + 1 ≤ f := hgate.2
    have hcorr_sub : ∀ q, q ∉ (i :: s.corrupted) → q ∉ s.corrupted :=
      fun q hq h => hq (List.mem_cons_of_mem i h)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- B1
      intro p v hcp hdec
      have hcp' : isCorrect T n s p := hcorr_sub p hcp
      rcases hB1 p v hcp' hdec with hold_b | hold_bot
      · exact computeBound_preserves_binary T n f _ v hold_b
      · right ; exact computeBound_preserves_bot T n f _ hold_bot
    · -- B2
      intro hnew_bv p v hcp hdec
      have hcp' : isCorrect T n s p := hcorr_sub p hcp
      rcases computeBound_eq_some_none T n f _ hnew_bv with hold_bot | hthresh_new
      · exact hB2 hold_bot p v hcp' hdec
      · rcases hB1 p v hcp' hdec with hold_b | hold_bot
        · have hcomp_eq : computeBound T n f s = some (some v) := hB5.symm.trans hold_b
          have hold_not_bot : s.corrupted.length + correctVoteCount T n s none ≤ 2 * f := by
            by_contra hbot
            have hbot' : s.corrupted.length + correctVoteCount T n s none > 2 * f := by omega
            have h1 : computeBound T n f s = some none := by
              unfold computeBound ; simp [hbot']
            rw [h1] at hcomp_eq ; exact absurd hcomp_eq (by simp)
          have hlen : (i :: s.corrupted).length = s.corrupted.length + 1 := by simp
          rw [hlen] at hthresh_new
          have hcvc_none_le : correctVoteCount T n
              ({ s with corrupted := i :: s.corrupted, boundValue := s.boundValue } : State T n) none
              ≤ correctVoteCount T n s none := by
            apply filter_length_mono
            intro q hq
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hq ⊢
            exact ⟨fun h => hq.1 (List.mem_cons_of_mem i h), hq.2⟩
          have hvtrace_p : ∀ p q (b : T), isCorrect T n s q →
              (s.local_ p).voteRecv q (some b) = true → (s.local_ q).voted (some b) = true :=
            fun p q b hq hvr => hvtrace p q b hq hvr
          have hcnt := hvback p v hdec
          have hcvc_b_ge : correctVoteCount T n s (some v) ≥ n - f - s.corrupted.length :=
            correct_voters_of_decision T n f s p v hvtrace_p hcnt
          have hdisj := vote_once_disjoint T n s hB6 hB7 (by omega : s.corrupted.length ≤ n) v
          -- The correctVoteCount on the new state is ≤ the old one
          have hcvc_new_le_old : correctVoteCount T n
              ({ s with corrupted := i :: s.corrupted, boundValue := s.boundValue } : State T n) none
              ≤ correctVoteCount T n s none := hcvc_none_le
          -- Rewrite hthresh_new in terms of old state
          have hthresh_norm : s.corrupted.length + 1 +
              correctVoteCount T n
                ({ s with corrupted := i :: s.corrupted, boundValue := s.boundValue } : State T n) none > 2 * f := hthresh_new
          omega
        · exact hB2 hold_bot p v hcp' hdec
    · -- B3
      intro v₀ hnew_bv p w hcp hne
      have hcp' : isCorrect T n s p := hcorr_sub p hcp
      rcases computeBound_eq_some_some T n f _ v₀ hnew_bv with hold_same | ⟨_, hthresh⟩
      · exact hB3 v₀ hold_same p w hcp' hne
      · have hlen : (i :: s.corrupted).length = s.corrupted.length + 1 := by simp
        rw [hlen] at hthresh
        obtain ⟨q, hq_corr, hq_voted⟩ :=
          corrupt_extract_voter T n f s i v₀ s.boundValue hbudget_new hthresh
        by_contra hvoted_opp
        have hvoted_opp' : (s.local_ p).voted (some w) = true := by
          cases h : (s.local_ p).voted (some w) with
          | true => rfl
          | false => exact absurd h hvoted_opp
        have hagree := hvagree q p v₀ w hq_corr hcp' hq_voted hvoted_opp'
        exact absurd hagree.symm hne
    · -- B4
      intro v₀ hnew_bv
      rcases computeBound_eq_some_some T n f _ v₀ hnew_bv with hold_same | ⟨_, hthresh⟩
      · exact hB4 v₀ hold_same
      · have hlen : (i :: s.corrupted).length = s.corrupted.length + 1 := by simp
        rw [hlen] at hthresh
        obtain ⟨q, hq_corr, hq_voted⟩ :=
          corrupt_extract_voter T n f s i v₀ s.boundValue hbudget_new hthresh
        exact ⟨q, hecho_back q v₀ hq_corr hq_voted⟩
    · -- B5
      exact (computeBound_idempotent T n f { s with corrupted := i :: s.corrupted }).symm
    · -- B6
      intro p hcp v₁ v₂ hv1 hv2
      exact hB6 p (hcorr_sub p hcp) v₁ v₂ hv1 hv2
    · -- B7
      exact List.nodup_cons.mpr ⟨hi_corr, hB7⟩
    · -- B8
      intro hnb
      have hcvc_any : ∀ (bv : Option (Val T)) (v : Val T),
          correctVoteCount T n
            ({ s with corrupted := i :: s.corrupted, boundValue := bv } : State T n) v
          = correctVoteCount T n
            ({ s with corrupted := i :: s.corrupted, boundValue := s.boundValue } : State T n) v := by
        intro _ _ ; rfl
      rw [hcvc_any]
      rcases computeBound_eq_some_none T n f _ hnb with hold_bot | hthresh_new
      · have hs_bot : s.boundValue = some none := hold_bot
        have hold := hB8 hs_bot
        have hlen : (i :: s.corrupted).length = s.corrupted.length + 1 := by simp
        have hcvc_bound : correctVoteCount T n s none ≤
            correctVoteCount T n
              ({ s with corrupted := i :: s.corrupted, boundValue := s.boundValue } : State T n)
              none + 1 := by
          unfold correctVoteCount
          have h1 : ((List.finRange n).filter (fun p =>
              decide (p ∉ s.corrupted) && (s.local_ p).voted none)).length
              ≤ (i :: ((List.finRange n).filter (fun p =>
                decide (p ∉ i :: s.corrupted) && (s.local_ p).voted none))).length := by
            apply nodup_sub_length
              ((finRange_nodup n).sublist List.filter_sublist)
            intro x hx
            simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hx
            simp only [List.mem_cons, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
            by_cases heq : x = i
            · left ; exact heq
            · right
              refine ⟨hx.1, ?_, hx.2.2⟩
              intro h
              rcases h with h1 | h1
              · exact heq h1
              · exact hx.2.1 h1
          simp only [List.length_cons] at h1
          exact h1
        show (i :: s.corrupted).length + _ > 2 * f
        rw [hlen]
        omega
      · exact hthresh_new
  | send src dst t mv =>
    simp [bca, GatedAction.fires] at hfire
    obtain ⟨hgate, htrans⟩ := hfire ; subst htrans
    -- After subst, goal is bound_inv of { s with buffer, local_, boundValue := computeBound ... }
    -- Use bound_inv_of_voted_unchanged: voted/decided/corrupted unchanged, echoed may change for echo
    cases t with
    | init =>
      refine bound_inv_of_voted_unchanged T n f s _ rfl ?_ ?_ ?_ ?_ rfl hbvinv <;>
        intro p <;> (try intro) <;> by_cases hp : p = src <;>
        simp [*]
    | echo =>
      cases mv with
      | some b =>
        by_cases hsrc_mem : src ∈ s.corrupted
        · refine bound_inv_of_voted_unchanged T n f s _ rfl ?_ ?_ ?_ ?_ rfl hbvinv <;>
            intro p <;> (try intro) <;> by_cases hp : p = src <;>
            simp [*]
        · -- Correct src: echoed at src becomes some b
          -- Case split on whether old echoed was already some b
          rcases hgate with hmem | ⟨hcorr_src, _, hecho_gate⟩
          · exact absurd hmem hsrc_mem
          · -- gate: approved b ∧ (echoed = none ∨ echoed = some b)
            rcases hecho_gate.2 with h_old_none | h_old_same
            · -- old echoed = none: new echoed changes at src
              refine bound_inv_of_echoed_changed T n f s _ hbudget rfl ?_ ?_ ?_ rfl hvagree hecho_back hbvinv
              · intro p v ; by_cases hp : p = src <;> simp [hp]
              · intro p ; by_cases hp : p = src <;> simp [hp]
              · intro p q b' hold ; by_cases hp : p = src
                · subst hp ; simp ; exact hold
                · simp [hp] ; exact hold
            · -- old echoed = some b: echoed unchanged
              refine bound_inv_of_voted_unchanged T n f s _ rfl ?_ ?_ ?_ ?_ rfl hbvinv <;>
                intro p <;> (try intro) <;> by_cases hp : p = src <;>
                simp [*]
      | none =>
        refine bound_inv_of_voted_unchanged T n f s _ rfl ?_ ?_ ?_ ?_ rfl hbvinv <;>
          intro p <;> (try intro) <;> by_cases hp : p = src <;>
          simp [*]
    | vote =>
      cases mv with
      | some b =>
        by_cases hsrc_mem : src ∈ s.corrupted
        · refine bound_inv_of_voted_unchanged T n f s _ rfl ?_ ?_ ?_ ?_ rfl hbvinv <;>
            intro p <;> (try intro) <;> by_cases hpsrc : p = src <;> simp [*]
        · rcases hgate with hmem | ⟨_, _, hvoted_only, hecho_src⟩
          · exact absurd hmem hsrc_mem
          refine bound_inv_of_vote_some_at_src T n f s _ hn hbudget src b hsrc_mem
            hvoted_only hecho_src rfl ?_ ?_ ?_ ?_ rfl hetrace hecho_back hbvinv
          · intro w ; simp [hsrc_mem]
          · intro p w hpne ; simp [hpne]
          · intro p ; by_cases hpsrc : p = src <;> simp [hpsrc]
          · intro p q b' hold ; by_cases hpsrc : p = src
            · subst hpsrc ; simp ; exact hold
            · simp [hpsrc] ; exact hold
      | none =>
        by_cases hsrc_mem : src ∈ s.corrupted
        · refine bound_inv_of_voted_unchanged T n f s _ rfl ?_ ?_ ?_ ?_ rfl hbvinv <;>
            intro p <;> (try intro) <;> by_cases hpsrc : p = src <;> simp [*]
        · rcases hgate with hmem | ⟨_, _, hvoted_only, _⟩
          · exact absurd hmem hsrc_mem
          refine bound_inv_of_vote_none_at_src T n f s _ hn hbudget src hsrc_mem
            hvoted_only rfl ?_ ?_ ?_ ?_ rfl hetrace hvback hvtrace hecho_back hbvinv
          · intro w ; simp [hsrc_mem]
          · intro p w hpne ; simp [hpne]
          · intro p ; by_cases hpsrc : p = src <;> simp [hpsrc]
          · intro p q b' hold ; by_cases hpsrc : p = src
            · subst hpsrc ; simp ; exact hold
            · simp [hpsrc] ; exact hold
  | recv src dst t mv =>
    simp [bca, GatedAction.fires] at hfire
    obtain ⟨hgate, htrans⟩ := hfire ; subst htrans
    -- All recv: voted/decided/echoed unchanged, corrupted unchanged
    cases t with
    | init =>
      cases mv with
      | some b =>
        by_cases hnew : (s.local_ dst).initRecv src b = false <;> simp [hnew] <;>
          (refine bound_inv_of_voted_unchanged T n f s _ rfl ?_ ?_ ?_ ?_ rfl hbvinv <;>
            intro p <;> (try intro) <;> by_cases hp : p = dst <;> simp [*])
      | none =>
        refine bound_inv_of_voted_unchanged T n f s _ rfl ?_ ?_ ?_ ?_ rfl hbvinv <;>
          intro p <;> (try intro) <;> by_cases hp : p = dst <;> simp [*]
    | echo =>
      cases mv with
      | some b =>
        by_cases hnew : (s.local_ dst).echoRecv src b = false
        · simp only [hnew, ite_true]
          refine bound_inv_of_voted_unchanged T n f s _ rfl ?_ ?_ ?_ ?_ rfl hbvinv
          · intro p v ; by_cases hp : p = dst <;> simp [hp]
          · intro p ; by_cases hp : p = dst <;> simp [hp]
          · intro p q b' h ; by_cases hp : p = dst
            · subst hp ; simp ; right ; exact h
            · simp [hp] ; exact h
          · intro p ; by_cases hp : p = dst <;> simp [hp]
        · simp only [hnew]
          refine bound_inv_of_voted_unchanged T n f s _ rfl ?_ ?_ ?_ ?_ rfl hbvinv <;>
            intro p <;> (try intro) <;> by_cases hp : p = dst <;> simp [*]
      | none =>
        refine bound_inv_of_voted_unchanged T n f s _ rfl ?_ ?_ ?_ ?_ rfl hbvinv <;>
          intro p <;> (try intro) <;> by_cases hp : p = dst <;> simp [*]
    | vote =>
      by_cases hnew : (s.local_ dst).voteRecv src mv = false <;> simp [hnew] <;>
        (refine bound_inv_of_voted_unchanged T n f s _ rfl ?_ ?_ ?_ ?_ rfl hbvinv <;>
          intro p <;> (try intro) <;> by_cases hp : p = dst <;> simp [*])
  | decide i mv =>
    simp [bca, GatedAction.fires] at hfire
    obtain ⟨hgate, htrans⟩ := hfire ; subst htrans
    obtain ⟨hB1, hB2, hB3, hB4, hB5, hB6, hB7, hB8⟩ := hbvinv
    -- boundValue = computeBound(new state) = computeBound(s) = s.boundValue
    -- because voted/corrupted unchanged
    have hnew_bv : (computeBound T n f
        ({ s with local_ := fun p => if p = i
          then { s.local_ i with decided := some mv } else s.local_ p } : State T n))
        = s.boundValue := by
      have := computeBound_congr' (T := T) (n := n) (f := f) (s := s)
        (s' := { s with local_ := fun p => if p = i
          then { s.local_ i with decided := some mv } else s.local_ p })
        rfl
        (fun p v => by by_cases h : p = i <;> simp [h])
        (fun p => by by_cases h : p = i <;> simp [h])
        rfl
      rw [this] ; exact hB5.symm
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- B1: correct binary decision → bound matches
      intro p v hcp hdec
      by_cases hpi : p = i
      · subst hpi ; simp at hdec
        cases mv with
        | none => exact absurd hdec (by simp)
        | some v' =>
          simp at hdec ; subst hdec
          rw [hnew_bv]
          -- Get counting facts
          have hvc_gate : countVoteRecv T n (s.local_ p) (some v') ≥ n - f := by
            have := hgate.2.2 ; unfold returnThreshold at this ; exact this
          have hcvc_ge : correctVoteCount T n s (some v') ≥ n - f - s.corrupted.length :=
            correct_voters_of_decision (T := T) (n := n) (f := f) s p v' hvtrace hvc_gate
          have hcvc_pos : correctVoteCount T n s (some v') ≥ 1 := by omega
          -- Extract a correct voter via pigeonhole
          have hcvc_pos' : 0 < ((List.finRange n).filter
              (fun q => decide (q ∉ s.corrupted) && (s.local_ q).voted (some v'))).length := by
            unfold correctVoteCount at hcvc_pos ; omega
          obtain ⟨r, hr_mem⟩ := List.exists_mem_of_length_pos hcvc_pos'
          rw [List.mem_filter] at hr_mem
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hr_mem
          have hr_corr : isCorrect T n s r := hr_mem.2.1
          have hr_voted : (s.local_ r).voted (some v') = true := hr_mem.2.2
          -- Case on s.boundValue
          cases hbv : s.boundValue with
          | some bv =>
            cases bv with
            | some b₀ =>
              -- Binary bound: must equal v' (else B3 contradicts hr_voted)
              by_cases hvb : v' = b₀
              · left ; rw [hvb]
              · exfalso
                have := hB3 b₀ hbv r v' hr_corr hvb
                rw [this] at hr_voted ; exact absurd hr_voted (by simp)
            | none => right ; rfl
          | none =>
            -- computeBound s = none (by B5). Show contradiction via findBoundValue.
            exfalso
            have hcb_none : computeBound T n f s = none := hB5.symm.trans hbv
            obtain ⟨_, hfb_none⟩ := computeBound_eq_none T n f s hcb_none
            -- correctVoteCount(some v') > f contradicts findBoundValue = none
            -- via echo witness
            have hthresh : s.corrupted.length + correctVoteCount T n s (some v') > f := by
              have : n - f - s.corrupted.length > f := by omega
              omega
            -- hecho_back: correct vote → echo quorum. Some correct echoed v'.
            have hechoq : countEchoRecv T n (s.local_ r) v' ≥ echoThreshold n f :=
              hecho_back r v' hr_corr hr_voted
            -- Pigeonhole: echo quorum of n-f > |corrupted| → correct echoer
            have hecho_gt : s.corrupted.length < countEchoRecv T n (s.local_ r) v' := by
              unfold echoThreshold at hechoq ; omega
            obtain ⟨re, hre_echo, hre_corr⟩ := pigeonhole_filter
              ((s.local_ r).echoRecv · v') s.corrupted hecho_gt
            -- echo trace: correct receives echo(v') from re → re echoed v'
            have hre_echoed : (s.local_ re).echoed = some v' :=
              hetrace re r v' hre_corr hre_echo
            -- findBoundValue scans and should find v' at re (since threshold crossed)
            have hre_in : re ∈ List.finRange n := List.mem_finRange re
            have hre_val : ((fun p => match (s.local_ p).echoed with
                | some v => if s.corrupted.length + correctVoteCount T n s (some v) > f
                    then some v else none
                | none => none) re) = some v' := by
              simp [hre_echoed, hthresh]
            -- But findBoundValue = none means all map to none
            have hfbv_re : ((fun p => match (s.local_ p).echoed with
                | some v => if s.corrupted.length + correctVoteCount T n s (some v) > f
                    then some v else none
                | none => none) re) = none := by
              unfold findBoundValue at hfb_none
              exact List.findSome?_eq_none_iff.mp hfb_none re hre_in
            rw [hre_val] at hfbv_re ; exact absurd hfbv_re (by simp)
      · simp [hpi] at hdec
        rw [hnew_bv] ; exact hB1 p v hcp hdec
    · -- B2: boundValue = some none → no correct binary decision
      intro hbv p v hcp hdec ; rw [hnew_bv] at hbv
      by_cases hpi : p = i
      · -- i decided mv. hdec says decided = some (some v), so mv = some v.
        -- Gate: countVoteRecv(some v) ≥ n-f → correctVoteCount(some v) ≥ n-f-|corrupted|.
        -- vote_once_disjoint: correctVoteCount(some v) + correctVoteCount(none) ≤ n - |corrupted|.
        -- So correctVoteCount(none) ≤ f. Then |corrupted| + correctVoteCount(none) ≤ 2f.
        -- Contradicts hB8: |corrupted| + correctVoteCount(none) > 2f.
        subst hpi ; simp at hdec
        cases hmv : mv with
        | none => rw [hmv] at hdec ; exact absurd hdec (by simp)
        | some v' =>
          rw [hmv] at hdec ; simp at hdec ; subst hdec
          have hvc_gate : countVoteRecv T n (s.local_ p) (some v') ≥ n - f := by
            have := hgate.2.2 ; rw [hmv] at this ; unfold returnThreshold at this ; exact this
          have hcvc_ge : correctVoteCount T n s (some v') ≥ n - f - s.corrupted.length :=
            correct_voters_of_decision (T := T) (n := n) (f := f) s p v' hvtrace hvc_gate
          have hdisj : correctVoteCount T n s (some v') + correctVoteCount T n s none
              ≤ n - s.corrupted.length :=
            vote_once_disjoint (T := T) (n := n) s hB6 hB7 (by omega) v'
          have hcvc_none_le : correctVoteCount T n s none ≤ f := by omega
          have hbot_thresh := hB8 hbv
          omega
      · simp [hpi] at hdec ; exact hB2 hbv p v hcp hdec
    · -- B3
      intro v₀ hbv p w hcp hne ; rw [hnew_bv] at hbv
      have hvf := hB3 v₀ hbv p w hcp hne
      by_cases hpi : p = i
      · subst hpi ; simp ; exact hvf
      · simp [hpi] ; exact hvf
    · intro v₀ hbv ; rw [hnew_bv] at hbv
      obtain ⟨p, hp⟩ := hB4 v₀ hbv
      refine ⟨p, ?_⟩
      by_cases hpi : p = i
      · subst hpi ; simp ; exact hp
      · simp [hpi] ; exact hp
    · -- B5: boundValue = computeBound. Use idempotency: computeBound(s') = computeBound(s₀) since s' = {s₀ with bv := computeBound s₀}.
      exact (computeBound_idempotent T n f _).symm
    · intro p hcp v₁ v₂ hv1 hv2
      have hv1' : (s.local_ p).voted v₁ = true := by
        by_cases hpi : p = i
        · subst hpi ; simp at hv1 ; exact hv1
        · simp [hpi] at hv1 ; exact hv1
      have hv2' : (s.local_ p).voted v₂ = true := by
        by_cases hpi : p = i
        · subst hpi ; simp at hv2 ; exact hv2
        · simp [hpi] at hv2 ; exact hv2
      exact hB6 p hcp v₁ v₂ hv1' hv2'
    · exact hB7
    · -- B8: correctVoteCount(none) unchanged since voted unchanged at every process
      intro hbv ; rw [hnew_bv] at hbv
      have := hB8 hbv
      show _ > _
      simp only [correctVoteCount] at this ⊢
      have hlist : (List.finRange n).filter
          (fun p => decide (p ∉ s.corrupted) &&
            ((fun p => if p = i then { s.local_ i with decided := some mv }
              else s.local_ p) p).voted none)
          = (List.finRange n).filter
          (fun p => decide (p ∉ s.corrupted) && (s.local_ p).voted none) := by
        apply List.filter_congr ; intro q _
        by_cases hqi : q = i <;> simp [hqi]
      rw [hlist] ; exact this
  | set_input j w =>
    simp [bca, GatedAction.fires] at hfire
    obtain ⟨hgate, htrans⟩ := hfire ; subst htrans
    -- set_input only changes `input`. voted/decided/echoed/corrupted/boundValue all unchanged.
    obtain ⟨hB1, hB2, hB3, hB4, hB5, hB6, hB7, hB8⟩ := hbvinv
    -- After subst, s'.boundValue = s.boundValue (set_input doesn't update boundValue).
    -- computeBound of s' = computeBound of s (input doesn't affect bound computation).
    have hnew_bv : (computeBound T n f
        ({ s with local_ := fun p => if p = j
          then { s.local_ j with input := some w } else s.local_ p } : State T n))
        = s.boundValue := by
      have := computeBound_congr' (T := T) (n := n) (f := f) (s := s)
        (s' := { s with local_ := fun p => if p = j
          then { s.local_ j with input := some w } else s.local_ p })
        rfl
        (fun p v => by by_cases h : p = j <;> simp [h])
        (fun p => by by_cases h : p = j <;> simp [h])
        rfl
      rw [this] ; exact hB5.symm
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- B1: boundValue unchanged (= s.boundValue)
      intro p v hcp hdec
      have hdec' : (s.local_ p).decided = some (some v) := by
        by_cases hpj : p = j <;> simp [hpj] at hdec ⊢ <;> exact hdec
      exact hB1 p v hcp hdec'
    · -- B2: boundValue unchanged
      intro hbv p v hcp hdec
      have hdec' : (s.local_ p).decided = some (some v) := by
        by_cases hpj : p = j <;> simp [hpj] at hdec ⊢ <;> exact hdec
      exact hB2 hbv p v hcp hdec'
    · -- B3: boundValue unchanged
      intro v₀ hbv p u hcp hne
      have hvf := hB3 v₀ hbv p u hcp hne
      by_cases hpj : p = j
      · subst hpj ; simp ; exact hvf
      · simp [hpj] ; exact hvf
    · -- B4: boundValue unchanged
      intro v₀ hbv
      obtain ⟨p, hp⟩ := hB4 v₀ hbv
      refine ⟨p, ?_⟩
      by_cases hpj : p = j
      · subst hpj ; simp ; exact hp
      · simp [hpj] ; exact hp
    · -- B5: s'.boundValue = s.boundValue = computeBound T n f s = computeBound T n f s'
      exact hnew_bv.symm
    · -- B6: voted unchanged
      intro p hcp v₁ v₂ hv1 hv2
      have hv1' : (s.local_ p).voted v₁ = true := by
        by_cases hpj : p = j <;> simp [hpj] at hv1 ⊢ <;> exact hv1
      have hv2' : (s.local_ p).voted v₂ = true := by
        by_cases hpj : p = j <;> simp [hpj] at hv2 ⊢ <;> exact hv2
      exact hB6 p hcp v₁ v₂ hv1' hv2'
    · exact hB7
    · -- B8: boundValue unchanged; voted unchanged
      intro hbv
      have := hB8 hbv
      show _ > _
      simp only [correctVoteCount] at this ⊢
      have hlist : (List.finRange n).filter
          (fun p => decide (p ∉ s.corrupted) &&
            ((fun p => if p = j then { s.local_ j with input := some w }
              else s.local_ p) p).voted none)
          = (List.finRange n).filter
          (fun p => decide (p ∉ s.corrupted) && (s.local_ p).voted none) := by
        apply List.filter_congr ; intro q _
        by_cases hqj : q = j <;> simp [hqj]
      rw [hlist] ; exact this

theorem bound_binary_monotone
    {T : Type} [DecidableEq T]
    (n f : Nat)
    (e : exec (State T n)) (hsafety : e |=tla= (bca T n f).safety)
    (b : T) (k₁ k₂ : Nat) (hle : k₁ ≤ k₂)
    (hbv : (e k₁).boundValue = some (some b)) :
    (e k₂).boundValue = some (some b) ∨ (e k₂).boundValue = some none := by
  obtain ⟨_, hnext⟩ := hsafety
  have step : ∀ k, (e k).boundValue = some (some b) ∨ (e k).boundValue = some none →
      (e (k+1)).boundValue = some (some b) ∨ (e (k+1)).boundValue = some none := by
    intro k hk_bv
    have hstep : (bca T n f).toSpec.next (e k) (e (k + 1)) := by
      have := hnext k ; simp [action_pred, exec.drop] at this ; rwa [Nat.add_comm] at this
    obtain ⟨action, hfire⟩ := hstep
    -- Generalize e (k+1) to a free variable to avoid dependent elimination issues.
    generalize hs_gen : e (k + 1) = s' at hfire hk_bv ⊢
    -- Case analysis on action (s' is now free, so dep-elim works).
    cases action with
    | set_input j w =>
      simp [bca, GatedAction.fires] at hfire
      obtain ⟨_, htrans⟩ := hfire ; subst htrans
      simpa using hk_bv
    | corrupt i =>
      simp [bca, GatedAction.fires] at hfire
      obtain ⟨_, htrans⟩ := hfire ; subst htrans
      rcases hk_bv with hk_bv | hk_bv
      · exact computeBound_preserves_binary T n f _ b (by simp [hk_bv])
      · right ; exact computeBound_preserves_bot T n f _ (by simp [hk_bv])
    | send src dst t mv | recv src dst t mv | decide i mv =>
      simp [bca, GatedAction.fires] at hfire
      obtain ⟨_, htrans⟩ := hfire ; subst htrans
      rcases hk_bv with hk_bv | hk_bv
      · exact computeBound_preserves_binary T n f _ b (by simp [hk_bv])
      · right ; exact computeBound_preserves_bot T n f _ (by simp [hk_bv])
  induction hle with
  | refl => exact Or.inl hbv
  | step _ ih => exact step _ ih


theorem bca_binding [Nonempty T] (hn : n > 3 * f) :
    pred_implies (bca T n f).safety (binding T n) := by
  intro e hsafety
  have hinv := init_invariant
    (fun s hi => (⟨bca_inv_init T n f s hi, bound_inv_init T n f s hi⟩ :
      bca_inv T n f s ∧ bound_inv T n f s))
    (fun s s' hnext ⟨hbca, hbv⟩ =>
      (⟨bca_inv_step T n f hn s s' hnext hbca,
        bound_inv_step T n f hn s s' hnext hbca hbv⟩ :
        bca_inv T n f s' ∧ bound_inv T n f s'))
    e hsafety
  have hinv' : ∀ k, bca_inv T n f (e k) ∧ bound_inv T n f (e k) := fun k => by
    have h : bca_inv T n f (exec.drop k e 0) ∧ bound_inv T n f (exec.drop k e 0) := hinv k
    simp only [exec.drop, Nat.zero_add] at h
    exact h
  intro hexists
  by_cases hbin : ∃ k, ∃ b : T, (e k).boundValue = some (some b)
  · obtain ⟨k₁, b₁, hbv₁⟩ := hbin
    -- There is some binary bound b₁ at step k₁.
    -- We need to find a b such that no correct process ever decides some (some v) with v ≠ b.
    -- Use b₁. For any correct decision some (some v) at step k:
    -- B1 says boundValue ∈ {some (some v), some none}.
    -- By bound_binary_monotone, the bound at k is consistent with k₁.
    -- This forces v = b₁.
    refine ⟨b₁, fun k q v hq hdec_eq => ?_⟩
    -- From B1: (e k).boundValue = some (some v) ∨ some none
    rcases (hinv' k).2.1 q v hq hdec_eq with hb_k | hb_k
    · -- (e k).boundValue = some (some v)
      -- Compare with (e k₁).boundValue = some (some b₁)
      rcases Nat.le_total k₁ k with hle | hle
      · rcases bound_binary_monotone n f e hsafety b₁ k₁ k hle hbv₁ with h | h
        · rw [h] at hb_k ; exact (Option.some.inj (Option.some.inj hb_k)).symm
        · rw [h] at hb_k ; exact absurd hb_k (by simp)
      · rcases bound_binary_monotone n f e hsafety v k k₁ hle hb_k with h | h
        · rw [h] at hbv₁ ; exact Option.some.inj (Option.some.inj hbv₁)
        · rw [h] at hbv₁ ; exact absurd hbv₁ (by simp)
    · -- (e k).boundValue = some none → B2 gives contradiction
      exact absurd hdec_eq ((hinv' k).2.2.1 hb_k q v hq)
  · -- No binary bound ever appears. Pick an arbitrary value.
    refine ⟨Classical.choice ‹Nonempty T›, fun k q v hq hdec_eq => ?_⟩
    -- B1 gives (e k).boundValue ∈ {some (some v), some none}
    rcases (hinv' k).2.1 q v hq hdec_eq with hb_k | hb_k
    · -- (e k).boundValue = some (some v) — contradicts hbin
      exact absurd ⟨k, v, hb_k⟩ hbin
    · -- (e k).boundValue = some none → B2 gives contradiction
      exact absurd hdec_eq ((hinv' k).2.2.1 hb_k q v hq)

end BoundStep

end BindingCrusaderAgreement
