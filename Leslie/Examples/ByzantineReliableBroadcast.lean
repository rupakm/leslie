import Leslie.Action

set_option linter.unnecessarySeqFocus false

/-! # Byzantine Reliable Broadcast (Bracha)

  Byzantine Reliable Broadcast for `n` processes with at most `f` Byzantine
  faults, where `n > 3f`.

  The global state is composed of:
  - A **local state** per process (receipts, echoed/voted/returned values,
    and local counters)
  - A **message buffer** (pending messages in transit)
  - A **sent** log (messages ever sent, prevents re-sending)
  - A **list of corrupted** processes

  Protocol (for a designated sender):
  1. Sender sends value `v` to all
  2. On receiving `v` from sender: send ECHO(v) to all
  3. On receiving n−f ECHO(v): send VOTE(v) to all
  4. On receiving f+1 VOTE(v): send VOTE(v) to all (vote amplification)
  5. On receiving n−f VOTE(v): return v

  Byzantine processes can inject arbitrary messages into the network.

  ## Properties (safety)
  - **Validity**: If the sender is non-faulty and a non-faulty process returns
    a value, then that value is the sender's input.
  - **Agreement**: All non-faulty processes that return a value, return the
    same value.
-/

open TLA

namespace ByzantineReliableBroadcast

/-! ### Messages -/

inductive MsgType where
  | init | echo | vote
  deriving DecidableEq

structure Message (n : Nat) (Value : Type) where
  src : Fin n
  dst : Fin n
  type : MsgType
  val : Value
  deriving DecidableEq

/-! ### Local state -/

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

/-! ### Global state -/

structure State (n : Nat) (Value : Type) where
  /-- Per-process local state. -/
  local_ : Fin n → LocalState n Value
  /-- Network buffer: pending messages in transit. -/
  buffer : Message n Value → Bool
  /-- List of corrupted (Byzantine) processes. -/
  corrupted : List (Fin n)

/-! ### Actions -/

inductive Action (n : Nat) (Value : Type) where
  | corrupt (i : Fin n)
  | send (src dst : Fin n) (t : MsgType) (v : Value)
  | recv (src dst : Fin n) (t : MsgType) (v : Value)
  | doReturn (i : Fin n) (v : Value)

/-! ### Helpers -/

variable (n f : Nat) (Value : Type) [DecidableEq Value]

def isCorrect (s : State n Value) (p : Fin n) : Prop := p ∉ s.corrupted

/-- Count of distinct sources from which ECHO(v) was received. -/
def countEchoRecv (ls : LocalState n Value) (v : Value) : Nat :=
  (List.finRange n).filter (ls.echoRecv · v) |>.length

/-- Count of distinct sources from which VOTE(v) was received. -/
def countVoteRecv (ls : LocalState n Value) (v : Value) : Nat :=
  (List.finRange n).filter (ls.voteRecv · v) |>.length

def echoThreshold : Nat := n - f
def voteThreshold : Nat := f + 1
def returnThreshold : Nat := n - f

/-- Default initial local state: everything empty/none/zero. -/
def LocalState.init : LocalState n Value where
  sent := fun _ _ _ => false
  sendRecv := none
  echoRecv := fun _ _ => false
  voteRecv := fun _ _ => false
  echoed := none
  voted := fun _ => false
  returned := none

/-! ### Specification -/

def brb (sender : Fin n) (val : Value) : ActionSpec (State n Value) (Action n Value) where
  -- Initially: all local states are empty, buffer is clear, no corruptions.
  init := fun s =>
    (∀ p, s.local_ p = LocalState.init n Value) ∧
    (∀ m, s.buffer m = false) ∧
    s.corrupted = []
  actions := fun
    --
    -- === Adversary action ===
    --
    -- The adversary corrupts a correct process, provided the total
    -- number of corruptions stays within the budget f.
    | .corrupt i => {
        gate := fun s =>
          isCorrect n Value s i ∧
          s.corrupted.length + 1 ≤ f
        transition := fun s s' => s' = { s with
          corrupted := i :: s.corrupted }
      }
    --
    -- === Send action ===
    --
    -- Process `src` sends a message of type `t` carrying value `v`
    -- to process `dst`, placing it in the network buffer.
    --
    -- Byzantine processes can send any message at any time.
    -- Correct processes must follow the protocol:
    --   SEND: only the designated sender, carrying `val`
    --   ECHO: triggered by receiving SEND(v), or having already echoed v
    --   VOTE: triggered by having received n−f ECHOs for v,
    --         or having received f+1 VOTEs for v (vote amplification),
    --         or having already voted for v
    --
    -- A correct process cannot re-send the same message to the
    -- same destination (tracked by local `sent`).
    --
    -- The sender's local state records the echo/vote decision.
    | .send src dst t mv => {
        gate := fun s =>
          -- Byzantine: unconstrained
          src ∈ s.corrupted ∨
          -- Correct: protocol rules
          (isCorrect n Value s src ∧ (s.local_ src).sent dst t mv = false ∧
            match t with
            | .init =>
              -- Only the designated sender may send SEND, carrying val.
              src = sender ∧ mv = val
            | .echo =>
              -- Echo(mv) if: already echoed mv, or first echo from SEND(mv).
              (s.local_ src).echoed = some mv
              ∨ ((s.local_ src).echoed = none ∧ (s.local_ src).sendRecv = some mv)
            | .vote =>
              -- Vote(mv) if: already voted for mv, received ≥ n−f ECHO(mv),
              -- or received ≥ f+1 VOTE(mv).
              (s.local_ src).voted mv = true ∨
              countEchoRecv n Value (s.local_ src) mv ≥ echoThreshold n f ∨
              countVoteRecv n Value (s.local_ src) mv ≥ voteThreshold f)
        transition := fun s s' =>
          let msg : Message n Value := ⟨src, dst, t, mv⟩
          s' = { s with
            -- Place message in network buffer.
            buffer := fun m => if m = msg then true else s.buffer m
            -- Update sender's local state.
            local_ := fun p => if p = src then
              { s.local_ src with
                -- Record this message as sent.
                sent := fun d t' w => if d = dst ∧ t' = t ∧ w = mv then true
                  else (s.local_ src).sent d t' w
                -- For ECHO: record the echoed value (correct processes only).
                echoed := match t with
                  | .echo => if src ∉ s.corrupted then some mv
                             else (s.local_ src).echoed
                  | _ => (s.local_ src).echoed
                -- For VOTE: mark mv as voted (correct processes only).
                voted := match t with
                  | .vote => if src ∉ s.corrupted
                    then fun w => if w = mv then true else (s.local_ src).voted w
                    else (s.local_ src).voted
                  | _ => (s.local_ src).voted }
              else s.local_ p }
      }
    --
    -- === Receive action ===
    --
    -- Process `dst` receives a pending message of type `t` carrying
    -- value `v` from `src`. The message is removed from the buffer
    -- and the receiver's local state is updated.
    --
    -- Any process can receive a message from the buffer. The message
    -- is removed from the buffer. The receiver's local state is updated
    -- only if the message is new (not already received); duplicate
    -- deliveries are ignored. SEND is only accepted from the sender.
    --
    -- Local counters are incremented only on genuinely new receipts.
    | .recv src dst t mv => {
        gate := fun s =>
          s.buffer ⟨src, dst, t, mv⟩ = true
        transition := fun s s' =>
          let msg : Message n Value := ⟨src, dst, t, mv⟩
          let ls := s.local_ dst
          s' = { s with
            -- Remove message from buffer.
            buffer := fun m => if m = msg then false else s.buffer m
            -- Update receiver's local state (ignore if already received).
            local_ := fun p => if p = dst then
              match t with
              | .init =>
                -- Accept SEND only from the designated sender and only once.
                if src = sender ∧ ls.sendRecv = none
                then { ls with sendRecv := some mv }
                else ls
              | .echo =>
                -- Accept ECHO(mv) from src only once per (source, value).
                if ls.echoRecv src mv = false
                then { ls with
                  echoRecv := fun q w => if q = src ∧ w = mv then true
                    else ls.echoRecv q w }
                else ls
              | .vote =>
                -- Accept VOTE(mv) from src only once per (source, value).
                if ls.voteRecv src mv = false
                then { ls with
                  voteRecv := fun q w => if q = src ∧ w = mv then true
                    else ls.voteRecv q w }
                else ls
              else s.local_ p }
      }
    --
    -- === Return action ===
    --
    -- Correct process `i` returns value `v` once it has received
    -- ≥ n−f VOTE(v) messages from distinct sources.
    -- A process returns at most once.
    | .doReturn i mv => {
        gate := fun s =>
          isCorrect n Value s i ∧
          (s.local_ i).returned = none ∧
          countVoteRecv n Value (s.local_ i) mv ≥ returnThreshold n f
        transition := fun s s' => s' = { s with
          local_ := fun p => if p = i
            then { s.local_ i with returned := some mv }
            else s.local_ p }
      }

/-! ### Safety properties -/

def validity (sender : Fin n) (val : Value) (s : State n Value) : Prop :=
  isCorrect n Value s sender →
  ∀ p v, isCorrect n Value s p → (s.local_ p).returned = some v → v = val

def agreement (s : State n Value) : Prop :=
  ∀ p q vp vq,
    isCorrect n Value s p → isCorrect n Value s q →
    (s.local_ p).returned = some vp → (s.local_ q).returned = some vq →
    vp = vq

/-! ### Inductive invariant

    We prove both **validity** and **agreement** from a single invariant
    `brb_inv`.
-/

/-- Local consistency: a correct process's own decisions are consistent
    with val. This covers sent messages, sendRecv, echoed, voted, returned.
    It does NOT cover echoRecv/voteRecv, which may contain values from
    Byzantine sources. -/
def local_consistent (val : Value) (ls : LocalState n Value) : Prop :=
  (∀ dst t w, ls.sent dst t w = true → w = val) ∧
  (∀ w, ls.sendRecv = some w → w = val) ∧
  (∀ w, ls.echoed = some w → w = val) ∧
  (∀ w, ls.voted w = true → w = val) ∧
  (∀ w, ls.returned = some w → w = val)

/-- Buffer consistency: all pending messages from correct processes
    carry val. -/
def buffer_consistent (val : Value) (s : State n Value) : Prop :=
  ∀ m, s.buffer m = true → isCorrect n Value s m.src → m.val = val

/-- The inductive invariant for BRB safety. Ten conjuncts:
    1. **Budget**: at most f processes corrupted
    2. **Echo trace**: echoRecv reflects echoed values of correct processes
    3. **Buffer echo trace**: pending ECHO messages reflect echoed values
    4. **Vote trace**: voteRecv reflects voted values of correct processes
    5. **Buffer vote trace**: pending VOTE messages reflect voted values
    6. **Conditional** (for validity): if sender is correct, local states
       and buffer carry `val`
    7. **Vote backing** (for agreement): correct returned processes still
       have ≥ n−f votes in the current state
    8. **Vote agreement**: all votes from correct processes agree
    9. **Echo/vote backing**: every correct vote is backed by ≥ n−f echo
       receipts or ≥ f+1 vote receipts
    10. **Echo witness**: if any correct process voted v, some process has ≥ n−f echo receipts for v -/
def brb_inv (sender : Fin n) (val : Value) (s : State n Value) : Prop :=
  -- 1. Budget
  s.corrupted.length ≤ f ∧
  -- 2. Echo trace
  (∀ p q v, isCorrect n Value s p →
    (s.local_ q).echoRecv p v = true → (s.local_ p).echoed = some v) ∧
  -- 3. Buffer echo trace
  (∀ p dst v, isCorrect n Value s p →
    s.buffer ⟨p, dst, .echo, v⟩ = true → (s.local_ p).echoed = some v) ∧
  -- 4. Vote trace
  (∀ p q w, isCorrect n Value s q →
    (s.local_ p).voteRecv q w = true → (s.local_ q).voted w = true) ∧
  -- 5. Buffer vote trace
  (∀ p dst v, isCorrect n Value s p →
    s.buffer ⟨p, dst, .vote, v⟩ = true → (s.local_ p).voted v = true) ∧
  -- 6. Conditional (validity)
  (isCorrect n Value s sender →
    (∀ p, isCorrect n Value s p → local_consistent n Value val (s.local_ p)) ∧
    buffer_consistent n Value val s) ∧
  -- 7. Vote backing (agreement): no isCorrect needed since only correct processes can return
  (∀ p v, (s.local_ p).returned = some v →
    countVoteRecv n Value (s.local_ p) v ≥ returnThreshold n f) ∧
  -- 8. Vote agreement: all votes from correct processes are for the same value
  (∀ p q vp vq, isCorrect n Value s p → isCorrect n Value s q →
    (s.local_ p).voted vp = true → (s.local_ q).voted vq = true → vp = vq) ∧
  -- 9. Echo/vote backing: every correct vote is backed by a quorum
  (∀ p v, isCorrect n Value s p →
    (s.local_ p).voted v = true →
    countEchoRecv n Value (s.local_ p) v ≥ echoThreshold n f ∨
    countVoteRecv n Value (s.local_ p) v ≥ voteThreshold f) ∧
  -- 10. Echo witness: if any correct process voted v, some process has ≥ n−f echo receipts
  (∀ v, (∃ p, isCorrect n Value s p ∧ (s.local_ p).voted v = true) →
    ∃ q, countEchoRecv n Value (s.local_ q) v ≥ echoThreshold n f)

-- All conjuncts vacuously true: sent/voted/echoRecv/voteRecv all false, buffer empty.
theorem brb_inv_init (sender : Fin n) (val : Value) :
    ∀ s, (brb n f Value sender val).init s → brb_inv n f Value sender val s := by
  intro s ⟨hlocal, hbuf, hcorr⟩
  refine ⟨by simp [hcorr], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p q v _ h ; simp [hlocal, LocalState.init] at h
  · intro p dst v _ h ; simp [hbuf] at h
  · intro p q w _ h ; simp [hlocal, LocalState.init] at h
  · intro p dst v _ h ; simp [hbuf] at h
  · intro _ ; exact ⟨fun p _ => by simp [hlocal, LocalState.init, local_consistent],
      fun m hm _ => by simp [hbuf] at hm⟩
  · intro p v h ; simp [hlocal, LocalState.init] at h
  · intro p q vp vq _ _ hvp _ ; simp [hlocal, LocalState.init] at hvp
  · intro p v _ hvp ; simp [hlocal, LocalState.init] at hvp
  · intro v ⟨p, _, hvp⟩ ; simp [hlocal, LocalState.init] at hvp

/-! ### Helper lemmas -/

/-- A nodup sublist has bounded length. If every element of `l` appears
    in `m` and `l` has no duplicates, then `l.length ≤ m.length`.
    Used in `pigeonhole_filter` and `brb_agreement` to bound the number
    of corrupted processes appearing in `finRange n`. -/
theorem nodup_sub_length {α : Type} [DecidableEq α]
    {l m : List α} (hnd : l.Nodup) (hsub : ∀ x ∈ l, x ∈ m) :
    l.length ≤ m.length := by
  induction l generalizing m with
  | nil => simp
  | cons a t ih =>
    have ⟨hat, hnd_t⟩ := List.nodup_cons.mp hnd
    have ha := hsub a (List.mem_cons.mpr (.inl rfl))
    have h1 := ih hnd_t fun x hx =>
      (List.mem_erase_of_ne (show x ≠ a from fun h => hat (h ▸ hx))).mpr
        (hsub x (List.mem_cons.mpr (.inr hx)))
    have h2 := List.length_erase_of_mem ha
    have : m.length ≥ 1 := by cases m with | nil => simp at ha | cons => simp
    simp [List.length_cons] ; omega


/-- `List.finRange n` has no duplicates.
    Basis for all counting arguments over process indices. -/
theorem finRange_nodup : ∀ n, (List.finRange n).Nodup := by
  intro n ; induction n with
  | zero => simp [List.finRange]
  | succ n ih =>
    rw [List.finRange_succ, List.nodup_cons]
    exact ⟨by simp [List.mem_map] ; exact fun _ => Fin.succ_ne_zero _,
      ih.map Fin.succ fun a b hab heq =>
        hab (by simp [Fin.ext_iff, Fin.val_succ] at heq ; exact Fin.ext heq)⟩

/-- Monotonicity: if P implies Q pointwise then |filter P| ≤ |filter Q|.
    Used in `recv.vote` to show `countVoteRecv` is monotone
    when `voteRecv` gains a new entry. -/
theorem filter_length_mono {α : Type} (P Q : α → Bool) (l : List α)
    (h : ∀ x, P x = true → Q x = true) :
    (l.filter P).length ≤ (l.filter Q).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.filter_cons]
    cases hpa : P a <;> cases hqa : Q a <;> simp_all <;> omega

/-- |filter (P ∧ Q)| ≤ |filter Q|: a conjunctive filter is bounded
    by either conjunct alone.
    Follows from `List.filter_filter` and `List.filter_sublist`. -/
theorem filter_and_le {α : Type} (P Q : α → Bool) (l : List α) :
    (l.filter (fun x => P x && Q x)).length ≤ (l.filter Q).length := by
  rw [← List.filter_filter] ; exact List.filter_sublist.length_le

/-- |filter P| = |filter (P ∧ Q)| + |filter (P ∧ ¬Q)|: decompose
    a filter into two disjoint parts.
    Core lemma for the quorum intersection arguments in both
    validity (echo counting) and agreement (vote counting). -/
theorem filter_split {α : Type} [DecidableEq α] (P Q : α → Bool) (l : List α) :
    (l.filter P).length =
    (l.filter (fun x => P x && Q x)).length +
    (l.filter (fun x => P x && !Q x)).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.filter_cons]
    cases P a <;> cases Q a <;> simp <;> omega

/-- Pigeonhole: if |{r | P r}| > |corrupted|, some r satisfies P
    and is not corrupted. Uses `filter_split` + `filter_and_le` to
    decompose the filter and extract a correct witness via
    `List.exists_mem_of_length_pos`. -/
theorem pigeonhole_filter (P : Fin n → Bool) (corrupted : List (Fin n))
    (hgt : corrupted.length < ((List.finRange n).filter P).length) :
    ∃ q, P q = true ∧ q ∉ corrupted := by
  let Q : Fin n → Bool := fun x => decide (x ∈ corrupted)
  have hsplit := filter_split P Q (List.finRange n)
  have hle : ((List.finRange n).filter (fun x => P x && Q x)).length ≤
      corrupted.length := by
    calc ((List.finRange n).filter (fun x => P x && Q x)).length
        ≤ ((List.finRange n).filter Q).length := filter_and_le P Q _
      _ ≤ corrupted.length := by
          apply nodup_sub_length ((finRange_nodup n).sublist List.filter_sublist)
          intro x hx ; simp [Q, List.mem_filter] at hx ; exact hx
  obtain ⟨q, hq⟩ := List.exists_mem_of_length_pos (by omega :
    0 < ((List.finRange n).filter (fun x => P x && !Q x)).length)
  have ⟨_, hq2⟩ := List.mem_filter.mp hq
  simp only [Q, Bool.and_eq_true, Bool.not_eq_true'] at hq2
  exact ⟨q, hq2.1, fun h => by simp [h] at hq2⟩


/-! ### Invariant preservation

    We prove `brb_inv_step` by case analysis on the action. For each action,
    seven conjuncts must be preserved. Two helper lemmas factor out the
    pigeonhole counting arguments that appear in multiple action cases.

    For each action, the seven conjuncts are:
    1. budget  2. echo trace  3. buffer echo trace
    4. vote trace  5. buffer vote trace
    6. conditional (validity)  7. vote backing (agreement)
-/

/-- Pigeonhole on echo quorum: if |echoRecv(v)| > |corrupted|, then some
    correct process echoed v, and local_consistent gives v = val. -/
-- Pigeonhole on echo count gives a correct echo source. Echo trace gives echoed = some v. local_consistent gives v = val.
private theorem echo_quorum_val {n : Nat} {Value : Type} [DecidableEq Value]
    (s : State n Value) (p : Fin n) (v : Value) {val : Value}
    (hetrace : ∀ p q v, isCorrect n Value s p →
      (s.local_ q).echoRecv p v = true → (s.local_ p).echoed = some v)
    (hloc : ∀ q, isCorrect n Value s q → local_consistent n Value val (s.local_ q))
    (hgt : s.corrupted.length < countEchoRecv n Value (s.local_ p) v) :
    v = val := by
  obtain ⟨q, hqecho, hqcorr⟩ := pigeonhole_filter n
    ((s.local_ p).echoRecv · v) s.corrupted hgt
  have := hetrace q p v hqcorr hqecho
  exact (hloc q hqcorr).2.2.1 v this

-- Same argument via vote trace: pigeonhole gives correct voter, local_consistent gives v = val.
private theorem vote_quorum_val {n : Nat} {Value : Type} [DecidableEq Value]
    (s : State n Value) (p : Fin n) (v : Value) {val : Value}
    (hvtrace : ∀ p q w, isCorrect n Value s q →
      (s.local_ p).voteRecv q w = true → (s.local_ q).voted w = true)
    (hloc : ∀ q, isCorrect n Value s q → local_consistent n Value val (s.local_ q))
    (hgt : s.corrupted.length < countVoteRecv n Value (s.local_ p) v) :
    v = val := by
  obtain ⟨q, hqvote, hqcorr⟩ := pigeonhole_filter n
    ((s.local_ p).voteRecv · v) s.corrupted hgt
  exact (hloc q hqcorr).2.2.2.1 v (hvtrace p q v hqcorr hqvote)

-- Proof: by contradiction. Two echo quorums of size n-f give n-f-c correct echoes each.
-- Since echoed : Option (at most one value per process), the disjoint sets sum to 2(n-f-c),
-- but three-way bound with corrupted gives n ≤ 2f+c ≤ 3f, contradicting n > 3f.
/-- Echo quorum intersection: two values can't both have ≥ n−f echo
    sources when n > 3f and each correct process echoes at most one value.
    If p1 received n−f echos for v and p2 received n−f echos for w, then v = w. -/
private theorem echo_quorum_intersection {n : Nat} {Value : Type} [DecidableEq Value]
    {f : Nat} (hn : n > 3 * f)
    (s : State n Value) (p1 p2 : Fin n) (v w : Value)
    (hbudget : s.corrupted.length ≤ f)
    (hetrace : ∀ p q v, isCorrect n Value s p →
      (s.local_ q).echoRecv p v = true → (s.local_ p).echoed = some v)
    (hv : countEchoRecv n Value (s.local_ p1) v ≥ echoThreshold n f)
    (hw : countEchoRecv n Value (s.local_ p2) w ≥ echoThreshold n f) :
    v = w := by
  by_contra hvw
  simp only [echoThreshold] at hv hw
  -- Step 1: From n-f echo sources for v at p1, extract ≥ n-f-c correct with echoed = some v.
  -- echoRecv sources split into correct + corrupted. Correct ones have echoed = some v (hetrace).
  -- count(echoRecv · v, correct) ≥ countEchoRecv - corrupted ≥ n-f-c
  -- Each correct echoRecv source r has echoed r = some v (by hetrace).
  -- So: count(echoed = some v, correct) ≥ count(echoRecv · v, correct) ≥ n-f-c.
  -- Helper: correct echoRecv sources for val at proc have echoed = some val
  have echo_mono := fun (proc : Fin n) (val : Value) =>
    filter_length_mono
      (fun r => (s.local_ proc).echoRecv r val && !decide (r ∈ s.corrupted))
      (fun r => decide (r ∉ s.corrupted) && decide ((s.local_ r).echoed = some val))
      (List.finRange n)
      (fun r hr => by
        rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hr
        rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
        exact ⟨hr.2, hetrace r proc val hr.2 hr.1⟩)
  -- cc = distinct corrupted count (≤ corrupted.length ≤ f)
  let cc := ((List.finRange n).filter (fun r => decide (r ∈ s.corrupted))).length
  have hcc_le : cc ≤ f :=
    Nat.le_trans
      (nodup_sub_length ((finRange_nodup n).sublist List.filter_sublist)
        (fun x hx => by simp [List.mem_filter] at hx ; exact hx))
      hbudget
  -- hcount_v: correct echoed v ≥ n - f - cc (using cc, not corrupted.length)
  have hcount_v : ((List.finRange n).filter (fun r =>
      decide (r ∉ s.corrupted) && decide ((s.local_ r).echoed = some v))).length
      ≥ n - f - cc := by
    apply Nat.le_trans _ (echo_mono p1 v)
    -- correct echoRecv sources ≥ total echoRecv - corrupted echoRecv ≥ (n-f) - cc
    have hsplit := filter_split ((s.local_ p1).echoRecv · v)
      (fun r => decide (r ∈ s.corrupted)) (List.finRange n)
    have hle := filter_and_le ((s.local_ p1).echoRecv · v)
      (fun r => decide (r ∈ s.corrupted)) (List.finRange n)
    simp only [countEchoRecv] at hv ; omega
  have hcount_w : ((List.finRange n).filter (fun r =>
      decide (r ∉ s.corrupted) && decide ((s.local_ r).echoed = some w))).length
      ≥ n - f - cc := by
    apply Nat.le_trans _ (echo_mono p2 w)
    have hsplit := filter_split ((s.local_ p2).echoRecv · w)
      (fun r => decide (r ∈ s.corrupted)) (List.finRange n)
    have hle := filter_and_le ((s.local_ p2).echoRecv · w)
      (fun r => decide (r ∈ s.corrupted)) (List.finRange n)
    simp only [countEchoRecv] at hw ; omega
  -- Step 3: Three-way bound. correct-echoed-v + correct-echoed-w + corrupted ≤ n.
  -- Disjoint because echoed : Option (at most one value per process).
  have h3 : ∀ (l : List (Fin n)),
      (l.filter (fun r => decide (r ∉ s.corrupted) && decide ((s.local_ r).echoed = some v))).length +
      (l.filter (fun r => decide (r ∉ s.corrupted) && decide ((s.local_ r).echoed = some w))).length +
      (l.filter (fun r => decide (r ∈ s.corrupted))).length
      ≤ l.length := by
    intro l ; induction l with
    | nil => simp
    | cons a t ih =>
      simp only [List.filter_cons, List.length_cons]
      split <;> split <;> split <;> simp_all
      all_goals first
        | omega
  have h3way := h3 (List.finRange n)
  have hlen : (List.finRange n).length = n := List.length_finRange
  -- Convert Nat subtraction to addition: count ≥ n - f - c means count + f + c ≥ n
  -- (since n > 3f ≥ f + c, no underflow).
  -- Convert ≥ with Nat subtraction to addition form for omega
  have hcv_add : n ≤ ((List.finRange n).filter (fun r =>
    decide (r ∉ s.corrupted) && decide ((s.local_ r).echoed = some v))).length
    + f + s.corrupted.length := by omega
  have hcw_add : n ≤ ((List.finRange n).filter (fun r =>
    decide (r ∉ s.corrupted) && decide ((s.local_ r).echoed = some w))).length
    + f + s.corrupted.length := by omega
  -- h3way: cv + cw + cc ≤ n. hcorr_le: cc ≤ c ≤ f.
  -- cv + f + c ≥ n and cw + f + c ≥ n and cv + cw + cc ≤ n and cc ≤ f and c ≤ f
  -- → cv ≥ n - f - c, cw ≥ n - f - c → cv + cw ≥ 2(n-f-c) = 2n-2f-2c
  -- → 2n-2f-2c + cc ≤ n → n ≤ 2f + 2c - cc ≤ 2f + c ≤ 3f. Contradiction.
  omega

set_option maxHeartbeats 400000 in
theorem brb_inv_step (sender : Fin n) (val : Value) (hn : n > 3 * f) :
    ∀ s s', (∃ i, ((brb n f Value sender val).actions i).fires s s') →
    brb_inv n f Value sender val s → brb_inv n f Value sender val s' := by
  intro s s' ⟨action, hfire⟩ ⟨hbudget, hetrace, hbet, hvtrace, hbvt, hcond, hvotes, hvagree, hecho_back, hecho_wit⟩
  simp [brb, GatedAction.fires] at hfire
  obtain ⟨hgate, htrans⟩ := hfire
  cases action with
  -- ── corrupt: isCorrect weakens; all fields unchanged ──
  | corrupt i =>
    subst htrans
    -- Corruption only adds to corrupted list; all local state and buffer unchanged.
    -- Every conjunct is preserved by weakening isCorrect through hcw.
    have hcw : ∀ q, isCorrect n Value
        { s with corrupted := i :: s.corrupted } q → isCorrect n Value s q :=
      fun q hq h => hq (List.mem_cons_of_mem i h)
    exact ⟨by simp [List.length_cons] ; exact hgate.2,  -- budget: gate bounds length
      fun p q v hp h => hetrace p q v (hcw p hp) h,     -- all other conjuncts:
      fun p d v hp h => hbet p d v (hcw p hp) h,         -- fields unchanged,
      fun p q w hp h => hvtrace p q w (hcw q hp) h,      -- only isCorrect weakens
      fun p d v hp h => hbvt p d v (hcw p hp) h,         -- via hcw
      fun hs' => let ⟨hl, hb⟩ := hcond (hcw sender hs') ;
        ⟨fun p hp => hl p (hcw p hp), fun m hm hsrc => hb m hm (hcw m.src hsrc)⟩,
      fun p v hret => hvotes p v hret,
      fun p q vp vq hp hq hvp hvq => hvagree p q vp vq (hcw p hp) (hcw q hq) hvp hvq,
      -- echo backing: echoRecv unchanged, isCorrect weakens
      fun p v hp hvp => hecho_back p v (hcw p hp) hvp,
      fun v ⟨p, hp, hvp⟩ => hecho_wit v ⟨p, hcw p hp, hvp⟩⟩
  | send src dst t v =>
    subst htrans
    cases t with
    | init => -- send.init: only sent and buffer change (new .init message)
      -- Only sent and buffer change. All traces preserved trivially. Conditional: v = val from gate (sender sends val). Vote backing/agreement/echo witness: unchanged.
      dsimp only
      refine ⟨hbudget, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- echo trace: echoRecv/echoed unchanged
        intro p q w hp h
        have := hetrace p q w hp (by by_cases h' : q = src <;> simp_all)
        by_cases h' : p = src <;> simp_all
      · -- buffer echo trace: new msg is .init, not .echo
        intro p d w hp hbuf ; simp at hbuf
        have := hbet p d w hp hbuf
        by_cases h' : p = src <;> simp_all
      · -- vote trace: voteRecv/voted unchanged
        intro p q w hp h
        have := hvtrace p q w hp (by by_cases h' : p = src <;> simp_all)
        by_cases h' : q = src <;> (try subst h') <;> simp_all
      · -- buffer vote trace: new msg is .init, not .vote
        intro p d w hp hbuf ; simp at hbuf
        have := hbvt p d w hp hbuf
        by_cases h' : p = src <;> simp_all
      · -- conditional: sent grows, v = val from gate
        intro hs'
        obtain ⟨hloc, hbuf⟩ := hcond hs'
        constructor
        · intro p hp ; by_cases hpsrc : p = src
          · subst hpsrc
            have hv : v = val := by cases hgate with
              | inl hmem => exact absurd hmem hp | inr hc => exact hc.2.2.2
            have hcons := hloc p hp
            constructor
            · intro d t' w hsent ; simp at hsent
              rcases hsent with ⟨_, _, rfl⟩ | hold
              · exact hv
              · exact hcons.1 d t' w hold
            · simp only [local_consistent] at hcons ⊢ ; exact hcons.2
          · simp [hpsrc] ; exact hloc p hp
        · intro m hm hsrc ; simp at hm ; rcases hm with rfl | hold
          · cases hgate with | inl h => exact absurd h hsrc | inr hc => exact hc.2.2.2
          · exact hbuf m hold hsrc
      · -- vote backing: voteRecv/returned unchanged
        intro p w hret
        by_cases h' : p = src
        · subst h' ; simp at hret ⊢ ; exact hvotes p w hret
        · simp [h'] at hret ⊢ ; exact hvotes p w hret
      · -- vote agreement: voted unchanged
        intro p q vp vq hp hq hvp hvq
        exact hvagree p q vp vq hp hq
          (by by_cases h' : p = src <;> simp_all)
          (by by_cases h' : q = src <;> simp_all)
      · -- echo backing: echoRecv/voted unchanged
        intro p w hp hvp
        by_cases hpsrc : p = src
        · subst hpsrc ; simp at hvp ⊢ ; exact hecho_back p w hp hvp
        · simp [hpsrc] at hvp ⊢ ; exact hecho_back p w hp hvp
      · -- echo witness: voted/echoRecv unchanged → old witness persists
        intro w ⟨p, hp, hvp⟩
        have hvp' : (s.local_ p).voted w = true := by
          by_cases h' : p = src ; subst h' ; simp at hvp ; exact hvp ; simp [h'] at hvp ; exact hvp
        obtain ⟨q, hq⟩ := hecho_wit w ⟨p, hp, hvp'⟩
        refine ⟨q, ?_⟩ ; simp only [countEchoRecv] at hq ⊢
        by_cases h' : q = src
        · subst h' ; simp ; exact hq
        · simp [h'] ; exact hq
    | echo => -- send.echo: echoed changes at src; buffer grows
      -- echoed changes at src (set to some v for correct src). Echo trace: gate ensures echoed was none or already some v (single echo). Conditional: v = val from gate (echoed or sendRecv). Others: unchanged.
      dsimp only
      refine ⟨hbudget, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- echo trace: echoed set to some v at correct src; echoRecv unchanged
        intro p q w hp h
        have h' : (s.local_ q).echoRecv p w = true := by
          by_cases hq : q = src <;> simp_all
        have hold := hetrace p q w hp h'
        by_cases hpsrc : p = src
        · -- p = src: new echoed = some v (correct). Need some v = some w.
          -- hold : old echoed = some w. Gate: echoed = some v ∨ (echoed = none ∧ ...).
          -- If old echoed = some w (from hold), gate gives some w = some v → w = v.
          subst hpsrc ; simp [show p ∉ s.corrupted from hp]
          cases hgate with
          | inl hmem => exact absurd hmem hp
          | inr hc => rcases hc.2.2 with hev | ⟨hnone, _⟩
                      · rw [hold] at hev ; simp at hev ; exact hev.symm
                      · rw [hold] at hnone ; simp at hnone
        · simp [hpsrc, hold]
      · -- buffer echo trace: new echo msg has echoed set; old preserved
        intro p d w hp hbuf ; simp at hbuf
        by_cases hpsrc : p = src
        · subst hpsrc ; simp [show p ∉ s.corrupted from hp]
          rcases hbuf with ⟨_, rfl, rfl⟩ | hold
          · simp
          · -- old buffer entry: old echoed = some w, same argument as above
            have := hbet p d w hp hold
            cases hgate with
            | inl hmem => exact absurd hmem hp
            | inr hc => rcases hc.2.2 with hev | ⟨hnone, _⟩
                        · rw [this] at hev ; simp at hev ; exact hev.symm
                        · rw [this] at hnone ; simp at hnone
        · simp [hpsrc] at hbuf ⊢ ; exact hbet p d w hp hbuf
      · -- vote trace: voteRecv/voted unchanged
        intro p q w hp h
        have := hvtrace p q w hp (by by_cases h' : p = src <;> simp_all)
        by_cases h' : q = src <;> (try subst h') <;> simp_all
      · -- buffer vote trace: new msg is .echo, not .vote
        intro p d w hp hbuf ; simp at hbuf
        have := hbvt p d w hp hbuf
        by_cases h' : p = src <;> simp_all
      · -- conditional: sent + echoed grow. v = val from gate.
        intro hs'
        obtain ⟨hloc, hbuf⟩ := hcond hs'
        have hv : isCorrect n Value s src → v = val := fun hp => by
          cases hgate with
          | inl hmem => exact absurd hmem hp
          | inr hc =>
            obtain ⟨_, _, htrigger⟩ := hc
            rcases htrigger with hechoed | ⟨_, hsendrecv⟩
            · exact (hloc src hp).2.2.1 v hechoed
            · exact (hloc src hp).2.1 v hsendrecv
        constructor
        · intro p hp ; by_cases hpsrc : p = src
          · subst hpsrc
            have hval := hv hp ; have hcons := hloc p hp
            simp only [local_consistent] at hcons ⊢
            refine ⟨?_, hcons.2.1, ?_, hcons.2.2.2⟩
            · intro d t' w hsent ; simp at hsent
              rcases hsent with ⟨_, _, rfl⟩ | hold ; exact hval ; exact hcons.1 d t' w hold
            · intro w hechoed ; simp [show p ∉ s.corrupted from hp] at hechoed
              exact hechoed ▸ hval
          · simp [hpsrc] ; exact hloc p hp
        · intro m hm hsrc ; simp at hm
          rcases hm with rfl | hold ; exact hv hsrc ; exact hbuf m hold hsrc
      · -- vote backing: voteRecv/returned unchanged
        intro p w hret
        by_cases hpsrc : p = src
        · subst hpsrc ; simp at hret ⊢ ; exact hvotes p w hret
        · simp [hpsrc] at hret ⊢ ; exact hvotes p w hret
      · -- vote agreement: voted unchanged
        intro p q vp vq hp hq hvp hvq
        exact hvagree p q vp vq hp hq
          (by by_cases h' : p = src <;> simp_all)
          (by by_cases h' : q = src <;> simp_all)
      · -- echo backing: echoRecv/voted unchanged
        intro p w hp hvp
        by_cases hpsrc : p = src
        · subst hpsrc ; simp at hvp ⊢ ; exact hecho_back p w hp hvp
        · simp [hpsrc] at hvp ⊢ ; exact hecho_back p w hp hvp
      · -- echo witness: voted/echoRecv unchanged → old witness persists
        intro w ⟨p, hp, hvp⟩
        have hvp' : (s.local_ p).voted w = true := by
          by_cases h' : p = src ; subst h' ; simp at hvp ; exact hvp ; simp [h'] at hvp ; exact hvp
        obtain ⟨q, hq⟩ := hecho_wit w ⟨p, hp, hvp'⟩
        refine ⟨q, ?_⟩ ; simp only [countEchoRecv] at hq ⊢
        by_cases h' : q = src
        · subst h' ; simp ; exact hq
        · simp [h'] ; exact hq
    | vote => -- send.vote: voted changes at src; buffer grows
      -- voted changes at src. Vote trace: old voted preserved (monotone). Buffer vote trace: new message carries voted value. Conditional: v = val from echo_quorum_val or vote_quorum_val. Vote agreement: echo_quorum_intersection for echo-backed votes, pigeonhole + old hvagree for vote-backed. Echo witness: src is witness for echo threshold, old witness for re-vote/vote threshold.
      dsimp only
      refine ⟨hbudget, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- echo trace: echoRecv/echoed unchanged
        intro p q w hp h
        have := hetrace p q w hp (by by_cases hq : q = src <;> simp_all)
        by_cases h' : p = src <;> simp_all
      · -- buffer echo trace: new msg is .vote, not .echo
        intro p d w hp hbuf ; simp at hbuf
        have := hbet p d w hp hbuf
        by_cases h' : p = src <;> simp_all
      · -- vote trace: voted grows at src; voteRecv unchanged
        intro p q w hp h
        have h' : (s.local_ p).voteRecv q w = true := by
          by_cases h' : p = src <;> simp_all
        have hvold := hvtrace p q w hp h'
        by_cases hqsrc : q = src
        · -- q = src (correct): new voted w = true (old was true, stays true)
          subst hqsrc ; simp [show q ∉ s.corrupted from hp] ; simp_all
        · simp [hqsrc] ; exact hvold
      · -- buffer vote trace: new vote msg; voted set at src
        intro p d w hp hbuf ; simp at hbuf
        by_cases hpsrc : p = src
        · subst hpsrc ; simp [show p ∉ s.corrupted from hp]
          rcases hbuf with ⟨_, rfl, rfl⟩ | hold
          · simp  -- new msg: voted v = true by transition
          · -- old msg: old voted w = true → new voted w = true
            have := hbvt p d w hp hold
            simp_all
        · simp [hpsrc] at hbuf ⊢ ; exact hbvt p d w hp hbuf
      · -- conditional: sent + voted grow. v = val from counting.
        intro hs'
        obtain ⟨hloc, hbuf⟩ := hcond hs'
        have hv : isCorrect n Value s src → v = val := fun hp => by
          cases hgate with
          | inl hmem => exact absurd hmem hp
          | inr hc =>
            obtain ⟨_, _, htrigger⟩ := hc
            rcases htrigger with hvoted_old | hecho_count | hvote_count
            · exact (hloc src hp).2.2.2.1 v hvoted_old
            · exact echo_quorum_val s src v hetrace hloc
                (calc s.corrupted.length ≤ f := hbudget
                  _ < n - f := by omega
                  _ ≤ _ := hecho_count)
            · exact vote_quorum_val s src v hvtrace hloc
                (calc s.corrupted.length ≤ f := hbudget
                  _ < f + 1 := by omega
                  _ ≤ _ := hvote_count)
        constructor
        · intro p hp ; by_cases hpsrc : p = src
          · subst hpsrc
            have hval := hv hp ; have hcons := hloc p hp
            simp only [local_consistent] at hcons ⊢
            refine ⟨?_, hcons.2.1, hcons.2.2.1, ?_, hcons.2.2.2.2⟩
            · intro d t' w hsent ; simp at hsent
              rcases hsent with ⟨_, _, rfl⟩ | hold ; exact hval ; exact hcons.1 d t' w hold
            · intro w hvd ; simp [show p ∉ s.corrupted from hp] at hvd
              rcases hvd with rfl | hold ; exact hval ; exact hcons.2.2.2.1 w hold
          · simp [hpsrc] ; exact hloc p hp
        · intro m hm hsrc ; simp at hm
          rcases hm with rfl | hold ; exact hv hsrc ; exact hbuf m hold hsrc
      · -- vote backing: voteRecv/returned unchanged
        intro p w hret
        by_cases hpsrc : p = src
        · subst hpsrc ; simp at hret ⊢ ; exact hvotes p w hret
        · simp [hpsrc] at hret ⊢ ; exact hvotes p w hret
      · -- vote agreement: new vote v at correct src must agree with all correct votes.
        intro p q vp vq hp hq hvp hvq
        -- voted only grows at src: new voted w = true iff w = v ∨ old voted w = true
        have hvp_cases : vp = v ∨ (s.local_ p).voted vp = true := by
          by_cases h' : p = src
          · subst h' ; simp [show p ∉ s.corrupted from hp] at hvp ; exact hvp
          · right ; simp [h'] at hvp ; exact hvp
        have hvq_cases : vq = v ∨ (s.local_ q).voted vq = true := by
          by_cases h' : q = src
          · subst h' ; simp [show q ∉ s.corrupted from hq] at hvq ; exact hvq
          · right ; simp [h'] at hvq ; exact hvq
        -- Case-split on the gate trigger for v
        cases hgate with
        | inl hmem =>
          -- src is corrupt: voted unchanged at src → both old → old hvagree
          have hvp_old : (s.local_ p).voted vp = true := by
            by_cases h' : p = src
            · subst h' ; exact absurd hmem hp
            · simp [h'] at hvp ; exact hvp
          have hvq_old : (s.local_ q).voted vq = true := by
            by_cases h' : q = src
            · subst h' ; exact absurd hmem hq
            · simp [h'] at hvq ; exact hvq
          exact hvagree p q vp vq hp hq hvp_old hvq_old
        | inr hc =>
          obtain ⟨hsrc_corr, _, htrigger⟩ := hc
          rcases htrigger with hvoted_old | hecho_count | hvote_count
          · -- re-vote: v was already voted by src
            -- vp is either v or old; vq is either v or old. All agree via hvagree.
            rcases hvp_cases with hvp_eq | hvp_old <;> rcases hvq_cases with hvq_eq | hvq_old
            · rw [hvp_eq, hvq_eq]
            · rw [hvp_eq] ; exact hvagree src q v vq hsrc_corr hq hvoted_old hvq_old
            · rw [hvq_eq] ; exact (hvagree p src vp v hp hsrc_corr hvp_old hvoted_old)
            · exact hvagree p q vp vq hp hq hvp_old hvq_old
          · -- echo threshold (n-f echos for v): quorum intersection
            -- src has n-f echo sources for v → n-f-c correct with echoed = some v.
            -- Any old correct vote w must also have an echo quorum (from hecho_back).
            -- Two echo quorums for v ≠ w contradict n > 3f.
            rcases hvp_cases with hvp_eq | hvp_old <;> rcases hvq_cases with hvq_eq | hvq_old
            · rw [hvp_eq, hvq_eq]
            · -- vp = v (new), vq = w (old). Need v = vq.
              rw [hvp_eq]
              -- Get echo/vote backing for vq from old voter q.
              rcases hecho_back q vq hq hvq_old with hecho_w | hvote_w
              · -- Both v and vq have echo quorums → quorum intersection.
                by_contra hvw
                -- n-f-c correct echoes for v (from echo trace on src's echoRecv)
                have hgt_v : s.corrupted.length < countEchoRecv n Value (s.local_ src) v :=
                  calc s.corrupted.length ≤ f := hbudget
                    _ < n - f := by omega
                    _ ≤ _ := hecho_count
                -- n-f-c correct echoes for vq (from echo trace on q's echoRecv)
                have hgt_w : s.corrupted.length < countEchoRecv n Value (s.local_ q) vq :=
                  calc s.corrupted.length ≤ f := hbudget
                    _ < n - f := by omega
                    _ ≤ _ := hecho_w
                -- Pigeonhole: correct process r1 echoed v, correct r2 echoed vq
                obtain ⟨r1, hr1_echo, hr1_corr⟩ := pigeonhole_filter n
                  ((s.local_ src).echoRecv · v) s.corrupted hgt_v
                obtain ⟨r2, hr2_echo, hr2_corr⟩ := pigeonhole_filter n
                  ((s.local_ q).echoRecv · vq) s.corrupted hgt_w
                -- Echo trace: r1.echoed = some v, r2.echoed = some vq
                have hr1_echoed := hetrace r1 src v hr1_corr hr1_echo
                have hr2_echoed := hetrace r2 q vq hr2_corr hr2_echo
                exact hvw (echo_quorum_intersection hn s src q v vq hbudget hetrace hecho_count hecho_w)
              · -- vq backed by f+1 votes → correct old voter for vq → use echo_quorum_intersection
                have hgt_w : s.corrupted.length < countVoteRecv n Value (s.local_ q) vq :=
                  calc s.corrupted.length ≤ f := hbudget
                    _ < f + 1 := by omega
                    _ ≤ _ := hvote_w
                obtain ⟨r, hr_vote, hr_corr⟩ := pigeonhole_filter n
                  ((s.local_ q).voteRecv · vq) s.corrupted hgt_w
                have hr_voted := hvtrace q r vq hr_corr hr_vote
                -- r voted vq (old). By hecho_back, r has echo or vote backing for vq.
                rcases hecho_back r vq hr_corr hr_voted with hecho_r | hvote_r
                · -- r has echo backing → quorum intersection with src's echo count
                  exact echo_quorum_intersection hn s src r v vq hbudget hetrace hecho_count hecho_r
                · -- r has vote backing → use echo witness to get echo-backed process
                  obtain ⟨q2, hq2⟩ := hecho_wit vq ⟨r, hr_corr, hr_voted⟩
                  exact echo_quorum_intersection hn s src q2 v vq hbudget hetrace hecho_count hq2
            · -- vp = w (old), vq = v (new). Symmetric.
              rw [hvq_eq]
              rcases hecho_back p vp hp hvp_old with hecho_w | hvote_w
              · by_contra hvw
                have hgt_v : s.corrupted.length < countEchoRecv n Value (s.local_ src) v :=
                  calc s.corrupted.length ≤ f := hbudget
                    _ < n - f := by omega
                    _ ≤ _ := hecho_count
                have hgt_w : s.corrupted.length < countEchoRecv n Value (s.local_ p) vp :=
                  calc s.corrupted.length ≤ f := hbudget
                    _ < n - f := by omega
                    _ ≤ _ := hecho_w
                exact hvw (echo_quorum_intersection hn s p src vp v hbudget hetrace hecho_w hecho_count)
              · -- vp backed by f+1 votes → symmetric argument
                have hgt_w : s.corrupted.length < countVoteRecv n Value (s.local_ p) vp :=
                  calc s.corrupted.length ≤ f := hbudget
                    _ < f + 1 := by omega
                    _ ≤ _ := hvote_w
                obtain ⟨r, hr_vote, hr_corr⟩ := pigeonhole_filter n
                  ((s.local_ p).voteRecv · vp) s.corrupted hgt_w
                have hr_voted := hvtrace p r vp hr_corr hr_vote
                rcases hecho_back r vp hr_corr hr_voted with hecho_r | hvote_r
                · exact echo_quorum_intersection hn s r src vp v hbudget hetrace hecho_r hecho_count
                · -- use echo witness to get echo-backed process
                  obtain ⟨q2, hq2⟩ := hecho_wit vp ⟨r, hr_corr, hr_voted⟩
                  exact echo_quorum_intersection hn s q2 src vp v hbudget hetrace hq2 hecho_count
            · exact hvagree p q vp vq hp hq hvp_old hvq_old
          · -- vote threshold (f+1 votes for v): pigeonhole → correct old voter → old hvagree
            -- f+1 > f ≥ |corrupted| → ∃ correct r with voteRecv src r v = true
            have hgt : s.corrupted.length < countVoteRecv n Value (s.local_ src) v :=
              calc s.corrupted.length ≤ f := hbudget
                _ < f + 1 := by omega
                _ ≤ _ := hvote_count
            obtain ⟨r, hr_vote, hr_corr⟩ := pigeonhole_filter n
              ((s.local_ src).voteRecv · v) s.corrupted hgt
            -- r voted v in old state (via vote trace)
            have hr_voted := hvtrace src r v hr_corr hr_vote
            -- v agrees with all old correct votes via hvagree
            rcases hvp_cases with hvp_eq | hvp_old <;> rcases hvq_cases with hvq_eq | hvq_old
            · rw [hvp_eq, hvq_eq]
            · rw [hvp_eq] ; exact hvagree r q v vq hr_corr hq hr_voted hvq_old
            · rw [hvq_eq] ; exact (hvagree p r vp v hp hr_corr hvp_old hr_voted)
            · exact hvagree p q vp vq hp hq hvp_old hvq_old
      · -- echo backing: voted changes at src; echoRecv unchanged
        intro p w hp hvp
        -- New voted at src: if w = v then true else old.
        -- Either w = v (new vote) or old voted w = true.
        have hvp_cases : w = v ∨ (s.local_ p).voted w = true := by
          by_cases h' : p = src
          · subst h' ; simp [show p ∉ s.corrupted from hp] at hvp ; exact hvp
          · right ; simp [h'] at hvp ; exact hvp
        -- isCorrect unchanged by send
        have hp' : isCorrect n Value s p := hp
        rcases hvp_cases with rfl | hvp_old
        · -- new vote w (= v) at p = src (must be src, since only src gains new voted)
          by_cases h' : p = src
          · subst h'
            cases hgate with
            | inl hmem => exact absurd hmem hp'  -- src corrupt contradicts p correct
            | inr hc =>
              obtain ⟨_, _, htrigger⟩ := hc
              simp at ⊢
              rcases htrigger with hvoted_old | hecho_count | hvote_count
              · exact hecho_back p w hp' hvoted_old  -- re-vote: old disjunction
              · left ; exact hecho_count               -- echo threshold from gate
              · right ; exact hvote_count              -- vote threshold from gate
          · -- p ≠ src: new voted w → old voted w (since voted unchanged at p)
            simp [h'] at hvp ⊢ ; exact hecho_back p w hp' hvp
        · -- old vote: echoRecv unchanged at p
          by_cases h' : p = src
          · subst h' ; simp at ⊢ ; exact hecho_back p w hp' hvp_old
          · simp [h'] at ⊢ ; exact hecho_back p w hp' hvp_old
      · -- echo witness: new vote at src → src is witness or old witness persists
        intro w ⟨p, hp, hvp⟩
        have hp' : isCorrect n Value s p := hp
        have hvp_cases : w = v ∨ (s.local_ p).voted w = true := by
          by_cases h' : p = src
          · subst h' ; simp [show p ∉ s.corrupted from hp] at hvp ; exact hvp
          · right ; simp [h'] at hvp ; exact hvp
        rcases hvp_cases with hwv | hvp_old
        · -- w = v (new vote): case split on gate trigger
          cases hgate with
          | inl hmem =>
            by_cases hps : p = src
            · exact absurd (hps ▸ hmem) hp'
            · have : (s.local_ p).voted w = true := by simp [hps] at hvp ; exact hvp
              obtain ⟨q, hq⟩ := hecho_wit w ⟨p, hp', this⟩
              refine ⟨q, ?_⟩ ; simp only [countEchoRecv] at hq ⊢
              by_cases h' : q = src <;> (try subst h') <;> simp_all
          | inr hc =>
            obtain ⟨hsrc_corr, _, htrigger⟩ := hc
            rcases htrigger with hvoted_old | hecho_count | hvote_count
            · -- re-vote: old witness
              obtain ⟨q, hq⟩ := hecho_wit w ⟨src, hsrc_corr, hwv ▸ hvoted_old⟩
              refine ⟨q, ?_⟩ ; simp only [countEchoRecv] at hq ⊢
              by_cases h' : q = src <;> (try subst h') <;> simp_all
            · -- echo threshold: src is the witness
              refine ⟨src, ?_⟩ ; simp only [countEchoRecv] at hecho_count ⊢
              simp ; rw [hwv] ; exact hecho_count
            · -- vote threshold: old witness via pigeonhole
              have hgt : s.corrupted.length < countVoteRecv n Value (s.local_ src) v :=
                calc s.corrupted.length ≤ f := hbudget
                  _ < f + 1 := by omega
                  _ ≤ _ := hvote_count
              obtain ⟨r, hr_vote, hr_corr⟩ := pigeonhole_filter n
                ((s.local_ src).voteRecv · v) s.corrupted hgt
              have hr_voted := hvtrace src r v hr_corr hr_vote
              obtain ⟨q, hq⟩ := hecho_wit w ⟨r, hr_corr, hwv ▸ hr_voted⟩
              refine ⟨q, ?_⟩ ; simp only [countEchoRecv] at hq ⊢
              by_cases h' : q = src <;> (try subst h') <;> simp_all
        · -- old vote: old witness persists
          obtain ⟨q, hq⟩ := hecho_wit w ⟨p, hp', hvp_old⟩
          refine ⟨q, ?_⟩ ; simp only [countEchoRecv] at hq ⊢
          by_cases h' : q = src
          · subst h' ; simp ; exact hq
          · simp [h'] ; exact hq
  | recv src dst t v =>
    subst htrans
    cases t with
    | init => -- recv.init: sendRecv may change at dst; buffer shrinks
      -- sendRecv may change at dst. All other fields unchanged. Conditional: v = val from buffer_consistent.
      dsimp only ; simp at hgate
      refine ⟨hbudget, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- echo trace: echoRecv/echoed unchanged
        intro p q w hp h
        have h' : (s.local_ q).echoRecv p w = true := by
          by_cases hq : q = dst
          · subst hq ; by_cases hc : src = sender ∧ (s.local_ q).sendRecv = none <;> simp [hc] at h <;> exact h
          · simp [hq] at h ; exact h
        have := hetrace p q w hp h'
        by_cases hp' : p = dst
        · subst hp' ; by_cases hc : src = sender ∧ (s.local_ p).sendRecv = none <;> simp [hc] <;> exact this
        · simp [hp'] ; exact this
      · -- buffer echo trace: buffer shrinks, echoed unchanged
        intro p d w hp hbuf ; simp at hbuf
        have := hbet p d w hp hbuf
        by_cases hp' : p = dst
        · subst hp' ; by_cases hc : src = sender ∧ (s.local_ p).sendRecv = none <;> simp [hc] <;> exact this
        · simp [hp'] ; exact this
      · -- vote trace: voteRecv/voted unchanged
        intro p q w hp h
        have h' : (s.local_ p).voteRecv q w = true := by
          by_cases hp' : p = dst
          · subst hp' ; by_cases hc : src = sender ∧ (s.local_ p).sendRecv = none <;> simp [hc] at h <;> exact h
          · simp [hp'] at h ; exact h
        have := hvtrace p q w hp h'
        by_cases hq' : q = dst
        · subst hq' ; by_cases hc : src = sender ∧ (s.local_ q).sendRecv = none <;> simp [hc] <;> exact this
        · simp [hq'] ; exact this
      · -- buffer vote trace: buffer shrinks, voted unchanged
        intro p d w hp hbuf ; simp at hbuf
        have := hbvt p d w hp hbuf
        by_cases hp' : p = dst
        · subst hp' ; by_cases hc : src = sender ∧ (s.local_ p).sendRecv = none <;> simp [hc] <;> exact this
        · simp [hp'] ; exact this
      · -- conditional: sendRecv may change; mv = val from buffer_consistent
        intro hs'
        obtain ⟨hloc, hbuf⟩ := hcond hs'
        constructor
        · intro p hp ; by_cases hpdst : p = dst
          · subst hpdst ; have hcons := hloc p hp
            by_cases hrecv : src = sender ∧ (s.local_ p).sendRecv = none
            · simp [hrecv]
              have hval : v = val := hbuf ⟨src, p, .init, v⟩ hgate (hrecv.1 ▸ hs')
              subst hval
              exact ⟨hcons.1, fun w h => by injection h with h ; exact h ▸ rfl, hcons.2.2⟩
            · simp [hrecv] ; exact hcons
          · simp [hpdst] ; exact hloc p hp
        · intro m hm hsrc ; simp at hm ; exact hbuf m hm.2 hsrc
      · -- vote backing: voteRecv/returned unchanged
        intro p w hret
        by_cases hp' : p = dst
        · subst hp'
          by_cases hc : src = sender ∧ (s.local_ p).sendRecv = none
          · simp [hc] at hret ⊢ ; exact hvotes p w hret
          · simp [hc] at hret ⊢ ; exact hvotes p w hret
        · simp [hp'] at hret ⊢ ; exact hvotes p w hret
      · -- vote agreement: voted unchanged
        intro p q vp vq hp hq hvp hvq
        exact hvagree p q vp vq hp hq
          (by by_cases hp' : p = dst
              · subst hp' ; by_cases hc : src = sender ∧ (s.local_ p).sendRecv = none <;> simp [hc] at hvp <;> exact hvp
              · simp [hp'] at hvp ; exact hvp)
          (by by_cases hq' : q = dst
              · subst hq' ; by_cases hc : src = sender ∧ (s.local_ q).sendRecv = none <;> simp [hc] at hvq <;> exact hvq
              · simp [hq'] at hvq ; exact hvq)
      · -- echo backing: echoRecv/voted unchanged by recv.init
        intro p w hp hvp
        have hvp' : (s.local_ p).voted w = true := by
          by_cases h' : p = dst
          · subst h' ; by_cases hc : src = sender ∧ (s.local_ p).sendRecv = none <;> simp [hc] at hvp <;> exact hvp
          · simp [h'] at hvp ; exact hvp
        have hold := hecho_back p w hp hvp'
        simp only [countEchoRecv] at hold ⊢
        by_cases h' : p = dst
        · subst h' ; by_cases hc : src = sender ∧ (s.local_ p).sendRecv = none <;> simp [hc] <;> exact hold
        · simp [h'] ; exact hold
      · -- echo witness: voted/echoRecv unchanged → old witness persists
        intro w ⟨p, hp, hvp⟩
        have hvp' : (s.local_ p).voted w = true := by
          by_cases h' : p = dst
          · subst h' ; by_cases hc : src = sender ∧ (s.local_ p).sendRecv = none <;> simp [hc] at hvp <;> exact hvp
          · simp [h'] at hvp ; exact hvp
        obtain ⟨q, hq⟩ := hecho_wit w ⟨p, hp, hvp'⟩
        refine ⟨q, ?_⟩ ; simp only [countEchoRecv] at hq ⊢
        by_cases h' : q = dst
        · subst h' ; by_cases hc : src = sender ∧ (s.local_ q).sendRecv = none <;> simp [hc] <;> exact hq
        · simp [h'] ; exact hq
    | echo => -- recv.echo: echoRecv grows at dst; buffer shrinks
      -- echoRecv grows at dst. Echo trace: new entry from buffer echo trace. Counts monotone. Others unchanged.
      dsimp only ; simp at hgate
      refine ⟨hbudget, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- echo trace: new echoRecv entry from buffer echo trace; old from echo trace
        intro p q w hp h
        have h_old_or_new : (s.local_ q).echoRecv p w = true ∨
            (q = dst ∧ p = src ∧ w = v) := by
          by_cases hqdst : q = dst
          · subst hqdst ; simp at h ; split at h
            · simp at h ; by_cases hpv : p = src ∧ w = v
              · right ; exact ⟨rfl, hpv.1, hpv.2⟩
              · left ; simp [hpv] at h ; exact h
            · left ; exact h
          · left ; simp [hqdst] at h ; exact h
        rcases h_old_or_new with hold | ⟨_, hpsrc, hwv⟩
        · -- old entry: use echo trace, push through if
          have := hetrace p q w hp hold
          by_cases hp' : p = dst
          · subst hp' ; simp ; split <;> exact this
          · simp [hp'] ; exact this
        · -- new entry: p = src, w = v → use buffer echo trace
          subst hpsrc ; rw [hwv]
          have := hbet p dst v hp hgate
          by_cases hp' : p = dst
          · subst hp' ; simp ; split <;> exact this
          · simp [hp'] ; exact this
      · -- buffer echo trace: buffer shrinks, echoed unchanged
        intro p d w hp hbuf ; simp at hbuf
        have := hbet p d w hp hbuf.2
        by_cases hp' : p = dst
        · subst hp' ; simp ; split <;> exact this
        · simp [hp'] ; exact this
      · -- vote trace: voteRecv/voted unchanged
        intro p q w hp h
        have h' : (s.local_ p).voteRecv q w = true := by
          by_cases hp' : p = dst
          · subst hp' ; simp at h ; split at h <;> exact h
          · simp [hp'] at h ; exact h
        have := hvtrace p q w hp h'
        by_cases hq' : q = dst
        · subst hq' ; simp ; split <;> exact this
        · simp [hq'] ; exact this
      · -- buffer vote trace: buffer shrinks, voted unchanged
        intro p d w hp hbuf ; simp at hbuf
        have := hbvt p d w hp hbuf
        by_cases hp' : p = dst
        · subst hp' ; simp ; split <;> exact this
        · simp [hp'] ; exact this
      · -- conditional: echoRecv not in local_consistent
        intro hs'
        obtain ⟨hloc, hbuf⟩ := hcond hs'
        constructor
        · intro p hp ; by_cases hpdst : p = dst
          · subst hpdst ; have hcons := hloc p hp
            simp only [local_consistent] at hcons ⊢
            by_cases hnew : (s.local_ p).echoRecv src v = false <;> simp [hnew]
            all_goals exact hcons
          · simp [hpdst] ; exact hloc p hp
        · intro m hm hsrc ; simp at hm ; exact hbuf m hm.2 hsrc
      · -- vote backing: voteRecv/returned unchanged
        intro p w hret
        by_cases hp' : p = dst
        · subst hp' ; simp at hret ⊢ ; split at hret <;> simp_all <;> exact hvotes p w (by assumption)
        · simp [hp'] at hret ⊢ ; exact hvotes p w hret
      · -- vote agreement: voted unchanged
        intro p q vp vq hp hq hvp hvq
        exact hvagree p q vp vq hp hq
          (by by_cases hp' : p = dst
              · subst hp' ; simp at hvp ; split at hvp <;> exact hvp
              · simp [hp'] at hvp ; exact hvp)
          (by by_cases hq' : q = dst
              · subst hq' ; simp at hvq ; split at hvq <;> exact hvq
              · simp [hq'] at hvq ; exact hvq)
      · -- echo backing: echoRecv grows at dst (monotone), voted unchanged
        intro p w hp hvp
        have hvp' : (s.local_ p).voted w = true := by
          by_cases h' : p = dst
          · subst h' ; simp at hvp ; split at hvp <;> exact hvp
          · simp [h'] at hvp ; exact hvp
        have hold := hecho_back p w hp hvp'
        -- For p ≠ dst: local state unchanged → hold applies directly.
        -- For p = dst: echoRecv grows (monotone), voteRecv unchanged.
        by_cases h' : p = dst
        · subst h'
          by_cases hc : (s.local_ p).echoRecv src v = false
          · -- New echoRecv entry
            simp only [hc, ite_true] at ⊢
            rcases hold with h1 | h2
            · left ; simp only [countEchoRecv] at h1 ⊢
              apply Nat.le_trans h1 ; apply filter_length_mono
              intro q hq ; simp at hq ⊢
              by_cases hqs : q = src ∧ w = v <;> simp_all
            · right ; simp only [countVoteRecv] at h2 ⊢ ; exact h2
          · -- echoRecv unchanged (already had entry)
            simp only [hc] at ⊢ ; exact hold
        · simp only [h', ite_false] at ⊢ ; exact hold
      · -- echo witness: voted unchanged, echoRecv grows → old witness count ≥ old
        intro w ⟨p, hp, hvp⟩
        have hvp' : (s.local_ p).voted w = true := by
          by_cases h' : p = dst
          · subst h' ; by_cases hc : (s.local_ p).echoRecv src v = false <;> simp [hc] at hvp <;> exact hvp
          · simp [h'] at hvp ; exact hvp
        obtain ⟨q, hq⟩ := hecho_wit w ⟨p, hp, hvp'⟩
        refine ⟨q, ?_⟩
        -- echoRecv at q: unchanged if q ≠ dst, grows if q = dst → count ≥ old
        by_cases h' : q = dst
        · subst h'
          by_cases hc : (s.local_ q).echoRecv src v = false
          · -- new entry: count grows
            simp only [countEchoRecv, hc, ite_true] at hq ⊢
            apply Nat.le_trans hq ; apply filter_length_mono
            intro r hr ; simp at hr ⊢ ; by_cases hrs : r = src ∧ w = v <;> simp_all
          · -- already had entry: unchanged
            simp only [countEchoRecv, hc] at hq ⊢ ; exact hq
        · simp only [countEchoRecv, h', ite_false] at hq ⊢ ; exact hq
    | vote => -- recv.vote: voteRecv grows at dst; buffer shrinks
      -- voteRecv grows at dst. Vote trace: new entry from buffer vote trace. Vote backing: countVoteRecv monotone. Others unchanged.
      dsimp only ; simp at hgate
      refine ⟨hbudget, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- echo trace: echoRecv/echoed unchanged (recv.vote only touches voteRecv)
        intro p q w hp h
        have h' := hetrace p q w hp (show (s.local_ q).echoRecv p w = true by
          by_cases hq : q = dst
          · subst hq ; by_cases hc : (s.local_ q).voteRecv src v = false <;> simp [hc] at h <;> exact h
          · simp [hq] at h ; exact h)
        by_cases hp' : p = dst
        · subst hp' ; by_cases hc : (s.local_ p).voteRecv src v = false <;> simp [hc] <;> exact h'
        · simp [hp'] ; exact h'
      · -- buffer echo trace: buffer shrinks, echoed unchanged
        intro p d w hp hbuf ; simp at hbuf
        have h' := hbet p d w hp hbuf
        by_cases hp' : p = dst
        · subst hp' ; by_cases hc : (s.local_ p).voteRecv src v = false <;> simp [hc] <;> exact h'
        · simp [hp'] ; exact h'
      · -- vote trace: new voteRecv entry from buffer vote trace; old from vote trace
        intro p q w hp h
        have h_old_or_new : (s.local_ p).voteRecv q w = true ∨
            (p = dst ∧ q = src ∧ w = v) := by
          by_cases hpdst : p = dst
          · subst hpdst ; by_cases hc : (s.local_ p).voteRecv src v = false
            · simp [hc] at h ; by_cases hqv : q = src ∧ w = v
              · right ; exact ⟨rfl, hqv.1, hqv.2⟩
              · left ; simp [hqv] at h ; exact h
            · left ; simp [hc] at h ; exact h
          · left ; simp [hpdst] at h ; exact h
        rcases h_old_or_new with hold | ⟨_, hqsrc, hwv⟩
        · -- old entry: use vote trace, push through if
          have := hvtrace p q w hp hold
          by_cases hq' : q = dst
          · subst hq' ; by_cases hc : (s.local_ q).voteRecv src v = false <;> simp [hc] <;> exact this
          · simp [hq'] ; exact this
        · -- new entry: q = src, w = v → use buffer vote trace
          rw [hqsrc, hwv]
          have hpc : isCorrect n Value s src := by rw [← hqsrc] ; exact hp
          have := hbvt src dst v hpc hgate
          by_cases hq' : src = dst
          · subst hq' ; simp ; by_cases hc : (s.local_ src).voteRecv src v = false <;> simp [hc] <;> exact this
          · simp [hq'] ; exact this
      · -- buffer vote trace: buffer shrinks, voted unchanged
        intro p d w hp hbuf ; simp at hbuf
        have := hbvt p d w hp hbuf.2
        by_cases hp' : p = dst
        · subst hp' ; by_cases hc : (s.local_ p).voteRecv src v = false <;> simp [hc] <;> exact this
        · simp [hp'] ; exact this
      · -- conditional: voteRecv not in local_consistent
        intro hs'
        obtain ⟨hloc, hbuf⟩ := hcond hs'
        constructor
        · intro p hp ; by_cases hpdst : p = dst
          · subst hpdst ; have hcons := hloc p hp
            simp only [local_consistent] at hcons ⊢
            by_cases hnew : (s.local_ p).voteRecv src v = false <;> simp [hnew]
            all_goals exact hcons
          · simp [hpdst] ; exact hloc p hp
        · intro m hm hsrc ; simp at hm ; exact hbuf m hm.2 hsrc
      · -- vote backing: countVoteRecv monotone (voteRecv only grows)
        intro p w hret
        by_cases hpdst : p = dst
        · subst hpdst
          by_cases hc : (s.local_ p).voteRecv src v = false
          · -- new entry: countVoteRecv can only grow
            simp [hc] at hret ⊢
            have hold := hvotes p w hret
            simp only [countVoteRecv] at hold ⊢
            apply Nat.le_trans hold ; apply filter_length_mono
            intro q hq ; simp at hq
            by_cases hqs : q = src <;> simp_all
          · simp [hc] at hret ⊢ ; exact hvotes p w hret
        · simp [hpdst] at hret ⊢ ; exact hvotes p w hret
      · -- vote agreement: voted unchanged
        intro p q vp vq hp hq hvp hvq
        exact hvagree p q vp vq hp hq
          (by by_cases hp' : p = dst
              · subst hp' ; by_cases hc : (s.local_ p).voteRecv src v = false <;> simp [hc] at hvp <;> exact hvp
              · simp [hp'] at hvp ; exact hvp)
          (by by_cases hq' : q = dst
              · subst hq' ; by_cases hc : (s.local_ q).voteRecv src v = false <;> simp [hc] at hvq <;> exact hvq
              · simp [hq'] at hvq ; exact hvq)
      · -- echo backing: echoRecv/voted unchanged by recv.vote
        intro p w hp hvp
        have hvp' : (s.local_ p).voted w = true := by
          by_cases h' : p = dst
          · subst h' ; by_cases hc : (s.local_ p).voteRecv src v = false <;> simp [hc] at hvp <;> exact hvp
          · simp [h'] at hvp ; exact hvp
        have hold := hecho_back p w hp hvp'
        -- echoRecv unchanged, voteRecv grows at dst → both counts ≥ old
        rcases hold with hecho | hvote
        · -- echo backing: countEchoRecv unchanged at p
          left ; simp only [countEchoRecv] at hecho ⊢
          by_cases h' : p = dst
          · subst h' ; by_cases hc : (s.local_ p).voteRecv src v = false <;> simp [hc] <;> exact hecho
          · simp [h'] ; exact hecho
        · -- vote backing: countVoteRecv monotone at p (voteRecv grows)
          right ; simp only [countVoteRecv] at hvote ⊢
          by_cases h' : p = dst
          · subst h' ; by_cases hc : (s.local_ p).voteRecv src v = false <;> simp [hc]
            · apply Nat.le_trans hvote ; apply filter_length_mono
              intro q hq ; simp at hq ⊢ ; by_cases hqs : q = src ∧ w = v <;> simp_all
            · exact hvote
          · simp [h'] ; exact hvote
      · -- echo witness: voted/echoRecv unchanged → old witness persists
        intro w ⟨p, hp, hvp⟩
        have hvp' : (s.local_ p).voted w = true := by
          by_cases h' : p = dst
          · subst h' ; by_cases hc : (s.local_ p).voteRecv src v = false <;> simp [hc] at hvp <;> exact hvp
          · simp [h'] at hvp ; exact hvp
        obtain ⟨q, hq⟩ := hecho_wit w ⟨p, hp, hvp'⟩
        refine ⟨q, ?_⟩ ; simp only [countEchoRecv] at hq ⊢
        by_cases h' : q = dst
        · subst h' ; by_cases hc : (s.local_ q).voteRecv src v = false <;> simp [hc] <;> exact hq
        · simp [h'] ; exact hq
  -- ── doReturn: only returned changes at process i ──
  -- Only returned changes. Conditional: v = val from vote_quorum_val. Vote backing: gate gives count. Others unchanged.
  | doReturn i v =>
    subst htrans
    refine ⟨hbudget, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- echo trace: unchanged
      intro p q w hp h
      have := hetrace p q w hp (by by_cases h' : q = i <;> simp_all)
      by_cases h' : p = i <;> (try subst h') <;> simp_all
    · -- buffer echo trace: unchanged
      intro p dst w hp hbuf
      have := hbet p dst w hp hbuf
      by_cases h' : p = i <;> (try subst h') <;> simp_all
    · -- vote trace: unchanged
      intro p q w hp h
      have := hvtrace p q w hp (by by_cases h' : p = i <;> simp_all)
      by_cases h' : q = i <;> (try subst h') <;> simp_all
    · -- buffer vote trace: unchanged
      intro p dst w hp hbuf
      have := hbvt p dst w hp hbuf
      by_cases h' : p = i <;> (try subst h') <;> simp_all
    · -- conditional: returned changes; v = val by vote counting
      intro hs'
      obtain ⟨hloc, hbuf⟩ := hcond hs'
      constructor
      · intro p hp ; by_cases hpi : p = i
        · subst hpi ; have hcons := hloc p hp
          simp only [local_consistent] at hcons ⊢
          refine ⟨hcons.1, hcons.2.1, hcons.2.2.1, hcons.2.2.2.1, ?_⟩
          intro w hret ; simp at hret ; subst hret
          -- v = val from vote quorum: countVoteRecv ≥ n−f > f ≥ |corrupted|
          exact vote_quorum_val s p v hvtrace hloc
            (calc s.corrupted.length ≤ f := hbudget
              _ < n - f := by omega
              _ ≤ _ := hgate.2.2)
        · simp [hpi] ; exact hloc p hp
      · exact hbuf
    · -- vote backing: gate gives count for i; others unchanged
      intro p w hret
      by_cases hpi : p = i
      · subst hpi ; simp at hret ; subst hret ; simp ; exact hgate.2.2
      · simp [hpi] at hret ⊢ ; exact hvotes p w hret
    · -- vote agreement: voted unchanged
      intro p q vp vq hp hq hvp hvq
      exact hvagree p q vp vq hp hq
        (by by_cases h' : p = i ; subst h' ; simp at hvp ; exact hvp ; simp [h'] at hvp ; exact hvp)
        (by by_cases h' : q = i ; subst h' ; simp at hvq ; exact hvq ; simp [h'] at hvq ; exact hvq)
    · -- echo/vote backing: echoRecv/voteRecv/voted unchanged
      intro p w hp hvp
      have hvp' : (s.local_ p).voted w = true := by
        by_cases h' : p = i ; subst h' ; simp at hvp ; exact hvp ; simp [h'] at hvp ; exact hvp
      have hold := hecho_back p w hp hvp'
      by_cases hpi : p = i
      · subst hpi ; simp only [ite_true] at ⊢
        rcases hold with h1 | h2
        · left ; simp only [countEchoRecv] at h1 ⊢ ; exact h1
        · right ; simp only [countVoteRecv] at h2 ⊢ ; exact h2
      · simp only [hpi, ite_false] at ⊢ ; exact hold
    · -- echo witness: voted/echoRecv unchanged → old witness persists
      intro w ⟨p, hp, hvp⟩
      have hvp' : (s.local_ p).voted w = true := by
        by_cases h' : p = i ; subst h' ; simp at hvp ; exact hvp ; simp [h'] at hvp ; exact hvp
      obtain ⟨q, hq⟩ := hecho_wit w ⟨p, hp, hvp'⟩
      refine ⟨q, ?_⟩ ; simp only [countEchoRecv] at hq ⊢
      by_cases h' : q = i
      · subst h' ; simp ; exact hq
      · simp [h'] ; exact hq

/-! ### Validity -/

/-- Validity: if the sender is always correct, any correct process
    that returns a value returns `val`. -/
-- Derives from conjunct 6 (conditional): if sender correct, local_consistent gives returned = some v → v = val.
theorem brb_validity (sender : Fin n) (val : Value) (hn : n > 3 * f) :
    pred_implies
      (tla_and (brb n f Value sender val).safety
        [tlafml| □ ⌜ fun s => isCorrect n Value s sender ⌝])
      [tlafml| □ ⌜ fun s => ∀ p v, isCorrect n Value s p →
        (s.local_ p).returned = some v → v = val ⌝] := by
  intro e ⟨hsafety, hsc⟩
  have hinv := init_invariant
    (brb_inv_init n f Value sender val)
    (fun s s' hn' hi => brb_inv_step n f Value sender val hn s s' hn' hi)
    e hsafety
  intro k
  obtain ⟨_, _, _, _, _, hcond, _, _, _, _⟩ := hinv k
  intro p v hp hret
  exact (hcond (hsc k)).1 p hp |>.2.2.2.2 v hret

/-! ### Agreement -/

/-- Agreement: all non-faulty processes that return a value, return the
    same value. Proof: each returned value has ≥ n−f votes. Since n−f > f,
    pigeonhole gives a correct voter for each. Vote agreement (conjunct 8)
    forces the values to be equal. -/
-- Each returned value has ≥ n-f votes. Pigeonhole gives a correct voter. Vote trace bridges voteRecv → voted. Vote agreement (conjunct 8) forces values equal.
theorem brb_agreement (sender : Fin n) (val : Value) (hn : n > 3 * f) :
    pred_implies (brb n f Value sender val).safety
      [tlafml| □ ⌜ agreement n Value ⌝] := by
  intro e hsafety
  have hinv := init_invariant
    (brb_inv_init n f Value sender val)
    (fun s s' hn' hi => brb_inv_step n f Value sender val hn s s' hn' hi)
    e hsafety
  intro k
  obtain ⟨hbudget, _, _, hvtrace, _, _, hvotes, hvagree, _, _⟩ := hinv k
  intro p q vp vq hp hq hretp hretq
  -- p returned vp with ≥ n−f votes. Since n−f > f ≥ |corrupted|,
  -- pigeonhole gives a correct voter rp that voted vp.
  have hvp := hvotes p vp hretp
  have hgt_p : (exec.drop k e 0).corrupted.length <
      countVoteRecv n Value ((exec.drop k e 0).local_ p) vp :=
    calc (exec.drop k e 0).corrupted.length ≤ f := hbudget
      _ < n - f := by omega
      _ ≤ _ := hvp
  obtain ⟨rp, hrp_vote, hrp_corr⟩ := pigeonhole_filter n
    ((exec.drop k e 0).local_ p |>.voteRecv · vp) (exec.drop k e 0).corrupted hgt_p
  -- Similarly for q and vq.
  have hvq := hvotes q vq hretq
  have hgt_q : (exec.drop k e 0).corrupted.length <
      countVoteRecv n Value ((exec.drop k e 0).local_ q) vq :=
    calc (exec.drop k e 0).corrupted.length ≤ f := hbudget
      _ < n - f := by omega
      _ ≤ _ := hvq
  obtain ⟨rq, hrq_vote, hrq_corr⟩ := pigeonhole_filter n
    ((exec.drop k e 0).local_ q |>.voteRecv · vq) (exec.drop k e 0).corrupted hgt_q
  -- rp voted vp and rq voted vq (via vote trace). By vote agreement, vp = vq.
  have hrp_voted := hvtrace p rp vp hrp_corr hrp_vote
  have hrq_voted := hvtrace q rq vq hrq_corr hrq_vote
  exact hvagree rp rq vp vq hrp_corr hrq_corr hrp_voted hrq_voted

/-! ### Message tracking invariant -/

/-- Message tracking invariant: once a vote is sent, it is either
    still in the buffer or already received. Init: sent=false (vacuous).
    Step: send sets both sent and buffer; recv consumes buffer and sets
    voteRecv; other actions preserve both. -/
theorem vote_msg_tracking (sender : Fin n) (val : Value) :
    pred_implies (brb n f Value sender val).safety
      [tlafml| □ ⌜ fun s => ∀ q r v,
        (s.local_ q).sent r .vote v = true →
        s.buffer ⟨q, r, .vote, v⟩ = true ∨
        (s.local_ r).voteRecv q v = true ⌝] := by
  intro e hsafety
  apply init_invariant
    (fun s hs => by intro q r w h ; simp [hs.1, LocalState.init] at h)
    (fun s s' hnext hi => by
      obtain ⟨action, _, htrans⟩ := hnext
      cases action with
      | corrupt j =>
        simp only [brb] at htrans ; subst htrans ; exact hi
      | send src dst t mv =>
        simp only [brb] at htrans ; subst htrans
        intro q r w hsent
        by_cases hq : q = src
        · -- q = src: sent may have new entries, buffer gains entry
          by_cases hnew : r = dst ∧ MsgType.vote = t ∧ w = mv
          · -- new sent entry → buffer has it
            obtain ⟨rfl, rfl, rfl⟩ := hnew ; left ; simp [hq]
          · -- old sent entry → use IH
            have hold : (s.local_ src).sent r .vote w = true := by
              simp only [hq, ite_true, hnew, ite_false] at hsent ; exact hsent
            rcases hi q r w (by rw [hq] ; exact hold) with hbuf | hvr
            · left ; simp only []
              by_cases hm : (⟨q, r, MsgType.vote, w⟩ : Message n Value) = ⟨src, dst, t, mv⟩
              · rw [if_pos hm]
              · rw [if_neg hm] ; exact hbuf
            · right ; by_cases hr : r = src
              · simp only [hr, ite_true] ; rw [hr] at hvr; exact hvr
              · simp [hr] ; exact hvr
        · -- q ≠ src: sent unchanged
          simp [hq] at hsent
          rcases hi q r w hsent with hbuf | hvr
          · left ; simp [hbuf]
          · right ; by_cases hr : r = src
            · simp only [hr, ite_true] ; rw [hr] at hvr; exact hvr
            · simp [hr] ; exact hvr
      | recv src dst t mv =>
        simp only [brb] at htrans ; subst htrans
        intro q r w hsent
        -- recv doesn't change sent; extract old sent value
        have hold : (s.local_ q).sent r .vote w = true := by
          by_cases hq : q = dst
          · simp only [apply_ite LocalState.sent, hq] at hsent
            cases t <;> simp at hsent <;> split at hsent <;> simp_all
          · simp [hq] at hsent ; exact hsent
        rcases hi q r w hold with hbuf | hvr
        · -- buffer was true: check if this recv consumed our message
          by_cases hm : (⟨q, r, .vote, w⟩ : Message n Value) = ⟨src, dst, t, mv⟩
          · -- consumed: voteRecv updated
            obtain ⟨rfl, rfl, ht, rfl⟩ := Message.mk.inj hm
            right ; subst ht
            simp only [apply_ite LocalState.voteRecv]
            split
            · split <;> simp_all
            · rename_i h ; exact absurd trivial h
          · -- not consumed: buffer preserved
            left ; simp only [] ; rw [if_neg hm] ; exact hbuf
        · -- voteRecv was true: preserved through recv
          right ; by_cases hr : r = dst
          · simp only [apply_ite LocalState.voteRecv, hr]
            cases t <;> simp <;> split <;> simp_all
          · simp [hr] ; exact hvr
      | doReturn j mv =>
        simp only [brb] at htrans ; subst htrans
        intro q r w hsent
        have hold : (s.local_ q).sent r .vote w = true := by
          by_cases hq : q = j <;> simp_all
        rcases hi q r w hold with hbuf | hvr
        · left ; exact hbuf
        · right ; by_cases hr : r = j <;> simp_all)
    e hsafety

/-! ### Liveness: Totality

    If a correct process returns, all correct processes eventually return.

    The proof is decomposed into leads-to steps using weak fairness.
    Fairness is assumed on all non-corrupt actions (send, recv, doReturn).
-/

/-- The "fires" relation for a specific BRB action instance. -/
def brb_action (sender : Fin n) (val : Value) (a : Action n Value) :
    action (State n Value) :=
  (brb n f Value sender val).actions a |>.fires

/-- The overall next-state relation. -/
def brb_next (sender : Fin n) (val : Value) : action (State n Value) :=
  (brb n f Value sender val).next

/-- Weak fairness for BRB actions by correct processes.
    Corrupt processes have no fairness obligation.
    - Send: WF only for correct senders (not corrupt sends)
    - Recv/doReturn: WF for all processes -/
def brb_fairness (sender : Fin n) (val : Value) : pred (State n Value) :=
  fun e =>
    (∀ src dst t v, TLA.weak_fairness
      (fun s s' => isCorrect n Value s src ∧
        brb_action n f Value sender val (.send src dst t v) s s') e) ∧
    (∀ src dst t v, TLA.weak_fairness (brb_action n f Value sender val (.recv src dst t v)) e) ∧
    (∀ i v, TLA.weak_fairness (brb_action n f Value sender val (.doReturn i v)) e)

/-! #### Stability and monotonicity -/

/-- Stability of P ∨ ¬isCorrect(q): if P is stable under □⟨next⟩ and
    corruption is irreversible, then P ∨ ¬isCorrect(q) is stable. -/
theorem stable_or_corrupt (sender : Fin n) (val : Value)
    (q : Fin n) (P : State n Value → Prop)
    (hP : pred_implies
      (tla_and (state_pred P) [tlafml| □ ⟨(brb n f Value sender val).next⟩])
      [tlafml| □ ⌜ P ⌝]) :
    pred_implies
      (tla_and
        (state_pred (fun s => P s ∨ ¬isCorrect n Value s q))
        [tlafml| □ ⟨(brb n f Value sender val).next⟩])
      [tlafml| □ ⌜ fun s => P s ∨ ¬isCorrect n Value s q ⌝] := by
  intro e ⟨h0, hnext⟩ k
  rcases h0 with hP0 | hC0
  · left ; exact hP e ⟨hP0, hnext⟩ k
  · right ; induction k with
    | zero => exact hC0
    | succ k' ih =>
      simp only [isCorrect, always, action_pred, exec.drop,
        ActionSpec.next, GatedAction.fires] at hnext ih ⊢
      rw [show 0 + (k' + 1) = 1 + k' from by omega]
      obtain ⟨i, _, htrans⟩ := hnext k'
      cases i with
      | corrupt j =>
        simp only [brb] at htrans ; rw [htrans]
        exact fun habs => ih (fun hmem => habs (List.mem_cons_of_mem j hmem))
      | send src dst t mv =>
        simp only [brb] at htrans ; rw [htrans] ; exact ih
      | recv src dst t v' =>
        simp only [brb] at htrans ; rw [htrans] ; exact ih
      | doReturn j v' =>
        simp only [brb] at htrans ; rw [htrans] ; exact ih

/-- Corruption is irreversible: once a process is corrupt, it stays corrupt.
    Corollary of stable_or_corrupt with P = False. -/
theorem corrupt_persistent (sender : Fin n) (val : Value)
    (q : Fin n) :
    pred_implies
      (tla_and (state_pred (fun s => ¬isCorrect n Value s q))
        [tlafml| □ ⟨(brb n f Value sender val).next⟩])
      [tlafml| □ ⌜ fun s => ¬isCorrect n Value s q ⌝] := by
  intro e ⟨h0, hnext⟩ k
  have h := stable_or_corrupt n f Value sender val q (fun _ => False)
    (by intro e' ⟨h, _⟩ ; exact absurd h (by simp [state_pred]))
    e ⟨Or.inr h0, hnext⟩ k
  exact h.resolve_left (by simp)

/-- Stability: once ∀ x ∈ l, voteRecv(x,q,v) holds, it holds forever. -/
theorem voteRecv_list_stable (sender : Fin n) (val : Value)
    (q : Fin n) (v : Value) (l : List (Fin n)) :
    pred_implies
      (tla_and
        (state_pred (fun s => ∀ x ∈ l, (s.local_ x).voteRecv q v = true))
        [tlafml| □ ⟨(brb n f Value sender val).next⟩])
      [tlafml| □ ⌜ fun s => ∀ x ∈ l, (s.local_ x).voteRecv q v = true ⌝] := by
  intro e ⟨h0, hnext⟩
  simp only [always, action_pred, state_pred, exec.drop, ActionSpec.next,
    GatedAction.fires] at h0 hnext ⊢
  intro k
  induction k with
  | zero => exact h0
  | succ k' ih =>
    simp only [state_pred, exec.drop, Nat.zero_add] at ih ⊢
    rw [show k' + 1 = 1 + k' from by omega]
    obtain ⟨i, _, htrans⟩ := hnext k'
    intro x hx
    have hprev := ih x hx
    cases i with
    | corrupt j =>
      simp only [brb, Nat.zero_add] at htrans ; rw [htrans] ; exact hprev
    | send src dst t mv =>
      simp only [brb, Nat.zero_add] at htrans ; rw [htrans]
      by_cases hx : x = src <;> simp_all
    | recv src dst t mv =>
      simp only [brb, Nat.zero_add] at htrans ; rw [htrans]
      by_cases hx : x = dst
      · subst hx ; simp
        cases t <;> simp
        · split <;> simp_all
        · split <;> simp_all
        · by_cases hc : ((e k').local_ x).voteRecv src mv = false <;> simp [hc]
          · by_cases hsv : src = q ∧ mv = v <;> simp_all
          · exact hprev
      · simp_all
    | doReturn j mv =>
      simp only [brb, Nat.zero_add] at htrans ; rw [htrans]
      by_cases hx : x = j <;> simp_all

/-- Stability: once voted(q,v) = true, it stays true forever.
    Only the send.vote action modifies voted, and only to set entries to true. -/
theorem voted_stable (sender : Fin n) (val : Value)
    (q : Fin n) (v : Value) :
    pred_implies
      (tla_and
        (state_pred (fun s => (s.local_ q).voted v = true))
        [tlafml| □ ⟨(brb n f Value sender val).next⟩])
      [tlafml| □ ⌜ fun s => (s.local_ q).voted v = true ⌝] := by
  intro e ⟨h0, hnext⟩
  simp only [always, action_pred, state_pred, exec.drop, ActionSpec.next,
    GatedAction.fires] at h0 hnext ⊢
  intro k
  induction k with
  | zero => exact h0
  | succ k' ih =>
    simp only [state_pred, exec.drop, Nat.zero_add] at ih ⊢
    rw [show k' + 1 = 1 + k' from by omega]
    obtain ⟨i, _, htrans⟩ := hnext k'
    cases i with
    | corrupt j =>
      simp only [brb, Nat.zero_add] at htrans ; rw [htrans] ; exact ih
    | send src dst t mv =>
      simp only [brb, Nat.zero_add] at htrans ; rw [htrans]
      by_cases hq : q = src
      · cases t
        · simp_all  -- init: voted unchanged
        · simp_all  -- echo: voted unchanged
        · -- vote: voted may grow but doesn't shrink
          simp only [hq, ite_true]
          rw [hq] at ih
          by_cases hc : src ∈ (e k').corrupted <;> simp [hc]
          · exact ih  -- corrupted: voted unchanged
          · by_cases hv : v = mv <;> simp [hv, ih]
      · simp [hq] ; exact ih
    | recv src dst t mv =>
      simp only [brb, Nat.zero_add] at htrans ; rw [htrans]
      by_cases hq : q = dst
      · cases t <;> simp [hq] <;> split <;> simp_all
      · simp [hq] ; exact ih
    | doReturn j mv =>
      simp only [brb, Nat.zero_add] at htrans ; rw [htrans]
      by_cases hq : q = j <;> simp_all

/-- Stability: once sent(q,dst,t,v) = true, it stays true forever.
    Only the send action modifies sent, and only to set entries to true. -/
theorem sent_stable (sender : Fin n) (val : Value)
    (q : Fin n) (dst : Fin n) (t : MsgType) (v : Value) :
    pred_implies
      (tla_and
        (state_pred (fun s => (s.local_ q).sent dst t v = true))
        [tlafml| □ ⟨(brb n f Value sender val).next⟩])
      [tlafml| □ ⌜ fun s => (s.local_ q).sent dst t v = true ⌝] := by
  intro e ⟨h0, hnext⟩
  simp only [always, action_pred, state_pred, exec.drop, ActionSpec.next,
    GatedAction.fires] at h0 hnext ⊢
  intro k
  induction k with
  | zero => exact h0
  | succ k' ih =>
    simp only [state_pred, exec.drop, Nat.zero_add] at ih ⊢
    rw [show k' + 1 = 1 + k' from by omega]
    obtain ⟨i, _, htrans⟩ := hnext k'
    cases i with
    | corrupt j =>
      simp only [brb, Nat.zero_add] at htrans ; rw [htrans] ; exact ih
    | send src dst' t' mv =>
      simp only [brb, Nat.zero_add] at htrans ; rw [htrans]
      by_cases hq : q = src
      · rw [hq] at ih ; simp only [hq, ite_true]
        by_cases h : dst' = dst ∧ t' = t ∧ mv = v <;> simp [h, ih]
      · simp [hq] ; exact ih
    | recv src dst' t' mv =>
      simp only [brb, Nat.zero_add] at htrans ; rw [htrans]
      by_cases hq : q = dst'
      · cases t' <;> simp [hq] <;> split <;> simp_all
      · simp [hq] ; exact ih
    | doReturn j mv =>
      simp only [brb, Nat.zero_add] at htrans ; rw [htrans]
      by_cases hq : q = j <;> simp_all

/-- Stability: once returned(q) ≠ none, it stays non-none forever.
    Only the doReturn action modifies returned, setting it from none to some v. -/
theorem returned_stable (sender : Fin n) (val : Value)
    (q : Fin n) :
    pred_implies
      (tla_and
        (state_pred (fun s => (s.local_ q).returned ≠ none))
        [tlafml| □ ⟨(brb n f Value sender val).next⟩])
      [tlafml| □ ⌜ fun s => (s.local_ q).returned ≠ none ⌝] := by
  intro e ⟨h0, hnext⟩
  simp only [always, action_pred, state_pred, exec.drop, ActionSpec.next,
    GatedAction.fires] at h0 hnext ⊢
  intro k
  induction k with
  | zero => exact h0
  | succ k' ih =>
    simp only [state_pred, exec.drop, Nat.zero_add] at ih ⊢
    rw [show k' + 1 = 1 + k' from by omega]
    obtain ⟨i, _, htrans⟩ := hnext k'
    cases i with
    | corrupt j =>
      simp only [brb, Nat.zero_add] at htrans ; rw [htrans] ; exact ih
    | send src dst t mv =>
      simp only [brb, Nat.zero_add] at htrans ; rw [htrans]
      by_cases hq : q = src <;> simp_all
    | recv src dst t mv =>
      simp only [brb, Nat.zero_add] at htrans ; rw [htrans]
      by_cases hq : q = dst
      · cases t <;> simp [hq] <;> split <;> simp_all
      · simp [hq] ; exact ih
    | doReturn j mv =>
      simp only [brb, Nat.zero_add] at htrans ; rw [htrans]
      by_cases hq : q = j
      · simp [hq]
      · simp [hq] ; exact ih

/-- Stability: countVoteRecv is monotone — once ≥ threshold, stays ≥ threshold.
    Follows from voteRecv pointwise monotonicity (voteRecv_list_stable). -/
theorem countVoteRecv_stable (sender : Fin n) (val : Value)
    (q : Fin n) (v : Value) (threshold : Nat) :
    pred_implies
      (tla_and
        (state_pred (fun s => countVoteRecv n Value (s.local_ q) v ≥ threshold))
        [tlafml| □ ⟨(brb n f Value sender val).next⟩])
      [tlafml| □ ⌜ fun s => countVoteRecv n Value (s.local_ q) v ≥ threshold ⌝] := by
  intro e ⟨h0, hnext⟩
  simp only [always, action_pred, state_pred, exec.drop, ActionSpec.next,
    GatedAction.fires] at h0 hnext ⊢
  intro k
  induction k with
  | zero => exact h0
  | succ k' ih =>
    simp only [state_pred, exec.drop, Nat.zero_add] at ih ⊢
    rw [show k' + 1 = 1 + k' from by omega]
    obtain ⟨i, _, htrans⟩ := hnext k'
    -- It suffices to show voteRecv only grows pointwise, so the count doesn't decrease.
    apply Nat.le_trans ih
    simp only [countVoteRecv]
    apply filter_length_mono
    intro r hr
    -- Show: old voteRecv(q,r,v) = true → new voteRecv(q,r,v) = true
    cases i with
    | corrupt j =>
      simp only [brb, Nat.zero_add] at htrans ; rw [htrans] ; exact hr
    | send src dst t mv =>
      simp only [brb, Nat.zero_add] at htrans ; rw [htrans]
      by_cases hq : q = src <;> simp_all
    | recv src dst t mv =>
      simp only [brb, Nat.zero_add] at htrans ; rw [htrans]
      by_cases hq : q = dst
      · cases t
        · simp [hq] ; split <;> simp_all  -- init
        · simp [hq] ; split <;> simp_all  -- echo
        · -- vote: voteRecv may grow
          rw [hq] at hr
          by_cases hc : ((e k').local_ dst).voteRecv src mv = false <;> simp_all
      · simp [hq] ; exact hr
    | doReturn j mv =>
      simp only [brb, Nat.zero_add] at htrans ; rw [htrans]
      by_cases hq : q = j <;> simp_all

/-- Step-level corollary of voteRecv_list_stable: voteRecv(r,q,v) persists. -/
theorem voteRecv_persist (sender : Fin n) (val : Value)
    (e : exec (State n Value)) (hsafety : (brb n f Value sender val).safety e)
    (r q : Fin n) (v : Value) (j d : Nat) :
    ((exec.drop j e 0).local_ r).voteRecv q v = true →
    ((exec.drop (j + d) e 0).local_ r).voteRecv q v = true := by
  intro h
  have := voteRecv_list_stable n f Value sender val q v [r] (exec.drop j e)
    ⟨by simp [state_pred] ; exact h,
     by intro j' ; rw [exec.drop_drop] ; exact hsafety.2 _⟩ d
  simp only [state_pred, exec.drop_drop] at this
  exact this r (List.mem_singleton.mpr rfl)

/-- Step-level corollary of corrupt_persistent: ¬isCorrect persists. -/
theorem isCorrect_persist (sender : Fin n) (val : Value)
    (e : exec (State n Value)) (hsafety : (brb n f Value sender val).safety e)
    (q : Fin n) (j d : Nat) :
    ¬isCorrect n Value (exec.drop j e 0) q →
    ¬isCorrect n Value (exec.drop (j + d) e 0) q := by
  intro h
  have := corrupt_persistent n f Value sender val q (exec.drop j e)
    ⟨h, by intro j' ; rw [exec.drop_drop] ; exact hsafety.2 _⟩ d
  simp only [state_pred, exec.drop_drop] at this
  exact this

/-- Step-level corollary of countVoteRecv_stable: vote count threshold persists. -/
theorem countVoteRecv_persist (sender : Fin n) (val : Value)
    (e : exec (State n Value)) (hsafety : (brb n f Value sender val).safety e)
    (q : Fin n) (v : Value) (threshold : Nat) (j d : Nat) :
    countVoteRecv n Value ((exec.drop j e 0).local_ q) v ≥ threshold →
    countVoteRecv n Value ((exec.drop (j + d) e 0).local_ q) v ≥ threshold := by
  intro h
  have := countVoteRecv_stable n f Value sender val q v threshold (exec.drop j e)
    ⟨h, by intro j' ; rw [exec.drop_drop] ; exact hsafety.2 _⟩ d
  simp only [state_pred, exec.drop_drop] at this
  exact this

/-- Step-level corollary of voted_stable: voted(q,v) persists. -/
theorem voted_persist (sender : Fin n) (val : Value)
    (e : exec (State n Value)) (hsafety : (brb n f Value sender val).safety e)
    (q : Fin n) (v : Value) (j d : Nat) :
    ((exec.drop j e 0).local_ q).voted v = true →
    ((exec.drop (j + d) e 0).local_ q).voted v = true := by
  intro h
  have := voted_stable n f Value sender val q v (exec.drop j e)
    ⟨h, by intro j' ; rw [exec.drop_drop] ; exact hsafety.2 _⟩ d
  simp only [state_pred, exec.drop_drop] at this
  exact this

/-! #### Weak fairness proof obligations

    The four core WF applications. Each uses the wf1 rule to show that
    an enabled action eventually fires.

    1. `wf_vote_send`: voted → send vote (WF on correct send)
    2. `wf_vote_threshold_send`: f+1 votes → send vote (WF on correct send)
    3. `wf_return`: n-f votes → return (WF on doReturn)
    4. `wf_deliver`: message in buffer → received (WF on recv)
-/

/-- WF on correct send: if q voted v, then q eventually
    sends vote(v) to p. Uses WF on the correct send(q,p,.vote,v) action.
    The gate is enabled because voted(v) = true and sent = false. -/
theorem wf_vote_send (sender : Fin n) (val : Value)
    (q p : Fin n) (v : Value) :
    pred_implies
      (tla_and (brb n f Value sender val).safety
        (brb_fairness n f Value sender val))
      [tlafml|
        ⌜ fun s => (s.local_ q).voted v = true ⌝ ↝
        ⌜ fun s => (s.local_ q).sent p .vote v = true ∨ ¬isCorrect n Value s q ⌝] := by
  intro e ⟨hsafety, hfair⟩
  obtain ⟨hwf_send, _, _⟩ := hfair
  -- Fairness action: correct send(q, p, .vote, v)
  let a : action (State n Value) :=
    fun s s' => isCorrect n Value s q ∧
      brb_action n f Value sender val (.send q p .vote v) s s'
  exact wf1
    (state_pred (fun s => (s.local_ q).voted v = true))
    (state_pred (fun s => (s.local_ q).sent p .vote v = true ∨ ¬isCorrect n Value s q))
    ((brb n f Value sender val).next)
    a e
    ⟨by -- Persistence: p ∧ ⟨next⟩ ⇒ ◯p ∨ ◯q
        -- voted is stable under all actions, so ◯p always holds
        intro k ; dsimp only [tlasimp_def]
        intro ⟨hvoted, hnext_k⟩
        simp only [exec.drop, ActionSpec.next, GatedAction.fires, Nat.zero_add] at hvoted hnext_k ⊢
        obtain ⟨action, _, htrans⟩ := hnext_k
        cases action with
        | corrupt j =>
          simp only [brb] at htrans ; rw [htrans]
          by_cases hj : q = j
          · right ; right ; simp [isCorrect, hj]
          · left ; exact hvoted
        | send s d t mv =>
          left ; simp only [brb] at htrans ; rw [htrans]
          by_cases hq : q = s
          · cases t <;> simp_all
            -- .vote: voted may grow
            by_cases hc : s ∈ (e k).corrupted <;> simp [hc]
            · exact hvoted
            · by_cases hv : v = mv <;> simp [hv, hvoted]
          · simp [hq] ; exact hvoted
        | recv s d t mv =>
          left ; simp only [brb] at htrans ; rw [htrans]
          by_cases hq : q = d
          · simp only [apply_ite LocalState.voted, hq]
            cases t <;> simp <;> split <;> simp_all
          · simp [hq] ; exact hvoted
        | doReturn j mv =>
          left ; simp only [brb] at htrans ; rw [htrans]
          by_cases hq : q = j <;> simp_all,
     by -- Progress: p ∧ ⟨next⟩ ∧ ⟨a⟩ ⇒ ◯q
        -- When correct send(q,p,.vote,v) fires, sent becomes true
        intro k ; dsimp only [tlasimp_def]
        intro ⟨_, _, ha⟩
        simp only [exec.drop, Nat.zero_add] at ha ⊢
        obtain ⟨_, _, htrans⟩ := ha
        simp only [brb] at htrans ; rw [htrans]
        left ; simp,
     by -- Enabledness: p ⇒ Enabled a ∨ q
        intro k ; dsimp only [tlasimp_def]
        intro hvoted
        simp only [exec.drop, Nat.zero_add] at hvoted ⊢
        by_cases hsent : ((e k).local_ q).sent p .vote v = true
        · right ; left ; exact hsent
        · by_cases hcorr : isCorrect n Value (e k) q
          · left ; simp only [tla_enabled, enabled, state_pred, exec.drop, a,
              brb_action, GatedAction.fires, brb, isCorrect, Nat.zero_add]
            have hsent' : ((e k).local_ q).sent p .vote v = false := by
              cases h : ((e k).local_ q).sent p .vote v
              · rfl
              · exact absurd h hsent
            exact ⟨_, hcorr, Or.inr ⟨hcorr, hsent', Or.inl hvoted⟩, rfl⟩
          · right ; right ; exact hcorr,
     hsafety.2, hwf_send q p .vote v⟩

/-- WF on correct send (threshold): if q has ≥ f+1 votes for v, then q eventually sends vote(v) to p. The vote gate is
    enabled by the threshold (third disjunct), and the send also sets
    voted(v) = true for correct q. -/
theorem wf_vote_threshold_send (sender : Fin n) (val : Value)
    (q p : Fin n) (v : Value) :
    pred_implies
      (tla_and (brb n f Value sender val).safety
        (brb_fairness n f Value sender val))
      [tlafml|
        ⌜ fun s => countVoteRecv n Value (s.local_ q) v ≥ voteThreshold f ⌝ ↝
        ⌜ fun s => (s.local_ q).sent p .vote v = true ∨ ¬isCorrect n Value s q ⌝] := by
  intro e ⟨hsafety, hfair⟩
  obtain ⟨hwf_send, _, _⟩ := hfair
  let a : action (State n Value) :=
    fun s s' => isCorrect n Value s q ∧
      brb_action n f Value sender val (.send q p .vote v) s s'
  exact wf1
    (state_pred (fun s => countVoteRecv n Value (s.local_ q) v ≥ voteThreshold f))
    (state_pred (fun s => (s.local_ q).sent p .vote v = true ∨ ¬isCorrect n Value s q))
    ((brb n f Value sender val).next)
    a e
    ⟨by -- Persistence: countVoteRecv is monotone, so ◯p always holds
        intro k ; dsimp only [tlasimp_def]
        intro ⟨hcount, hnext_k⟩
        simp only [exec.drop, ActionSpec.next, GatedAction.fires, Nat.zero_add] at hcount hnext_k ⊢
        obtain ⟨action, _, htrans⟩ := hnext_k
        cases action with
        | corrupt j =>
          simp only [brb] at htrans ; rw [htrans]
          by_cases hj : q = j
          · right ; right ; simp [isCorrect, hj]
          · left ; exact hcount
        | send s d t mv =>
          left ; simp only [brb] at htrans ; rw [htrans]
          simp only [countVoteRecv] ; apply Nat.le_trans hcount
          apply filter_length_mono ; intro r hr
          by_cases hqr : q = s <;> simp_all
        | recv s d t mv =>
          left ; simp only [brb] at htrans ; rw [htrans]
          simp only [countVoteRecv] ; apply Nat.le_trans hcount
          apply filter_length_mono ; intro r hr
          by_cases hqr : q = d
          · simp only [apply_ite LocalState.voteRecv, hqr]
            cases t <;> simp <;> split <;> simp_all
          · simp_all
        | doReturn j mv =>
          simp only [brb] at htrans ; rw [htrans]
          by_cases hj : q = j
          · left ; rw [hj] at hcount
            simp only [hj, ite_true]
            simp only [countVoteRecv] ; exact hcount
          · left ; simp [hj] ; omega,
     by -- Progress: when correct send(q,p,.vote,v) fires, sent becomes true
        intro k ; dsimp only [tlasimp_def]
        intro ⟨_, _, ha⟩
        simp only [exec.drop, Nat.zero_add] at ha ⊢
        obtain ⟨_, _, htrans⟩ := ha
        simp only [brb] at htrans ; rw [htrans]
        left ; simp,
     by -- Enabledness: countVoteRecv ≥ f+1 ⇒ Enabled a ∨ q
        intro k ; dsimp only [tlasimp_def]
        intro hcount
        simp only [exec.drop, Nat.zero_add] at hcount ⊢
        by_cases hsent : ((e k).local_ q).sent p .vote v = true
        · right ; left ; exact hsent
        · by_cases hcorr : isCorrect n Value (e k) q
          · left ; simp only [tla_enabled, enabled, state_pred, exec.drop, a,
              brb_action, GatedAction.fires, brb, isCorrect, Nat.zero_add]
            have hsent' : ((e k).local_ q).sent p .vote v = false := by
              cases h : ((e k).local_ q).sent p .vote v
              · rfl
              · exact absurd h hsent
            -- gate: third disjunct (vote threshold)
            exact ⟨_, hcorr, Or.inr ⟨hcorr, hsent', Or.inr (Or.inr hcount)⟩, rfl⟩
          · right ; right ; exact hcorr,
     hsafety.2, hwf_send q p .vote v⟩

/-- WF on doReturn: if r has ≥ n-f votes for v, then r eventually returns.
    The doReturn gate requires isCorrect, returned = none, and the threshold. -/
theorem wf_return (sender : Fin n) (val : Value)
    (r : Fin n) (v : Value) :
    pred_implies
      (tla_and (brb n f Value sender val).safety
        (brb_fairness n f Value sender val))
      [tlafml|
        ⌜ fun s => countVoteRecv n Value (s.local_ r) v ≥ returnThreshold n f ⌝ ↝
        ⌜ fun s => (s.local_ r).returned ≠ none ∨ ¬isCorrect n Value s r ⌝] := by
  intro e ⟨hsafety, hfair⟩
  obtain ⟨_, _, hwf_ret⟩ := hfair
  exact wf1
    (state_pred (fun s => countVoteRecv n Value (s.local_ r) v ≥ returnThreshold n f))
    (state_pred (fun s => (s.local_ r).returned ≠ none ∨ ¬isCorrect n Value s r))
    ((brb n f Value sender val).next)
    (brb_action n f Value sender val (.doReturn r v))
    e
    ⟨by -- Persistence: p ∧ ⟨next⟩ ⇒ ◯p ∨ ◯q
        intro k ; dsimp only [tlasimp_def]
        intro ⟨hcount, hnext_k⟩
        simp only [exec.drop, ActionSpec.next, GatedAction.fires, Nat.zero_add] at hcount hnext_k ⊢
        obtain ⟨action, _, htrans⟩ := hnext_k
        cases action with
        | corrupt j =>
          simp only [brb] at htrans ; rw [htrans]
          by_cases hcr : r = j
          · right ; right ; simp [isCorrect, hcr]
          · left ; exact hcount
        | send s d t mv =>
          left ; simp only [brb] at htrans ; rw [htrans]
          simp only [countVoteRecv] ; apply Nat.le_trans hcount
          apply filter_length_mono ; intro q hq
          by_cases hqr : r = s <;> simp_all
        | recv s d t mv =>
          left ; simp only [brb] at htrans ; rw [htrans]
          simp only [countVoteRecv] ; apply Nat.le_trans hcount
          apply filter_length_mono ; intro q hq
          by_cases hqr : r = d
          · simp only [apply_ite LocalState.voteRecv, hqr]
            cases t <;> simp <;> split <;> simp_all
          · simp_all
        | doReturn j mv =>
          simp only [brb] at htrans ; rw [htrans]
          by_cases hj : r = j
          · right ; left ; simp [hj]
          · left ; simp [hj] ; omega,
     by -- Progress: p ∧ ⟨next⟩ ∧ ⟨a⟩ ⇒ ◯q
        intro k ; dsimp only [tlasimp_def]
        intro ⟨_, _, ha⟩
        simp only [exec.drop, brb_action, GatedAction.fires] at ha ⊢
        obtain ⟨_, htrans⟩ := ha
        simp only [brb] at htrans ; rw [htrans]
        left ; simp,
     by -- Enabledness: p ⇒ Enabled a ∨ q
        intro k ; dsimp only [tlasimp_def]
        intro hcount
        simp only [exec.drop] at hcount
        by_cases hret : ((exec.drop k e 0).local_ r).returned = none
        · by_cases hcorr : isCorrect n Value (exec.drop k e 0) r
          · -- isCorrect, returned = none, count ≥ threshold → action enabled
            left
            simp only [tla_enabled, enabled, state_pred, exec.drop,
              brb_action, GatedAction.fires, brb]
            exact ⟨_, ⟨hcorr, hret, hcount⟩, rfl⟩
          · right ; right ; exact hcorr
        · right ; left ; exact hret,
     hsafety.2, hwf_ret r v⟩

/-- WF on recv: if a vote message is in the buffer, it is eventually
    received. Uses WF on the recv(src,dst,.vote,v) action. -/
theorem wf_deliver (sender : Fin n) (val : Value)
    (src dst : Fin n) (v : Value) :
    pred_implies
      (tla_and (brb n f Value sender val).safety
        (brb_fairness n f Value sender val))
      [tlafml|
        ⌜ fun s => s.buffer ⟨src, dst, .vote, v⟩ = true ⌝ ↝
        ⌜ fun s => (s.local_ dst).voteRecv src v = true ⌝] := by
  intro e ⟨hsafety, hfair⟩
  obtain ⟨_, hwf_recv, _⟩ := hfair
  exact wf1
    (state_pred (fun s => s.buffer ⟨src, dst, .vote, v⟩ = true))
    (state_pred (fun s => (s.local_ dst).voteRecv src v = true))
    ((brb n f Value sender val).next)
    (brb_action n f Value sender val (.recv src dst .vote v))
    e
    ⟨by -- Persistence: p ∧ ⟨next⟩ ⇒ ◯p ∨ ◯q
        intro k ; dsimp only [tlasimp_def]
        intro ⟨hbuf, hnext_k⟩
        simp only [exec.drop, ActionSpec.next, GatedAction.fires] at hbuf hnext_k ⊢
        obtain ⟨action, _, htrans⟩ := hnext_k
        cases action with
        | corrupt j => left ; simp only [brb] at htrans ; rw [htrans] ; exact hbuf
        | send s d t mv => left ; simp only [brb] at htrans ; rw [htrans] ; dsimp ; simp_all
        | recv s d t mv =>
          simp only [brb] at htrans
          by_cases hm : (⟨s, d, t, mv⟩ : Message n Value) = ⟨src, dst, .vote, v⟩
          · right ; obtain ⟨rfl, rfl, rfl, rfl⟩ := Message.mk.inj hm
            rw [htrans] ; simp only [] ; split
            · -- outer isTrue: voteRecv was false, struct updated
              -- need to show updated voteRecv at (s, mv) = true
              -- updated voteRecv = fun q w => decide (q=s) && decide (w=mv) || old
              -- at (s, mv): decide (s=s) && decide (mv=mv) || old = true
              simp only [apply_ite LocalState.voteRecv]
              split
              · simp [and_self]
              · simp_all
            · -- outer isFalse: voteRecv was already true, state unchanged
              rename_i h ; cases ((e k).local_ d).voteRecv s mv <;> simp_all
          · left ; rw [htrans] ; simp only [] ; simp only [Ne.symm hm, ite_false] ; exact hbuf;
        | doReturn j mv => left ; simp only [brb] at htrans ; rw [htrans] ; exact hbuf,
     by -- Progress: p ∧ ⟨next⟩ ∧ ⟨a⟩ ⇒ ◯q
        intro k ; dsimp only [tlasimp_def]
        intro ⟨_, _, ha⟩
        simp only [exec.drop, brb_action, GatedAction.fires] at ha ⊢
        obtain ⟨_, htrans⟩ := ha
        simp only [brb] at htrans ; rw [htrans] ; simp ; split <;> simp_all,
     by -- Enabledness: p ⇒ Enabled a ∨ q
        intro k ; dsimp only [tlasimp_def]
        intro hbuf ; left
        simp only [tla_enabled, enabled, state_pred, exec.drop,
          brb_action, GatedAction.fires, brb] at ⊢
        exact ⟨_, hbuf, rfl⟩,
     hsafety.2, hwf_recv src dst .vote v⟩

/-! #### Chaining send + deliver

    Each chains a send WF step with vote_msg_tracking and wf_deliver
    to get end-to-end delivery: precondition ↝ voteRecv ∨ ¬isCorrect.
-/

/-- Vote delivery: if q voted v, then either r eventually receives the
    vote, or q gets corrupted.
    Chain: wf_vote_send(q,r) → vote_msg_tracking → wf_deliver(q,r).
    - If q is correct and hasn't sent yet: WF fires send, message enters buffer.
    - If q already sent: message is in buffer or already received (tracking).
    - Buffer message → received (wf_deliver).
    - If q gets corrupted: ¬isCorrect escape. -/
theorem vote_delivery (sender : Fin n) (val : Value)
    (q r : Fin n) (v : Value) :
    pred_implies
      (tla_and (brb n f Value sender val).safety
        (brb_fairness n f Value sender val))
      [tlafml|
        ⌜ fun s => (s.local_ q).voted v = true ⌝ ↝
        ⌜ fun s => (s.local_ r).voteRecv q v = true ∨ ¬isCorrect n Value s q ⌝] := by
  intro e ⟨hsafety, hfair⟩
  have hwf1 := wf_vote_send n f Value sender val q r v e ⟨hsafety, hfair⟩
  have hwf2 := wf_deliver n f Value sender val q r v e ⟨hsafety, hfair⟩
  have htrack := vote_msg_tracking n f Value sender val e hsafety
  intro k hvoted
  -- Step 1: voted → eventually sent ∨ ¬isCorrect
  obtain ⟨k1, hsent_or⟩ := hwf1 k hvoted
  rw [exec.drop_drop] at hsent_or
  rcases hsent_or with hsent | hcorr
  · -- Step 2: sent → buffer ∨ voteRecv (message tracking invariant)
    rcases htrack (k + k1) q r v hsent with hbuf | hvr
    · -- Step 3: buffer → eventually voteRecv (wf_deliver)
      obtain ⟨k2, hvr⟩ := hwf2 (k + k1) hbuf
      rw [exec.drop_drop] at hvr
      exact ⟨k1 + k2, by
        rw [exec.drop_drop, show k + (k1 + k2) = (k + k1) + k2 from by omega]
        exact Or.inl hvr⟩
    · exact ⟨k1, by rw [exec.drop_drop] ; exact Or.inl hvr⟩
  · exact ⟨k1, by rw [exec.drop_drop] ; exact Or.inr hcorr⟩

/-- Vote threshold delivery: if q has ≥ f+1 votes for v, then either r
    eventually receives a vote from q, or q gets corrupted.
    Chain: wf_vote_threshold_send(q,r) → vote_msg_tracking → wf_deliver(q,r).
    Same structure as vote_delivery but triggered by the vote threshold
    instead of an existing voted flag. -/
theorem vote_threshold_delivery (sender : Fin n) (val : Value)
    (q r : Fin n) (v : Value) :
    pred_implies
      (tla_and (brb n f Value sender val).safety
        (brb_fairness n f Value sender val))
      [tlafml|
        ⌜ fun s => countVoteRecv n Value (s.local_ q) v ≥ voteThreshold f ⌝ ↝
        ⌜ fun s => (s.local_ r).voteRecv q v = true ∨ ¬isCorrect n Value s q ⌝] := by
  intro e ⟨hsafety, hfair⟩
  have hwf1 := wf_vote_threshold_send n f Value sender val q r v e ⟨hsafety, hfair⟩
  have hwf2 := wf_deliver n f Value sender val q r v e ⟨hsafety, hfair⟩
  have htrack := vote_msg_tracking n f Value sender val e hsafety
  intro k hcount
  -- Step 1: threshold → eventually sent ∨ ¬isCorrect
  obtain ⟨k1, hsent_or⟩ := hwf1 k hcount
  rw [exec.drop_drop] at hsent_or
  rcases hsent_or with hsent | hcorr
  · -- Step 2: sent → buffer ∨ voteRecv (message tracking invariant)
    rcases htrack (k + k1) q r v hsent with hbuf | hvr
    · -- Step 3: buffer → eventually voteRecv (wf_deliver)
      obtain ⟨k2, hvr⟩ := hwf2 (k + k1) hbuf
      rw [exec.drop_drop] at hvr
      exact ⟨k1 + k2, by
        rw [exec.drop_drop, show k + (k1 + k2) = (k + k1) + k2 from by omega]
        exact Or.inl hvr⟩
    · exact ⟨k1, by rw [exec.drop_drop] ; exact Or.inl hvr⟩
  · exact ⟨k1, by rw [exec.drop_drop] ; exact Or.inr hcorr⟩

/-! #### Combining deliveries (multiple senders, one receiver)

    Each combination lemma takes a list P of processes and shows that if
    all of them satisfy a precondition at step k, then eventually all of
    them satisfy a postcondition (or got corrupted). Proved by induction
    on P using the corresponding chain lemma + monotonicity of voteRecv
    and irreversibility of corruption.
-/

/-- Combine vote deliveries: if every q in l voted v at step k, then
    eventually for every q in l, voteRecv(r,q,v) or ¬isCorrect(q).
    Also preserves any voteRecv already true at step k. -/
theorem combine_vote_delivery (sender : Fin n) (val : Value)
    (r : Fin n) (v : Value)
    (e : exec (State n Value)) (k : Nat)
    (hsafety : (brb n f Value sender val).safety e)
    (hfair : brb_fairness n f Value sender val e)
    (l : List (Fin n)) :
    ∃ kl,
      (∀ q ∈ l, ((exec.drop k e 0).local_ q).voted v = true →
        ((exec.drop (k + kl) e 0).local_ r).voteRecv q v = true
        ∨ ¬isCorrect n Value (exec.drop (k + kl) e 0) q) ∧
      (∀ q, ((exec.drop k e 0).local_ r).voteRecv q v = true →
        ((exec.drop (k + kl) e 0).local_ r).voteRecv q v = true) := by
  -- Main proof by induction on l
  induction l with
  | nil => exact ⟨0, fun _ h => absurd h (by simp), fun _ h => by simp at h ⊢ ; exact h⟩
  | cons q₀ l' ih =>
    obtain ⟨kl', hdel', hmono'⟩ := ih
    have hvd := vote_delivery n f Value sender val q₀ r v e ⟨hsafety, hfair⟩
    -- Split on whether voted(q₀) holds at step k
    by_cases hvq : ((exec.drop k e 0).local_ q₀).voted v = true
    · -- voted(q₀) at k → persists to k+kl' → vote_delivery gives k₀
      have hvq' := voted_persist n f Value sender val e hsafety q₀ v k kl' hvq
      obtain ⟨k₀, hq₀⟩ := hvd (k + kl') hvq'
      rw [exec.drop_drop] at hq₀
      refine ⟨kl' + k₀, fun q hq hvoted => ?_, fun q h => ?_⟩
      · -- Delivery for q ∈ q₀ :: l'
        rcases List.mem_cons.mp hq with rfl | hq'
        · -- q = q₀: result from vote_delivery at step k+kl'+k₀
          rw [show k + (kl' + k₀) = (k + kl') + k₀ from by omega] ; exact hq₀
        · -- q ∈ l': IH result at k+kl', extended to k+kl'+k₀
          rcases hdel' q hq' hvoted with hvr | hcorr
          · left ; rw [show k + (kl' + k₀) = (k + kl') + k₀ from by omega]
            exact voteRecv_persist n f Value sender val e hsafety r q v (k + kl') k₀ hvr
          · right ; rw [show k + (kl' + k₀) = (k + kl') + k₀ from by omega]
            exact isCorrect_persist n f Value sender val e hsafety q (k + kl') k₀ hcorr
      · -- Monotonicity: voteRecv at k → voteRecv at k+kl'+k₀
        rw [show k + (kl' + k₀) = (k + kl') + k₀ from by omega]
        exact voteRecv_persist n f Value sender val e hsafety r q v (k + kl') k₀ (hmono' q h)
    · -- voted(q₀) doesn't hold at k: vacuous for q₀, IH for l'
      exact ⟨kl', fun q hq hvoted => by
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact absurd hvoted hvq
        · exact hdel' q hq' hvoted, hmono'⟩

/-- Combine vote threshold deliveries: if every q in l has ≥ f+1 votes
    for v at step k, then eventually for every q in l, voteRecv(r,q,v)
    or ¬isCorrect(q). Also preserves existing voteRecv values. -/
theorem combine_vote_threshold_delivery (sender : Fin n) (val : Value)
    (r : Fin n) (v : Value)
    (e : exec (State n Value)) (k : Nat)
    (hsafety : (brb n f Value sender val).safety e)
    (hfair : brb_fairness n f Value sender val e)
    (l : List (Fin n)) :
    ∃ kl,
      (∀ q ∈ l, countVoteRecv n Value ((exec.drop k e 0).local_ q) v ≥ voteThreshold f →
        ((exec.drop (k + kl) e 0).local_ r).voteRecv q v = true
        ∨ ¬isCorrect n Value (exec.drop (k + kl) e 0) q) ∧
      (∀ q, ((exec.drop k e 0).local_ r).voteRecv q v = true →
        ((exec.drop (k + kl) e 0).local_ r).voteRecv q v = true) := by
  induction l with
  | nil => exact ⟨0, fun _ h => absurd h (by simp), fun _ h => by simp at h ⊢ ; exact h⟩
  | cons q₀ l' ih =>
    obtain ⟨kl', hdel', hmono'⟩ := ih
    have hvd := vote_threshold_delivery n f Value sender val q₀ r v e ⟨hsafety, hfair⟩
    by_cases hvq : countVoteRecv n Value ((exec.drop k e 0).local_ q₀) v ≥ voteThreshold f
    · -- countVoteRecv ≥ f+1 at k → persists to k+kl' → vote_threshold_delivery gives k₀
      have hvq' := countVoteRecv_persist n f Value sender val e hsafety q₀ v (voteThreshold f) k kl' hvq
      obtain ⟨k₀, hq₀⟩ := hvd (k + kl') hvq'
      rw [exec.drop_drop] at hq₀
      refine ⟨kl' + k₀, fun q hq hcount => ?_, fun q h => ?_⟩
      · rcases List.mem_cons.mp hq with rfl | hq'
        · rw [show k + (kl' + k₀) = (k + kl') + k₀ from by omega] ; exact hq₀
        · rcases hdel' q hq' hcount with hvr | hcorr
          · left ; rw [show k + (kl' + k₀) = (k + kl') + k₀ from by omega]
            exact voteRecv_persist n f Value sender val e hsafety r q v (k + kl') k₀ hvr
          · right ; rw [show k + (kl' + k₀) = (k + kl') + k₀ from by omega]
            exact isCorrect_persist n f Value sender val e hsafety q (k + kl') k₀ hcorr
      · rw [show k + (kl' + k₀) = (k + kl') + k₀ from by omega]
        exact voteRecv_persist n f Value sender val e hsafety r q v (k + kl') k₀ (hmono' q h)
    · exact ⟨kl', fun q hq hcount => by
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact absurd hcount hvq
        · exact hdel' q hq' hcount, hmono'⟩

/-- Combine returns: if every q in l has ≥ n-f votes for v at step k,
    then eventually every q in l has returned or got corrupted. -/
theorem combine_return (sender : Fin n) (val : Value)
    (v : Value)
    (e : exec (State n Value)) (k : Nat)
    (hsafety : (brb n f Value sender val).safety e)
    (hfair : brb_fairness n f Value sender val e)
    (l : List (Fin n)) :
    ∃ kl,
      ∀ q ∈ l, countVoteRecv n Value ((exec.drop k e 0).local_ q) v ≥ returnThreshold n f →
        ((exec.drop (k + kl) e 0).local_ q).returned ≠ none
        ∨ ¬isCorrect n Value (exec.drop (k + kl) e 0) q := by
  -- Helper: returned ≠ none persists from step j to step j+d
  have ret_persist : ∀ q' j d, ((exec.drop j e 0).local_ q').returned ≠ none →
      ((exec.drop (j + d) e 0).local_ q').returned ≠ none := by
    intro q' j d h
    have := returned_stable n f Value sender val q' (exec.drop j e)
      ⟨h, by intro j' ; rw [exec.drop_drop] ; exact hsafety.2 _⟩ d
    simp only [state_pred, exec.drop_drop] at this
    exact this
  induction l with
  | nil => exact ⟨0, fun _ h => absurd h (by simp)⟩
  | cons q₀ l' ih =>
    obtain ⟨kl', hdel'⟩ := ih
    have hwr := wf_return n f Value sender val q₀ v e ⟨hsafety, hfair⟩
    by_cases hvq : countVoteRecv n Value ((exec.drop k e 0).local_ q₀) v ≥ returnThreshold n f
    · -- count ≥ threshold at k → persists to k+kl' → wf_return gives k₀
      have hvq' := countVoteRecv_persist n f Value sender val e hsafety q₀ v (returnThreshold n f) k kl' hvq
      obtain ⟨k₀, hq₀⟩ := hwr (k + kl') hvq'
      rw [exec.drop_drop] at hq₀
      exact ⟨kl' + k₀, fun q hq hcount => by
        rcases List.mem_cons.mp hq with rfl | hq'
        · rw [show k + (kl' + k₀) = (k + kl') + k₀ from by omega] ; exact hq₀
        · rcases hdel' q hq' hcount with hret | hcorr
          · left ; rw [show k + (kl' + k₀) = (k + kl') + k₀ from by omega]
            exact ret_persist q (k + kl') k₀ hret
          · right ; rw [show k + (kl' + k₀) = (k + kl') + k₀ from by omega]
            exact isCorrect_persist n f Value sender val e hsafety q (k + kl') k₀ hcorr⟩
    · exact ⟨kl', fun q hq hcount => by
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact absurd hcount hvq
        · exact hdel' q hq' hcount⟩

/-! #### Multi-receiver delivery

    Combines single-receiver deliveries across all receivers. Given ≥ n−f
    vote sources, shows that every process eventually gets ≥ f+1 votes
    (or gets corrupted). Uses combine_vote_delivery per receiver, voteRecv
    monotonicity across receivers, and the counting argument.
-/

/-- Multi-receiver vote delivery: given ≥ n−f vote sources for v at step k,
    there exists k1 such that every process has ≥ f+1 votes for v or is
    corrupt at step k+k1.
    Proof: call combine_vote_delivery for each receiver, take the max offset,
    use voteRecv monotonicity (voteRecv_list_stable) to show earlier results
    persist, then apply the counting argument (filter_split + pigeonhole). -/
theorem combine_vote_delivery_all_receivers (sender : Fin n) (val : Value) (hn : n > 3 * f)
    (p : Fin n) (v : Value)
    (e : exec (State n Value)) (k : Nat)
    (hsafety : (brb n f Value sender val).safety e)
    (hfair : brb_fairness n f Value sender val e)
    (hvback : countVoteRecv n Value ((exec.drop k e 0).local_ p) v ≥ returnThreshold n f) :
    ∃ k1,
      ∀ q, countVoteRecv n Value ((exec.drop (k + k1) e 0).local_ q) v ≥ voteThreshold f
        ∨ ¬isCorrect n Value (exec.drop (k + k1) e 0) q := by
  -- Reduce ∀ q to ∀ q ∈ finRange n via List.mem_finRange
  suffices h : ∃ k1, ∀ q ∈ List.finRange n,
      countVoteRecv n Value ((exec.drop (k + k1) e 0).local_ q) v ≥ voteThreshold f
      ∨ ¬isCorrect n Value (exec.drop (k + k1) e 0) q from by
    obtain ⟨k1, h⟩ := h ; exact ⟨k1, fun q => h q (List.mem_finRange q)⟩
  -- Induction on the list of receivers
  induction (List.finRange n) with
  | nil => exact ⟨0, fun _ h => absurd h (by simp)⟩
  | cons r receivers ih =>
    obtain ⟨k1', hall'⟩ := ih
    -- Step 1: Get the invariant at step k+k1' (vote trace + budget)
    have hinv := init_invariant
      (brb_inv_init n f Value sender val)
      (fun s s' hn' hi => brb_inv_step n f Value sender val hn s s' hn' hi)
      e hsafety
    obtain ⟨hbudget', _, _, hvtrace', _, _, _, _, _, _⟩ := hinv (k + k1')
    -- hvtrace': correct source q with voteRecv(p,q,v) at step k+k1' has voted(q,v)
    -- hbudget': |corrupted| ≤ f at step k+k1'
    -- Step 2: Apply combine_vote_delivery for receiver r at step k+k1'
    -- Need: vote sources still have voteRecv at p at step k+k1' (by voteRecv_persist)
    have hvback' := countVoteRecv_persist n f Value sender val e hsafety p v
      (returnThreshold n f) k k1' hvback
    obtain ⟨k₀, hdel_r, hmono_r⟩ :=
      combine_vote_delivery n f Value sender val r v e (k + k1') hsafety hfair (List.finRange n)
    -- hdel_r: ∀ q ∈ finRange n, voted(q,v) at k+k1' → voteRecv(r,q,v) ∨ ¬isCorrect(q) at k+k1'+k₀
    -- hmono_r: voteRecv at k+k1' preserved at k+k1'+k₀
    -- Step 3: Counting argument → r has ≥ f+1 votes at step k+k1'+k₀
    have hf1_r : countVoteRecv n Value ((exec.drop ((k + k1') + k₀) e 0).local_ r) v ≥ voteThreshold f := by
      let sk := exec.drop (k + k1') e 0    -- state at step k+k1'
      let sk' := exec.drop ((k + k1') + k₀) e 0  -- state at step k+k1'+k₀
      let P : Fin n → Bool := fun q => (sk.local_ p).voteRecv q v    -- sources at p
      let A : Fin n → Bool := fun q => (sk'.local_ r).voteRecv q v   -- received at r
      let B : Fin n → Bool := fun q => decide (q ∈ sk'.corrupted)    -- corrupt
      -- Fact 1: |filter P| ≥ n - f
      have h1 : ((List.finRange n).filter P).length ≥ n - f := hvback'
      -- Fact 2: P q → A q ∨ B q
      have h2 : ∀ q, P q = true → A q = true ∨ B q = true := by
        intro q hPq
        by_cases hcq : isCorrect n Value sk q
        · have hvoted_q := hvtrace' p q v hcq hPq
          rcases hdel_r q (List.mem_finRange q) hvoted_q with hvr | hc
          · left ; exact hvr
          · right ; simp only [B, decide_eq_true_eq, isCorrect] at hc ⊢
            exact Classical.not_not.mp hc
        · right ; simp only [B, decide_eq_true_eq]
          have := isCorrect_persist n f Value sender val e hsafety q (k + k1') k₀ hcq
          simp only [isCorrect, Classical.not_not] at this ; exact this
      -- Fact 3: |filter B| ≤ f
      obtain ⟨hbudget_k, _⟩ := hinv ((k + k1') + k₀)
      have h3 : ((List.finRange n).filter B).length ≤ f := by
        calc ((List.finRange n).filter B).length
            ≤ sk'.corrupted.length := by
              apply nodup_sub_length ((finRange_nodup n).sublist List.filter_sublist)
              intro x hx ; simp [B, List.mem_filter] at hx ; exact hx
          _ ≤ f := hbudget_k
      -- Counting: |filter A| ≥ n - 2f ≥ f + 1
      have hsplit := filter_split P A (List.finRange n)
      have hbound : ((List.finRange n).filter (fun x => P x && !A x)).length ≤ f := by
        calc ((List.finRange n).filter (fun x => P x && !A x)).length
            ≤ ((List.finRange n).filter B).length := by
              apply filter_length_mono
              intro q hq ; simp at hq
              rcases h2 q hq.1 with ha | hb
              · simp [hq.2] at ha
              · exact hb
          _ ≤ f := h3
      show countVoteRecv n Value (sk'.local_ r) v ≥ voteThreshold f
      unfold countVoteRecv voteThreshold
      change ((List.finRange n).filter A).length ≥ f + 1
      have : ((List.finRange n).filter (fun x => P x && A x)).length ≥ n - 2 * f := by omega
      have hfA := filter_and_le P A (List.finRange n)
      omega
    -- Step 4: Assemble result with kl = k1' + k₀
    refine ⟨k1' + k₀, fun q hq => ?_⟩
    rcases List.mem_cons.mp hq with rfl | hq'
    · -- q = r: use hf1_r
      left ; rw [show k + (k1' + k₀) = (k + k1') + k₀ from by omega] ; exact hf1_r
    · -- q ∈ receivers: IH result at k+k1', extended to k+k1'+k₀
      rcases hall' q hq' with hcount | hcorr
      · left ; rw [show k + (k1' + k₀) = (k + k1') + k₀ from by omega]
        exact countVoteRecv_persist n f Value sender val e hsafety q v (voteThreshold f) (k + k1') k₀ hcount
      · right ; rw [show k + (k1' + k₀) = (k + k1') + k₀ from by omega]
        exact isCorrect_persist n f Value sender val e hsafety q (k + k1') k₀ hcorr

/-! #### Totality

    The main liveness theorem: if some process returned, all correct
    processes eventually return. Combines all the previous results.
-/

/-- Totality: if some process returned v, then every process eventually
    returns or gets corrupted.
    Proof:
    1. p returned v → n-f vote sources (invariant, vote backing)
    2. combine_vote_delivery_all_receivers: all processes get ≥ f+1 votes or corrupt
    3. combine_vote_threshold_delivery: each process with f+1 votes delivers to r
    4. Counting: at most f corrupt among n → r gets ≥ n-f votes
    5. wf_return: r returns or gets corrupted -/
theorem totality (sender : Fin n) (val : Value) (hn : n > 3 * f)
    (r : Fin n) (v : Value) :
    pred_implies
      (tla_and (brb n f Value sender val).safety
        (brb_fairness n f Value sender val))
      [tlafml|
        ⌜ fun s => ∃ p, (s.local_ p).returned = some v ⌝ ↝
        ⌜ fun s => (s.local_ r).returned ≠ none ∨ ¬isCorrect n Value s r ⌝] := by
  intro e ⟨hsafety, hfair⟩
  have hinv := init_invariant
    (brb_inv_init n f Value sender val)
    (fun s s' hn' hi => brb_inv_step n f Value sender val hn s s' hn' hi)
    e hsafety
  unfold TLA.leads_to always eventually
  intro k ⟨p, hpret⟩
  -- Step 1: p returned v → n-f vote sources
  obtain ⟨_, _, _, _, _, _, hvback, _, _, _⟩ := hinv k
  have hvotes_p := hvback p v hpret

  -- Step 2: Multi-receiver delivery → all processes get f+1 votes or corrupt
  obtain ⟨k1, hall_f1⟩ :=
    combine_vote_delivery_all_receivers n f Value sender val hn p v e k hsafety hfair hvotes_p

  -- Step 3: combine_vote_threshold_delivery for receiver r at step k+k1
  obtain ⟨k2, hdel2, _⟩ :=
    combine_vote_threshold_delivery n f Value sender val r v e (k + k1) hsafety hfair
      (List.finRange n)

  -- Step 4: Counting → r has ≥ n-f votes at step k+k1+k2
  --   At step k+k1, ∀ q, q has f+1 votes ∨ corrupt.
  --   After combine_vote_threshold_delivery, each with f+1 delivers to r or got corrupt.
  --   Corrupt at k+k1 persists to k+k1+k2.
  --   So ∀ q, voteRecv(r,q,v) ∨ ¬isCorrect(q) at k+k1+k2.
  --   At most f corrupt → ≥ n-f delivered → countVoteRecv(r,v) ≥ n-f.
  have hnf : countVoteRecv n Value ((exec.drop (k + k1 + k2) e 0).local_ r) v ≥
      returnThreshold n f
      ∨ ¬isCorrect n Value (exec.drop (k + k1 + k2) e 0) r := by
    left
    let sk12 := exec.drop (k + k1 + k2) e 0
    let A : Fin n → Bool := fun q => (sk12.local_ r).voteRecv q v
    let B : Fin n → Bool := fun q => decide (q ∈ sk12.corrupted)
    -- ∀ q, A q ∨ B q (each process delivered or corrupt)
    have hab : ∀ q, A q = true ∨ B q = true := by
      intro q
      rcases hall_f1 q with hf1 | hcorrupt
      · -- q had f+1 at k+k1 → delivered or corrupt at k+k1+k2
        rcases hdel2 q (List.mem_finRange q) hf1 with hvr | hc
        · left ; exact hvr
        · right ; simp only [B, decide_eq_true_eq, isCorrect] at hc ⊢
          exact Classical.not_not.mp hc
      · -- q corrupt at k+k1 → still corrupt at k+k1+k2
        right ; simp only [B, decide_eq_true_eq]
        have hcp := corrupt_persistent n f Value sender val q (exec.drop (k + k1) e)
          ⟨hcorrupt, by intro j ; rw [exec.drop_drop] ; exact hsafety.2 _⟩ k2
        have : ¬isCorrect n Value (exec.drop k2 (exec.drop (k + k1) e) 0) q := hcp
        simp only [exec.drop, isCorrect, Classical.not_not] at this
        rw [show 0 + k2 + (k + k1) = 0 + (k + k1 + k2) from by omega] at this
        exact this
    -- |filter B| ≤ f
    obtain ⟨hbudget12, _⟩ := hinv (k + k1 + k2)
    have hB : ((List.finRange n).filter B).length ≤ f := by
      calc ((List.finRange n).filter B).length
          ≤ sk12.corrupted.length := by
            apply nodup_sub_length ((finRange_nodup n).sublist List.filter_sublist)
            intro x hx ; simp [B, List.mem_filter] at hx ; exact hx
        _ ≤ f := hbudget12
    -- |filter ¬A| ≤ f (since ¬A → B)
    have hnotA : ((List.finRange n).filter (fun x => !A x)).length ≤ f := by
      calc ((List.finRange n).filter (fun x => !A x)).length
          ≤ ((List.finRange n).filter B).length := by
            apply filter_length_mono
            intro q hq
            rcases hab q with ha | hb
            · simp [ha] at hq
            · exact hb
        _ ≤ f := hB
    -- |filter A| + |filter ¬A| = n → |filter A| ≥ n - f
    have hsplit : ∀ (l : List (Fin n)), l.length =
        (l.filter A).length + (l.filter (fun x => !A x)).length := by
      intro l ; induction l with
      | nil => simp
      | cons a t ih => simp only [List.filter_cons] ; cases A a <;> simp <;> omega
    show countVoteRecv n Value (sk12.local_ r) v ≥ returnThreshold n f
    unfold countVoteRecv returnThreshold
    change ((List.finRange n).filter A).length ≥ n - f
    have hlen := hsplit (List.finRange n)
    have hfin : (List.finRange n).length = n := List.length_finRange
    omega

  -- Step 5: wf_return → r returns or gets corrupted
  rcases hnf with hnf_votes | hcorrupt
  · have hret := wf_return n f Value sender val r v e ⟨hsafety, hfair⟩
    unfold TLA.leads_to always eventually at hret
    obtain ⟨k3, hk3⟩ := hret (k + k1 + k2) hnf_votes
    exact ⟨k1 + k2 + k3, by
      simp only [exec.drop_drop] at hk3 ⊢
      rw [show k + k1 + k2 + k3 = k + (k1 + k2 + k3) from by omega] at hk3
      exact hk3⟩
  · exact ⟨k1 + k2, by
      simp only [exec.drop_drop] at hcorrupt ⊢
      rw [show k + k1 + k2 = k + (k1 + k2) from by omega] at hcorrupt
      exact Or.inr hcorrupt⟩

end ByzantineReliableBroadcast
