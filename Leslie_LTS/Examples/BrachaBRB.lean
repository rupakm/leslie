import Leslie_LTS.Framework
import Leslie_LTS.Examples.UtilityByzantine

/-! # Byzantine Reliable Broadcast (Bracha) — LTS Formulation

  Bracha's BRB for `n` processes with at most `f` Byzantine faults (`n > 3f`).
-/

open LTS

namespace BRB_LTS

/-! ### Messages -/

/-- The three types of protocol messages. -/
inductive MsgType where
  | init | echo | vote
  deriving DecidableEq

/-- A protocol message: source, destination, type, and carried value. -/
structure Message (n : Nat) (Value : Type) where
  src : Fin n
  dst : Fin n
  type : MsgType
  val : Value
  deriving DecidableEq

/-! ### Local State -/

/-- Per-process local state. -/
structure LocalState (n : Nat) (Value : Type) where
  /-- The value this process will broadcast (only meaningful for the sender). -/
  broadcastVal : Option Value
  /-- `sent dst t v = true` iff this process has sent message (t, v) to dst. -/
  sent : Fin n → MsgType → Value → Bool
  /-- Value received via SEND from the designated sender (at most one). -/
  sendRecv : Option Value
  /-- Received ECHO(v) from process j. -/
  echoRecv : Fin n → Value → Bool
  /-- Received VOTE(v) from process j. -/
  voteRecv : Fin n → Value → Bool
  /-- Value echoed (at most one). -/
  echoed : Option Value
  /-- `voted v = true` iff this process has voted for value v. -/
  voted : Value → Bool
  /-- Value returned (at most one). -/
  returned : Option Value

/-! ### Global State -/

/-- The global system state. -/
structure State (n : Nat) (Value : Type) where
  /-- Per-process local state. -/
  local_ : Fin n → LocalState n Value
  /-- Network buffer: pending messages in transit. -/
  buffer : Message n Value → Bool
  /-- List of corrupted (Byzantine) processes. -/
  corrupted : List (Fin n)

/-! ### Labels (Actions) -/

/-- The labels of the BRB LTS. -/
inductive Label (n : Nat) (Value : Type) where
  /-- The adversary corrupts a process. -/
  | corrupt (i : Fin n)
  /-- Process `src` sends a message of type `t` with value `v` to `dst`. -/
  | send (src dst : Fin n) (t : MsgType) (v : Value)
  /-- Process `dst` receives a message of type `t` with value `v` from `src`. -/
  | recv (src dst : Fin n) (t : MsgType) (v : Value)
  /-- Correct process `i` returns value `v`. -/
  | output (i : Fin n) (v : Value)
  /-- The environment sets the broadcast value for process `i`. -/
  | input (i : Fin n) (v : Value)

instance {Value : Type} [Inhabited (Fin n)] [Inhabited Value] : Inhabited (Label n Value) :=
  ⟨.send default default .init default⟩

/-! ### Helpers -/

variable (n f : Nat) (Value : Type) [DecidableEq Value]

/-- A process is correct if it has not been corrupted. -/
def isCorrect (s : State n Value) (p : Fin n) : Prop := p ∉ s.corrupted

/-- Count of distinct sources from which ECHO(v) was received. -/
def countEchoRecv (ls : LocalState n Value) (v : Value) : Nat :=
  (List.finRange n).filter (ls.echoRecv · v) |>.length

/-- Count of distinct sources from which VOTE(v) was received. -/
def countVoteRecv (ls : LocalState n Value) (v : Value) : Nat :=
  (List.finRange n).filter (ls.voteRecv · v) |>.length

/-- Threshold for echoes: n − f. -/
def echoThreshold : Nat := n - f

/-- Threshold for vote amplification: f + 1. -/
def voteThreshold : Nat := f + 1

/-- Threshold for returning: n − f. -/
def returnThreshold : Nat := n - f

/-- Default initial local state: everything empty/none. -/
def LocalState.init : LocalState n Value where
  broadcastVal := none
  sent := fun _ _ _ => false
  sendRecv := none
  echoRecv := fun _ _ => false
  voteRecv := fun _ _ => false
  echoed := none
  voted := fun _ => false
  returned := none

/-! ### The BRB System as an LTS -/

/-- The BRB system as a labelled transition system. -/
def brb (sender : Fin n) : System (State n Value) (Label n Value) where
  init := fun s =>
    (∀ p, s.local_ p = LocalState.init n Value) ∧
    (∀ m, s.buffer m = false) ∧
    s.corrupted = []
  step := fun s lbl s' =>
    match lbl with
    | .corrupt i =>
        isCorrect n Value s i ∧
        s.corrupted.length + 1 ≤ f ∧
        s' = { s with corrupted := i :: s.corrupted }
    | .input i v =>
        i = sender ∧
        (s.local_ sender).broadcastVal = none ∧
        s' = { s with
          local_ := fun p => if p = sender
            then { s.local_ sender with broadcastVal := some v }
            else s.local_ p }
    | .send src dst t mv =>
        (src ∈ s.corrupted ∨
         (isCorrect n Value s src ∧ (s.local_ src).sent dst t mv = false ∧
           match t with
           | .init => src = sender ∧ (s.local_ src).broadcastVal = some mv
           | .echo =>
             (s.local_ src).echoed = some mv
             ∨ ((s.local_ src).echoed = none ∧ (s.local_ src).sendRecv = some mv)
           | .vote =>
             (s.local_ src).voted mv = true ∨
             countEchoRecv n Value (s.local_ src) mv ≥ echoThreshold n f ∨
             countVoteRecv n Value (s.local_ src) mv ≥ voteThreshold f)) ∧
        let msg : Message n Value := ⟨src, dst, t, mv⟩
        s' = { s with
          buffer := fun m => if m = msg then true else s.buffer m
          local_ := fun p => if p = src then
            { s.local_ src with
              sent := fun d t' w => if d = dst ∧ t' = t ∧ w = mv then true
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
        s.buffer ⟨src, dst, t, mv⟩ = true ∧
        let msg : Message n Value := ⟨src, dst, t, mv⟩
        let ls := s.local_ dst
        s' = { s with
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
                echoRecv := fun q w => if q = src ∧ w = mv then true
                  else ls.echoRecv q w }
              else ls
            | .vote =>
              if ls.voteRecv src mv = false
              then { ls with
                voteRecv := fun q w => if q = src ∧ w = mv then true
                  else ls.voteRecv q w }
              else ls
            else s.local_ p }
    | .output i mv =>
        isCorrect n Value s i ∧
        (s.local_ i).returned = none ∧
        countVoteRecv n Value (s.local_ i) mv ≥ returnThreshold n f ∧
        s' = { s with
          local_ := fun p => if p = i
            then { s.local_ i with returned := some mv }
            else s.local_ p }

/-! ### Internal / External Labelling -/

/-- `corrupt`, `input`, `output` are external; `send`, `recv` are internal. -/
def brb_labelling [Inhabited (Fin n)] [Inhabited Value] : Labelling (Label n Value) where
  is_internal := fun l =>
    match l with
    | .corrupt _ => false
    | .send .. => true
    | .recv .. => true
    | .output _ _ => false
    | .input _ _ => false
  tau := .send default default .init default
  tau_internal := rfl

/-! ### Safety Properties (label-based)

    Properties are expressed purely in terms of the observable label
    trace, without inspecting internal state. -/

/-- Validity: if sender is never corrupted, outputs match sender input. -/
def validity (sender : Fin n) : TraceProp (State n Value) (Label n Value) :=
  fun e _pos =>
    (∀ k, e.labels k ≠ .corrupt sender) →
    ∀ k i v, e.labels k = .output i v →
      ∃ k', e.labels k' = .input sender v

/-- **Agreement** (label-based): all output values in the trace agree. -/
def agreement : TraceProp (State n Value) (Label n Value) :=
  fun e _pos => ∀ k₁ k₂ p q vp vq,
    e.labels k₁ = .output p vp →
    e.labels k₂ = .output q vq →
    vp = vq

/-! ### Projection Lemmas

    These lemmas extract field equalities from the step relation,
    avoiding the need to substitute with large structure literals. -/

section mechanical_helpers
variable {n f : Nat} {Value : Type} [DecidableEq Value]

/-- For any step, the local state of a process `p` that is NOT the "affected"
    process of the transition is entirely unchanged. The affected process is:
    - `src` for send, `dst` for recv, `i` for output/input, nobody for corrupt.
    This subsumes many per-field projections. -/
theorem step_local_other {s s' : State n Value} {l : Label n Value} {sender : Fin n}
    (h : (brb n f Value sender).step s l s') (p : Fin n)
    (hp : match l with
      | .send src _ _ _ => p ≠ src
      | .recv _ dst _ _ => p ≠ dst
      | .output i _ => p ≠ i
      | .input i _ => p ≠ i
      | .corrupt _ => True) :
    s'.local_ p = s.local_ p := by
  match l with
  | .corrupt _ => obtain ⟨_, _, rfl⟩ := h; rfl
  | .send src _ _ _ => obtain ⟨_, rfl⟩ := h; simp [hp]
  | .recv _ dst _ _ => obtain ⟨_, rfl⟩ := h; simp [hp]
  | .output i _ => obtain ⟨_, _, _, rfl⟩ := h; simp [hp]
  | .input i _ =>
    obtain ⟨rfl, _, rfl⟩ := h; simp [hp]


/-- Correct in post-state implies correct in pre-state. -/
theorem step_correct_prev {s s' : State n Value} {l : Label n Value} {sender : Fin n}
    (hstep : (brb n f Value sender).step s l s')
    (p : Fin n) (hp : isCorrect n Value s' p) :
    isCorrect n Value s p := by
  match l with
  | .corrupt i =>
    obtain ⟨_, _, rfl⟩ := hstep
    simp only [isCorrect, List.mem_cons, not_or] at hp ⊢; exact hp.2
  | .send .. => obtain ⟨_, rfl⟩ := hstep; exact hp
  | .recv .. => obtain ⟨_, rfl⟩ := hstep; exact hp
  | .output .. => obtain ⟨_, _, _, rfl⟩ := hstep; exact hp
  | .input i _ =>
    obtain ⟨rfl, _, rfl⟩ := hstep; exact hp

theorem corrupt_corrupted {s s' : State n Value} {i} {sender : Fin n}
    (h : (brb n f Value sender).step s (.corrupt i) s') :
    s'.corrupted = i :: s.corrupted := by
  obtain ⟨_, _, rfl⟩ := h; rfl

theorem corrupt_local {s s' : State n Value} {i} {sender : Fin n}
    (h : (brb n f Value sender).step s (.corrupt i) s') (p : Fin n) :
    s'.local_ p = s.local_ p := by
  obtain ⟨_, _, rfl⟩ := h; rfl

theorem corrupt_isCorrect {s s' : State n Value} {i} {sender : Fin n}
    (h : (brb n f Value sender).step s (.corrupt i) s') :
    isCorrect n Value s i := by
  obtain ⟨hc, _, _⟩ := h; exact hc

theorem corrupt_budget {s s' : State n Value} {i} {sender : Fin n}
    (h : (brb n f Value sender).step s (.corrupt i) s') :
    s.corrupted.length + 1 ≤ f := by
  obtain ⟨_, hb, _⟩ := h; exact hb


theorem recv_init_corrupted {s s' : State n Value} {src dst v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.recv src dst .init v) s') :
    s'.corrupted = s.corrupted := by
  obtain ⟨_, rfl⟩ := h; rfl

theorem recv_init_returned {s s' : State n Value} {src dst v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.recv src dst .init v) s') (p : Fin n) :
    (s'.local_ p).returned = (s.local_ p).returned := by
  obtain ⟨_, rfl⟩ := h; simp; by_cases hp : p = dst <;> simp [hp]
  by_cases hc : src = sender ∧ (s.local_ dst).sendRecv = none <;> simp [hc]

theorem recv_init_broadcastVal {s s' : State n Value} {src dst v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.recv src dst .init v) s') (p : Fin n) :
    (s'.local_ p).broadcastVal = (s.local_ p).broadcastVal := by
  obtain ⟨_, rfl⟩ := h; simp; by_cases hp : p = dst <;> simp [hp]
  by_cases hc : src = sender ∧ (s.local_ dst).sendRecv = none <;> simp [hc]

theorem recv_init_sendRecv_some {s s' : State n Value} {src dst v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.recv src dst .init v) s')
    (p : Fin n) (w : Value) (hw : (s.local_ p).sendRecv = some w) :
    (s'.local_ p).sendRecv = some w := by
  obtain ⟨_, hs'⟩ := h; subst hs'; simp only
  by_cases heq : p = dst
  · subst heq; simp only
    by_cases hcond : src = sender ∧ (s.local_ p).sendRecv = none
    · rw [hw] at hcond; exact absurd hcond.2 (by simp)
    · simp only [hcond]; exact hw
  · simp only [heq]; exact hw

theorem recv_init_sendRecv_other {s s' : State n Value} {src dst v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.recv src dst .init v) s')
    (p : Fin n) (w : Value) (hw : w ≠ v)
    (hw' : (s'.local_ p).sendRecv = some w) :
    (s.local_ p).sendRecv = some w := by
  obtain ⟨_, hs'⟩ := h; subst hs'; simp only at hw'
  by_cases heq : p = dst
  · subst heq; simp only at hw'
    by_cases hcond : src = sender ∧ (s.local_ p).sendRecv = none
    · simp [hcond] at hw'; exact absurd hw'.symm hw
    · simp only [hcond] at hw'; exact hw'
  · simp only [heq] at hw'; exact hw'

/-- If `recv init v` sets `sendRecv` of `dst`, then `src = sender` and `p = dst`. -/
theorem recv_init_src_eq_sender {s s' : State n Value} {src dst v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.recv src dst .init v) s')
    (p : Fin n)
    (hbefore : (s.local_ p).sendRecv = none)
    (hafter : (s'.local_ p).sendRecv = some v) :
    src = sender ∧ p = dst := by
  obtain ⟨_, hs'⟩ := h; subst hs'; simp only at hafter
  by_cases heq : p = dst
  · subst heq; simp only at hafter
    by_cases hcond : src = sender ∧ (s.local_ p).sendRecv = none
    · exact ⟨hcond.1, rfl⟩
    · simp only [↓reduceIte, hcond] at hafter; rw [hafter] at hbefore; contradiction
  · simp only [heq, ↓reduceIte] at hafter; rw [hafter] at hbefore; contradiction


theorem send_corrupted {s s' : State n Value} {src dst t v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.send src dst t v) s') :
    s'.corrupted = s.corrupted := by
  obtain ⟨_, rfl⟩ := h; rfl

theorem send_returned {s s' : State n Value} {src dst t v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.send src dst t v) s') (p : Fin n) :
    (s'.local_ p).returned = (s.local_ p).returned := by
  obtain ⟨_, rfl⟩ := h; simp; by_cases hp : p = src <;> simp [hp]

theorem send_sendRecv {s s' : State n Value} {src dst t v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.send src dst t v) s') (p : Fin n) :
    (s'.local_ p).sendRecv = (s.local_ p).sendRecv := by
  obtain ⟨_, rfl⟩ := h; simp; by_cases hp : p = src <;> simp [hp]

theorem send_broadcastVal {s s' : State n Value} {src dst t v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.send src dst t v) s') (p : Fin n) :
    (s'.local_ p).broadcastVal = (s.local_ p).broadcastVal := by
  obtain ⟨_, rfl⟩ := h; simp; by_cases hp : p = src <;> simp [hp]


theorem recv_echo_corrupted {s s' : State n Value} {src dst v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.recv src dst .echo v) s') :
    s'.corrupted = s.corrupted := by
  obtain ⟨_, rfl⟩ := h; rfl

theorem recv_echo_returned {s s' : State n Value} {src dst v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.recv src dst .echo v) s') (p : Fin n) :
    (s'.local_ p).returned = (s.local_ p).returned := by
  obtain ⟨_, rfl⟩ := h; simp; by_cases hp : p = dst <;> simp [hp]
  by_cases hc : (s.local_ dst).echoRecv src v = false <;> simp [hc]

theorem recv_echo_sendRecv {s s' : State n Value} {src dst v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.recv src dst .echo v) s') (p : Fin n) :
    (s'.local_ p).sendRecv = (s.local_ p).sendRecv := by
  obtain ⟨_, rfl⟩ := h; simp; by_cases hp : p = dst <;> simp [hp]
  by_cases hc : (s.local_ dst).echoRecv src v = false <;> simp [hc]

theorem recv_echo_broadcastVal {s s' : State n Value} {src dst v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.recv src dst .echo v) s') (p : Fin n) :
    (s'.local_ p).broadcastVal = (s.local_ p).broadcastVal := by
  obtain ⟨_, rfl⟩ := h; simp; by_cases hp : p = dst <;> simp [hp]
  by_cases hc : (s.local_ dst).echoRecv src v = false <;> simp [hc]


theorem recv_vote_corrupted {s s' : State n Value} {src dst v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.recv src dst .vote v) s') :
    s'.corrupted = s.corrupted := by
  obtain ⟨_, rfl⟩ := h; rfl

theorem recv_vote_returned {s s' : State n Value} {src dst v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.recv src dst .vote v) s') (p : Fin n) :
    (s'.local_ p).returned = (s.local_ p).returned := by
  obtain ⟨_, rfl⟩ := h; simp; by_cases hp : p = dst <;> simp [hp]
  by_cases hc : (s.local_ dst).voteRecv src v = false <;> simp [hc]

theorem recv_vote_sendRecv {s s' : State n Value} {src dst v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.recv src dst .vote v) s') (p : Fin n) :
    (s'.local_ p).sendRecv = (s.local_ p).sendRecv := by
  obtain ⟨_, rfl⟩ := h; simp; by_cases hp : p = dst <;> simp [hp]
  by_cases hc : (s.local_ dst).voteRecv src v = false <;> simp [hc]

theorem recv_vote_broadcastVal {s s' : State n Value} {src dst v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.recv src dst .vote v) s') (p : Fin n) :
    (s'.local_ p).broadcastVal = (s.local_ p).broadcastVal := by
  obtain ⟨_, rfl⟩ := h; simp; by_cases hp : p = dst <;> simp [hp]
  by_cases hc : (s.local_ dst).voteRecv src v = false <;> simp [hc]


theorem input_corrupted {s s' : State n Value} {i v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.input i v) s') :
    s'.corrupted = s.corrupted := by
  obtain ⟨_, _, rfl⟩ := h; rfl

theorem input_eq_sender {s s' : State n Value} {i v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.input i v) s') :
    i = sender :=
  h.1

theorem input_returned {s s' : State n Value} {i v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.input i v) s') (p : Fin n) :
    (s'.local_ p).returned = (s.local_ p).returned := by
  have := input_eq_sender h; subst this
  obtain ⟨_, _, rfl⟩ := h; simp; by_cases hp : p = i <;> simp [hp]

theorem input_sendRecv {s s' : State n Value} {i v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.input i v) s') (p : Fin n) :
    (s'.local_ p).sendRecv = (s.local_ p).sendRecv := by
  have := input_eq_sender h; subst this
  obtain ⟨_, _, rfl⟩ := h; simp; by_cases hp : p = i <;> simp [hp]

theorem input_broadcastVal {s s' : State n Value} {i v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.input i v) s') :
    (s'.local_ sender).broadcastVal = some v := by
  have := input_eq_sender h; subst this
  obtain ⟨_, _, rfl⟩ := h; simp


theorem output_corrupted {s s' : State n Value} {i v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.output i v) s') :
    s'.corrupted = s.corrupted := by
  obtain ⟨_, _, _, rfl⟩ := h; rfl

/-- `output i v` sets `returned i := some v` and preserves `returned p` for `p ≠ i`. -/
theorem output_returned {s s' : State n Value} {i v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.output i v) s') (p : Fin n) :
    (s'.local_ p).returned = if p = i then some v else (s.local_ p).returned := by
  obtain ⟨_, _, _, rfl⟩ := h; simp; by_cases hp : p = i <;> simp [hp]

/-- `output` preserves `sendRecv` for all processes. -/
theorem output_sendRecv {s s' : State n Value} {i v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.output i v) s') (p : Fin n) :
    (s'.local_ p).sendRecv = (s.local_ p).sendRecv := by
  obtain ⟨_, _, _, rfl⟩ := h; simp; by_cases hp : p = i <;> simp [hp]

/-- `output` preserves `broadcastVal` for all processes. -/
theorem output_broadcastVal {s s' : State n Value} {i v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.output i v) s') (p : Fin n) :
    (s'.local_ p).broadcastVal = (s.local_ p).broadcastVal := by
  obtain ⟨_, _, _, rfl⟩ := h; simp; by_cases hp : p = i <;> simp [hp]


/-- After a `send`, a message is in the buffer iff it was just sent or was already there. -/
theorem send_buffer {s s' : State n Value} {src dst t v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.send src dst t v) s') (m : Message n Value) :
    s'.buffer m = true → m = ⟨src, dst, t, v⟩ ∨ s.buffer m = true := by
  obtain ⟨_, rfl⟩ := h; simp

/-- `recv init` only removes the consumed message from the buffer. -/
theorem recv_init_buffer {s s' : State n Value} {src dst v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.recv src dst .init v) s') (m : Message n Value) :
    s'.buffer m = true → m ≠ ⟨src, dst, .init, v⟩ ∧ s.buffer m = true := by
  obtain ⟨_, rfl⟩ := h; simp

/-- `recv echo` only removes the consumed message from the buffer. -/
theorem recv_echo_buffer {s s' : State n Value} {src dst v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.recv src dst .echo v) s') (m : Message n Value) :
    s'.buffer m = true → m ≠ ⟨src, dst, .echo, v⟩ ∧ s.buffer m = true := by
  obtain ⟨_, rfl⟩ := h; simp

/-- `recv vote` only removes the consumed message from the buffer. -/
theorem recv_vote_buffer {s s' : State n Value} {src dst v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.recv src dst .vote v) s') (m : Message n Value) :
    s'.buffer m = true → m ≠ ⟨src, dst, .vote, v⟩ ∧ s.buffer m = true := by
  obtain ⟨_, rfl⟩ := h; simp

/-- `corrupt` preserves the buffer. -/
theorem corrupt_buffer {s s' : State n Value} {i} {sender : Fin n}
    (h : (brb n f Value sender).step s (.corrupt i) s') (m : Message n Value) :
    s'.buffer m = s.buffer m := by
  obtain ⟨_, _, rfl⟩ := h; rfl

/-- `output` preserves the buffer. -/
theorem output_buffer {s s' : State n Value} {i v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.output i v) s') (m : Message n Value) :
    s'.buffer m = s.buffer m := by
  obtain ⟨_, _, _, rfl⟩ := h; rfl

/-- `input` preserves the buffer. -/
theorem input_buffer {s s' : State n Value} {i v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.input i v) s') (m : Message n Value) :
    s'.buffer m = s.buffer m := by
  have := input_eq_sender h; subst this
  obtain ⟨_, _, rfl⟩ := h; rfl

/-! #### Unified mechanical helpers

    These merge all the per-label helpers into one lemma per field.
    Each lemma does a `match` on the label internally. -/

/-- `corrupted` is unchanged by all non-corrupt labels. For corrupt, it grows by one. -/
theorem step_corrupted {s s' : State n Value} {l : Label n Value} {sender : Fin n}
    (h : (brb n f Value sender).step s l s') :
    s'.corrupted = match l with
      | .corrupt i => i :: s.corrupted
      | _ => s.corrupted := by
  match l with
  | .corrupt _ => obtain ⟨_, _, rfl⟩ := h; rfl
  | .send .. => obtain ⟨_, rfl⟩ := h; rfl
  | .recv .. => obtain ⟨_, rfl⟩ := h; rfl
  | .output .. => obtain ⟨_, _, _, rfl⟩ := h; rfl
  | .input _ _ => have := input_eq_sender h; subst this; obtain ⟨_, _, rfl⟩ := h; rfl

/-- `returned p` is unchanged by all non-output labels. For output, only process `i` changes. -/
theorem step_returned {s s' : State n Value} {l : Label n Value} {sender : Fin n}
    (h : (brb n f Value sender).step s l s') (p : Fin n)
    (hl : ∀ i v, l = .output i v → p ≠ i) :
    (s'.local_ p).returned = (s.local_ p).returned := by
  match l with
  | .corrupt _ => obtain ⟨_, _, rfl⟩ := h; rfl
  | .send src .. => exact (send_returned h p)
  | .recv _ _ .init _ => exact (recv_init_returned h p)
  | .recv _ _ .echo _ => exact (recv_echo_returned h p)
  | .recv _ _ .vote _ => exact (recv_vote_returned h p)
  | .output i v =>
    have hne := hl i v rfl
    obtain ⟨_, _, _, rfl⟩ := h; simp [hne]
  | .input _ _ => exact (input_returned h p)

/-- `sendRecv p` is unchanged by all non-recv-init labels. -/
theorem step_sendRecv {s s' : State n Value} {l : Label n Value} {sender : Fin n}
    (h : (brb n f Value sender).step s l s') (p : Fin n)
    (hl : ∀ src dst v, l ≠ .recv src dst .init v) :
    (s'.local_ p).sendRecv = (s.local_ p).sendRecv := by
  match l with
  | .corrupt _ => obtain ⟨_, _, rfl⟩ := h; rfl
  | .send .. => exact (send_sendRecv h p)
  | .recv _ _ .init _ => exact absurd rfl (hl _ _ _)
  | .recv _ _ .echo _ => exact (recv_echo_sendRecv h p)
  | .recv _ _ .vote _ => exact (recv_vote_sendRecv h p)
  | .output .. => exact (output_sendRecv h p)
  | .input .. => exact (input_sendRecv h p)

/-- `broadcastVal p` is unchanged by all non-input labels. -/
theorem step_broadcastVal {s s' : State n Value} {l : Label n Value} {sender : Fin n}
    (h : (brb n f Value sender).step s l s') (p : Fin n)
    (hl : ∀ i v, l ≠ .input i v) :
    (s'.local_ p).broadcastVal = (s.local_ p).broadcastVal := by
  match l with
  | .corrupt _ => obtain ⟨_, _, rfl⟩ := h; rfl
  | .send .. => exact (send_broadcastVal h p)
  | .recv _ _ .init _ => exact (recv_init_broadcastVal h p)
  | .recv _ _ .echo _ => exact (recv_echo_broadcastVal h p)
  | .recv _ _ .vote _ => exact (recv_vote_broadcastVal h p)
  | .output .. => exact (output_broadcastVal h p)
  | .input _ _ => exact absurd rfl (hl _ _)

/-- Buffer is unchanged by corrupt, output, input. For send it adds, for recv it removes. -/
theorem step_buffer_preserved {s s' : State n Value} {l : Label n Value} {sender : Fin n}
    (h : (brb n f Value sender).step s l s') (m : Message n Value)
    (hl : (∀ src dst t v, l ≠ .send src dst t v) ∧ (∀ src dst t v, l ≠ .recv src dst t v)) :
    s'.buffer m = s.buffer m := by
  match l with
  | .corrupt _ => exact (corrupt_buffer h m)
  | .send .. => exact absurd rfl (hl.1 _ _ _ _)
  | .recv .. => exact absurd rfl (hl.2 _ _ _ _)
  | .output .. => exact (output_buffer h m)
  | .input .. => exact (input_buffer h m)

/-- `voted p v` is monotone across steps. -/
theorem step_voted {s s' : State n Value} {l : Label n Value} {sender : Fin n}
    (h : (brb n f Value sender).step s l s')
    (p : Fin n) (v : Value)
    (hvoted : (s.local_ p).voted v = true) :
    (s'.local_ p).voted v = true := by
  match l with
  | .corrupt _ => obtain ⟨_, _, rfl⟩ := h; exact hvoted
  | .send src dst t mv =>
    obtain ⟨_, rfl⟩ := h; simp only
    by_cases hp : p = src <;> simp only [hp]
    · subst hp; match t with
      | .init | .echo => exact hvoted
      | .vote =>
        by_cases hcorr : p ∈ s.corrupted <;> simp only [hcorr]
        · exact hvoted
        · by_cases hv : v = mv <;> simp [hv, hvoted]
    · exact hvoted
  | .recv src dst .init _ =>
    obtain ⟨_, rfl⟩ := h; simp only
    by_cases hp : p = dst <;> simp only [hp]
    · by_cases hc : (src : Fin n) = sender ∧ (s.local_ dst).sendRecv = none
      · simp only [hc]; rw [← hp]; exact hvoted
      · simp only [hc]; rw [← hp]; exact hvoted
    · exact hvoted
  | .recv src dst .echo mv =>
    obtain ⟨_, rfl⟩ := h; simp only
    by_cases hp : p = dst <;> simp only [hp]
    · subst hp
      by_cases hc : (s.local_ p).echoRecv src mv = false
      · simp only [hc]; exact hvoted
      · simp only [hc]; exact hvoted
    · exact hvoted
  | .recv src dst .vote mv =>
    obtain ⟨_, rfl⟩ := h; simp only
    by_cases hp : p = dst <;> simp only [hp]
    · subst hp
      by_cases hc : (s.local_ p).voteRecv src mv = false
      · simp only [hc]; exact hvoted
      · simp only [hc]; exact hvoted
    · exact hvoted
  | .output i _ =>
    obtain ⟨_, _, _, rfl⟩ := h; simp only
    by_cases hp : p = i <;> simp only [hp]
    · subst hp; exact hvoted
    · exact hvoted
  | .input i _ =>
    have := input_eq_sender h; subst this
    obtain ⟨_, _, rfl⟩ := h; simp only
    by_cases hp : p = i <;> simp only [hp]
    · subst hp; exact hvoted
    · exact hvoted

/-- `voted p v` traced to previous state when step is not `send vote v` by `p`. -/
theorem step_voted_prev {s s' : State n Value} {l : Label n Value} {sender : Fin n}
    (h : (brb n f Value sender).step s l s')
    (p : Fin n) (v : Value)
    (hvoted : (s'.local_ p).voted v = true)
    (hl : ∀ dst, l ≠ .send p dst .vote v) :
    (s.local_ p).voted v = true := by
  match l with
  | .corrupt _ => obtain ⟨_, _, rfl⟩ := h; exact hvoted
  | .send src dst t mv =>
    obtain ⟨_, rfl⟩ := h; simp only at hvoted
    by_cases hp : p = src <;> simp only [hp] at hvoted
    · subst hp; match t with
      | .init | .echo => exact hvoted
      | .vote =>
        by_cases hcorr : p ∈ s.corrupted <;> simp only [hcorr] at hvoted
        · exact hvoted
        · by_cases hv : v = mv
          · subst hv; exact absurd rfl (hl dst)
          · simp only [↓reduceIte, Bool.if_true_left, Bool.decide_and, not_false_eq_true, hv,
            decide_false, Bool.false_or] at hvoted; exact hvoted
    · exact hvoted
  | .recv src dst .init _ =>
    obtain ⟨_, rfl⟩ := h; simp only at hvoted
    by_cases hp : p = dst <;> simp only [hp] at hvoted
    · subst hp
      by_cases hc : (src : Fin n) = sender ∧ (s.local_ p).sendRecv = none
      · simp only [hc] at hvoted; exact hvoted
      · simp only [hc] at hvoted; exact hvoted
    · exact hvoted
  | .recv src dst .echo mv =>
    obtain ⟨_, rfl⟩ := h; simp only at hvoted
    by_cases hp : p = dst <;> simp only [hp] at hvoted
    · subst hp
      by_cases hc : (s.local_ p).echoRecv src mv = false
      · simp only [hc] at hvoted; exact hvoted
      · simp only [hc] at hvoted; exact hvoted
    · exact hvoted
  | .recv src dst .vote mv =>
    obtain ⟨_, rfl⟩ := h; simp only at hvoted
    by_cases hp : p = dst <;> simp only [hp] at hvoted
    · subst hp
      by_cases hc : (s.local_ p).voteRecv src mv = false
      · simp only [hc] at hvoted; exact hvoted
      · simp only [hc] at hvoted; exact hvoted
    · exact hvoted
  | .output i _ =>
    obtain ⟨_, _, _, rfl⟩ := h; simp only at hvoted
    by_cases hp : p = i <;> simp only [hp] at hvoted
    · subst hp; exact hvoted
    · exact hvoted
  | .input i _ =>
    have := input_eq_sender h; subst this
    obtain ⟨_, _, rfl⟩ := h; simp only at hvoted
    by_cases hp : p = i <;> simp only [hp] at hvoted
    · subst hp; exact hvoted
    · exact hvoted

/-- `echoRecv p q v` is monotone: if true before a step, still true after. -/
theorem step_echoRecv {s s' : State n Value} {l : Label n Value} {sender : Fin n}
    (h : (brb n f Value sender).step s l s')
    (p q : Fin n) (v : Value)
    (hrecv : (s.local_ p).echoRecv q v = true) :
    (s'.local_ p).echoRecv q v = true := by
  match l with
  | .corrupt _ => obtain ⟨_, _, rfl⟩ := h; exact hrecv
  | .send src _ _ _ =>
    obtain ⟨_, rfl⟩ := h; simp only
    by_cases hp : p = src <;> simp only [hp]
    · subst hp; exact hrecv
    · exact hrecv
  | .recv src dst .init _ =>
    obtain ⟨_, rfl⟩ := h; simp only
    by_cases hp : p = dst <;> simp only [hp]
    · subst hp
      by_cases hc : (src : Fin n) = sender ∧ (s.local_ p).sendRecv = none
      · simp only [hc]; exact hrecv
      · simp only [hc]; exact hrecv
    · exact hrecv
  | .recv src dst .echo mv =>
    obtain ⟨_, rfl⟩ := h; simp only
    by_cases hp : p = dst <;> simp only [hp]
    · subst hp
      by_cases hc : (s.local_ p).echoRecv src mv = false
      · simp only [hc]; by_cases hqv : q = src ∧ v = mv
        · simp [hqv]
        · simp only [↓reduceIte, Bool.if_true_left, Bool.decide_and, Bool.or_eq_true,
          Bool.and_eq_true, decide_eq_true_eq, hqv, false_or]; exact hrecv
      · simp only [hc]; exact hrecv
    · exact hrecv
  | .recv src dst .vote mv =>
    obtain ⟨_, rfl⟩ := h; simp only
    by_cases hp : p = dst <;> simp only [hp]
    · subst hp
      by_cases hc : (s.local_ p).voteRecv src mv = false
      · simp only [hc]; exact hrecv
      · simp only [hc]; exact hrecv
    · exact hrecv
  | .output i _ =>
    obtain ⟨_, _, _, rfl⟩ := h; simp only
    by_cases hp : p = i <;> simp only [hp]
    · subst hp; exact hrecv
    · exact hrecv
  | .input i _ =>
    have := input_eq_sender h; subst this
    obtain ⟨_, _, rfl⟩ := h; simp only
    by_cases hp : p = i <;> simp only [hp]
    · subst hp; exact hrecv
    · exact hrecv

/-- `echoed p` is monotone across steps. -/
theorem step_echoed {s s' : State n Value} {l : Label n Value} {sender : Fin n}
    (h : (brb n f Value sender).step s l s')
    (p : Fin n) (v : Value)
    (hechoed : (s.local_ p).echoed = some v) :
    (s'.local_ p).echoed = some v := by
  match l with
  | .corrupt _ => obtain ⟨_, _, rfl⟩ := h; exact hechoed
  | .send src _ t _ =>
    have hstep' := h
    obtain ⟨hgate, rfl⟩ := h; simp only
    by_cases hp : p = src <;> simp only [hp]
    · subst hp; match t with
      | .init | .vote => exact hechoed
      | .echo =>
        by_cases hcorr : p ∈ s.corrupted <;> simp only [↓reduceIte, Bool.if_true_left,
          Bool.decide_and, hcorr, not_false_eq_true, Option.some.injEq]
        · exact hechoed
        · rcases hgate with hbyz | ⟨_, _, hecho_reason⟩
          · exact absurd hbyz hcorr
          · rcases hecho_reason with hev | ⟨hnone, _⟩
            · rw [hechoed] at hev; exact (Option.some.inj hev).symm
            · rw [hechoed] at hnone; exact absurd hnone (by simp)
    · exact hechoed
  | .recv src dst .init mv =>
    obtain ⟨_, rfl⟩ := h; simp only
    by_cases hp : p = dst <;> simp only [hp]
    · subst hp
      by_cases hc : src = sender ∧ (s.local_ p).sendRecv = none
      · simp only [hc]; exact hechoed
      · simp only [hc]; exact hechoed
    · exact hechoed
  | .recv src dst .echo mv =>
    obtain ⟨_, rfl⟩ := h; simp only
    by_cases hp : p = dst <;> simp only [hp]
    · subst hp
      by_cases hc : (s.local_ p).echoRecv src mv = false
      · simp only [hc]; exact hechoed
      · simp only [hc]; exact hechoed
    · exact hechoed
  | .recv src dst .vote mv =>
    obtain ⟨_, rfl⟩ := h; simp only
    by_cases hp : p = dst <;> simp only [hp]
    · subst hp
      by_cases hc : (s.local_ p).voteRecv src mv = false
      · simp only [hc]; exact hechoed
      · simp only [hc]; exact hechoed
    · exact hechoed
  | .output i _ =>
    obtain ⟨_, _, _, rfl⟩ := h; simp only
    by_cases hp : p = i <;> simp only [hp]
    · subst hp; exact hechoed
    · exact hechoed
  | .input i _ =>
    have := input_eq_sender h; subst this
    obtain ⟨_, _, rfl⟩ := h; simp only
    by_cases hp : p = i <;> simp only [hp]
    · subst hp; exact hechoed
    · exact hechoed

/-- `echoRecv p q v` traced to previous state when step is not matching `recv echo`. -/
theorem step_echoRecv_prev {s s' : State n Value} {l : Label n Value} {sender : Fin n}
    (h : (brb n f Value sender).step s l s')
    (p q : Fin n) (v : Value)
    (hrecv : (s'.local_ p).echoRecv q v = true)
    (hl : ∀ src dst mv, l = .recv src dst .echo mv → ¬(p = dst ∧ q = src ∧ v = mv)) :
    (s.local_ p).echoRecv q v = true := by
  match l with
  | .corrupt _ => obtain ⟨_, _, rfl⟩ := h; exact hrecv
  | .send src _ _ _ =>
    obtain ⟨_, rfl⟩ := h; simp only at hrecv
    by_cases hp : p = src <;> simp only [hp] at hrecv
    · subst hp; exact hrecv
    · exact hrecv
  | .recv src dst .echo mv =>
    obtain ⟨_, rfl⟩ := h; simp only at hrecv
    by_cases hp : p = dst <;> simp only [hp] at hrecv
    · subst hp
      by_cases hc : (s.local_ p).echoRecv src mv = false
      · simp only [hc] at hrecv
        by_cases hqv : q = src ∧ v = mv
        · exact (hl src p mv rfl ⟨rfl, hqv.1, hqv.2⟩).elim
        · simp only [↓reduceIte, Bool.if_true_left, Bool.decide_and, Bool.or_eq_true,
          Bool.and_eq_true, decide_eq_true_eq, hqv, false_or] at hrecv; exact hrecv
      · simp only [hc] at hrecv; exact hrecv
    · exact hrecv
  | .recv src dst .init _ =>
    obtain ⟨_, rfl⟩ := h; simp only at hrecv
    by_cases hp : p = dst <;> simp only [hp] at hrecv
    · subst hp
      by_cases hc : src = sender ∧ (s.local_ p).sendRecv = none
      · simp only [hc] at hrecv; exact hrecv
      · simp only [hc] at hrecv; exact hrecv
    · exact hrecv
  | .recv src dst .vote mv =>
    obtain ⟨_, rfl⟩ := h; simp only at hrecv
    by_cases hp : p = dst <;> simp only [hp] at hrecv
    · subst hp
      by_cases hc : (s.local_ p).voteRecv src mv = false
      · simp only [hc] at hrecv; exact hrecv
      · simp only [hc] at hrecv; exact hrecv
    · exact hrecv
  | .output i _ =>
    obtain ⟨_, _, _, rfl⟩ := h; simp only at hrecv
    by_cases hp : p = i <;> simp only [hp] at hrecv
    · subst hp; exact hrecv
    · exact hrecv
  | .input i _ =>
    have := input_eq_sender h; subst this
    obtain ⟨_, _, rfl⟩ := h; simp only at hrecv
    by_cases hp : p = i <;> simp only [hp] at hrecv
    · subst hp; exact hrecv
    · exact hrecv

/-- `voteRecv p q v` traced to previous state when step is not matching `recv vote`. -/
theorem step_voteRecv_prev {s s' : State n Value} {l : Label n Value} {sender : Fin n}
    (h : (brb n f Value sender).step s l s')
    (p q : Fin n) (v : Value)
    (hrecv : (s'.local_ p).voteRecv q v = true)
    (hl : ∀ src dst mv, l = .recv src dst .vote mv → ¬(p = dst ∧ q = src ∧ v = mv)) :
    (s.local_ p).voteRecv q v = true := by
  match l with
  | .corrupt _ => obtain ⟨_, _, rfl⟩ := h; exact hrecv
  | .send src _ _ _ =>
    obtain ⟨_, rfl⟩ := h; simp only at hrecv
    by_cases hp : p = src <;> simp only [hp] at hrecv
    · subst hp; exact hrecv
    · exact hrecv
  | .recv src dst .vote mv =>
    obtain ⟨_, rfl⟩ := h; simp only at hrecv
    by_cases hp : p = dst <;> simp only [hp] at hrecv
    · subst hp
      by_cases hc : (s.local_ p).voteRecv src mv = false
      · simp only [hc] at hrecv
        by_cases hqv : q = src ∧ v = mv
        · exact (hl src p mv rfl ⟨rfl, hqv.1, hqv.2⟩).elim
        · simp only [↓reduceIte, Bool.if_true_left, Bool.decide_and, Bool.or_eq_true,
          Bool.and_eq_true, decide_eq_true_eq, hqv, false_or] at hrecv; exact hrecv
      · simp only [hc] at hrecv; exact hrecv
    · exact hrecv
  | .recv src dst .init _ =>
    obtain ⟨_, rfl⟩ := h; simp only at hrecv
    by_cases hp : p = dst <;> simp only [hp] at hrecv
    · subst hp
      by_cases hc : src = sender ∧ (s.local_ p).sendRecv = none
      · simp only [hc] at hrecv; exact hrecv
      · simp only [hc] at hrecv; exact hrecv
    · exact hrecv
  | .recv src dst .echo mv =>
    obtain ⟨_, rfl⟩ := h; simp only at hrecv
    by_cases hp : p = dst <;> simp only [hp] at hrecv
    · subst hp
      by_cases hc : (s.local_ p).echoRecv src mv = false
      · simp only [hc] at hrecv; exact hrecv
      · simp only [hc] at hrecv; exact hrecv
    · exact hrecv
  | .output i _ =>
    obtain ⟨_, _, _, rfl⟩ := h; simp only at hrecv
    by_cases hp : p = i <;> simp only [hp] at hrecv
    · subst hp; exact hrecv
    · exact hrecv
  | .input i _ =>
    have := input_eq_sender h; subst this
    obtain ⟨_, _, rfl⟩ := h; simp only at hrecv
    by_cases hp : p = i <;> simp only [hp] at hrecv
    · subst hp; exact hrecv
    · exact hrecv

/-- `echoed p = some v` traced to previous state when step is not `send echo v` by `p`. -/
theorem step_echoed_prev {s s' : State n Value} {l : Label n Value} {sender : Fin n}
    (h : (brb n f Value sender).step s l s')
    (p : Fin n) (v : Value)
    (hechoed : (s'.local_ p).echoed = some v)
    (hl : ∀ dst, l ≠ .send p dst .echo v) :
    (s.local_ p).echoed = some v := by
  match l with
  | .corrupt _ => obtain ⟨_, _, rfl⟩ := h; exact hechoed
  | .send src dst t mv =>
    obtain ⟨_, rfl⟩ := h; simp only at hechoed
    by_cases hp : p = src <;> simp only [hp] at hechoed
    · subst hp; match t with
      | .init | .vote => exact hechoed
      | .echo =>
        by_cases hcorr : p ∈ s.corrupted <;> simp only [↓reduceIte, Bool.if_true_left,
          Bool.decide_and, hcorr, not_false_eq_true, Option.some.injEq] at hechoed
        · exact hechoed
        · -- echoed set to some mv. Need v = mv to contradict hl.
          by_cases hv : v = mv
          · subst hv; exact absurd rfl (hl dst)
          · exact absurd hechoed.symm hv
    · exact hechoed
  | .recv src dst .init _ =>
    obtain ⟨_, rfl⟩ := h; simp only at hechoed
    by_cases hp : p = dst <;> simp only [hp] at hechoed
    · subst hp
      by_cases hc : src = sender ∧ (s.local_ p).sendRecv = none
      · simp only [hc] at hechoed; exact hechoed
      · simp only [hc] at hechoed; exact hechoed
    · exact hechoed
  | .recv src dst .echo mv =>
    obtain ⟨_, rfl⟩ := h; simp only at hechoed
    by_cases hp : p = dst <;> simp only [hp] at hechoed
    · subst hp
      by_cases hc : (s.local_ p).echoRecv src mv = false
      · simp only [hc] at hechoed; exact hechoed
      · simp only [hc] at hechoed; exact hechoed
    · exact hechoed
  | .recv src dst .vote mv =>
    obtain ⟨_, rfl⟩ := h; simp only at hechoed
    by_cases hp : p = dst <;> simp only [hp] at hechoed
    · subst hp
      by_cases hc : (s.local_ p).voteRecv src mv = false
      · simp only [hc] at hechoed; exact hechoed
      · simp only [hc] at hechoed; exact hechoed
    · exact hechoed
  | .output i _ =>
    obtain ⟨_, _, _, rfl⟩ := h; simp only at hechoed
    by_cases hp : p = i <;> simp only [hp] at hechoed
    · subst hp; exact hechoed
    · exact hechoed
  | .input i _ =>
    have := input_eq_sender h; subst this
    obtain ⟨_, _, rfl⟩ := h; simp only at hechoed
    by_cases hp : p = i <;> simp only [hp] at hechoed
    · subst hp; exact hechoed
    · exact hechoed

/-- `sendRecv p = some v` traced to previous state when step is not matching `recv init`. -/
theorem step_sendRecv_prev {s s' : State n Value} {l : Label n Value} {sender : Fin n}
    (h : (brb n f Value sender).step s l s')
    (p : Fin n) (v : Value)
    (hrecv : (s'.local_ p).sendRecv = some v)
    (hl : ∀ src dst mv, l = .recv src dst .init mv → ¬(p = dst ∧ v = mv)) :
    (s.local_ p).sendRecv = some v := by
  match l with
  | .corrupt _ => obtain ⟨_, _, rfl⟩ := h; exact hrecv
  | .send src _ _ _ =>
    obtain ⟨_, rfl⟩ := h; simp only at hrecv
    by_cases hp : p = src <;> simp only [hp] at hrecv
    · subst hp; exact hrecv
    · exact hrecv
  | .recv src dst .init mv =>
    obtain ⟨_, rfl⟩ := h; simp only at hrecv
    by_cases hp : p = dst <;> simp only [hp] at hrecv
    · subst hp
      by_cases hc : src = sender ∧ (s.local_ p).sendRecv = none
      · simp only [↓reduceIte, hc, and_self, Option.some.injEq] at hrecv
        exact (hl src p mv rfl ⟨rfl, hrecv.symm⟩).elim
      · simp only [hc] at hrecv; exact hrecv
    · exact hrecv
  | .recv src dst .echo mv =>
    obtain ⟨_, rfl⟩ := h; simp only at hrecv
    by_cases hp : p = dst <;> simp only [hp] at hrecv
    · subst hp
      by_cases hc : (s.local_ p).echoRecv src mv = false
      · simp only [hc] at hrecv; exact hrecv
      · simp only [hc] at hrecv; exact hrecv
    · exact hrecv
  | .recv src dst .vote mv =>
    obtain ⟨_, rfl⟩ := h; simp only at hrecv
    by_cases hp : p = dst <;> simp only [hp] at hrecv
    · subst hp
      by_cases hc : (s.local_ p).voteRecv src mv = false
      · simp only [hc] at hrecv; exact hrecv
      · simp only [hc] at hrecv; exact hrecv
    · exact hrecv
  | .output i _ =>
    obtain ⟨_, _, _, rfl⟩ := h; simp only at hrecv
    by_cases hp : p = i <;> simp only [hp] at hrecv
    · subst hp; exact hrecv
    · exact hrecv
  | .input i _ =>
    have := input_eq_sender h; subst this
    obtain ⟨_, _, rfl⟩ := h; simp only at hrecv
    by_cases hp : p = i <;> simp only [hp] at hrecv
    · subst hp; exact hrecv
    · exact hrecv

/-- `sendRecv p` is monotone across steps. -/
theorem step_sendRecv_mono {s s' : State n Value} {l : Label n Value} {sender : Fin n}
    (h : (brb n f Value sender).step s l s')
    (p : Fin n) (v : Value)
    (hrecv : (s.local_ p).sendRecv = some v) :
    (s'.local_ p).sendRecv = some v := by
  match l with
  | .corrupt _ => obtain ⟨_, _, rfl⟩ := h; exact hrecv
  | .send .. => rw [send_sendRecv h]; exact hrecv
  | .recv _ _ .init _ => exact recv_init_sendRecv_some h p v hrecv
  | .recv _ _ .echo _ => rw [recv_echo_sendRecv h]; exact hrecv
  | .recv _ _ .vote _ => rw [recv_vote_sendRecv h]; exact hrecv
  | .output .. => rw [output_sendRecv h]; exact hrecv
  | .input .. => rw [input_sendRecv h]; exact hrecv

/-- After `send echo v` by a correct process `src`, `echoed src = some v`. -/
theorem send_echo_sets_echoed {s s' : State n Value} {src dst v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.send src dst .echo v) s')
    (hcorr : isCorrect n Value s src) :
    (s'.local_ src).echoed = some v := by
  obtain ⟨_, rfl⟩ := h; simp only [isCorrect] at hcorr; simp only [↓reduceIte,
    Bool.if_true_left, Bool.decide_and, hcorr, not_false_eq_true]

/-- After `send vote v` by a correct process `src`, `voted src v = true`. -/
theorem send_vote_sets_voted {s s' : State n Value} {src dst v} {sender : Fin n}
    (h : (brb n f Value sender).step s (.send src dst .vote v) s')
    (hcorr : isCorrect n Value s src) :
    (s'.local_ src).voted v = true := by
  obtain ⟨_, rfl⟩ := h; simp only [isCorrect] at hcorr; simp only [↓reduceIte,
    Bool.if_true_left, Bool.decide_and, hcorr, not_false_eq_true, decide_true, Bool.true_or]

/-- `sent p dst t v = true` is monotone across steps. -/
theorem step_sent_mono {s s' : State n Value} {l : Label n Value} {sender : Fin n}
    (h : (brb n f Value sender).step s l s')
    (p dst : Fin n) (t : MsgType) (v : Value)
    (hsent : (s.local_ p).sent dst t v = true) :
    (s'.local_ p).sent dst t v = true := by
  -- sent is only changed by send steps; all other steps preserve sent.
  -- For send(src, dst', t', mv): p ≠ src → unchanged; p = src → OR gate
  -- with new (dst', t', mv) entry set to true, old entries preserved.
  match l with
  | .corrupt _ => obtain ⟨_, _, rfl⟩ := h; exact hsent
  | .send src dst' t' mv =>
    obtain ⟨_, rfl⟩ := h; simp only
    by_cases hp : p = src
    · subst hp; simp only [↓reduceIte]; split <;> [rfl; exact hsent]
    · simp [hp]; exact hsent
  | .recv _ rdst .init _ =>
    have : (s'.local_ p).sent = (s.local_ p).sent := by
      obtain ⟨_, rfl⟩ := h; simp only
      by_cases hp : p = rdst
      · subst hp; simp only [↓reduceIte]; split <;> rfl
      · simp [hp]
    exact this ▸ hsent
  | .recv _ rdst .echo _ =>
    have : (s'.local_ p).sent = (s.local_ p).sent := by
      obtain ⟨_, rfl⟩ := h; simp only
      by_cases hp : p = rdst
      · subst hp; simp only [↓reduceIte]; split <;> rfl
      · simp [hp]
    exact this ▸ hsent
  | .recv _ rdst .vote _ =>
    have : (s'.local_ p).sent = (s.local_ p).sent := by
      obtain ⟨_, rfl⟩ := h; simp only
      by_cases hp : p = rdst
      · subst hp; simp only [↓reduceIte]; split <;> rfl
      · simp [hp]
    exact this ▸ hsent
  | .output i _ =>
    have : (s'.local_ p).sent = (s.local_ p).sent := by
      obtain ⟨_, _, _, rfl⟩ := h; simp only
      by_cases hp : p = i <;> simp [hp]
    exact this ▸ hsent
  | .input i _ =>
    have : (s'.local_ p).sent = (s.local_ p).sent := by
      have := input_eq_sender h; subst this
      obtain ⟨_, _, rfl⟩ := h; simp only
      by_cases hp : p = i <;> simp [hp]
    exact this ▸ hsent

/-- `countEchoRecv` is monotone across steps. -/
theorem step_countEchoRecv_mono {s s' : State n Value} {l : Label n Value} {sender : Fin n}
    (h : (brb n f Value sender).step s l s') (q : Fin n) (v : Value) :
    countEchoRecv n Value (s.local_ q) v ≤
    countEchoRecv n Value (s'.local_ q) v := by
  unfold countEchoRecv
  apply filter_length_mono
  intro r hr; simp only at hr ⊢
  exact step_echoRecv h q r v hr

/-- `voteRecv p q v` is monotone: if true before a step, still true after. -/
theorem step_voteRecv {s s' : State n Value} {l : Label n Value} {sender : Fin n}
    (h : (brb n f Value sender).step s l s')
    (p q : Fin n) (v : Value)
    (hrecv : (s.local_ p).voteRecv q v = true) :
    (s'.local_ p).voteRecv q v = true := by
  match l with
  | .corrupt _ => obtain ⟨_, _, rfl⟩ := h; exact hrecv
  | .send src _ _ _ =>
    obtain ⟨_, rfl⟩ := h; simp only
    by_cases hp : p = src <;> simp only [hp]
    · subst hp; exact hrecv
    · exact hrecv
  | .recv src dst .init _ =>
    obtain ⟨_, rfl⟩ := h; simp only
    by_cases hp : p = dst <;> simp only [hp]
    · subst hp
      by_cases hc : (src : Fin n) = sender ∧ (s.local_ p).sendRecv = none
      · simp only [hc]; exact hrecv
      · simp only [hc]; exact hrecv
    · exact hrecv
  | .recv src dst .echo mv =>
    obtain ⟨_, rfl⟩ := h; simp only
    by_cases hp : p = dst <;> simp only [hp]
    · subst hp
      by_cases hc : (s.local_ p).echoRecv src mv = false
      · simp only [hc]; exact hrecv
      · simp only [hc]; exact hrecv
    · exact hrecv
  | .recv src dst .vote mv =>
    obtain ⟨_, rfl⟩ := h; simp only
    by_cases hp : p = dst <;> simp only [hp]
    · subst hp
      by_cases hc : (s.local_ p).voteRecv src mv = false
      · simp only [hc]; by_cases hqv : q = src ∧ v = mv
        · simp [hqv]
        · simp only [↓reduceIte, Bool.if_true_left, Bool.decide_and, Bool.or_eq_true,
          Bool.and_eq_true, decide_eq_true_eq, hqv, false_or]; exact hrecv
      · simp only [hc]; exact hrecv
    · exact hrecv
  | .output i _ =>
    obtain ⟨_, _, _, rfl⟩ := h; simp only
    by_cases hp : p = i <;> simp only [hp]
    · subst hp; exact hrecv
    · exact hrecv
  | .input i _ =>
    have := input_eq_sender h; subst this
    obtain ⟨_, _, rfl⟩ := h; simp only
    by_cases hp : p = i <;> simp only [hp]
    · subst hp; exact hrecv
    · exact hrecv

/-- `countVoteRecv` is monotone across steps. -/
theorem step_countVoteRecv_mono {s s' : State n Value} {l : Label n Value} {sender : Fin n}
    (h : (brb n f Value sender).step s l s') (q : Fin n) (v : Value) :
    countVoteRecv n Value (s.local_ q) v ≤
    countVoteRecv n Value (s'.local_ q) v := by
  unfold countVoteRecv
  apply filter_length_mono
  intro r hr; simp only at hr ⊢
  exact step_voteRecv h q r v hr

end mechanical_helpers

/-! ### Execution-level persistence lemmas

    These chain single-step monotonicity across valid executions.
    Used by the delivery chain proofs in `BRB_Liveness.lean`. -/

section execution_persistence

open LTS

variable {n f : Nat} {Value : Type} [DecidableEq Value] {sender : Fin n}

/-- Corruption membership persists across a single step. -/
private theorem step_corrupted_mem {s s' : State n Value} {l : Label n Value}
    (h : (brb n f Value sender).step s l s') {p : Fin n}
    (hp : p ∈ s.corrupted) : p ∈ s'.corrupted := by
  have hc := step_corrupted h
  match l with
  | .corrupt i => simp [hc]; exact Or.inr hp
  | .send _ _ _ _ => rw [hc]; exact hp
  | .recv _ _ _ _ => rw [hc]; exact hp
  | .output _ _ => rw [hc]; exact hp
  | .input _ _ => rw [hc]; exact hp

/-- Corruption persists along valid BRB executions. -/
theorem corrupted_mem_persist_along
    {e : Execution (State n Value) (Label n Value)}
    (hv : (brb n f Value sender).valid_exec e)
    {k : Nat} {p : Fin n}
    (h : p ∈ (e.states k).corrupted) (k' : Nat) (hk : k ≤ k') :
    p ∈ (e.states k').corrupted := by
  induction k' with
  | zero => exact (Nat.le_zero.mp hk) ▸ h
  | succ k' ih =>
    rcases Nat.eq_or_lt_of_le hk with rfl | hlt
    · exact h
    · exact step_corrupted_mem (hv.2 k') (ih (by omega))

/-- `voteRecv p q v = true` persists along valid BRB executions. -/
theorem voteRecv_persist_along
    {e : Execution (State n Value) (Label n Value)}
    (hv : (brb n f Value sender).valid_exec e)
    {k : Nat} {p q : Fin n} {v : Value}
    (h : ((e.states k).local_ p).voteRecv q v = true)
    (k' : Nat) (hk : k ≤ k') :
    ((e.states k').local_ p).voteRecv q v = true := by
  induction k' with
  | zero => exact (Nat.le_zero.mp hk) ▸ h
  | succ k' ih =>
    rcases Nat.eq_or_lt_of_le hk with rfl | hlt
    · exact h
    · exact step_voteRecv (hv.2 k') p q v (ih (by omega))

/-- `countVoteRecv` is non-decreasing along valid BRB executions. -/
theorem countVoteRecv_mono_along
    {e : Execution (State n Value) (Label n Value)}
    (hv : (brb n f Value sender).valid_exec e)
    (p : Fin n) (v : Value) (k k' : Nat) (hk : k ≤ k') :
    countVoteRecv n Value ((e.states k).local_ p) v ≤
    countVoteRecv n Value ((e.states k').local_ p) v := by
  induction k' with
  | zero => exact (Nat.le_zero.mp hk) ▸ Nat.le_refl _
  | succ k' ih =>
    rcases Nat.eq_or_lt_of_le hk with rfl | hlt
    · exact Nat.le_refl _
    · exact Nat.le_trans (ih (by omega)) (step_countVoteRecv_mono (hv.2 k') p v)

/-- `echoRecv p q v = true` persists along valid BRB executions. -/
theorem echoRecv_persist_along
    {e : Execution (State n Value) (Label n Value)}
    (hv : (brb n f Value sender).valid_exec e)
    {k : Nat} {p q : Fin n} {v : Value}
    (h : ((e.states k).local_ p).echoRecv q v = true)
    (k' : Nat) (hk : k ≤ k') :
    ((e.states k').local_ p).echoRecv q v = true := by
  induction k' with
  | zero => exact (Nat.le_zero.mp hk) ▸ h
  | succ k' ih =>
    rcases Nat.eq_or_lt_of_le hk with rfl | hlt
    · exact h
    · exact step_echoRecv (hv.2 k') p q v (ih (by omega))

/-- `voted p v = true` persists along valid BRB executions. -/
theorem voted_persist_along
    {e : Execution (State n Value) (Label n Value)}
    (hv : (brb n f Value sender).valid_exec e)
    {k : Nat} {p : Fin n} {v : Value}
    (h : ((e.states k).local_ p).voted v = true)
    (k' : Nat) (hk : k ≤ k') :
    ((e.states k').local_ p).voted v = true := by
  induction k' with
  | zero => exact (Nat.le_zero.mp hk) ▸ h
  | succ k' ih =>
    rcases Nat.eq_or_lt_of_le hk with rfl | hlt
    · exact h
    · exact step_voted (hv.2 k') p v (ih (by omega))

/-- `broadcastVal p = some v` is preserved by a single step. -/
private theorem step_broadcastVal_persist {s s' : State n Value} {l : Label n Value}
    (h : (brb n f Value sender).step s l s') (p : Fin n) (v : Value)
    (hbv : (s.local_ p).broadcastVal = some v) :
    (s'.local_ p).broadcastVal = some v := by
  match l with
  | .input i w =>
    have := input_eq_sender h; subst this
    obtain ⟨_, hbv_none, rfl⟩ := h; simp only
    by_cases hp : p = i
    · subst hp; simp only [↓reduceIte]; rw [hbv_none] at hbv; exact absurd hbv nofun
    · simp [hp]; exact hbv
  | .corrupt _ => rw [step_broadcastVal h p (by intros; nofun)]; exact hbv
  | .send _ _ _ _ => rw [step_broadcastVal h p (by intros; nofun)]; exact hbv
  | .recv _ _ _ _ => rw [step_broadcastVal h p (by intros; nofun)]; exact hbv
  | .output _ _ => rw [step_broadcastVal h p (by intros; nofun)]; exact hbv

/-- `broadcastVal p = some v` persists along valid BRB executions. -/
theorem broadcastVal_persist_along
    {e : Execution (State n Value) (Label n Value)}
    (hv : (brb n f Value sender).valid_exec e)
    {k : Nat} {p : Fin n} {v : Value}
    (h : ((e.states k).local_ p).broadcastVal = some v)
    (k' : Nat) (hk : k ≤ k') :
    ((e.states k').local_ p).broadcastVal = some v := by
  induction k' with
  | zero => exact (Nat.le_zero.mp hk) ▸ h
  | succ k' ih =>
    rcases Nat.eq_or_lt_of_le hk with rfl | hlt
    · exact h
    · exact step_broadcastVal_persist (hv.2 k') p v (ih (by omega))

/-- `sent p dst t v = true` persists along valid BRB executions. -/
theorem sent_persist_along
    {e : Execution (State n Value) (Label n Value)}
    (hv : (brb n f Value sender).valid_exec e)
    {k : Nat} {p dst : Fin n} {t : MsgType} {v : Value}
    (h : ((e.states k).local_ p).sent dst t v = true)
    (k' : Nat) (hk : k ≤ k') :
    ((e.states k').local_ p).sent dst t v = true := by
  induction k' with
  | zero => exact (Nat.le_zero.mp hk) ▸ h
  | succ k' ih =>
    rcases Nat.eq_or_lt_of_le hk with rfl | hlt
    · exact h
    · exact step_sent_mono (hv.2 k') p dst t v (ih (by omega))

/-- `sendRecv p = some v` persists along valid BRB executions. -/
theorem sendRecv_persist_along
    {e : Execution (State n Value) (Label n Value)}
    (hv : (brb n f Value sender).valid_exec e)
    {k : Nat} {p : Fin n} {v : Value}
    (h : ((e.states k).local_ p).sendRecv = some v)
    (k' : Nat) (hk : k ≤ k') :
    ((e.states k').local_ p).sendRecv = some v := by
  induction k' with
  | zero => exact (Nat.le_zero.mp hk) ▸ h
  | succ k' ih =>
    rcases Nat.eq_or_lt_of_le hk with rfl | hlt
    · exact h
    · exact step_sendRecv_mono (hv.2 k') p v (ih (by omega))

/-- `returned p = some v` persists along valid BRB executions. -/
theorem returned_persist_along
    {e : Execution (State n Value) (Label n Value)}
    (hv : (brb n f Value sender).valid_exec e)
    {k : Nat} {p : Fin n} {v : Value}
    (h : ((e.states k).local_ p).returned = some v)
    (k' : Nat) (hk : k ≤ k') :
    ((e.states k').local_ p).returned = some v := by
  induction k' with
  | zero => exact (Nat.le_zero.mp hk) ▸ h
  | succ k' ih =>
    rcases Nat.eq_or_lt_of_le hk with rfl | hlt
    · exact h
    · -- returned is unchanged unless the step is output for p.
      -- If it's output for p, returned p goes from none to some w.
      -- But returned p was already some v, so either:
      --   (a) the step is not output for p → preserved by step_returned
      --   (b) the step is output for p → but output requires returned = none,
      --       contradicting returned = some v
      have hprev := ih (by omega)
      by_cases hout : ∃ w, (e.labels k') = .output p w
      · obtain ⟨w, hw⟩ := hout
        -- output p w requires (s.local_ p).returned = none
        have hstep := hv.2 k'
        rw [hw] at hstep
        simp only [brb] at hstep
        exact absurd hstep.2.1 (by rw [hprev]; exact nofun)
      · push_neg at hout
        have hne : ∀ i w, (e.labels k') = .output i w → p ≠ i := by
          intro i w hlbl hpi; subst hpi; exact hout w hlbl
        rw [step_returned (hv.2 k') p hne]
        exact hprev

/-- `echoed p = some v` persists along valid BRB executions. -/
theorem echoed_persist_along
    {e : Execution (State n Value) (Label n Value)}
    (hv : (brb n f Value sender).valid_exec e)
    {k : Nat} {p : Fin n} {v : Value}
    (h : ((e.states k).local_ p).echoed = some v)
    (k' : Nat) (hk : k ≤ k') :
    ((e.states k').local_ p).echoed = some v := by
  induction k' with
  | zero => exact (Nat.le_zero.mp hk) ▸ h
  | succ k' ih =>
    rcases Nat.eq_or_lt_of_le hk with rfl | hlt
    · exact h
    · exact step_echoed (hv.2 k') p v (ih (by omega))

end execution_persistence

/-! ### Reachability Invariants (delivery + value)
    IMPORTANT: These are sorry'd pending mechanical induction proofs.
    Each follows the same pattern: induction on Reachable, case-split on step label,
    use projection lemmas to show field relationships are preserved.

    These connect sent, buffer, and recv-effect fields in reachable states.
    Used by `brb_fair_deadlock_implies_terminated` in `BRB_Liveness.lean`. -/

section reachability_invariants
variable {n f : Nat} {Value : Type} [DecidableEq Value] {sender : Fin n}
open LTS

/-- **Init delivery invariant**: if sender has `sent dst init v = true`,
    then buffer has the message or dst has `sendRecv ≠ none`. -/
theorem init_delivery_inv
    (s : State n Value)
    (hr : Reachable (brb n f Value sender) s)
    (dst : Fin n) (v : Value)
    (hsent : (s.local_ sender).sent dst .init v = true) :
    s.buffer ⟨sender, dst, .init, v⟩ = true ∨ (s.local_ dst).sendRecv ≠ none := by
  induction hr with
  | init hinit => simp [hinit.1 sender, LocalState.init] at hsent
  | @step s₀ l s _ hstep ih =>
    match l with
    | .corrupt _ =>
      obtain ⟨_, _, rfl⟩ := hstep; exact ih hsent
    | .input i v' =>
      -- input only changes broadcastVal; sent/buffer/sendRecv unchanged
      have hsent₀ : (s₀.local_ sender).sent dst .init v = true := by
        have hi := input_eq_sender hstep; subst hi
        obtain ⟨_, _, rfl⟩ := hstep
        dsimp only at hsent; rw [if_pos rfl] at hsent; exact hsent
      rcases ih hsent₀ with h | h
      · left; rw [input_buffer hstep]; exact h
      · right; rw [input_sendRecv hstep]; exact h
    | .output i v' =>
      -- output only changes returned; sent/buffer/sendRecv unchanged
      have hsent₀ : (s₀.local_ sender).sent dst .init v = true := by
        obtain ⟨_, _, _, rfl⟩ := hstep; dsimp only at hsent
        by_cases h : sender = i
        · subst h; rw [if_pos rfl] at hsent; exact hsent
        · rw [if_neg h] at hsent; exact hsent
      rcases ih hsent₀ with h | h
      · left; rw [output_buffer hstep]; exact h
      · right; rw [output_sendRecv hstep]; exact h
    | .send src dst' t' mv' =>
      -- sent and buffer both change; sendRecv unchanged
      by_cases hps : sender = src
      · subst hps
        -- Check if this is the message being sent
        have hstep' := hstep; obtain ⟨_, rfl⟩ := hstep'
        simp only [ite_true] at hsent
        by_cases heq : dst = dst' ∧ MsgType.init = t' ∧ v = mv'
        · obtain ⟨rfl, rfl, rfl⟩ := heq; left; simp
        · simp only [heq, ite_false] at hsent
          rcases ih hsent with h | h
          · left; simp [h]
          · right; rw [send_sendRecv hstep]; exact h
      · -- sender ≠ src: sent unchanged via step_local_other
        have hsent₀ : (s₀.local_ sender).sent dst .init v = true := by
          rw [step_local_other hstep sender hps] at hsent; exact hsent
        rcases ih hsent₀ with h | h
        · left; obtain ⟨_, rfl⟩ := hstep; simp [h]
        · right; rw [send_sendRecv hstep]; exact h
    | .recv src' dst' .init mv' =>
      -- sent unchanged; buffer may lose our message → sendRecv gets set
      have hsent₀ : (s₀.local_ sender).sent dst .init v = true := by
        obtain ⟨_, rfl⟩ := hstep; simp only at hsent
        by_cases h : sender = dst'
        · subst h; simp only [ite_true] at hsent; split at hsent <;> exact hsent
        · simp only [h, ite_false] at hsent; exact hsent
      rcases ih hsent₀ with hbuf | hrecv
      · -- Buffer had our message. Check if consumed.
        by_cases hm : sender = src' ∧ dst = dst' ∧ v = mv'
        · -- Our message consumed by this recv
          obtain ⟨rfl, rfl, rfl⟩ := hm
          right
          obtain ⟨_, rfl⟩ := hstep; dsimp only
          by_cases hc : (s₀.local_ dst).sendRecv = none
          · simp [hc]
          · simp [hc]
        · -- Different message consumed; our message preserved
          left
          have hne : ¬(⟨sender, dst, MsgType.init, v⟩ : Message n Value) =
              ⟨src', dst', .init, mv'⟩ := by
            intro heq; apply hm
            simp only [Message.mk.injEq] at heq
            exact ⟨heq.1, heq.2.1, heq.2.2.2⟩
          obtain ⟨_, rfl⟩ := hstep; simp only [hne, ite_false]; exact hbuf
      · -- sendRecv was non-none, stays non-none
        right
        by_cases hd : dst = dst'
        · subst hd
          obtain ⟨_, rfl⟩ := hstep; simp only [ite_true]
          by_cases hc : src' = sender ∧ (s₀.local_ dst).sendRecv = none
          · exact absurd hc.2 hrecv
          · simp only [hc, ite_false]; exact hrecv
        · obtain ⟨_, rfl⟩ := hstep; simp only [hd, ite_false]; exact hrecv
    | .recv src' dst' .echo mv' =>
      -- sent unchanged; buffer only removes echo message (≠ init); sendRecv unchanged
      have hsent₀ : (s₀.local_ sender).sent dst .init v = true := by
        obtain ⟨_, rfl⟩ := hstep; simp only at hsent
        by_cases h : sender = dst'
        · subst h; simp only [ite_true] at hsent; split at hsent <;> exact hsent
        · simp only [h, ite_false] at hsent; exact hsent
      rcases ih hsent₀ with h | h
      · left
        have hne : ¬(⟨sender, dst, MsgType.init, v⟩ : Message n Value) =
            ⟨src', dst', .echo, mv'⟩ := by
          intro heq; simp only [Message.mk.injEq] at heq
          exact MsgType.noConfusion heq.2.2.1
        obtain ⟨_, rfl⟩ := hstep; simp only [hne, ite_false]; exact h
      · right; rw [recv_echo_sendRecv hstep]; exact h
    | .recv src' dst' .vote mv' =>
      -- sent unchanged; buffer only removes vote message (≠ init); sendRecv unchanged
      have hsent₀ : (s₀.local_ sender).sent dst .init v = true := by
        obtain ⟨_, rfl⟩ := hstep; simp only at hsent
        by_cases h : sender = dst'
        · subst h; simp only [ite_true] at hsent; split at hsent <;> exact hsent
        · simp only [h, ite_false] at hsent; exact hsent
      rcases ih hsent₀ with h | h
      · left
        have hne : ¬(⟨sender, dst, MsgType.init, v⟩ : Message n Value) =
            ⟨src', dst', .vote, mv'⟩ := by
          intro heq; simp only [Message.mk.injEq] at heq
          exact MsgType.noConfusion heq.2.2.1
        obtain ⟨_, rfl⟩ := hstep; simp only [hne, ite_false]; exact h
      · right; rw [recv_vote_sendRecv hstep]; exact h

/-- **Echo delivery invariant**: if src has `sent dst echo v = true`,
    then buffer has the message or dst has `echoRecv src v = true`. -/
theorem echo_delivery_inv
    (s : State n Value)
    (hr : Reachable (brb n f Value sender) s)
    (src dst : Fin n) (v : Value)
    (hsent : (s.local_ src).sent dst .echo v = true) :
    s.buffer ⟨src, dst, .echo, v⟩ = true ∨ (s.local_ dst).echoRecv src v = true := by
  induction hr with
  | init hinit => simp [hinit.1 src, LocalState.init] at hsent
  | @step s₀ l s _ hstep ih =>
    match l with
    | .corrupt _ =>
      obtain ⟨_, _, rfl⟩ := hstep; exact ih hsent
    | .input i v' =>
      have hsent₀ : (s₀.local_ src).sent dst .echo v = true := by
        obtain ⟨_, _, rfl⟩ := hstep; simp only at hsent
        by_cases h : src = sender
        · subst h; simp only [ite_true] at hsent; exact hsent
        · simp only [h, ite_false] at hsent; exact hsent
      rcases ih hsent₀ with h | h
      · left; rw [input_buffer hstep]; exact h
      · right; exact step_echoRecv hstep dst src v h
    | .output i v' =>
      have hsent₀ : (s₀.local_ src).sent dst .echo v = true := by
        obtain ⟨_, _, _, rfl⟩ := hstep; simp only at hsent
        by_cases h : src = i
        · subst h; simp only [ite_true] at hsent; exact hsent
        · simp only [h, ite_false] at hsent; exact hsent
      rcases ih hsent₀ with h | h
      · left; rw [output_buffer hstep]; exact h
      · right; exact step_echoRecv hstep dst src v h
    | .send src' dst' t' mv' =>
      have hsent₀_or : (src = src' ∧ dst = dst' ∧ MsgType.echo = t' ∧ v = mv') ∨
          (s₀.local_ src).sent dst .echo v = true := by
        obtain ⟨_, rfl⟩ := hstep; simp only at hsent
        by_cases hps : src = src'
        · subst hps; simp only [ite_true] at hsent
          by_cases heq : dst = dst' ∧ MsgType.echo = t' ∧ v = mv'
          · exact .inl ⟨rfl, heq.1, heq.2.1, heq.2.2⟩
          · simp only [heq, ite_false] at hsent; exact .inr hsent
        · simp only [hps, ite_false] at hsent; exact .inr hsent
      rcases hsent₀_or with ⟨hsrc, hdst, ht, hv⟩ | hsent₀
      · left; obtain ⟨_, rfl⟩ := hstep; simp only
        rw [hsrc, hdst, ht, hv, if_pos rfl]
      · rcases ih hsent₀ with h | h
        · left; obtain ⟨_, rfl⟩ := hstep; simp [h]
        · right; exact step_echoRecv hstep dst src v h
    | .recv src' dst' .echo mv' =>
      have hsent₀ : (s₀.local_ src).sent dst .echo v = true := by
        obtain ⟨_, rfl⟩ := hstep; simp only at hsent
        by_cases h : src = dst'
        · subst h; simp only [ite_true] at hsent; split at hsent <;> exact hsent
        · simp only [h, ite_false] at hsent; exact hsent
      rcases ih hsent₀ with hbuf | hrecv
      · by_cases hm : src = src' ∧ dst = dst' ∧ v = mv'
        · -- Our echo message consumed → echoRecv set to true
          obtain ⟨rfl, rfl, rfl⟩ := hm
          right; obtain ⟨_, rfl⟩ := hstep; simp only [ite_true]
          split <;> simp_all
        · left
          have hne : ¬(⟨src, dst, MsgType.echo, v⟩ : Message n Value) =
              ⟨src', dst', .echo, mv'⟩ := by
            intro heq; apply hm; simp only [Message.mk.injEq] at heq
            exact ⟨heq.1, heq.2.1, heq.2.2.2⟩
          obtain ⟨_, rfl⟩ := hstep; simp only [hne, ite_false]; exact hbuf
      · right; exact step_echoRecv hstep dst src v hrecv
    | .recv src' dst' .init mv' =>
      have hsent₀ : (s₀.local_ src).sent dst .echo v = true := by
        obtain ⟨_, rfl⟩ := hstep; simp only at hsent
        by_cases h : src = dst'
        · subst h; simp only [ite_true] at hsent; split at hsent <;> exact hsent
        · simp only [h, ite_false] at hsent; exact hsent
      rcases ih hsent₀ with h | h
      · left
        have hne : ¬(⟨src, dst, MsgType.echo, v⟩ : Message n Value) =
            ⟨src', dst', .init, mv'⟩ := by
          intro heq; simp only [Message.mk.injEq] at heq; exact MsgType.noConfusion heq.2.2.1
        obtain ⟨_, rfl⟩ := hstep; simp only [hne, ite_false]; exact h
      · right; exact step_echoRecv hstep dst src v h
    | .recv src' dst' .vote mv' =>
      have hsent₀ : (s₀.local_ src).sent dst .echo v = true := by
        obtain ⟨_, rfl⟩ := hstep; simp only at hsent
        by_cases h : src = dst'
        · subst h; simp only [ite_true] at hsent; split at hsent <;> exact hsent
        · simp only [h, ite_false] at hsent; exact hsent
      rcases ih hsent₀ with h | h
      · left
        have hne : ¬(⟨src, dst, MsgType.echo, v⟩ : Message n Value) =
            ⟨src', dst', .vote, mv'⟩ := by
          intro heq; simp only [Message.mk.injEq] at heq; exact MsgType.noConfusion heq.2.2.1
        obtain ⟨_, rfl⟩ := hstep; simp only [hne, ite_false]; exact h
      · right; exact step_echoRecv hstep dst src v h

/-- **Vote delivery invariant**: if src has `sent dst vote v = true`,
    then buffer has the message or dst has `voteRecv src v = true`. -/
theorem vote_delivery_inv
    (s : State n Value)
    (hr : Reachable (brb n f Value sender) s)
    (src dst : Fin n) (v : Value)
    (hsent : (s.local_ src).sent dst .vote v = true) :
    s.buffer ⟨src, dst, .vote, v⟩ = true ∨ (s.local_ dst).voteRecv src v = true := by
  induction hr with
  | init hinit => simp [hinit.1 src, LocalState.init] at hsent
  | @step s₀ l s _ hstep ih =>
    match l with
    | .corrupt _ =>
      obtain ⟨_, _, rfl⟩ := hstep; exact ih hsent
    | .input i v' =>
      have hsent₀ : (s₀.local_ src).sent dst .vote v = true := by
        obtain ⟨_, _, rfl⟩ := hstep; simp only at hsent
        by_cases h : src = sender
        · subst h; simp only [ite_true] at hsent; exact hsent
        · simp only [h, ite_false] at hsent; exact hsent
      rcases ih hsent₀ with h | h
      · left; rw [input_buffer hstep]; exact h
      · right; exact step_voteRecv hstep dst src v h
    | .output i v' =>
      have hsent₀ : (s₀.local_ src).sent dst .vote v = true := by
        obtain ⟨_, _, _, rfl⟩ := hstep; simp only at hsent
        by_cases h : src = i
        · subst h; simp only [ite_true] at hsent; exact hsent
        · simp only [h, ite_false] at hsent; exact hsent
      rcases ih hsent₀ with h | h
      · left; rw [output_buffer hstep]; exact h
      · right; exact step_voteRecv hstep dst src v h
    | .send src' dst' t' mv' =>
      have hsent₀_or : (src = src' ∧ dst = dst' ∧ MsgType.vote = t' ∧ v = mv') ∨
          (s₀.local_ src).sent dst .vote v = true := by
        obtain ⟨_, rfl⟩ := hstep; simp only at hsent
        by_cases hps : src = src'
        · subst hps; simp only [ite_true] at hsent
          by_cases heq : dst = dst' ∧ MsgType.vote = t' ∧ v = mv'
          · exact .inl ⟨rfl, heq.1, heq.2.1, heq.2.2⟩
          · simp only [heq, ite_false] at hsent; exact .inr hsent
        · simp only [hps, ite_false] at hsent; exact .inr hsent
      rcases hsent₀_or with ⟨hsrc, hdst, ht, hv⟩ | hsent₀
      · left; obtain ⟨_, rfl⟩ := hstep; simp only
        rw [hsrc, hdst, ht, hv, if_pos rfl]
      · rcases ih hsent₀ with h | h
        · left; obtain ⟨_, rfl⟩ := hstep; simp [h]
        · right; exact step_voteRecv hstep dst src v h
    | .recv src' dst' .vote mv' =>
      have hsent₀ : (s₀.local_ src).sent dst .vote v = true := by
        obtain ⟨_, rfl⟩ := hstep; simp only at hsent
        by_cases h : src = dst'
        · subst h; simp only [ite_true] at hsent; split at hsent <;> exact hsent
        · simp only [h, ite_false] at hsent; exact hsent
      rcases ih hsent₀ with hbuf | hrecv
      · by_cases hm : src = src' ∧ dst = dst' ∧ v = mv'
        · -- Our vote message consumed → voteRecv set to true
          obtain ⟨rfl, rfl, rfl⟩ := hm
          right; obtain ⟨_, rfl⟩ := hstep; simp only [ite_true]
          split <;> simp_all
        · left
          have hne : ¬(⟨src, dst, MsgType.vote, v⟩ : Message n Value) =
              ⟨src', dst', .vote, mv'⟩ := by
            intro heq; apply hm; simp only [Message.mk.injEq] at heq
            exact ⟨heq.1, heq.2.1, heq.2.2.2⟩
          obtain ⟨_, rfl⟩ := hstep; simp only [hne, ite_false]; exact hbuf
      · right; exact step_voteRecv hstep dst src v hrecv
    | .recv src' dst' .init mv' =>
      have hsent₀ : (s₀.local_ src).sent dst .vote v = true := by
        obtain ⟨_, rfl⟩ := hstep; simp only at hsent
        by_cases h : src = dst'
        · subst h; simp only [ite_true] at hsent; split at hsent <;> exact hsent
        · simp only [h, ite_false] at hsent; exact hsent
      rcases ih hsent₀ with h | h
      · left
        have hne : ¬(⟨src, dst, MsgType.vote, v⟩ : Message n Value) =
            ⟨src', dst', .init, mv'⟩ := by
          intro heq; simp only [Message.mk.injEq] at heq; exact MsgType.noConfusion heq.2.2.1
        obtain ⟨_, rfl⟩ := hstep; simp only [hne, ite_false]; exact h
      · right; exact step_voteRecv hstep dst src v h
    | .recv src' dst' .echo mv' =>
      have hsent₀ : (s₀.local_ src).sent dst .vote v = true := by
        obtain ⟨_, rfl⟩ := hstep; simp only at hsent
        by_cases h : src = dst'
        · subst h; simp only [ite_true] at hsent; split at hsent <;> exact hsent
        · simp only [h, ite_false] at hsent; exact hsent
      rcases ih hsent₀ with h | h
      · left
        have hne : ¬(⟨src, dst, MsgType.vote, v⟩ : Message n Value) =
            ⟨src', dst', .echo, mv'⟩ := by
          intro heq; simp only [Message.mk.injEq] at heq; exact MsgType.noConfusion heq.2.2.1
        obtain ⟨_, rfl⟩ := hstep; simp only [hne, ite_false]; exact h
      · right; exact step_voteRecv hstep dst src v h

/-- **Buffer-init value invariant**: with correct sender, if a message from
    sender is in the buffer, broadcastVal matches. -/
theorem buffer_init_broadcastVal_inv
    (s : State n Value)
    (hr : Reachable (brb n f Value sender) s)
    (hcorr : isCorrect n Value s sender)
    (dst : Fin n) (w : Value)
    (hbuf : s.buffer ⟨sender, dst, .init, w⟩ = true) :
    (s.local_ sender).broadcastVal = some w := by
  induction hr with
  | init hinit => simp [hinit.2.1] at hbuf
  | @step s₀ l s _ hstep ih =>
    have hcorr₀ : isCorrect n Value s₀ sender := step_correct_prev hstep sender hcorr
    match l with
    | .corrupt _ =>
      obtain ⟨_, _, rfl⟩ := hstep; exact ih hcorr₀ hbuf
    | .input _ _ =>
      have hbuf₀ := hbuf; rw [input_buffer hstep] at hbuf₀
      have h_bv := ih hcorr₀ hbuf₀
      obtain ⟨_, hbv_none, _⟩ := hstep
      rw [h_bv] at hbv_none; exact absurd hbv_none (by simp)
    | .output _ _ =>
      have hbuf₀ := hbuf; rw [output_buffer hstep] at hbuf₀
      rw [step_broadcastVal hstep sender (by intro _ _ h; cases h)]
      exact ih hcorr₀ hbuf₀
    | .send src' dst' t' mv' =>
      rw [send_broadcastVal hstep sender]
      obtain ⟨hpre, rfl⟩ := hstep
      simp only at hbuf
      by_cases hm : (⟨sender, dst, .init, w⟩ : Message n Value) = ⟨src', dst', t', mv'⟩
      · simp only [Message.mk.injEq] at hm
        obtain ⟨hsrc, _, ht, hv⟩ := hm; subst hsrc; subst hv
        rcases hpre with hcorrupt | ⟨_, _, hcond⟩
        · exact absurd hcorrupt hcorr₀
        · cases ht; exact hcond.2
      · simp only [hm, ite_false] at hbuf
        exact ih hcorr₀ hbuf
    | .recv src' dst' t' mv' =>
      rw [step_broadcastVal hstep sender (by intro _ _ h; cases h)]
      -- Buffer: recv removes a message. If ours was removed, buffer = false → contradiction.
      obtain ⟨_, rfl⟩ := hstep; simp only at hbuf
      by_cases hm : (⟨sender, dst, .init, w⟩ : Message n Value) = ⟨src', dst', t', mv'⟩
      · simp [hm] at hbuf
      · simp only [hm, ite_false] at hbuf; exact ih hcorr₀ hbuf

/-- **SendRecv value invariant**: with correct sender and broadcastVal = some v,
    sendRecv = some w implies w = v. -/
theorem sendRecv_value_inv
    (s : State n Value)
    (hr : Reachable (brb n f Value sender) s)
    (hcorr : isCorrect n Value s sender)
    (hbv : (s.local_ sender).broadcastVal = some v)
    (dst : Fin n) (w : Value)
    (hrecv : (s.local_ dst).sendRecv = some w) :
    w = v := by
  sorry

/-- **Echoed value invariant**: with correct sender and broadcastVal = some v,
    if correct process q has echoed = some w, then w = v. -/
theorem echoed_value_inv
    (s : State n Value)
    (hr : Reachable (brb n f Value sender) s)
    (hcorr : isCorrect n Value s sender)
    (hbv : (s.local_ sender).broadcastVal = some v)
    (q : Fin n) (hq : isCorrect n Value s q) (w : Value)
    (hechoed : (s.local_ q).echoed = some w) :
    w = v := by
  sorry

end reachability_invariants

end BRB_LTS
