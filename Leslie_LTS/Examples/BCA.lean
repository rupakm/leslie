import Leslie_LTS.Framework
import Leslie_LTS.Examples.UtilityByzantine

/-! # Binding Crusader Agreement — LTS Formulation

  Binding Crusader Agreement for `n` processes with at most `f` Byzantine
  faults, where `n > 3f`. Decisions are in {0, 1, ⊥} with agreement,
  validity, and binding properties.
-/

open LTS

namespace BCA_LTS

/-! ### Messages -/

inductive MsgType where
  | init | echo | vote
  deriving DecidableEq

variable (T : Type)

/-- Protocol values: `some b` for binary, `none` for ⊥. -/
abbrev Val (T : Type) := Option T

/-- A protocol message. -/
structure Message (n : Nat) where
  src : Fin n
  dst : Fin n
  type : MsgType
  val : Val T
  deriving DecidableEq

/-! ### Local State -/

/-- Per-process local state. -/
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

/-! ### Global State -/

/-- The global system state. -/
structure State (n : Nat) where
  /-- Per-process local state. -/
  local_ : Fin n → LocalState T n
  /-- Network buffer: pending messages in transit. -/
  buffer : Message T n → Bool
  /-- List of corrupted (Byzantine) processes. -/
  corrupted : List (Fin n)

/-! ### Labels -/

/-- The labels of the BCA LTS. -/
inductive Label (n : Nat) where
  /-- The adversary corrupts a process. -/
  | corrupt (i : Fin n)
  /-- Process `src` sends a message of type `t` with value `v` to `dst`. -/
  | send (src dst : Fin n) (t : MsgType) (v : Val T)
  /-- Process `dst` receives a message of type `t` with value `v` from `src`. -/
  | recv (src dst : Fin n) (t : MsgType) (v : Val T)
  /-- Correct process `i` decides value `v`. -/
  | output (i : Fin n) (v : Val T)
  /-- The environment sets the input for process `i`. -/
  | input (i : Fin n) (v : T)

/-! ### Helpers -/

variable (n f : Nat) [DecidableEq T]

/-- A process is correct if it has not been corrupted. -/
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

/-- Threshold for input amplification: f + 1. -/
def amplifyThreshold : Nat := f + 1

/-- Threshold for approval: n − f. -/
def approveThreshold : Nat := n - f

/-- Threshold for echo quorum: n − f. -/
def echoThreshold : Nat := n - f

/-- Threshold for decision: n − f. -/
def returnThreshold : Nat := n - f

/-- Count of correct processes with input `b`. Concrete analog of
    `IdealBCA.inputSupport`. -/
def inputSupport (s : State T n) (b : T) : Nat :=
  ((List.finRange n).filter (fun p =>
    decide (p ∉ s.corrupted) && decide ((s.local_ p).input = some b))).length

/-- Count of correct processes (not corrupted). -/
def correctCount (s : State T n) : Nat :=
  ((List.finRange n).filter (fun p => decide (p ∉ s.corrupted))).length

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

/-! ### The BCA System as an LTS -/

/-- The BCA system as a labelled transition system. -/
def bca : System (State T n) (Label T n) where
  init := fun s =>
    (∀ p, s.local_ p = LocalState.init T n) ∧
    (∀ m, s.buffer m = false) ∧
    s.corrupted = []
  step := fun s lbl s' =>
    match lbl with
    | .corrupt i =>
        isCorrect T n s i ∧
        s.corrupted.length + 1 ≤ f ∧
        s' = { s with corrupted := i :: s.corrupted }
    | .input i v =>
        (s.local_ i).input = none ∧
        s' = { s with
          local_ := fun p => if p = i
            then { s.local_ i with input := some v }
            else s.local_ p }
    | .send src dst t mv =>
        (src ∈ s.corrupted ∨
         (isCorrect T n s src ∧ (s.local_ src).sent dst t mv = false ∧
           match t with
           | .init =>
             match mv with
             | some b =>
               (s.local_ src).input = some b ∨
               countInitRecv T n (s.local_ src) b ≥ amplifyThreshold f
             | none => False
           | .echo =>
             match mv with
             | some b =>
               (s.local_ src).approved b = true ∧
               ((s.local_ src).echoed = none ∨ (s.local_ src).echoed = some b)
             | none => False
           | .vote =>
             (∀ w, (s.local_ src).voted w = true → w = mv) ∧
             match mv with
             | some b =>
               countEchoRecv T n (s.local_ src) b ≥ echoThreshold n f
             | none =>
               ∃ v₁ v₂, v₁ ≠ v₂ ∧ (s.local_ src).approved v₁ = true ∧
                 (s.local_ src).approved v₂ = true)) ∧
        let msg : Message T n := ⟨src, dst, t, mv⟩
        s' = { s with
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
    | .recv src dst t mv =>
        s.buffer ⟨src, dst, t, mv⟩ = true ∧
        let msg : Message T n := ⟨src, dst, t, mv⟩
        let ls := s.local_ dst
        s' = { s with
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
                  approved := fun w => if w = b ∧
                    countInitRecv T n ls b + 1 ≥ approveThreshold n f
                    then true else ls.approved w }
                else ls
              | none => ls
            | .echo =>
              match mv with
              | some b =>
                if ls.echoRecv src b = false
                then { ls with
                  echoRecv := fun q w => if q = src ∧ w = b then true
                    else ls.echoRecv q w }
                else ls
              | none => ls
            | .vote =>
              if ls.voteRecv src mv = false
              then { ls with
                voteRecv := fun q w => if q = src ∧ w = mv then true
                  else ls.voteRecv q w }
              else ls
            else s.local_ p }
    | .output i mv =>
        isCorrect T n s i ∧
        (s.local_ i).decided = none ∧
        (match mv with
         | some b =>
           countVoteRecv T n (s.local_ i) (some b) ≥ returnThreshold n f
         | none =>
           (∃ v₁ v₂, v₁ ≠ v₂ ∧ (s.local_ i).approved v₁ = true ∧
             (s.local_ i).approved v₂ = true) ∧
           ∃ (vals : List (Val T)),
             countAnyVoteRecv T n (s.local_ i) vals ≥ returnThreshold n f) ∧
        s' = { s with
          local_ := fun p => if p = i
            then { s.local_ i with decided := some mv }
            else s.local_ p }

/-! ### Internal / External Labelling -/

/-- Internal/external labelling for BCA. -/
def bca_labelling [Inhabited T] [Inhabited (Fin n)] : Labelling (Label T n) where
  is_internal := fun l =>
    match l with
    | .corrupt _ => false
    | .send .. => true
    | .recv .. => true
    | .output _ _ => false
    | .input _ _ => false
  tau := .send default default .init default
  tau_internal := rfl

/-! ### Safety Properties -/

/-- No two correct processes decide different binary values. -/
def agreement (s : State T n) : Prop :=
  ∀ p q v w,
    isCorrect T n s p → isCorrect T n s q →
    (s.local_ p).decided = some (some v) →
    (s.local_ q).decided = some (some w) →
    v = w

/-- If all correct inputs are `v`, every correct decision is `v` or undecided. -/
def validity (v : T) (s : State T n) : Prop :=
  (∀ p, ¬isCorrect T n s p ∨ (s.local_ p).input = none ∨ (s.local_ p).input = some v) →
  ∀ p, (s.local_ p).decided = none ∨ (s.local_ p).decided = some (some v)

/-- Once any correct process decides, all future correct binary decisions agree. -/
def binding (sys : System (State T n) (Label T n)) : Prop :=
  ∀ s, Reachable sys s →
    (∃ p v, isCorrect T n s p ∧ (s.local_ p).decided = some v) →
    ∃ b : T, ∀ s', Star sys s s' →
      ∀ q w, isCorrect T n s' q →
        (s'.local_ q).decided = some (some w) → w = b

/-! ### Step Decomposition Helpers -/

section StepHelpers
variable {T : Type} [DecidableEq T] {n f : Nat}

private theorem send_local_eq {s : State T n} {src dst t mv} (p : Fin n) (hp : p ≠ src) :
    ({ s with
      buffer := fun m => if m = ⟨src, dst, t, mv⟩ then true else s.buffer m
      local_ := fun q => if q = src then
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
        else s.local_ q } : State T n).local_ p = s.local_ p := by
  simp [hp]

/-- Send does not change corrupted. -/
theorem send_corrupted {s s' : State T n} {src dst t mv}
    (h : (bca T n f).step s (.send src dst t mv) s') :
    s'.corrupted = s.corrupted := by
  obtain ⟨_, rfl⟩ := h; rfl

/-- Send does not change input. -/
theorem send_input {s s' : State T n} {src dst t mv}
    (h : (bca T n f).step s (.send src dst t mv) s') (p : Fin n) :
    (s'.local_ p).input = (s.local_ p).input := by
  obtain ⟨_, rfl⟩ := h; by_cases hp : p = src <;> simp [hp]

/-- Send does not change decided. -/
theorem send_decided {s s' : State T n} {src dst t mv}
    (h : (bca T n f).step s (.send src dst t mv) s') (p : Fin n) :
    (s'.local_ p).decided = (s.local_ p).decided := by
  obtain ⟨_, rfl⟩ := h; by_cases hp : p = src <;> simp [hp]

/-- Send init does not change echoed. -/
theorem send_init_echoed {s s' : State T n} {src dst mv}
    (h : (bca T n f).step s (.send src dst .init mv) s') (p : Fin n) :
    (s'.local_ p).echoed = (s.local_ p).echoed := by
  obtain ⟨_, rfl⟩ := h; by_cases hp : p = src <;> simp [hp]

/-- Send init does not change voted. -/
theorem send_init_voted {s s' : State T n} {src dst mv}
    (h : (bca T n f).step s (.send src dst .init mv) s') (p : Fin n) (w : Val T) :
    (s'.local_ p).voted w = (s.local_ p).voted w := by
  obtain ⟨_, rfl⟩ := h; by_cases hp : p = src <;> simp [hp]

/-- Recv does not change corrupted. -/
theorem recv_corrupted {s s' : State T n} {src dst t mv}
    (h : (bca T n f).step s (.recv src dst t mv) s') :
    s'.corrupted = s.corrupted := by
  obtain ⟨_, rfl⟩ := h; rfl

/-- Recv does not change the local state of any process other than dst. -/
theorem recv_local_other {s s' : State T n} {src dst t mv}
    (h : (bca T n f).step s (.recv src dst t mv) s') (p : Fin n) (hp : p ≠ dst) :
    s'.local_ p = s.local_ p := by
  obtain ⟨_, rfl⟩ := h; simp [hp]

/-- Recv init does not change echoed. -/
theorem recv_init_echoed {s s' : State T n} {src dst mv}
    (h : (bca T n f).step s (.recv src dst .init mv) s') (p : Fin n) :
    (s'.local_ p).echoed = (s.local_ p).echoed := by
  by_cases hp : p = dst
  · subst hp; obtain ⟨_, rfl⟩ := h; simp only
    rcases mv with _ | b <;> simp
    split <;> simp
  · rw [(recv_local_other h p hp)]

/-- Recv init does not change voted. -/
theorem recv_init_voted {s s' : State T n} {src dst mv}
    (h : (bca T n f).step s (.recv src dst .init mv) s') (p : Fin n) (w : Val T) :
    (s'.local_ p).voted w = (s.local_ p).voted w := by
  by_cases hp : p = dst
  · subst hp; obtain ⟨_, rfl⟩ := h; simp only
    rcases mv with _ | b <;> simp
    split <;> simp
  · rw [(recv_local_other h p hp)]

/-- Recv init does not change input. -/
theorem recv_init_input {s s' : State T n} {src dst mv}
    (h : (bca T n f).step s (.recv src dst .init mv) s') (p : Fin n) :
    (s'.local_ p).input = (s.local_ p).input := by
  by_cases hp : p = dst
  · subst hp; obtain ⟨_, rfl⟩ := h; simp only
    rcases mv with _ | b <;> simp
    split <;> simp
  · rw [(recv_local_other h p hp)]

/-- Recv init does not change decided. -/
theorem recv_init_decided {s s' : State T n} {src dst mv}
    (h : (bca T n f).step s (.recv src dst .init mv) s') (p : Fin n) :
    (s'.local_ p).decided = (s.local_ p).decided := by
  by_cases hp : p = dst
  · subst hp; obtain ⟨_, rfl⟩ := h; simp only
    rcases mv with _ | b <;> simp
    split <;> simp
  · rw [(recv_local_other h p hp)]

/-- Recv echo does not change echoed. -/
theorem recv_echo_echoed {s s' : State T n} {src dst mv}
    (h : (bca T n f).step s (.recv src dst .echo mv) s') (p : Fin n) :
    (s'.local_ p).echoed = (s.local_ p).echoed := by
  by_cases hp : p = dst
  · subst hp; obtain ⟨_, rfl⟩ := h; simp only
    rcases mv with _ | b <;> simp
    split <;> simp
  · rw [(recv_local_other h p hp)]

/-- Recv echo does not change voted. -/
theorem recv_echo_voted {s s' : State T n} {src dst mv}
    (h : (bca T n f).step s (.recv src dst .echo mv) s') (p : Fin n) (w : Val T) :
    (s'.local_ p).voted w = (s.local_ p).voted w := by
  by_cases hp : p = dst
  · subst hp; obtain ⟨_, rfl⟩ := h; simp only
    rcases mv with _ | b <;> simp
    split <;> simp
  · rw [(recv_local_other h p hp)]

/-- Recv echo does not change input. -/
theorem recv_echo_input {s s' : State T n} {src dst mv}
    (h : (bca T n f).step s (.recv src dst .echo mv) s') (p : Fin n) :
    (s'.local_ p).input = (s.local_ p).input := by
  by_cases hp : p = dst
  · subst hp; obtain ⟨_, rfl⟩ := h; simp only
    rcases mv with _ | b <;> simp
    split <;> simp
  · rw [(recv_local_other h p hp)]

/-- Recv echo does not change decided. -/
theorem recv_echo_decided {s s' : State T n} {src dst mv}
    (h : (bca T n f).step s (.recv src dst .echo mv) s') (p : Fin n) :
    (s'.local_ p).decided = (s.local_ p).decided := by
  by_cases hp : p = dst
  · subst hp; obtain ⟨_, rfl⟩ := h; simp only
    rcases mv with _ | b <;> simp
    split <;> simp
  · rw [(recv_local_other h p hp)]

/-- Recv vote does not change echoed. -/
theorem recv_vote_echoed {s s' : State T n} {src dst mv}
    (h : (bca T n f).step s (.recv src dst .vote mv) s') (p : Fin n) :
    (s'.local_ p).echoed = (s.local_ p).echoed := by
  by_cases hp : p = dst
  · subst hp; obtain ⟨_, rfl⟩ := h; simp
    split <;> simp
  · rw [(recv_local_other h p hp)]

/-- Recv vote does not change voted. -/
theorem recv_vote_voted {s s' : State T n} {src dst mv}
    (h : (bca T n f).step s (.recv src dst .vote mv) s') (p : Fin n) (w : Val T) :
    (s'.local_ p).voted w = (s.local_ p).voted w := by
  by_cases hp : p = dst
  · subst hp; obtain ⟨_, rfl⟩ := h; simp
    split <;> simp
  · rw [(recv_local_other h p hp)]

/-- Recv vote does not change input. -/
theorem recv_vote_input {s s' : State T n} {src dst mv}
    (h : (bca T n f).step s (.recv src dst .vote mv) s') (p : Fin n) :
    (s'.local_ p).input = (s.local_ p).input := by
  by_cases hp : p = dst
  · subst hp; obtain ⟨_, rfl⟩ := h; simp
    split <;> simp
  · rw [(recv_local_other h p hp)]

/-- Recv vote does not change decided. -/
theorem recv_vote_decided {s s' : State T n} {src dst mv}
    (h : (bca T n f).step s (.recv src dst .vote mv) s') (p : Fin n) :
    (s'.local_ p).decided = (s.local_ p).decided := by
  by_cases hp : p = dst
  · subst hp; obtain ⟨_, rfl⟩ := h; simp
    split <;> simp
  · rw [(recv_local_other h p hp)]

/-- Send echo does not change voted. -/
theorem send_echo_voted {s s' : State T n} {src dst mv}
    (h : (bca T n f).step s (.send src dst .echo mv) s') (p : Fin n) (w : Val T) :
    (s'.local_ p).voted w = (s.local_ p).voted w := by
  obtain ⟨_, rfl⟩ := h; by_cases hp : p = src <;> simp [hp]

/-- Send echo: echoed of p ≠ src is unchanged. -/
theorem send_echo_echoed_other {s s' : State T n} {src dst mv}
    (h : (bca T n f).step s (.send src dst .echo mv) s') (p : Fin n) (hp : p ≠ src) :
    (s'.local_ p).echoed = (s.local_ p).echoed := by
  obtain ⟨_, rfl⟩ := h; simp [hp]

/-- Send echo(some b): correct sender's echoed becomes some b. -/
theorem send_echo_echoed_correct {s s' : State T n} {src dst b}
    (h : (bca T n f).step s (.send src dst .echo (some b)) s')
    (hcorr : isCorrect T n s src) :
    (s'.local_ src).echoed = some b := by
  obtain ⟨_, rfl⟩ := h; simp [isCorrect] at hcorr; simp [hcorr]

/-- Send echo(some b): byzantine sender's echoed is unchanged. -/
theorem send_echo_echoed_byzantine {s s' : State T n} {src dst b}
    (h : (bca T n f).step s (.send src dst .echo (some b)) s')
    (hbyz : src ∈ s.corrupted) :
    (s'.local_ src).echoed = (s.local_ src).echoed := by
  obtain ⟨_, rfl⟩ := h; simp [hbyz]

/-- Send echo(none): echoed is unchanged. -/
theorem send_echo_none_echoed {s s' : State T n} {src dst}
    (h : (bca T n f).step s (.send src dst .echo none) s') (p : Fin n) :
    (s'.local_ p).echoed = (s.local_ p).echoed := by
  obtain ⟨_, rfl⟩ := h; by_cases hp : p = src <;> simp [hp]

/-- Send vote does not change echoed. -/
theorem send_vote_echoed {s s' : State T n} {src dst mv}
    (h : (bca T n f).step s (.send src dst .vote mv) s') (p : Fin n) :
    (s'.local_ p).echoed = (s.local_ p).echoed := by
  obtain ⟨_, rfl⟩ := h; by_cases hp : p = src <;> simp [hp]

/-- Send vote: voted of p ≠ src is unchanged. -/
theorem send_vote_voted_other {s s' : State T n} {src dst mv}
    (h : (bca T n f).step s (.send src dst .vote mv) s') (p : Fin n) (hp : p ≠ src)
    (w : Val T) :
    (s'.local_ p).voted w = (s.local_ p).voted w := by
  obtain ⟨_, rfl⟩ := h; simp [hp]

/-- Send vote: if src is byzantine, voted src is unchanged. -/
theorem send_vote_voted_byzantine {s s' : State T n} {src dst mv}
    (h : (bca T n f).step s (.send src dst .vote mv) s')
    (hbyz : src ∈ s.corrupted) (w : Val T) :
    (s'.local_ src).voted w = (s.local_ src).voted w := by
  obtain ⟨_, rfl⟩ := h; simp [hbyz]

/-- Send vote: if src is correct, voted src mv becomes true. -/
theorem send_vote_voted_correct {s s' : State T n} {src dst mv}
    (h : (bca T n f).step s (.send src dst .vote mv) s')
    (hcorr : isCorrect T n s src) :
    (s'.local_ src).voted mv = true := by
  obtain ⟨_, rfl⟩ := h; simp [isCorrect] at hcorr; simp [hcorr]

/-- Send vote: if src is correct and w ≠ mv, voted src w is unchanged. -/
theorem send_vote_voted_correct_other {s s' : State T n} {src dst mv}
    (h : (bca T n f).step s (.send src dst .vote mv) s')
    (hcorr : isCorrect T n s src) (w : Val T) (hw : w ≠ mv) :
    (s'.local_ src).voted w = (s.local_ src).voted w := by
  obtain ⟨_, rfl⟩ := h; simp [isCorrect] at hcorr; simp [hcorr, hw]

/-- Input does not change corrupted. -/
theorem input_corrupted {s s' : State T n} {i v}
    (h : (bca T n f).step s (.input i v) s') :
    s'.corrupted = s.corrupted := by
  obtain ⟨_, rfl⟩ := h; rfl

/-- Input: the old input was none. -/
theorem input_was_none {s s' : State T n} {i v}
    (h : (bca T n f).step s (.input i v) s') :
    (s.local_ i).input = none := by
  exact h.1

/-- Input does not change echoed. -/
theorem input_echoed {s s' : State T n} {i v}
    (h : (bca T n f).step s (.input i v) s') (p : Fin n) :
    (s'.local_ p).echoed = (s.local_ p).echoed := by
  obtain ⟨_, rfl⟩ := h; by_cases hp : p = i <;> simp [hp]

/-- Input does not change voted. -/
theorem input_voted {s s' : State T n} {i v}
    (h : (bca T n f).step s (.input i v) s') (p : Fin n) (w : Val T) :
    (s'.local_ p).voted w = (s.local_ p).voted w := by
  obtain ⟨_, rfl⟩ := h; by_cases hp : p = i <;> simp [hp]

/-- Input does not change decided. -/
theorem input_decided {s s' : State T n} {i v}
    (h : (bca T n f).step s (.input i v) s') (p : Fin n) :
    (s'.local_ p).decided = (s.local_ p).decided := by
  obtain ⟨_, rfl⟩ := h; by_cases hp : p = i <;> simp [hp]

/-- Input: new input for process i. -/
theorem input_input_self {s s' : State T n} {i v}
    (h : (bca T n f).step s (.input i v) s') :
    (s'.local_ i).input = some v := by
  obtain ⟨_, rfl⟩ := h; simp

/-- Input: input for other processes unchanged. -/
theorem input_input_other {s s' : State T n} {i v}
    (h : (bca T n f).step s (.input i v) s') (p : Fin n) (hp : p ≠ i) :
    (s'.local_ p).input = (s.local_ p).input := by
  obtain ⟨_, rfl⟩ := h; simp [hp]

/-- Corrupt: state decomposition. -/
theorem corrupt_eq {s s' : State T n} {i}
    (h : (bca T n f).step s (.corrupt i) s') :
    s' = { s with corrupted := i :: s.corrupted } := by
  obtain ⟨_, _, rfl⟩ := h; rfl

/-- Corrupt: isCorrect guard. -/
theorem corrupt_isCorrect {s s' : State T n} {i}
    (h : (bca T n f).step s (.corrupt i) s') :
    isCorrect T n s i := by
  exact h.1

/-- Corrupt: budget guard. -/
theorem corrupt_budget {s s' : State T n} {i}
    (h : (bca T n f).step s (.corrupt i) s') :
    s.corrupted.length + 1 ≤ f := by
  exact h.2.1

/-- Corrupt does not change local state. -/
theorem corrupt_local {s s' : State T n} {i}
    (h : (bca T n f).step s (.corrupt i) s') (p : Fin n) :
    s'.local_ p = s.local_ p := by
  obtain ⟨_, _, rfl⟩ := h; rfl

/-- Output: isCorrect guard. -/
theorem output_isCorrect {s s' : State T n} {i mv}
    (h : (bca T n f).step s (.output i mv) s') :
    isCorrect T n s i := by
  exact h.1

/-- Output: decided was none. -/
theorem output_decided_none {s s' : State T n} {i mv}
    (h : (bca T n f).step s (.output i mv) s') :
    (s.local_ i).decided = none := by
  exact h.2.1

/-- Output does not change corrupted. -/
theorem output_corrupted {s s' : State T n} {i mv}
    (h : (bca T n f).step s (.output i mv) s') :
    s'.corrupted = s.corrupted := by
  obtain ⟨_, _, _, rfl⟩ := h; rfl

/-- Output does not change echoed. -/
theorem output_echoed {s s' : State T n} {i mv}
    (h : (bca T n f).step s (.output i mv) s') (p : Fin n) :
    (s'.local_ p).echoed = (s.local_ p).echoed := by
  obtain ⟨_, _, _, rfl⟩ := h; by_cases hp : p = i <;> simp [hp]

/-- Output does not change voted. -/
theorem output_voted {s s' : State T n} {i mv}
    (h : (bca T n f).step s (.output i mv) s') (p : Fin n) (w : Val T) :
    (s'.local_ p).voted w = (s.local_ p).voted w := by
  obtain ⟨_, _, _, rfl⟩ := h; by_cases hp : p = i <;> simp [hp]

/-- Output does not change input. -/
theorem output_input {s s' : State T n} {i mv}
    (h : (bca T n f).step s (.output i mv) s') (p : Fin n) :
    (s'.local_ p).input = (s.local_ p).input := by
  obtain ⟨_, _, _, rfl⟩ := h; by_cases hp : p = i <;> simp [hp]

/-- Output: decided of i is set. -/
theorem output_decided_self {s s' : State T n} {i mv}
    (h : (bca T n f).step s (.output i mv) s') :
    (s'.local_ i).decided = some mv := by
  obtain ⟨_, _, _, rfl⟩ := h; simp

/-- Output: decided of other processes unchanged. -/
theorem output_decided_other {s s' : State T n} {i mv}
    (h : (bca T n f).step s (.output i mv) s') (p : Fin n) (hp : p ≠ i) :
    (s'.local_ p).decided = (s.local_ p).decided := by
  obtain ⟨_, _, _, rfl⟩ := h; simp [hp]

/-- Send preserves buffer modulo the new message. -/
theorem send_buffer {s s' : State T n} {src dst t mv}
    (h : (bca T n f).step s (.send src dst t mv) s')
    (m : Message T n) (hm : s'.buffer m = true) :
    m = ⟨src, dst, t, mv⟩ ∨ s.buffer m = true := by
  obtain ⟨_, rfl⟩ := h; simp only at hm
  by_cases hmeq : m = ⟨src, dst, t, mv⟩
  · left; exact hmeq
  · right; simp only [hmeq] at hm; exact hm

/-- Send: the sent field. For the sender, it's updated with the new message. -/
theorem send_sent {s s' : State T n} {src dst t mv}
    (h : (bca T n f).step s (.send src dst t mv) s')
    (d : Fin n) (tt : MsgType) (ww : Val T) :
    (s'.local_ src).sent d tt ww =
      (if d = dst ∧ tt = t ∧ ww = mv then true
       else (s.local_ src).sent d tt ww) := by
  obtain ⟨_, rfl⟩ := h; simp

/-- Send: sent field for a different sender is unchanged. -/
theorem send_sent_other {s s' : State T n} {src dst t mv}
    (h : (bca T n f).step s (.send src dst t mv) s')
    (p : Fin n) (hp : p ≠ src) (d : Fin n) (tt : MsgType) (ww : Val T) :
    (s'.local_ p).sent d tt ww = (s.local_ p).sent d tt ww := by
  obtain ⟨_, rfl⟩ := h; simp [hp]

/-- Send: buffer is monotone (existing entries preserved). -/
theorem send_buffer_mono {s s' : State T n} {src dst t mv}
    (h : (bca T n f).step s (.send src dst t mv) s')
    (m : Message T n) (hm : s.buffer m = true) :
    s'.buffer m = true := by
  obtain ⟨_, rfl⟩ := h; simp only
  by_cases hmeq : m = ⟨src, dst, t, mv⟩ <;> simp [hmeq, hm]

/-- After send, the sent message is in the buffer. -/
theorem send_buffer_new {s s' : State T n} {src dst t mv}
    (h : (bca T n f).step s (.send src dst t mv) s') :
    s'.buffer ⟨src, dst, t, mv⟩ = true := by
  obtain ⟨_, rfl⟩ := h; simp

/-- Recv echo: buffer preservation. -/
theorem recv_echo_buffer {s s' : State T n} {src dst b}
    (h : (bca T n f).step s (.recv src dst .echo (some b)) s')
    (m : Message T n) (hm : s'.buffer m = true) :
    m = ⟨src, dst, .echo, some b⟩ ∨ s.buffer m = true := by
  obtain ⟨_, rfl⟩ := h; simp only at hm; by_cases hmeq : m = ⟨src, dst, .echo, some b⟩
  · left; exact hmeq
  · right; simp only [hmeq] at hm; exact hm

/-- Corrupt does not change the buffer. -/
theorem corrupt_buffer {s s' : State T n} {i}
    (h : (bca T n f).step s (.corrupt i) s') :
    s'.buffer = s.buffer := by
  obtain ⟨_, _, rfl⟩ := h; rfl

/-- Output does not change the buffer. -/
theorem output_buffer {s s' : State T n} {i mv}
    (h : (bca T n f).step s (.output i mv) s') :
    s'.buffer = s.buffer := by
  obtain ⟨_, _, _, rfl⟩ := h; rfl

/-- Input does not change the sent field. -/
theorem input_sent {s s' : State T n} {i v}
    (h : (bca T n f).step s (.input i v) s') (p : Fin n)
    (d : Fin n) (t : MsgType) (w : Val T) :
    (s'.local_ p).sent d t w = (s.local_ p).sent d t w := by
  obtain ⟨_, rfl⟩ := h; by_cases hp : p = i <;> simp [hp]

/-- Output does not change the sent field. -/
theorem output_sent {s s' : State T n} {i mv}
    (h : (bca T n f).step s (.output i mv) s') (p : Fin n)
    (d : Fin n) (t : MsgType) (w : Val T) :
    (s'.local_ p).sent d t w = (s.local_ p).sent d t w := by
  obtain ⟨_, _, _, rfl⟩ := h; by_cases hp : p = i <;> simp [hp]

/-- Input does not change the buffer. -/
theorem input_buffer {s s' : State T n} {i v}
    (h : (bca T n f).step s (.input i v) s') :
    s'.buffer = s.buffer := by
  obtain ⟨_, rfl⟩ := h; rfl

/-- Recv init: buffer preservation. -/
theorem recv_init_buffer {s s' : State T n} {src dst mv}
    (h : (bca T n f).step s (.recv src dst .init mv) s')
    (m : Message T n) (hm : s'.buffer m = true) :
    m = ⟨src, dst, .init, mv⟩ ∨ s.buffer m = true := by
  obtain ⟨_, rfl⟩ := h; simp only at hm
  by_cases hmeq : m = ⟨src, dst, .init, mv⟩
  · left; exact hmeq
  · right; simp only [hmeq] at hm; exact hm

/-- Recv vote: buffer preservation. -/
theorem recv_vote_buffer {s s' : State T n} {src dst mv}
    (h : (bca T n f).step s (.recv src dst .vote mv) s')
    (m : Message T n) (hm : s'.buffer m = true) :
    m = ⟨src, dst, .vote, mv⟩ ∨ s.buffer m = true := by
  obtain ⟨_, rfl⟩ := h; simp only at hm
  by_cases hmeq : m = ⟨src, dst, .vote, mv⟩
  · left; exact hmeq
  · right; simp only [hmeq] at hm; exact hm

/-- Echoed is persistent for correct processes. -/
theorem step_echoed_persist {s s' : State T n} {l : Label T n}
    (h : (bca T n f).step s l s') (p : Fin n) (b : T)
    (hcorr : isCorrect T n s' p)
    (hechoed : (s.local_ p).echoed = some b) :
    (s'.local_ p).echoed = some b := by
  match l with
  | .corrupt _ => rw [corrupt_local h]; exact hechoed
  | .send src dst .init mv => rw [send_init_echoed h]; exact hechoed
  | .send src dst .echo mv =>
    by_cases hp : p = src
    · subst hp
      rcases mv with _ | b'
      · rw [send_echo_none_echoed h]; exact hechoed
      · have hcorr' : isCorrect T n s p := by
          simp only [isCorrect] at hcorr ⊢; rwa [← send_corrupted h]
        have heo : (s.local_ p).echoed = none ∨ (s.local_ p).echoed = some b' := by
          obtain ⟨hgate, _⟩ := h
          rcases hgate with hbyz | ⟨_, _, _, heo⟩
          · exact absurd hbyz hcorr'
          · exact heo
        rcases heo with hn | hs
        · rw [hechoed] at hn; exact absurd hn (by simp)
        · rw [hechoed] at hs
          rw [send_echo_echoed_correct h hcorr', (Option.some.inj hs).symm]
    · rw [send_echo_echoed_other h p hp]; exact hechoed
  | .send src dst .vote mv => rw [send_vote_echoed h]; exact hechoed
  | .recv src dst .init mv => rw [recv_init_echoed h]; exact hechoed
  | .recv src dst .echo mv => rw [recv_echo_echoed h]; exact hechoed
  | .recv src dst .vote mv => rw [recv_vote_echoed h]; exact hechoed
  | .output _ _ => rw [output_echoed h]; exact hechoed
  | .input _ _ => rw [input_echoed h]; exact hechoed

/-- Correct in post-state implies correct in pre-state. -/
theorem step_correct_prev {s s' : State T n} {l : Label T n}
    (h : (bca T n f).step s l s') (p : Fin n)
    (hcorr : isCorrect T n s' p) :
    isCorrect T n s p := by
  simp only [isCorrect] at hcorr ⊢
  match l with
  | .corrupt i =>
    rw [corrupt_eq h] at hcorr; simp only [List.mem_cons, not_or] at hcorr;
    exact hcorr.2
  | .send .. => rwa [← send_corrupted h]
  | .recv .. => rwa [← recv_corrupted h]
  | .output .. => rwa [← output_corrupted h]
  | .input .. => rwa [← input_corrupted h]

/-- echoRecv traced to previous state. -/
theorem step_echoRecv_prev {s s' : State T n} {l : Label T n}
    (h : (bca T n f).step s l s') (p q : Fin n) (b : T)
    (hrecv : (s'.local_ p).echoRecv q b = true)
    (hnot_recv : ∀ dst, l ≠ .recv q dst .echo (some b)) :
    (s.local_ p).echoRecv q b = true := by
  match l with
  | .corrupt _ => rwa [corrupt_local h] at hrecv
  | .send src dst t mv =>
    by_cases hp : p = src
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only at hrecv; exact hrecv
    · obtain ⟨_, rfl⟩ := h; simp only [hp] at hrecv; exact hrecv
  | .recv src dst .echo (some bv) =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only at hrecv
      by_cases hdup : (s.local_ p).echoRecv src bv = false
      · simp only [hdup] at hrecv
        by_cases hqb : q = src ∧ b = bv
        · obtain ⟨rfl, rfl⟩ := hqb; exfalso; exact hnot_recv p rfl
        · simp only [↓reduceIte, Bool.if_true_left, Bool.decide_and, Bool.or_eq_true,
          Bool.and_eq_true, decide_eq_true_eq, hqb, false_or] at hrecv; exact hrecv
      · simp only [hdup] at hrecv; exact hrecv
    · rw [recv_local_other h p hp] at hrecv; exact hrecv
  | .recv src dst .echo none =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only at hrecv; exact hrecv
    · rw [recv_local_other h p hp] at hrecv; exact hrecv
  | .recv src dst .init mv =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only at hrecv
      rcases mv with _ | bv <;> simp only at hrecv
      · exact hrecv
      · by_cases hdup : (s.local_ p).initRecv src bv = false
        · simp only [hdup] at hrecv; exact hrecv
        · simp only [hdup] at hrecv; exact hrecv
    · rw [recv_local_other h p hp] at hrecv; exact hrecv
  | .recv src dst .vote mv =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only at hrecv
      by_cases hdup : (s.local_ p).voteRecv src mv = false
      · simp only [hdup] at hrecv; exact hrecv
      · simp only [hdup] at hrecv; exact hrecv
    · rw [recv_local_other h p hp] at hrecv; exact hrecv
  | .output i mv =>
    by_cases hp : p = i
    · subst hp; obtain ⟨_, _, _, rfl⟩ := h; simp only at hrecv; exact hrecv
    · obtain ⟨_, _, _, rfl⟩ := h; simp only [hp] at hrecv; exact hrecv
  | .input i v =>
    by_cases hp : p = i
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only at hrecv; exact hrecv
    · obtain ⟨_, rfl⟩ := h; simp only [hp] at hrecv; exact hrecv

/-- Send echo gate for a correct sender. -/
theorem send_echo_gate {s s' : State T n} {src dst b}
    (h : (bca T n f).step s (.send src dst .echo (some b)) s')
    (hcorr : isCorrect T n s src) :
    (s.local_ src).approved b = true ∧
    ((s.local_ src).echoed = none ∨ (s.local_ src).echoed = some b) := by
  obtain ⟨hgate, _⟩ := h
  rcases hgate with hbyz | ⟨_, _, happr, heo⟩
  · exact absurd hbyz hcorr
  · exact ⟨happr, heo⟩

/-- voted(some b) is persistent for correct processes. -/
theorem step_voted_persist {s s' : State T n} {l : Label T n}
    (h : (bca T n f).step s l s') (p : Fin n) (b : T)
    (hcorr : isCorrect T n s' p)
    (hvoted : (s.local_ p).voted (some b) = true) :
    (s'.local_ p).voted (some b) = true := by
  match l with
  | .corrupt _ => rw [corrupt_local h]; exact hvoted
  | .send src dst .init mv =>
    rw [send_init_voted h p]; exact hvoted
  | .send src dst .echo mv =>
    rw [send_echo_voted h p]; exact hvoted
  | .send src dst .vote mv =>
    by_cases hp : p = src
    · subst hp
      have hcorr' : isCorrect T n s p := by
        simp only [isCorrect] at hcorr ⊢; rwa [← send_corrupted h]
      rcases h.1 with hbyz | ⟨_, _, huniq, _⟩
      · exact absurd hbyz hcorr'
      · have := huniq _ hvoted; subst this
        exact send_vote_voted_correct h hcorr'
    · rw [send_vote_voted_other h p hp]; exact hvoted
  | .recv _ _ .init _ => rw [recv_init_voted h p]; exact hvoted
  | .recv _ _ .echo _ => rw [recv_echo_voted h p]; exact hvoted
  | .recv _ _ .vote _ => rw [recv_vote_voted h p]; exact hvoted
  | .output .. => rw [output_voted h p]; exact hvoted
  | .input .. => rw [input_voted h p]; exact hvoted

/-- voted(none) is persistent for correct processes. -/
theorem step_voted_none_persist {s s' : State T n} {l : Label T n}
    (h : (bca T n f).step s l s') (p : Fin n)
    (hcorr : isCorrect T n s' p)
    (hvoted : (s.local_ p).voted none = true) :
    (s'.local_ p).voted none = true := by
  match l with
  | .corrupt _ => rw [corrupt_local h]; exact hvoted
  | .send src dst .init mv => rw [send_init_voted h p]; exact hvoted
  | .send src dst .echo mv => rw [send_echo_voted h p]; exact hvoted
  | .send src dst .vote mv =>
    by_cases hp : p = src
    · subst hp
      have hcorr' : isCorrect T n s p := by
        simp only [isCorrect] at hcorr ⊢; rwa [← send_corrupted h]
      rcases h.1 with hbyz | ⟨_, _, huniq, _⟩
      · exact absurd hbyz hcorr'
      · have := huniq _ hvoted; subst this
        exact send_vote_voted_correct h hcorr'
    · rw [send_vote_voted_other h p hp]; exact hvoted
  | .recv _ _ .init _ => rw [recv_init_voted h p]; exact hvoted
  | .recv _ _ .echo _ => rw [recv_echo_voted h p]; exact hvoted
  | .recv _ _ .vote _ => rw [recv_vote_voted h p]; exact hvoted
  | .output .. => rw [output_voted h p]; exact hvoted
  | .input .. => rw [input_voted h p]; exact hvoted

/-- voteRecv(some b) traced to previous state. -/
theorem step_voteRecv_prev {s s' : State T n} {l : Label T n}
    (h : (bca T n f).step s l s') (p q : Fin n) (b : T)
    (hrecv : (s'.local_ p).voteRecv q (some b) = true)
    (hnot_recv : ∀ dst, l ≠ .recv q dst .vote (some b)) :
    (s.local_ p).voteRecv q (some b) = true := by
  match l with
  | .corrupt _ => rwa [corrupt_local h] at hrecv
  | .send src dst t mv =>
    by_cases hp : p = src
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only at hrecv; exact hrecv
    · obtain ⟨_, rfl⟩ := h; simp only [hp] at hrecv; exact hrecv
  | .recv src dst .vote mv =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only at hrecv
      by_cases hdup : (s.local_ p).voteRecv src mv = false
      · simp only [hdup] at hrecv
        by_cases hqb : q = src ∧ (some b : Val T) = mv
        · obtain ⟨rfl, rfl⟩ := hqb; exfalso; exact hnot_recv p rfl
        · simp only [↓reduceIte, Bool.if_true_left, Bool.decide_and, Bool.or_eq_true,
          Bool.and_eq_true, decide_eq_true_eq, hqb, false_or] at hrecv; exact hrecv
      · simp only [hdup] at hrecv; exact hrecv
    · rw [recv_local_other h p hp] at hrecv; exact hrecv
  | .recv src dst .echo mv =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only at hrecv
      rcases mv with _ | bv <;> simp only at hrecv
      · exact hrecv
      · by_cases hdup : (s.local_ p).echoRecv src bv = false
        · simp only [hdup] at hrecv; exact hrecv
        · simp only [hdup] at hrecv; exact hrecv
    · rw [recv_local_other h p hp] at hrecv; exact hrecv
  | .recv src dst .init mv =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only at hrecv
      rcases mv with _ | bv <;> simp only at hrecv
      · exact hrecv
      · by_cases hdup : (s.local_ p).initRecv src bv = false
        · simp only [hdup] at hrecv; exact hrecv
        · simp only [hdup] at hrecv; exact hrecv
    · rw [recv_local_other h p hp] at hrecv; exact hrecv
  | .output i mv =>
    by_cases hp : p = i
    · subst hp; obtain ⟨_, _, _, rfl⟩ := h; simp only at hrecv; exact hrecv
    · obtain ⟨_, _, _, rfl⟩ := h; simp only [hp] at hrecv; exact hrecv
  | .input i v =>
    by_cases hp : p = i
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only at hrecv; exact hrecv
    · obtain ⟨_, rfl⟩ := h; simp only [hp] at hrecv; exact hrecv

/-- voteRecv(none) traced to previous state. -/
theorem step_voteRecv_none_prev {s s' : State T n} {l : Label T n}
    (h : (bca T n f).step s l s') (p q : Fin n)
    (hrecv : (s'.local_ p).voteRecv q none = true)
    (hnot_recv : ∀ dst, l ≠ .recv q dst .vote none) :
    (s.local_ p).voteRecv q none = true := by
  match l with
  | .corrupt _ => rwa [corrupt_local h] at hrecv
  | .send src dst t mv =>
    by_cases hp : p = src
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only at hrecv; exact hrecv
    · obtain ⟨_, rfl⟩ := h; simp only [hp] at hrecv; exact hrecv
  | .recv src dst .vote mv =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only at hrecv
      by_cases hdup : (s.local_ p).voteRecv src mv = false
      · simp only [hdup] at hrecv
        by_cases hqb : q = src ∧ (none : Val T) = mv
        · obtain ⟨rfl, rfl⟩ := hqb; exfalso; exact hnot_recv p rfl
        · simp only [↓reduceIte, Bool.if_true_left, Bool.decide_and, Bool.or_eq_true,
          Bool.and_eq_true, decide_eq_true_eq, hqb, false_or] at hrecv; exact hrecv
      · simp only [hdup] at hrecv; exact hrecv
    · rw [recv_local_other h p hp] at hrecv; exact hrecv
  | .recv src dst .echo mv =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only at hrecv
      rcases mv with _ | bv <;> simp only at hrecv
      · exact hrecv
      · by_cases hdup : (s.local_ p).echoRecv src bv = false
        · simp only [hdup] at hrecv; exact hrecv
        · simp only [hdup] at hrecv; exact hrecv
    · rw [recv_local_other h p hp] at hrecv; exact hrecv
  | .recv src dst .init mv =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only at hrecv
      rcases mv with _ | bv <;> simp only at hrecv
      · exact hrecv
      · by_cases hdup : (s.local_ p).initRecv src bv = false
        · simp only [hdup] at hrecv; exact hrecv
        · simp only [hdup] at hrecv; exact hrecv
    · rw [recv_local_other h p hp] at hrecv; exact hrecv
  | .output i mv =>
    by_cases hp : p = i
    · subst hp; obtain ⟨_, _, _, rfl⟩ := h; simp only at hrecv; exact hrecv
    · obtain ⟨_, _, _, rfl⟩ := h; simp only [hp] at hrecv; exact hrecv
  | .input i v =>
    by_cases hp : p = i
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only at hrecv; exact hrecv
    · obtain ⟨_, rfl⟩ := h; simp only [hp] at hrecv; exact hrecv

/-- initRecv is monotone. -/
theorem step_initRecv_mono {s s' : State T n} {l : Label T n}
    (h : (bca T n f).step s l s') (p q : Fin n) (b : T)
    (hrecv : (s.local_ p).initRecv q b = true) :
    (s'.local_ p).initRecv q b = true := by
  match l with
  | .corrupt _ => rw [corrupt_local h]; exact hrecv
  | .send src dst t mv =>
    by_cases hp : p = src
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only; exact hrecv
    · obtain ⟨_, rfl⟩ := h; simp only [hp]; exact hrecv
  | .recv src dst .init mv =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only
      rcases mv with _ | bv <;> simp only
      · exact hrecv
      · by_cases hdup : (s.local_ p).initRecv src bv = false
        · simp [hdup]; by_cases hqb : q = src ∧ b = bv <;> simp [hqb, hrecv]
        · simp only [hdup]; exact hrecv
    · rw [show s'.local_ p = s.local_ p from recv_local_other h p hp]; exact hrecv
  | .recv src dst .echo mv =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only
      rcases mv with _ | bv <;> simp only
      · exact hrecv
      · by_cases hdup : (s.local_ p).echoRecv src bv = false
        · simp only [hdup]; exact hrecv
        · simp only [hdup]; exact hrecv
    · rw [show s'.local_ p = s.local_ p from recv_local_other h p hp]; exact hrecv
  | .recv src dst .vote mv =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only
      by_cases hdup : (s.local_ p).voteRecv src mv = false
      · simp only [hdup]; exact hrecv
      · simp only [hdup]; exact hrecv
    · rw [show s'.local_ p = s.local_ p from recv_local_other h p hp]; exact hrecv
  | .output i mv =>
    by_cases hp : p = i
    · subst hp; obtain ⟨_, _, _, rfl⟩ := h; simp only; exact hrecv
    · obtain ⟨_, _, _, rfl⟩ := h; simp only [hp]; exact hrecv
  | .input i v =>
    by_cases hp : p = i
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only; exact hrecv
    · obtain ⟨_, rfl⟩ := h; simp only [hp]; exact hrecv

/-- countInitRecv is monotone. -/
theorem step_countInitRecv_mono {s s' : State T n} {l : Label T n}
    (h : (bca T n f).step s l s') (p : Fin n) (b : T) :
    countInitRecv T n (s.local_ p) b ≤ countInitRecv T n (s'.local_ p) b := by
  unfold countInitRecv
  apply filter_length_mono; intro q hq; simp only at hq ⊢
  exact step_initRecv_mono h p q b hq

/-- Recv init with a new entry increments countInitRecv by at least 1. -/
theorem recv_init_countInitRecv_inc {s s' : State T n} {src dst : Fin n} {b : T}
    (h : (bca T n f).step s (.recv src dst .init (some b)) s')
    (hdup : (s.local_ dst).initRecv src b = false) :
    countInitRecv T n (s'.local_ dst) b ≥ countInitRecv T n (s.local_ dst) b + 1 := by
  have hmono := step_countInitRecv_mono h dst b
  have hsrc_new : (s'.local_ dst).initRecv src b = true := by
    obtain ⟨_, rfl⟩ := h; simp [hdup]
  have hsrc_old : (s.local_ dst).initRecv src b = false := hdup
  unfold countInitRecv at hmono ⊢
  have hsplit := filter_split
    (fun q : Fin n => (s'.local_ dst).initRecv q b)
    (fun q : Fin n => !decide (q = src))
    (List.finRange n)
  have hone : ((List.finRange n).filter (fun q =>
      (s'.local_ dst).initRecv q b && !!decide (q = src))).length ≥ 1 := by
    have : src ∈ (List.finRange n).filter (fun q =>
        (s'.local_ dst).initRecv q b && !!decide (q = src)) := by
      simp [List.mem_filter, List.mem_finRange, hsrc_new, Bool.not_not]
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (List.length_pos_of_mem this)
  have hrest : ((List.finRange n).filter (fun q =>
      (s.local_ dst).initRecv q b)).length ≤
    ((List.finRange n).filter (fun q =>
      (s'.local_ dst).initRecv q b && !decide (q = src))).length := by
    apply filter_length_mono; intro q hq; simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_false_iff_not] at hq ⊢
    exact ⟨step_initRecv_mono h dst q b hq, fun heq => by
      subst heq; rw [hdup] at hq; exact absurd hq (by simp)⟩
  omega

/-- Exact count: recv_init with new entry increments countInitRecv by exactly 1.
    Proof: initRecv changes only at (src, b), adding one new true entry.
    The lower bound is recv_init_countInitRecv_inc; the upper bound follows from
    the filter growing by at most {src}. -/
theorem recv_init_countInitRecv_eq {s s' : State T n} {src dst : Fin n} {b : T}
    (h : (bca T n f).step s (.recv src dst .init (some b)) s')
    (hdup : (s.local_ dst).initRecv src b = false) :
    countInitRecv T n (s'.local_ dst) b = countInitRecv T n (s.local_ dst) b + 1 := by
  -- initRecv changes only at (src, b): false → true, all others unchanged
  have hge := recv_init_countInitRecv_inc h hdup
  -- For the upper bound, use filter_length_strict_mono:
  --   P = old.initRecv · b, Q = new.initRecv · b
  --   P → Q (initRecv is monotone: step_initRecv_mono)
  --   P src = false (hdup), Q src = true
  -- So filter Q ≥ filter P + 1, which means filter Q = filter P + 1 (combined with ≥)
  have hsrc_new : (s'.local_ dst).initRecv src b = true := by
    obtain ⟨_, rfl⟩ := h; simp only [↓reduceIte, hdup, ↓reduceIte, and_self, ↓reduceIte]
  have hmono_rev : ∀ q : Fin n, (s'.local_ dst).initRecv q b = true →
      (s.local_ dst).initRecv q b = true ∨ q = src := by
    intro q hq
    by_cases hqs : q = src
    · right; exact hqs
    · left
      -- For q ≠ src: new.initRecv q b = old.initRecv q b (recv only updates src)
      obtain ⟨_, rfl⟩ := h; simp only [↓reduceIte, hdup] at hq
      simp only [hqs, false_and, ↓reduceIte] at hq
      exact hq
  -- Upper bound: each new filter entry was either an old entry or src
  unfold countInitRecv at hge ⊢
  have hle : ((List.finRange n).filter (fun q => (s'.local_ dst).initRecv q b)).length ≤
      ((List.finRange n).filter (fun q => (s.local_ dst).initRecv q b)).length + 1 := by
    have := filter_split
      (fun q : Fin n => (s'.local_ dst).initRecv q b)
      (fun q : Fin n => (s.local_ dst).initRecv q b) (List.finRange n)
    -- |new filter| = |new ∧ old| + |new ∧ ¬old|
    -- |new ∧ old| ≤ |old| (by filter_and_le)
    have hle1 := filter_and_le
      (fun q : Fin n => (s'.local_ dst).initRecv q b)
      (fun q : Fin n => (s.local_ dst).initRecv q b) (List.finRange n)
    -- |new ∧ ¬old| ≤ 1 (only src can be new-but-not-old)
    have hle2 : ((List.finRange n).filter (fun q =>
        (s'.local_ dst).initRecv q b && !(s.local_ dst).initRecv q b)).length ≤ 1 := by
      apply Nat.le_trans (filter_length_mono _ _ _ _)
      · exact Nat.le_trans (filter_mem_le [src]) (by simp)
      · intro q hq
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hq
        have := hmono_rev q hq.1
        rcases this with hold | rfl
        · simp [hold] at hq
        · simp
    omega
  omega

/-- Recv init that sets approved(b) crossed the approval threshold. -/
theorem recv_init_approved_threshold {s s' : State T n} {src dst : Fin n} {b : T}
    (h : (bca T n f).step s (.recv src dst .init (some b)) s')
    (hdup : (s.local_ dst).initRecv src b = false)
    (hprev : (s.local_ dst).approved b ≠ true)
    (hpost : (s'.local_ dst).approved b = true) :
    countInitRecv T n (s.local_ dst) b + 1 ≥ approveThreshold n f := by
  obtain ⟨_, rfl⟩ := h; simp only [↓reduceIte, hdup, Bool.if_true_left, Bool.decide_and,
    ge_iff_le, decide_true, Bool.true_and, Bool.or_eq_true, decide_eq_true_eq] at hpost
  rcases hpost with hthresh | hold
  · exact hthresh
  · exact absurd hold hprev

/-- Receiving init(some b') preserves approved(b) when b ≠ b'. -/
theorem recv_init_approved_other {s s' : State T n} {src dst : Fin n} {b b' : T}
    (h : (bca T n f).step s (.recv src dst .init (some b')) s')
    (hne : b ≠ b') :
    (s'.local_ dst).approved b = (s.local_ dst).approved b := by
  obtain ⟨_, rfl⟩ := h; simp
  by_cases hdup : (s.local_ dst).initRecv src b' = false
  · simp [hdup, hne]
  · simp [hdup]

/-- countInitRecv is preserved for non-recv-init steps. -/
theorem step_countInitRecv_eq {s s' : State T n} {l : Label T n}
    (h : (bca T n f).step s l s') (p : Fin n) (b : T)
    (hl : ∀ src dst mv, l ≠ .recv src dst .init mv) :
    countInitRecv T n (s'.local_ p) b = countInitRecv T n (s.local_ p) b := by
  unfold countInitRecv; congr 1; apply List.filter_congr; intro q _
  match l with
  | .corrupt _ => rw [corrupt_local h]
  | .send src dst t mv =>
    obtain ⟨_, rfl⟩ := h; by_cases hp : p = src <;> simp [hp]
  | .recv src dst .init mv => exact absurd rfl (hl src dst mv)
  | .recv src dst .echo mv =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only
      rcases mv with _ | bv <;> simp
      by_cases hdup : (s.local_ p).echoRecv src bv = false <;> simp [hdup]
    · rw [show s'.local_ p = s.local_ p from recv_local_other h p hp]
  | .recv src dst .vote mv =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp
      by_cases hdup : (s.local_ p).voteRecv src mv = false <;> simp [hdup]
    · rw [show s'.local_ p = s.local_ p from recv_local_other h p hp]
  | .output i mv =>
    by_cases hp : p = i
    · subst hp; obtain ⟨_, _, _, rfl⟩ := h; simp
    · obtain ⟨_, _, _, rfl⟩ := h; simp [hp]
  | .input i v =>
    by_cases hp : p = i
    · subst hp; obtain ⟨_, rfl⟩ := h; simp
    · obtain ⟨_, rfl⟩ := h; simp [hp]

/-- initRecv traced to previous state. -/
theorem step_initRecv_prev {s s' : State T n} {l : Label T n}
    (h : (bca T n f).step s l s') (p q : Fin n) (b : T)
    (hrecv : (s'.local_ p).initRecv q b = true)
    (hnot_recv : ∀ dst, l ≠ .recv q dst .init (some b)) :
    (s.local_ p).initRecv q b = true := by
  match l with
  | .corrupt _ => rwa [corrupt_local h] at hrecv
  | .send src dst t mv =>
    by_cases hp : p = src
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only at hrecv; exact hrecv
    · obtain ⟨_, rfl⟩ := h; simp only [hp] at hrecv; exact hrecv
  | .recv src dst .init mv =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only at hrecv
      rcases mv with _ | bv <;> simp only at hrecv
      · exact hrecv
      · by_cases hdup : (s.local_ p).initRecv src bv = false
        · simp only [hdup] at hrecv
          by_cases hqb : q = src ∧ b = bv
          · obtain ⟨rfl, rfl⟩ := hqb; exfalso; exact hnot_recv p rfl
          · simp only [↓reduceIte, Bool.if_true_left, Bool.decide_and, ge_iff_le, Bool.or_eq_true,
            Bool.and_eq_true, decide_eq_true_eq, hqb, false_or] at hrecv; exact hrecv
        · simp only [hdup] at hrecv; exact hrecv
    · rw [recv_local_other h p hp] at hrecv; exact hrecv
  | .recv src dst .echo mv =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only at hrecv
      rcases mv with _ | bv <;> simp only at hrecv
      · exact hrecv
      · by_cases hdup : (s.local_ p).echoRecv src bv = false
        · simp only [hdup] at hrecv; exact hrecv
        · simp only [hdup] at hrecv; exact hrecv
    · rw [recv_local_other h p hp] at hrecv; exact hrecv
  | .recv src dst .vote mv =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only at hrecv
      by_cases hdup : (s.local_ p).voteRecv src mv = false
      · simp only [hdup] at hrecv; exact hrecv
      · simp only [hdup] at hrecv; exact hrecv
    · rw [recv_local_other h p hp] at hrecv; exact hrecv
  | .output i mv =>
    by_cases hp : p = i
    · subst hp; obtain ⟨_, _, _, rfl⟩ := h; simp only at hrecv; exact hrecv
    · obtain ⟨_, _, _, rfl⟩ := h; simp only [hp] at hrecv; exact hrecv
  | .input i v =>
    by_cases hp : p = i
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only at hrecv; exact hrecv
    · obtain ⟨_, rfl⟩ := h; simp only [hp] at hrecv; exact hrecv

/-- Input is persistent. -/
theorem step_input_persist {s s' : State T n} {l : Label T n}
    (h : (bca T n f).step s l s') (p : Fin n) (v : T)
    (hinput : (s.local_ p).input = some v) :
    (s'.local_ p).input = some v := by
  match l with
  | .corrupt _ => rw [corrupt_local h]; exact hinput
  | .send .. => rw [send_input h]; exact hinput
  | .recv _ _ .init _ => rw [recv_init_input h]; exact hinput
  | .recv _ _ .echo _ => rw [recv_echo_input h]; exact hinput
  | .recv _ _ .vote _ => rw [recv_vote_input h]; exact hinput
  | .output .. => rw [output_input h]; exact hinput
  | .input i v' =>
    by_cases hp : p = i
    · subst hp; exact absurd (input_was_none h) (by rw [hinput]; simp)
    · rw [input_input_other h p hp]; exact hinput

/-- Approved is preserved for non-recv-init steps. -/
theorem step_approved_eq {s s' : State T n} {l : Label T n}
    (h : (bca T n f).step s l s') (p : Fin n) (b : T)
    (hl : ∀ src dst mv, l ≠ .recv src dst .init mv) :
    (s'.local_ p).approved b = (s.local_ p).approved b := by
  match l with
  | .corrupt _ => rw [corrupt_local h]
  | .send src dst t mv =>
    by_cases hp : p = src
    · subst hp; obtain ⟨_, rfl⟩ := h; simp
    · obtain ⟨_, rfl⟩ := h; simp [hp]
  | .recv src dst .init mv => exact absurd rfl (hl src dst mv)
  | .recv src dst .echo mv =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only
      rcases mv with _ | bv <;> simp
      by_cases hdup : (s.local_ p).echoRecv src bv = false <;> simp [hdup]
    · rw [show s'.local_ p = s.local_ p from recv_local_other h p hp]
  | .recv src dst .vote mv =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp
      by_cases hdup : (s.local_ p).voteRecv src mv = false <;> simp [hdup]
    · rw [show s'.local_ p = s.local_ p from recv_local_other h p hp]
  | .output i mv =>
    by_cases hp : p = i
    · subst hp; obtain ⟨_, _, _, rfl⟩ := h; simp
    · obtain ⟨_, _, _, rfl⟩ := h; simp [hp]
  | .input i v =>
    by_cases hp : p = i
    · subst hp; obtain ⟨_, rfl⟩ := h; simp
    · obtain ⟨_, rfl⟩ := h; simp [hp]

/-- voted is preserved for non-send-vote steps (from p). -/
theorem step_voted_eq {s s' : State T n} {l : Label T n}
    (h : (bca T n f).step s l s') (p : Fin n) (w : Val T)
    (hl : ∀ dst mv, l ≠ .send p dst .vote mv) :
    (s'.local_ p).voted w = (s.local_ p).voted w := by
  match l with
  | .corrupt _ => rw [corrupt_local h]
  | .send src dst .init mv => rw [send_init_voted h p]
  | .send src dst .echo mv => rw [send_echo_voted h p]
  | .send src dst .vote mv =>
    by_cases hp : p = src
    · subst hp; exact absurd rfl (hl dst mv)
    · rw [send_vote_voted_other h p hp]
  | .recv _ _ .init _ => rw [recv_init_voted h p]
  | .recv _ _ .echo _ => rw [recv_echo_voted h p]
  | .recv _ _ .vote _ => rw [recv_vote_voted h p]
  | .output .. => rw [output_voted h p]
  | .input .. => rw [input_voted h p]

/-- echoed is preserved for non-send-echo steps (from p). -/
theorem step_echoed_eq {s s' : State T n} {l : Label T n}
    (h : (bca T n f).step s l s') (p : Fin n)
    (hl : ∀ dst mv, l ≠ .send p dst .echo mv) :
    (s'.local_ p).echoed = (s.local_ p).echoed := by
  match l with
  | .corrupt _ => rw [corrupt_local h]
  | .send src dst .init _ => exact send_init_echoed h p
  | .send src dst .echo mv =>
    by_cases hp : p = src
    · subst hp; exact absurd rfl (hl dst mv)
    · exact send_echo_echoed_other h p hp
  | .send _ _ .vote _ => exact send_vote_echoed h p
  | .recv _ _ .init _ => exact recv_init_echoed h p
  | .recv _ _ .echo _ => exact recv_echo_echoed h p
  | .recv _ _ .vote _ => exact recv_vote_echoed h p
  | .output .. => exact output_echoed h p
  | .input .. => exact input_echoed h p

/-- Approved is persistent. -/
theorem step_approved_persist {s s' : State T n} {l : Label T n}
    (h : (bca T n f).step s l s') (p : Fin n) (b : T)
    (happroved : (s.local_ p).approved b = true) :
    (s'.local_ p).approved b = true := by
  match l with
  | .corrupt _ => rw [corrupt_local h]; exact happroved
  | .send src dst t mv =>
    by_cases hp : p = src
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only; exact happroved
    · obtain ⟨_, rfl⟩ := h; simp only [hp]; exact happroved
  | .recv src dst .init mv =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only
      rcases mv with _ | bv <;> simp only
      · exact happroved
      · by_cases hdup : (s.local_ p).initRecv src bv = false
        · simp only [hdup];
          by_cases hbb : b = bv ∧ countInitRecv T n (s.local_ p) bv + 1 ≥ approveThreshold n f
          · simp [hbb]
          · simp only [↓reduceIte, Bool.if_true_left, Bool.decide_and, ge_iff_le, Bool.or_eq_true,
            Bool.and_eq_true, decide_eq_true_eq, hbb, false_or]; exact happroved
        · simp only [hdup]; exact happroved
    · rw [show s'.local_ p = s.local_ p from recv_local_other h p hp]; exact happroved
  | .recv src dst .echo mv =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only
      rcases mv with _ | bv <;> simp only
      · exact happroved
      · by_cases hdup : (s.local_ p).echoRecv src bv = false
        · simp only [hdup]; exact happroved
        · simp only [hdup]; exact happroved
    · rw [show s'.local_ p = s.local_ p from recv_local_other h p hp]; exact happroved
  | .recv src dst .vote mv =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only
      by_cases hdup : (s.local_ p).voteRecv src mv = false
      · simp only [hdup]; exact happroved
      · simp only [hdup]; exact happroved
    · rw [show s'.local_ p = s.local_ p from recv_local_other h p hp]; exact happroved
  | .output i mv =>
    by_cases hp : p = i
    · subst hp; obtain ⟨_, _, _, rfl⟩ := h; simp only; exact happroved
    · obtain ⟨_, _, _, rfl⟩ := h; simp only [hp]; exact happroved
  | .input i v =>
    by_cases hp : p = i
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only; exact happroved
    · obtain ⟨_, rfl⟩ := h; simp only [hp]; exact happroved

/-- echoRecv is monotone. -/
theorem step_echoRecv_mono {s s' : State T n} {l : Label T n}
    (h : (bca T n f).step s l s') (p q : Fin n) (b : T)
    (hrecv : (s.local_ p).echoRecv q b = true) :
    (s'.local_ p).echoRecv q b = true := by
  match l with
  | .corrupt _ => rw [corrupt_local h]; exact hrecv
  | .send src dst t mv =>
    by_cases hp : p = src
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only; exact hrecv
    · obtain ⟨_, rfl⟩ := h; simp only [hp]; exact hrecv
  | .recv src dst .echo mv =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only
      rcases mv with _ | bv <;> simp only
      · exact hrecv
      · by_cases hdup : (s.local_ p).echoRecv src bv = false
        · simp only [hdup]; by_cases hqb : q = src ∧ b = bv <;> simp [hqb, hrecv]
        · simp only [hdup]; exact hrecv
    · rw [recv_local_other h p hp]; exact hrecv
  | .recv src dst .init mv =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only
      rcases mv with _ | bv <;> simp only
      · exact hrecv
      · by_cases hdup : (s.local_ p).initRecv src bv = false
        · simp only [hdup]; exact hrecv
        · simp only [hdup]; exact hrecv
    · rw [recv_local_other h p hp]; exact hrecv
  | .recv src dst .vote mv =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only
      by_cases hdup : (s.local_ p).voteRecv src mv = false
      · simp only [hdup]; exact hrecv
      · simp only [hdup]; exact hrecv
    · rw [recv_local_other h p hp]; exact hrecv
  | .output i mv =>
    by_cases hp : p = i
    · subst hp; obtain ⟨_, _, _, rfl⟩ := h; simp only; exact hrecv
    · obtain ⟨_, _, _, rfl⟩ := h; simp only [hp]; exact hrecv
  | .input i v =>
    by_cases hp : p = i
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only; exact hrecv
    · obtain ⟨_, rfl⟩ := h; simp only [hp]; exact hrecv

/-- voteRecv is monotone. -/
theorem step_voteRecv_mono {s s' : State T n} {l : Label T n}
    (h : (bca T n f).step s l s') (p q : Fin n) (v : Val T)
    (hrecv : (s.local_ p).voteRecv q v = true) :
    (s'.local_ p).voteRecv q v = true := by
  match l with
  | .corrupt _ => rw [corrupt_local h]; exact hrecv
  | .send src dst t mv =>
    by_cases hp : p = src
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only; exact hrecv
    · obtain ⟨_, rfl⟩ := h; simp only [hp]; exact hrecv
  | .recv src dst .vote mv =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only
      by_cases hdup : (s.local_ p).voteRecv src mv = false
      · simp only [hdup]; by_cases hqv : q = src ∧ v = mv <;> simp [hqv, hrecv]
      · simp only [hdup]; exact hrecv
    · rw [recv_local_other h p hp]; exact hrecv
  | .recv src dst .echo mv =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only
      rcases mv with _ | bv <;> simp only
      · exact hrecv
      · by_cases hdup : (s.local_ p).echoRecv src bv = false
        · simp only [hdup]; exact hrecv
        · simp only [hdup]; exact hrecv
    · rw [recv_local_other h p hp]; exact hrecv
  | .recv src dst .init mv =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only
      rcases mv with _ | bv <;> simp only
      · exact hrecv
      · by_cases hdup : (s.local_ p).initRecv src bv = false
        · simp only [hdup]; exact hrecv
        · simp only [hdup]; exact hrecv
    · rw [recv_local_other h p hp]; exact hrecv
  | .output i mv =>
    by_cases hp : p = i
    · subst hp; obtain ⟨_, _, _, rfl⟩ := h; simp only; exact hrecv
    · obtain ⟨_, _, _, rfl⟩ := h; simp only [hp]; exact hrecv
  | .input i w =>
    by_cases hp : p = i
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only; exact hrecv
    · obtain ⟨_, rfl⟩ := h; simp only [hp]; exact hrecv

/-- countEchoRecv is monotone. -/
theorem step_countEchoRecv_mono {s s' : State T n} {l : Label T n}
    (h : (bca T n f).step s l s') (p : Fin n) (b : T) :
    countEchoRecv T n (s.local_ p) b ≤ countEchoRecv T n (s'.local_ p) b := by
  unfold countEchoRecv
  apply filter_length_mono; intro q hq; simp only at hq ⊢
  exact step_echoRecv_mono h p q b hq

/-- countVoteRecv is monotone. -/
theorem step_countVoteRecv_mono {s s' : State T n} {l : Label T n}
    (h : (bca T n f).step s l s') (p : Fin n) (v : Val T) :
    countVoteRecv T n (s.local_ p) v ≤ countVoteRecv T n (s'.local_ p) v := by
  unfold countVoteRecv
  apply filter_length_mono; intro q hq; simp only at hq ⊢
  exact step_voteRecv_mono h p q v hq

/-- Recv echo with a new entry increments countEchoRecv by at least 1. -/
theorem recv_echo_countEchoRecv_inc {s s' : State T n} {src dst : Fin n} {b : T}
    (h : (bca T n f).step s (.recv src dst .echo (some b)) s')
    (hdup : (s.local_ dst).echoRecv src b = false) :
    countEchoRecv T n (s'.local_ dst) b ≥ countEchoRecv T n (s.local_ dst) b + 1 := by
  have hmono := step_countEchoRecv_mono h dst b
  have hsrc_new : (s'.local_ dst).echoRecv src b = true := by
    obtain ⟨_, rfl⟩ := h; simp [hdup]
  unfold countEchoRecv at hmono ⊢
  have hsplit := filter_split
    (fun q : Fin n => (s'.local_ dst).echoRecv q b)
    (fun q : Fin n => !decide (q = src))
    (List.finRange n)
  have hone : ((List.finRange n).filter (fun q =>
      (s'.local_ dst).echoRecv q b && !!decide (q = src))).length ≥ 1 := by
    have : src ∈ (List.finRange n).filter (fun q =>
        (s'.local_ dst).echoRecv q b && !!decide (q = src)) := by
      simp [List.mem_filter, List.mem_finRange, hsrc_new, Bool.not_not]
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (List.length_pos_of_mem this)
  have hrest : ((List.finRange n).filter (fun q =>
      (s.local_ dst).echoRecv q b)).length ≤
    ((List.finRange n).filter (fun q =>
      (s'.local_ dst).echoRecv q b && !decide (q = src))).length := by
    apply filter_length_mono; intro q hq; simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_false_iff_not] at hq ⊢
    exact ⟨step_echoRecv_mono h dst q b hq, fun heq => by
      subst heq; rw [hdup] at hq; exact absurd hq (by simp)⟩
  omega

/-- Recv vote with a new entry increments countVoteRecv by at least 1. -/
theorem recv_vote_countVoteRecv_inc {s s' : State T n} {src dst : Fin n} {v : Val T}
    (h : (bca T n f).step s (.recv src dst .vote v) s')
    (hdup : (s.local_ dst).voteRecv src v = false) :
    countVoteRecv T n (s'.local_ dst) v ≥ countVoteRecv T n (s.local_ dst) v + 1 := by
  have hmono := step_countVoteRecv_mono h dst v
  have hsrc_new : (s'.local_ dst).voteRecv src v = true := by
    obtain ⟨_, rfl⟩ := h; simp [hdup]
  unfold countVoteRecv at hmono ⊢
  have hsplit := filter_split
    (fun q : Fin n => (s'.local_ dst).voteRecv q v)
    (fun q : Fin n => !decide (q = src))
    (List.finRange n)
  have hone : ((List.finRange n).filter (fun q =>
      (s'.local_ dst).voteRecv q v && !!decide (q = src))).length ≥ 1 := by
    have : src ∈ (List.finRange n).filter (fun q =>
        (s'.local_ dst).voteRecv q v && !!decide (q = src)) := by
      simp [List.mem_filter, List.mem_finRange, hsrc_new, Bool.not_not]
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (List.length_pos_of_mem this)
  have hrest : ((List.finRange n).filter (fun q =>
      (s.local_ dst).voteRecv q v)).length ≤
    ((List.finRange n).filter (fun q =>
      (s'.local_ dst).voteRecv q v && !decide (q = src))).length := by
    apply filter_length_mono; intro q hq; simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_false_iff_not] at hq ⊢
    exact ⟨step_voteRecv_mono h dst q v hq, fun heq => by
      subst heq; rw [hdup] at hq; exact absurd hq (by simp)⟩
  omega

/-- sent is monotone. -/
theorem step_sent_mono {s s' : State T n} {l : Label T n}
    (h : (bca T n f).step s l s') (p : Fin n) (dst : Fin n)
    (t : MsgType) (v : Val T)
    (hsent : (s.local_ p).sent dst t v = true) :
    (s'.local_ p).sent dst t v = true := by
  match l with
  | .corrupt _ => rw [corrupt_local h]; exact hsent
  | .send src dst' t' mv =>
    by_cases hp : p = src
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only
      by_cases heq : dst = dst' ∧ t = t' ∧ v = mv <;> simp [heq, hsent]
    · obtain ⟨_, rfl⟩ := h; simp only [hp]; exact hsent
  | .recv src dst' .init mv =>
    by_cases hp : p = dst'
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only
      rcases mv with _ | bv <;> simp only
      · exact hsent
      · by_cases hdup : (s.local_ p).initRecv src bv = false
        · simp only [hdup]; exact hsent
        · simp only [hdup]; exact hsent
    · rw [recv_local_other h p hp]; exact hsent
  | .recv src dst' .echo mv =>
    by_cases hp : p = dst'
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only
      rcases mv with _ | bv <;> simp only
      · exact hsent
      · by_cases hdup : (s.local_ p).echoRecv src bv = false
        · simp only [hdup]; exact hsent
        · simp only [hdup]; exact hsent
    · rw [recv_local_other h p hp]; exact hsent
  | .recv src dst' .vote mv =>
    by_cases hp : p = dst'
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only
      by_cases hdup : (s.local_ p).voteRecv src mv = false
      · simp only [hdup]; exact hsent
      · simp only [hdup]; exact hsent
    · rw [recv_local_other h p hp]; exact hsent
  | .output i mv =>
    by_cases hp : p = i
    · subst hp; obtain ⟨_, _, _, rfl⟩ := h; simp only; exact hsent
    · obtain ⟨_, _, _, rfl⟩ := h; simp only [hp]; exact hsent
  | .input i w =>
    by_cases hp : p = i
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only; exact hsent
    · obtain ⟨_, rfl⟩ := h; simp only [hp]; exact hsent

/-- countEchoRecv is preserved for non-recv-echo steps. -/
theorem step_countEchoRecv_eq {s s' : State T n} {l : Label T n}
    (h : (bca T n f).step s l s') (p : Fin n) (b : T)
    (hl : ∀ src dst mv, l ≠ .recv src dst .echo mv) :
    countEchoRecv T n (s'.local_ p) b = countEchoRecv T n (s.local_ p) b := by
  unfold countEchoRecv; congr 1; apply List.filter_congr; intro q _
  match l with
  | .corrupt _ => rw [corrupt_local h]
  | .send src dst t mv =>
    obtain ⟨_, rfl⟩ := h; by_cases hp : p = src <;> simp [hp]
  | .recv src dst .echo mv => exact absurd rfl (hl src dst mv)
  | .recv src dst .init mv =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only
      rcases mv with _ | bv <;> simp
      by_cases hdup : (s.local_ p).initRecv src bv = false <;> simp [hdup]
    · rw [show s'.local_ p = s.local_ p from recv_local_other h p hp]
  | .recv src dst .vote mv =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp
      by_cases hdup : (s.local_ p).voteRecv src mv = false <;> simp [hdup]
    · rw [show s'.local_ p = s.local_ p from recv_local_other h p hp]
  | .output i mv =>
    by_cases hp : p = i
    · subst hp; obtain ⟨_, _, _, rfl⟩ := h; simp
    · obtain ⟨_, _, _, rfl⟩ := h; simp [hp]
  | .input i v =>
    by_cases hp : p = i
    · subst hp; obtain ⟨_, rfl⟩ := h; simp
    · obtain ⟨_, rfl⟩ := h; simp [hp]

/-- countVoteRecv is preserved for non-recv-vote steps. -/
theorem step_countVoteRecv_eq {s s' : State T n} {l : Label T n}
    (h : (bca T n f).step s l s') (p : Fin n) (v : Val T)
    (hl : ∀ src dst mv, l ≠ .recv src dst .vote mv) :
    countVoteRecv T n (s'.local_ p) v = countVoteRecv T n (s.local_ p) v := by
  unfold countVoteRecv; congr 1; apply List.filter_congr; intro q _
  match l with
  | .corrupt _ => rw [corrupt_local h]
  | .send src dst t mv =>
    obtain ⟨_, rfl⟩ := h; by_cases hp : p = src <;> simp [hp]
  | .recv src dst .vote mv => exact absurd rfl (hl src dst mv)
  | .recv src dst .init mv =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only
      rcases mv with _ | bv <;> simp
      by_cases hdup : (s.local_ p).initRecv src bv = false <;> simp [hdup]
    · rw [show s'.local_ p = s.local_ p from recv_local_other h p hp]
  | .recv src dst .echo mv =>
    by_cases hp : p = dst
    · subst hp; obtain ⟨_, rfl⟩ := h; simp only
      rcases mv with _ | bv <;> simp
      by_cases hdup : (s.local_ p).echoRecv src bv = false <;> simp [hdup]
    · rw [show s'.local_ p = s.local_ p from recv_local_other h p hp]
  | .output i mv =>
    by_cases hp : p = i
    · subst hp; obtain ⟨_, _, _, rfl⟩ := h; simp
    · obtain ⟨_, _, _, rfl⟩ := h; simp [hp]
  | .input i w =>
    by_cases hp : p = i
    · subst hp; obtain ⟨_, rfl⟩ := h; simp
    · obtain ⟨_, rfl⟩ := h; simp [hp]

/-- decided is persistent: once `some v`, it stays `some v`. -/
theorem step_decided_persist {s s' : State T n} {l : Label T n}
    (h : (bca T n f).step s l s') (p : Fin n) (v : Val T)
    (hdec : (s.local_ p).decided = some v) :
    (s'.local_ p).decided = some v := by
  match l with
  | .corrupt _ => rw [corrupt_local h]; exact hdec
  | .send .. => rw [send_decided h]; exact hdec
  | .recv _ _ .init _ => rw [recv_init_decided h]; exact hdec
  | .recv _ _ .echo _ => rw [recv_echo_decided h]; exact hdec
  | .recv _ _ .vote _ => rw [recv_vote_decided h]; exact hdec
  | .input _ _ => rw [input_decided h]; exact hdec
  | .output i mv =>
    by_cases hp : p = i
    · subst hp; exact absurd (output_decided_none h) (by rw [hdec]; simp)
    · rw [output_decided_other h p hp]; exact hdec

/-- Corruption is persistent. -/
theorem step_corrupted_mem_persist {s s' : State T n} {l : Label T n}
    (h : (bca T n f).step s l s') (p : Fin n)
    (hc : p ∈ s.corrupted) :
    p ∈ s'.corrupted := by
  match l with
  | .corrupt i =>
    rw [corrupt_eq h]; exact List.mem_cons.mpr (Or.inr hc)
  | .send .. => rw [send_corrupted h]; exact hc
  | .recv .. => rw [recv_corrupted h]; exact hc
  | .output .. => rw [output_corrupted h]; exact hc
  | .input .. => rw [input_corrupted h]; exact hc

/-- Buffer is monotone for non-recv steps. -/
theorem step_buffer_mono_non_recv {s s' : State T n} {l : Label T n}
    (h : (bca T n f).step s l s')
    (hl : ∀ src dst t mv, l ≠ .recv src dst t mv)
    (m : Message T n) (hm : s.buffer m = true) :
    s'.buffer m = true := by
  match l with
  | .corrupt _ => obtain ⟨_, _, rfl⟩ := h; exact hm
  | .send src dst t mv =>
    obtain ⟨_, rfl⟩ := h; simp only
    by_cases hmeq : m = ⟨src, dst, t, mv⟩ <;> simp [hmeq, hm]
  | .recv src dst t mv => exact absurd rfl (hl src dst t mv)
  | .output _ _ => obtain ⟨_, _, _, rfl⟩ := h; exact hm
  | .input _ _ => obtain ⟨_, rfl⟩ := h; exact hm

/-- countAnyVoteRecv is monotone. -/
theorem step_countAnyVoteRecv_mono {s s' : State T n} {l : Label T n}
    (h : (bca T n f).step s l s') (p : Fin n) (vals : List (Val T)) :
    countAnyVoteRecv T n (s.local_ p) vals ≤ countAnyVoteRecv T n (s'.local_ p) vals := by
  unfold countAnyVoteRecv
  apply filter_length_mono; intro q hq; simp only [List.any_eq_true] at hq ⊢
  obtain ⟨v, hv_mem, hv_recv⟩ := hq
  exact ⟨v, hv_mem, step_voteRecv_mono h p q v hv_recv⟩

-- Execution-level persistence (for liveness proofs)

theorem decided_persist_along {e : Execution (State T n) (Label T n)}
    (hv : (bca T n f).valid_exec e)
    {k : Nat} {p : Fin n} {v : Val T}
    (h : ((e.states k).local_ p).decided = some v) :
    ∀ k', k ≤ k' → ((e.states k').local_ p).decided = some v := by
  intro k'; induction k' with
  | zero => intro hle; rw [show k = 0 from Nat.le_zero.mp hle] at h; exact h
  | succ k' ih =>
    intro hle; rcases Nat.eq_or_lt_of_le hle with rfl | hlt
    · exact h
    · exact step_decided_persist (hv.2 k') p v (ih (by omega))

theorem corrupted_mem_persist_along {e : Execution (State T n) (Label T n)}
    (hv : (bca T n f).valid_exec e)
    {k : Nat} {p : Fin n}
    (h : p ∈ (e.states k).corrupted) :
    ∀ k', k ≤ k' → p ∈ (e.states k').corrupted := by
  intro k'; induction k' with
  | zero => intro hle; rw [show k = 0 from Nat.le_zero.mp hle] at h; exact h
  | succ k' ih =>
    intro hle; rcases Nat.eq_or_lt_of_le hle with rfl | hlt
    · exact h
    · exact step_corrupted_mem_persist (hv.2 k') p (ih (by omega))

theorem input_persist_along {e : Execution (State T n) (Label T n)}
    (hv : (bca T n f).valid_exec e)
    {k : Nat} {p : Fin n} {v : T}
    (h : ((e.states k).local_ p).input = some v) :
    ∀ k', k ≤ k' → ((e.states k').local_ p).input = some v := by
  intro k'; induction k' with
  | zero => intro hle; rw [show k = 0 from Nat.le_zero.mp hle] at h; exact h
  | succ k' ih =>
    intro hle; rcases Nat.eq_or_lt_of_le hle with rfl | hlt
    · exact h
    · exact step_input_persist (hv.2 k') p v (ih (by omega))

theorem approved_persist_along {e : Execution (State T n) (Label T n)}
    (hv : (bca T n f).valid_exec e)
    {k : Nat} {p : Fin n} {b : T}
    (h : ((e.states k).local_ p).approved b = true) :
    ∀ k', k ≤ k' → ((e.states k').local_ p).approved b = true := by
  intro k'; induction k' with
  | zero => intro hle; rw [show k = 0 from Nat.le_zero.mp hle] at h; exact h
  | succ k' ih =>
    intro hle; rcases Nat.eq_or_lt_of_le hle with rfl | hlt
    · exact h
    · exact step_approved_persist (hv.2 k') p b (ih (by omega))

theorem sent_persist_along {e : Execution (State T n) (Label T n)}
    (hv : (bca T n f).valid_exec e)
    {k : Nat} {p dst : Fin n} {t : MsgType} {v : Val T}
    (h : ((e.states k).local_ p).sent dst t v = true) :
    ∀ k', k ≤ k' → ((e.states k').local_ p).sent dst t v = true := by
  intro k'; induction k' with
  | zero => intro hle; rw [show k = 0 from Nat.le_zero.mp hle] at h; exact h
  | succ k' ih =>
    intro hle; rcases Nat.eq_or_lt_of_le hle with rfl | hlt
    · exact h
    · exact step_sent_mono (hv.2 k') p dst t v (ih (by omega))

/-- A correct-to-correct init(some b) send is enabled when src has input b
    or enough initRecvs, and hasn't sent yet. -/
theorem send_init_enabled {s : State T n} {src dst : Fin n} {b : T}
    (hcorr : isCorrect T n s src)
    (hsent : (s.local_ src).sent dst .init (some b) = false)
    (hgate : (s.local_ src).input = some b ∨
             countInitRecv T n (s.local_ src) b ≥ amplifyThreshold f) :
    (bca T n f).enabled (.send src dst .init (some b)) s := by
  refine ⟨_, Or.inr ⟨hcorr, hsent, ?_⟩, rfl⟩
  exact hgate

/-- At a reachable state, a correct process with echoed = some b has approved b. -/
theorem echoed_implies_approved {s : State T n}
    (hreach : LTS.Reachable (bca T n f) s)
    (p : Fin n) (b : T)
    (hcorr : isCorrect T n s p)
    (hechoed : (s.local_ p).echoed = some b) :
    (s.local_ p).approved b = true := by
  induction hreach with
  | init hinit =>
    obtain ⟨hlocal, _, _⟩ := hinit
    simp [hlocal p, LocalState.init] at hechoed
  | step hreach_prev hstep ih =>
    rename_i s_prev l _
    have hcp := step_correct_prev hstep p hcorr
    by_cases hprev : (s_prev.local_ p).echoed = some b
    · -- Already echoed: approved b persists.
      exact step_approved_persist hstep p b (ih hcp hprev)
    · -- Newly echoed: must be send echo (some b) from p.
      match l with
      | .send src dst .echo (some b') =>
        by_cases hp : p = src
        · subst hp
          have happr := (send_echo_gate hstep hcp).1
          have hechoed_new := send_echo_echoed_correct hstep hcp
          rw [hechoed_new] at hechoed
          have hbb : b' = b := Option.some.inj hechoed
          subst hbb
          exact step_approved_persist hstep p b' happr
        · rw [send_echo_echoed_other hstep p hp] at hechoed
          exact absurd hechoed hprev
      | .send src dst .echo none =>
        rw [send_echo_none_echoed hstep p] at hechoed
        exact absurd hechoed hprev
      | .corrupt _ => rw [corrupt_local hstep] at hechoed; exact absurd hechoed hprev
      | .send _ _ .init _ => rw [send_init_echoed hstep] at hechoed; exact absurd hechoed hprev
      | .send _ _ .vote _ => rw [send_vote_echoed hstep] at hechoed; exact absurd hechoed hprev
      | .recv _ _ .init _ => rw [recv_init_echoed hstep] at hechoed; exact absurd hechoed hprev
      | .recv _ _ .echo _ => rw [recv_echo_echoed hstep] at hechoed; exact absurd hechoed hprev
      | .recv _ _ .vote _ => rw [recv_vote_echoed hstep] at hechoed; exact absurd hechoed hprev
      | .output _ _ => rw [output_echoed hstep] at hechoed; exact absurd hechoed hprev
      | .input _ _ => rw [input_echoed hstep] at hechoed; exact absurd hechoed hprev

/-- Recv is enabled when the message is in the buffer. -/
theorem recv_enabled {s : State T n} {src dst : Fin n} {t : MsgType} {v : Val T}
    (hbuf : s.buffer ⟨src, dst, t, v⟩ = true) :
    (bca T n f).enabled (.recv src dst t v) s := by
  simp only [System.enabled, bca]
  exact ⟨_, hbuf, rfl⟩

/-- A correct-to-correct echo(some b) send is enabled when src has
    approved b, echoed is compatible, and hasn't sent yet. -/
theorem send_echo_enabled {s : State T n} {src dst : Fin n} {b : T}
    (hcorr : isCorrect T n s src)
    (hsent : (s.local_ src).sent dst .echo (some b) = false)
    (happroved : (s.local_ src).approved b = true)
    (hechoed : (s.local_ src).echoed = none ∨ (s.local_ src).echoed = some b) :
    (bca T n f).enabled (.send src dst .echo (some b)) s := by
  refine ⟨_, Or.inr ⟨hcorr, hsent, happroved, hechoed⟩, rfl⟩

/-- A correct-to-correct vote(some b) send is enabled when src has
    enough echo quorum, is vote-consistent, and hasn't sent yet. -/
theorem send_vote_binary_enabled {s : State T n} {src dst : Fin n} {b : T}
    (hcorr : isCorrect T n s src)
    (hsent : (s.local_ src).sent dst .vote (some b) = false)
    (huniq : ∀ w, (s.local_ src).voted w = true → w = some b)
    (hquorum : countEchoRecv T n (s.local_ src) b ≥ echoThreshold n f) :
    (bca T n f).enabled (.send src dst .vote (some b)) s := by
  refine ⟨_, Or.inr ⟨hcorr, hsent, huniq, hquorum⟩, rfl⟩

/-- Output(p, some b) is enabled when p is correct, undecided, and has
    enough binary votes. -/
theorem output_binary_enabled {s : State T n} {p : Fin n} {b : T}
    (hcorr : isCorrect T n s p)
    (hdec : (s.local_ p).decided = none)
    (hvotes : countVoteRecv T n (s.local_ p) (some b) ≥ returnThreshold n f) :
    (bca T n f).enabled (.output p (some b)) s := by
  refine ⟨_, hcorr, hdec, hvotes, rfl⟩

/-- At a reachable state, if a correct process decided (some b),
    then it had countVoteRecv(some b) ≥ returnThreshold at the time of decision.
    Since countVoteRecv is monotone, it still holds. -/
theorem decided_binary_implies_voteRecv {s : State T n}
    (hreach : LTS.Reachable (bca T n f) s)
    (p : Fin n) (b : T)
    (hdec : (s.local_ p).decided = some (some b)) :
    countVoteRecv T n (s.local_ p) (some b) ≥ returnThreshold n f := by
  induction hreach with
  | init hinit =>
    obtain ⟨hlocal, _, _⟩ := hinit
    simp [hlocal p, LocalState.init] at hdec
  | step hreach_prev hstep ih =>
    rename_i s_prev l _
    by_cases hdec_prev : (s_prev.local_ p).decided = some (some b)
    · have := ih hdec_prev
      exact Nat.le_trans this (step_countVoteRecv_mono hstep p (some b))
    · -- Newly decided: must be output(p, some b)
      match l with
      | .output i mv =>
        by_cases hp : p = i
        · subst hp
          have hguard := hstep.2.2.1
          have hdec_self := output_decided_self hstep
          rw [hdec_self] at hdec; simp at hdec; subst hdec
          exact Nat.le_trans hguard (step_countVoteRecv_mono hstep p (some b))
        · rw [output_decided_other hstep p hp] at hdec
          exact absurd hdec hdec_prev
      | .corrupt _ => rw [corrupt_local hstep] at hdec; exact absurd hdec hdec_prev
      | .send .. => rw [send_decided hstep] at hdec; exact absurd hdec hdec_prev
      | .recv _ _ .init _ => rw [recv_init_decided hstep] at hdec; exact absurd hdec hdec_prev
      | .recv _ _ .echo _ => rw [recv_echo_decided hstep] at hdec; exact absurd hdec hdec_prev
      | .recv _ _ .vote _ => rw [recv_vote_decided hstep] at hdec; exact absurd hdec hdec_prev
      | .input _ _ => rw [input_decided hstep] at hdec; exact absurd hdec hdec_prev

/-- Corrupted list length is non-decreasing across steps. -/
theorem step_corrupted_length_mono {s s' : State T n} {l : Label T n}
    (h : (bca T n f).step s l s') :
    s.corrupted.length ≤ s'.corrupted.length := by
  match l with
  | .corrupt _ => rw [corrupt_eq h]; simp
  | .send .. => rw [send_corrupted h]
  | .recv .. => rw [recv_corrupted h]
  | .output .. => rw [output_corrupted h]
  | .input .. => rw [input_corrupted h]

theorem echoed_persist_along {e : Execution (State T n) (Label T n)}
    (hv : (bca T n f).valid_exec e)
    {k : Nat} {p : Fin n} {b : T}
    (h : ((e.states k).local_ p).echoed = some b)
    (hcorr : ∀ k', k ≤ k' → p ∉ (e.states k').corrupted) :
    ∀ k', k ≤ k' → ((e.states k').local_ p).echoed = some b := by
  intro k'; induction k' with
  | zero => intro hle; rw [show k = 0 from Nat.le_zero.mp hle] at h; exact h
  | succ k' ih =>
    intro hle; rcases Nat.eq_or_lt_of_le hle with rfl | hlt
    · exact h
    · exact step_echoed_persist (hv.2 k') p b (hcorr (k' + 1) (by omega)) (ih (by omega))

theorem voted_persist_along {e : Execution (State T n) (Label T n)}
    (hv : (bca T n f).valid_exec e)
    {k : Nat} {p : Fin n} {b : T}
    (h : ((e.states k).local_ p).voted (some b) = true)
    (hcorr : ∀ k', k ≤ k' → p ∉ (e.states k').corrupted) :
    ∀ k', k ≤ k' → ((e.states k').local_ p).voted (some b) = true := by
  intro k'; induction k' with
  | zero => intro hle; rw [show k = 0 from Nat.le_zero.mp hle] at h; exact h
  | succ k' ih =>
    intro hle; rcases Nat.eq_or_lt_of_le hle with rfl | hlt
    · exact h
    · exact step_voted_persist (hv.2 k') p b (hcorr (k' + 1) (by omega)) (ih (by omega))

theorem initRecv_mono_along {e : Execution (State T n) (Label T n)}
    (hv : (bca T n f).valid_exec e)
    {k : Nat} {p q : Fin n} {b : T}
    (h : ((e.states k).local_ p).initRecv q b = true) :
    ∀ k', k ≤ k' → ((e.states k').local_ p).initRecv q b = true := by
  intro k'; induction k' with
  | zero => intro hle; rw [show k = 0 from Nat.le_zero.mp hle] at h; exact h
  | succ k' ih =>
    intro hle; rcases Nat.eq_or_lt_of_le hle with rfl | hlt
    · exact h
    · exact step_initRecv_mono (hv.2 k') p q b (ih (by omega))

theorem echoRecv_mono_along {e : Execution (State T n) (Label T n)}
    (hv : (bca T n f).valid_exec e)
    {k : Nat} {p q : Fin n} {b : T}
    (h : ((e.states k).local_ p).echoRecv q b = true) :
    ∀ k', k ≤ k' → ((e.states k').local_ p).echoRecv q b = true := by
  intro k'; induction k' with
  | zero => intro hle; rw [show k = 0 from Nat.le_zero.mp hle] at h; exact h
  | succ k' ih =>
    intro hle; rcases Nat.eq_or_lt_of_le hle with rfl | hlt
    · exact h
    · exact step_echoRecv_mono (hv.2 k') p q b (ih (by omega))

theorem voteRecv_mono_along {e : Execution (State T n) (Label T n)}
    (hv : (bca T n f).valid_exec e)
    {k : Nat} {p q : Fin n} {v : Val T}
    (h : ((e.states k).local_ p).voteRecv q v = true) :
    ∀ k', k ≤ k' → ((e.states k').local_ p).voteRecv q v = true := by
  intro k'; induction k' with
  | zero => intro hle; rw [show k = 0 from Nat.le_zero.mp hle] at h; exact h
  | succ k' ih =>
    intro hle; rcases Nat.eq_or_lt_of_le hle with rfl | hlt
    · exact h
    · exact step_voteRecv_mono (hv.2 k') p q v (ih (by omega))

end StepHelpers

/-! ### Delivery Invariants

    At any reachable state, if a message has been sent, it is either still in the
    buffer or has been received by the destination.

    Proof approach: step-level preservation + Reachable induction. -/

section DeliveryInvariants

variable {T : Type} [DecidableEq T] {n f : Nat}

/-- Recv does not change the sent field (for any process). -/
private theorem recv_sent {s s' : State T n} {src' dst' t' mv'}
    (h : (bca T n f).step s (.recv src' dst' t' mv') s')
    (p : Fin n) (d : Fin n) (t : MsgType) (v : Val T) :
    (s'.local_ p).sent d t v = (s.local_ p).sent d t v := by
  by_cases hp : p = dst'
  · subst hp; obtain ⟨_, rfl⟩ := h; simp only
    match t' with
    | .init =>
      match mv' with
      | some b' => by_cases hdup : (s.local_ p).initRecv src' b' = false <;> simp [hdup]
      | none => simp
    | .echo =>
      match mv' with
      | some b' => by_cases hdup : (s.local_ p).echoRecv src' b' = false <;> simp [hdup]
      | none => simp
    | .vote =>
      by_cases hdup : (s.local_ p).voteRecv src' mv' = false <;> simp [hdup]
  · rw [recv_local_other h p hp]

/-- After recv(src, dst, init, some b), initRecv(dst, src, b) = true. -/
private theorem recv_init_initRecv_set {s s' : State T n} {src dst : Fin n} {b : T}
    (h : (bca T n f).step s (.recv src dst .init (some b)) s') :
    (s'.local_ dst).initRecv src b = true := by
  obtain ⟨_, rfl⟩ := h; simp only
  by_cases hdup : (s.local_ dst).initRecv src b = false
  · simp [hdup]
  · simp only [Bool.not_eq_false] at hdup; simp [hdup]

/-- After recv(src, dst, echo, some b), echoRecv(dst, src, b) = true. -/
private theorem recv_echo_echoRecv_set {s s' : State T n} {src dst : Fin n} {b : T}
    (h : (bca T n f).step s (.recv src dst .echo (some b)) s') :
    (s'.local_ dst).echoRecv src b = true := by
  obtain ⟨_, rfl⟩ := h; simp only
  by_cases hdup : (s.local_ dst).echoRecv src b = false
  · simp [hdup]
  · simp only [Bool.not_eq_false] at hdup; simp [hdup]

/-- After recv(src, dst, vote, v), voteRecv(dst, src, v) = true. -/
private theorem recv_vote_voteRecv_set {s s' : State T n} {src dst : Fin n} {v : Val T}
    (h : (bca T n f).step s (.recv src dst .vote v) s') :
    (s'.local_ dst).voteRecv src v = true := by
  obtain ⟨_, rfl⟩ := h; simp only
  by_cases hdup : (s.local_ dst).voteRecv src v = false
  · simp [hdup]
  · simp only [Bool.not_eq_false] at hdup; simp [hdup]

/-- Recv clears only the consumed buffer entry; other entries are preserved. -/
private theorem recv_buffer_other {s s' : State T n} {src' dst' t' mv'}
    (h : (bca T n f).step s (.recv src' dst' t' mv') s')
    {m : Message T n} (hne : m ≠ ⟨src', dst', t', mv'⟩)
    (hm : s.buffer m = true) :
    s'.buffer m = true := by
  obtain ⟨_, rfl⟩ := h; simp [hne, hm]

/-- Send preserves initRecv. -/
private theorem send_initRecv {s s' : State T n} {src' dst' t' mv'}
    (h : (bca T n f).step s (.send src' dst' t' mv') s')
    (p : Fin n) (q : Fin n) (b : T) :
    (s'.local_ p).initRecv q b = (s.local_ p).initRecv q b := by
  by_cases hp : p = src'
  · subst hp; obtain ⟨_, rfl⟩ := h; simp
  · obtain ⟨_, rfl⟩ := h; simp [hp]

/-- Send preserves echoRecv. -/
private theorem send_echoRecv {s s' : State T n} {src' dst' t' mv'}
    (h : (bca T n f).step s (.send src' dst' t' mv') s')
    (p : Fin n) (q : Fin n) (b : T) :
    (s'.local_ p).echoRecv q b = (s.local_ p).echoRecv q b := by
  by_cases hp : p = src'
  · subst hp; obtain ⟨_, rfl⟩ := h; simp
  · obtain ⟨_, rfl⟩ := h; simp [hp]

/-- Send preserves voteRecv. -/
private theorem send_voteRecv {s s' : State T n} {src' dst' t' mv'}
    (h : (bca T n f).step s (.send src' dst' t' mv') s')
    (p : Fin n) (q : Fin n) (v : Val T) :
    (s'.local_ p).voteRecv q v = (s.local_ p).voteRecv q v := by
  by_cases hp : p = src'
  · subst hp; obtain ⟨_, rfl⟩ := h; simp
  · obtain ⟨_, rfl⟩ := h; simp [hp]

/-- Step-level: init delivery invariant is preserved by every step. -/
private theorem step_init_delivery_inv {s s' : State T n} {l : Label T n}
    (h : (bca T n f).step s l s') (src dst : Fin n) (b : T)
    (hsent' : (s'.local_ src).sent dst .init (some b) = true)
    (ih : (s.local_ src).sent dst .init (some b) = true →
          s.buffer ⟨src, dst, .init, some b⟩ = true ∨
          (s.local_ dst).initRecv src b = true) :
    s'.buffer ⟨src, dst, .init, some b⟩ = true ∨
    (s'.local_ dst).initRecv src b = true := by
  match l with
  | .corrupt _ =>
    rw [corrupt_local h] at hsent'
    rcases ih hsent' with hbuf | hrecv
    · left; rw [corrupt_buffer h]; exact hbuf
    · right; rw [corrupt_local h]; exact hrecv
  | .input _ _ =>
    rw [input_sent h src dst .init (some b)] at hsent'
    rcases ih hsent' with hbuf | hrecv
    · left; rw [input_buffer h]; exact hbuf
    · right; exact step_initRecv_mono h dst src b hrecv
  | .output _ _ =>
    rw [output_sent h src dst .init (some b)] at hsent'
    rcases ih hsent' with hbuf | hrecv
    · left; rw [output_buffer h]; exact hbuf
    · right; exact step_initRecv_mono h dst src b hrecv
  | .send src' dst' t' mv' =>
    by_cases hsrc : src = src'
    · subst hsrc
      rw [send_sent h dst .init (some b)] at hsent'
      split_ifs at hsent' with heq
      · obtain ⟨rfl, rfl, rfl⟩ := heq; left; exact send_buffer_new h
      · rcases ih hsent' with hbuf | hrecv
        · left; exact send_buffer_mono h _ hbuf
        · right; rw [send_initRecv h dst src b]; exact hrecv
    · rw [send_sent_other h src (hsrc) dst .init (some b)] at hsent'
      rcases ih hsent' with hbuf | hrecv
      · left; exact send_buffer_mono h _ hbuf
      · right; rw [send_initRecv h dst src b]; exact hrecv
  | .recv src' dst' t' mv' =>
    rw [recv_sent h src dst .init (some b)] at hsent'
    rcases ih hsent' with hbuf | hrecv
    · by_cases hmeq : (⟨src, dst, .init, some b⟩ : Message T n) = ⟨src', dst', t', mv'⟩
      · have : src = src' ∧ dst = dst' ∧ t' = .init ∧ mv' = some b := by
          simp [Message.mk.injEq] at hmeq; exact ⟨hmeq.1, hmeq.2.1, hmeq.2.2.1.symm, hmeq.2.2.2.symm⟩
        obtain ⟨rfl, rfl, rfl, rfl⟩ := this
        right; exact recv_init_initRecv_set h
      · left; exact recv_buffer_other h hmeq hbuf
    · right; exact step_initRecv_mono h dst src b hrecv

/-- If init(some b) was sent from src to dst, it is either in the buffer or received. -/
theorem init_delivery_inv {s : State T n}
    (hreach : LTS.Reachable (bca T n f) s)
    (src dst : Fin n) (b : T)
    (hsent : (s.local_ src).sent dst .init (some b) = true) :
    s.buffer ⟨src, dst, .init, some b⟩ = true ∨
    (s.local_ dst).initRecv src b = true := by
  induction hreach with
  | init hinit =>
    obtain ⟨hlocal, _, _⟩ := hinit
    simp [hlocal src, LocalState.init] at hsent
  | step hreach' hstep ih =>
    exact step_init_delivery_inv hstep src dst b hsent ih

/-- Step-level: echo delivery invariant is preserved by every step. -/
private theorem step_echo_delivery_inv {s s' : State T n} {l : Label T n}
    (h : (bca T n f).step s l s') (src dst : Fin n) (b : T)
    (hsent' : (s'.local_ src).sent dst .echo (some b) = true)
    (ih : (s.local_ src).sent dst .echo (some b) = true →
          s.buffer ⟨src, dst, .echo, some b⟩ = true ∨
          (s.local_ dst).echoRecv src b = true) :
    s'.buffer ⟨src, dst, .echo, some b⟩ = true ∨
    (s'.local_ dst).echoRecv src b = true := by
  match l with
  | .corrupt _ =>
    rw [corrupt_local h] at hsent'
    rcases ih hsent' with hbuf | hrecv
    · left; rw [corrupt_buffer h]; exact hbuf
    · right; rw [corrupt_local h]; exact hrecv
  | .input _ _ =>
    rw [input_sent h src dst .echo (some b)] at hsent'
    rcases ih hsent' with hbuf | hrecv
    · left; rw [input_buffer h]; exact hbuf
    · right; exact step_echoRecv_mono h dst src b hrecv
  | .output _ _ =>
    rw [output_sent h src dst .echo (some b)] at hsent'
    rcases ih hsent' with hbuf | hrecv
    · left; rw [output_buffer h]; exact hbuf
    · right; exact step_echoRecv_mono h dst src b hrecv
  | .send src' dst' t' mv' =>
    by_cases hsrc : src = src'
    · subst hsrc
      rw [send_sent h dst .echo (some b)] at hsent'
      split_ifs at hsent' with heq
      · obtain ⟨rfl, rfl, rfl⟩ := heq; left; exact send_buffer_new h
      · rcases ih hsent' with hbuf | hrecv
        · left; exact send_buffer_mono h _ hbuf
        · right; rw [send_echoRecv h dst src b]; exact hrecv
    · rw [send_sent_other h src (hsrc) dst .echo (some b)] at hsent'
      rcases ih hsent' with hbuf | hrecv
      · left; exact send_buffer_mono h _ hbuf
      · right; rw [send_echoRecv h dst src b]; exact hrecv
  | .recv src' dst' t' mv' =>
    rw [recv_sent h src dst .echo (some b)] at hsent'
    rcases ih hsent' with hbuf | hrecv
    · by_cases hmeq : (⟨src, dst, .echo, some b⟩ : Message T n) = ⟨src', dst', t', mv'⟩
      · have : src = src' ∧ dst = dst' ∧ t' = .echo ∧ mv' = some b := by
          simp [Message.mk.injEq] at hmeq; exact ⟨hmeq.1, hmeq.2.1, hmeq.2.2.1.symm, hmeq.2.2.2.symm⟩
        obtain ⟨rfl, rfl, rfl, rfl⟩ := this
        right; exact recv_echo_echoRecv_set h
      · left; exact recv_buffer_other h hmeq hbuf
    · right; exact step_echoRecv_mono h dst src b hrecv

/-- If echo(some b) was sent from src to dst, it is either in the buffer or received. -/
theorem echo_delivery_inv {s : State T n}
    (hreach : LTS.Reachable (bca T n f) s)
    (src dst : Fin n) (b : T)
    (hsent : (s.local_ src).sent dst .echo (some b) = true) :
    s.buffer ⟨src, dst, .echo, some b⟩ = true ∨
    (s.local_ dst).echoRecv src b = true := by
  induction hreach with
  | init hinit =>
    obtain ⟨hlocal, _, _⟩ := hinit
    simp [hlocal src, LocalState.init] at hsent
  | step hreach' hstep ih =>
    exact step_echo_delivery_inv hstep src dst b hsent ih

/-- Step-level: vote delivery invariant is preserved by every step. -/
private theorem step_vote_delivery_inv {s s' : State T n} {l : Label T n}
    (h : (bca T n f).step s l s') (src dst : Fin n) (v : Val T)
    (hsent' : (s'.local_ src).sent dst .vote v = true)
    (ih : (s.local_ src).sent dst .vote v = true →
          s.buffer ⟨src, dst, .vote, v⟩ = true ∨
          (s.local_ dst).voteRecv src v = true) :
    s'.buffer ⟨src, dst, .vote, v⟩ = true ∨
    (s'.local_ dst).voteRecv src v = true := by
  match l with
  | .corrupt _ =>
    rw [corrupt_local h] at hsent'
    rcases ih hsent' with hbuf | hrecv
    · left; rw [corrupt_buffer h]; exact hbuf
    · right; rw [corrupt_local h]; exact hrecv
  | .input _ _ =>
    rw [input_sent h src dst .vote v] at hsent'
    rcases ih hsent' with hbuf | hrecv
    · left; rw [input_buffer h]; exact hbuf
    · right; exact step_voteRecv_mono h dst src v hrecv
  | .output _ _ =>
    rw [output_sent h src dst .vote v] at hsent'
    rcases ih hsent' with hbuf | hrecv
    · left; rw [output_buffer h]; exact hbuf
    · right; exact step_voteRecv_mono h dst src v hrecv
  | .send src' dst' t' mv' =>
    by_cases hsrc : src = src'
    · subst hsrc
      rw [send_sent h dst .vote v] at hsent'
      split_ifs at hsent' with heq
      · obtain ⟨rfl, rfl, rfl⟩ := heq; left; exact send_buffer_new h
      · rcases ih hsent' with hbuf | hrecv
        · left; exact send_buffer_mono h _ hbuf
        · right; rw [send_voteRecv h dst src v]; exact hrecv
    · rw [send_sent_other h src (hsrc) dst .vote v] at hsent'
      rcases ih hsent' with hbuf | hrecv
      · left; exact send_buffer_mono h _ hbuf
      · right; rw [send_voteRecv h dst src v]; exact hrecv
  | .recv src' dst' t' mv' =>
    rw [recv_sent h src dst .vote v] at hsent'
    rcases ih hsent' with hbuf | hrecv
    · by_cases hmeq : (⟨src, dst, .vote, v⟩ : Message T n) = ⟨src', dst', t', mv'⟩
      · have : src = src' ∧ dst = dst' ∧ t' = .vote ∧ mv' = v := by
          simp [Message.mk.injEq] at hmeq; exact ⟨hmeq.1, hmeq.2.1, hmeq.2.2.1.symm, hmeq.2.2.2.symm⟩
        obtain ⟨rfl, rfl, rfl, rfl⟩ := this
        right; exact recv_vote_voteRecv_set h
      · left; exact recv_buffer_other h hmeq hbuf
    · right; exact step_voteRecv_mono h dst src v hrecv

/-- If vote(v) was sent from src to dst, it is either in the buffer or received. -/
theorem vote_delivery_inv {s : State T n}
    (hreach : LTS.Reachable (bca T n f) s)
    (src dst : Fin n) (v : Val T)
    (hsent : (s.local_ src).sent dst .vote v = true) :
    s.buffer ⟨src, dst, .vote, v⟩ = true ∨
    (s.local_ dst).voteRecv src v = true := by
  induction hreach with
  | init hinit =>
    obtain ⟨hlocal, _, _⟩ := hinit
    simp [hlocal src, LocalState.init] at hsent
  | step hreach' hstep ih =>
    exact step_vote_delivery_inv hstep src dst v hsent ih

/-- At a reachable state, a correct process that has sent echo(some b)
    to any destination has echoed = some b.
    Proof: echo send by correct src sets echoed := some b. The echoed field
    persists. So if sent = true, echoed was set and persists. -/
theorem sent_echo_implies_echoed {s : State T n}
    (hreach : LTS.Reachable (bca T n f) s)
    {p : Fin n} (b : T)
    (hcorr : isCorrect T n s p)
    {dst : Fin n}
    (hsent : (s.local_ p).sent dst .echo (some b) = true) :
    (s.local_ p).echoed = some b := by
  induction hreach with
  | init hinit =>
    obtain ⟨hlocal, _, _⟩ := hinit
    simp [hlocal p, LocalState.init] at hsent
  | step hreach_prev hstep ih =>
    rename_i s_prev l _
    have hcp := step_correct_prev hstep p hcorr
    by_cases hprev : (s_prev.local_ p).sent dst .echo (some b) = true
    · exact step_echoed_persist hstep p b hcorr (ih hcp hprev)
    · -- Newly sent in this step: must be send echo(some b) from p.
      simp only [Bool.not_eq_true] at hprev
      match l with
      | .send src dst' .echo (some b') =>
        by_cases hp : p = src
        · subst hp
          rw [send_sent hstep dst .echo (some b)] at hsent
          split_ifs at hsent with heq
          · have hbb := Option.some.inj heq.2.2
            subst hbb; exact send_echo_echoed_correct hstep hcp
          · exact absurd hsent (by rw [hprev]; simp)
        · rw [send_sent_other hstep p hp dst .echo (some b)] at hsent
          exact absurd hsent (by rw [hprev]; simp)
      | .send src dst' .echo none =>
        by_cases hp : p = src
        · subst hp; obtain ⟨_, rfl⟩ := hstep; simp at hsent
          exact absurd hsent (by rw [hprev]; simp)
        · rw [send_sent_other hstep p hp dst .echo (some b)] at hsent
          exact absurd hsent (by rw [hprev]; simp)
      | .send src dst' .init mv =>
        by_cases hp : p = src
        · subst hp; obtain ⟨_, rfl⟩ := hstep; simp at hsent
          exact absurd hsent (by rw [hprev]; simp)
        · rw [send_sent_other hstep p hp dst .echo (some b)] at hsent
          exact absurd hsent (by rw [hprev]; simp)
      | .send src dst' .vote mv =>
        by_cases hp : p = src
        · subst hp; obtain ⟨_, rfl⟩ := hstep; simp at hsent
          exact absurd hsent (by rw [hprev]; simp)
        · rw [send_sent_other hstep p hp dst .echo (some b)] at hsent
          exact absurd hsent (by rw [hprev]; simp)
      | .corrupt _ =>
        rw [corrupt_local hstep] at hsent; exact absurd hsent (by rw [hprev]; simp)
      | .input _ _ =>
        rw [input_sent hstep p dst .echo (some b)] at hsent
        exact absurd hsent (by rw [hprev]; simp)
      | .output _ _ =>
        rw [output_sent hstep p dst .echo (some b)] at hsent
        exact absurd hsent (by rw [hprev]; simp)
      | .recv _ _ _ _ =>
        rw [recv_sent hstep p dst .echo (some b)] at hsent
        exact absurd hsent (by rw [hprev]; simp)

end DeliveryInvariants

/-! ### Reachable Invariants -/

section ReachableInvariants

variable {T : Type} {n f : Nat} [DecidableEq T]

/-- At a reachable state, corrupted.length ≤ f. -/
theorem corrupted_budget_reachable {s : State T n}
    (hreach : LTS.Reachable (bca T n f) s) :
    s.corrupted.length ≤ f := by
  induction hreach with
  | init hinit => obtain ⟨_, _, hcorr⟩ := hinit; rw [hcorr]; simp
  | step _ hstep ih =>
    rename_i s_prev l s' _
    match l with
    | .corrupt i =>
      obtain ⟨_, hbudget, rfl⟩ := hstep
      simp only [List.length_cons]; omega
    | .send .. => rw [send_corrupted hstep]; exact ih
    | .recv .. => rw [recv_corrupted hstep]; exact ih
    | .output .. => rw [output_corrupted hstep]; exact ih
    | .input .. => rw [input_corrupted hstep]; exact ih

/-- At a reachable state, if countInitRecv ≥ approveThreshold and approveThreshold > 0,
    then approved = true. The threshold positivity holds whenever n > f. -/
theorem countInitRecv_ge_implies_approved {s : State T n}
    (hreach : LTS.Reachable (bca T n f) s)
    (p : Fin n) (b : T)
    (hpos : approveThreshold n f > 0)
    (hge : countInitRecv T n (s.local_ p) b ≥ approveThreshold n f) :
    (s.local_ p).approved b = true := by
  induction hreach with
  | init hinit =>
    obtain ⟨hlocal, _, _⟩ := hinit
    simp only [hlocal p, LocalState.init, countInitRecv] at hge
    simp only [List.filter_false, List.length_nil] at hge; omega
  | step _ hstep ih =>
    rename_i s_prev l s' _
    by_cases hprev_ge : countInitRecv T n (s_prev.local_ p) b ≥ approveThreshold n f
    · exact step_approved_persist hstep p b (ih hprev_ge)
    · -- countInitRecv newly crossed the threshold at this step.
      simp only [not_le] at hprev_ge
      -- Only recv_init(some b) at p=dst with new receipt can increase countInitRecv(p, b)
      -- For all other steps, countInitRecv is unchanged or unchanged, contradicting hge
      match l with
      | .recv src dst .init (some b') =>
        by_cases hp : p = dst
        · subst hp
          by_cases hbb : b = b'
          · subst hbb
            by_cases hdup : (s_prev.local_ p).initRecv src b = false
            · -- Exact count: post = prev + 1
              have hexact := recv_init_countInitRecv_eq hstep hdup
              -- prev + 1 ≥ threshold
              have hthresh : countInitRecv T n (s_prev.local_ p) b + 1 ≥
                  approveThreshold n f := by omega
              -- The step sets approved(b) when old_count + 1 ≥ threshold
              by_cases happr : (s'.local_ p).approved b = true
              · exact happr
              · -- approved = false contradicts threshold being met
                exfalso
                have : (s'.local_ p).approved b = true := by
                  obtain ⟨_, rfl⟩ := hstep
                  simp only [↓reduceIte, hdup]
                  exact if_pos ⟨trivial, hthresh⟩
                rw [this] at happr; simp at happr
            · -- Duplicate receipt: local state unchanged
              simp only [Bool.not_eq_false] at hdup
              have hlocal : (s'.local_ p) = (s_prev.local_ p) := by
                obtain ⟨_, rfl⟩ := hstep; simp [hdup]
              rw [hlocal] at hge; omega
          · -- Different value b': countInitRecv(b) unchanged
            have heq : countInitRecv T n (s'.local_ p) b =
                countInitRecv T n (s_prev.local_ p) b := by
              unfold countInitRecv; congr 1; apply List.filter_congr; intro q _
              obtain ⟨_, rfl⟩ := hstep; simp only [↓reduceIte]
              by_cases hdup : (s_prev.local_ p).initRecv src b' = false
              · simp only [hdup, ↓reduceIte]
                -- if q = src ∧ b = b' then true else old
                -- Since b ≠ b', the conjunction is false
                split_ifs with hcond
                · exact absurd hcond.2 hbb
                · rfl
              · simp [hdup]
            rw [heq] at hge; omega
        · -- p ≠ dst: local_ p unchanged
          have hlocal : (s'.local_ p) = (s_prev.local_ p) := by
            obtain ⟨_, rfl⟩ := hstep; simp [hp]
          rw [hlocal] at hge; omega
      | .recv _ dst .init none =>
        have hlocal : (s'.local_ p) = (s_prev.local_ p) := by
          obtain ⟨_, rfl⟩ := hstep; by_cases hp : p = dst <;> simp [hp]
        rw [hlocal] at hge; omega
      | .corrupt _ => rw [corrupt_local hstep] at hge; omega
      | .send .. =>
        rw [step_countInitRecv_eq hstep p b (by intro _ _ _; simp)] at hge; omega
      | .recv _ _ .echo _ =>
        rw [step_countInitRecv_eq hstep p b (by intro _ _ _; simp)] at hge; omega
      | .recv _ _ .vote _ =>
        rw [step_countInitRecv_eq hstep p b (by intro _ _ _; simp)] at hge; omega
      | .output .. =>
        rw [step_countInitRecv_eq hstep p b (by intro _ _ _; simp)] at hge; omega
      | .input .. =>
        rw [step_countInitRecv_eq hstep p b (by intro _ _ _; simp)] at hge; omega

/-- Output(none) is enabled when p is correct, undecided, has two approved values,
    and enough total votes. -/
theorem output_none_enabled {s : State T n} {p : Fin n}
    (hcorr : isCorrect T n s p)
    (hdec : (s.local_ p).decided = none)
    (v₁ v₂ : T) (hne : v₁ ≠ v₂)
    (happr1 : (s.local_ p).approved v₁ = true)
    (happr2 : (s.local_ p).approved v₂ = true)
    (vals : List (Val T))
    (hvotes : countAnyVoteRecv T n (s.local_ p) vals ≥ returnThreshold n f) :
    (bca T n f).enabled (.output p none) s := by
  exact ⟨_, hcorr, hdec, ⟨⟨v₁, v₂, hne, happr1, happr2⟩, vals, hvotes⟩, rfl⟩

/-- A correct-to-correct vote(none) send is enabled when src has two
    distinct approved values, is vote-consistent, and hasn't sent yet. -/
theorem send_vote_none_enabled {s : State T n} {src dst : Fin n}
    (hcorr : isCorrect T n s src)
    (hsent : (s.local_ src).sent dst .vote none = false)
    (huniq : ∀ w, (s.local_ src).voted w = true → w = none)
    (v₁ v₂ : T) (hne : v₁ ≠ v₂)
    (happr1 : (s.local_ src).approved v₁ = true)
    (happr2 : (s.local_ src).approved v₂ = true) :
    (bca T n f).enabled (.send src dst .vote none) s := by
  refine ⟨_, Or.inr ⟨hcorr, hsent, huniq, v₁, v₂, hne, happr1, happr2⟩, rfl⟩

/-- At a reachable state, approved(b) = true → countInitRecv(b) ≥ approveThreshold.
    Proof: approved is set when countInitRecv + 1 ≥ threshold (exact count gives = old + 1).
    After the step, countInitRecv ≥ threshold. Since countInitRecv is monotone, it stays ≥. -/
theorem approved_implies_countInitRecv_ge {s : State T n}
    (hreach : LTS.Reachable (bca T n f) s)
    (p : Fin n) (b : T)
    (happr : (s.local_ p).approved b = true) :
    countInitRecv T n (s.local_ p) b ≥ approveThreshold n f := by
  induction hreach with
  | init hinit =>
    obtain ⟨hlocal, _, _⟩ := hinit
    simp [hlocal p, LocalState.init] at happr
  | step _ hstep ih =>
    rename_i s_prev l s' _
    by_cases hprev : (s_prev.local_ p).approved b = true
    · -- Already approved: countInitRecv monotone gives ≥
      exact Nat.le_trans (ih hprev) (step_countInitRecv_mono hstep p b)
    · -- Newly approved at this step: only recv_init(some b) at p=dst can set approved
      match l with
      | .recv src dst .init (some b') =>
        by_cases hp : p = dst
        · subst hp
          by_cases hbb : b = b'
          · subst hbb
            by_cases hdup : (s_prev.local_ p).initRecv src b = false
            · -- This step set approved, so old count + 1 ≥ threshold
              have hexact := recv_init_countInitRecv_eq hstep hdup
              -- The fact that approved was set implies old + 1 ≥ threshold
              -- From recv_init_approved_threshold (the existing lemma):
              have := recv_init_approved_threshold hstep hdup hprev happr
              omega
            · simp only [Bool.not_eq_false] at hdup
              have : (s'.local_ p) = (s_prev.local_ p) := by
                obtain ⟨_, rfl⟩ := hstep; simp [hdup]
              rw [this] at happr; exact absurd happr hprev
          · rw [recv_init_approved_other hstep hbb] at happr
            exact absurd happr hprev
        · have : (s'.local_ p) = (s_prev.local_ p) := by
            obtain ⟨_, rfl⟩ := hstep; simp [hp]
          rw [this] at happr; exact absurd happr hprev
      | .recv _ dst .init none =>
        have : (s'.local_ p) = (s_prev.local_ p) := by
          obtain ⟨_, rfl⟩ := hstep; by_cases hp : p = dst <;> simp [hp]
        rw [this] at happr; exact absurd happr hprev
      | .corrupt _ =>
        rw [corrupt_local hstep] at happr; exact absurd happr hprev
      | .send .. =>
        rw [step_approved_eq hstep p b (by intro _ _ _; simp)] at happr
        exact absurd happr hprev
      | .recv _ _ .echo _ =>
        rw [step_approved_eq hstep p b (by intro _ _ _; simp)] at happr
        exact absurd happr hprev
      | .recv _ _ .vote _ =>
        rw [step_approved_eq hstep p b (by intro _ _ _; simp)] at happr
        exact absurd happr hprev
      | .output .. =>
        rw [step_approved_eq hstep p b (by intro _ _ _; simp)] at happr
        exact absurd happr hprev
      | .input .. =>
        rw [step_approved_eq hstep p b (by intro _ _ _; simp)] at happr
        exact absurd happr hprev

/-- At a reachable state, if correct src sent init(some b) to any dst,
    then src's init gate for b is open: input = some b or
    countInitRecv ≥ amplifyThreshold. -/
theorem sent_init_implies_gate {s : State T n}
    (hreach : LTS.Reachable (bca T n f) s)
    {src : Fin n} (hcorr : isCorrect T n s src) (b : T)
    {dst : Fin n}
    (hsent : (s.local_ src).sent dst .init (some b) = true) :
    (s.local_ src).input = some b ∨
    countInitRecv T n (s.local_ src) b ≥ amplifyThreshold f := by
  induction hreach with
  | init hinit =>
    obtain ⟨hlocal, _, _⟩ := hinit
    simp [hlocal src, LocalState.init] at hsent
  | step _ hstep ih =>
    rename_i s_prev l s' _
    have hcp := step_correct_prev hstep src hcorr
    by_cases hprev : (s_prev.local_ src).sent dst .init (some b) = true
    · -- Already sent: gate conditions persist
      rcases ih hcp hprev with hinput | hcount
      · left; exact step_input_persist hstep src b hinput
      · right; exact Nat.le_trans hcount (step_countInitRecv_mono hstep src b)
    · -- Newly sent at this step: must be a send step from src
      simp only [Bool.not_eq_true] at hprev
      match l with
      | .send src' dst' .init (some b') =>
        by_cases hp : src = src'
        · subst hp
          rw [send_sent hstep dst .init (some b)] at hsent
          split_ifs at hsent with heq
          · obtain ⟨_, _, hvv⟩ := heq
            have hbb := Option.some.inj hvv; subst hbb
            -- The send gate was open at pre-state: extract it
            have hgate : (s_prev.local_ src).input = some b ∨
                countInitRecv T n (s_prev.local_ src) b ≥ amplifyThreshold f := by
              rcases hstep.1 with hcorrupt | ⟨_, _, hg⟩
              · exact absurd hcorrupt hcp
              · exact hg
            -- Gate conditions persist to post-state
            rcases hgate with hinput | hamplify
            · left; exact step_input_persist hstep src b hinput
            · right; exact Nat.le_trans hamplify (step_countInitRecv_mono hstep src b)
          · exact absurd hsent (by rw [hprev]; simp)
        · rw [send_sent_other hstep src hp dst .init (some b)] at hsent
          exact absurd hsent (by rw [hprev]; simp)
      | .send src' _ .init none =>
        by_cases hp : src = src'
        · subst hp; rw [send_sent hstep dst .init (some b)] at hsent
          simp at hsent; exact absurd hsent (by rw [hprev]; simp)
        · rw [send_sent_other hstep src hp dst .init (some b)] at hsent
          exact absurd hsent (by rw [hprev]; simp)
      | .send src' _ .echo _ =>
        by_cases hp : src = src'
        · subst hp; rw [send_sent hstep dst .init (some b)] at hsent
          simp at hsent; exact absurd hsent (by rw [hprev]; simp)
        · rw [send_sent_other hstep src hp dst .init (some b)] at hsent
          exact absurd hsent (by rw [hprev]; simp)
      | .send src' _ .vote _ =>
        by_cases hp : src = src'
        · subst hp; rw [send_sent hstep dst .init (some b)] at hsent
          simp at hsent; exact absurd hsent (by rw [hprev]; simp)
        · rw [send_sent_other hstep src hp dst .init (some b)] at hsent
          exact absurd hsent (by rw [hprev]; simp)
      | .corrupt _ =>
        rw [corrupt_local hstep] at hsent; exact absurd hsent (by rw [hprev]; simp)
      | .recv _ _ _ _ =>
        rw [recv_sent hstep src dst .init (some b)] at hsent
        exact absurd hsent (by rw [hprev]; simp)
      | .output _ _ =>
        rw [output_sent hstep src dst .init (some b)] at hsent
        exact absurd hsent (by rw [hprev]; simp)
      | .input _ _ =>
        rw [input_sent hstep src dst .init (some b)] at hsent
        exact absurd hsent (by rw [hprev]; simp)

/-- At a reachable state, a correct process has at most one voted value. -/
theorem voted_unique {s : State T n}
    (hreach : LTS.Reachable (bca T n f) s)
    {p : Fin n} (hp : p ∉ s.corrupted)
    {w₁ w₂ : Val T}
    (h1 : (s.local_ p).voted w₁ = true)
    (h2 : (s.local_ p).voted w₂ = true) :
    w₁ = w₂ := by
  induction hreach with
  | init hinit =>
    obtain ⟨hlocal, _, _⟩ := hinit
    simp [hlocal p, LocalState.init] at h1
  | step hreach_prev hstep ih =>
    rename_i s_prev l _
    have hp_prev := step_correct_prev hstep p hp
    match l with
    | .send src _ .vote mv =>
      by_cases hsrc : p = src
      · subst hsrc
        have hguard : ∀ w, (s_prev.local_ p).voted w = true → w = mv :=
          (hstep.1.resolve_left hp_prev).2.2.1
        have hw1 : w₁ = mv := by
          by_cases heq : w₁ = mv
          · exact heq
          · rw [send_vote_voted_correct_other hstep hp_prev w₁ heq] at h1
            exact hguard w₁ h1
        have hw2 : w₂ = mv := by
          by_cases heq : w₂ = mv
          · exact heq
          · rw [send_vote_voted_correct_other hstep hp_prev w₂ heq] at h2
            exact hguard w₂ h2
        rw [hw1, hw2]
      · rw [send_vote_voted_other hstep p hsrc] at h1 h2
        exact ih hp_prev h1 h2
    | .send _ _ .init _ =>
      rw [send_init_voted hstep p] at h1 h2; exact ih hp_prev h1 h2
    | .send _ _ .echo _ =>
      rw [send_echo_voted hstep p] at h1 h2; exact ih hp_prev h1 h2
    | .corrupt _ =>
      rw [corrupt_local hstep] at h1 h2; exact ih hp_prev h1 h2
    | .recv _ _ .init _ =>
      rw [recv_init_voted hstep p] at h1 h2; exact ih hp_prev h1 h2
    | .recv _ _ .echo _ =>
      rw [recv_echo_voted hstep p] at h1 h2; exact ih hp_prev h1 h2
    | .recv _ _ .vote _ =>
      rw [recv_vote_voted hstep p] at h1 h2; exact ih hp_prev h1 h2
    | .output _ _ =>
      rw [output_voted hstep p] at h1 h2; exact ih hp_prev h1 h2
    | .input _ _ =>
      rw [input_voted hstep p] at h1 h2; exact ih hp_prev h1 h2

/-- voted(mv) persists for correct processes (unifying some/none). -/
theorem step_voted_val_persist {s s' : State T n} {l : Label T n}
    (h : (bca T n f).step s l s') (p : Fin n) (mv : Val T)
    (hcorr : isCorrect T n s' p) (hvoted : (s.local_ p).voted mv = true) :
    (s'.local_ p).voted mv = true :=
  match mv with
  | some b => step_voted_persist h p b hcorr hvoted
  | none => step_voted_none_persist h p hcorr hvoted

/-- At a reachable state, if correct src sent vote(mv), then voted(mv) = true. -/
theorem sent_vote_implies_voted {s : State T n}
    (hreach : LTS.Reachable (bca T n f) s)
    {src : Fin n} (mv : Val T) (hp : src ∉ s.corrupted)
    {dst : Fin n} (hsent : (s.local_ src).sent dst .vote mv = true) :
    (s.local_ src).voted mv = true := by
  induction hreach with
  | init hinit =>
    obtain ⟨hlocal, _, _⟩ := hinit
    simp [hlocal src, LocalState.init] at hsent
  | step hreach_prev hstep ih =>
    rename_i s_prev l _
    have hp_prev := step_correct_prev hstep src hp
    by_cases hprev_sent : (s_prev.local_ src).sent dst .vote mv = true
    · exact step_voted_val_persist hstep src mv hp (ih hp_prev hprev_sent)
    · simp only [Bool.not_eq_true] at hprev_sent
      match l with
      | .send src' dst' .vote mv' =>
        by_cases hsrc : src = src'
        · subst hsrc
          rw [send_sent hstep dst .vote mv] at hsent
          split_ifs at hsent with heq
          · obtain ⟨_, _, rfl⟩ := heq
            exact send_vote_voted_correct hstep hp_prev
          · exact absurd hsent (by simp [hprev_sent])
        · rw [send_sent_other hstep src hsrc dst .vote mv] at hsent
          exact absurd hsent (by simp [hprev_sent])
      | .send src' _ .init _ =>
        by_cases hsrc : src = src'
        · subst hsrc; rw [send_sent hstep dst .vote mv] at hsent
          simp_all
        · rw [send_sent_other hstep src hsrc dst .vote mv] at hsent
          exact absurd hsent (by simp [hprev_sent])
      | .send src' _ .echo _ =>
        by_cases hsrc : src = src'
        · subst hsrc; rw [send_sent hstep dst .vote mv] at hsent
          simp_all
        · rw [send_sent_other hstep src hsrc dst .vote mv] at hsent
          exact absurd hsent (by simp [hprev_sent])
      | .recv .. =>
        rw [recv_sent hstep src dst .vote mv] at hsent
        exact absurd hsent (by simp [hprev_sent])
      | .corrupt _ =>
        rw [corrupt_local hstep] at hsent
        exact absurd hsent (by simp [hprev_sent])
      | .output _ _ =>
        rw [output_sent hstep src dst .vote mv] at hsent
        exact absurd hsent (by simp [hprev_sent])
      | .input _ _ =>
        rw [input_sent hstep src dst .vote mv] at hsent
        exact absurd hsent (by simp [hprev_sent])

/-! ### Additional invariants for BCA liveness proofs -/

/-- Recv echo preserves initRecv at the destination. -/
private theorem recv_echo_initRecv {s s' : State T n} {src' dst' mv'}
    (h : (bca T n f).step s (.recv src' dst' .echo mv') s')
    (q : Fin n) (b : T) :
    (s'.local_ dst').initRecv q b = (s.local_ dst').initRecv q b := by
  obtain ⟨_, rfl⟩ := h; simp only [↓reduceIte]
  rcases mv' with _ | b'
  · rfl
  · by_cases hdup : (s.local_ dst').echoRecv src' b' = false
    · simp [hdup]
    · simp only [Bool.not_eq_false] at hdup; simp [hdup]

/-- Recv vote preserves initRecv at the destination. -/
private theorem recv_vote_initRecv {s s' : State T n} {src' dst' mv'}
    (h : (bca T n f).step s (.recv src' dst' .vote mv') s')
    (q : Fin n) (b : T) :
    (s'.local_ dst').initRecv q b = (s.local_ dst').initRecv q b := by
  obtain ⟨_, rfl⟩ := h; simp only [↓reduceIte]
  by_cases hdup : (s.local_ dst').voteRecv src' mv' = false
  · simp [hdup]
  · simp only [Bool.not_eq_false] at hdup; simp [hdup]

/-- At a reachable state, if a message is in the buffer, the sender has sent it. -/
theorem buffer_implies_sent {s : State T n}
    (hreach : LTS.Reachable (bca T n f) s)
    {src dst : Fin n} {t : MsgType} {mv : Val T}
    (hbuf : s.buffer ⟨src, dst, t, mv⟩ = true) :
    (s.local_ src).sent dst t mv = true := by
  induction hreach with
  | init hinit =>
    obtain ⟨_, hb, _⟩ := hinit
    exact absurd (hb _ ▸ hbuf) Bool.false_ne_true
  | step hreach_prev hstep ih =>
    rename_i s_prev _l _
    by_cases hprev : s_prev.buffer ⟨src, dst, t, mv⟩ = true
    · exact step_sent_mono hstep src dst t mv (ih hprev)
    · simp only [Bool.not_eq_true] at hprev
      -- The buffer entry was NOT true at s_prev. If it's true at s,
      -- then the current step must have SET it (send) or we have a contradiction.
      match _l with
      | .send src' dst' t' mv' =>
        by_cases heq : src = src' ∧ dst = dst' ∧ t = t' ∧ mv = mv'
        · obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
          rw [send_sent hstep dst t mv]; simp
        · -- Different message: send doesn't change our buffer entry
          have hne : ¬ (⟨src, dst, t, mv⟩ : Message T n) = ⟨src', dst', t', mv'⟩ := by
            intro h; simp only [Message.mk.injEq] at h; exact heq h
          obtain ⟨_, rfl⟩ := hstep; dsimp only at hbuf
          rw [if_neg hne] at hbuf; exact absurd hbuf (by rw [hprev]; simp)
      | .recv src' dst' t' mv' =>
        -- Recv clears one buffer entry; either ours (contradiction) or another
        obtain ⟨_, rfl⟩ := hstep; dsimp only at hbuf
        by_cases heq : (⟨src, dst, t, mv⟩ : Message T n) = ⟨src', dst', t', mv'⟩
        · rw [if_pos heq] at hbuf; exact absurd hbuf (by simp)
        · rw [if_neg heq] at hbuf; exact absurd hbuf (by rw [hprev]; simp)
      | .corrupt _ => rw [corrupt_buffer hstep] at hbuf; exact absurd hbuf (by rw [hprev]; simp)
      | .output _ _ => obtain ⟨_, _, _, rfl⟩ := hstep; exact absurd hbuf (by rw [hprev]; simp)
      | .input _ _ => obtain ⟨_, rfl⟩ := hstep; exact absurd hbuf (by rw [hprev]; simp)

/-- At a reachable state, initRecv(dst, src, b) → sent(src, dst, init, some b).
    Proof: track when initRecv was first set — only a recv-init step can set it,
    and that step consumes a buffer entry that implies sent. -/
theorem initRecv_implies_sent {s : State T n}
    (hreach : LTS.Reachable (bca T n f) s)
    {src dst : Fin n} {b : T}
    (hinitRecv : (s.local_ dst).initRecv src b = true) :
    (s.local_ src).sent dst .init (some b) = true := by
  induction hreach with
  | init hinit =>
    obtain ⟨hlocal, _, _⟩ := hinit
    simp [hlocal dst, LocalState.init] at hinitRecv
  | step hreach_prev hstep ih =>
    rename_i s_prev _l _
    by_cases hprev : (s_prev.local_ dst).initRecv src b = true
    · exact step_sent_mono hstep src dst .init (some b) (ih hprev)
    · simp only [Bool.not_eq_true] at hprev
      -- initRecv was newly set → must be recv src dst .init (some b)
      match _l with
      | .recv src' dst' .init (some b') =>
        by_cases hdst : dst = dst'
        · subst hdst
          by_cases hsrcb : src = src' ∧ b = b'
          · obtain ⟨rfl, rfl⟩ := hsrcb
            exact step_sent_mono hstep src dst .init (some b)
              (buffer_implies_sent hreach_prev hstep.1)
          · -- Different source or value: initRecv unchanged for (src, b)
            obtain ⟨_, rfl⟩ := hstep; simp only [↓reduceIte] at hinitRecv
            by_cases hdup : (s_prev.local_ dst).initRecv src' b' = false
            · simp only [hdup, ↓reduceIte] at hinitRecv
              -- The if condition is (q = src' ∧ w = b')
              by_cases hcond : src = src' ∧ b = b'
              · exact absurd hcond hsrcb
              · simp only [hcond, ↓reduceIte] at hinitRecv
                exact absurd hinitRecv (by simp [hprev])
            · simp only [Bool.not_eq_false] at hdup; simp only [hdup, ↓reduceIte] at hinitRecv
              exact absurd hinitRecv (by simp [hprev])
        · rw [recv_local_other hstep dst hdst] at hinitRecv
          exact absurd hinitRecv (by simp [hprev])
      | .recv _ dst' .init none =>
        by_cases hdst : dst = dst'
        · subst hdst; obtain ⟨_, rfl⟩ := hstep; simp only [↓reduceIte] at hinitRecv
          exact absurd hinitRecv (by simp [hprev])
        · rw [recv_local_other hstep dst hdst] at hinitRecv
          exact absurd hinitRecv (by simp [hprev])
      | .recv _ dst' .echo _ =>
        by_cases hdst : dst = dst'
        · subst hdst; rw [recv_echo_initRecv hstep src b] at hinitRecv
          exact absurd hinitRecv (by simp [hprev])
        · rw [recv_local_other hstep dst hdst] at hinitRecv
          exact absurd hinitRecv (by simp [hprev])
      | .recv _ dst' .vote _ =>
        by_cases hdst : dst = dst'
        · subst hdst; rw [recv_vote_initRecv hstep src b] at hinitRecv
          exact absurd hinitRecv (by simp [hprev])
        · rw [recv_local_other hstep dst hdst] at hinitRecv
          exact absurd hinitRecv (by simp [hprev])
      | .send _ _ _ _ =>
        rw [send_initRecv hstep dst src b] at hinitRecv
        exact absurd hinitRecv (by simp [hprev])
      | .corrupt _ =>
        rw [corrupt_local hstep] at hinitRecv
        exact absurd hinitRecv (by simp [hprev])
      | .output i _ =>
        obtain ⟨_, _, _, rfl⟩ := hstep
        by_cases hp : dst = i
        · subst hp; simp only [↓reduceIte] at hinitRecv
          exact absurd hinitRecv (by simp [hprev])
        · simp only [hp, ↓reduceIte] at hinitRecv
          exact absurd hinitRecv (by simp [hprev])
      | .input i _ =>
        obtain ⟨_, rfl⟩ := hstep
        by_cases hp : dst = i
        · subst hp; simp only [↓reduceIte] at hinitRecv
          exact absurd hinitRecv (by simp [hprev])
        · simp only [hp, ↓reduceIte] at hinitRecv
          exact absurd hinitRecv (by simp [hprev])

/-- echoRecv(q, r, b) → sent(r, q, echo, some b). -/
theorem echoRecv_implies_sent {s : State T n}
    (hreach : LTS.Reachable (bca T n f) s)
    {q r : Fin n} {b : T}
    (hrecv : (s.local_ q).echoRecv r b = true) :
    (s.local_ r).sent q .echo (some b) = true := by
  induction hreach with
  | init hinit =>
    obtain ⟨hlocal, _, _⟩ := hinit
    simp [hlocal q, LocalState.init] at hrecv
  | step hreach_prev hstep ih =>
    rename_i s_prev _l _
    by_cases hprev : (s_prev.local_ q).echoRecv r b = true
    · exact step_sent_mono hstep r q .echo (some b) (ih hprev)
    · simp only [Bool.not_eq_true] at hprev
      match _l with
      | .recv src' dst' .echo (some b') =>
        by_cases hdst : q = dst'
        · subst hdst
          by_cases hsrcb : r = src' ∧ b = b'
          · obtain ⟨rfl, rfl⟩ := hsrcb
            exact step_sent_mono hstep r q .echo (some b)
              (buffer_implies_sent hreach_prev hstep.1)
          · obtain ⟨_, rfl⟩ := hstep; simp only [↓reduceIte] at hrecv
            by_cases hdup : (s_prev.local_ q).echoRecv src' b' = false
            · simp only [hdup, ↓reduceIte] at hrecv
              by_cases hcond : r = src' ∧ b = b'
              · exact absurd hcond hsrcb
              · simp only [hcond, ↓reduceIte] at hrecv
                exact absurd hrecv (by simp [hprev])
            · simp only [Bool.not_eq_false] at hdup; simp only [hdup, ↓reduceIte] at hrecv
              exact absurd hrecv (by simp [hprev])
        · rw [recv_local_other hstep q hdst] at hrecv
          exact absurd hrecv (by simp [hprev])
      | .recv _ dst' .echo none =>
        by_cases hdst : q = dst'
        · subst hdst; obtain ⟨_, rfl⟩ := hstep; simp only [↓reduceIte] at hrecv
          exact absurd hrecv (by simp [hprev])
        · rw [recv_local_other hstep q hdst] at hrecv
          exact absurd hrecv (by simp [hprev])
      | .recv _ dst' .init _ =>
        by_cases hdst : q = dst'
        · subst hdst
          have := step_echoRecv_prev hstep q r b hrecv (by intro d h; cases h)
          exact absurd this (by simp [hprev])
        · rw [recv_local_other hstep q hdst] at hrecv
          exact absurd hrecv (by simp [hprev])
      | .recv _ dst' .vote _ =>
        by_cases hdst : q = dst'
        · subst hdst
          have := step_echoRecv_prev hstep q r b hrecv (by intro d h; cases h)
          exact absurd this (by simp [hprev])
        · rw [recv_local_other hstep q hdst] at hrecv
          exact absurd hrecv (by simp [hprev])
      | .corrupt _ =>
        rw [corrupt_local hstep] at hrecv; exact absurd hrecv (by simp [hprev])
      | .send .. =>
        rw [send_echoRecv hstep q r b] at hrecv
        exact absurd hrecv (by simp [hprev])
      | .output .. =>
        have := step_echoRecv_prev hstep q r b hrecv (by intro d h; cases h)
        exact absurd this (by simp [hprev])
      | .input .. =>
        have := step_echoRecv_prev hstep q r b hrecv (by intro d h; cases h)
        exact absurd this (by simp [hprev])

/-- voted(none) → two distinct approved values. -/
theorem voted_none_implies_two_approved {s : State T n}
    (hreach : LTS.Reachable (bca T n f) s)
    {p : Fin n} (hp : p ∉ s.corrupted)
    (hvoted : (s.local_ p).voted none = true) :
    ∃ b₁ b₂, b₁ ≠ b₂ ∧ (s.local_ p).approved b₁ = true ∧
      (s.local_ p).approved b₂ = true := by
  induction hreach with
  | init hinit =>
    obtain ⟨hlocal, _, _⟩ := hinit
    simp [hlocal p, LocalState.init] at hvoted
  | step hreach_prev hstep ih =>
    rename_i s_prev _l _
    have hp_prev := step_correct_prev hstep p hp
    match _l with
    | .send src _ .vote mv =>
      by_cases hsrc : p = src
      · subst hsrc
        by_cases hprev_voted : (s_prev.local_ p).voted none = true
        · obtain ⟨b₁, b₂, hne, h1, h2⟩ := ih hp_prev hprev_voted
          exact ⟨b₁, b₂, hne, step_approved_persist hstep p b₁ h1,
                 step_approved_persist hstep p b₂ h2⟩
        · simp only [Bool.not_eq_true] at hprev_voted
          have hmv : mv = none := by
            by_contra hne
            rw [send_vote_voted_correct_other hstep hp_prev none (Ne.symm hne)] at hvoted
            exact absurd hvoted (by rw [hprev_voted]; simp)
          subst hmv
          rcases hstep.1 with hcorrupt | ⟨_, _, _, hgate⟩
          · exact absurd hcorrupt hp_prev
          · obtain ⟨v₁, v₂, hne, h1, h2⟩ := hgate
            exact ⟨v₁, v₂, hne, step_approved_persist hstep p v₁ h1,
                   step_approved_persist hstep p v₂ h2⟩
      · rw [send_vote_voted_other hstep p hsrc] at hvoted
        obtain ⟨b₁, b₂, hne, h1, h2⟩ := ih hp_prev hvoted
        exact ⟨b₁, b₂, hne, step_approved_persist hstep p b₁ h1,
               step_approved_persist hstep p b₂ h2⟩
    | .send _ _ .init _ =>
      rw [send_init_voted hstep] at hvoted
      obtain ⟨b₁, b₂, hne, h1, h2⟩ := ih hp_prev hvoted
      exact ⟨b₁, b₂, hne, step_approved_persist hstep p b₁ h1,
             step_approved_persist hstep p b₂ h2⟩
    | .send _ _ .echo _ =>
      rw [send_echo_voted hstep] at hvoted
      obtain ⟨b₁, b₂, hne, h1, h2⟩ := ih hp_prev hvoted
      exact ⟨b₁, b₂, hne, step_approved_persist hstep p b₁ h1,
             step_approved_persist hstep p b₂ h2⟩
    | .recv _ _ .init _ =>
      rw [recv_init_voted hstep] at hvoted
      obtain ⟨b₁, b₂, hne, h1, h2⟩ := ih hp_prev hvoted
      exact ⟨b₁, b₂, hne, step_approved_persist hstep p b₁ h1,
             step_approved_persist hstep p b₂ h2⟩
    | .recv _ _ .echo _ =>
      rw [recv_echo_voted hstep] at hvoted
      obtain ⟨b₁, b₂, hne, h1, h2⟩ := ih hp_prev hvoted
      exact ⟨b₁, b₂, hne, step_approved_persist hstep p b₁ h1,
             step_approved_persist hstep p b₂ h2⟩
    | .recv _ _ .vote _ =>
      rw [recv_vote_voted hstep] at hvoted
      obtain ⟨b₁, b₂, hne, h1, h2⟩ := ih hp_prev hvoted
      exact ⟨b₁, b₂, hne, step_approved_persist hstep p b₁ h1,
             step_approved_persist hstep p b₂ h2⟩
    | .output .. =>
      rw [output_voted hstep] at hvoted
      obtain ⟨b₁, b₂, hne, h1, h2⟩ := ih hp_prev hvoted
      exact ⟨b₁, b₂, hne, step_approved_persist hstep p b₁ h1,
             step_approved_persist hstep p b₂ h2⟩
    | .input .. =>
      rw [input_voted hstep] at hvoted
      obtain ⟨b₁, b₂, hne, h1, h2⟩ := ih hp_prev hvoted
      exact ⟨b₁, b₂, hne, step_approved_persist hstep p b₁ h1,
             step_approved_persist hstep p b₂ h2⟩
    | .corrupt _ =>
      rw [corrupt_local hstep] at hvoted
      obtain ⟨b₁, b₂, hne, h1, h2⟩ := ih hp_prev hvoted
      exact ⟨b₁, b₂, hne, step_approved_persist hstep p b₁ h1,
             step_approved_persist hstep p b₂ h2⟩

/-- voted(some b) → countEchoRecv(p, b) ≥ echoThreshold. -/
theorem voted_binary_implies_echoRecv {s : State T n}
    (hreach : LTS.Reachable (bca T n f) s)
    {p : Fin n} (hp : p ∉ s.corrupted) {b : T}
    (hvoted : (s.local_ p).voted (some b) = true) :
    countEchoRecv T n (s.local_ p) b ≥ echoThreshold n f := by
  induction hreach with
  | init hinit =>
    obtain ⟨hlocal, _, _⟩ := hinit
    simp [hlocal p, LocalState.init] at hvoted
  | step hreach_prev hstep ih =>
    rename_i s_prev _l _
    have hp_prev := step_correct_prev hstep p hp
    match _l with
    | .send src _ .vote mv =>
      by_cases hsrc : p = src
      · subst hsrc
        by_cases hprev : (s_prev.local_ p).voted (some b) = true
        · exact Nat.le_trans (ih hp_prev hprev) (step_countEchoRecv_mono hstep p b)
        · simp only [Bool.not_eq_true] at hprev
          have hmv : mv = some b := by
            by_contra hne
            rw [send_vote_voted_correct_other hstep hp_prev (some b) (Ne.symm hne)] at hvoted
            exact absurd hvoted (by rw [hprev]; simp)
          subst hmv
          rcases hstep.1 with hcorrupt | ⟨_, _, _, hgate⟩
          · exact absurd hcorrupt hp_prev
          · exact Nat.le_trans hgate (step_countEchoRecv_mono hstep p b)
      · rw [send_vote_voted_other hstep p hsrc] at hvoted
        exact Nat.le_trans (ih hp_prev hvoted) (step_countEchoRecv_mono hstep p b)
    | .send _ _ .init _ =>
      rw [send_init_voted hstep] at hvoted
      exact Nat.le_trans (ih hp_prev hvoted) (step_countEchoRecv_mono hstep p b)
    | .send _ _ .echo _ =>
      rw [send_echo_voted hstep] at hvoted
      exact Nat.le_trans (ih hp_prev hvoted) (step_countEchoRecv_mono hstep p b)
    | .recv _ _ .init _ =>
      rw [recv_init_voted hstep] at hvoted
      exact Nat.le_trans (ih hp_prev hvoted) (step_countEchoRecv_mono hstep p b)
    | .recv _ _ .echo _ =>
      rw [recv_echo_voted hstep] at hvoted
      exact Nat.le_trans (ih hp_prev hvoted) (step_countEchoRecv_mono hstep p b)
    | .recv _ _ .vote _ =>
      rw [recv_vote_voted hstep] at hvoted
      exact Nat.le_trans (ih hp_prev hvoted) (step_countEchoRecv_mono hstep p b)
    | .output .. =>
      rw [output_voted hstep] at hvoted
      exact Nat.le_trans (ih hp_prev hvoted) (step_countEchoRecv_mono hstep p b)
    | .input .. =>
      rw [input_voted hstep] at hvoted
      exact Nat.le_trans (ih hp_prev hvoted) (step_countEchoRecv_mono hstep p b)
    | .corrupt _ =>
      rw [corrupt_local hstep] at hvoted
      exact Nat.le_trans (ih hp_prev hvoted) (step_countEchoRecv_mono hstep p b)

end ReachableInvariants

end BCA_LTS
