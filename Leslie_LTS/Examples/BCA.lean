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

end StepHelpers

end BCA_LTS
