import Leslie.Action
import Leslie.Gadgets.SetFn

open TLA

/-! ## Directory-based MSI Cache Coherence Protocol — Model

    Types, state, named state transformers, frame simp-lemmas,
    actions, init, and transition relation.
    No proofs. Imported by all other files in this module.
-/

namespace DirectoryMSI

abbrev Val := Nat

-- ── Message types ──────────────────────────────────────────────────────────

inductive ReqCmd where
  | empty | getS | getM
  deriving DecidableEq, Repr, BEq

inductive D2CCmd where
  | empty | gntS | gntE | inv | fetch
  deriving DecidableEq, Repr, BEq

inductive C2DCmd where
  | empty | ack
  deriving DecidableEq, Repr, BEq

structure ReqMsg where
  cmd  : ReqCmd := .empty
  data : Val    := 0
  deriving DecidableEq, Repr

structure D2CMsg where
  cmd  : D2CCmd := .empty
  data : Val    := 0
  deriving DecidableEq, Repr

structure C2DMsg where
  cmd  : C2DCmd := .empty
  data : Val    := 0
  deriving DecidableEq, Repr

-- ── Cache / Directory state types ─────────────────────────────────────────

inductive CState where
  | M | S | I
  deriving DecidableEq, Repr, BEq

inductive DirSt where
  | Uncached | Shared | Exclusive
  deriving DecidableEq, Repr, BEq

structure CacheEntry where
  state : CState := .I
  data  : Val    := 0
  deriving DecidableEq, Repr

-- ── Global state ──────────────────────────────────────────────────────────

structure MState (n : Nat) where
  cache   : Fin n → CacheEntry
  reqChan : Fin n → ReqMsg
  d2cChan : Fin n → D2CMsg
  c2dChan : Fin n → C2DMsg
  dirSt   : DirSt
  shrSet  : Fin n → Bool
  exNode  : Fin n
  curCmd  : ReqCmd
  curNode : Fin n
  invSet  : Fin n → Bool
  memData : Val
  auxData : Val

-- ── setFn helper ──────────────────────────────────────────────────────────

-- ── Named state-transformer helpers ───────────────────────────────────────

-- Action 1: processor sends GetS (no directory state change)
-- (pure channel write, no named transformer needed — done inline)

-- Action 3: directory grants S when Uncached
def recvGetS_UncachedState {n} (s : MState n) (i : Fin n) : MState n :=
  { s with
    d2cChan := setFn s.d2cChan i { cmd := .gntS, data := s.memData }
    shrSet  := setFn s.shrSet  i true
    dirSt   := .Shared
    reqChan := setFn s.reqChan i {} }

-- Action 4: directory grants S when already Shared
def recvGetS_SharedState {n} (s : MState n) (i : Fin n) : MState n :=
  { s with
    d2cChan := setFn s.d2cChan i { cmd := .gntS, data := s.memData }
    shrSet  := setFn s.shrSet  i true
    reqChan := setFn s.reqChan i {} }

-- Action 5: directory sends fetch to exclusive holder when GetS arrives
def recvGetS_ExclusiveState {n} (s : MState n) (i : Fin n) : MState n :=
  { s with
    d2cChan := setFn s.d2cChan s.exNode { cmd := .fetch, data := 0 }
    curCmd  := .getS
    curNode := i
    reqChan := setFn s.reqChan i {} }

-- Action 6: directory grants E when Uncached
def recvGetM_UncachedState {n} (s : MState n) (i : Fin n) : MState n :=
  { s with
    d2cChan := setFn s.d2cChan i { cmd := .gntE, data := s.memData }
    exNode  := i
    dirSt   := .Exclusive
    reqChan := setFn s.reqChan i {}
    auxData := s.memData }

-- Action 7: directory starts invalidation when GetM arrives in Shared state
def recvGetM_SharedState {n} (s : MState n) (i : Fin n) : MState n :=
  { s with
    curCmd  := .getM
    curNode := i
    invSet  := setFn s.shrSet i false
    shrSet  := setFn s.shrSet i false
    reqChan := setFn s.reqChan i {} }

-- Action 8: directory sends inv to exclusive holder when GetM arrives (Exclusive state)
def recvGetM_ExclusiveState {n} (s : MState n) (i : Fin n) : MState n :=
  { s with
    d2cChan := setFn s.d2cChan s.exNode { cmd := .inv, data := 0 }
    curCmd  := .getM
    curNode := i
    reqChan := setFn s.reqChan i {} }

-- Action 9: directory sends a pending invalidation to node j
def sendInvState {n} (s : MState n) (j : Fin n) : MState n :=
  { s with
    d2cChan := setFn s.d2cChan j { cmd := .inv, data := 0 }
    invSet  := setFn s.invSet  j false }

-- Action 10: after all sharer acks received (GetM_Shared case), grant E to curNode
--   shrSet is already cleared per ack; just send grant and update directory state.
def sendGntE_AfterSharedState {n} (s : MState n) : MState n :=
  { s with
    d2cChan := setFn s.d2cChan s.curNode { cmd := .gntE, data := s.memData }
    dirSt   := .Exclusive
    exNode  := s.curNode
    curCmd  := .empty
    auxData := s.memData }

-- Action 11: cache receives gntS
def recvGntSState {n} (s : MState n) (i : Fin n) : MState n :=
  { s with
    cache   := setFn s.cache   i { state := .S, data := (s.d2cChan i).data }
    d2cChan := setFn s.d2cChan i {} }

-- Action 12: cache receives gntE
def recvGntEState {n} (s : MState n) (i : Fin n) : MState n :=
  { s with
    cache   := setFn s.cache   i { state := .M, data := (s.d2cChan i).data }
    d2cChan := setFn s.d2cChan i {} }

-- Action 13: cache receives inv, sends ack with data
def recvInvState {n} (s : MState n) (i : Fin n) : MState n :=
  { s with
    cache   := setFn s.cache   i { (s.cache i) with state := .I }
    c2dChan := setFn s.c2dChan i { cmd := .ack, data := (s.cache i).data }
    d2cChan := setFn s.d2cChan i {} }

-- Action 14: cache receives fetch (from exclusive holder), sends ack with data
def recvFetchState {n} (s : MState n) (i : Fin n) : MState n :=
  { s with
    cache   := setFn s.cache   i { (s.cache i) with state := .I }
    c2dChan := setFn s.c2dChan i { cmd := .ack, data := (s.cache i).data }
    d2cChan := setFn s.d2cChan i {} }

-- Action 15: directory receives ack in GetM/Shared context — clears ack and shrSet entry
def recvAck_GetM_SharedState {n} (s : MState n) (j : Fin n) : MState n :=
  { s with
    c2dChan := setFn s.c2dChan j {}
    shrSet  := setFn s.shrSet j false }

-- Action 16a: directory receives writeback ack from old M-holder (GetM/Exclusive case)
--   Writes data to memory, becomes Uncached. curCmd stays getM — grant sent separately.
def recvAck_GetM_ExclusiveState {n} (s : MState n) (j : Fin n) : MState n :=
  { s with
    memData := (s.c2dChan j).data
    auxData := (s.c2dChan j).data
    c2dChan := setFn s.c2dChan j {}
    dirSt   := .Uncached }

-- Action 16b: directory sends gntE to new requester after exclusive writeback
def sendGntE_AfterExclusiveState {n} (s : MState n) : MState n :=
  { s with
    d2cChan := setFn s.d2cChan s.curNode { cmd := .gntE, data := s.memData }
    dirSt   := .Exclusive
    exNode  := s.curNode
    curCmd  := .empty }

-- Action 17a: directory receives fetch ack from old M-holder (GetS/Exclusive case)
--   Writes data to memory, becomes Uncached. curCmd stays getS — grant sent separately.
def recvAck_GetSState {n} (s : MState n) (j : Fin n) : MState n :=
  { s with
    memData := (s.c2dChan j).data
    auxData := (s.c2dChan j).data
    c2dChan := setFn s.c2dChan j {}
    dirSt   := .Uncached }

-- Action 17b: directory sends gntS to pending GetS requester after fetch writeback
def sendGntS_AfterFetchState {n} (s : MState n) : MState n :=
  { s with
    d2cChan := setFn s.d2cChan s.curNode { cmd := .gntS, data := s.memData }
    dirSt   := .Shared
    shrSet  := setFn s.shrSet s.curNode true
    curCmd  := .empty }

-- ── Frame simp-lemmas for recvGetS_UncachedState ──────────────────────────

@[simp] theorem recvGetS_UncachedState_cache   {n} (s : MState n) (i) : (recvGetS_UncachedState s i).cache   = s.cache   := rfl
@[simp] theorem recvGetS_UncachedState_reqChan_self {n} (s : MState n) (i) : (recvGetS_UncachedState s i).reqChan i = {} := by simp [recvGetS_UncachedState, setFn]
@[simp] theorem recvGetS_UncachedState_reqChan_ne   {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : (recvGetS_UncachedState s i).reqChan j = s.reqChan j := by simp [recvGetS_UncachedState, h]
@[simp] theorem recvGetS_UncachedState_d2cChan_self {n} (s : MState n) (i) : (recvGetS_UncachedState s i).d2cChan i = { cmd := .gntS, data := s.memData } := by simp [recvGetS_UncachedState, setFn]
@[simp] theorem recvGetS_UncachedState_d2cChan_ne   {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : (recvGetS_UncachedState s i).d2cChan j = s.d2cChan j := by simp [recvGetS_UncachedState, h]
@[simp] theorem recvGetS_UncachedState_c2dChan {n} (s : MState n) (i) : (recvGetS_UncachedState s i).c2dChan = s.c2dChan := rfl
@[simp] theorem recvGetS_UncachedState_dirSt   {n} (s : MState n) (i) : (recvGetS_UncachedState s i).dirSt   = .Shared  := rfl
@[simp] theorem recvGetS_UncachedState_shrSet_self {n} (s : MState n) (i) : (recvGetS_UncachedState s i).shrSet i = true := by simp [recvGetS_UncachedState, setFn]
@[simp] theorem recvGetS_UncachedState_shrSet_ne   {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : (recvGetS_UncachedState s i).shrSet j = s.shrSet j := by simp [recvGetS_UncachedState, h]
@[simp] theorem recvGetS_UncachedState_exNode  {n} (s : MState n) (i) : (recvGetS_UncachedState s i).exNode  = s.exNode  := rfl
@[simp] theorem recvGetS_UncachedState_curCmd  {n} (s : MState n) (i) : (recvGetS_UncachedState s i).curCmd  = s.curCmd  := rfl
@[simp] theorem recvGetS_UncachedState_curNode {n} (s : MState n) (i) : (recvGetS_UncachedState s i).curNode = s.curNode := rfl
@[simp] theorem recvGetS_UncachedState_invSet  {n} (s : MState n) (i) : (recvGetS_UncachedState s i).invSet  = s.invSet  := rfl
@[simp] theorem recvGetS_UncachedState_memData {n} (s : MState n) (i) : (recvGetS_UncachedState s i).memData = s.memData := rfl
@[simp] theorem recvGetS_UncachedState_auxData {n} (s : MState n) (i) : (recvGetS_UncachedState s i).auxData = s.auxData := rfl

-- ── Frame simp-lemmas for recvGetS_SharedState ────────────────────────────

@[simp] theorem recvGetS_SharedState_cache   {n} (s : MState n) (i) : (recvGetS_SharedState s i).cache   = s.cache   := rfl
@[simp] theorem recvGetS_SharedState_reqChan_self {n} (s : MState n) (i) : (recvGetS_SharedState s i).reqChan i = {} := by simp [recvGetS_SharedState, setFn]
@[simp] theorem recvGetS_SharedState_reqChan_ne   {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : (recvGetS_SharedState s i).reqChan j = s.reqChan j := by simp [recvGetS_SharedState, h]
@[simp] theorem recvGetS_SharedState_d2cChan_self {n} (s : MState n) (i) : (recvGetS_SharedState s i).d2cChan i = { cmd := .gntS, data := s.memData } := by simp [recvGetS_SharedState, setFn]
@[simp] theorem recvGetS_SharedState_d2cChan_ne   {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : (recvGetS_SharedState s i).d2cChan j = s.d2cChan j := by simp [recvGetS_SharedState, h]
@[simp] theorem recvGetS_SharedState_c2dChan {n} (s : MState n) (i) : (recvGetS_SharedState s i).c2dChan = s.c2dChan := rfl
@[simp] theorem recvGetS_SharedState_dirSt   {n} (s : MState n) (i) : (recvGetS_SharedState s i).dirSt   = s.dirSt   := rfl
@[simp] theorem recvGetS_SharedState_shrSet_self {n} (s : MState n) (i) : (recvGetS_SharedState s i).shrSet i = true := by simp [recvGetS_SharedState, setFn]
@[simp] theorem recvGetS_SharedState_shrSet_ne   {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : (recvGetS_SharedState s i).shrSet j = s.shrSet j := by simp [recvGetS_SharedState, h]
@[simp] theorem recvGetS_SharedState_exNode  {n} (s : MState n) (i) : (recvGetS_SharedState s i).exNode  = s.exNode  := rfl
@[simp] theorem recvGetS_SharedState_curCmd  {n} (s : MState n) (i) : (recvGetS_SharedState s i).curCmd  = s.curCmd  := rfl
@[simp] theorem recvGetS_SharedState_curNode {n} (s : MState n) (i) : (recvGetS_SharedState s i).curNode = s.curNode := rfl
@[simp] theorem recvGetS_SharedState_invSet  {n} (s : MState n) (i) : (recvGetS_SharedState s i).invSet  = s.invSet  := rfl
@[simp] theorem recvGetS_SharedState_memData {n} (s : MState n) (i) : (recvGetS_SharedState s i).memData = s.memData := rfl
@[simp] theorem recvGetS_SharedState_auxData {n} (s : MState n) (i) : (recvGetS_SharedState s i).auxData = s.auxData := rfl

-- ── Frame simp-lemmas for recvGetS_ExclusiveState ─────────────────────────

@[simp] theorem recvGetS_ExclusiveState_cache   {n} (s : MState n) (i) : (recvGetS_ExclusiveState s i).cache   = s.cache   := rfl
@[simp] theorem recvGetS_ExclusiveState_reqChan_self {n} (s : MState n) (i) : (recvGetS_ExclusiveState s i).reqChan i = {} := by simp [recvGetS_ExclusiveState, setFn]
@[simp] theorem recvGetS_ExclusiveState_reqChan_ne   {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : (recvGetS_ExclusiveState s i).reqChan j = s.reqChan j := by simp [recvGetS_ExclusiveState, h]
@[simp] theorem recvGetS_ExclusiveState_d2cChan_exNode {n} (s : MState n) (i) : (recvGetS_ExclusiveState s i).d2cChan s.exNode = { cmd := .fetch, data := 0 } := by simp [recvGetS_ExclusiveState, setFn]
@[simp] theorem recvGetS_ExclusiveState_d2cChan_ne {n} (s : MState n) (i j : Fin n) (h : j ≠ s.exNode) : (recvGetS_ExclusiveState s i).d2cChan j = s.d2cChan j := by simp [recvGetS_ExclusiveState, h]
@[simp] theorem recvGetS_ExclusiveState_c2dChan {n} (s : MState n) (i) : (recvGetS_ExclusiveState s i).c2dChan = s.c2dChan := rfl
@[simp] theorem recvGetS_ExclusiveState_dirSt   {n} (s : MState n) (i) : (recvGetS_ExclusiveState s i).dirSt   = s.dirSt   := rfl
@[simp] theorem recvGetS_ExclusiveState_shrSet  {n} (s : MState n) (i) : (recvGetS_ExclusiveState s i).shrSet  = s.shrSet  := rfl
@[simp] theorem recvGetS_ExclusiveState_exNode  {n} (s : MState n) (i) : (recvGetS_ExclusiveState s i).exNode  = s.exNode  := rfl
@[simp] theorem recvGetS_ExclusiveState_curCmd  {n} (s : MState n) (i) : (recvGetS_ExclusiveState s i).curCmd  = .getS     := rfl
@[simp] theorem recvGetS_ExclusiveState_curNode {n} (s : MState n) (i) : (recvGetS_ExclusiveState s i).curNode = i         := rfl
@[simp] theorem recvGetS_ExclusiveState_invSet  {n} (s : MState n) (i) : (recvGetS_ExclusiveState s i).invSet  = s.invSet  := rfl
@[simp] theorem recvGetS_ExclusiveState_memData {n} (s : MState n) (i) : (recvGetS_ExclusiveState s i).memData = s.memData := rfl
@[simp] theorem recvGetS_ExclusiveState_auxData {n} (s : MState n) (i) : (recvGetS_ExclusiveState s i).auxData = s.auxData := rfl

-- ── Frame simp-lemmas for recvGetM_UncachedState ──────────────────────────

@[simp] theorem recvGetM_UncachedState_cache   {n} (s : MState n) (i) : (recvGetM_UncachedState s i).cache   = s.cache   := rfl
@[simp] theorem recvGetM_UncachedState_reqChan_self {n} (s : MState n) (i) : (recvGetM_UncachedState s i).reqChan i = {} := by simp [recvGetM_UncachedState, setFn]
@[simp] theorem recvGetM_UncachedState_reqChan_ne   {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : (recvGetM_UncachedState s i).reqChan j = s.reqChan j := by simp [recvGetM_UncachedState, h]
@[simp] theorem recvGetM_UncachedState_d2cChan_self {n} (s : MState n) (i) : (recvGetM_UncachedState s i).d2cChan i = { cmd := .gntE, data := s.memData } := by simp [recvGetM_UncachedState, setFn]
@[simp] theorem recvGetM_UncachedState_d2cChan_ne   {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : (recvGetM_UncachedState s i).d2cChan j = s.d2cChan j := by simp [recvGetM_UncachedState, h]
@[simp] theorem recvGetM_UncachedState_c2dChan {n} (s : MState n) (i) : (recvGetM_UncachedState s i).c2dChan = s.c2dChan := rfl
@[simp] theorem recvGetM_UncachedState_dirSt   {n} (s : MState n) (i) : (recvGetM_UncachedState s i).dirSt   = .Exclusive := rfl
@[simp] theorem recvGetM_UncachedState_shrSet  {n} (s : MState n) (i) : (recvGetM_UncachedState s i).shrSet  = s.shrSet   := rfl
@[simp] theorem recvGetM_UncachedState_exNode  {n} (s : MState n) (i) : (recvGetM_UncachedState s i).exNode  = i          := rfl
@[simp] theorem recvGetM_UncachedState_curCmd  {n} (s : MState n) (i) : (recvGetM_UncachedState s i).curCmd  = s.curCmd   := rfl
@[simp] theorem recvGetM_UncachedState_curNode {n} (s : MState n) (i) : (recvGetM_UncachedState s i).curNode = s.curNode  := rfl
@[simp] theorem recvGetM_UncachedState_invSet  {n} (s : MState n) (i) : (recvGetM_UncachedState s i).invSet  = s.invSet   := rfl
@[simp] theorem recvGetM_UncachedState_memData {n} (s : MState n) (i) : (recvGetM_UncachedState s i).memData = s.memData  := rfl
@[simp] theorem recvGetM_UncachedState_auxData {n} (s : MState n) (i) : (recvGetM_UncachedState s i).auxData = s.memData  := rfl

-- ── Frame simp-lemmas for recvGetM_SharedState ────────────────────────────

@[simp] theorem recvGetM_SharedState_cache   {n} (s : MState n) (i) : (recvGetM_SharedState s i).cache   = s.cache   := rfl
@[simp] theorem recvGetM_SharedState_reqChan_self {n} (s : MState n) (i) : (recvGetM_SharedState s i).reqChan i = {} := by simp [recvGetM_SharedState, setFn]
@[simp] theorem recvGetM_SharedState_reqChan_ne   {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : (recvGetM_SharedState s i).reqChan j = s.reqChan j := by simp [recvGetM_SharedState, h]
@[simp] theorem recvGetM_SharedState_d2cChan {n} (s : MState n) (i) : (recvGetM_SharedState s i).d2cChan = s.d2cChan := rfl
@[simp] theorem recvGetM_SharedState_c2dChan {n} (s : MState n) (i) : (recvGetM_SharedState s i).c2dChan = s.c2dChan := rfl
@[simp] theorem recvGetM_SharedState_dirSt   {n} (s : MState n) (i) : (recvGetM_SharedState s i).dirSt   = s.dirSt   := rfl
@[simp] theorem recvGetM_SharedState_shrSet_self {n} (s : MState n) (i) : (recvGetM_SharedState s i).shrSet i = false := by simp [recvGetM_SharedState, setFn]
@[simp] theorem recvGetM_SharedState_shrSet_ne   {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : (recvGetM_SharedState s i).shrSet j = s.shrSet j := by simp [recvGetM_SharedState, h]
@[simp] theorem recvGetM_SharedState_exNode  {n} (s : MState n) (i) : (recvGetM_SharedState s i).exNode  = s.exNode  := rfl
@[simp] theorem recvGetM_SharedState_curCmd  {n} (s : MState n) (i) : (recvGetM_SharedState s i).curCmd  = .getM     := rfl
@[simp] theorem recvGetM_SharedState_curNode {n} (s : MState n) (i) : (recvGetM_SharedState s i).curNode = i         := rfl
@[simp] theorem recvGetM_SharedState_invSet_self {n} (s : MState n) (i) : (recvGetM_SharedState s i).invSet i = false := by simp [recvGetM_SharedState, setFn]
@[simp] theorem recvGetM_SharedState_invSet_ne   {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : (recvGetM_SharedState s i).invSet j = s.shrSet j := by simp [recvGetM_SharedState, h]
@[simp] theorem recvGetM_SharedState_memData {n} (s : MState n) (i) : (recvGetM_SharedState s i).memData = s.memData := rfl
@[simp] theorem recvGetM_SharedState_auxData {n} (s : MState n) (i) : (recvGetM_SharedState s i).auxData = s.auxData := rfl

-- ── Frame simp-lemmas for recvGetM_ExclusiveState ─────────────────────────

@[simp] theorem recvGetM_ExclusiveState_cache   {n} (s : MState n) (i) : (recvGetM_ExclusiveState s i).cache   = s.cache   := rfl
@[simp] theorem recvGetM_ExclusiveState_reqChan_self {n} (s : MState n) (i) : (recvGetM_ExclusiveState s i).reqChan i = {} := by simp [recvGetM_ExclusiveState, setFn]
@[simp] theorem recvGetM_ExclusiveState_reqChan_ne   {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : (recvGetM_ExclusiveState s i).reqChan j = s.reqChan j := by simp [recvGetM_ExclusiveState, h]
@[simp] theorem recvGetM_ExclusiveState_d2cChan_exNode {n} (s : MState n) (i) : (recvGetM_ExclusiveState s i).d2cChan s.exNode = { cmd := .inv, data := 0 } := by simp [recvGetM_ExclusiveState, setFn]
@[simp] theorem recvGetM_ExclusiveState_d2cChan_ne {n} (s : MState n) (i j : Fin n) (h : j ≠ s.exNode) : (recvGetM_ExclusiveState s i).d2cChan j = s.d2cChan j := by simp [recvGetM_ExclusiveState, h]
@[simp] theorem recvGetM_ExclusiveState_c2dChan {n} (s : MState n) (i) : (recvGetM_ExclusiveState s i).c2dChan = s.c2dChan := rfl
@[simp] theorem recvGetM_ExclusiveState_dirSt   {n} (s : MState n) (i) : (recvGetM_ExclusiveState s i).dirSt   = s.dirSt   := rfl
@[simp] theorem recvGetM_ExclusiveState_shrSet  {n} (s : MState n) (i) : (recvGetM_ExclusiveState s i).shrSet  = s.shrSet  := rfl
@[simp] theorem recvGetM_ExclusiveState_exNode  {n} (s : MState n) (i) : (recvGetM_ExclusiveState s i).exNode  = s.exNode  := rfl
@[simp] theorem recvGetM_ExclusiveState_curCmd  {n} (s : MState n) (i) : (recvGetM_ExclusiveState s i).curCmd  = .getM     := rfl
@[simp] theorem recvGetM_ExclusiveState_curNode {n} (s : MState n) (i) : (recvGetM_ExclusiveState s i).curNode = i         := rfl
@[simp] theorem recvGetM_ExclusiveState_invSet  {n} (s : MState n) (i) : (recvGetM_ExclusiveState s i).invSet  = s.invSet  := rfl
@[simp] theorem recvGetM_ExclusiveState_memData {n} (s : MState n) (i) : (recvGetM_ExclusiveState s i).memData = s.memData := rfl
@[simp] theorem recvGetM_ExclusiveState_auxData {n} (s : MState n) (i) : (recvGetM_ExclusiveState s i).auxData = s.auxData := rfl

-- ── Frame simp-lemmas for sendInvState ───────────────────────────────────

@[simp] theorem sendInvState_cache   {n} (s : MState n) (j) : (sendInvState s j).cache   = s.cache   := rfl
@[simp] theorem sendInvState_reqChan {n} (s : MState n) (j) : (sendInvState s j).reqChan = s.reqChan := rfl
@[simp] theorem sendInvState_d2cChan_self {n} (s : MState n) (j) : (sendInvState s j).d2cChan j = { cmd := .inv, data := 0 } := by simp [sendInvState, setFn]
@[simp] theorem sendInvState_d2cChan_ne   {n} (s : MState n) (j k : Fin n) (h : k ≠ j) : (sendInvState s j).d2cChan k = s.d2cChan k := by simp [sendInvState, h]
@[simp] theorem sendInvState_c2dChan {n} (s : MState n) (j) : (sendInvState s j).c2dChan = s.c2dChan := rfl
@[simp] theorem sendInvState_dirSt   {n} (s : MState n) (j) : (sendInvState s j).dirSt   = s.dirSt   := rfl
@[simp] theorem sendInvState_shrSet  {n} (s : MState n) (j) : (sendInvState s j).shrSet  = s.shrSet  := rfl
@[simp] theorem sendInvState_exNode  {n} (s : MState n) (j) : (sendInvState s j).exNode  = s.exNode  := rfl
@[simp] theorem sendInvState_curCmd  {n} (s : MState n) (j) : (sendInvState s j).curCmd  = s.curCmd  := rfl
@[simp] theorem sendInvState_curNode {n} (s : MState n) (j) : (sendInvState s j).curNode = s.curNode := rfl
@[simp] theorem sendInvState_invSet_self {n} (s : MState n) (j) : (sendInvState s j).invSet j = false := by simp [sendInvState, setFn]
@[simp] theorem sendInvState_invSet_ne   {n} (s : MState n) (j k : Fin n) (h : k ≠ j) : (sendInvState s j).invSet k = s.invSet k := by simp [sendInvState, h]
@[simp] theorem sendInvState_memData {n} (s : MState n) (j) : (sendInvState s j).memData = s.memData := rfl
@[simp] theorem sendInvState_auxData {n} (s : MState n) (j) : (sendInvState s j).auxData = s.auxData := rfl

-- ── Frame simp-lemmas for sendGntE_AfterSharedState ──────────────────────

@[simp] theorem sendGntE_AfterSharedState_cache   {n} (s : MState n) : (sendGntE_AfterSharedState s).cache   = s.cache   := rfl
@[simp] theorem sendGntE_AfterSharedState_reqChan {n} (s : MState n) : (sendGntE_AfterSharedState s).reqChan = s.reqChan := rfl
@[simp] theorem sendGntE_AfterSharedState_d2cChan_curNode {n} (s : MState n) : (sendGntE_AfterSharedState s).d2cChan s.curNode = { cmd := .gntE, data := s.memData } := by simp [sendGntE_AfterSharedState, setFn]
@[simp] theorem sendGntE_AfterSharedState_d2cChan_ne {n} (s : MState n) (j : Fin n) (h : j ≠ s.curNode) : (sendGntE_AfterSharedState s).d2cChan j = s.d2cChan j := by simp [sendGntE_AfterSharedState, h]
@[simp] theorem sendGntE_AfterSharedState_c2dChan {n} (s : MState n) : (sendGntE_AfterSharedState s).c2dChan = s.c2dChan := rfl
@[simp] theorem sendGntE_AfterSharedState_dirSt   {n} (s : MState n) : (sendGntE_AfterSharedState s).dirSt   = .Exclusive := rfl
@[simp] theorem sendGntE_AfterSharedState_shrSet  {n} (s : MState n) (j) : (sendGntE_AfterSharedState s).shrSet j = s.shrSet j := rfl
@[simp] theorem sendGntE_AfterSharedState_exNode  {n} (s : MState n) : (sendGntE_AfterSharedState s).exNode  = s.curNode := rfl
@[simp] theorem sendGntE_AfterSharedState_curCmd  {n} (s : MState n) : (sendGntE_AfterSharedState s).curCmd  = .empty    := rfl
@[simp] theorem sendGntE_AfterSharedState_curNode {n} (s : MState n) : (sendGntE_AfterSharedState s).curNode = s.curNode := rfl
@[simp] theorem sendGntE_AfterSharedState_invSet  {n} (s : MState n) : (sendGntE_AfterSharedState s).invSet  = s.invSet  := rfl
@[simp] theorem sendGntE_AfterSharedState_memData {n} (s : MState n) : (sendGntE_AfterSharedState s).memData = s.memData := rfl
@[simp] theorem sendGntE_AfterSharedState_auxData {n} (s : MState n) : (sendGntE_AfterSharedState s).auxData = s.memData := rfl

-- ── Frame simp-lemmas for recvGntSState ──────────────────────────────────

@[simp] theorem recvGntSState_cache_state_self {n} (s : MState n) (i) : ((recvGntSState s i).cache i).state = .S := by simp [recvGntSState]
@[simp] theorem recvGntSState_cache_data_self  {n} (s : MState n) (i) : ((recvGntSState s i).cache i).data  = (s.d2cChan i).data := by simp [recvGntSState]
@[simp] theorem recvGntSState_cache_state_ne   {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : ((recvGntSState s i).cache j).state = (s.cache j).state := by simp [recvGntSState, h]
@[simp] theorem recvGntSState_cache_data_ne    {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : ((recvGntSState s i).cache j).data  = (s.cache j).data  := by simp [recvGntSState, h]
@[simp] theorem recvGntSState_reqChan {n} (s : MState n) (i) : (recvGntSState s i).reqChan = s.reqChan := rfl
@[simp] theorem recvGntSState_d2cChan_self {n} (s : MState n) (i) : (recvGntSState s i).d2cChan i = {} := by simp [recvGntSState, setFn]
@[simp] theorem recvGntSState_d2cChan_ne   {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : (recvGntSState s i).d2cChan j = s.d2cChan j := by simp [recvGntSState, h]
@[simp] theorem recvGntSState_c2dChan {n} (s : MState n) (i) : (recvGntSState s i).c2dChan = s.c2dChan := rfl
@[simp] theorem recvGntSState_dirSt   {n} (s : MState n) (i) : (recvGntSState s i).dirSt   = s.dirSt   := rfl
@[simp] theorem recvGntSState_shrSet  {n} (s : MState n) (i) : (recvGntSState s i).shrSet  = s.shrSet  := rfl
@[simp] theorem recvGntSState_exNode  {n} (s : MState n) (i) : (recvGntSState s i).exNode  = s.exNode  := rfl
@[simp] theorem recvGntSState_curCmd  {n} (s : MState n) (i) : (recvGntSState s i).curCmd  = s.curCmd  := rfl
@[simp] theorem recvGntSState_curNode {n} (s : MState n) (i) : (recvGntSState s i).curNode = s.curNode := rfl
@[simp] theorem recvGntSState_invSet  {n} (s : MState n) (i) : (recvGntSState s i).invSet  = s.invSet  := rfl
@[simp] theorem recvGntSState_memData {n} (s : MState n) (i) : (recvGntSState s i).memData = s.memData := rfl
@[simp] theorem recvGntSState_auxData {n} (s : MState n) (i) : (recvGntSState s i).auxData = s.auxData := rfl

-- ── Frame simp-lemmas for recvGntEState ──────────────────────────────────

@[simp] theorem recvGntEState_cache_state_self {n} (s : MState n) (i) : ((recvGntEState s i).cache i).state = .M := by simp [recvGntEState]
@[simp] theorem recvGntEState_cache_data_self  {n} (s : MState n) (i) : ((recvGntEState s i).cache i).data  = (s.d2cChan i).data := by simp [recvGntEState]
@[simp] theorem recvGntEState_cache_state_ne   {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : ((recvGntEState s i).cache j).state = (s.cache j).state := by simp [recvGntEState, h]
@[simp] theorem recvGntEState_cache_data_ne    {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : ((recvGntEState s i).cache j).data  = (s.cache j).data  := by simp [recvGntEState, h]
@[simp] theorem recvGntEState_reqChan {n} (s : MState n) (i) : (recvGntEState s i).reqChan = s.reqChan := rfl
@[simp] theorem recvGntEState_d2cChan_self {n} (s : MState n) (i) : (recvGntEState s i).d2cChan i = {} := by simp [recvGntEState, setFn]
@[simp] theorem recvGntEState_d2cChan_ne   {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : (recvGntEState s i).d2cChan j = s.d2cChan j := by simp [recvGntEState, h]
@[simp] theorem recvGntEState_c2dChan {n} (s : MState n) (i) : (recvGntEState s i).c2dChan = s.c2dChan := rfl
@[simp] theorem recvGntEState_dirSt   {n} (s : MState n) (i) : (recvGntEState s i).dirSt   = s.dirSt   := rfl
@[simp] theorem recvGntEState_shrSet  {n} (s : MState n) (i) : (recvGntEState s i).shrSet  = s.shrSet  := rfl
@[simp] theorem recvGntEState_exNode  {n} (s : MState n) (i) : (recvGntEState s i).exNode  = s.exNode  := rfl
@[simp] theorem recvGntEState_curCmd  {n} (s : MState n) (i) : (recvGntEState s i).curCmd  = s.curCmd  := rfl
@[simp] theorem recvGntEState_curNode {n} (s : MState n) (i) : (recvGntEState s i).curNode = s.curNode := rfl
@[simp] theorem recvGntEState_invSet  {n} (s : MState n) (i) : (recvGntEState s i).invSet  = s.invSet  := rfl
@[simp] theorem recvGntEState_memData {n} (s : MState n) (i) : (recvGntEState s i).memData = s.memData := rfl
@[simp] theorem recvGntEState_auxData {n} (s : MState n) (i) : (recvGntEState s i).auxData = s.auxData := rfl

-- ── Frame simp-lemmas for recvInvState ───────────────────────────────────

@[simp] theorem recvInvState_cache_state_self {n} (s : MState n) (i) : ((recvInvState s i).cache i).state = .I := by simp [recvInvState]
@[simp] theorem recvInvState_cache_data_self  {n} (s : MState n) (i) : ((recvInvState s i).cache i).data  = (s.cache i).data := by simp [recvInvState]
@[simp] theorem recvInvState_cache_state_ne   {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : ((recvInvState s i).cache j).state = (s.cache j).state := by simp [recvInvState, h]
@[simp] theorem recvInvState_cache_data_ne    {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : ((recvInvState s i).cache j).data  = (s.cache j).data  := by simp [recvInvState, h]
@[simp] theorem recvInvState_reqChan {n} (s : MState n) (i) : (recvInvState s i).reqChan = s.reqChan := rfl
@[simp] theorem recvInvState_d2cChan_self {n} (s : MState n) (i) : (recvInvState s i).d2cChan i = {} := by simp [recvInvState, setFn]
@[simp] theorem recvInvState_d2cChan_ne   {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : (recvInvState s i).d2cChan j = s.d2cChan j := by simp [recvInvState, h]
@[simp] theorem recvInvState_c2dChan_self {n} (s : MState n) (i) : (recvInvState s i).c2dChan i = { cmd := .ack, data := (s.cache i).data } := by simp [recvInvState, setFn]
@[simp] theorem recvInvState_c2dChan_ne   {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : (recvInvState s i).c2dChan j = s.c2dChan j := by simp [recvInvState, h]
@[simp] theorem recvInvState_dirSt   {n} (s : MState n) (i) : (recvInvState s i).dirSt   = s.dirSt   := rfl
@[simp] theorem recvInvState_shrSet  {n} (s : MState n) (i) : (recvInvState s i).shrSet  = s.shrSet  := rfl
@[simp] theorem recvInvState_exNode  {n} (s : MState n) (i) : (recvInvState s i).exNode  = s.exNode  := rfl
@[simp] theorem recvInvState_curCmd  {n} (s : MState n) (i) : (recvInvState s i).curCmd  = s.curCmd  := rfl
@[simp] theorem recvInvState_curNode {n} (s : MState n) (i) : (recvInvState s i).curNode = s.curNode := rfl
@[simp] theorem recvInvState_invSet  {n} (s : MState n) (i) : (recvInvState s i).invSet  = s.invSet  := rfl
@[simp] theorem recvInvState_memData {n} (s : MState n) (i) : (recvInvState s i).memData = s.memData := rfl
@[simp] theorem recvInvState_auxData {n} (s : MState n) (i) : (recvInvState s i).auxData = s.auxData := rfl

-- ── Frame simp-lemmas for recvFetchState ─────────────────────────────────

@[simp] theorem recvFetchState_cache_state_self {n} (s : MState n) (i) : ((recvFetchState s i).cache i).state = .I := by simp [recvFetchState]
@[simp] theorem recvFetchState_cache_data_self  {n} (s : MState n) (i) : ((recvFetchState s i).cache i).data  = (s.cache i).data := by simp [recvFetchState]
@[simp] theorem recvFetchState_cache_state_ne   {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : ((recvFetchState s i).cache j).state = (s.cache j).state := by simp [recvFetchState, h]
@[simp] theorem recvFetchState_cache_data_ne    {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : ((recvFetchState s i).cache j).data  = (s.cache j).data  := by simp [recvFetchState, h]
@[simp] theorem recvFetchState_reqChan {n} (s : MState n) (i) : (recvFetchState s i).reqChan = s.reqChan := rfl
@[simp] theorem recvFetchState_d2cChan_self {n} (s : MState n) (i) : (recvFetchState s i).d2cChan i = {} := by simp [recvFetchState, setFn]
@[simp] theorem recvFetchState_d2cChan_ne   {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : (recvFetchState s i).d2cChan j = s.d2cChan j := by simp [recvFetchState, h]
@[simp] theorem recvFetchState_c2dChan_self {n} (s : MState n) (i) : (recvFetchState s i).c2dChan i = { cmd := .ack, data := (s.cache i).data } := by simp [recvFetchState, setFn]
@[simp] theorem recvFetchState_c2dChan_ne   {n} (s : MState n) (i j : Fin n) (h : j ≠ i) : (recvFetchState s i).c2dChan j = s.c2dChan j := by simp [recvFetchState, h]
@[simp] theorem recvFetchState_dirSt   {n} (s : MState n) (i) : (recvFetchState s i).dirSt   = s.dirSt   := rfl
@[simp] theorem recvFetchState_shrSet  {n} (s : MState n) (i) : (recvFetchState s i).shrSet  = s.shrSet  := rfl
@[simp] theorem recvFetchState_exNode  {n} (s : MState n) (i) : (recvFetchState s i).exNode  = s.exNode  := rfl
@[simp] theorem recvFetchState_curCmd  {n} (s : MState n) (i) : (recvFetchState s i).curCmd  = s.curCmd  := rfl
@[simp] theorem recvFetchState_curNode {n} (s : MState n) (i) : (recvFetchState s i).curNode = s.curNode := rfl
@[simp] theorem recvFetchState_invSet  {n} (s : MState n) (i) : (recvFetchState s i).invSet  = s.invSet  := rfl
@[simp] theorem recvFetchState_memData {n} (s : MState n) (i) : (recvFetchState s i).memData = s.memData := rfl
@[simp] theorem recvFetchState_auxData {n} (s : MState n) (i) : (recvFetchState s i).auxData = s.auxData := rfl

-- ── Frame simp-lemmas for recvAck_GetM_SharedState ───────────────────────

@[simp] theorem recvAck_GetM_SharedState_cache   {n} (s : MState n) (j) : (recvAck_GetM_SharedState s j).cache   = s.cache   := rfl
@[simp] theorem recvAck_GetM_SharedState_reqChan {n} (s : MState n) (j) : (recvAck_GetM_SharedState s j).reqChan = s.reqChan := rfl
@[simp] theorem recvAck_GetM_SharedState_d2cChan {n} (s : MState n) (j) : (recvAck_GetM_SharedState s j).d2cChan = s.d2cChan := rfl
@[simp] theorem recvAck_GetM_SharedState_c2dChan_self {n} (s : MState n) (j) : (recvAck_GetM_SharedState s j).c2dChan j = {} := by simp [recvAck_GetM_SharedState, setFn]
@[simp] theorem recvAck_GetM_SharedState_c2dChan_ne   {n} (s : MState n) (j k : Fin n) (h : k ≠ j) : (recvAck_GetM_SharedState s j).c2dChan k = s.c2dChan k := by simp [recvAck_GetM_SharedState, h]
@[simp] theorem recvAck_GetM_SharedState_dirSt   {n} (s : MState n) (j) : (recvAck_GetM_SharedState s j).dirSt   = s.dirSt   := rfl
@[simp] theorem recvAck_GetM_SharedState_shrSet_self {n} (s : MState n) (j) : (recvAck_GetM_SharedState s j).shrSet j = false := by simp [recvAck_GetM_SharedState, setFn]
@[simp] theorem recvAck_GetM_SharedState_shrSet_ne   {n} (s : MState n) (j k : Fin n) (h : k ≠ j) : (recvAck_GetM_SharedState s j).shrSet k = s.shrSet k := by simp [recvAck_GetM_SharedState, h]
@[simp] theorem recvAck_GetM_SharedState_exNode  {n} (s : MState n) (j) : (recvAck_GetM_SharedState s j).exNode  = s.exNode  := rfl
@[simp] theorem recvAck_GetM_SharedState_curCmd  {n} (s : MState n) (j) : (recvAck_GetM_SharedState s j).curCmd  = s.curCmd  := rfl
@[simp] theorem recvAck_GetM_SharedState_curNode {n} (s : MState n) (j) : (recvAck_GetM_SharedState s j).curNode = s.curNode := rfl
@[simp] theorem recvAck_GetM_SharedState_invSet  {n} (s : MState n) (j) : (recvAck_GetM_SharedState s j).invSet  = s.invSet  := rfl
@[simp] theorem recvAck_GetM_SharedState_memData {n} (s : MState n) (j) : (recvAck_GetM_SharedState s j).memData = s.memData := rfl
@[simp] theorem recvAck_GetM_SharedState_auxData {n} (s : MState n) (j) : (recvAck_GetM_SharedState s j).auxData = s.auxData := rfl

-- ── Frame simp-lemmas for recvAck_GetM_ExclusiveState ────────────────────

@[simp] theorem recvAck_GetM_ExclusiveState_cache   {n} (s : MState n) (j) : (recvAck_GetM_ExclusiveState s j).cache   = s.cache   := rfl
@[simp] theorem recvAck_GetM_ExclusiveState_reqChan {n} (s : MState n) (j) : (recvAck_GetM_ExclusiveState s j).reqChan = s.reqChan := rfl
@[simp] theorem recvAck_GetM_ExclusiveState_d2cChan {n} (s : MState n) (j) : (recvAck_GetM_ExclusiveState s j).d2cChan = s.d2cChan := rfl
@[simp] theorem recvAck_GetM_ExclusiveState_c2dChan_self {n} (s : MState n) (j) : (recvAck_GetM_ExclusiveState s j).c2dChan j = {} := by simp [recvAck_GetM_ExclusiveState, setFn]
@[simp] theorem recvAck_GetM_ExclusiveState_c2dChan_ne   {n} (s : MState n) (j k : Fin n) (h : k ≠ j) : (recvAck_GetM_ExclusiveState s j).c2dChan k = s.c2dChan k := by simp [recvAck_GetM_ExclusiveState, h]
@[simp] theorem recvAck_GetM_ExclusiveState_dirSt   {n} (s : MState n) (j) : (recvAck_GetM_ExclusiveState s j).dirSt   = .Uncached  := rfl
@[simp] theorem recvAck_GetM_ExclusiveState_shrSet  {n} (s : MState n) (j) : (recvAck_GetM_ExclusiveState s j).shrSet  = s.shrSet   := rfl
@[simp] theorem recvAck_GetM_ExclusiveState_exNode  {n} (s : MState n) (j) : (recvAck_GetM_ExclusiveState s j).exNode  = s.exNode   := rfl
@[simp] theorem recvAck_GetM_ExclusiveState_curCmd  {n} (s : MState n) (j) : (recvAck_GetM_ExclusiveState s j).curCmd  = s.curCmd   := rfl
@[simp] theorem recvAck_GetM_ExclusiveState_curNode {n} (s : MState n) (j) : (recvAck_GetM_ExclusiveState s j).curNode = s.curNode  := rfl
@[simp] theorem recvAck_GetM_ExclusiveState_invSet  {n} (s : MState n) (j) : (recvAck_GetM_ExclusiveState s j).invSet  = s.invSet   := rfl
@[simp] theorem recvAck_GetM_ExclusiveState_memData {n} (s : MState n) (j) : (recvAck_GetM_ExclusiveState s j).memData = (s.c2dChan j).data := rfl
@[simp] theorem recvAck_GetM_ExclusiveState_auxData {n} (s : MState n) (j) : (recvAck_GetM_ExclusiveState s j).auxData = (s.c2dChan j).data := rfl

-- ── Frame simp-lemmas for recvAck_GetSState ───────────────────────────────

@[simp] theorem recvAck_GetSState_cache   {n} (s : MState n) (j) : (recvAck_GetSState s j).cache   = s.cache   := rfl
@[simp] theorem recvAck_GetSState_reqChan {n} (s : MState n) (j) : (recvAck_GetSState s j).reqChan = s.reqChan := rfl
@[simp] theorem recvAck_GetSState_d2cChan  {n} (s : MState n) (j) : (recvAck_GetSState s j).d2cChan  = s.d2cChan  := rfl
@[simp] theorem recvAck_GetSState_c2dChan_self {n} (s : MState n) (j) : (recvAck_GetSState s j).c2dChan j = {} := by simp [recvAck_GetSState, setFn]
@[simp] theorem recvAck_GetSState_c2dChan_ne   {n} (s : MState n) (j k : Fin n) (h : k ≠ j) : (recvAck_GetSState s j).c2dChan k = s.c2dChan k := by simp [recvAck_GetSState, h]
@[simp] theorem recvAck_GetSState_dirSt   {n} (s : MState n) (j) : (recvAck_GetSState s j).dirSt   = .Uncached  := rfl
@[simp] theorem recvAck_GetSState_shrSet  {n} (s : MState n) (j) : (recvAck_GetSState s j).shrSet  = s.shrSet   := rfl
@[simp] theorem recvAck_GetSState_exNode  {n} (s : MState n) (j) : (recvAck_GetSState s j).exNode  = s.exNode   := rfl
@[simp] theorem recvAck_GetSState_curCmd  {n} (s : MState n) (j) : (recvAck_GetSState s j).curCmd  = s.curCmd   := rfl
@[simp] theorem recvAck_GetSState_curNode {n} (s : MState n) (j) : (recvAck_GetSState s j).curNode = s.curNode  := rfl
@[simp] theorem recvAck_GetSState_invSet  {n} (s : MState n) (j) : (recvAck_GetSState s j).invSet  = s.invSet   := rfl
@[simp] theorem recvAck_GetSState_memData {n} (s : MState n) (j) : (recvAck_GetSState s j).memData = (s.c2dChan j).data := rfl
@[simp] theorem recvAck_GetSState_auxData {n} (s : MState n) (j) : (recvAck_GetSState s j).auxData = (s.c2dChan j).data := rfl

-- ── Frame simp-lemmas for sendGntE_AfterExclusiveState ───────────────────

@[simp] theorem sendGntE_AfterExclusiveState_cache   {n} (s : MState n) : (sendGntE_AfterExclusiveState s).cache   = s.cache   := rfl
@[simp] theorem sendGntE_AfterExclusiveState_reqChan {n} (s : MState n) : (sendGntE_AfterExclusiveState s).reqChan = s.reqChan := rfl
@[simp] theorem sendGntE_AfterExclusiveState_d2cChan_curNode {n} (s : MState n) : (sendGntE_AfterExclusiveState s).d2cChan s.curNode = { cmd := .gntE, data := s.memData } := by simp [sendGntE_AfterExclusiveState, setFn]
@[simp] theorem sendGntE_AfterExclusiveState_d2cChan_ne {n} (s : MState n) (j : Fin n) (h : j ≠ s.curNode) : (sendGntE_AfterExclusiveState s).d2cChan j = s.d2cChan j := by simp [sendGntE_AfterExclusiveState, h]
@[simp] theorem sendGntE_AfterExclusiveState_c2dChan {n} (s : MState n) : (sendGntE_AfterExclusiveState s).c2dChan = s.c2dChan := rfl
@[simp] theorem sendGntE_AfterExclusiveState_dirSt   {n} (s : MState n) : (sendGntE_AfterExclusiveState s).dirSt   = .Exclusive := rfl
@[simp] theorem sendGntE_AfterExclusiveState_shrSet  {n} (s : MState n) : (sendGntE_AfterExclusiveState s).shrSet  = s.shrSet   := rfl
@[simp] theorem sendGntE_AfterExclusiveState_exNode  {n} (s : MState n) : (sendGntE_AfterExclusiveState s).exNode  = s.curNode  := rfl
@[simp] theorem sendGntE_AfterExclusiveState_curCmd  {n} (s : MState n) : (sendGntE_AfterExclusiveState s).curCmd  = .empty     := rfl
@[simp] theorem sendGntE_AfterExclusiveState_curNode {n} (s : MState n) : (sendGntE_AfterExclusiveState s).curNode = s.curNode  := rfl
@[simp] theorem sendGntE_AfterExclusiveState_invSet  {n} (s : MState n) : (sendGntE_AfterExclusiveState s).invSet  = s.invSet   := rfl
@[simp] theorem sendGntE_AfterExclusiveState_memData {n} (s : MState n) : (sendGntE_AfterExclusiveState s).memData = s.memData  := rfl
@[simp] theorem sendGntE_AfterExclusiveState_auxData {n} (s : MState n) : (sendGntE_AfterExclusiveState s).auxData = s.auxData  := rfl

-- ── Frame simp-lemmas for sendGntS_AfterFetchState ───────────────────────

@[simp] theorem sendGntS_AfterFetchState_cache   {n} (s : MState n) : (sendGntS_AfterFetchState s).cache   = s.cache   := rfl
@[simp] theorem sendGntS_AfterFetchState_reqChan {n} (s : MState n) : (sendGntS_AfterFetchState s).reqChan = s.reqChan := rfl
@[simp] theorem sendGntS_AfterFetchState_d2cChan_curNode {n} (s : MState n) : (sendGntS_AfterFetchState s).d2cChan s.curNode = { cmd := .gntS, data := s.memData } := by simp [sendGntS_AfterFetchState, setFn]
@[simp] theorem sendGntS_AfterFetchState_d2cChan_ne {n} (s : MState n) (j : Fin n) (h : j ≠ s.curNode) : (sendGntS_AfterFetchState s).d2cChan j = s.d2cChan j := by simp [sendGntS_AfterFetchState, h]
@[simp] theorem sendGntS_AfterFetchState_c2dChan {n} (s : MState n) : (sendGntS_AfterFetchState s).c2dChan = s.c2dChan := rfl
@[simp] theorem sendGntS_AfterFetchState_dirSt   {n} (s : MState n) : (sendGntS_AfterFetchState s).dirSt   = .Shared   := rfl
@[simp] theorem sendGntS_AfterFetchState_shrSet_curNode {n} (s : MState n) : (sendGntS_AfterFetchState s).shrSet s.curNode = true := by simp [sendGntS_AfterFetchState, setFn]
@[simp] theorem sendGntS_AfterFetchState_shrSet_ne {n} (s : MState n) (j : Fin n) (h : j ≠ s.curNode) : (sendGntS_AfterFetchState s).shrSet j = s.shrSet j := by simp [sendGntS_AfterFetchState, h]
@[simp] theorem sendGntS_AfterFetchState_exNode  {n} (s : MState n) : (sendGntS_AfterFetchState s).exNode  = s.exNode  := rfl
@[simp] theorem sendGntS_AfterFetchState_curCmd  {n} (s : MState n) : (sendGntS_AfterFetchState s).curCmd  = .empty    := rfl
@[simp] theorem sendGntS_AfterFetchState_curNode {n} (s : MState n) : (sendGntS_AfterFetchState s).curNode = s.curNode := rfl
@[simp] theorem sendGntS_AfterFetchState_invSet  {n} (s : MState n) : (sendGntS_AfterFetchState s).invSet  = s.invSet  := rfl
@[simp] theorem sendGntS_AfterFetchState_memData {n} (s : MState n) : (sendGntS_AfterFetchState s).memData = s.memData := rfl
@[simp] theorem sendGntS_AfterFetchState_auxData {n} (s : MState n) : (sendGntS_AfterFetchState s).auxData = s.auxData := rfl

-- ── Actions ───────────────────────────────────────────────────────────────

-- 1. Processor sends GetS (cache is in I, reqChan is empty)
def SendGetS (s s' : MState n) (i : Fin n) : Prop :=
  (s.reqChan i).cmd = .empty ∧
  (s.cache i).state = .I ∧
  s' = { s with reqChan := setFn s.reqChan i { cmd := .getS } }

-- 2. Processor sends GetM (cache is not in M, reqChan is empty)
def SendGetM (s s' : MState n) (i : Fin n) : Prop :=
  (s.reqChan i).cmd = .empty ∧
  (s.cache i).state ≠ .M ∧
  s' = { s with reqChan := setFn s.reqChan i { cmd := .getM } }

-- 3. Directory processes GetS when Uncached — immediately grants S
def RecvGetS_Uncached (s s' : MState n) (i : Fin n) : Prop :=
  (s.reqChan i).cmd = .getS ∧
  s.curCmd = .empty ∧
  s.dirSt = .Uncached ∧
  (s.d2cChan i).cmd = .empty ∧
  s' = recvGetS_UncachedState s i

-- 4. Directory processes GetS when Shared — grants another S
def RecvGetS_Shared (s s' : MState n) (i : Fin n) : Prop :=
  (s.reqChan i).cmd = .getS ∧
  s.curCmd = .empty ∧
  s.dirSt = .Shared ∧
  (s.d2cChan i).cmd = .empty ∧
  s' = recvGetS_SharedState s i

-- 5. Directory processes GetS when Exclusive — fetches data from exclusive holder
def RecvGetS_Exclusive (s s' : MState n) (i : Fin n) : Prop :=
  (s.reqChan i).cmd = .getS ∧
  s.curCmd = .empty ∧
  s.dirSt = .Exclusive ∧
  (s.d2cChan s.exNode).cmd = .empty ∧
  s' = recvGetS_ExclusiveState s i

-- 6. Directory processes GetM when Uncached — immediately grants E
def RecvGetM_Uncached (s s' : MState n) (i : Fin n) : Prop :=
  (s.reqChan i).cmd = .getM ∧
  s.curCmd = .empty ∧
  s.dirSt = .Uncached ∧
  (s.d2cChan i).cmd = .empty ∧
  s' = recvGetM_UncachedState s i

-- 7. Directory processes GetM when Shared — start sending invalidations
def RecvGetM_Shared (s s' : MState n) (i : Fin n) : Prop :=
  (s.reqChan i).cmd = .getM ∧
  s.curCmd = .empty ∧
  s.dirSt = .Shared ∧
  s' = recvGetM_SharedState s i

-- 8. Directory processes GetM when Exclusive — invalidate current exclusive holder
def RecvGetM_Exclusive (s s' : MState n) (i : Fin n) : Prop :=
  (s.reqChan i).cmd = .getM ∧
  s.curCmd = .empty ∧
  s.dirSt = .Exclusive ∧
  s.exNode ≠ i ∧
  (s.d2cChan s.exNode).cmd = .empty ∧
  s' = recvGetM_ExclusiveState s i

-- 9. Directory sends a pending invalidation
def SendInv (s s' : MState n) (j : Fin n) : Prop :=
  s.invSet j = true ∧
  (s.d2cChan j).cmd = .empty ∧
  s' = sendInvState s j

-- 10. After all sharer acks received (shrSet fully cleared), grant E to curNode
def SendGntE_AfterShared (s s' : MState n) : Prop :=
  s.curCmd = .getM ∧
  s.dirSt = .Shared ∧
  (∀ j : Fin n, s.shrSet j = false) ∧
  (∀ j : Fin n, s.invSet j = false) ∧
  (s.d2cChan s.curNode).cmd = .empty ∧
  s' = sendGntE_AfterSharedState s

-- 11. Cache receives gntS
def RecvGntS (s s' : MState n) (i : Fin n) : Prop :=
  (s.d2cChan i).cmd = .gntS ∧
  s' = recvGntSState s i

-- 12. Cache receives gntE
def RecvGntE (s s' : MState n) (i : Fin n) : Prop :=
  (s.d2cChan i).cmd = .gntE ∧
  s' = recvGntEState s i

-- 13. Cache receives inv, sends ack carrying data
def RecvInv (s s' : MState n) (i : Fin n) : Prop :=
  (s.d2cChan i).cmd = .inv ∧
  (s.c2dChan i).cmd = .empty ∧
  s' = recvInvState s i

-- 14. Cache receives fetch (exclusive → I, send ack with data)
def RecvFetch (s s' : MState n) (i : Fin n) : Prop :=
  (s.d2cChan i).cmd = .fetch ∧
  (s.c2dChan i).cmd = .empty ∧
  s' = recvFetchState s i

-- 15. Directory receives ack in GetM/Shared context
def RecvAck_GetM_Shared (s s' : MState n) (j : Fin n) : Prop :=
  (s.c2dChan j).cmd = .ack ∧
  s.curCmd = .getM ∧
  s.dirSt = .Shared ∧
  s' = recvAck_GetM_SharedState s j

-- 16a. Directory receives writeback ack from old M-holder (GetM/Exclusive case)
def RecvAck_GetM_Exclusive (s s' : MState n) (j : Fin n) : Prop :=
  (s.c2dChan j).cmd = .ack ∧
  s.curCmd = .getM ∧
  s.dirSt = .Exclusive ∧
  s' = recvAck_GetM_ExclusiveState s j

-- 16b. Directory sends gntE to new requester after exclusive writeback received
def SendGntE_AfterExclusive (s s' : MState n) : Prop :=
  s.curCmd = .getM ∧
  s.dirSt = .Uncached ∧
  (s.d2cChan s.curNode).cmd = .empty ∧
  s' = sendGntE_AfterExclusiveState s

-- 17a. Directory receives fetch ack from old M-holder (GetS/Exclusive case)
def RecvAck_GetS (s s' : MState n) (j : Fin n) : Prop :=
  (s.c2dChan j).cmd = .ack ∧
  s.curCmd = .getS ∧
  s' = recvAck_GetSState s j

-- 17b. Directory sends gntS to pending requester after fetch writeback received
def SendGntS_AfterFetch (s s' : MState n) : Prop :=
  s.curCmd = .getS ∧
  s.dirSt = .Uncached ∧
  (s.d2cChan s.curNode).cmd = .empty ∧
  s' = sendGntS_AfterFetchState s

-- ── Initial state ─────────────────────────────────────────────────────────

def init (n : Nat) (s : MState n) : Prop :=
  (∀ i, s.cache   i = {}) ∧
  (∀ i, s.reqChan i = {}) ∧
  (∀ i, s.d2cChan i = {}) ∧
  (∀ i, s.c2dChan i = {}) ∧
  s.dirSt  = .Uncached ∧
  (∀ i, s.shrSet i = false) ∧
  (∀ i, s.invSet i = false) ∧
  s.curCmd  = .empty ∧
  s.memData = s.auxData

-- ── Transition relation ───────────────────────────────────────────────────

def next (n : Nat) (s s' : MState n) : Prop :=
  (∃ i, SendGetS s s' i) ∨
  (∃ i, SendGetM s s' i) ∨
  (∃ i, RecvGetS_Uncached s s' i) ∨
  (∃ i, RecvGetS_Shared s s' i) ∨
  (∃ i, RecvGetS_Exclusive s s' i) ∨
  (∃ i, RecvGetM_Uncached s s' i) ∨
  (∃ i, RecvGetM_Shared s s' i) ∨
  (∃ i, RecvGetM_Exclusive s s' i) ∨
  (∃ j, SendInv s s' j) ∨
  SendGntE_AfterShared s s' ∨
  (∃ i, RecvGntS s s' i) ∨
  (∃ i, RecvGntE s s' i) ∨
  (∃ i, RecvInv s s' i) ∨
  (∃ i, RecvFetch s s' i) ∨
  (∃ j, RecvAck_GetM_Shared s s' j) ∨
  (∃ j, RecvAck_GetM_Exclusive s s' j) ∨
  SendGntE_AfterExclusive s s' ∨
  (∃ j, RecvAck_GetS s s' j) ∨
  SendGntS_AfterFetch s s'

def directoryMSISpec (n : Nat) : Spec (MState n) where
  init := init n
  next := next n
  fair := []

end DirectoryMSI
