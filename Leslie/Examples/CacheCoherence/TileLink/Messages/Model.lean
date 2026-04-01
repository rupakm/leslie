import Leslie.SymShared
import Leslie.Examples.CacheCoherence.TileLink.Common

open TLA SymShared Classical

/-! ## TileLink TL-C Message-Level Model

    This file starts Stage 2 of the TileLink plan: an explicit single-line
    message model with per-channel endpoint state.

    The current checkpoint is intentionally narrow:

    - explicit A/B/C/D/E endpoint slots are present in the local state
    - shared state tracks manager memory, directory metadata, and the current
      serialized transaction
    - the current action slice covers acquire send/receive, explicit probe
      receive and probe-ack handling, explicit D/E grant completion, and
      explicit C/D release completion:
      `sendAcquireBlock`, `sendAcquirePerm`, `recvAcquireAtManager`,
      `recvProbeAtMaster`, `recvProbeAckAtManager`, `sendGrantToRequester`,
      `recvGrantAtMaster`, `recvGrantAckAtManager`, `sendRelease`,
      `sendReleaseData`, `recvReleaseAtManager`, and `recvReleaseAckAtMaster`
    - `recvAcquireAtManager` enqueues the required B-channel probes,
      `recvProbeAtMaster` turns a B probe into a C probe acknowledgment, and
      `recvProbeAckAtManager` clears one outstanding probe and can move the
      manager transaction to `grantReady`
    - `sendGrantToRequester` emits the D-channel grant, `recvGrantAtMaster`
      consumes that grant and emits an E-channel acknowledgment, and
      `recvGrantAckAtManager` retires the serialized transaction

    No proofs live here. This module is only the concrete state and transition
    vocabulary that later invariant and step-proof files will build on.
-/

namespace TileLink.Messages

open TileLink

def lineAddr : Addr := 0

inductive ReqKind where
  | acquireBlock
  | acquirePerm
  deriving DecidableEq, Repr

inductive TxnPhase where
  | probing
  | grantReady
  | grantPendingAck
  deriving DecidableEq, Repr

structure AMsg where
  opcode : AOpcode
  param : GrowParam
  source : SourceId
  address : Addr := lineAddr
  deriving DecidableEq, Repr

structure BMsg where
  opcode : BOpcode
  param : CapParam
  source : SourceId
  address : Addr := lineAddr
  deriving DecidableEq, Repr

structure CMsg where
  opcode : COpcode
  param : Option PruneReportParam := none
  source : SourceId := 0
  sink : Option SinkId := none
  address : Addr := lineAddr
  data : Option Val := none
  deriving DecidableEq, Repr

structure DMsg where
  opcode : DOpcode
  sink : SinkId
  source : SourceId
  param : Option CapParam := none
  address : Addr := lineAddr
  data : Option Val := none
  deriving DecidableEq, Repr

structure EMsg where
  opcode : EOpcode := .grantAck
  sink : SinkId
  deriving DecidableEq, Repr

structure ManagerTxn where
  requester : Nat
  source : SourceId
  sink : SinkId
  kind : ReqKind
  grow : GrowParam
  phase : TxnPhase
  grantHasData : Bool
  resultPerm : TLPerm
  transferVal : Val
  usedDirtySource : Bool
  probesNeeded : Nat → Bool
  probesRemaining : Nat → Bool
  preLines : Nat → CacheLine

structure HomeState where
  mem : Val
  dir : Nat → TLPerm
  currentTxn : Option ManagerTxn
  pendingGrantAck : Option Nat
  pendingReleaseAck : Option Nat
  nextSink : SinkId

structure NodeState where
  line : CacheLine
  chanA : Option AMsg := none
  chanB : Option BMsg := none
  chanC : Option CMsg := none
  chanD : Option DMsg := none
  chanE : Option EMsg := none
  pendingSource : Option SourceId := none
  pendingSink : Option SinkId := none
  releaseInFlight : Bool := false
  deriving DecidableEq, Repr

inductive Act where
  | sendAcquireBlock (grow : GrowParam) (source : SourceId)
  | sendAcquirePerm (grow : GrowParam) (source : SourceId)
  | recvAcquireAtManager
  | recvProbeAtMaster
  | recvProbeAckAtManager
  | sendGrantToRequester
  | recvGrantAtMaster
  | recvGrantAckAtManager
  | sendRelease (param : PruneReportParam)
  | sendReleaseData (param : PruneReportParam)
  | recvReleaseAtManager
  | recvReleaseAckAtMaster
  deriving DecidableEq

def mkAcquireBlockMsg (grow : GrowParam) (source : SourceId) : AMsg :=
  { opcode := .acquireBlock, param := grow, source := source }

def mkAcquirePermMsg (grow : GrowParam) (source : SourceId) : AMsg :=
  { opcode := .acquirePerm, param := grow, source := source }

def probeOpcodeOfKind : ReqKind → BOpcode
  | .acquireBlock => .probeBlock
  | .acquirePerm => .probePerm

def probeCapOfResult : TLPerm → CapParam
  | .N => .toN
  | .B => .toB
  | .T => .toN

def probeAckOpcodeOfLine (line : CacheLine) : COpcode :=
  if line.dirty then .probeAckData else .probeAck

def probeAckDataOfLine (line : CacheLine) : Option Val :=
  if line.dirty then some line.data else none

def invalidatedLine (line : CacheLine) : CacheLine :=
  { line with perm := .N, valid := false, dirty := false }

def branchAfterProbe (line : CacheLine) : CacheLine :=
  { perm := .B, valid := true, dirty := false, data := line.data }

def tipAfterProbe (line : CacheLine) : CacheLine :=
  { perm := .T, valid := true, dirty := false, data := line.data }

@[simp] theorem invalidatedLine_perm (line : CacheLine) :
    (invalidatedLine line).perm = .N := rfl

@[simp] theorem invalidatedLine_wf (line : CacheLine) :
    (invalidatedLine line).WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · intro hdirty
    simp [invalidatedLine] at hdirty
  · intro hperm
    simp [invalidatedLine] at hperm
  · intro hperm
    simp [invalidatedLine] at hperm ⊢

@[simp] theorem branchAfterProbe_wf (line : CacheLine) :
    (branchAfterProbe line).WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · intro hdirty
    simp [branchAfterProbe] at hdirty
  · intro hperm
    simp [branchAfterProbe] at hperm ⊢
  · intro hperm
    simp [branchAfterProbe] at hperm

@[simp] theorem tipAfterProbe_wf (line : CacheLine) :
    (tipAfterProbe line).WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · intro hdirty
    simp [tipAfterProbe] at hdirty
  · intro hperm
    simp [tipAfterProbe] at hperm
  · intro hperm
    simp [tipAfterProbe] at hperm

def probedLine (line : CacheLine) (cap : CapParam) : CacheLine :=
  match cap with
  | .toN => invalidatedLine line
  | .toB => branchAfterProbe line
  | .toT => tipAfterProbe line

@[simp] theorem probedLine_wf (line : CacheLine) (cap : CapParam) :
    (probedLine line cap).WellFormed := by
  cases cap <;> simp [probedLine]

def clearProbeIdx (probeMask : Nat → Bool) (idx : Nat) : Nat → Bool :=
  fun k => if k = idx then false else probeMask k

def updateDirAt {n : Nat} (dir : Nat → TLPerm) (i : Fin n) (perm : TLPerm) : Nat → TLPerm :=
  fun k => if k = i.1 then perm else dir k

@[simp] theorem updateDirAt_self {n : Nat} (dir : Nat → TLPerm) (i : Fin n) (perm : TLPerm) :
    updateDirAt dir i perm i.1 = perm := by
  simp [updateDirAt]

@[simp] theorem updateDirAt_ne {n : Nat} (dir : Nat → TLPerm) (i : Fin n) (perm : TLPerm)
    {k : Nat} (h : k ≠ i.1) :
    updateDirAt dir i perm k = dir k := by
  simp [updateDirAt, h]

def probeAckPhase {n : Nat} (probeMask : Nat → Bool) : TxnPhase :=
  if _ : ∀ j : Fin n, probeMask j.1 = false then .grantReady else .probing

def probeAckMsg (i : Fin n) (line : CacheLine) : CMsg :=
  { opcode := probeAckOpcodeOfLine line
  , source := i.1
  , data := probeAckDataOfLine line }

def grantOpcodeOfTxn (tx : ManagerTxn) : DOpcode :=
  if tx.grantHasData then .grantData else .grant

def grantDataOfTxn (tx : ManagerTxn) : Option Val :=
  if tx.grantHasData then some tx.transferVal else none

def grantMsgOfTxn (tx : ManagerTxn) : DMsg :=
  { opcode := grantOpcodeOfTxn tx
  , sink := tx.sink
  , source := tx.source
  , param := some (probeCapOfResult tx.resultPerm)
  , data := grantDataOfTxn tx }

def grantLine (line : CacheLine) (tx : ManagerTxn) : CacheLine :=
  if tx.grantHasData then
    match tx.resultPerm with
    | .N => invalidatedLine line
    | .B => { perm := .B, valid := true, dirty := false, data := tx.transferVal }
    | .T => { perm := .T, valid := true, dirty := false, data := tx.transferVal }
  else
    { line with perm := .T, valid := false, dirty := false }

def releasedLine (line : CacheLine) (perm : TLPerm) : CacheLine :=
  match perm with
  | .N => invalidatedLine line
  | .B => branchAfterProbe line
  | .T => tipAfterProbe line

def releaseOpcode (withData : Bool) : COpcode :=
  if withData then .releaseData else .release

def releaseDataPayload (withData : Bool) (line : CacheLine) : Option Val :=
  if withData then some line.data else none

def releaseMsg (source : SourceId) (param : PruneReportParam)
    (withData : Bool) (line : CacheLine) : CMsg :=
  { opcode := releaseOpcode withData
  , param := some param
  , source := source
  , data := releaseDataPayload withData line }

def releaseAckMsg (source : SourceId) : DMsg :=
  { opcode := .releaseAck, sink := 0, source := source }

def releaseMsgWellFormed (msg : CMsg) : Prop :=
  (msg.opcode = .release ∧ ∃ param : PruneReportParam, msg.param = some param ∧ msg.data = none) ∨
  (msg.opcode = .releaseData ∧ ∃ param : PruneReportParam, ∃ v : Val,
    msg.param = some param ∧ msg.data = some v)

def probeAckMsgWellFormed (msg : CMsg) : Prop :=
  (msg.opcode = .probeAck ∧ msg.data = none) ∨
  (msg.opcode = .probeAckData ∧ ∃ v : Val, msg.data = some v)

theorem probeAckMsg_wf {n : Nat} (i : Fin n) (line : CacheLine) :
    probeAckMsgWellFormed (probeAckMsg i line) := by
  by_cases hdirty : line.dirty = true
  · right
    refine ⟨?_, ?_⟩
    · simp [probeAckMsg, probeAckOpcodeOfLine, hdirty]
    · exact ⟨line.data, by simp [probeAckMsg, probeAckDataOfLine, hdirty]⟩
  · left
    refine ⟨?_, ?_⟩
    · simp [probeAckMsg, probeAckOpcodeOfLine, hdirty]
    · simp [probeAckMsg, probeAckDataOfLine, hdirty]

@[simp] theorem grantLine_wf (line : CacheLine) (tx : ManagerTxn) :
    (grantLine line tx).WellFormed := by
  by_cases hdata : tx.grantHasData
  · cases hperm : tx.resultPerm
    · simp [grantLine, hdata, hperm, invalidatedLine_wf]
    · refine ⟨?_, ?_, ?_⟩ <;> simp [grantLine, hdata, hperm]
    · refine ⟨?_, ?_, ?_⟩ <;> simp [grantLine, hdata, hperm]
  · refine ⟨?_, ?_, ?_⟩ <;> simp [grantLine, hdata]

theorem grantLine_perm_eq_result (line : CacheLine) (tx : ManagerTxn)
    (hnoData : tx.grantHasData = false → tx.resultPerm = .T) :
    (grantLine line tx).perm = tx.resultPerm := by
  cases hdata : tx.grantHasData
  · simp [grantLine, hdata, hnoData hdata]
  · cases hperm : tx.resultPerm <;> simp [grantLine, hdata, hperm, invalidatedLine_perm]

@[simp] theorem releasedLine_perm (line : CacheLine) (perm : TLPerm) :
    (releasedLine line perm).perm = perm := by
  cases perm <;> rfl

@[simp] theorem releasedLine_wf (line : CacheLine) (perm : TLPerm) :
    (releasedLine line perm).WellFormed := by
  cases perm <;> simp [releasedLine]

theorem releaseMsg_of_clean (source : SourceId) (param : PruneReportParam) (line : CacheLine) :
    releaseMsgWellFormed (releaseMsg source param false line) := by
  left
  refine ⟨by simp [releaseMsg, releaseOpcode], ?_⟩
  exact ⟨param, by simp [releaseMsg, releaseDataPayload]⟩

theorem releaseMsg_of_dirty (source : SourceId) (param : PruneReportParam) (line : CacheLine) :
    releaseMsgWellFormed (releaseMsg source param true line) := by
  right
  refine ⟨by simp [releaseMsg, releaseOpcode], ?_⟩
  exact ⟨param, line.data, by simp [releaseMsg, releaseDataPayload]⟩

def hasDirtyOther {n : Nat} (s : SymState HomeState NodeState n) (i : Fin n) : Prop :=
  ∃ j : Fin n, j ≠ i ∧ (s.locals j).line.dirty = true

def hasCachedOther {n : Nat} (s : SymState HomeState NodeState n) (i : Fin n) : Prop :=
  ∃ j : Fin n, j ≠ i ∧ (s.locals j).line.perm ≠ .N

def allOthersInvalid {n : Nat} (s : SymState HomeState NodeState n) (i : Fin n) : Prop :=
  ∀ j : Fin n, j ≠ i → (s.locals j).line.perm = .N

noncomputable def dirtyOwnerOpt {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n) : Option (Fin n) :=
  if h : ∃ j : Fin n, j ≠ i ∧ (s.locals j).line.dirty = true then
    some (Classical.choose h)
  else
    none

def noProbeMask : Nat → Bool :=
  fun _ => false

def writableProbeMask {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n) : Nat → Bool :=
  fun k =>
    if hk : k < n then
      let p : Fin n := ⟨k, hk⟩
      if p = i then false else decide ((s.locals p).line.perm = .T)
    else
      false

def cachedProbeMask {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n) : Nat → Bool :=
  fun k =>
    if hk : k < n then
      let p : Fin n := ⟨k, hk⟩
      if p = i then false else decide ((s.locals p).line.perm ≠ .N)
    else
      false

def probeMaskForResult {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n) (perm : TLPerm) : Nat → Bool :=
  match perm with
  | .N => noProbeMask
  | .B => writableProbeMask s i
  | .T => cachedProbeMask s i

def allTargetBsEmpty {n : Nat}
    (s : SymState HomeState NodeState n) (probeMask : Nat → Bool) : Prop :=
  ∀ j : Fin n, probeMask j.1 = true → (s.locals j).chanB = none

noncomputable def plannedTransferVal {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n) : Val :=
  match dirtyOwnerOpt s i with
  | some j => (s.locals j).line.data
  | none => s.shared.mem

noncomputable def plannedUsedDirtySource {n : Nat}
    (s : SymState HomeState NodeState n) (i : Fin n) : Bool :=
  match dirtyOwnerOpt s i with
  | some _ => true
  | none => false

noncomputable def plannedTxn {n : Nat}
    (s : SymState HomeState NodeState n)
    (requester : Fin n)
    (kind : ReqKind)
    (grow : GrowParam)
    (source : SourceId) : ManagerTxn :=
  let resultPerm := grow.result
  let probeMask := probeMaskForResult s requester resultPerm
  let preLines : Nat → CacheLine :=
    fun k =>
      if hk : k < n then
        (s.locals ⟨k, hk⟩).line
      else
        ({ perm := .N, valid := false, dirty := false, data := 0 } : CacheLine)
  { requester := requester.1
  , source := source
  , sink := s.shared.nextSink
  , kind := kind
  , grow := grow
  , phase := .probing
  , grantHasData := decide (kind = .acquireBlock)
  , resultPerm := resultPerm
  , transferVal := plannedTransferVal s requester
  , usedDirtySource := plannedUsedDirtySource s requester
  , probesNeeded := probeMask
  , probesRemaining := probeMask
  , preLines := preLines }

def recvProbeLocal {n : Nat} (node : NodeState) (i : Fin n) (msg : BMsg) : NodeState :=
  { node with
      line := probedLine node.line msg.param
      chanB := none
      chanC := some (probeAckMsg i node.line) }

def recvProbeLocals {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n)
    (msg : BMsg) : Fin n → NodeState :=
  setFn s.locals i (recvProbeLocal (s.locals i) i msg)

def recvProbeState {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n)
    (msg : BMsg) : SymState HomeState NodeState n :=
  { shared := s.shared
  , locals := recvProbeLocals s i msg }

noncomputable def recvProbeAckShared {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n)
    (tx : ManagerTxn) : HomeState :=
  let remaining := clearProbeIdx tx.probesRemaining i.1
  let phase := probeAckPhase (n := n) remaining
  { s.shared with
      dir := updateDirAt s.shared.dir i (s.locals i).line.perm
      currentTxn := some { tx with probesRemaining := remaining, phase := phase } }

def recvProbeAckLocals {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) : Fin n → NodeState :=
  setFn s.locals i { (s.locals i) with chanC := none }

noncomputable def recvProbeAckState {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n)
    (tx : ManagerTxn) : SymState HomeState NodeState n :=
  { shared := recvProbeAckShared s i tx
  , locals := recvProbeAckLocals s i }

noncomputable def sendGrantShared {n : Nat}
    (s : SymState HomeState NodeState n)
    (tx : ManagerTxn) : HomeState :=
  { s.shared with
      currentTxn := some { tx with phase := .grantPendingAck }
      pendingGrantAck := some tx.requester }

def sendGrantLocals {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n)
    (tx : ManagerTxn) : Fin n → NodeState :=
  setFn s.locals i
    { (s.locals i) with
        chanD := some (grantMsgOfTxn tx)
        pendingSink := some tx.sink }

noncomputable def sendGrantState {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n)
    (tx : ManagerTxn) : SymState HomeState NodeState n :=
  { shared := sendGrantShared s tx
  , locals := sendGrantLocals s i tx }

noncomputable def recvGrantShared {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n)
    (tx : ManagerTxn) : HomeState :=
  { s.shared with dir := updateDirAt s.shared.dir i tx.resultPerm }

def recvGrantLocal
    (node : NodeState)
    (tx : ManagerTxn) : NodeState :=
  { node with
      line := grantLine node.line tx
      chanD := none
      chanE := some { sink := tx.sink }
      pendingSource := none }

def recvGrantLocals {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n)
    (tx : ManagerTxn) : Fin n → NodeState :=
  setFn s.locals i (recvGrantLocal (s.locals i) tx)

noncomputable def recvGrantState {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n)
    (tx : ManagerTxn) : SymState HomeState NodeState n :=
  { shared := recvGrantShared s i tx
  , locals := recvGrantLocals s i tx }

noncomputable def recvGrantAckShared
    (s : SymState HomeState NodeState n) : HomeState :=
  { s.shared with currentTxn := none, pendingGrantAck := none }

def recvGrantAckLocals {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) : Fin n → NodeState :=
  setFn s.locals i
    { (s.locals i) with
        chanE := none
        pendingSink := none }

noncomputable def recvGrantAckState {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) : SymState HomeState NodeState n :=
  { shared := recvGrantAckShared s
  , locals := recvGrantAckLocals s i }

def sendReleaseLocal (node : NodeState) (source : SourceId)
    (param : PruneReportParam) (withData : Bool) : NodeState :=
  { node with
      line := releasedLine node.line param.result
      chanC := some (releaseMsg source param withData node.line)
      releaseInFlight := true }

def sendReleaseLocals {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n)
    (param : PruneReportParam)
    (withData : Bool) : Fin n → NodeState :=
  setFn s.locals i (sendReleaseLocal (s.locals i) i.1 param withData)

noncomputable def sendReleaseState {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n)
    (param : PruneReportParam)
    (withData : Bool) : SymState HomeState NodeState n :=
  { shared := s.shared
  , locals := sendReleaseLocals s i param withData }

def releaseWriteback (mem : Val) (msg : CMsg) : Val :=
  match msg.data with
  | some v => v
  | none => mem

noncomputable def recvReleaseShared {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n)
    (msg : CMsg)
    (param : PruneReportParam) : HomeState :=
  { s.shared with
      mem := releaseWriteback s.shared.mem msg
      dir := updateDirAt s.shared.dir i param.result
      pendingReleaseAck := some i.1 }

def recvReleaseLocal (node : NodeState) (source : SourceId) : NodeState :=
  { node with
      chanC := none
      chanD := some (releaseAckMsg source) }

def recvReleaseLocals {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) : Fin n → NodeState :=
  setFn s.locals i (recvReleaseLocal (s.locals i) i.1)

noncomputable def recvReleaseState {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n)
    (msg : CMsg)
    (param : PruneReportParam) : SymState HomeState NodeState n :=
  { shared := recvReleaseShared s i msg param
  , locals := recvReleaseLocals s i }

noncomputable def recvReleaseAckShared {n : Nat}
    (s : SymState HomeState NodeState n) : HomeState :=
  { s.shared with pendingReleaseAck := none }

def recvReleaseAckLocal (node : NodeState) : NodeState :=
  { node with
      chanD := none
      releaseInFlight := false }

def recvReleaseAckLocals {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) : Fin n → NodeState :=
  setFn s.locals i (recvReleaseAckLocal (s.locals i))

noncomputable def recvReleaseAckState {n : Nat}
    (s : SymState HomeState NodeState n)
    (i : Fin n) : SymState HomeState NodeState n :=
  { shared := recvReleaseAckShared s
  , locals := recvReleaseAckLocals s i }

def scheduleProbeLocals {n : Nat}
    (s : SymState HomeState NodeState n)
    (requester : Fin n)
    (probeMask : Nat → Bool)
    (kind : ReqKind)
    (resultPerm : TLPerm)
    (source : SourceId) : Fin n → NodeState :=
  fun j =>
    let clearedA :=
      if j = requester then
        { (s.locals j) with chanA := none }
      else
        s.locals j
    if probeMask j.1 = true then
      { clearedA with
          chanB := some
            { opcode := probeOpcodeOfKind kind
            , param := probeCapOfResult resultPerm
            , source := source } }
    else
      clearedA

noncomputable def recvAcquireShared {n : Nat}
    (s : SymState HomeState NodeState n)
    (requester : Fin n)
    (kind : ReqKind)
    (grow : GrowParam)
    (source : SourceId) : HomeState :=
  { mem := s.shared.mem
  , dir := s.shared.dir
  , currentTxn := some (plannedTxn s requester kind grow source)
  , pendingGrantAck := none
  , pendingReleaseAck := none
  , nextSink := s.shared.nextSink + 1 }

noncomputable def recvAcquireLocals {n : Nat}
    (s : SymState HomeState NodeState n)
    (requester : Fin n)
    (kind : ReqKind)
    (grow : GrowParam)
    (source : SourceId) : Fin n → NodeState :=
  scheduleProbeLocals s requester (probeMaskForResult s requester grow.result) kind grow.result source

noncomputable def recvAcquireState {n : Nat}
    (s : SymState HomeState NodeState n)
    (requester : Fin n)
    (kind : ReqKind)
    (grow : GrowParam)
    (source : SourceId) : SymState HomeState NodeState n :=
  { shared := recvAcquireShared s requester kind grow source
  , locals := recvAcquireLocals s requester kind grow source }

def SendAcquireBlock {n : Nat}
    (s s' : SymState HomeState NodeState n)
    (i : Fin n) (grow : GrowParam) (source : SourceId) : Prop :=
  (s.locals i).chanA = none ∧
  (s.locals i).chanB = none ∧
  (s.locals i).chanC = none ∧
  (s.locals i).pendingSource = none ∧
  (s.locals i).releaseInFlight = false ∧
  (s.locals i).line.perm = .N ∧
  grow.legalFrom (s.locals i).line.perm ∧
  s' = { shared := s.shared
       , locals := setFn s.locals i
           { (s.locals i) with
               chanA := some (mkAcquireBlockMsg grow source)
               pendingSource := some source } }

def SendAcquirePerm {n : Nat}
    (s s' : SymState HomeState NodeState n)
    (i : Fin n) (grow : GrowParam) (source : SourceId) : Prop :=
  (s.locals i).chanA = none ∧
  (s.locals i).chanB = none ∧
  (s.locals i).chanC = none ∧
  (s.locals i).pendingSource = none ∧
  (s.locals i).releaseInFlight = false ∧
  grow.legalFrom (s.locals i).line.perm ∧
  grow.result = .T ∧
  s' = { shared := s.shared
       , locals := setFn s.locals i
           { (s.locals i) with
               chanA := some (mkAcquirePermMsg grow source)
               pendingSource := some source } }

def RecvAcquireBlockAtManager {n : Nat}
    (s s' : SymState HomeState NodeState n)
    (i : Fin n) (grow : GrowParam) (source : SourceId) : Prop :=
  s.shared.currentTxn = none ∧
  s.shared.pendingGrantAck = none ∧
  s.shared.pendingReleaseAck = none ∧
  (∀ j : Fin n, (s.locals j).chanC = none) ∧
  (s.locals i).chanA = some (mkAcquireBlockMsg grow source) ∧
  (s.locals i).line.perm = .N ∧
  grow.legalFrom (s.locals i).line.perm ∧
  ¬hasDirtyOther s i ∧
  ((hasCachedOther s i ∧ grow.result = .B) ∨
   (allOthersInvalid s i ∧ grow.result = .T)) ∧
  allTargetBsEmpty s (probeMaskForResult s i grow.result) ∧
  s' = recvAcquireState s i .acquireBlock grow source

def RecvAcquirePermAtManager {n : Nat}
    (s s' : SymState HomeState NodeState n)
    (i : Fin n) (grow : GrowParam) (source : SourceId) : Prop :=
  s.shared.currentTxn = none ∧
  s.shared.pendingGrantAck = none ∧
  s.shared.pendingReleaseAck = none ∧
  (∀ j : Fin n, (s.locals j).chanC = none) ∧
  (s.locals i).chanA = some (mkAcquirePermMsg grow source) ∧
  grow.legalFrom (s.locals i).line.perm ∧
  grow.result = .T ∧
  ¬hasDirtyOther s i ∧
  allTargetBsEmpty s (probeMaskForResult s i grow.result) ∧
  s' = recvAcquireState s i .acquirePerm grow source

def RecvAcquireAtManager {n : Nat}
    (s s' : SymState HomeState NodeState n) (i : Fin n) : Prop :=
  (∃ grow source, RecvAcquireBlockAtManager s s' i grow source) ∨
  (∃ grow source, RecvAcquirePermAtManager s s' i grow source)

def RecvProbeAtMaster {n : Nat}
    (s s' : SymState HomeState NodeState n) (i : Fin n) : Prop :=
  ∃ tx msg,
    s.shared.currentTxn = some tx ∧
    tx.phase = .probing ∧
    tx.probesRemaining i.1 = true ∧
    (s.locals i).chanA = none ∧
    (s.locals i).chanB = some msg ∧
    msg.source = tx.source ∧
    msg.opcode = probeOpcodeOfKind tx.kind ∧
    msg.param = probeCapOfResult tx.resultPerm ∧
    (s.locals i).chanC = none ∧
    s' = recvProbeState s i msg

def RecvProbeAckAtManager {n : Nat}
    (s s' : SymState HomeState NodeState n) (i : Fin n) : Prop :=
  ∃ tx msg,
    s.shared.currentTxn = some tx ∧
    tx.phase = .probing ∧
    tx.probesRemaining i.1 = true ∧
    (s.locals i).chanA = none ∧
    (s.locals i).chanC = some msg ∧
    msg.source = i.1 ∧
    probeAckMsgWellFormed msg ∧
    s' = recvProbeAckState s i tx

def SendGrantToRequester {n : Nat}
    (s s' : SymState HomeState NodeState n) (i : Fin n) : Prop :=
  ∃ tx,
    s.shared.currentTxn = some tx ∧
    tx.requester = i.1 ∧
    tx.phase = .grantReady ∧
    s.shared.pendingGrantAck = none ∧
    s.shared.pendingReleaseAck = none ∧
    (s.locals i).chanD = none ∧
    (s.locals i).chanE = none ∧
    (s.locals i).pendingSink = none ∧
    s' = sendGrantState s i tx

def RecvGrantAtMaster {n : Nat}
    (s s' : SymState HomeState NodeState n) (i : Fin n) : Prop :=
  ∃ tx msg,
    s.shared.currentTxn = some tx ∧
    tx.requester = i.1 ∧
    tx.phase = .grantPendingAck ∧
    s.shared.pendingGrantAck = some i.1 ∧
    (s.locals i).chanA = none ∧
    (s.locals i).chanD = some msg ∧
    (s.locals i).chanE = none ∧
    (s.locals i).pendingSink = some tx.sink ∧
    msg = grantMsgOfTxn tx ∧
    s' = recvGrantState s i tx

def RecvGrantAckAtManager {n : Nat}
    (s s' : SymState HomeState NodeState n) (i : Fin n) : Prop :=
  ∃ tx msg,
    s.shared.currentTxn = some tx ∧
    tx.requester = i.1 ∧
    tx.phase = .grantPendingAck ∧
    s.shared.pendingGrantAck = some i.1 ∧
    (s.locals i).chanD = none ∧
    (s.locals i).chanE = some msg ∧
    (s.locals i).pendingSink = some tx.sink ∧
    msg = ({ sink := tx.sink } : EMsg) ∧
    s' = recvGrantAckState s i

def SendRelease {n : Nat}
    (s s' : SymState HomeState NodeState n)
    (i : Fin n) (param : PruneReportParam) : Prop :=
  s.shared.currentTxn = none ∧
  s.shared.pendingGrantAck = none ∧
  s.shared.pendingReleaseAck = none ∧
  (∀ j : Fin n, j ≠ i → (s.locals j).chanC = none) ∧
  (s.locals i).chanA = none ∧
  (s.locals i).chanB = none ∧
  (s.locals i).chanC = none ∧
  (s.locals i).chanD = none ∧
  (s.locals i).chanE = none ∧
  (s.locals i).pendingSource = none ∧
  (s.locals i).pendingSink = none ∧
  (s.locals i).releaseInFlight = false ∧
  param.legalFrom (s.locals i).line.perm ∧
  (s.locals i).line.dirty = false ∧
  s' = sendReleaseState s i param false

def SendReleaseData {n : Nat}
    (s s' : SymState HomeState NodeState n)
    (i : Fin n) (param : PruneReportParam) : Prop :=
  s.shared.currentTxn = none ∧
  s.shared.pendingGrantAck = none ∧
  s.shared.pendingReleaseAck = none ∧
  (∀ j : Fin n, j ≠ i → (s.locals j).chanC = none) ∧
  (s.locals i).chanA = none ∧
  (s.locals i).chanB = none ∧
  (s.locals i).chanC = none ∧
  (s.locals i).chanD = none ∧
  (s.locals i).chanE = none ∧
  (s.locals i).pendingSource = none ∧
  (s.locals i).pendingSink = none ∧
  (s.locals i).releaseInFlight = false ∧
  param.legalFrom (s.locals i).line.perm ∧
  (s.locals i).line.dirty = true ∧
  s' = sendReleaseState s i param true

def RecvReleaseAtManager {n : Nat}
    (s s' : SymState HomeState NodeState n) (i : Fin n) : Prop :=
  ∃ msg param,
    s.shared.currentTxn = none ∧
    s.shared.pendingGrantAck = none ∧
    s.shared.pendingReleaseAck = none ∧
    (s.locals i).releaseInFlight = true ∧
    (s.locals i).chanC = some msg ∧
    msg.source = i.1 ∧
    releaseMsgWellFormed msg ∧
    msg.param = some param ∧
    (s.locals i).line.perm = param.result ∧
    (s.locals i).chanD = none ∧
    s' = recvReleaseState s i msg param

def RecvReleaseAckAtMaster {n : Nat}
    (s s' : SymState HomeState NodeState n) (i : Fin n) : Prop :=
  ∃ msg,
    s.shared.currentTxn = none ∧
    s.shared.pendingGrantAck = none ∧
    s.shared.pendingReleaseAck = some i.1 ∧
    (s.locals i).releaseInFlight = true ∧
    (s.locals i).chanD = some msg ∧
    msg = releaseAckMsg i.1 ∧
    s' = recvReleaseAckState s i

noncomputable def tlMessages : SymSharedSpec where
  Shared := HomeState
  Local := NodeState
  ActType := Act
  init_shared := fun sh =>
    sh.mem = 0 ∧
    (∀ k : Nat, sh.dir k = .N) ∧
    sh.currentTxn = none ∧
    sh.pendingGrantAck = none ∧
    sh.pendingReleaseAck = none ∧
    sh.nextSink = 0
  init_local := fun loc =>
    loc.line = { perm := .N, valid := false, dirty := false, data := 0 } ∧
    loc.chanA = none ∧
    loc.chanB = none ∧
    loc.chanC = none ∧
    loc.chanD = none ∧
    loc.chanE = none ∧
    loc.pendingSource = none ∧
    loc.pendingSink = none ∧
    loc.releaseInFlight = false
  step := fun _n i a s s' =>
    match a with
    | .sendAcquireBlock grow source => SendAcquireBlock s s' i grow source
    | .sendAcquirePerm grow source => SendAcquirePerm s s' i grow source
    | .recvAcquireAtManager => RecvAcquireAtManager s s' i
    | .recvProbeAtMaster => RecvProbeAtMaster s s' i
    | .recvProbeAckAtManager => RecvProbeAckAtManager s s' i
    | .sendGrantToRequester => SendGrantToRequester s s' i
    | .recvGrantAtMaster => RecvGrantAtMaster s s' i
    | .recvGrantAckAtManager => RecvGrantAckAtManager s s' i
    | .sendRelease param => SendRelease s s' i param
    | .sendReleaseData param => SendReleaseData s s' i param
    | .recvReleaseAtManager => RecvReleaseAtManager s s' i
    | .recvReleaseAckAtMaster => RecvReleaseAckAtMaster s s' i

end TileLink.Messages
