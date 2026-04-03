import Leslie.Examples.CacheCoherence.TileLink.Messages.FrameLemmas

namespace TileLink.Messages

open TileLink SymShared

def lineWFInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ i : Fin n, (s.locals i).line.WellFormed

def dirInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  ∀ i : Fin n, (s.locals i).chanC = none → s.shared.dir i.1 = (s.locals i).line.perm

def pendingInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  match s.shared.currentTxn with
  | none =>
      s.shared.pendingGrantAck = none ∧
      match s.shared.pendingReleaseAck with
      | none => True
      | some i =>
          i < n ∧ ∃ fi : Fin n, fi.1 = i ∧ (s.locals fi).releaseInFlight = true
  | some tx =>
      s.shared.pendingReleaseAck = none ∧
      if tx.phase = .grantPendingAck then
        s.shared.pendingGrantAck = some tx.requester
      else
        s.shared.pendingGrantAck = none

def txnCoreInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  match s.shared.currentTxn with
  | none => True
  | some tx =>
      tx.requester < n ∧
      (tx.phase = .probing ∨ tx.phase = .grantReady ∨ tx.phase = .grantPendingAck) ∧
      tx.resultPerm = tx.grow.result ∧
      (tx.grantHasData = false → tx.resultPerm = .T) ∧
      tx.probesNeeded tx.requester = false ∧
      (∀ k : Nat, tx.probesRemaining k = true → tx.probesNeeded k = true) ∧
      (tx.phase = .grantReady → ∀ j : Fin n, tx.probesRemaining j.1 = false) ∧
      (tx.phase = .grantPendingAck → ∀ j : Fin n, tx.probesRemaining j.1 = false)

def coreInv (n : Nat) (s : SymState HomeState NodeState n) : Prop :=
  lineWFInv n s ∧ dirInv n s ∧ pendingInv n s ∧ txnCoreInv n s

theorem init_lineWFInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → lineWFInv n s := by
  intro s hinit i
  rcases hinit with ⟨_, hlocals⟩
  rcases hlocals i with ⟨hline, _, _, _, _, _, _, _, _⟩
  rw [hline]
  exact CacheLine.default_wf

theorem init_dirInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → dirInv n s := by
  intro s hinit i
  rcases hinit with ⟨⟨_, hdir, _, _, _, _⟩, hlocals⟩
  rcases hlocals i with ⟨hline, _, _, hC, _, _, _, _, _⟩
  intro hCnone
  simpa [hline, hC] using hdir i.1

theorem init_pendingInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → pendingInv n s := by
  intro s hinit
  rcases hinit with ⟨⟨_, _, htxn, hgrant, hrel, _⟩, _⟩
  simp [pendingInv, htxn, hgrant, hrel]

theorem init_txnCoreInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → txnCoreInv n s := by
  intro s hinit
  rcases hinit with ⟨⟨_, _, htxn, _, _, _⟩, _⟩
  rw [txnCoreInv, htxn]
  trivial

theorem init_coreInv (n : Nat) :
    ∀ s : SymState HomeState NodeState n, (tlMessages.toSpec n).init s → coreInv n s := by
  intro s hinit
  exact ⟨init_lineWFInv n s hinit, init_dirInv n s hinit,
    init_pendingInv n s hinit, init_txnCoreInv n s hinit⟩

end TileLink.Messages
