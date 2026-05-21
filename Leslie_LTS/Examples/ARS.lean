import Leslie_LTS.Framework
import Mathlib.Data.ZMod.Basic
import Leslie_LTS.Examples.BrachaBRB
import Leslie_LTS.Examples.RabinICP
import Leslie_LTS.Examples.UtilityByzantine

/-! # Asynchronous Recoverable Sharing (ARS) — LTS Formulation

  ARS for `n` processes with at most `f` Byzantine faults.
  Computations are in Z_p where `p` is prime. ICP security parameter `k`.
  ## Architecture
  The ARS system is a three-level parallel composition:
      ars = parallel
              (parallel arsCore brbBankSys brb_sync)
              icpBankSys
              outer_sync
  - **BRB Bank** (`iparallel`): `n + n²` BrachaBRB instances for OK and
    recovery broadcasts. Corruption is global; other actions per-instance.
  - **ICP Bank** (`iparallel`): `n²` RabinICP instances wrapped with
    enriched labels (`ICPExtLabel`). Corruption is global (mapped from
    ARS process ids to ICP roles); observation labels (`genReady`,
    `verifyReady`, `authReady`) carry data as stutter steps.
  - **ARS Core**: Protocol logic — ICP phase tracking, polynomial,
    thresholds, interpolation. Sync labels connect to both banks.
  - **Sync predicates**: `brb_sync` ties core ↔ BRB; `outer_sync` ties
    the inner system ↔ ICP bank.
-/

open LTS

namespace ARS_LTS

/-! ## Parameters -/

variable (n f : Nat) (p : Nat) [NeZero p] (k : Nat)

/-- Shorthand for the value type. -/
abbrev V (p : Nat) := ZMod p

/-! ## Polynomial Representation -/

/-- Evaluate a polynomial (given by coefficients) at a point. -/
def evalPoly (coeffs : Fin (f + 1) → V p) (x : V p) : V p :=
  (List.finRange (f + 1)).foldl (fun acc i =>
    acc + coeffs i * (List.finRange i.val).foldl (fun r _ => r * x) (1 : V p)) (0 : V p)

/-! ## Shared Types -/

/-- An ICP instance identifier: the intermediary and the receiver. -/
structure ICPId (n : Nat) where
  intermediary : Fin n
  receiver : Fin n
  deriving DecidableEq

/-- The phase of an ICP instance from the perspective of a participant. -/
inductive ICPPhase where
  | idle | generationDone | verificationDone | authenticationDone
  deriving DecidableEq

/-- Value type for BRB messages. OK broadcasts carry `.ok`; recovery
    broadcasts carry `.share v` with the authenticated share value. -/
inductive BRBValue (p : Nat) where
  | ok : BRBValue p
  | share (v : V p) : BRBValue p
  deriving DecidableEq

instance : Inhabited (BRBValue p) := ⟨.ok⟩

/-- Index type for BRB instances. -/
inductive BRBInst (n : Nat) where
  | ok (sender : Fin n)
  | recovery (id id' : Fin n)
  deriving DecidableEq

/-- The designated sender for each BRB instance. -/
def brbSender : BRBInst n → Fin n
  | .ok sender => sender
  | .recovery _ id' => id'

/-! ## 1. BRB Bank (via `iparallel`)

    Indexed parallel composition of all BRB instances. Corruption
    synchronizes globally; all other BRB actions are per-instance. -/

/-- The BRB bank: `n + n²` BrachaBRB instances composed via `iparallel`. -/
def brbBankSys :=
  iparallel (fun inst => BRB_LTS.brb n f (BRBValue p) (brbSender n inst))
            (fun l => ∃ i, l = BRB_LTS.Label.corrupt i)

/-! ## 2. ICP Bank (via `iparallel`)

    Each of the `n²` RabinICP instances is wrapped in `icpExt`, which
    enriches the label type with:
    - `corruptProcess i` — maps ARS process `i` to the appropriate ICP
      roles (Dealer/Intermediary/Receiver) for that instance
    - `feedSecret sec` — delegates to `RabinICP.step (.input sec)`
    - `genReady`, `verifyReady`, `authReady` — stutter steps that carry
      phase-completion data in the label for synchronization
    The bank uses `iparallel` with `corruptProcess` as the global sync. -/

/-- Extended labels for a single ICP instance. -/
inductive ICPExtLabel (n : Nat) (p : Nat) (k : Nat) where
  /-- Standard ICP action (excluding corrupt, which is handled by `corruptProcess`). -/
  | icp (l : RabinICP.Label p k)
  /-- ARS-level corruption: corrupt process `i`'s roles in this instance. -/
  | corruptProcess (i : Fin n)
  /-- Stutter: ICP generation data received. -/
  | genReady
  /-- Stutter: ICP verification succeeded. -/
  | verifyReady
  /-- Stutter: ICP authentication decided with result and value. -/
  | authReady (accepted : Bool) (val : Option (V p))

/-- Per-instance wrapper around `RabinICP.system`. Parameterized by
    `dealer` (the ARS dealer) and `inst` (the ICP instance id) so that
    `corruptProcess` knows the role mapping. -/
def icpExt (dealer : Fin n) (inst : ICPId n) :
    System (RabinICP.State p k) (ICPExtLabel n p k) where
  init := (RabinICP.system p k).init
  step := fun s l s' =>
    match l with
    | .icp l =>
        (∀ proc, l ≠ .corrupt proc) ∧
        RabinICP.step p k s l s'
    | .corruptProcess i =>
        -- Chain up to 3 RabinICP corruption steps, one per role i plays
        ∃ s₁ s₂ : RabinICP.State p k,
          (if i = dealer
           then RabinICP.step p k s (.corrupt .Dealer) s₁
           else s₁ = s) ∧
          (if i = inst.intermediary
           then RabinICP.step p k s₁ (.corrupt .Intermediary) s₂
           else s₂ = s₁) ∧
          (if i = inst.receiver
           then RabinICP.step p k s₂ (.corrupt .Receiver) s'
           else s' = s₂)
    | .genReady =>
        s.intermediary.received.isSome = true ∧
        s' = s
    | .verifyReady =>
        s.intermediary.verified = some true ∧ s' = s
    | .authReady accepted val =>
        s.receiver.decision = some accepted ∧
        (accepted = true → ∃ v, val = some v) ∧
        (accepted = false → val = none) ∧
        s' = s

/-- The ICP bank: `n²` wrapped ICP instances composed via `iparallel`.
    `corruptProcess` is the global sync label. -/
def icpBankSys (dealer : Fin n) :=
  iparallel (fun inst => icpExt n p k dealer inst)
            (fun l => ∃ i, l = ICPExtLabel.corruptProcess i)

/-! ## 3. ARS Core

    Protocol logic: ICP phase tracking, polynomial selection, thresholds,
    interpolation. Synchronization labels connect to both banks:
    - `corrupt`, `broadcastOK`, `deliverOK`, `broadcastRecovery`,
      `deliverRecovery` sync with BRB bank
    - `feedSecret`, `icpGenDone`, `icpVerifyDone`, `icpAuthDone` sync
      with ICP bank -/

namespace Core

/-- Per-process local state. -/
structure LocalState (n f : Nat) (p : Nat) where
  icpPhase : ICPId n → ICPPhase
  verifiedCount : Nat
  okBroadcast : Bool
  okRecv : Fin n → Bool
  okCount : Nat
  sharingComplete : Bool
  authSuccess : ICPId n → Bool
  authValue : ICPId n → Option (V p)
  recoveryBroadcast : ICPId n → Bool
  recoveryRecvCount : Fin n → V p → Nat
  recoveryRecv : Fin n → Fin n → Bool
  interpolationSet : List (Fin n × V p)
  recoveredSecret : Option (V p)

/-- The core system state. -/
structure State (n f : Nat) (p : Nat) where
  local_ : Fin n → Core.LocalState n f p
  corrupted : List (Fin n)
  dealerPoly : Option (Fin (f + 1) → V p)

/-- Core labels. Each label is either a sync point with the BRB bank,
    a sync point with the ICP bank, or a core-only action. -/
inductive Label (n f : Nat) (p : Nat) where
  -- Sync with BRB bank
  | corrupt (i : Fin n)
  | broadcastOK (id : Fin n)
  | deliverOK (p_id : Fin n) (id : Fin n)
  | broadcastRecovery (inst : ICPId n) (val : V p)
  | deliverRecovery (q : Fin n) (id id' : Fin n) (val : V p)
  -- Sync with ICP bank
  | feedSecret (inst : ICPId n) (sec : V p)
  | icpGenDone (inst : ICPId n)
  | icpVerifyDone (inst : ICPId n)
  | icpAuthDone (inst : ICPId n) (success : Bool) (val : Option (V p))
  -- Core-only
  | input (s : V p) (poly : Fin (f + 1) → V p)
  | sharingDone (id' : Fin n)
  | acceptLegal (q : Fin n) (id : Fin n) (val : V p)
  | output (q : Fin n) (secret : V p)

def isCorrect (s : Core.State n f p) (i : Fin n) : Prop := i ∉ s.corrupted

def LocalState.init : Core.LocalState n f p where
  icpPhase := fun _ => .idle
  verifiedCount := 0
  okBroadcast := false
  okRecv := fun _ => false
  okCount := 0
  sharingComplete := false
  authSuccess := fun _ => false
  authValue := fun _ => none
  recoveryBroadcast := fun _ => false
  recoveryRecvCount := fun _ _ => 0
  recoveryRecv := fun _ _ => false
  interpolationSet := []
  recoveredSecret := none

def okThreshold : Nat := 2 * f + 1
def sharingThreshold : Nat := 2 * f + 1
def legalThreshold : Nat := f + 1
def interpolationThreshold : Nat := f + 1

/-- The ARS core system. -/
def arsCore (dealer : Fin n) : System (Core.State n f p) (Core.Label n f p) where
  init := fun s =>
    (∀ i, s.local_ i = Core.LocalState.init n f p) ∧
    s.corrupted = [] ∧
    s.dealerPoly = none
  step := fun s lbl s' =>
    match lbl with
    /- ── Sync with both BRB and ICP banks ────────────────────────── -/
    -- Adversary corrupts process i. Syncs with BRB bank (global corrupt)
    -- and ICP bank (global corruptProcess).
    | .corrupt i =>
        Core.isCorrect n f p s i ∧
        s.corrupted.length + 1 ≤ f ∧
        s' = { s with corrupted := i :: s.corrupted }
    /- ── Sync with BRB bank only ─────────────────────────────────── -/
    -- Process id initiates OK broadcast after ≥ 2f+1 verified ICP instances.
    -- Syncs with BRB instance (ok id) input.
    | .broadcastOK id =>
        Core.isCorrect n f p s id ∧
        (s.local_ id).okBroadcast = false ∧
        (s.local_ id).verifiedCount ≥ Core.okThreshold f ∧
        s' = { s with
          local_ := fun i => if i = id
            then { s.local_ id with okBroadcast := true }
            else s.local_ i }
    -- Process p_id receives BRB-delivered OK from process id.
    -- Syncs with BRB instance (ok id) output.
    | .deliverOK p_id id =>
        Core.isCorrect n f p s p_id ∧
        (s.local_ p_id).okRecv id = false ∧
        s' = { s with
          local_ := fun i => if i = p_id
            then { s.local_ p_id with
              okRecv := fun j => if j = id then true else (s.local_ p_id).okRecv j
              okCount := (s.local_ p_id).okCount + 1 }
            else s.local_ i }
    -- Process id' initiates recovery broadcast of authenticated share.
    -- Syncs with BRB instance (recovery id id') input.
    | .broadcastRecovery inst val =>
        Core.isCorrect n f p s inst.receiver ∧
        (s.local_ inst.receiver).authSuccess inst = true ∧
        (s.local_ inst.receiver).authValue inst = some val ∧
        (s.local_ inst.receiver).recoveryBroadcast inst = false ∧
        s' = { s with
          local_ := fun i => if i = inst.receiver
            then { s.local_ inst.receiver with
              recoveryBroadcast := fun inst' =>
                if inst' = inst then true
                else (s.local_ inst.receiver).recoveryBroadcast inst' }
            else s.local_ i }
    -- Process q receives BRB-delivered recovery share (id, id', val).
    -- Syncs with BRB instance (recovery id id') output.
    | .deliverRecovery q id id' val =>
        Core.isCorrect n f p s q ∧
        (s.local_ q).recoveryRecv id id' = false ∧
        s' = { s with
          local_ := fun i => if i = q
            then { s.local_ q with
              recoveryRecv := fun j j' =>
                if j = id ∧ j' = id' then true
                else (s.local_ q).recoveryRecv j j'
              recoveryRecvCount := fun j v =>
                if j = id ∧ v = val then (s.local_ q).recoveryRecvCount j v + 1
                else (s.local_ q).recoveryRecvCount j v }
            else s.local_ i }
    /- ── Sync with ICP bank only ─────────────────────────────────── -/
    -- Dealer feeds poly(intermediary) to ICP instance as secret.
    -- Stutter step: validates sec matches polynomial, no state change.
    -- Syncs with ICP bank .icp (.input sec).
    | .feedSecret inst sec =>
        (∃ poly, s.dealerPoly = some poly ∧
          sec = evalPoly f p poly
            ((inst.intermediary.val : ZMod p))) ∧
        s' = s
    -- ICP generation complete for instance (id, id'). Updates icpPhase.
    -- The share value is internal to the ICP bank.
    -- Syncs with ICP bank genReady.
    | .icpGenDone inst =>
        Core.isCorrect n f p s inst.intermediary ∧
        (s.local_ inst.intermediary).icpPhase inst = .idle ∧
        s' = { s with
          local_ := fun i => if i = inst.intermediary
            then { s.local_ inst.intermediary with
              icpPhase := fun inst' =>
                if inst' = inst then .generationDone
                else (s.local_ inst.intermediary).icpPhase inst' }
            else s.local_ i }
    -- ICP verification succeeded for instance (id, id'). Increments
    -- the intermediary's verifiedCount.
    -- Syncs with ICP bank verifyReady.
    | .icpVerifyDone inst =>
        Core.isCorrect n f p s inst.intermediary ∧
        (s.local_ inst.intermediary).icpPhase inst = .generationDone ∧
        s' = { s with
          local_ := fun i => if i = inst.intermediary
            then { s.local_ inst.intermediary with
              icpPhase := fun inst' =>
                if inst' = inst then .verificationDone
                else (s.local_ inst.intermediary).icpPhase inst'
              verifiedCount := (s.local_ inst.intermediary).verifiedCount + 1 }
            else s.local_ i }
    -- ICP authentication decided for instance (id, id'). Updates
    -- the receiver's authSuccess/authValue.
    -- Syncs with ICP bank authReady.
    | .icpAuthDone inst success val =>
        Core.isCorrect n f p s inst.receiver ∧
        (s.local_ inst.receiver).icpPhase inst ≠ .authenticationDone ∧
        (success = true → val.isSome = true) ∧
        s' = { s with
          local_ := fun i => if i = inst.receiver
            then { s.local_ inst.receiver with
              icpPhase := fun inst' =>
                if inst' = inst then .authenticationDone
                else (s.local_ inst.receiver).icpPhase inst'
              authSuccess := fun inst' =>
                if inst' = inst then success
                else (s.local_ inst.receiver).authSuccess inst'
              authValue := fun inst' =>
                if inst' = inst then val
                else (s.local_ inst.receiver).authValue inst' }
            else s.local_ i }
    /- ── Core-only actions (no sync) ─────────────────────────────── -/
    -- Dealer receives secret s and picks polynomial poly with poly(0) = s.
    | .input sec poly =>
        Core.isCorrect n f p s dealer ∧
        s.dealerPoly = none ∧
        poly ⟨0, Nat.zero_lt_succ f⟩ = sec ∧
        s' = { s with dealerPoly := some poly }
    -- Process id' considers sharing complete after ≥ 2f+1 OK deliveries.
    | .sharingDone id' =>
        Core.isCorrect n f p s id' ∧
        (s.local_ id').sharingComplete = false ∧
        (s.local_ id').okCount ≥ Core.sharingThreshold f ∧
        s' = { s with
          local_ := fun i => if i = id'
            then { s.local_ id' with sharingComplete := true }
            else s.local_ i }
    -- Process q accepts (id, val) as a legal share after ≥ f+1 matching
    -- recovery messages. Adds it to the interpolation set.
    | .acceptLegal q id val =>
        Core.isCorrect n f p s q ∧
        (s.local_ q).recoveryRecvCount id val ≥ Core.legalThreshold f ∧
        (id, val) ∉ (s.local_ q).interpolationSet ∧
        (∀ v, (id, v) ∉ (s.local_ q).interpolationSet) ∧
        s' = { s with
          local_ := fun i => if i = q
            then { s.local_ q with
              interpolationSet := (id, val) :: (s.local_ q).interpolationSet }
            else s.local_ i }
    -- Process q recovers the secret by interpolation after ≥ f+1 points in IS.
    -- The secret is the unique degree-≤-f polynomial through IS, evaluated at 0.
    | .output q secret =>
        Core.isCorrect n f p s q ∧
        (s.local_ q).recoveredSecret = none ∧
        (s.local_ q).interpolationSet.length ≥ Core.interpolationThreshold f ∧
        (∃ poly : Fin (f + 1) → V p,
          (∀ pt ∈ (s.local_ q).interpolationSet,
            evalPoly f p poly ((pt.1.val : ZMod p)) = pt.2) ∧
          secret = evalPoly f p poly (0 : V p)) ∧
        s' = { s with
          local_ := fun i => if i = q
            then { s.local_ q with recoveredSecret := some secret }
            else s.local_ i }

end Core

/-! ## 4. Composed ARS System

    Three-level parallel composition, all through generic combinators:
        ars dealer =
          parallel
            (parallel (arsCore dealer) brbBankSys brb_sync)
            (icpBankSys dealer)
            outer_sync
-/

/-- BRB synchronization: core ↔ BRB bank. -/
def brb_sync :
    Core.Label n f p → ICompLabel (BRBInst n) (BRB_LTS.Label n (BRBValue p)) → Prop
  | .corrupt i₁, .global (.corrupt i₂) => i₁ = i₂
  | .broadcastOK id, .ind inst (.input j v) =>
      inst = .ok id ∧ j = id ∧ v = .ok
  | .deliverOK p_id id, .ind inst (.output j v) =>
      inst = .ok id ∧ j = p_id ∧ v = .ok
  | .broadcastRecovery inst val, .ind brbInst (.input j v) =>
      brbInst = .recovery inst.intermediary inst.receiver ∧
      j = inst.receiver ∧ v = .share val
  | .deliverRecovery q id id' val, .ind brbInst (.output j v) =>
      brbInst = .recovery id id' ∧ j = q ∧ v = .share val
  | _, _ => False

/-- Inner system: core ↔ BRB bank via `parallel`. -/
def innerSys (dealer : Fin n) :=
  parallel (Core.arsCore n f p dealer) (brbBankSys n f p) (brb_sync n f p)

/-- Outer synchronization: inner system ↔ ICP bank.
    - Corruption syncs three-way (core + BRB + ICP)
    - `feedSecret`, `icpGenDone`, `icpVerifyDone`, `icpAuthDone` sync
      core labels with ICP observation/action labels -/
def outer_sync :
    CompLabel (Core.Label n f p)
      (ICompLabel (BRBInst n) (BRB_LTS.Label n (BRBValue p))) →
    ICompLabel (ICPId n) (ICPExtLabel n p k) → Prop
  | .sync (.corrupt i) _, .global (.corruptProcess i') =>
      i = i'
  | .left (.feedSecret inst sec), .ind inst' (.icp (.input sec')) =>
      inst = inst' ∧ sec = sec'
  | .left (.icpGenDone inst), .ind inst' .genReady =>
      inst = inst'
  | .left (.icpVerifyDone inst), .ind inst' .verifyReady =>
      inst = inst'
  | .left (.icpAuthDone inst succ val), .ind inst' (.authReady succ' val') =>
      inst = inst' ∧ succ = succ' ∧ val = val'
  | _, _ => False

/-- The ARS system: pure `parallel` composition, no hand-written step. -/
def ars (dealer : Fin n) :=
  parallel (innerSys n f p dealer) (icpBankSys n p k dealer)
           (outer_sync n f p k)

/-! ## Labelling -/

/-- Only `corrupt`, `input`, and `output` are external. -/
def ars_labelling [Inhabited (Fin n)]
    [Inhabited (BRB_LTS.Label n (BRBValue p))]
    [Inhabited (ICPExtLabel n p k)] :
    Labelling (CompLabel
      (CompLabel (Core.Label n f p)
        (ICompLabel (BRBInst n) (BRB_LTS.Label n (BRBValue p))))
      (ICompLabel (ICPId n) (ICPExtLabel n p k))) where
  is_internal := fun l =>
    match l with
    | .sync (.sync (.corrupt _) _) (.global (.corruptProcess _)) => false
    | .left (.left (.input _ _)) => false
    | .left (.left (.output _ _)) => false
    | _ => true
  tau := .left (.left (.sharingDone default))
  tau_internal := rfl

/-! ## Safety Properties -/

/-- Validity: if the dealer is never corrupted, outputs match the secret. -/
def validity (dealer : Fin n) :
    TraceProp
      ((Core.State n f p × (BRBInst n → BRB_LTS.State n (BRBValue p)))
        × (ICPId n → RabinICP.State p k))
      (CompLabel
        (CompLabel (Core.Label n f p)
          (ICompLabel (BRBInst n) (BRB_LTS.Label n (BRBValue p))))
        (ICompLabel (ICPId n) (ICPExtLabel n p k))) :=
  fun e _pos =>
    (∀ j, ∀ brb_l, e.labels j ≠
      .sync (.sync (.corrupt dealer) brb_l) (.global (.corruptProcess dealer))) →
    ∀ j q sec, e.labels j = .left (.left (.output q sec)) →
      ∃ j' s poly, e.labels j' = .left (.left (.input s poly)) ∧ sec = s

/-- Agreement: all output values agree. -/
def agreement :
    TraceProp
      ((Core.State n f p × (BRBInst n → BRB_LTS.State n (BRBValue p)))
        × (ICPId n → RabinICP.State p k))
      (CompLabel
        (CompLabel (Core.Label n f p)
          (ICompLabel (BRBInst n) (BRB_LTS.Label n (BRBValue p))))
        (ICompLabel (ICPId n) (ICPExtLabel n p k))) :=
  fun e _pos => ∀ j₁ j₂ q₁ q₂ s₁ s₂,
    e.labels j₁ = .left (.left (.output q₁ s₁)) →
    e.labels j₂ = .left (.left (.output q₂ s₂)) →
    s₁ = s₂

end ARS_LTS
