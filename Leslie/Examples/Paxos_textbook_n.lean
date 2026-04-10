import Leslie.Action
import Leslie.Round
import Leslie.Gadgets.SetFn

open TLA

namespace PaxosTextbookN

inductive Value where
  | v1 | v2
  deriving DecidableEq, Repr

structure ConsensusState where
  chosen : Option Value

inductive ConsensusAction where
  | choose1 | choose2

def consensus : ActionSpec ConsensusState ConsensusAction where
  init := fun s => s.chosen = none
  actions := fun
    | .choose1 => {
        gate := fun s => s.chosen = none
        transition := fun _ s' => s' = { chosen := some .v1 }
      }
    | .choose2 => {
        gate := fun s => s.chosen = none
        transition := fun _ s' => s' = { chosen := some .v2 }
      }

@[ext]
structure PaxosState (n m : Nat) where
  prom : Fin n → Nat
  got1b : Fin m → Fin n → Bool
  prop : Fin m → Option Value
  did2b : Fin m → Fin n → Bool

inductive PaxosAction (n m : Nat) where
  | p1b (p : Fin m) (i : Fin n)
  | p2a (p : Fin m)
  | p2b (p : Fin m) (i : Fin n)

def countTrue {n : Nat} (f : Fin n → Bool) : Nat :=
  ((List.finRange n).filter fun i => f i).length

def majority {n : Nat} (f : Fin n → Bool) : Bool := by
  exact decide (countTrue f * 2 > n)

theorem countTrue_setFn_true_ge {n : Nat} (f : Fin n → Bool) (i : Fin n) :
    countTrue f ≤ countTrue (setFn f i true) := by
  unfold countTrue
  exact filter_length_mono (List.finRange n) (fun j => f j) (fun j => setFn f i true j) (by
    intro j hj
    by_cases hji : j = i
    · subst hji
      simp [setFn]
    · simp [setFn, hji, hj])

theorem majority_setFn_true_of_majority {n : Nat} (f : Fin n → Bool) (i : Fin n)
    (h : majority f = true) : majority (setFn f i true) = true := by
  unfold majority at *
  have hmaj : countTrue f * 2 > n := by
    simpa [decide_eq_true_eq] using h
  have hle : countTrue f ≤ countTrue (setFn f i true) := countTrue_setFn_true_ge f i
  apply decide_eq_true
  omega

theorem exists_true_of_majority {n : Nat} {f : Fin n → Bool}
    (h : majority f = true) : ∃ i : Fin n, f i = true := by
  have hmaj : countTrue f * 2 > n := by
    unfold majority at h
    simpa [decide_eq_true_eq] using h
  by_contra hnone
  have hall : ∀ i : Fin n, f i = false := by
    intro i
    cases hfi : f i with
    | false => rfl
    | true => exact False.elim (hnone ⟨i, hfi⟩)
  have hzero : countTrue f = 0 := by
    unfold countTrue
    simp [hall]
  omega

def paxos (n m : Nat) (ballot : Fin m → Nat) : ActionSpec (PaxosState n m) (PaxosAction n m) where
  init := fun s =>
    (∀ i, s.prom i = 0) ∧
    (∀ p i, s.got1b p i = false) ∧
    (∀ p, s.prop p = none) ∧
    (∀ p i, s.did2b p i = false)
  actions := fun
    | .p1b p i => {
        gate := fun s => s.got1b p i = false ∧ s.prom i ≤ ballot p
        transition := fun s s' =>
          s' = {
            s with
            prom := setFn s.prom i (ballot p)
            got1b := setFn s.got1b p (setFn (s.got1b p) i true)
          }
      }
    | .p2a p => {
        gate := fun s => s.prop p = none ∧ majority (s.got1b p) = true
        transition := fun s s' =>
          ∃ v,
            (∀ q w, s.prop q = some w → v = w) ∧
            s' = { s with prop := setFn s.prop p (some v) }
      }
    | .p2b p i => {
        gate := fun s => s.did2b p i = false ∧ s.prom i ≤ ballot p
        transition := fun s s' =>
          ∃ v, s.prop p = some v ∧
            s' = {
              s with
              prom := setFn s.prom i (ballot p)
              did2b := setFn s.did2b p (setFn (s.did2b p) i true)
            }
      }

structure PaxosInv {n m : Nat} (s : PaxosState n m) : Prop where
  hA : ∀ p i, s.did2b p i = true → s.prop p ≠ none
  hK : ∀ p q v w, s.prop p = some v → s.prop q = some w → v = w

def paxos_inv {n m : Nat} (s : PaxosState n m) : Prop := PaxosInv s

def agreement {n m : Nat} (s : PaxosState n m) : Prop :=
  ∀ p q v w,
    majority (s.did2b p) = true →
    majority (s.did2b q) = true →
    s.prop p = some v →
    s.prop q = some w →
    v = w

theorem paxos_inv_init {n m : Nat} (ballot : Fin m → Nat) :
    ∀ s, (paxos n m ballot).init s → paxos_inv s := by
  intro s hinit
  rcases hinit with ⟨_, _, hprop, hdid⟩
  exact {
    hA := by
      intro p i hi
      simp [hdid p i] at hi
    hK := by
      intro p q v w hp hq
      simp [hprop p] at hp
  }

theorem paxos_inv_next {n m : Nat} (ballot : Fin m → Nat) :
    ∀ s s', paxos_inv s →
      (∃ a, ((paxos n m ballot).actions a).fires s s') →
      paxos_inv s' := by
  intro s s' hinv ⟨a, hfires⟩
  cases a with
  | p1b p i =>
      simp only [GatedAction.fires] at hfires
      dsimp only [paxos] at hfires
      obtain ⟨_, rfl⟩ := hfires
      exact {
        hA := by
          intro p' i' h
          exact hinv.hA p' i' h
        hK := by
          intro p q v w hp hq
          exact hinv.hK p q v w hp hq
      }
  | p2a p =>
      simp only [GatedAction.fires] at hfires
      dsimp only [paxos] at hfires
      obtain ⟨⟨hpn, _⟩, v, hcon, rfl⟩ := hfires
      exact {
        hA := by
          intro p' i' h
          by_cases hp' : p' = p
          · subst hp'
            simp [setFn]
          · have hold : s.did2b p' i' = true := by simpa using h
            have hnon : s.prop p' ≠ none := hinv.hA p' i' hold
            simpa [setFn, hp'] using hnon
        hK := by
          intro p1 p2 x y hp1 hp2
          by_cases hp1p : p1 = p
          · subst hp1p
            have hx : v = x := by simpa [setFn] using hp1
            by_cases hp2p : p2 = p1
            · subst hp2p
              have hy : v = y := by simpa [setFn] using hp2
              exact hx.symm.trans hy
            · have hp2old : s.prop p2 = some y := by simpa [setFn, hp2p] using hp2
              have hvy : v = y := hcon p2 y hp2old
              exact hx.symm.trans hvy
          · have hp1old : s.prop p1 = some x := by simpa [setFn, hp1p] using hp1
            by_cases hp2p : p2 = p
            · subst hp2p
              have hy : v = y := by simpa [setFn] using hp2
              have hvx : v = x := hcon p1 x hp1old
              exact hvx.symm.trans hy
            · have hp2old : s.prop p2 = some y := by simpa [setFn, hp2p] using hp2
              exact hinv.hK p1 p2 x y hp1old hp2old
      }
  | p2b p i =>
      simp only [GatedAction.fires] at hfires
      dsimp only [paxos] at hfires
      obtain ⟨⟨_, _⟩, v, hpv, rfl⟩ := hfires
      exact {
        hA := by
          intro p' i' h
          by_cases hp' : p' = p
          · subst hp'
            by_cases hi' : i' = i
            · subst hi'
              simp [setFn] at h
              simp [hpv]
            · have hold : s.did2b p' i' = true := by
                simpa [setFn, hi'] using h
              exact hinv.hA p' i' hold
          · have hold : s.did2b p' i' = true := by
              simpa [setFn, hp'] using h
            exact hinv.hA p' i' hold
        hK := by
          intro p1 p2 x y hp1 hp2
          have hp1old : s.prop p1 = some x := by simpa using hp1
          have hp2old : s.prop p2 = some y := by simpa using hp2
          exact hinv.hK p1 p2 x y hp1old hp2old
      }

theorem agreement_of_inv {n m : Nat} (s : PaxosState n m)
    (hinv : paxos_inv s) : agreement s := by
  intro p q v w hmp hmq hp hq
  exact hinv.hK p q v w hp hq

end PaxosTextbookN
