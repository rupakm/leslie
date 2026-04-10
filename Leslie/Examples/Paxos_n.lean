import Leslie.Action
import Leslie.Round
import Leslie.Gadgets.SetFn

open TLA

namespace PaxosN

inductive Value where
  | v1 | v2
  deriving DecidableEq, Repr

inductive Ballot where
  | b1 | b2
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
structure PaxosState (n : Nat) where
  prom : Fin n → Option Ballot
  got1b1 : Fin n → Bool
  got1b2 : Fin n → Bool
  prop1 : Option Value
  prop2 : Option Value
  did2b1 : Fin n → Bool
  did2b2 : Fin n → Bool

inductive PaxosAction (n : Nat) where
  | p1b_1 (i : Fin n)
  | p1b_2 (i : Fin n)
  | p2a_1
  | p2a_2
  | p2b_1 (i : Fin n)
  | p2b_2 (i : Fin n)

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
    | true =>
        exfalso
        exact hnone ⟨i, hfi⟩
  have hzero : countTrue f = 0 := by
    unfold countTrue
    simp [hall]
  omega

def paxos (n : Nat) : ActionSpec (PaxosState n) (PaxosAction n) where
  init := fun s =>
    (∀ i, s.prom i = none) ∧
    (∀ i, s.got1b1 i = false) ∧
    (∀ i, s.got1b2 i = false) ∧
    s.prop1 = none ∧
    s.prop2 = none ∧
    (∀ i, s.did2b1 i = false) ∧
    (∀ i, s.did2b2 i = false)
  actions := fun
    | .p1b_1 i => {
        gate := fun s => s.got1b1 i = false ∧ (s.prom i = none ∨ s.prom i = some .b1)
        transition := fun s s' =>
          s' = {
            s with
            prom := setFn s.prom i (some .b1)
            got1b1 := setFn s.got1b1 i true
          }
      }
    | .p1b_2 i => {
        gate := fun s => s.got1b2 i = false
        transition := fun s s' =>
          s' = {
            s with
            prom := setFn s.prom i (some .b2)
            got1b2 := setFn s.got1b2 i true
          }
      }
    | .p2a_1 => {
        gate := fun s => s.prop1 = none ∧ majority s.got1b1 = true
        transition := fun s s' => ∃ v, s' = { s with prop1 := some v }
      }
    | .p2a_2 => {
        gate := fun s => s.prop2 = none ∧ majority s.got1b2 = true
        transition := fun s s' => ∃ v, s' = { s with prop2 := some v }
      }
    | .p2b_1 i => {
        gate := fun s =>
          s.did2b1 i = false ∧
          (s.prom i = none ∨ s.prom i = some .b1) ∧
          s.prop2 = none
        transition := fun s s' =>
          ∃ v, s.prop1 = some v ∧
            s' = {
              s with
              prom := setFn s.prom i (some .b1)
              did2b1 := setFn s.did2b1 i true
            }
      }
    | .p2b_2 i => {
        gate := fun s => s.did2b2 i = false
        transition := fun s s' =>
          ∃ v, s.prop2 = some v ∧
            s' = {
              s with
              prom := setFn s.prom i (some .b2)
              did2b2 := setFn s.did2b2 i true
            }
      }

def paxos_ref {n : Nat} (s : PaxosState n) : ConsensusState where
  chosen :=
    if majority s.did2b1 then s.prop1
    else if majority s.did2b2 then s.prop2
    else none

structure PaxosInv {n : Nat} (s : PaxosState n) : Prop where
  hA1 : ∀ i, s.did2b1 i = true → s.prop1 ≠ none
  hA2 : ∀ i, s.did2b2 i = true → s.prop2 ≠ none

def paxos_inv {n : Nat} (s : PaxosState n) : Prop := PaxosInv s

theorem no_majority_did2b1_if_prop1_none {n : Nat} (s : PaxosState n)
    (hinv : paxos_inv s) (hprop1 : s.prop1 = none) : majority s.did2b1 = false := by
  cases hm : majority s.did2b1 with
  | false => rfl
  | true =>
      exfalso
      rcases exists_true_of_majority hm with ⟨i, hi⟩
      exact (hinv.hA1 i hi) hprop1

theorem no_majority_did2b2_if_prop2_none {n : Nat} (s : PaxosState n)
    (hinv : paxos_inv s) (hprop2 : s.prop2 = none) : majority s.did2b2 = false := by
  cases hm : majority s.did2b2 with
  | false => rfl
  | true =>
      exfalso
      rcases exists_true_of_majority hm with ⟨i, hi⟩
      exact (hinv.hA2 i hi) hprop2

theorem paxos_inv_init {n : Nat} : ∀ s, (paxos n).init s → paxos_inv s := by
  intro s hinit
  rcases hinit with ⟨_, _, _, hp1, hp2, hd1, hd2⟩
  exact {
    hA1 := by intro i hi; simp [hd1 i] at hi
    hA2 := by intro i hi; simp [hd2 i] at hi
  }

theorem paxos_inv_next {n : Nat} : ∀ s s', paxos_inv s →
    (∃ a, ((paxos n).actions a).fires s s') → paxos_inv s' := by
  intro s s' hinv ⟨a, hfires⟩
  cases a with
  | p1b_1 i =>
      simp only [GatedAction.fires] at hfires
      dsimp only [paxos] at hfires
      obtain ⟨_, rfl⟩ := hfires
      exact {
        hA1 := by intro j hj; exact hinv.hA1 j hj
        hA2 := by intro j hj; exact hinv.hA2 j hj
      }
  | p1b_2 i =>
      simp only [GatedAction.fires] at hfires
      dsimp only [paxos] at hfires
      obtain ⟨_, rfl⟩ := hfires
      exact {
        hA1 := by intro j hj; exact hinv.hA1 j hj
        hA2 := by intro j hj; exact hinv.hA2 j hj
      }
  | p2a_1 =>
      simp only [GatedAction.fires] at hfires
      dsimp only [paxos] at hfires
      obtain ⟨_, _, rfl⟩ := hfires
      exact {
        hA1 := by intro _ _; simp
        hA2 := by intro j hj; exact hinv.hA2 j hj
      }
  | p2a_2 =>
      simp only [GatedAction.fires] at hfires
      dsimp only [paxos] at hfires
      obtain ⟨_, _, rfl⟩ := hfires
      exact {
        hA1 := by intro j hj; exact hinv.hA1 j hj
        hA2 := by intro _ _; simp
      }
  | p2b_1 i =>
      simp only [GatedAction.fires] at hfires
      dsimp only [paxos] at hfires
      obtain ⟨⟨_, _, _⟩, v, hp1, rfl⟩ := hfires
      exact {
        hA1 := by
          intro j hj
          by_cases hji : j = i
          · subst hji
            simp [hp1]
          · have hjold : s.did2b1 j = true := by
              simpa [setFn, hji] using hj
            exact hinv.hA1 j hjold
        hA2 := by
          intro j hj
          exact hinv.hA2 j hj
      }
  | p2b_2 i =>
      simp only [GatedAction.fires] at hfires
      dsimp only [paxos] at hfires
      obtain ⟨_, v, hp2, rfl⟩ := hfires
      exact {
        hA1 := by
          intro j hj
          exact hinv.hA1 j hj
        hA2 := by
          intro j hj
          by_cases hji : j = i
          · subst hji
            simp [hp2]
          · have hjold : s.did2b2 j = true := by
              simpa [setFn, hji] using hj
            exact hinv.hA2 j hjold
      }

theorem paxos_init_preserved {n : Nat} : ∀ s, (paxos n).init s →
    consensus.init (paxos_ref s) := by
  intro s hinit
  rcases hinit with ⟨_, _, _, _, _, hd1, hd2⟩
  have hmajFalse : majority (fun _ : Fin n => false) = false := by
    unfold majority countTrue
    apply decide_eq_false
    have h0 : (List.filter (fun _ : Fin n => false) (List.finRange n)).length = 0 := by simp
    simp [h0]
  have hdid1 : s.did2b1 = (fun _ : Fin n => false) := by
    funext i
    exact hd1 i
  have hdid2 : s.did2b2 = (fun _ : Fin n => false) := by
    funext i
    exact hd2 i
  unfold consensus ActionSpec.init paxos_ref
  simp [hdid1, hdid2, hmajFalse]

theorem paxos_step_sim {n : Nat} : ∀ s s', paxos_inv s →
    (∃ a, ((paxos n).actions a).fires s s') →
    (∃ i, (consensus.actions i).fires (paxos_ref s) (paxos_ref s')) ∨
      paxos_ref s = paxos_ref s' := by
  intro s s' hinv ⟨a, hfires⟩
  cases a with
  | p1b_1 i =>
      simp only [GatedAction.fires] at hfires
      dsimp only [paxos] at hfires
      obtain ⟨_, rfl⟩ := hfires
      right
      rfl
  | p1b_2 i =>
      simp only [GatedAction.fires] at hfires
      dsimp only [paxos] at hfires
      obtain ⟨_, rfl⟩ := hfires
      right
      rfl
  | p2a_1 =>
      simp only [GatedAction.fires] at hfires
      dsimp only [paxos] at hfires
      obtain ⟨⟨hprop1none, _⟩, _, rfl⟩ := hfires
      have hnoMaj1 : majority s.did2b1 = false :=
        no_majority_did2b1_if_prop1_none s hinv hprop1none
      right
      simp [paxos_ref, hnoMaj1]
  | p2a_2 =>
      simp only [GatedAction.fires] at hfires
      dsimp only [paxos] at hfires
      obtain ⟨⟨hprop2none, _⟩, _, rfl⟩ := hfires
      have hnoMaj2 : majority s.did2b2 = false :=
        no_majority_did2b2_if_prop2_none s hinv hprop2none
      right
      simp [paxos_ref, hnoMaj2]
  | p2b_1 i =>
      simp only [GatedAction.fires] at hfires
      dsimp only [paxos] at hfires
      obtain ⟨⟨_, _, hprop2none⟩, v, hp1, rfl⟩ := hfires
      by_cases hpre1 : majority s.did2b1 = true
      · right
        have hpost1 : majority (setFn s.did2b1 i true) = true :=
          majority_setFn_true_of_majority s.did2b1 i hpre1
        simp [paxos_ref, hpre1, hpost1]
      · have hpre1f : majority s.did2b1 = false := by
          cases h : majority s.did2b1 <;> simp_all
        by_cases hpost1 : majority (setFn s.did2b1 i true) = true
        · have hpre2 : majority s.did2b2 = false :=
            no_majority_did2b2_if_prop2_none s hinv hprop2none
          left
          cases v with
          | v1 =>
              refine ⟨.choose1, ?_⟩
              constructor <;> simp [consensus, paxos_ref, hpre1f, hpre2, hpost1, hp1]
          | v2 =>
              refine ⟨.choose2, ?_⟩
              constructor <;> simp [consensus, paxos_ref, hpre1f, hpre2, hpost1, hp1]
        · right
          have hpost1f : majority (setFn s.did2b1 i true) = false := by
            cases h : majority (setFn s.did2b1 i true) <;> simp_all
          simp [paxos_ref, hpre1f, hpost1f]
  | p2b_2 i =>
      simp only [GatedAction.fires] at hfires
      dsimp only [paxos] at hfires
      obtain ⟨_, v, hp2, rfl⟩ := hfires
      by_cases hpre1 : majority s.did2b1 = true
      · right
        simp [paxos_ref, hpre1]
      · have hpre1f : majority s.did2b1 = false := by
          cases h : majority s.did2b1 <;> simp_all
        by_cases hpre2 : majority s.did2b2 = true
        · right
          have hpost2 : majority (setFn s.did2b2 i true) = true :=
            majority_setFn_true_of_majority s.did2b2 i hpre2
          simp [paxos_ref, hpre1f, hpre2, hpost2, hp2]
        · have hpre2f : majority s.did2b2 = false := by
            cases h : majority s.did2b2 <;> simp_all
          by_cases hpost2 : majority (setFn s.did2b2 i true) = true
          · left
            cases v with
            | v1 =>
                refine ⟨.choose1, ?_⟩
                constructor <;> simp [consensus, paxos_ref, hpre1f, hpre2f, hpost2, hp2]
            | v2 =>
                refine ⟨.choose2, ?_⟩
                constructor <;> simp [consensus, paxos_ref, hpre1f, hpre2f, hpost2, hp2]
          · right
            have hpost2f : majority (setFn s.did2b2 i true) = false := by
              cases h : majority (setFn s.did2b2 i true) <;> simp_all
            simp [paxos_ref, hpre1f, hpre2f, hpost2f]

theorem paxos_refines_consensus (n : Nat) :
    refines_via paxos_ref (paxos n).toSpec.safety consensus.toSpec.safety_stutter := by
  apply refinement_mapping_stutter_with_invariant
    (paxos n).toSpec consensus.toSpec paxos_ref paxos_inv
  · exact paxos_inv_init
  · intro s s' hinv hstep
    exact paxos_inv_next s s' hinv hstep
  · exact paxos_init_preserved
  · exact paxos_step_sim

end PaxosN
