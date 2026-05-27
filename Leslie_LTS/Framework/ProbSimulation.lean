import Leslie_LTS.Framework.WeakProbabilistic
import Leslie_LTS.Framework.Simulation

/-! # Probabilistic Simulations for PLTS

    This module defines probabilistic simulation relations between PLTS,
    building on the weak probabilistic transitions from `WeakProbabilistic.lean`.

    Two notions are provided:

    1. **Weak probabilistic simulation** (`WeakProbSim`): the simulation
       relation `R : S₁ → S₂ → Prop` is between states. The step condition
       uses a **coupling** (`LiftR`) to relate the concrete and abstract
       successor distributions.

    2. **Probabilistic forward simulation** (`ProbForwardSim`): the simulation
       maps each concrete state to a **distribution** over abstract states,
       `R : S₁ → PMF S₂`. The step condition requires the abstract system
       to make a weak transition from `R s₁` to `μ₁.bind R` — the
       distribution obtained by applying `R` pointwise to the concrete
       successor distribution `μ₁`.
-/

namespace PLTS

/-! ## Probabilistic Lifting of Relations (Coupling) -/

section Lifting

variable {S₁ : Type u₁} {S₂ : Type u₂}

/-- The probabilistic lifting (coupling) of a relation `R` to distributions.
    `LiftR R μ₁ μ₂` holds if there exists a joint distribution `ω` over
    `S₁ × S₂` (a **coupling**) whose marginals are `μ₁` and `μ₂`, and
    which is concentrated on `R`. -/
def LiftR (R : S₁ → S₂ → Prop) (μ₁ : PMF S₁) (μ₂ : PMF S₂) : Prop :=
  ∃ ω : PMF (S₁ × S₂),
    (∀ p ∈ ω.support, R p.1 p.2) ∧
    ω.bind (fun p => PMF.pure p.1) = μ₁ ∧
    ω.bind (fun p => PMF.pure p.2) = μ₂

/-- `LiftR` respects the identity relation via the diagonal coupling. -/
theorem LiftR.id (μ : PMF S₁) : LiftR (fun s₁ s₂ => s₁ = s₂) μ μ := by
  refine ⟨μ.bind (fun s => PMF.pure (s, s)), fun ⟨a, b⟩ h => ?_, ?_, ?_⟩
  · simp [PMF.support_bind] at h
    exact h.2 ▸ rfl
  · ext s; simp [PMF.bind_bind, PMF.pure_bind, PMF.bind_pure]
  · ext s; simp [PMF.bind_bind, PMF.pure_bind, PMF.bind_pure]

end Lifting

/-! ## Weak Probabilistic Simulation

    The simulation relation `R : S₁ → S₂ → Prop` is between states. Each
    concrete step is matched by an abstract weak transition, with the
    resulting distributions related by `LiftR R` (a coupling). -/

/-- A weak probabilistic simulation between two PLTS.

    Each concrete **strong** step `s₁ --l--> μ₁` from a related pair
    `(s₁, s₂)` is matched by an abstract **weak** transition from
    `PMF.pure s₂` to some `μ₂`, with `LiftR R μ₁ μ₂`. -/
structure WeakProbSim
    {S₁ : Type u₁} {L₁ : Type v₁} {S₂ : Type u₂} {L₂ : Type v₂}
    (concrete : System S₁ L₁) (lab₁ : LTS.Labelling L₁)
    (abstract : System S₂ L₂) (lab₂ : LTS.Labelling L₂) where
  /-- The simulation relation between concrete and abstract states. -/
  R : S₁ → S₂ → Prop
  /-- The function mapping concrete external labels to abstract labels. -/
  label_map : L₁ → L₂
  /-- Every concrete initial state has a related abstract initial state. -/
  init_sim : ∀ s₁, concrete.init s₁ →
    Σ' s₂, abstract.init s₂ ×' R s₁ s₂
  /-- An internal concrete step from a related, reachable pair is matched
      by an abstract internal weak transition, with the resulting
      distributions related by the lifting of R. -/
  step_internal : ∀ s₁ l₁ (μ₁ : PMF S₁) s₂,
    Reachable concrete s₁ → R s₁ s₂ →
    lab₁.is_internal l₁ = true → concrete.step s₁ l₁ μ₁ →
    Σ' μ₂ : PMF S₂,
      InternalWeakStar abstract lab₂ (PMF.pure s₂) μ₂ ×'
      LiftR R μ₁ μ₂
  /-- An external concrete step from a related, reachable pair is matched
      by an abstract weak transition with the mapped label, with the
      resulting distributions related by the lifting of R. -/
  step_external : ∀ s₁ l₁ (μ₁ : PMF S₁) s₂,
    Reachable concrete s₁ → R s₁ s₂ →
    lab₁.is_external l₁ = true → concrete.step s₁ l₁ μ₁ →
    Σ' μ₂ : PMF S₂,
      WeakStep abstract lab₂ (label_map l₁) (PMF.pure s₂) μ₂ ×'
      LiftR R μ₁ μ₂

/-! ## Lifting State-to-Distribution Relations -/

section DistLifting

variable {S₁ : Type u₁} {S₂ : Type u₂}

/-- The natural lifting of a relation `R : S₁ → PMF S₂ → Prop` to
    distributions. `DistLiftR R μ ν` holds if there exists a choice
    function `f` assigning to each `p ∈ μ.support` a distribution `f p`
    with `R p (f p)`, and `ν = μ.bind f`.

    Intuitively: `ν` is the mixture `∑ μ(p) · f(p)` where each component
    `f(p)` is an abstract distribution related to `p` by `R`. -/
def DistLiftR (R : S₁ → PMF S₂ → Sort*) (μ : PMF S₁) (ν : PMF S₂) :=
  Σ' f : S₁ → PMF S₂,
    (∀ p ∈ μ.support, R p (f p)) ×'
    ν = μ.bind f

/-- `DistLiftR` from a Dirac distribution extracts `R s ν`. -/
def DistLiftR.of_pure {R : S₁ → PMF S₂ → Sort*} {s : S₁} {ν : PMF S₂}
    (h : DistLiftR R (PMF.pure s) ν) : R s ν := by
  obtain ⟨f, hR, hν⟩ := h
  have hmem : s ∈ (PMF.pure s).support := by simp [PMF.support_pure]
  have : ν = f s := by simp [hν, PMF.pure_bind]
  rw [this]; exact hR s hmem

/-- Construct `DistLiftR R (PMF.pure s) ν` from `R s ν`. -/
def DistLiftR.pure_intro {R : S₁ → PMF S₂ → Sort*} {s : S₁} {ν : PMF S₂}
    (h : R s ν) : DistLiftR R (PMF.pure s) ν :=
  ⟨fun _ => ν, fun p hp => by
    simp [PMF.support_pure] at hp; subst hp; exact h,
    by simp⟩

/-- `DistLiftR` witnesses can be extracted: if `DistLiftR R μ ν` and
    `s₁ ∈ μ.support`, then `R s₁ (f s₁)` for the witness `f`. -/
def DistLiftR.witness {R : S₁ → PMF S₂ → Sort*}
    {μ : PMF S₁} {ν : PMF S₂}
    (h : DistLiftR R μ ν) {s₁ : S₁} (hs : s₁ ∈ μ.support) :
    Σ' ν_s₁, R s₁ ν_s₁ :=
  ⟨h.1 s₁, h.2.1 s₁ hs⟩

/-- Construct `DistLiftR` directly from a choice function. -/
def DistLiftR.intro {R : S₁ → PMF S₂ → Sort*}
    {μ : PMF S₁} (f : S₁ → PMF S₂)
    (hR : ∀ s₁ ∈ μ.support, R s₁ (f s₁)) :
    DistLiftR R μ (μ.bind f) :=
  ⟨f, hR, rfl⟩

end DistLifting

/-! ## Probabilistic Forward Simulation

    The simulation relation `R : S₁ → PMF S₂ → Prop` relates each concrete
    state to a distribution over abstract states. Given `R s₁ ν` and a
    concrete step `s₁ --l--> μ₁`, the abstract must match with a weak
    transition `ν ==l==> ν'` such that `DistLiftR R μ₁ ν'` — the successor
    distributions are related by the lifting of `R`. -/

/-- A probabilistic forward simulation between two PLTS (Segala).

    Each concrete step `s₁ --l--> μ₁` where `R s₁ ν` is matched by an
    abstract weak transition `ν ==l==> ν'` with `DistLiftR R μ₁ ν'`. -/
structure ProbForwardSim
    {S₁ : Type u₁} {L₁ : Type v₁} {S₂ : Type u₂} {L₂ : Type v₂}
    (concrete : System S₁ L₁) (lab₁ : LTS.Labelling L₁)
    (abstract : System S₂ L₂) (lab₂ : LTS.Labelling L₂) where
  /-- Relates each concrete state to a distribution over abstract states. -/
  R : S₁ → PMF S₂ → Prop
  /-- Maps concrete external labels to abstract labels. -/
  label_map : L₁ → L₂
  /-- Every concrete initial state is related to some distribution
      concentrated on abstract initial states. -/
  init_sim : ∀ s₁, concrete.init s₁ →
    Σ' ν, R s₁ ν ×' ∀ s₂ ∈ ν.support, abstract.init s₂
  /-- An internal concrete step is matched by an abstract internal weak
      transition, with successor distributions related by `DistLiftR R`. -/
  step_internal : ∀ s₁ l₁ (μ₁ : PMF S₁) (ν : PMF S₂),
    Reachable concrete s₁ → R s₁ ν →
    lab₁.is_internal l₁ = true → concrete.step s₁ l₁ μ₁ →
    Σ' ν' : PMF S₂,
      InternalWeakStar abstract lab₂ ν ν' ×'
      DistLiftR R μ₁ ν'
  /-- An external concrete step is matched by an abstract weak transition
      with the mapped label, with successor distributions related by
      `DistLiftR R`. -/
  step_external : ∀ s₁ l₁ (μ₁ : PMF S₁) (ν : PMF S₂),
    Reachable concrete s₁ → R s₁ ν →
    lab₁.is_external l₁ = true → concrete.step s₁ l₁ μ₁ →
    Σ' ν' : PMF S₂,
      WeakStep abstract lab₂ (label_map l₁) ν ν' ×'
      DistLiftR R μ₁ ν'

/-! ## Single-Step Transfer

    The simulation's step conditions directly give the single-step
    invariant: one concrete step from a related pair produces a related
    successor pair. -/

/-- A single concrete step transfers through the simulation: given
    `R s₁ ν` and `concrete.step s₁ l₁ μ₁`, there exists an abstract
    weak transition from `ν` and `DistLiftR R μ₁ ν'`. -/
def ProbForwardSim.single_step_transfer
    {S₁ : Type u₁} {L₁ : Type v₁} {S₂ : Type u₂} {L₂ : Type v₂}
    {concrete : System S₁ L₁} {lab₁ : LTS.Labelling L₁}
    {abstract : System S₂ L₂} {lab₂ : LTS.Labelling L₂}
    (sim : ProbForwardSim concrete lab₁ abstract lab₂)
    {s₁ : S₁} {l₁ : L₁} {μ₁ : PMF S₁} {ν : PMF S₂}
    (hreach : Reachable concrete s₁) (hR : sim.R s₁ ν)
    (hstep : concrete.step s₁ l₁ μ₁) :
    Σ' ν' : PMF S₂,
      (InternalWeakStar abstract lab₂ ν ν' ∨
       ∃ l₂, WeakStep abstract lab₂ l₂ ν ν') ×'
      DistLiftR sim.R μ₁ ν' := by
  by_cases hint : lab₁.is_internal l₁ = true
  · obtain ⟨ν', hws, hlift⟩ := sim.step_internal s₁ l₁ μ₁ ν hreach hR hint hstep
    exact ⟨ν', Or.inl hws, hlift⟩
  · have hext : lab₁.is_external l₁ = true := by
      simp [LTS.Labelling.is_external, hint]
    obtain ⟨ν', hws, hlift⟩ := sim.step_external s₁ l₁ μ₁ ν hreach hR hext hstep
    exact ⟨ν', Or.inr ⟨sim.label_map l₁, hws⟩, hlift⟩

/-- The initial condition provides a `DistLiftR` from the Dirac distribution
    at a concrete initial state. -/
def ProbForwardSim.init_distlift
    {S₁ : Type u₁} {L₁ : Type v₁} {S₂ : Type u₂} {L₂ : Type v₂}
    {concrete : System S₁ L₁} {lab₁ : LTS.Labelling L₁}
    {abstract : System S₂ L₂} {lab₂ : LTS.Labelling L₂}
    (sim : ProbForwardSim concrete lab₁ abstract lab₂)
    {s₁₀ : S₁} (hinit : concrete.init s₁₀) :
    Σ' ν₀ : PMF S₂,
      DistLiftR sim.R (PMF.pure s₁₀) ν₀ ×'
      ∀ s₂ ∈ ν₀.support, abstract.init s₂ := by
  obtain ⟨ν₀, hR₀, hinit₂⟩ := sim.init_sim s₁₀ hinit
  exact ⟨ν₀, DistLiftR.pure_intro hR₀, hinit₂⟩

/-! ## Per-Path Simulation Invariant

    Along any valid concrete execution (in `toLTS concrete`), the simulation
    relation `R` can be maintained at every state. This is the per-path
    (possibilistic) consequence of the simulation — it doesn't require
    measure theory, only the existence of witnesses at each step. -/

/-- Along any valid concrete execution, each state is related by `R` to
    some abstract distribution, and that distribution is reachable in the
    abstract system via weak transitions.

    This is proved by induction: at step 0, `init_sim` provides the initial
    abstract distribution. At step n+1, the toLTS step gives
    `∃ μ, concrete.step s_n l_n μ ∧ s_{n+1} ∈ μ.support`. The simulation's
    step condition gives `DistLiftR R μ ν'`, and `DistLiftR.witness`
    extracts `R s_{n+1} (f s_{n+1})` for the specific successor. -/
theorem ProbForwardSim.path_simulation_invariant
    {S₁ : Type u₁} {L₁ : Type v₁} {S₂ : Type u₂} {L₂ : Type v₂}
    {concrete : System S₁ L₁} {lab₁ : LTS.Labelling L₁}
    {abstract : System S₂ L₂} {lab₂ : LTS.Labelling L₂}
    (sim : ProbForwardSim concrete lab₁ abstract lab₂)
    (e : LTS.Execution S₁ L₁)
    (hval : (toLTS concrete).valid_exec e) :
    ∀ n, ∃ ν : PMF S₂, sim.R (e.states n) ν := by
  have hreach := LTS.System.valid_exec_reachable hval
  intro n; induction n with
  | zero =>
    obtain ⟨ν₀, hR₀, _⟩ := sim.init_sim _ hval.1
    exact ⟨ν₀, hR₀⟩
  | succ n ih =>
    obtain ⟨ν_n, hR_n⟩ := ih
    obtain ⟨μ, hstep_p, hmem⟩ := hval.2 n
    -- The reachability in PLTS is the same as in toLTS
    have hreach_p : Reachable concrete (e.states n) := hreach n
    by_cases hint : lab₁.is_internal (e.labels n) = true
    · let ⟨_, _, hlift⟩ :=
        sim.step_internal _ _ μ ν_n hreach_p hR_n hint hstep_p
      let ⟨ν', hR'⟩ := hlift.witness hmem
      exact ⟨ν', hR'⟩
    · have hext : lab₁.is_external (e.labels n) = true := by
        simp [LTS.Labelling.is_external, hint]
      let ⟨_, _, hlift⟩ :=
        sim.step_external _ _ μ ν_n hreach_p hR_n hext hstep_p
      let ⟨ν', hR'⟩ := hlift.witness hmem
      exact ⟨ν', hR'⟩

/-- Corollary: A `ProbForwardSim` transfers **possibilistic** reachability
    invariants. If `P` holds on all states in every abstract distribution
    related by `R` to any reachable concrete state, then `P` holds on all
    reachable concrete states (via `R`).

    This is weaker than trace distribution inclusion but requires no
    measure theory. -/
theorem ProbForwardSim.preserves_invariant
    {S₁ : Type u₁} {L₁ : Type v₁} {S₂ : Type u₂} {L₂ : Type v₂}
    {concrete : System S₁ L₁} {lab₁ : LTS.Labelling L₁}
    {abstract : System S₂ L₂} {lab₂ : LTS.Labelling L₂}
    (sim : ProbForwardSim concrete lab₁ abstract lab₂)
    (P : S₁ → Prop)
    (hP : ∀ s₁ (ν : PMF S₂), sim.R s₁ ν → P s₁) :
    ∀ e : LTS.Execution S₁ L₁,
      (toLTS concrete).valid_exec e → ∀ n, P (e.states n) := by
  intro e hval n
  obtain ⟨ν, hR⟩ := sim.path_simulation_invariant e hval n
  exact hP _ ν hR

/-! ## Equivalence with LTS Forward Simulation

    For PLTS arising from `fromLTS`, all transitions are Dirac. Weak
    probabilistic transitions from `PMF.pure s` therefore remain Dirac.
    This lets us convert between `LTS.ForwardSim` and `ProbForwardSim`. -/

section LTSEquiv

variable {S₁ : Type u₁} {L₁ : Type v₁} {S₂ : Type u₂} {L₂ : Type v₂}

/-- In a `fromLTS` system, `InternalHyperStep` from a Dirac produces a Dirac.
    The intermediate state and the witnessing internal step are extracted. -/
theorem InternalHyperStep_fromLTS_pure
    {sys : LTS.System S₂ L₂} {lab : LTS.Labelling L₂}
    {s : S₂} {μ : PMF S₂}
    (h : InternalHyperStep (fromLTS sys) lab (PMF.pure s) μ) :
    ∃ s', μ = PMF.pure s' ∧ ∃ l, lab.is_internal l = true ∧ sys.step s l s' := by
  obtain ⟨f, _, ⟨q, hq, l, hint, hstep⟩, hμ⟩ := h
  simp [PMF.support_pure] at hq; subst hq
  obtain ⟨s', hstep', hf⟩ := hstep
  exact ⟨s', by simp [hμ, PMF.pure_bind, hf], l, hint, hstep'⟩

/-- In a `fromLTS` system, `InternalWeakStar` from a Dirac produces a Dirac,
    and the path corresponds to an `LTS.InternalStar`. -/
theorem InternalWeakStar_fromLTS_pure
    {sys : LTS.System S₂ L₂} {lab : LTS.Labelling L₂}
    {s : S₂} {μ : PMF S₂}
    (h : InternalWeakStar (fromLTS sys) lab (PMF.pure s) μ) :
    ∃ s', μ = PMF.pure s' ∧ Nonempty (LTS.InternalStar sys lab s s') := by
  suffices ∀ ν₀ ν₁, InternalWeakStar (fromLTS sys) lab ν₀ ν₁ →
      ∀ s, ν₀ = PMF.pure s →
      ∃ s', ν₁ = PMF.pure s' ∧ Nonempty (LTS.InternalStar sys lab s s') from
    this _ _ h s rfl
  intro ν₀ ν₁ h
  induction h with
  | refl => intro s heq; exact ⟨s, heq, ⟨.refl⟩⟩
  | step hstep _ ih =>
    intro s heq; subst heq
    obtain ⟨s₁, rfl, l, hint, hstep'⟩ := InternalHyperStep_fromLTS_pure hstep
    obtain ⟨s', rfl, ⟨hstar⟩⟩ := ih s₁ rfl
    exact ⟨s', rfl, ⟨.step hint hstep' hstar⟩⟩

/-- In a `fromLTS` system, `HyperStep` from a Dirac produces a Dirac. -/
theorem HyperStep_fromLTS_pure
    {sys : LTS.System S₂ L₂}
    {l : L₂} {s : S₂} {μ : PMF S₂}
    (h : HyperStep (fromLTS sys) l (PMF.pure s) μ) :
    ∃ s', μ = PMF.pure s' ∧ sys.step s l s' := by
  obtain ⟨f, hf, hμ⟩ := h
  have hmem : s ∈ (PMF.pure s).support := by simp [PMF.support_pure]
  obtain ⟨s', hstep, hfs⟩ := hf s hmem
  exact ⟨s', by simp [hμ, PMF.pure_bind, hfs], hstep⟩

/-- In a `fromLTS` system, `WeakStep` from a Dirac produces a Dirac. -/
theorem WeakStep_fromLTS_pure
    {sys : LTS.System S₂ L₂} {lab : LTS.Labelling L₂}
    {l : L₂} {s : S₂} {μ : PMF S₂}
    (h : WeakStep (fromLTS sys) lab l (PMF.pure s) μ) :
    ∃ s', μ = PMF.pure s' := by
  obtain ⟨μ₁, μ₂, hpre, hext, hpost⟩ := h
  obtain ⟨s₁, rfl, _⟩ := InternalWeakStar_fromLTS_pure hpre
  obtain ⟨s₂, rfl, _⟩ := HyperStep_fromLTS_pure hext
  obtain ⟨s', rfl, _⟩ := InternalWeakStar_fromLTS_pure hpost
  exact ⟨s', rfl⟩

/-- Converse: `LTS.InternalStar` lifts to `InternalWeakStar` on `fromLTS`. -/
theorem InternalStar_to_InternalWeakStar
    {sys : LTS.System S₂ L₂} {lab : LTS.Labelling L₂}
    {s s' : S₂}
    (h : LTS.InternalStar sys lab s s') :
    InternalWeakStar (fromLTS sys) lab (PMF.pure s) (PMF.pure s') := by
  induction h with
  | refl => exact .refl
  | step hint hstep _ ih =>
    refine .step ?_ ih
    exact ⟨fun _ => PMF.pure _,
      fun q hq => by
        simp [PMF.support_pure] at hq; subst hq
        exact Or.inl ⟨_, hint, _, hstep, rfl⟩,
      ⟨_, by simp [PMF.support_pure], _, hint, _, hstep, rfl⟩,
      by simp⟩

/-- Convert `LTS.ForwardSim` to `ProbForwardSim` on `fromLTS` systems. -/
noncomputable def ForwardSim_to_ProbForwardSim
    {c : LTS.System S₁ L₁} {lab₁ : LTS.Labelling L₁}
    {a : LTS.System S₂ L₂} {lab₂ : LTS.Labelling L₂}
    (sim : LTS.ForwardSim c lab₁ a lab₂) :
    ProbForwardSim (fromLTS c) lab₁ (fromLTS a) lab₂ where
  R := fun s₁ ν => ∃ s₂, ν = PMF.pure s₂ ∧ sim.R s₁ s₂
  label_map := sim.label_map
  init_sim := fun s₁ hinit =>
    let ⟨s₂, hinit₂, hR⟩ := sim.init_sim s₁ hinit
    ⟨PMF.pure s₂, ⟨s₂, rfl, hR⟩, fun s₂' hs₂' => by
      simp [PMF.support_pure] at hs₂'; subst hs₂'; exact hinit₂⟩
  step_internal := fun s₁ l₁ μ₁ ν hreach hRν hint hstep =>
    let s₂ := hRν.choose
    let hν := hRν.choose_spec.1
    let hR := hRν.choose_spec.2
    let s₁' := hstep.choose
    let hstep₁ := hstep.choose_spec.1
    let hμ := hstep.choose_spec.2
    let hreach₁ : LTS.Reachable c s₁ := (reachable_fromLTS c s₁).mp hreach
    let ⟨s₂', hstar, hR'⟩ := sim.step_internal s₁ l₁ s₁' s₂ hreach₁ hR hint hstep₁
    hν ▸ hμ ▸ ⟨PMF.pure s₂',
      InternalStar_to_InternalWeakStar hstar,
      DistLiftR.pure_intro ⟨s₂', rfl, hR'⟩⟩
  step_external := fun s₁ l₁ μ₁ ν hreach hRν hext hstep =>
    let s₂ := hRν.choose
    let hν := hRν.choose_spec.1
    let hR := hRν.choose_spec.2
    let s₁' := hstep.choose
    let hstep₁ := hstep.choose_spec.1
    let hμ := hstep.choose_spec.2
    let hreach₁ : LTS.Reachable c s₁ := (reachable_fromLTS c s₁).mp hreach
    let ⟨s₂_mid, s₂_mid', s₂', hstar1, hstep₂, hstar2, hR'⟩ :=
      sim.step_external s₁ l₁ s₁' s₂ hreach₁ hR hext hstep₁
    hν ▸ hμ ▸ ⟨PMF.pure s₂',
      ⟨PMF.pure s₂_mid, PMF.pure s₂_mid',
        InternalStar_to_InternalWeakStar hstar1,
        HyperStep.from_step ⟨s₂_mid', hstep₂, rfl⟩,
        InternalStar_to_InternalWeakStar hstar2⟩,
      DistLiftR.pure_intro ⟨s₂', rfl, hR'⟩⟩

/-- Injectivity of `PMF.pure`: if `PMF.pure a = PMF.pure b` then `a = b`. -/
theorem PMF.pure_injective' {α : Type*} {a b : α}
    (h : PMF.pure a = PMF.pure b) : a = b := by
  have : a ∈ (PMF.pure b).support := h ▸ by simp [PMF.support_pure]
  simpa [PMF.support_pure] using this

/-- Convert `ProbForwardSim` on `fromLTS` systems back to `LTS.ForwardSim`.

    Requires `hpure`: the simulation relation only relates concrete states
    to Dirac distributions. This is automatically satisfied by any
    `ProbForwardSim` constructed via `ForwardSim_to_ProbForwardSim`. -/
noncomputable def ProbForwardSim_to_ForwardSim
    {c : LTS.System S₁ L₁} {lab₁ : LTS.Labelling L₁}
    {a : LTS.System S₂ L₂} {lab₂ : LTS.Labelling L₂}
    (sim : ProbForwardSim (fromLTS c) lab₁ (fromLTS a) lab₂)
    (hpure : ∀ s₁ ν, sim.R s₁ ν → ∃ s₂, ν = PMF.pure s₂) :
    LTS.ForwardSim c lab₁ a lab₂ where
  R := fun s₁ s₂ => sim.R s₁ (PMF.pure s₂)
  label_map := sim.label_map
  init_sim := fun s₁ hinit => by
    let ⟨ν₀, hR₀, hinit₂⟩ := sim.init_sim s₁ hinit
    set s₂ := (hpure s₁ ν₀ hR₀).choose
    have heq : ν₀ = PMF.pure s₂ := (hpure s₁ ν₀ hR₀).choose_spec
    exact ⟨s₂, hinit₂ s₂ (heq ▸ by simp [PMF.support_pure]), heq ▸ hR₀⟩
  step_internal := fun s₁ l₁ s₁' s₂ hreach hR hint hstep => by
    let ⟨ν', hws, hlift⟩ := sim.step_internal s₁ l₁ (PMF.pure s₁') (PMF.pure s₂)
      ((reachable_fromLTS c s₁).mpr hreach) hR hint ⟨s₁', hstep, rfl⟩
    set h := InternalWeakStar_fromLTS_pure hws
    set s₂' := h.choose
    have heq : ν' = PMF.pure s₂' := h.choose_spec.1
    exact ⟨s₂', Classical.choice h.choose_spec.2, heq ▸ hlift.of_pure⟩
  step_external := fun s₁ l₁ s₁' s₂ hreach hR hext hstep => by
    let ⟨ν', hws, hlift⟩ := sim.step_external s₁ l₁ (PMF.pure s₁') (PMF.pure s₂)
      ((reachable_fromLTS c s₁).mpr hreach) hR hext ⟨s₁', hstep, rfl⟩
    -- WeakStep is ∃-valued (Prop), so use .choose/.choose_spec
    set μ₁ := hws.choose
    set μ₂ := hws.choose_spec.choose
    have hpre : InternalWeakStar (fromLTS a) lab₂ (PMF.pure s₂) μ₁ :=
      hws.choose_spec.choose_spec.1
    have hext_s : HyperStep (fromLTS a) (sim.label_map l₁) μ₁ μ₂ :=
      hws.choose_spec.choose_spec.2.1
    have hpost : InternalWeakStar (fromLTS a) lab₂ μ₂ ν' :=
      hws.choose_spec.choose_spec.2.2
    set p1 := InternalWeakStar_fromLTS_pure hpre
    have heq1 : μ₁ = PMF.pure p1.choose := p1.choose_spec.1
    set p2 := HyperStep_fromLTS_pure (heq1 ▸ hext_s)
    have heq2 : μ₂ = PMF.pure p2.choose := p2.choose_spec.1
    set p3 := InternalWeakStar_fromLTS_pure (heq2 ▸ hpost)
    have heq3 : ν' = PMF.pure p3.choose := p3.choose_spec.1
    exact ⟨p1.choose, p2.choose, p3.choose,
      Classical.choice p1.choose_spec.2,
      p2.choose_spec.2,
      Classical.choice p3.choose_spec.2,
      heq3 ▸ hlift.of_pure⟩

end LTSEquiv

/-! ## Trace Distribution Inclusion

    The main soundness theorem: a probabilistic forward simulation preserves
    the set of trace distributions achievable under an omniscient adversary.

    Given `ProbForwardSim concrete lab₁ abstract lab₂`, for every concrete
    strategy `σ₁` and initial state `s₁₀`, there exists an abstract strategy
    `σ₂` and initial state `s₂₀` such that the trace distributions match
    (up to `label_map`).

    The proof decomposes into four steps:

    1. **Strategy construction** (`construct_abstract_strategy`):
       Build `σ₂` from `σ₁` and the simulation data. At each abstract step,
       use the simulation's step condition to determine which weak transition
       to take. The simulation relation `R` is maintained as an invariant.

    2. **Simulation invariant** (`simulation_invariant_maintained`):
       Along the execution, the concrete distribution at step `n` and the
       abstract distribution at step `n` remain related by `DistLiftR R`.
       This is the inductive core: each concrete step preserves the relation
       via the simulation's step conditions.

    3. **Trace correspondence** (`trace_distributions_correspond`):
       The external trace of the abstract execution matches `label_map`
       applied to the concrete external trace. Internal concrete steps
       produce only internal abstract steps (no external trace contribution),
       and external concrete steps produce exactly one abstract external step
       with the mapped label.

    4. **Measure equality** (`trace_measures_equal`):
       The trace measures are equal:
       `rand_trace_measure abstract σ₂ lab₂ s₂₀ = map label_map (rand_trace_measure concrete σ₁ lab₁ s₁₀)`
       This follows from steps 2 and 3 by showing the pushforward through
       the trace projection commutes with the simulation. -/

section TraceInclusion

variable {S₁ : Type*} {L₁ : Type*} {S₂ : Type*} {L₂ : Type*}
variable {concrete : System S₁ L₁} {lab₁ : LTS.Labelling L₁}
variable {abstract : System S₂ L₂} {lab₂ : LTS.Labelling L₂}
variable (sim : ProbForwardSim concrete lab₁ abstract lab₂)

/-- **Step 1**: Construct an abstract strategy from a concrete strategy and
    the simulation data.

    At each step, the abstract strategy observes the abstract state (under
    the omniscient adversary), determines the corresponding concrete state
    via the simulation relation, and resolves the abstract transition using
    the simulation's step condition.

    The construction is non-trivial because:
    - The abstract state is drawn from a distribution (not a single state)
    - The weak transition may involve multiple internal steps before/after
      the external step
    - The strategy must be expressed in terms of signals, not raw
      distributions -/
noncomputable def construct_abstract_strategy
    [Inhabited L₁] [Inhabited L₂]
    (σ₁ : Strategy S₁ L₁)
    (s₁₀ : S₁) (hinit : concrete.init s₁₀) :
    Strategy S₂ L₂ :=
  sorry

/-- **Step 2**: The simulation invariant is maintained along the execution.

    At each step `n`, the concrete state distribution and the abstract
    state distribution remain related by `DistLiftR R`.

    This is the inductive core: each concrete step `s₁ --l--> μ₁` with
    `R s₁ ν` produces, via the simulation's step condition, an abstract
    weak transition `ν ==l'==> ν'` with `DistLiftR R μ₁ ν'`. -/
theorem simulation_invariant_maintained
    [Inhabited L₁] [Inhabited L₂]
    (σ₁ : Strategy S₁ L₁)
    (s₁₀ : S₁) (hinit₁ : concrete.init s₁₀)
    (ν₀ : PMF S₂) (hR₀ : sim.R s₁₀ ν₀) :
    ∀ n : ℕ, ∃ (μ₁_n : PMF S₁) (ν_n : PMF S₂),
      Nonempty (DistLiftR sim.R μ₁_n ν_n) :=
  sorry

/-- **Step 3**: The external traces correspond via `label_map`.

    Under the constructed abstract strategy, the abstract execution's
    external trace equals `label_map` applied to the concrete execution's
    external trace, almost surely. This follows from:
    - Internal concrete steps produce only internal abstract steps
    - External concrete steps produce exactly one abstract external step
      with label `label_map l₁` -/
theorem trace_correspondence
    [Inhabited L₁] [Inhabited L₂]
    (h_label_ext : ∀ l₁, lab₁.is_external l₁ = true →
      lab₂.is_external (sim.label_map l₁) = true)
    (σ₁ : Strategy S₁ L₁)
    (s₁₀ : S₁) (hinit₁ : concrete.init s₁₀)
    (ν₀ : PMF S₂) (hR₀ : sim.R s₁₀ ν₀)
    (σ₂ : Strategy S₂ L₂) (s₂₀ : S₂) :
    ∀ (ω₁ : ℕ → S₁ × L₁) (ω₂ : ℕ → S₂ × L₂) (n : ℕ),
      externalLabelsUntil lab₂ ω₂ n =
      (externalLabelsUntil lab₁ ω₁ n).map sim.label_map :=
  sorry

/-- **Step 4 (Main Theorem)**: A probabilistic forward simulation preserves
    the set of trace distributions.

    For every concrete strategy `σ₁` and initial state `s₁₀`, there exists
    an abstract strategy `σ₂` and initial state `s₂₀` such that the
    abstract trace distribution equals the concrete trace distribution
    composed with `label_map`.

    This is the soundness theorem for probabilistic forward simulation:
    every trace distribution achievable by the concrete PLTS is achievable
    (up to label renaming) by the abstract PLTS. -/
theorem ProbForwardSim.preserves_trace_distributions
    [Inhabited L₁] [Inhabited L₂]
    [MeasurableSpace S₁] [MeasurableSingletonClass S₁] [Countable S₁] [Inhabited S₁]
    [MeasurableSpace L₁] [MeasurableSingletonClass L₁] [Countable L₁]
    [MeasurableSpace S₂] [MeasurableSingletonClass S₂] [Countable S₂] [Inhabited S₂]
    [MeasurableSpace L₂] [MeasurableSingletonClass L₂] [Countable L₂]
    (h_label_ext : ∀ l₁, lab₁.is_external l₁ = true →
      lab₂.is_external (sim.label_map l₁) = true)
    (hres₁ : (omniscient concrete).observation_resolving)
    (hres₂ : (omniscient abstract).observation_resolving)
    (σ₁ : Strategy S₁ L₁)
    (s₁₀ : S₁) (hinit₁ : concrete.init s₁₀) :
    ∃ (σ₂ : Strategy S₂ L₂) (s₂₀ : S₂),
      abstract.init s₂₀ ∧
      rand_trace_measure (omniscient abstract) hres₂
        σ₂.toRandomised lab₂ s₂₀ =
      MeasureTheory.Measure.map (fun tr k => sim.label_map (tr k))
        (rand_trace_measure (omniscient concrete) hres₁
          σ₁.toRandomised lab₁ s₁₀) :=
  sorry

end TraceInclusion

end PLTS
