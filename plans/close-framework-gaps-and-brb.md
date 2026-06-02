# Closing framework gaps + BRB liveness — multi-session plan

## Current state (last updated 2026-06-02)

**Phases A, B, C, F are DONE.** The framework (`Leslie_LTS/Framework/`)
is fully sorry-free.  `preserves_fair_weak_divergence` and
`transfers_satisfaction` are both proven.  All that remains is **Phase D
— BRB protocol-design closure** in `Leslie_LTS/Examples/BRB_Liveness.lean`.

Run `grep -n sorry Leslie_LTS/Examples/BRB_Liveness.lean` to see the
exact current sorries.  See also the dependency graph and attack order
in the module header of that file.

**DO NOT re-do Phases A–C.** They are complete.  The descriptions below
are preserved as historical context for the design decisions.

## Design decisions (historical — for understanding, not re-doing)

### Gap 1 — Case (ii.b.X) of the fair-divergence soundness proof

At
[`Simulation.lean:1770`](Leslie_LTS/Framework/Simulation.lean#L1770).
When the abstract response at some later fair index `k_j > k₀` is empty
or non-AllFair, rank decreases at `k_j` — but the witness API gives no
rank info at the *intermediate* fair-non-empty-AllFair steps in `[k₀,
k_j)`, so the rank chain back to `s₁` is broken.

Gaspard's actual recommendation (re-confirmed from the paper §6.4 plus
the user's intuition): **rank must be monotone non-increasing across
every internal concrete step**, not just unfair ones. Specifically — and
this is the missing clause — when the abstract responds to a fair
internal concrete step with a non-empty `AllFair` `InternalStar`
("lockstep fair progress"), rank stays equal or decreases. With this
clause, the prefix bridge from `s₁` to `e₁.states (k_j+1)` is intact.

### Gap 2 — `transfers_satisfaction`

At
[`Simulation.lean:1985`](Leslie_LTS/Framework/Simulation.lean#L1985).
The proof needs to build an abstract execution `e₂` from a concrete `e₁`
via `external_subseq_correspondence`, but that yields only
`valid_exec_stutter` (τ-stutters appear at boundaries where the abstract
elides a concrete internal move). The two hypotheses `h_abs` and
`h_prop_transfer` are currently typed over `valid_exec`, blocking the
chain.

**Fix (Option A):** introduce `System.satisfies_stutter sys lab φ := ∀
e, sys.valid_exec_stutter lab e → φ e 0`, re-type both hypotheses to
use stutter-tolerant variants, and provide the proof. The conclusion
`concrete.satisfies (…)` is unchanged — only the abstract-side
quantification is relaxed. For the property classes the framework
actually proves (state-based safety/liveness, observation-based
secrecy, branching), `satisfies_stutter` and `satisfies` coincide
modulo a wrapper — no real cost.

## Implementation

### Phase A — Gap 1: 5th witness clause + close (X) — ✅ DONE

#### A.1 Add the 5th field to `WeakDivPreserving`

In the `ForwardSim.WeakDivPreserving` structure
([`Simulation.lean` ~1330](Leslie_LTS/Framework/Simulation.lean#L1330)),
append:

```lean
/-- Lockstep fair progress: when the abstract responds to a fair
    internal concrete step with a non-empty `AllFair` `InternalStar`,
    rank does NOT increase.  This is the missing clause that makes rank
    monotone non-increasing across every internal step — combined with
    `rank_non_increasing` (unfair), `rank_decreases_on_fair_elision`
    (fair empty, strict), and `rank_decreases_on_unfair_abstract`
    (fair non-empty non-AllFair, strict), every internal step is
    classified.  Without this clause, Case (ii.b.X) cannot bridge rank
    through the prefix. -/
rank_non_increasing_on_fair_progress :
  ∀ s₁ l₁ s₁' s₂
    (hreach : Reachable concrete s₁)
    (hR : sim.R s₁ s₂)
    (hint : lab₁.is_internal l₁ = true)
    (hfair : fair_labels₁ s₁ l₁)
    (hstep : concrete.step s₁ l₁ s₁'),
    ¬ (sim.step_internal s₁ l₁ s₁' s₂ hreach hR hint hstep).2.1.IsEmpty →
      (sim.step_internal s₁ l₁ s₁' s₂ hreach hR hint hstep).2.1.AllFair
        fair_labels₂ →
      s₁' = s₁ ∨ rank s₁' s₁
```

Commit: `feat: add rank_non_increasing_on_fair_progress to WeakDivPreserving`.

#### A.2 Discharge in `compose_with_compatible`

In [`Composition.lean`](Leslie_LTS/Framework/Composition.lean), the
parallel composition witness needs the new clause. Pattern: one of the
component `InternalStar`s is `.refl` (the elided component) and the
other is the composed non-empty AllFair; the latter's component witness
provides the answer via its own `rank_non_increasing_on_fair_progress`,
and the elided component contributes `s' = s` so the lex pair satisfies
the disjunction. Mirrors the existing `rank_decreases_on_unfair_abstract`
proof in the same file.

Commit: `feat: discharge rank_non_increasing_on_fair_progress for compose_with_compatible`.

#### A.3 Add sorried discharges for BRB and BCA

In [`BRB_Liveness.lean`](Leslie_LTS/Examples/BRB_Liveness.lean) and
[`BCA_Liveness.lean`](Leslie_LTS/Examples/BCA_Liveness.lean),
add `rank_non_increasing_on_fair_progress := by sorry` to the
respective `brb_weak_div_witness` / `bca_weak_div_witness`. These are
protocol-specific obligations tied to the (already deferred)
`*_progress_measure` design and live alongside the existing sorried
witness fields.

Commit: `feat: add (sorried) rank_non_increasing_on_fair_progress for BRB/BCA witnesses`.

#### A.4 Generalise the prefix bridge

In Case A of `preserves_fair_weak_divergence`
([`Simulation.lean` ~1520-1660](Leslie_LTS/Framework/Simulation.lean#L1520)),
extend the existing `bridge_from_hrank_k0` helper so that at each step `i`
in the prefix, it picks the right clause:

* unfair step → `rank_non_increasing` (existing)
* fair step with empty abstract → `rank_decreases_on_fair_elision` (strict, existing)
* fair step with non-empty AllFair abstract → **new clause**
* fair step with non-empty non-AllFair abstract → `rank_decreases_on_unfair_abstract` (strict, existing)

In all four cases the conclusion has shape `s' = s ∨ rank s' s`, so the
existing case-split on "all equalities" vs "some strict decrease"
generalises directly — just one more conditional to feed the right
clause. Rename to `bridge_from_hrank_at` (parameterised by the index
where the strict decrease happens) so both (i)/(ii.a)/(ii.b.X) call
sites share it.

Commit: `feat: generalise bridge_from_hrank to handle fair-non-empty-AllFair prefix steps`.

#### A.5 Close Case (ii.b.X)

Replace the sorry at
[`Simulation.lean:1770`](Leslie_LTS/Framework/Simulation.lean#L1770):
take the LEAST bad index `i_j` (`Nat.find` on `h_break`), derive
`hrank_at_kj : wd.rank (e₁.states (k₀+i_j+1)) (e₁.states (k₀+i_j))` via
`rank_decreases_on_fair_elision` or `rank_decreases_on_unfair_abstract`
depending on the disjunct of `h_break`, then call the generalised
`bridge_from_hrank_at (k₀+i_j) hrank_at_kj`.

Drop the "OBSTRUCTION / design-level resolutions" comment block.

Commit: `feat: close Case (ii.b.X) of preserves_fair_weak_divergence`.

### Phase B — Gap 2: `satisfies_stutter` + close `transfers_satisfaction` — ✅ DONE

#### B.1 Add `System.satisfies_stutter` definition

In [`LTL.lean`](Leslie_LTS/Framework/LTL.lean), next to the existing
`System.satisfies` (around line 150):

```lean
/-- A system satisfies φ in the stutter-tolerant sense iff every
    stutter-allowing execution satisfies φ.  Used for abstract-side
    obligations in the `WeakDivPreserving` soundness chain, where the
    abstract execution constructed by `external_subseq_correspondence`
    is only `valid_exec_stutter`.

    Strictly stronger than `satisfies`: every `valid_exec` is also a
    `valid_exec_stutter`, so `satisfies_stutter → satisfies`.  For the
    property classes proven in this codebase (state-based safety /
    liveness, externalSubseq-based secrecy, branching), the two
    coincide modulo a wrapper. -/
def System.satisfies_stutter (sys : System State Label)
    (lab : Labelling Label)
    (φ : TraceProp State Label) : Prop :=
  ∀ e, sys.valid_exec_stutter lab e → φ e 0
```

Commit: `feat: add System.satisfies_stutter for abstract-side stutter-tolerant obligations`.

#### B.2 Re-type `transfers_satisfaction` and prove it

At [`Simulation.lean:1936`](Leslie_LTS/Framework/Simulation.lean#L1936):

```lean
theorem transfers_satisfaction
    {sim : ForwardSim concrete lab₁ abstract lab₂}
    (wd : sim.WeakDivPreserving fair_labels₁ fair_labels₂)
    (h_fair_compat :
      ∀ s₁ l₁ s₂, sim.R s₁ s₂ → fair_labels₁ s₁ l₁ →
        fair_labels₂ s₂ (sim.label_map l₁))
    (φ_abs : TraceProp S₂ L₂) (φ_con : TraceProp S₁ L₁)
    (h_prop_transfer :
      ∀ (e₁ : Execution S₁ L₁) (e₂ : Execution S₂ L₂) (idx : Nat → Nat),
        concrete.valid_exec e₁ →
        abstract.valid_exec_stutter lab₂ e₂ →    -- relaxed
        (∀ k, idx k < idx (k + 1)) →
        idx 0 = 0 →
        (∀ k, sim.R (e₁.states k) (e₂.states (idx k))) →
        φ_abs e₂ 0 → φ_con e₁ 0)
    (h_abs :
      abstract.satisfies_stutter lab₂                  -- relaxed
        (assumes_fair_wf abstract fair_labels₂ φ_abs)) :
    concrete.satisfies (assumes_fair_wf concrete fair_labels₁ φ_con) := by
```

Proof shape:
1. Unfold the conclusion: take concrete `e₁` valid; assume the fair-WF
   antecedent on e₁; need `φ_con e₁ 0`.
2. Build abstract `e₂` and the index map `idx` via
   `sim.external_subseq_correspondence`
   ([`Simulation.lean:920`](Leslie_LTS/Framework/Simulation.lean#L920)) —
   gives `abstract.valid_exec_stutter lab₂ e₂` and `∀ k, sim.R (e₁.states k)
   (e₂.states (idx k))`.
3. Show `e₂` satisfies the abstract fair-WF antecedent. This uses
   `h_fair_compat` to translate concrete-fair labels through `label_map`
   and `preserves_fair_weak_divergence` (now fully closed by Phase A) to
   argue away abstract fair-weak-divergence.
4. Apply `h_abs` (now stutter-typed) to get `φ_abs e₂ 0`.
5. Apply `h_prop_transfer` (now stutter-typed) to get `φ_con e₁ 0`.

Step 3 is the substantive new work in this commit — the rest is
plumbing. The argument follows the structure already sketched in the
existing `preserves_external_trace_prop`
([`Simulation.lean:1240`](Leslie_LTS/Framework/Simulation.lean#L1240)),
just adapted for the fair-WF antecedent shape.

Commit: `feat: prove transfers_satisfaction via satisfies_stutter relaxation`.

#### B.3 Update the docstring blockers in BRB/BCA totality theorems

In `BRB_Liveness.lean` and `BCA_Liveness.lean`, the totality / decision
theorems (`brb_totality`, `bca_decision`) are sorried with comments
referencing the `transfers_satisfaction` blocker. Update those comments
to reference the now-discharged transfer + the still-deferred
`ideal_brb_totality` / `ideal_bca_decision` (which remain pure
LTL-chaining work on the ideal side).

This is documentation-only; no code change. Folded into the prior commit
or its own small commit.

## Files

| Path | Phase | Change |
|---|---|---|
| `Leslie_LTS/Framework/Simulation.lean` | A.1, A.4, A.5, B.2 | 5th field; generalised bridge; close (X); re-type and prove transfers_satisfaction |
| `Leslie_LTS/Framework/Composition.lean` | A.2 | Discharge 5th field in `compose_with_compatible` |
| `Leslie_LTS/Examples/BRB_Liveness.lean` | A.3, B.3 | Sorried discharge of 5th field; update totality comment |
| `Leslie_LTS/Examples/BCA_Liveness.lean` | A.3, B.3 | Sorried discharge of 5th field; update decision comment |
| `Leslie_LTS/Framework/LTL.lean` | B.1 | Add `System.satisfies_stutter` |

## Verification

1. `make LTS` after every commit; build green at every step.
2. After Phase A, `grep -n "sorry" Leslie_LTS/Framework/Simulation.lean`
   should show **only** the transfers_satisfaction sorry as a real
   sorry (the 1471-area mention is a docstring comment).
3. After Phase B, `grep -n "sorry" Leslie_LTS/Framework/Simulation.lean`
   should show **no real sorries**. Framework is sorry-free.
4. `grep -n "sorry" Leslie_LTS/Examples/BRB_Liveness.lean
   Leslie_LTS/Examples/BCA_Liveness.lean` will show the existing
   protocol-design sorries PLUS one new sorry per file for the 5th
   witness field discharge — these are tied to the deferred
   `*_progress_measure` design work, not introduced as fresh
   debt.
5. Spot-check no `decide` / `admit` / `axiom` introduced anywhere.

### Phase C — Fair-deadlock discharge correctness — ✅ DONE

Currently, `brb_weak_div_witness.fair_deadlock_diverges` and
`bca_weak_div_witness.fair_deadlock_diverges` are discharged by
`exfalso` on `brb_no_fair_deadlock_reachable` /
`bca_no_fair_deadlock_reachable` — i.e., by claiming that no reachable
state is ever a fair-deadlock. **This is false as stated**: a
terminated reachable state (all correct procs have output, no more
messages to deliver, only `corrupt` / `input` adversarial moves
enabled) is a fair-deadlock per `FairDeadlock`'s definition
(vacuously "every enabled label is unfair" — `corrupt` and `input` ARE
unfair).

The correct discharge: at any concrete fair-deadlock state `s₁` related
to abstract state `s₂` via `sim.R`, show that `s₂` is also a fair-
deadlock (or reaches one via an internal star). Then
`FairlyWeaklyDiverges` holds at `s₂` via the **second disjunct**
(`(∃ s', InternalStar to s' ∧ FairDeadlock at s')`) with the
`InternalStar` being `.refl`.

#### C.1 Helper: lift FairDeadlock through `sim.R`

In [`Simulation.lean`](Leslie_LTS/Framework/Simulation.lean), add a
framework-level helper:

```lean
/-- If a concrete state is a fair-deadlock and `sim.R s₁ s₂`, then `s₂`
    is a fair-deadlock on the abstract under a sufficient "no abstract
    progress" condition (no enabled abstract step at s₂ is fair).  Used
    to honestly discharge `fair_deadlock_diverges` for protocol witnesses
    at terminated states. -/
theorem ForwardSim.fair_deadlock_lifts
    (sim : ForwardSim concrete lab₁ abstract lab₂)
    (h_compat : ∀ s₁ l₁ s₂, sim.R s₁ s₂ → fair_labels₁ s₁ l₁ →
        fair_labels₂ s₂ (sim.label_map l₁))
    ... : ...
```

Exact statement depends on how cleanly the protocol's `sim_rel` encodes
"abstract is also terminated when concrete is". May require additional
protocol-specific hypotheses; flag if so.

#### C.2 Rewrite `brb_weak_div_witness.fair_deadlock_diverges`

Replace the `exfalso` with the proper `Or.inr ⟨s₂, ⟨.refl⟩, abstract-side
fair-deadlock proof⟩` construction. Same for BCA.

#### C.3 Either prove or weaken `*_no_fair_deadlock_reachable`

The `*_no_fair_deadlock_reachable` theorems as stated are false. Two options:
- **Weaken** to "no reachable state is fair-deadlock UNLESS it's terminated"
  — keep them as a useful invariant for non-terminated states.
- **Replace** with the more useful pair: "any reachable fair-deadlock is
  terminated" + "terminated reachable concrete state maps to a
  terminated abstract state". This is what the rewritten discharge
  actually needs.

Commits (one each):
- `fix: replace exfalso discharge of fair_deadlock_diverges with proper lift`
- `feat: add ForwardSim.fair_deadlock_lifts helper`
- `refactor: restate *_no_fair_deadlock_reachable per terminated-states reality`

### Phase D — BRB protocol-design closure — ⏳ IN PROGRESS (this is the remaining work)

Replace the placeholder `brb_progress_measure` with a real lex measure;
discharge the four `WeakDivPreserving` obligations (including the new
5th); prove no-fair-deadlock-or-terminated; prove `ideal_brb_totality`
via LTL leads-to chaining; lift to `brb_totality` via
`transfers_satisfaction` (closed by Phase B).

**Prior progress (2026-06-02):**
- `ideal_brb_totality`: **FULLY PROVEN** (zero sorries).
- `ideal_brb_totality_stutter`: **FULLY PROVEN** (zero sorries) — uses
  the new `assumes_fair_wf_step` variant for honest stutter-exec
  discharge. See `Leslie_LTS/issues.md` for the design decision.
- `brb_totality`: skeleton wired through `transfers_satisfaction` with
  3 inner sorries (h_prop_transfer, h_ante_transfer, now uses
  ideal_brb_totality_stutter for h_abs — no more sorry there).
- `brb_progress_measure` defined (placeholder 0).
- `brb_rank_wf` proven (trivially for placeholder).
- `brb_fair_compat` proven.
- Stutter-aware persistence lemmas for IdealBRB: broadcastVal, set_up,
  returned, corrupted.

**7 sorries remain** in BRB_Liveness.lean:
- brb_fair_deadlock_implies_terminated (line 164)
- rank_non_increasing (line 233) — tied to placeholder measure
- rank_decreases_on_fair_elision (line 239) — tied to placeholder measure
- rank_non_increasing_on_fair_progress (line 254) — tied to placeholder
- h_fair_reverse in fair_deadlock_diverges (line 272)
- h_prop_transfer in brb_totality (line 760) — needs Q-monotonicity +
  idx-unboundedness or a direct approach
- h_ante_transfer in brb_totality (line 764) — needs fair-WF antecedent
  lift from concrete to abstract

#### D.1 Design `brb_progress_measure`

Lex measure candidate, in priority order:

1. Number of correct procs without `returned`.
2. Number of correct procs whose `voted` is unset but whose vote
   condition is satisfied (echo or vote threshold crossed).
3. Number of correct procs whose `echoed` is unset but whose `sendRecv`
   is some.
4. Number of pending fair messages in the buffer (sent by correct to
   correct, not yet recv'd).

Decreases on every fair correct-process step (output drops 1;
vote-send drops 2; echo-send drops 3; recv drops 4).

Commit: `feat: define brb_progress_measure as lex over protocol phases`.

#### D.2 Prove `brb_rank_wf`

Follows from lex-of-Nat WF.

Commit: `feat: prove brb_rank_wf`.

#### D.3 Discharge the four `WeakDivPreserving` obligations

- `rank_non_increasing` (unfair internal steps)
- `rank_decreases_on_fair_elision` (helpful fair steps)
- `rank_decreases_on_unfair_abstract` (we already proved this vacuously — keep)
- `rank_non_increasing_on_fair_progress` (NEW from Phase A)

Each proof case-splits on the BRB label structure. Estimated 200-400 LOC
per obligation. May reveal that the measure needs adjustment.

Commits (one per field):
- `feat: prove brb rank_non_increasing`
- `feat: prove brb rank_decreases_on_fair_elision`
- `feat: prove brb rank_non_increasing_on_fair_progress`

#### D.4 Prove the corrected no-fair-deadlock-or-terminated

Per Phase C.3 restatement.

Commit: `feat: prove brb_no_unterminated_fair_deadlock_reachable`.

#### D.5 Prove `ideal_brb_totality`

Pure LTL leads-to chaining on `IdealBRB`:
- Fair `commit` eventually fires (when enabled at fair states).
- After commit, `output p _` is enabled for each correct `p` not yet output.
- Fair scheduling of `output` makes it fire.
- Hence every correct proc eventually has `returned`.

Estimated 300-500 LOC. Substantial liveness proof.

Commit: `feat: prove ideal_brb_totality via leads-to chaining`.

#### D.6 Lift to `brb_totality` via transfers_satisfaction

Apply `transfers_satisfaction` (closed by Phase B) with
`brb_weak_div_witness`, `h_fair_compat` for BRB labels, the appropriate
index map, and `ideal_brb_totality` as `h_abs`. The `h_prop_transfer`
hypothesis instantiates as: "the predicate 'every correct proc has
returned' transfers between concrete and ideal states via `sim_rel`."

Commit: `feat: prove brb_totality via transfers_satisfaction`.

**BCA out of scope** for this plan. The BCA witness still gets its
`rank_non_increasing_on_fair_progress` sorry from §A.3 (so the
framework's new field is satisfied at the witness call site), but the
full BCA protocol-design closure (progress measure, ideal decision,
transfer lift) is deferred to a follow-up session. The same goes for
the existing pre-session BCA sorries (`bca_progress_measure`,
`bca_rank_wf`, `bca_no_fair_deadlock_reachable`, `ideal_bca_decision`,
`bca_decision`, etc.) — they stay as they are.

### Phase F — Cleanup — ✅ DONE

Stale `fair_non_elision_progress` references and outdated blocker
comments have been pruned from `Simulation.lean`.

## Remaining work

| Phase | Status | Estimate |
|---|---|---|
| A | ✅ Done | — |
| B | ✅ Done | — |
| C | ✅ Done | — |
| D | ⏳ In progress | ~1000-2000 LOC remaining |
| F | ✅ Done | — |

### Remaining Phase D commits (in recommended order)

**Highest priority — close ideal_brb_totality (unblocks brb_totality):**

1. ~~Close Step A~~ — ✅ DONE (OR-condition + sender-corrupt branch).
2. **Prove Step B** (finite induction over correct procs — see detailed
   strategy comment in BRB_Liveness.lean at line ~449).
4. `feat: prove brb_totality via transfers_satisfaction` — apply
   `transfers_satisfaction` with `brb_weak_div_witness` +
   `ideal_brb_totality` + `brb_fair_compat`.

**Lower priority — real progress measure (independent of above):**

5. Replace placeholder `brb_progress_measure` (currently `0`) with a
   real lex measure.
6. Re-prove `brb_rank_wf` for the real measure.
7. Discharge rank obligations: `rank_non_increasing`,
   `rank_decreases_on_fair_elision`, `rank_non_increasing_on_fair_progress`.
8. Prove `brb_fair_deadlock_implies_terminated` and use it to close the
   `h_fair_reverse` sorry inside `fair_deadlock_diverges`.

### Phase E — BCA protocol-design closure (after BRB is done)

Once BRB is fully closed, mirror the same structure for BCA in
`Leslie_LTS/Examples/BCA_Liveness.lean`.  BCA is more complex than BRB
(graded protocol with multiple phases: init → echo → vote → decide),
so expect ~1.5× the BRB effort.

**First step: study the TLA-side BCA liveness proof** at
`Leslie/Examples/BindingCrusaderAgreementLiveness.lean` (4513 lines).
This file contains the complete TLA-level BCA liveness proof, including:
- `bca_fairness` (line 60) — the TLA fairness predicate.
- Step-monotonicity lemmas for all local-state fields (`input_persist`,
  `sent_persist`, `isCorrect_persist`, `initRecv_step_mono`,
  `echoRecv_step_mono`, `voteRecv_step_mono`, `decided_step_mono`, etc.).
- Delivery lemmas chaining through protocol phases:
  `init_delivery_correct_sender` → `init_delivery_from_initRecv` →
  `amplify_init_delivery` → `echo_delivery_from_approved` →
  `vote_delivery_from_ready` → `decide_delivery_binary` /
  `decide_delivery_none`.
- The headline `totality`-equivalent (decision) via leads-to chaining.

The LTS-side proof should follow the same phase-by-phase leads-to
structure but adapted to the `assumes_fair_wf` + `transfers_satisfaction`
framework instead of TLA-level `pred_implies ... ↝ ...`.

**BCA-specific design decisions:**
- `bca_fair_labels` and `ideal_bca_fair_labels` are already defined in
  `BCA_Liveness.lean` (mirroring BRB).
- The `ideal_bca_internalStar_allFair` helper (vacuous — `.bind` is
  always fair) and `rank_decreases_on_unfair_abstract` (exfalso) are
  already proven.
- The progress measure for BCA is likely lex of
  `(decided_count, vote_pending, echo_pending, init_pending)` — refer
  to the TLA file's delivery lemma chain for the decreasing quantities.
- `bca_forward_sim` is at `BCA_Simulation.lean:2480`.

**Attack order for BCA:**
1. Study `BindingCrusaderAgreementLiveness.lean` to understand the
   phase-by-phase leads-to chain.
2. Write step-preservation lemmas for `IdealBCA` (monotonicity of
   `bound_value`, `decided`, `corrupted`).
3. Prove `ideal_bca_decision` via leads-to chaining (bind fires →
   output enabled for each correct p → output fires → all decided).
4. Prove `bca_decision` via `transfers_satisfaction`.
5. Design `bca_progress_measure`, prove `bca_rank_wf`, discharge the
   rank obligations.
6. Prove `bca_fair_deadlock_implies_terminated` and close `h_fair_reverse`.
