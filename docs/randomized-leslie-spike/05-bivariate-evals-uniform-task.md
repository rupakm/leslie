# M1 W3 polish task — close `bivariate_evals_uniform`

This document is the briefing for a focused proving session that
closes the deferred `sorry` in `Leslie/Prob/Polynomial.lean`'s
`bivariate_evals_uniform`. With `evals_uniform` now proved (commit
`c8ad591`), the bivariate version reduces to two applications of the
univariate result.

## Goal

Prove `bivariate_evals_uniform` without `sorry`. Add field-size
hypotheses (one per direction); update the existing statement
accordingly. The univariate `evals_uniform` is fully proved and
available as a black box.

```lean
theorem bivariate_evals_uniform (dx dy : ℕ) (s : F)
    (pts_x : Finset F) (pts_y : Finset F)
    (h_cx : pts_x.card ≤ dx) (h_cy : pts_y.card ≤ dy)
    (h_nx : (0 : F) ∉ pts_x) (h_ny : (0 : F) ∉ pts_y) :
    (uniformBivariateWithFixedZero dx dy s).map
        (fun f => fun (p : pts_x) (q : pts_y) =>
          (f.eval (Polynomial.C p.val)).eval q.val)
      = PMF.uniform (pts_x → pts_y → F)
```

You will need to add:
- `h_Fx : dx + 1 ≤ Fintype.card F`
- `h_Fy : dy + 1 ≤ Fintype.card F`

These are needed to invoke `evals_uniform` in each direction.

## Repository state

- Path: `/Users/rupak/Code/tla/leslie`
- Branch: `randomized-leslie` (already checked out)
- Mathlib v4.27.0 in `lakefile.lean`
- Build: `lake build Leslie.Prob.Polynomial`
- Full project: `lake build`
- Conservativity gate: `bash scripts/check-conservative.sh`
  (must show "Conservative-extension check: OK ...")

## Setup context

`uniformBivariateWithFixedZero dx dy s : PMF (Polynomial (Polynomial F))`
is defined as:

```lean
noncomputable def uniformBivariateWithFixedZero (dx dy : ℕ) (s : F) :
    PMF (Polynomial (Polynomial F)) :=
  (PMF.uniform (Fin dx → Fin dy → F)).map fun coefs =>
    Polynomial.C (Polynomial.C s) + ∑ i : Fin dx, ∑ j : Fin dy,
      Polynomial.C (Polynomial.C (coefs i j)) *
        Polynomial.X ^ (i.val + 1) *
        (Polynomial.C Polynomial.X) ^ (j.val + 1)
```

Evaluating at `(p, q)`:
```
(f.eval (C p.val)).eval q.val = s + ∑ (i, j) coefs(i,j) * p^(i+1) * q^(j+1)
```

This is the bivariate polynomial `f(p, q)` with `f(0, 0) = s`.

The univariate `evals_uniform` (already proved, no sorry):
```lean
theorem evals_uniform (d : ℕ) (s : F)
    (pts : Finset F) (h_card : pts.card ≤ d) (h_nz : (0 : F) ∉ pts)
    (h_F : d + 1 ≤ Fintype.card F) :
    (uniformWithFixedZero d s).map
        (fun f => fun (p : pts) => f.eval p.val)
      = PMF.uniform (pts → F)
```

`uniformWithFixedZero d s = (uniform (Fin d → F)).map (fun coefs => C s + ∑ i, C (coefs i) * X^(i+1))`.

## Proof strategy — row-then-column reduction

The key insight: the bivariate eval factors through an intermediate
`Fin dx → pts_y → F` matrix.

### Algebraic factoring

For each `(p, q) ∈ pts_x × pts_y`:
```
f(p, q) = s + ∑_{i, j} coefs(i, j) * p^(i+1) * q^(j+1)
        = s + ∑_i (∑_j coefs(i, j) * q^(j+1)) * p^(i+1)
        = s + ∑_i b_i(q) * p^(i+1)
```
where `b_i(q) := ∑_j coefs(i, j) * q^(j+1)`.

So define:
```
Y_eval : (Fin dx → Fin dy → F) → (Fin dx → pts_y → F)
Y_eval coefs := fun i q => ∑ j, coefs(i, j) * q.val^(j+1)
```
and:
```
X_eval : (Fin dx → pts_y → F) → (pts_x → pts_y → F)
X_eval b := fun p q => s + ∑ i, b(i, q) * p.val^(i+1)
```

The composition `X_eval ∘ Y_eval` equals the bivariate eval map (up
to PMF.map_comp threading and showing the algebraic identities).

### Two pushforwards via `evals_uniform`

**Step 1:** `(uniform (Fin dx → Fin dy → F)).map Y_eval = uniform (Fin dx → pts_y → F)`.

For each row `i`, the row map `coefs(i, *) ↦ fun q => ∑ j coefs(i, j) * q.val^(j+1)`
is exactly the univariate eval map with `s = 0`, so:

```
(uniform (Fin dy → F)).map (fun row q => ∑ j row(j) * q.val^(j+1))
  = uniform (pts_y → F)
```

This is `evals_uniform dy 0 pts_y h_cy h_ny h_Fy` after unfolding
`uniformWithFixedZero` and `PMF.map_comp`.

To lift to the per-row Pi map, use a **product-uniform helper**:

```lean
lemma PMF.uniform_pi_map_of_uniform_map
    {ι α β : Type*} [Fintype ι] [Nonempty ι]
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    {h : α → β} (h_uniform : (PMF.uniform α).map h = PMF.uniform β) :
    (PMF.uniform (ι → α)).map (fun f i => h (f i)) = PMF.uniform (ι → β)
```

Proof: each fiber of `(fun f i => h (f i))` over `g : ι → β` has
size `(|h⁻¹{g i}|)^|ι|` (product of per-coordinate fiber sizes).
Since `h_uniform` implies all per-coordinate fibers are equal-sized,
this is constant in `g`. Apply `PMF.uniform_map_of_surjective_constFiber`.

Or prove via `PMF.ext` + `tsum_eq_sum` directly counting fibers.

**Step 2:** `(uniform (Fin dx → pts_y → F)).map X_eval = uniform (pts_x → pts_y → F)`.

For each `q ∈ pts_y`, the per-q map `b(*, q) ↦ fun p => s + ∑ i, b(i, q) * p.val^(i+1)`
is exactly the univariate eval map with `s = s`, so:

```
(uniform (Fin dx → F)).map (fun row p => s + ∑ i row(i) * p.val^(i+1))
  = uniform (pts_x → F)
```

This is `evals_uniform dx s pts_x h_cx h_nx h_Fx` after the same
unfolding.

To lift to the per-q Pi map, use the same Pi-uniform helper, but
now indexed by `pts_y` instead of `Fin dx`. The argument is
symmetric.

**Step 3:** Compose via `PMF.map_comp`:

```
(bivariate eval) = (X_eval ∘ Y_eval)
(uniform).map (X_eval ∘ Y_eval) = ((uniform).map Y_eval).map X_eval
                                = (uniform_intermediate).map X_eval  -- by Step 1
                                = uniform_final                       -- by Step 2
```

## Key Mathlib lemmas / project lemmas to use

- `evals_uniform` — the univariate result (in `Polynomial.lean`).
- `PMF.uniform_map_of_bijective` — already in the file.
- `PMF.uniform_map_of_surjective_constFiber` — already in the file
  (added by previous agent).
- `PMF.map_comp` — composition of pushforwards.
- `PMF.ext`, `tsum_eq_sum`, `Finset.card_eq` — for the Pi-uniform
  helper if you need to prove it directly.
- `Fintype.card_fun` — `card (α → β) = card β ^ card α`.

## Constraints

1. **Header fence**: do NOT modify the public signatures of
   `evals_uniform` or other existing theorems (those are committed
   to in PR #25). Only modify `bivariate_evals_uniform`'s signature
   to add the two `h_Fx`, `h_Fy` field-size hypotheses.

2. **Allowed paths** (per `scripts/check-conservative.sh` allowlist):
   - `Leslie/Prob/Polynomial.lean` (main target)
   - Other `Leslie/Prob/*` files if you need helpers
   - `docs/randomized-leslie-spike/` for notes
   - Do NOT touch existing main-branch Leslie code (Refinement.lean
     etc.) or `Leslie/Examples/Prob/*` (no callers of
     `bivariate_evals_uniform` yet — it's stated in anticipation of
     M3 AVSS).

3. **Add no new dependencies** to `lakefile.lean` (Mathlib already
   pinned at v4.27.0).

4. **Don't push to origin**. Local commits on `randomized-leslie`
   are fine; the user pushes when ready.

## Acceptance criteria

- `lake build Leslie.Prob.Polynomial` green with **0 sorries**.
- `lake build` (full project) green; same 4 pre-existing project
  sorries unchanged (`Refinement.lean` ×2, `LastVoting.lean` ×2);
  spike-file sorries also unchanged (`Spike/CoinFlip.lean`,
  `Spike/ASTSanity.lean`).
- `bash scripts/check-conservative.sh` passes.
- One commit on `randomized-leslie` describing the proof strategy
  and the new field-size hypotheses.

## What to do if you can't close the proof

If after serious attempt you can't close `bivariate_evals_uniform`
in budget:

1. Do NOT commit a worse state. The current state has 1 sorry
   (`bivariate_evals_uniform` itself, `evals_uniform` is proved).
2. Document specific Mathlib gaps you hit.
3. Make a partial attempt — e.g., prove the Pi-uniform helper as
   a standalone lemma and prove just one of the two reduction
   steps. Each step alone is meaningful progress.
4. Commit your partial result and update this document.

## Reference files to read first

In this order:
1. `Leslie/Prob/Polynomial.lean` (the target file; especially the
   already-proved `evals_uniform` to understand the proof style and
   structure)
2. `Leslie/Prob/PMF.lean` (helper context)
3. `docs/randomized-leslie-spike/04-evals-uniform-proof-task.md`
   (the prior briefing — proof patterns from there are reusable)

## Branch state at task start

```
c8ad591 feat(M1 W3): close evals_uniform — algebraic core of Shamir secrecy
11046da docs: spike task brief for evals_uniform proof
e546395 fix(M1 W4): apply review fixes to Shamir model
b4cd79d feat(M1 W4): Shamir secret sharing — secrecy proven (modulo evals_uniform)
... (older commits)
```

Currently 1 sorry remaining on the production codepath:
`Leslie/Prob/Polynomial.lean:435` — `bivariate_evals_uniform` (target).
Plus the 4 pre-existing project sorries (Refinement, LastVoting) and
2 spike sorries (CoinFlip, ASTSanity), all unchanged.
