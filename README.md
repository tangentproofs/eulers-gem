# Euler's Gem (`tangentproofs/eulers-gem`)

Lean 4 (+ archived Isabelle) formalization of **Euler's polyhedron formula**
and the Euler–Poincaré characteristic for convex polytopes
(Freek #13; popularized in David Richeson's *Euler's Gem*).

**Docs site:** [https://tangentproofs.github.io/eulers-gem/](https://tangentproofs.github.io/eulers-gem/)  
Auto-deploys on every push to `main` via [`.github/workflows/pages.yml`](.github/workflows/pages.yml) (GitHub Actions → Pages).

**Plain English:** [learn/](https://tangentproofs.github.io/eulers-gem/learn/) — each Results theorem and its definitions read back into English, with quizzes, sign-offs, a proof graph and interactive illustrations (source in `learn/`, see `learn/CONTRIBUTING.md`).

**Browsable Lean source:** [Results.lean](https://tangentproofs.github.io/eulers-gem/docs/Results.html)
([docs index](https://tangentproofs.github.io/eulers-gem/docs/)) — syntax-highlighted project modules with
cross-links; unknown identifiers (esp. `Mathlib.*`) redirect to
[mathlib4_docs](https://leanprover-community.github.io/mathlib4_docs/).

## Layout

```
lean/          Lean 4 project (active) — Lake / Mathlib / Results.lean
isabelle/      Isabelle — vendored AFP Euler_Polyhedron_Formula + Poly100 archive
scripts/       Comparator helpers + browsable-source builder
site/          GitHub Pages static site (+ docs/ built in CI from lean/)
learn/         Plain-English (informalization) app, built in CI into /learn/
```

## Proof strategy

**Lean (primary):** follow Lawrence C. Paulson's AFP
[*Euler's Polyhedron Formula*](https://isa-afp.org/entries/Euler_Polyhedron_Formula.html)
(2023; HOL Light port, credited to Jim Lawrence) — **hyperplane arrangements +
cell complexes + Euler-characteristic invariance** — especially where Mathlib
does not already provide the substrate. Target: Euler–Poincaré for
full-dimensional convex polytopes of arbitrary dimension, then `V − E + F = 2`
in dimension 3.

**Isabelle (comparison base):** the same AFP entry is **vendored** under
`isabelle/afp-Euler_Polyhedron_Formula/` (BSD; credit Paulson / AFP). See
`isabelle/README.md` for Lean Results ↔ AFP theorem mapping and build notes.
Do **not** invent a fresh Isabelle development.

**Isabelle on this box:** Isabelle2025-2 at `/home/box/Isabelle2025-2` (`isabelle` on PATH via `/home/box/bin/isabelle`). Vendored session **machine-checks green**: `isabelle build -d afp-Euler_Polyhedron_Formula -v -o document=false Euler_Polyhedron_Formula` (exit 0; Memnar #1535).

**Historical:** `isabelle/Poly100.thy` and `Poly100-notes.org` are Michal
Wallace's earlier unfinished Isabelle attempt (Tverberg triangulation +
induction on facets). They **predate** the AFP entry and are kept for provenance
and as an alternate strategy, not as the Lean roadmap.

## What's proved so far (Lean)

See `lean/Results.lean` (only claims what is actually proved):

| Theorem | Meaning |
|---------|---------|
| `results_euler_characteristic` | Euler characteristic of a full-dimensional convex polytope is `1` |
| `results_euler_polyhedron` | Euler's formula in real three-space from a finite convex hull and affine dimension 3 |
| `results_euler_relation_dimension_three` | Euler's formula: in dimension 3, `V − E + F = 2`, from that characteristic |
| `results_picks_theorem` | Pick's formula: area `= \|S\| + B/2 − 1` for a strictly convex lattice polygon, for any finite `S` equal to its interior lattice points (existence of that finite `S` not yet proved) |
| `results_picks_of_empty_primitive_fan` | Area `= B/2 − 1` for a strictly convex lattice polygon with primitive edges and no interior lattice points |
| `results_pick_count_of_euler` | Bookkeeping arithmetic: from `V = I + B`, `F = T + 1`, `V − E + F = 2`, `2E = 3T + B`, `A = T/2` (all hypotheses), `A = I + B/2 − 1` |
| `results_fan_pick_of_euler` | Arithmetic identity `(n − 2)/2 = n/2 − 1` for `n ≥ 3` (proof routed through the fan's disk Euler number) |
| `results_disk_pick_of_euler` | Arithmetic: given `A = (2I + B − 2)/2` and `3 ≤ n ≤ B`, `A = I + B/2 − 1` (proof routed through disk-Euler-preserving moves) |
| `results_five_platonic_solids` | Schläfli pairs: a combinatorially regular convex 3-polytope (every edge in two faces assumed) has `(s, m)` among `{3,3}`, `{4,3}`, `{3,4}`, `{5,3}`, `{3,5}`; plus the `(V, E, F)` of those five pairs. Not a construction of the solids; no metric regularity |

The Euler results require a finite convex hull and the appropriate affine
dimension, with no supplied halfspace presentation. `results_euler_polyhedron`
specializes the result to `EuclideanSpace ℝ (Fin 3)` and has exactly the two
geometric hypotheses `EulersGem.IsPolytope p` and `EulersGem.affDim p = 3`.
Its counts are the actual geometric face sets defined by `IsFaceOf` and `affDim`;
`facesOfDim_finite_of_isPolytope` supplies the geometric face-finiteness theorem.

`IsPolytope.isPolyhedron` supplies the finite-vertex-to-finite-halfspace
representation theorem in every finite-dimensional real inner product space.
The supporting linear-inequality elimination and representation lemmas work
over any linearly ordered field. They are in `EulersGem.LinearInequalities`,
`EulersGem.PolyhedralRepresentation`, and `EulersGem.PolytopeHalfspaces`;
`EulersGem.UnconditionalEuler` applies the hyperplane-arrangement Euler
argument from `EulersGem.Embed`.

Supporting proofs stay in `EulersGem.*`. The Platonic classification calls Euler's formula in dimension 3. Pick's theorem cuts the polygon into det-primitive triangles of total shoelace `T/2`, with `T = 2I + B − 2`, and reads `I + B/2 − 1` off the disk Euler number of that triangulation.

## Building (Lean)

Toolchain lockstep with other `tangentproofs` repos: **`leanprover/lean4:v4.35.0-rc1`**,
Mathlib pin `09a9e06e4e5ccd5b783f25e52ad3ebecfb1e2d68`.

```bash
cd lean
lake exe cache get   # never build Mathlib from scratch
lake build
./scripts/verify-euler.sh  # exact Euler contracts, axiom audit, and kernel replay
```

List paper-facing theorems:

```bash
./scripts/list-results.sh
# or: (cd lean && ./scripts/list-results.sh)
```

## References

- Lawrence C. Paulson, *Euler's Polyhedron Formula*, AFP 2023 —
  https://isa-afp.org/entries/Euler_Polyhedron_Formula.html
- Jim Lawrence, *A Short Proof of Euler's Relation for Convex Polytopes*,
  Canad. Math. Bull. 40 (1997)
- Michal Wallace, `Poly100.thy` / notes (pre-AFP unfinished Isabelle) —
  originally https://github.com/tangentstorm/tangentlabs/tree/master/isar
- David Richeson, *Euler's Gem*
- Freek Wiedijk, *Formalizing 100 Theorems* (#13 Polyhedron Formula)
