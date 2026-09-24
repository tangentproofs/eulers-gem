# Euler's Gem (`tangentproofs/eulers-gem`)

Lean 4 (+ archived Isabelle) formalization of **Euler's polyhedron formula**
and the Euler–Poincaré characteristic for convex polytopes
(Freek #13; popularized in David Richeson's *Euler's Gem*).

**Docs site:** [https://tangentproofs.github.io/eulers-gem/](https://tangentproofs.github.io/eulers-gem/)

## Layout

```
lean/          Lean 4 project (active) — Lake / Mathlib / Results.lean
isabelle/      Isabelle — vendored AFP Euler_Polyhedron_Formula + Poly100 archive
scripts/       Comparator helpers (list Results.lean theorems)
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
(`isabelle` on PATH). Vendored session **machine-checks green**:
`isabelle build -d afp-Euler_Polyhedron_Formula -v -o document=false Euler_Polyhedron_Formula` (exit 0; Memnar #1535).
**Historical:** `isabelle/Poly100.thy` and `Poly100-notes.org` are Michal
Wallace's earlier unfinished Isabelle attempt (Tverberg triangulation +
induction on facets). They **predate** the AFP entry and are kept for provenance
and as an alternate strategy, not as the Lean roadmap.

## What's proved so far (Lean)

See `lean/Results.lean` (only claims what is actually proved):

| Theorem | Meaning |
|---------|---------|
| `results_eulerChar_simplex` | Euler char of an `n`-simplex (incl. empty face) is `0` |
| `results_card_combinatorialFaces` | `#` of `m`-faces of an `n`-simplex is `C(n+1,m+1)` |
| `results_tetrahedron_polyhedron_numbers` | Tetrahedron: `V − E + F = 2` |
| `results_polyhedron_formula_of_eulerChar` | Bookkeeping: full Euler `0` ⇒ `F+V−E=2` |
| `results_faceEulerSum_simplex_faceCount` | Simplex face-sum (no empty face) `= 1` |
| `results_euler_relation_of_faceEulerSum` | Bookkeeping: `faceEulerSum=1` + unique solid ⇒ `V−E+F=2` |
| `results_faceEulerSum_of_height_one` | Height-1 H-rep: Paulson slice EP (`faceEulerSum = 1`) |
| `results_Euler_Poincare_full` | Full-dim H+V-rep polytope: `faceEulerSum = 1` |
| `results_euler_relation_convex_3polytope` | Convex 3-polytope (H+V-rep): `V − E + F = 2` |

Paulson cone→slice→embed path green: `ConeSliceFaceBijection`, height-1 EP,
`E × ℝ` embedding, `Euler_Poincare_full`, geometric 3D. Mathlib gap survey in
`lean/MATHLIB_SURVEY.md`.

## Parked (do not start)

- Pick's theorem (Euler → Pick via Funkenbusch)
- Five Platonic solids constructions

## Building (Lean)

Toolchain lockstep with other `tangentproofs` repos: **`leanprover/lean4:v4.35.0-rc1`**,
Mathlib pin `09a9e06e4e5ccd5b783f25e52ad3ebecfb1e2d68`.

```bash
cd lean
lake exe cache get   # never build Mathlib from scratch
lake build
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

## Tracking (prove2.me)

We track the Lean formalization as a **local milestone / declaration graph** under
[`prove2/`](prove2/) (see `prove2/milestones.json` and `lean/PROVE2.md`).

- **Local** = in-repo graph + optional `$HOME/prove2me_workspace`-style layout for
  Lean checks. The prove2.me **database is cloud API–only** (no self-hosted DB
  found); nothing here mirrors their server DB.
- **Later (optional):** private prove2.me mission or
  [`upload_full_project`](https://prove2.me/references/upload_full_project.md)
  once `lake build` is green and statements are stable.
- Do **not** block PRs on account registration or authenticated API calls.
