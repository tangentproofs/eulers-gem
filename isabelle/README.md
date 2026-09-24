# Isabelle side (Euler's Gem)

## Layout

```
isabelle/
  afp-Euler_Polyhedron_Formula/   # vendored AFP comparison base (Paulson)
    Euler_Formula.thy
    ROOT
    LICENSE                       # AFP BSD (see isa-afp.org/LICENSE)
    SOURCE_SHA256.txt             # provenance for the release tarball
    document/
  Poly100.thy                     # historical archive (Michal Wallace)
  Poly100-notes.org               # historical plan notes
  README.md                       # this file
```

## AFP comparison base (vendored)

Lawrence C. Paulson's AFP entry
**[Euler's Polyhedron Formula](https://isa-afp.org/entries/Euler_Polyhedron_Formula.html)**
(2023; HOL Light → Isabelle, credited to Jim Lawrence) is vendored under
`afp-Euler_Polyhedron_Formula/` as the **Isabelle comparison base** for the Lean
formalization in `../lean/`.

- Do **not** invent a fresh Isabelle development in this tree.
- Sources are copied from the official AFP release tarball (BSD license);
  copyright remains with the AFP authors — see `afp-Euler_Polyhedron_Formula/LICENSE`.
- Main theory: `Euler_Formula.thy` (`session Euler_Polyhedron_Formula`).

### Lean Results ↔ AFP theorems

| Lean (`lean/Results.lean`) | AFP (`Euler_Formula.thy`) | Meaning |
|----------------------------|---------------------------|---------|
| `results_faceEulerSum_of_height_one` | `Euler_Poincare_lemma` | Height-1 / slice H-rep: face Euler sum = 1 |
| (via cone path) | `Euler_polyhedral_cone` | Conic polyhedron: alternating face sum = 0 |
| `results_Euler_Poincare_full` | `Euler_Poincare_full` | Full-dim polytope: face Euler sum = 1 |
| `results_euler_relation_convex_3polytope` | `Euler_relation` | Convex 3-polytope: `V − E + F = 2` |
| `results_euler_relation_of_faceEulerSum` | (bookkeeping toward `Euler_relation`) | Face-sum = 1 + unique solid ⇒ `V−E+F=2` |

Supporting AFP substrate (hyperplane arrangements, cell complexes, Euler-char
invariance) maps to the Lean modules under `lean/EulersGem/` (see
`lean/MATHLIB_SURVEY.md`).

### Building / checking with Isabelle

This box does **not** currently have Isabelle installed (`isabelle` not on
`PATH`). To check the vendored session elsewhere:

1. Install [Isabelle](https://isabelle.in.tum.de/) (recent release; AFP entry
   targets `HOL-Analysis`).
2. Optionally install a matching [AFP](https://isa-afp.org/) release, or use
   this vendored tree alone (session depends only on `HOL-Analysis`).
3. From this directory:

```bash
# using the vendored session ROOT:
isabelle build -d afp-Euler_Polyhedron_Formula -v Euler_Polyhedron_Formula
```

Expected: session `Euler_Polyhedron_Formula` builds from `Euler_Formula.thy`
(timeout option in ROOT is 300s). Document generation (`document/`) is optional.

If Isabelle is later installed on this box, re-run the build command above and
update the status line under **Status**.

## Historical archive (Poly100)

Michal Wallace's unfinished Isabelle/HOL development, copied from
[`tangentstorm/tangentlabs`](https://github.com/tangentstorm/tangentlabs/tree/master/isar)
for provenance:

| File | Role |
|------|------|
| `Poly100.thy` | Working theory: simplex face counts, Euler char for simplices; stubs for Tverberg triangulation, general polytopes, Platonic solids, Pick's theorem |
| `Poly100-notes.org` | Plan notes: induction on facets, Tverberg dissection |

**Timeline:** these notes/theory **predate** Paulson's AFP entry — they are an
independent earlier attempt at Freek #13 / #50 / #92, not a derivative of Paulson.
Kept as historical archive only; not the Lean roadmap.

## Strategies (credited)

| Lineage | Approach | Role here |
|---------|----------|-----------|
| **Paulson AFP / HOL Light (Lawrence)** | Hyperplane arrangements, cell complexes, Euler-char invariance | **Base** (vendored under `afp-Euler_Polyhedron_Formula/`); **primary target** for Lean |
| **Michal Poly100** (earlier, unfinished) | Tverberg triangulation + induction on facets | Historical + alternate comparison only |

## Parked

- Pick's theorem (Euler → Pick via Funkenbusch)
- Five Platonic solids constructions (≤5 bound in Poly100; constructions TODO)

## Status

- **AFP vendored** as comparison base (`afp-Euler_Polyhedron_Formula/`).
- **Isabelle not installed on this box** — sources + build instructions only;
  session not machine-checked here.
- Poly100 kept as historical archive.
- Lean under `../lean/` is the active formalization path (`lake build`).
