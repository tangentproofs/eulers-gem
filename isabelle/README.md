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

### Box install (Isabelle2025-2)

Installed on this shared Grok box (Memnar #1535 / GTD #538):

| Item | Value |
|------|-------|
| Version | **Isabelle2025-2** (January 2026) |
| Install path | `/home/box/Isabelle2025-2` |
| Wrapper on PATH | `/home/box/bin/isabelle` → `…/Isabelle2025-2/bin/isabelle` |
| Env snippet | `/home/box/isabelle-env.sh` (`PATH` + `ISABELLE_HOME`) |
| Heaps | `~/.isabelle/Isabelle2025-2/heaps/` (user) + bundled Pure/HOL under `$ISABELLE_HOME/heaps` |

Invoke:

```bash
source /home/box/isabelle-env.sh   # or rely on ~/bin in PATH via ~/.bashrc
isabelle version                  # → Isabelle2025-2
```

Official source: https://isabelle.in.tum.de/ (Linux bundle
`Isabelle2025-2_linux.tar.gz`). Full AFP mirror **not** required — this vendored
session depends only on `HOL-Analysis`.

### Building / checking the vendored session

From this directory (`isabelle/`):

```bash
isabelle build -d afp-Euler_Polyhedron_Formula -v -o document=false Euler_Polyhedron_Formula
```

First run builds `HOL-Analysis` (~10 min wall / ~45 min CPU on this box), then
`Euler_Polyhedron_Formula` (~15 s). Subsequent runs are cached (~7 s).

**Machine-checked green** on this box (2026-09-24 EDT):

```
Finished HOL-Analysis (0:09:37 elapsed time, 0:44:48 cpu time, factor 4.66)
Finished Euler_Polyhedron_Formula (0:00:14 elapsed time, 0:00:31 cpu time, factor 2.11)
# exit status 0
```

Document generation (`document/`) is optional (`-o document=false` skips it).


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

- Pick's theorem / Platonic solids: **Lean Phase B (#1535) landed** combinatorial
  cores under `lean/EulersGem/{Picks,Platonic}.lean`. Geometric lattice gaps and
  regular embeddings remain open (Poly100 stubs kept for provenance).

## Status

- **AFP vendored** as comparison base (`afp-Euler_Polyhedron_Formula/`).
- **Isabelle2025-2 installed** at `/home/box/Isabelle2025-2`; `isabelle` on PATH
  via `/home/box/bin/isabelle`.
- **Session machine-checks green** on this box:
  `isabelle build -d afp-Euler_Polyhedron_Formula -v -o document=false Euler_Polyhedron_Formula` → exit 0
  (2026-09-24 EDT; HOL-Analysis + Euler_Polyhedron_Formula).
- Poly100 kept as historical archive.
- Lean under `../lean/` is the active formalization path (`lake build`).
