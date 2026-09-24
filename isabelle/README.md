# Isabelle side (Euler's Gem)

## What's here now

Michal Wallace's unfinished Isabelle/HOL development, copied from
[`tangentstorm/tangentlabs`](https://github.com/tangentstorm/tangentlabs/tree/master/isar)
for provenance and comparison:

| File | Role |
|------|------|
| `Poly100.thy` | Working theory: simplex face counts, Euler char for simplices; stubs for Tverberg triangulation, general polytopes, Platonic solids, Pick's theorem |
| `Poly100-notes.org` | Plan notes: induction on facets, Tverberg dissection |

**Timeline:** these notes/theory **predate** Paulson's AFP entry — they are an
independent earlier attempt at Freek #13 / #50 / #92, not a derivative of Paulson.

## Next Isabelle step (TODO — not this PR)

**Do not invent a new Isabelle development.** Port Lawrence C. Paulson's AFP
entry **[Euler's Polyhedron Formula](https://isa-afp.org/entries/Euler_Polyhedron_Formula.html)**
(2023; HOL Light → Isabelle, credited to Jim Lawrence) into this tree as the
**base** for the Isabelle side.

- AFP: https://isa-afp.org/entries/Euler_Polyhedron_Formula.html
- Main theory: `Euler_Formula.thy` (`Euler_Poincare_full`, …)
- Strategy: hyperplane arrangements + cell complexes; Euler-char invariance;
  then Euler–Poincaré for full-dimensional convex polytopes of arbitrary dimension.

Use the vendored AFP development to **cross-check** the Lean formalization under
`../lean/` (which aims to mirror the same Paulson approach).

## Strategies (credited)

| Lineage | Approach | Role here |
|---------|----------|-----------|
| **Paulson AFP / HOL Light (Lawrence)** | Hyperplane arrangements, cell complexes, Euler-char invariance | **Base** for Isabelle port; **primary target** for Lean |
| **Michal Poly100** (earlier, unfinished) | Tverberg triangulation + induction on facets | Historical + alternate comparison only |

## Parked

- Pick's theorem (Euler → Pick via Funkenbusch)
- Five Platonic solids constructions (≤5 bound in Poly100; constructions TODO)

## Status

Poly100 sources archived. Full AFP port is a follow-up PR. Lean under `../lean/`
is the active formalization path.
