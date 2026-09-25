# Unified spine (Michal 2026-09-24)

One story from *Euler's Gem*, not three unrelated proofs.

```
Euler–Poincaré (faceEulerSum / V−E+F=2 for convex polytopes)
        │
        ├──► Platonic: regularity + double-counting + Euler ⇒ five Schläfli
        │         (then geometric regular embeddings)
        │
        └──► Pick: lattice triangulation + planar/sphere Euler + area ½
                  ⇒ A = I + B/2 − 1
```

## Hard rules
- Platonic and Pick **discharge** Euler from the EP root (or a lemma derived from it).
- Forbidden: free `ℤ` hypothesis `V−E+F=2` as the only Euler input in a final Results claim.
- Forbidden: Pick via Ehrhart / generating functions / other routes that bypass Euler.
- Forbidden: naming classical Pick or geometric Platonic until the statement matches.

## Platonic lane — status (2026-09-25)

**Euler is discharged.** `RegularNumbers.hEuler` is no longer assumed anywhere in a final
claim: `PlatonicOfEuler.regular_polytope_counts` gets `V−E+F=2` from
`euler_relation_convex_3polytope`, proves `s·F=2·E` and `m·V=2·E` by double counting over
face-lattice incidence, and derives `0 < E`;
`schlafli_pair_mem_of_regular_polytope` then gives the five pairs.

**Three of the five solids are geometric**, each with its face lattice computed and all four
incidence counts proved, and each obtaining `V−E+F=2` from `Euler_Poincare_full`:

| solid | file | `V, E, F` | pair |
|---|---|---|---|
| tetrahedron | `SimplexFaces.lean` + `GeometricPlatonic.lean` | 4, 6, 4 | `{3,3}` |
| octahedron | `Octahedron.lean` | 6, 12, 8 | `{3,4}` |
| cube | `Cube.lean` | 8, 12, 6 | `{4,3}` |

`MetricRegular.lean` adds the first metric facts: the octahedron's and cube's vertices lie on a
sphere and all their edges have equal length, and `Cube.regularTetra` is a genuinely **regular**
tetrahedron (four pairwise-equidistant alternating cube corners) which is `{3,3}` with Euler
from EP. `lean/scripts/audit-axioms.sh` mechanically checks that no Results declaration depends
on a `native_decide` axiom or `sorryAx`.

Still open on this lane: the dodecahedron `{5,3}` and icosahedron `{3,5}` (golden-ratio
coordinates — the face lattice is not `decide`-able there); **one** polytope fact is still a
hypothesis of the general classification (the diamond property: every edge in two 2-faces),
proved for all three solids — "every edge has two vertices" is now proved in general
(`EdgeVertices.lean`); congruent-faces/flag-transitive regularity and uniqueness up to
similarity are not formalized. Details and the naming verdict: `PLATONIC_CLAUDE_AUDIT.md`.

## Current gap
- `euler_relation_convex_3polytope` — real geometric EP (root OK).
- Pick Funkenbusch identities — **assume** `heuler` in the general count form;
  unit-square / fan disks now prove planar Euler concretely (still not a call to
  `Euler_Poincare_full` for arbitrary disks).
- Pick witness-conditional shoelace form — geometric witness + emptiness landed;
  general form still takes `hEuler_planar` as EP-spine hyp. Unit-square case
  discharges Euler via `unitSquare_planar_euler`. Not classical Pick.
- Pick handshaking — **proved** for `CombinatorialDiskTriangulation` (incidence);
  unit-square witness wired to combinatorial disk; general polygons open.
- Planar disk Euler — fan-count lemma + unit square + fan `n≤5` proved;
  `planar_disk_euler_of_EP_bridge` still records the open general EP→planar gap.

## Done means
Results exports theorems whose proofs call the EP spine; auditors can follow Euler → corollary without a gap.
