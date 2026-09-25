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

## Current gap
- `euler_relation_convex_3polytope` — real geometric EP (root OK).
- Platonic `RegularNumbers.hEuler` — **assumed**, not discharged from EP.
- Pick Funkenbusch identities — **assume** `heuler`, not discharged from planar EP.
- Pick witness-conditional shoelace form — geometric witness + emptiness landed;
  still takes `hEuler_planar` as EP-spine hyp (discharge open). Not classical Pick.
- Pick handshaking — **proved** for `CombinatorialDiskTriangulation` (incidence);
  wiring geometric witness → combinatorial incidence still open.
- Planar disk Euler bridge — `PlanarDiskEulerCounts` / `planar_disk_euler_of_EP_bridge`
  records the EP discharge hyp; not yet derived from `Euler_Poincare_full`.

## Done means
Results exports theorems whose proofs call the EP spine; auditors can follow Euler → corollary without a gap.
