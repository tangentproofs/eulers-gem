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
