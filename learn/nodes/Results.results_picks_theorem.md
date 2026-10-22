---
id: Results.results_picks_theorem
title: "Pick's theorem for strictly convex lattice polygons"
summary: "For a strictly convex counterclockwise lattice polygon with distinct vertices, the Lebesgue area of its convex hull is `|S| + B/2 − 1`, for any `Finset S` equal to its set of interior lattice points. That such a finite `S` exists is not yet proved in the repo."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "**One hypothesis is not discharged.** The statement takes `S : Finset (ℤ × ℤ)` with `hS : (S : Set (ℤ × ℤ)) = P.interiorLatticePoints`. Nothing in this repository proves such an `S` exists — that is finiteness of the interior lattice points of a bounded convex region, which is true and is not proved here. If no such `S` existed for some polygon, the statement would be vacuous for that polygon. This is the single biggest gap in the Pick lane."
  - "**Strict convexity is required, in the listed order.** `StrictlyConvexCCW` is `ConvexCCW ∧ LocalCCWTurns`: every vertex weakly left of every directed edge, *and* a strict left turn at every vertex. A convex polygon listed clockwise fails the first; a convex polygon with a collinear listed vertex fails the second. The latter is a real trap — re-list the polygon without the redundant vertex and the theorem applies."
  - "**Nothing is claimed for non-convex polygons.** `interiorLatticePoints` is defined relative to `convexHullRegion`, the hull of the *vertex set*. For a non-convex polygon the Lean's `I` counts lattice points the polygon does not enclose, so `I + B/2 − 1` is not even the right number to aim at. Classical Pick for simple non-convex polygons is **not** proved here."
  - "The area is `MeasureTheory.volume P.convexHullRegion`, genuine Lebesgue measure on `ℝ × ℝ`, and the right-hand side is `ENNReal.ofReal` of a rational cast. So this is a measure-theoretic statement, not a shoelace identity — the bridge is `LatticeArea.volume_convexHullRegion_eq_ofReal_shoelace`."
widgets:
  - type: outline
    title: "Proof outline: how Results.lean proves it"
    config:
      steps:
        - text: "Hypothesis hS: a finite list S of the interior lattice points is handed in"
          gap: true
          link: Picks.LatticePolygon.interiorLatticePoints
          decl: Picks.LatticePolygon.interiorLatticePoints
          note: "That such a Finset exists (a bounded convex region has finitely many lattice points) is true but not proved in this repository. For a polygon with no such S the theorem says nothing."
        - text: "Triangulate and add up: P.shoelace = (2·|S| + B − 2) / 2"
          hard: true
          decl: Picks.LatticeFan.shoelace_eq_two_cardI_add_B_sub_two_div_two
          note: "exists_primitive_polygon_list cuts P into det-primitive triangles (the corner fan if the interior is empty, otherwise a fan from an interior point plus ears), T = 2I + B − 2 of them. Each has shoelace 1/2, so the polygon's shoelace is T/2. Uses hS, hverts and hsc. This is the geometric heart."
        - text: "Size bounds: 3 ≤ n (the length_ge field of a LatticePolygon) and n ≤ B (listed vertices are boundary lattice points)"
          link: Picks.LatticePolygon
          decl: Picks.LatticeFan.nVertices_le_B
          note: "n is the number of listed vertices. Both bounds are needed only to feed the next step."
        - text: "Euler for the triangulated disk: V − E + F = 2 with V = I + B, E = 3I + 2B − 3, F = T + 1"
          link: Picks.triangulated_disk_euler_from_characteristic
          decl: Picks.triangulated_disk_euler_from_characteristic
          note: "Starts from a triangle's Euler–Poincaré characteristic, then the corner n-cycle, B − n boundary insertions, B − 3 diagonals and I stellar subdivisions, each keeping the Euler number at 2. Its inputs are the numbers n, B, I only: it is not about the particular triangulation of the previous step."
        - text: "Handshake count: 2E = 3T + B, by omega"
          note: "Pure arithmetic on the definitions of E and T in Results.lean, using B ≥ 3."
        - text: "Pick's count from Euler: shoelace = T/2 and V − E + F = 2 give shoelace = I + B/2 − 1"
          link: Results.results_pick_count_of_euler
          decl: Results.results_pick_count_of_euler
          note: "The arithmetic step, applied to the shoelace number."
        - text: "Shoelace to Lebesgue measure: volume P.convexHullRegion = ofReal P.shoelace"
          hard: true
          link: Picks.LatticeArea.volume_convexHullRegion_eq_ofReal_shoelace
          decl: Picks.LatticeArea.volume_convexHullRegion_eq_ofReal_shoelace
          note: "The hull is the union of the n − 2 corner-fan triangles, almost-everywhere disjoint, and each triangle's measure is its shoelace. Uses hsc and hverts. The second piece of geometry."
        - text: "Rewrite the area, cast ℚ to ℝ, push_cast; ring"
          note: "Bookkeeping that closes the goal volume = ofReal(|S| + B/2 − 1)."
  - type: pick
    title: "Break the hypotheses and watch which one fails"
    config:
      preset: pentagon
      show: [counts, hypotheses, fan]
quiz:
  - q: "What is the left-hand side of the conclusion?"
    type: choice
    choices:
      - "`MeasureTheory.volume P.convexHullRegion`"
      - "`P.shoelace`"
      - "`(P.B : ℚ) / 2 - 1`"
      - "`P.interiorLatticePoints.ncard`"
    answer: 0
    explain: "`MeasureTheory.volume P.convexHullRegion = ENNReal.ofReal ((S.card : ℚ) + (P.B : ℚ) / 2 - 1)`. Lebesgue measure, not the shoelace number. The shoelace appears in the proof, via `LatticeArea.volume_convexHullRegion_eq_ofReal_shoelace`."
  - q: "What is `S`, and what is assumed about it?"
    type: choice
    choices:
      - "a `Finset (ℤ × ℤ)` with `↑S = P.interiorLatticePoints` — a *hypothesis*, since the existence of such an `S` is not proved here"
      - "defined to be `P.interiorLatticePoints`"
      - "the vertex set of `P`"
      - "the boundary lattice points"
    answer: 0
    explain: "`(S : Finset (ℤ × ℤ)) (hS : (S : Set (ℤ × ℤ)) = P.interiorLatticePoints)`. `interiorLatticePoints` is a `Set`, deliberately — its docstring says \"finiteness of lattice points in a bounded convex set is not discharged here\". So the theorem is conditional on being handed a finite enumeration."
  - q: "`StrictlyConvexCCW P` unfolds to which conjunction?"
    type: choice
    choices:
      - "`ConvexCCW P ∧ LocalCCWTurns P`"
      - "`ConvexCCW P ∧ PrimitiveEdges P`"
      - "`Function.Injective P.vertex ∧ ConvexCCW P`"
      - "`EmptyInterior P ∧ ConvexCCW P`"
    answer: 0
    explain: "`def StrictlyConvexCCW : Prop := ConvexCCW P ∧ LocalCCWTurns P` (LatticeFan.lean). Injectivity of the vertices is a *separate* hypothesis `hverts` of this theorem, not part of `StrictlyConvexCCW`."
  - q: "A square with vertices listed `(0,0), (1,0), (2,0), (2,2), (0,2)` — convex as a region, but with `(1,0)` collinear between its neighbours. Does the theorem apply?"
    type: choice
    choices:
      - "yes"
      - "no: `LocalCCWTurns` requires a *strict* left turn at every vertex, and at `(1,0)` the turn is zero"
      - "no: `ConvexCCW` fails"
    answer: 1
    explain: "`def LocalCCWTurns : Prop := ∀ i, 0 < latticeDet (P.vertex (P.prevIdx i)) (P.vertex i) (P.vertex (P.nextIdx i))` — strict. At a collinear vertex the determinant is `0`. `ConvexCCW` still holds (no vertex is strictly right of an edge). Drop `(1,0)` from the list and the theorem applies, to the same region. Try it in the widget's `collinear-vertex` preset."
  - q: "A dart-shaped (non-convex) lattice polygon. What does the theorem say about its area?"
    type: choice
    choices:
      - "`I + B/2 − 1`, as for any lattice polygon"
      - "nothing: `ConvexCCW` fails, and in any case `interiorLatticePoints` is taken in the convex hull, so the Lean's `I` counts points the dart excludes"
      - "`B/2 − 1`"
    answer: 1
    explain: "Both halves matter. `ConvexCCW` fails, so no hypothesis is met. And the conclusion is about `volume P.convexHullRegion`, the measure of the *hull*, which for a dart is larger than the dart. Classical Pick does hold for simple non-convex polygons; this repository does not prove it."
  - q: "`I = 4`, `B = 12` for a 3×3 lattice square. What is `I + B/2 − 1`?"
    type: number
    answer: 9
    explain: "`4 + 6 − 1 = 9`, which is the area of a 3×3 square. Each side has `gcd(3,0) = 3`, giving `4 × 3 = 12` boundary points with endpoints shared, and the interior is a 2×2 block."
---

## Plain English

**Pick's theorem.** Draw a convex polygon whose corners sit on the integer grid. Count the grid
points strictly inside it (`I`) and the grid points on its boundary (`B`). Then its area is

> `I + B/2 − 1`.

```lean
theorem results_picks_theorem
    (P : EulersGem.Picks.LatticePolygon) (S : Finset (ℤ × ℤ))
    (hS : (S : Set (ℤ × ℤ)) = P.interiorLatticePoints)
    (hverts : Function.Injective P.vertex)
    (hsc : EulersGem.Picks.LatticeFan.StrictlyConvexCCW P) :
    MeasureTheory.volume P.convexHullRegion =
      ENNReal.ofReal ((S.card : ℚ) + (P.B : ℚ) / 2 - 1)
```

The area on the left is genuine **Lebesgue measure**. The counts on the right are genuine lattice
point counts. Four hypotheses: a finite enumeration `S` of the interior points, distinct vertices,
and [strict counterclockwise convexity](#/node/Picks.LatticeFan.StrictlyConvexCCW) (which is two
conditions).

### In one breath

Rule a sheet of graph paper and draw a convex shape whose corners land exactly on crossings. Now
count: how many crossings are strictly inside, and how many sit on the outline. Take the inside
count, add half the outline count, subtract one. That is the area, exactly, in squares. A
three-by-three square: four inside, twelve on the outline, four plus six minus one is nine. It
works for any convex shape of this kind, and the reason it works is Euler's formula in disguise —
chop the shape into the smallest possible triangles, and Euler counts them for you.

## What this does and does not prove

**It does prove:**

- **Pick's theorem for strictly convex lattice polygons.** You may call it Pick's theorem, with
  "for strictly convex polygons, given a finite enumeration of the interior points" attached.
- With the **Lebesgue measure** of [`convexHullRegion`](#/node/Picks.LatticePolygon.convexHullRegion)
  on the left, not a shoelace sum. The identification of the two is
  [`LatticeArea.volume_convexHullRegion_eq_ofReal_shoelace`](#/node/Picks.LatticeArea.volume_convexHullRegion_eq_ofReal_shoelace),
  a separate theorem.
- With `B` the [geometric boundary count](#/node/Picks.LatticePolygon.B), computed through edge
  gcds, and `S.card` the count of
  [interior lattice points](#/node/Picks.LatticePolygon.interiorLatticePoints).
- Routing its Euler input through
  [`triangulated_disk_euler_from_characteristic`](#/node/Picks.triangulated_disk_euler_from_characteristic),
  whose proof begins at a geometric triangle's Euler–Poincaré characteristic.

**It does not prove:**

- **That the hypothesis `hS` can be met.** The existence of a `Finset S` equal to
  `P.interiorLatticePoints` — i.e. that a bounded convex region contains finitely many lattice
  points — is *not proved in this repository*. `interiorLatticePoints` is left as a `Set` and its
  docstring says so. The theorem is stated for whatever `S` a caller supplies; if none exists for
  some polygon, the claim is vacuous for it. This is the gap to fix next.
- **Classical Pick for non-convex simple polygons.** `interiorLatticePoints` and
  `convexHullRegion` are both defined via the convex hull of the vertex list, so for a non-convex
  polygon neither side of the equation is about the shape you drew.
- **Anything for a polygon listed with collinear vertices**, or clockwise, or with a repeated
  vertex. Each of those breaks a stated hypothesis, and the widget above will tell you which.
- A **triangulation existence theorem** in general. The proof constructs the triangulation it needs
  (`exists_primitive_polygon_list`) for strictly convex polygons; that construction is specific to
  this setting.

### How it is proved

The **proof outline** at the end of this explanation lists the steps of the Lean proof in
`Results.lean`, each with the node it uses and its source lines. Two of them are geometry: the
triangulation that makes the shoelace `T/2`, and the identification of the shoelace with Lebesgue
measure. The Euler, handshake and count steps between them are bookkeeping. It is worth knowing
which is which: on their own, those middle steps prove nothing about polygons at all.

### Where it sits

The top of the Pick lane. Below it:
[`LatticePolygon`](#/node/Picks.LatticePolygon),
[`B`](#/node/Picks.LatticePolygon.B),
[`interiorLatticePoints`](#/node/Picks.LatticePolygon.interiorLatticePoints),
[`convexHullRegion`](#/node/Picks.LatticePolygon.convexHullRegion),
[`shoelace`](#/node/Picks.LatticePolygon.shoelace),
[`StrictlyConvexCCW`](#/node/Picks.LatticeFan.StrictlyConvexCCW), and the two theorems named above.
The `I = 0` special case with a cleaner hypothesis list is
[`results_picks_of_empty_primitive_fan`](#/node/Results.results_picks_of_empty_primitive_fan).
