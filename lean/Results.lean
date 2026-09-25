/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import Mathlib.Tactic
import EulersGem.Embed
import EulersGem.PlatonicOfEuler
import EulersGem.LatticeArea

/-!
# Three theorems

Paper-facing statements of Euler's polyhedron formula, Pick's theorem for
strictly convex lattice polygons, and the Schläfli classification of
combinatorially regular convex polyhedra. Proofs are discharges of lemmas
already proved in `EulersGem.*`.

Each docstring is the claim an auditor should check. A classical name is used
only for the part the statement actually proves; the gaps below are part of
the claim, not asides.

* **Euler.** `V − E + F = 2` for a convex 3-polytope given both as a finite
  intersection of closed half-spaces and as the convex hull of a finite set.
  Mathlib has neither polyhedra nor polytope faces.
* **Pick.** Lebesgue area `I + B/2 − 1` for a strictly convex lattice polygon.
  Not the classical theorem for arbitrary simple (possibly non-convex) lattice
  polygons, and interior finiteness is still a `Finset` hypothesis.
* **Platonic.** A combinatorially regular convex 3-polytope has Schläfli
  symbol in a set of five pairs. Not “there are exactly five geometrically
  regular solids”: the icosahedron and dodecahedron are not constructed,
  uniqueness up to similarity is not proved, and metric regularity is not
  formalized. See the third docstring.
-/

open MeasureTheory
open EulersGem
open EulersGem.Picks

namespace Results

/-! ## Euler's polyhedron formula -/

/-- **Euler's polyhedron formula.**

Let `p` be a convex polyhedron in a 3-dimensional real inner product space:
a polytope (the convex hull of a finite set) that is also a polyhedron (a
finite intersection of closed half-spaces), of affine dimension `3`. If `V`,
`E`, and `F` are the numbers of faces of affine dimension `0`, `1`, and `2`
— the vertices, edges, and facets — then

`V − E + F = 2`.

A face is a convex extreme subset (`IsFaceOf`), Isabelle's `face_of`. The
empty set has affine dimension `−1` and the body itself has affine dimension
`3`, so neither is counted. That is the classical count for a convex
3-polytope.

Mathlib has no polyhedron or polytope predicate, no polytope-face relation
(`IsExtreme` does not require the face to be convex), and no set-level affine
dimension with `affDim ∅ = −1` (only `AffineSubspace.finDim : WithBot ℕ`).
`IsPolyhedron`, `IsPolytope`, `IsFaceOf`, and `affDim` are the four
definitions the statement cannot avoid; see `MATHLIB_SURVEY.md`.

The half-space representation is a separate hypothesis because this
development has not proved the Minkowski–Weyl theorem that every V-polytope
is an H-polyhedron. The identity is proved for every set that is both, which
is the classical object once that equivalence is granted.
-/
theorem euler_polyhedron_formula
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nonempty E]
    {p : Set E}
    (hHedron : IsPolyhedron p)
    (hP : IsPolytope p)
    (hdim : affDim p = 3)
    (hE : Module.finrank ℝ E = 3) :
    (({f : Set E | IsFaceOf p f ∧ affDim f = 0}.ncard) : ℤ) -
        ({f : Set E | IsFaceOf p f ∧ affDim f = 1}.ncard : ℤ) +
        ({f : Set E | IsFaceOf p f ∧ affDim f = 2}.ncard : ℤ) = 2 := by
  obtain ⟨H, hH, hp⟩ := hHedron
  exact euler_relation_convex_3polytope hH hp hP hdim hE

/-! ## Pick's theorem -/

/-- **Pick's theorem for a strictly convex lattice polygon.**

Let `P` be a cyclic list of at least three lattice points in `ℤ × ℤ`, with
distinct vertices, oriented counterclockwise, and strictly convex: the whole
vertex set lies in the closed half-plane to the left of every edge, and every
vertex is a strict left turn (`StrictlyConvexCCW`). Let `I` be a finite set
of lattice points equal to the lattice points of the convex hull that do not
lie on the boundary cycle, and let `B` be the number of lattice points on
that cycle (vertices and any lattice points strictly between them). Then the
Lebesgue area of the convex hull, as a real number, is

`I + B/2 − 1`.

Area is `(MeasureTheory.volume ·).toReal` on `ℝ × ℝ`, i.e. Lebesgue measure.
For a convex polygon the convex hull is the filled polygon, `I` counts its
interior lattice points, and `B` counts its boundary lattice points. The
formula is the classical one on this class.

It is not the full classical theorem. Classical Pick applies to every simple
lattice polygon, including non-convex ones, where the filled region is the
Jordan interior of the cycle rather than the convex hull of the vertices.
Finiteness of the interior lattice points is a hypothesis here (`I` is a
`Finset` whose underlying set equals that collection), not a proved fact
about bounded subsets of `ℤ × ℤ`.

Mathlib has no lattice polygon, no interior or boundary lattice-point count,
and no Pick theorem. `LatticePolygon`, `B`, `interiorLatticePoints`, and
`StrictlyConvexCCW` are the definitions the statement cannot avoid.
`convexHull`, `MeasureTheory.volume`, `Finset`, `ℚ`, and `ℝ` are Mathlib.
-/
theorem picks_theorem
    (P : LatticePolygon)
    (I : Finset (ℤ × ℤ))
    (hI : (I : Set (ℤ × ℤ)) = P.interiorLatticePoints)
    (hverts : Function.Injective P.vertex)
    (hsc : LatticeFan.StrictlyConvexCCW P) :
    (volume P.convexHullRegion).toReal =
      (I.card : ℝ) + (P.B : ℝ) / 2 - 1 := by
  classical
  have hvol :=
    LatticeArea.volume_eq_ofReal_cardI_add_B_div_two_sub_one_no_pe P I hI hverts hsc
  have hB : 3 ≤ P.B := by
    have hsub : P.vertexFinset ⊆ P.boundaryLatticePoints := by
      intro v hv
      exact LatticePolygon.vertices_mem_boundary P (List.mem_toFinset.mp hv)
    have hvc : P.vertexFinset.card = P.nVertices := by
      rw [LatticeFan.vertexFinset_eq_univ_image P, Finset.card_image_of_injective _ hverts,
        Finset.card_univ, Fintype.card_fin]
    have hlen : 3 ≤ P.nVertices := by simpa [LatticePolygon.nVertices] using P.length_ge
    have hle : P.nVertices ≤ P.B := by
      simpa [LatticePolygon.B, hvc] using Finset.card_le_card hsub
    exact le_trans hlen hle
  have hnn : 0 ≤ (I.card : ℚ) + (P.B : ℚ) / 2 - 1 := by
    have hB3 : (3 : ℚ) ≤ P.B := mod_cast hB
    have hI0 : (0 : ℚ) ≤ I.card := mod_cast Nat.zero_le I.card
    linarith
  rw [hvol, ENNReal.toReal_ofReal (by exact_mod_cast hnn)]
  push_cast
  rfl

/-! ## Schläfli classification -/

/-- **Schläfli classification of combinatorially regular convex polyhedra.**

Let `p` be a convex polyhedron as in `euler_polyhedron_formula`. Suppose
every 2-dimensional face has exactly `s` edges, exactly `m` edges meet at
every vertex, and every edge lies in exactly two 2-faces, with `s, m ≥ 3`.
Then the Schläfli symbol `(s, m)` belongs to

`{(3,3), (3,4), (3,5), (4,3), (5,3)}`,

a set of cardinality `5`.

`V − E + F = 2` is not a hypothesis. It is `euler_polyhedron_formula`, and
`0 < E` is derived from `s, m ≥ 3` together with the two double-counting
identities. Those identities are proved by counting incident pairs, not
assumed. “Every edge has two vertices” is proved for every polytope edge
(`ncard_vertices_of_edge`).

This is the combinatorial half of the classification of the Platonic solids:
the only possible face/vertex symbols are the five classical ones.

It is not the theorem that there are exactly five geometrically regular
solids in `ℝ³`. That statement is not proved here, for four reasons.

* No geometric icosahedron `{3,5}` or dodecahedron `{5,3}` is constructed.
  Integer `(V,E,F)` solutions for those two symbols live in `Platonic.lean`;
  they are not embeddings.
* A realization is not proved unique up to similarity.
* Metric regularity — congruent regular polygonal faces, equal dihedral
  angles, a flag-transitive symmetry group — is not formalized.
  `MetricRegular.lean` only records equal edge lengths and vertices on a
  sphere for the tetrahedron, the cube, and the octahedron.
* “Every edge lies in two faces” is still a hypothesis. It is proved for
  those three solids, and it is not derived from `IsPolytope` alone.

Mathlib has no Platonic or Schläfli type. The polytope vocabulary is the
same as in Euler's formula. `Platonic.facesOfDim p d` is the set of faces of
affine dimension `d`, definitionally
`{f | IsFaceOf p f ∧ affDim f = d}`.
-/
theorem platonic_schlafli_classification
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nonempty E]
    {p : Set E} {s m : ℕ}
    (hHedron : IsPolyhedron p)
    (hP : IsPolytope p)
    (hdim : affDim p = 3)
    (hEdim : Module.finrank ℝ E = 3)
    (hs : 3 ≤ s) (hm : 3 ≤ m)
    (hface_edges : ∀ f ∈ Platonic.facesOfDim p 2,
      {e ∈ Platonic.facesOfDim p 1 | e ⊆ f}.ncard = s)
    (hedge_faces : ∀ e ∈ Platonic.facesOfDim p 1,
      {f ∈ Platonic.facesOfDim p 2 | e ⊆ f}.ncard = 2)
    (hvert_edges : ∀ v ∈ Platonic.facesOfDim p 0,
      {e ∈ Platonic.facesOfDim p 1 | v ⊆ e}.ncard = m) :
    (s, m) ∈ ({(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)} : Finset (ℕ × ℕ)) ∧
      ({(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)} : Finset (ℕ × ℕ)).card = 5 := by
  obtain ⟨H, hH, hp⟩ := hHedron
  refine ⟨?_, by decide⟩
  simpa [Platonic.schlafliPairs] using
    Platonic.schlafli_pair_mem_of_regular_polytope hH hp hP hdim hEdim hs hm
      hface_edges hedge_faces hvert_edges

end Results
