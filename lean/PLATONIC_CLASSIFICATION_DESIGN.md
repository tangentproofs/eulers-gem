# Platonic solids: construction and classification — design note

Branch `platonic-classification`. Goal: upgrade "Euler's formula leaves five Schläfli pairs"
(`results_five_platonic_solids`) to (1) Lean *constructs* the five solids as convex polytopes
in ℝ³ and proves them regular, and (2) every regular convex polyhedron is similar to one of
them.

## The definition of "regular convex polyhedron"

`EulersGem/RegularPolyhedron.lean`:

```lean
def IsFlag (P : Set R3) (v e f : Set R3) : Prop :=
  v ∈ facesOfDim P 0 ∧ e ∈ facesOfDim P 1 ∧ f ∈ facesOfDim P 2 ∧ v ⊆ e ∧ e ⊆ f

def IsRegularPolyhedron (P : Set R3) : Prop :=
  IsPolytope P ∧ affDim P = 3 ∧
    ∀ v e f v' e' f', IsFlag P v e f → IsFlag P v' e' f' →
      ∃ g : R3 ≃ᵃⁱ[ℝ] R3, g '' P = P ∧ g '' v = v' ∧ g '' e = e' ∧ g '' f = f'

def Similar (P Q : Set R3) : Prop :=
  ∃ g : R3 ≃ᵃⁱ[ℝ] R3, ∃ r : ℝ, 0 < r ∧ Q = (fun x => r • x) '' (g '' P)
```

* `R3 = EuclideanSpace ℝ (Fin 3)`.
* **Polytope** = convex hull of a finite set (the repo's `IsPolytope`, Isabelle `polytope`).
* **Faces** = the repo's `IsFaceOf` (extreme + convex, Isabelle `face_of`), graded by `affDim`
  — the same notions as the Euler–Poincaré root and `results_five_platonic_solids`, so the new
  statements plug into the old ones without translation. Faces are *not* defined via
  supporting hyperplanes, but we prove (`ExposedFaces.lean`) that for polytopes every
  nonempty face is exposed, so the two notions agree.
* **Regular** = flag-transitive under the full isometry group of ℝ³ (translations,
  reflections allowed). This is the standard modern definition (Coxeter, *Regular
  Polytopes*; McMullen–Schulte). Alternatives considered:
  - Euclid/Cromwell: "faces congruent regular polygons, same number at each vertex". Needs a
    notion of regular polygon and of congruent faces, and the classical caveat that it must
    also be convex; it builds metric facts into the hypothesis.
  - "Congruent regular faces + congruent regular vertex figures": same objection, and vertex
    figures need more face-lattice theory.
  Flag-transitivity says nothing about lengths or angles, so in the classification the whole
  metric shape is a *consequence* — the honest, strongest form. It is equivalent to the
  classical definitions for convex polyhedra, but we do not formalize that equivalence.
* **Similar** = isometry then positive scaling about the origin (every similarity of ℝ³ has
  this form).

## Construction (done, sorry-free)

`EulersGem/PlatonicSolids/*.lean`, summarized in `EulersGem/PlatonicSolids.lean`:
vertices in `ℤ[φ]³` (`φ = Real.goldenRatio`) — tetrahedron (alternate cube corners), cube
`(±1,±1,±1)`, octahedron `±eᵢ`, icosahedron `(0,±1,±φ)` cyclic, dodecahedron
`(±1,±1,±1) ∪ (0,±φ⁻¹,±φ)` cyclic.

How the face lattice is proved, not assumed:
1. `ExposedFaces.lean`: every nonempty face of a V-polytope is `conv{v ∈ V | ⟪a,v⟫ = max}`
   (from the repo's V-to-H theorem `IsPolytope.isPolyhedron` + an averaging argument).
2. `ExplicitPolyhedron.lean`: a kernel-evaluated `Bool` checker over exact `ℤ[φ]` arithmetic
   (`ZPhi.lean`, with soundness lemmas `sgn_eq_one` etc.). It checks for **every** triple of
   vertices that the plane through them either separates vertices or cuts out a listed facet;
   for **every** pair that it is a listed edge or that its midpoint is a nonnegative
   combination of the other vertices (a certificate). `Data.face_cases` turns acceptance into:
   every face is ∅, the body, a vertex, a listed edge, or a listed facet.
3. `ExplicitRegular.lean`: dimensions, counts (`ncard`), incidences, and flag-transitivity
   via three reflections (normals in `ℤ[φ]³`) whose vertex permutations are checked, plus a
   table giving each flag as a word in them.
All checks are `decide +kernel`; no `native_decide` (so no `Lean.ofReduceBool` /
`trustCompiler` axioms).

## Classification (conditional; gaps quarantined in `PlatonicGaps.lean`)

Structure: regular ⇒ uniform Schläfli type `{s, m}` ⇒ `(s, m, V, E, F)` one of five (existing
Euler chain) ⇒ similar to the constructed solid of that type.

Proved, sorry-free, in `EulersGem/RegularCombinatorics.lean`:
* `IsRegularPolyhedron.uniform`: symmetries permute faces of each dimension and preserve
  inclusion, so flag-transitivity makes "edges per facet" and "edges per vertex" constant.
* `IsRegularPolyhedron.faceData`: regular + `FaceLatticeFacts P` ⇒ `HasFaceData P V E F s m`
  for one of the five classical tuples in `platonicTypes`.
* `FaceLatticeFacts.of_faceData`, `platonic_faceLatticeFacts`: the hypothesis is not vacuous
  (it holds for the five constructed solids).
* `Similar.ncard_facesOfDim`, `platonic_not_similar`, `platonicSolid_similar_unique`:
  similarity preserves face counts, so the five solids are pairwise non-similar (both
  directions) and a polyhedron is similar to at most one of them.

`uniform`, `faceData` and the `RegularCentre` results below are sorry-free but **assume
`FaceLatticeFacts P`**; they are unconditional only for the five constructed solids.

`FaceLatticeFacts P` collects standard facts about **every** convex 3-polytope (flags exist
through every vertex and facet, each edge lies in exactly two facets, each facet has and each
vertex meets at least three edges). It does not mention regularity, symmetry, metric data or
the five solids, so it does not smuggle in the classification.

Also sorry-free, `EulersGem/RegularCentre.lean` (first metric steps of the rigidity half):
`IsRegularPolyhedron.exists_centre` (the vertex centroid is fixed by every symmetry and all
vertices are equidistant from it), `edges_congruent` (all edges have one length),
`facets_congruent` / `edges_congruent'` (any two facets / edges are exchanged by a symmetry).

Gaps (`sorry`, in the separate `lean_lib PlatonicGaps`, file `lean/PlatonicGaps.lean`, not
imported by `EulersGem` or `Results`, so `scripts/audit-axioms.sh` stays green):
1. `GAP_faceLatticeFacts`: every 3-dimensional polytope in ℝ³ satisfies `FaceLatticeFacts`.
2. `GAP_rigidity`: two regular polyhedra with the same `(V, E, F, s, m)` are similar.

`PlatonicGaps.regular_polyhedron_classification`: every regular polyhedron is similar to one
of the five constructed solids; `regular_polyhedron_classification_unique`: to exactly one
(`∃! i : Fin 5, Similar (platonicSolid i) P`). `#print axioms` shows `sorryAx` (through the two
gaps only). `Similar` is not proved to be an equivalence relation; the uniqueness of the index
does not need it.

Next steps to close the gaps: (1) the diamond property and edge/facet incidences for
3-polytopes, from the exposed-face description; (2) the rigidity argument — common centre of
the vertices (centroid, fixed by all symmetries), regular facets, dihedral angle fixed by
`{s, m}`, then a similarity matching one base flag extends to all vertices by
flag-transitivity.
