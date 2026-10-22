/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.RegularCombinatorics

/-!
# The classification of regular polyhedra — with its gaps quarantined

**This file contains `sorry` on purpose.** It lives in its own `lean_lib` (`PlatonicGaps`), is
not imported by `EulersGem` or `Results`, and is outside the axiom audit. It records exactly
what is still missing for the full classical theorem:

> every regular convex polyhedron in `ℝ³` is similar to one of the five Platonic solids.

The proved part (no `sorry`):
* `five_platonic_solids_exist`: the five solids are constructed and are regular, with the
  classical face data;
* `IsRegularPolyhedron.faceData`: a regular polyhedron satisfying the general 3-polytope facts
  `FaceLatticeFacts` has one of the five classical `(s, m, V, E, F)`;
* `platonic_pairwise_not_similar`: the five are pairwise non-similar.

The two gaps:
1. `GAP_faceLatticeFacts`: general face-lattice facts of convex 3-polytopes (no regularity).
2. `GAP_rigidity`: two regular polyhedra with the same face data are similar.

`#print axioms regular_polyhedron_classification` shows `sorryAx`, as it must.
-/

namespace EulersGem.PlatonicGaps

open Platonic3

/-- **GAP 1 (face lattice of a 3-polytope; not yet formalized).** Every convex polytope of
affine dimension 3 in `ℝ³` has flags through every vertex and facet, each edge lies in a facet
and in exactly two facets, and each facet has / each vertex meets at least three edges.
Standard: Ziegler, *Lectures on Polytopes*, §2.2; Grünbaum, *Convex Polytopes*, §3.1.
Says nothing about regularity or the five solids. -/
theorem GAP_faceLatticeFacts {P : Set R3} (hP : IsPolytope P) (h3 : affDim P = 3) :
    FaceLatticeFacts P := by
  sorry

/-- **GAP 2 (geometric rigidity; not yet formalized).** Two regular polyhedra with the same
face data `(V, E, F, s, m)` are similar. Classical argument: a regular polyhedron has a centre
equidistant from all vertices, edges and facets; its facets are regular `s`-gons; the
dihedral angle is determined by `{s, m}`; hence the circumradius-to-edge ratio is determined,
and a flag of one is carried to a flag of the other by a similarity, which then matches all
vertices by flag-transitivity. -/
theorem GAP_rigidity {P Q : Set R3} (hP : IsRegularPolyhedron P) (hQ : IsRegularPolyhedron Q)
    {V E F s m : ℕ} (hPd : HasFaceData P V E F s m) (hQd : HasFaceData Q V E F s m) :
    Similar P Q := by
  sorry

/-- **Classification of the regular convex polyhedra (conditional on GAP 1 and GAP 2).**
Every regular convex polyhedron in `ℝ³` is similar to one of the five constructed solids.
Together with `five_platonic_solids_exist` and `platonic_pairwise_not_similar`, there are
exactly five similarity classes. -/
theorem regular_polyhedron_classification {P : Set R3} (hP : IsRegularPolyhedron P) :
    Similar tetrahedron P ∨ Similar cube P ∨ Similar octahedron P ∨ Similar dodecahedron P ∨
      Similar icosahedron P := by
  obtain ⟨t, ht, hd⟩ := hP.faceData (GAP_faceLatticeFacts hP.1 hP.2.1)
  simp only [platonicTypes, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (GAP_rigidity tetrahedron_isRegular hP tetrahedron_faceData hd)
  · exact Or.inr (Or.inl (GAP_rigidity cube_isRegular hP cube_faceData hd))
  · exact Or.inr (Or.inr (Or.inl (GAP_rigidity octahedron_isRegular hP octahedron_faceData hd)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (GAP_rigidity dodecahedron_isRegular hP dodecahedron_faceData hd))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (GAP_rigidity icosahedron_isRegular hP icosahedron_faceData hd))))

end EulersGem.PlatonicGaps
