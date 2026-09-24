# Lean roadmap (Paulson-first)

1. **Done (scaffold):** simplex face counts; `eulerChar_simplex = 0`; tetrahedron numbers;
   Results.lean + comparator script.
2. **Next:** Mathlib survey — what exists for hyperplanes, half-spaces, polyhedra,
   cell complexes, Euler characteristic?
3. **Port Paulson substrate:** `hyperplane_side` / arrangement cells / cell complexes;
   define Euler characteristic; prove refinement invariance.
4. **Cones → polytopes:** Euler relation for full-dimensional proper polyhedral cones;
   then `Euler_Poincare_full` analogue.
5. **Specialize:** convex 3-polytope ⇒ `V - E + F = 2`; re-export from Results.lean
   only when proved.
6. **Cross-check:** against vendored AFP under `../isabelle/` once ported.
7. **Parked:** Pick's theorem; Platonic solids constructions.

Alternate Tverberg path (Poly100-notes) is documented under `../isabelle/` only.
