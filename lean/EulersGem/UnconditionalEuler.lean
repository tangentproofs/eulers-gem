/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Codex
-/
import EulersGem.Embed
import EulersGem.PolytopeHalfspaces

/-!
# Euler's formula from a finite vertex presentation

The finite-halfspace representation theorem discharges the presentation
hypotheses of the original Euler proof. The counts use `IsFaceOf` and `affDim`,
with finiteness supplied by `facesOfDim_finite_of_isPolytope`.
-/

namespace EulersGem

section Ambient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A full-dimensional polytope in positive ambient dimension has Euler
characteristic one, without a supplied halfspace presentation. -/
theorem Euler_Poincare_of_isPolytope {p : Set E} (hp : IsPolytope p)
    (hdim : affDim p = Module.finrank ℝ E) (hn : 1 ≤ Module.finrank ℝ E) :
    faceEulerSum p (Module.finrank ℝ E) = 1 := by
  obtain ⟨H, hH, hrep⟩ := hp.isPolyhedron
  exact Euler_Poincare_full hH hrep hp hdim hn

/-- Euler's relation for a convex polytope in a three-dimensional ambient
space, without a supplied halfspace presentation. -/
theorem euler_relation_of_isPolytope {p : Set E} (hp : IsPolytope p)
    (hdim : affDim p = 3) (hE : Module.finrank ℝ E = 3) :
    ({f : Set E | IsFaceOf p f ∧ affDim f = 0}.ncard : ℤ) -
      ({f : Set E | IsFaceOf p f ∧ affDim f = 1}.ncard : ℤ) +
      ({f : Set E | IsFaceOf p f ∧ affDim f = 2}.ncard : ℤ) = 2 := by
  obtain ⟨H, hH, hrep⟩ := hp.isPolyhedron
  exact euler_relation_convex_3polytope hH hrep hp hdim hE

end Ambient

/-- Euler's polyhedron formula in real three-space. Its only geometric
hypotheses are a finite convex hull and affine dimension three. -/
theorem euler_polyhedron {p : Set (EuclideanSpace ℝ (Fin 3))}
    (hp : IsPolytope p) (hdim : affDim p = 3) :
    ({f : Set (EuclideanSpace ℝ (Fin 3)) | IsFaceOf p f ∧ affDim f = 0}.ncard : ℤ) -
      ({f : Set (EuclideanSpace ℝ (Fin 3)) | IsFaceOf p f ∧ affDim f = 1}.ncard : ℤ) +
      ({f : Set (EuclideanSpace ℝ (Fin 3)) | IsFaceOf p f ∧ affDim f = 2}.ncard : ℤ) = 2 :=
  euler_relation_of_isPolytope hp hdim (by simp)

end EulersGem
