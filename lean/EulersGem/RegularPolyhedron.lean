/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.R3Geometry
import EulersGem.PlatonicOfEuler

/-!
# Regular convex polyhedra in `ℝ³`

The definitions used by the Platonic classification. See
`lean/PLATONIC_CLASSIFICATION_DESIGN.md` for why these and not others.

* faces are the repository's `IsFaceOf` (extreme + convex), graded by `affDim`;
* a **flag** of `P` is a vertex ⊆ edge ⊆ facet, i.e. faces of dimension `0 ⊆ 1 ⊆ 2`;
* a **symmetry** is an isometry of `ℝ³` (`AffineIsometryEquiv`, translations allowed)
  mapping `P` onto itself;
* `P` is a **regular polyhedron** if it is a convex polytope (hull of finitely many points)
  of affine dimension `3` whose symmetries act transitively on flags.

Flag-transitivity is the standard modern definition (Coxeter, McMullen–Schulte). For convex
polyhedra it is classically equivalent to Euclid's "congruent regular faces, the same number at
every vertex" (that equivalence is not formalized in this repository), but it is the cleaner
formal statement: it says nothing about angles or lengths, so the metric shape is entirely a
*consequence*.

Flag-transitivity is a universal statement over flags, so on its own it would hold vacuously
for a set with no flags; non-vacuity for a given `P` comes from its face counts (for the five
solids, `HasFaceData`), and in the classification from `FaceLatticeFacts.exists_flag`.
-/

open Set
open scoped RealInnerProductSpace

namespace EulersGem

open Platonic (facesOfDim)

/-- A flag of `P`: a vertex inside an edge inside a facet. -/
def IsFlag (P : Set R3) (v e f : Set R3) : Prop :=
  v ∈ facesOfDim P 0 ∧ e ∈ facesOfDim P 1 ∧ f ∈ facesOfDim P 2 ∧ v ⊆ e ∧ e ⊆ f

/-- **Regular convex polyhedron.** A three-dimensional convex polytope in `ℝ³` whose isometry
group is transitive on flags. -/
def IsRegularPolyhedron (P : Set R3) : Prop :=
  IsPolytope P ∧ affDim P = 3 ∧
    ∀ v e f v' e' f', IsFlag P v e f → IsFlag P v' e' f' →
      ∃ g : R3 ≃ᵃⁱ[ℝ] R3, g '' P = P ∧ g '' v = v' ∧ g '' e = e' ∧ g '' f = f'

/-- `Q` is similar to `P`: an isometry followed by a positive scaling about the origin. -/
def Similar (P Q : Set R3) : Prop :=
  ∃ g : R3 ≃ᵃⁱ[ℝ] R3, ∃ r : ℝ, 0 < r ∧ Q = (fun x => r • x) '' (g '' P)

end EulersGem
