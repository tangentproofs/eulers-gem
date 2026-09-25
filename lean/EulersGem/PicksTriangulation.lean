/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import Mathlib.Tactic
import Mathlib.Data.Rat.Defs
import EulersGem.Picks
import EulersGem.LatticeTriangle
import EulersGem.LatticePolygon

/-!
# Primitive lattice triangulation witness (EP-spine Pick substrate)

**Architecture (Michal, hard constraint):** Pick must be a corollary that
discharges Euler from the Euler–Poincaré root
(`Euler_Poincare_full` / `euler_relation_convex_3polytope`, or a planar/spherical
instance derived from it) — **not** a free `V−E+F=2` on bare `ℤ` counters via
Ehrhart or other bypasses.

This file provides:

1. A **geometric** `PrimitiveLatticeTriangulationWitness` whose fields are
   lattice triangles (`IsDetPrimitive`), vertex containment in the polygon's
   convex-hull lattice points, and shoelace-area additivity.
2. A theorem: given such a witness **plus** planar Euler + handshaking
   hypotheses (named `hEuler_planar` / `hshake`, to be discharged later from
   the EP spine), conclude
   `shoelace = I + B/2 − 1`.

**Honesty / still open:**

* Existence of a triangulation for an arbitrary simple lattice polygon.
* Discharge of `hEuler_planar` from `Euler_Poincare_full` (disk / sphere /
  planar complex).
* Discharge of handshaking `2E = 3T + B` from a planar graph API.
* Shoelace = Haar/Lebesgue measure.
* Classical Pick's theorem (gated by `PICKS_CLAUDE_AUDIT.md`).

Identifiers deliberately avoid claiming classical Pick.
-/

namespace EulersGem
namespace Picks

open LatticeTriangle
open LatticePolygon

/-- Geometric witness for a det-primitive triangulation of a lattice polygon.

Fields are geometric (triangles, primitivity, vertex containment, shoelace
additivity). Does **not** assert triangulation existence for all polygons —
supplying a witness is the caller's obligation.

Euler / handshaking are **not** fields here: they must arrive as EP-spine
hypotheses on theorems that consume this witness. -/
structure PrimitiveLatticeTriangulationWitness where
  /-- Underlying cyclic lattice polygon. -/
  polygon : LatticePolygon
  /-- Det-primitive triangles of the triangulation. -/
  triangles : Finset Triangle
  /-- Every triangle has `|det| = 1`. -/
  primitive : ∀ t ∈ triangles, t.IsDetPrimitive
  /-- Each triangle vertex lies among the polygon's convex-hull lattice points. -/
  verts_in_poly :
    ∀ t ∈ triangles,
      t.a ∈ polygon.latticePointsInConvexHull ∧
        t.b ∈ polygon.latticePointsInConvexHull ∧
          t.c ∈ polygon.latticePointsInConvexHull
  /-- Polygon shoelace equals the sum of triangle shoelaces
  (area additivity as a witness field — not proved from measure theory). -/
  area_additivity : polygon.shoelace = ∑ t ∈ triangles, t.shoelace
  /-- Finite set of interior lattice points (convex-hull interpretation of `I`).
  Caller supplies a Finset of points from `polygon.interiorLatticePoints`. -/
  interior : Finset (ℤ × ℤ)
  /-- Every listed interior point lies in the geometric interior set. -/
  interior_mem : ∀ p ∈ interior, p ∈ polygon.interiorLatticePoints

namespace PrimitiveLatticeTriangulationWitness

variable (W : PrimitiveLatticeTriangulationWitness)

/-- Interior points are off the constructive boundary. -/
theorem interior_not_mem_boundary {p : ℤ × ℤ} (hp : p ∈ W.interior) :
    p ∉ W.polygon.boundaryLatticePoints :=
  (W.interior_mem p hp).2

/-- Geometric boundary Finset from the polygon. -/
def boundary : Finset (ℤ × ℤ) := W.polygon.boundaryLatticePoints

/-- Geometric `B`. -/
def B : ℕ := W.boundary.card

/-- Geometric `I` (cardinality of the witness interior Finset). -/
def I : ℕ := W.interior.card

/-- Number of triangles `T`. -/
def T : ℕ := W.triangles.card

/-- Polygon shoelace area. -/
def shoelaceArea : ℚ := W.polygon.shoelace

/-- From primitivity: shoelace area equals `T/2`. -/
theorem shoelaceArea_eq_T_div_two : W.shoelaceArea = (W.T : ℚ) / 2 := by
  have hsum := sum_shoelace_eq_card_div_two W.triangles W.primitive
  calc
    W.shoelaceArea = ∑ t ∈ W.triangles, t.shoelace := W.area_additivity
    _ = (W.triangles.card : ℚ) / 2 := hsum
    _ = (W.T : ℚ) / 2 := by rfl

/-- **Witness-conditional Pick-shaped identity on the EP spine.**

Given a geometric primitive triangulation witness, and

* `hV` : `V = I + B` (vertex split — combinatorial from lattice point partition
  when interior/boundary are proved disjoint and exhaustive; here a hyp),
* `hF` : `F = T + 1` (one unbounded outer face),
* `hEuler_planar` : `V − E + F = 2` — **must eventually be discharged from
  `Euler_Poincare_full` / a planar or spherical instance of the EP root;
  not a free bare-ℤ Euler claim**,
* `hshake` : `2E = 3T + B` (triangulation handshaking — planar graph API open),

conclude `shoelace = I + B/2 − 1`.

**Not classical Pick:** triangulation existence, EP→planar Euler discharge,
handshaking proof, and shoelace=measure remain open. See
`PICKS_CLAUDE_AUDIT.md`. -/
theorem shoelace_eq_I_add_B_div_two_sub_one
    (V E F : ℤ)
    (hV : V = (W.I : ℤ) + W.B)
    (hF : F = (W.T : ℤ) + 1)
    (hEuler_planar : V - E + F = 2)
    (hshake : 2 * E = 3 * (W.T : ℤ) + W.B) :
    W.shoelaceArea = (W.I : ℚ) + (W.B : ℚ) / 2 - 1 := by
  have harea : W.shoelaceArea = (W.T : ℚ) / 2 := W.shoelaceArea_eq_T_div_two
  exact triangulation_count_identity W.I W.B V E W.T F W.shoelaceArea
    hV hF hEuler_planar hshake harea

end PrimitiveLatticeTriangulationWitness

/-- Convenience export: same statement without the namespace prefix. -/
theorem shoelace_pick_form_of_primitive_triangulation_witness
    (W : PrimitiveLatticeTriangulationWitness)
    (V E F : ℤ)
    (hV : V = (W.I : ℤ) + W.B)
    (hF : F = (W.T : ℤ) + 1)
    (hEuler_planar : V - E + F = 2)
    (hshake : 2 * E = 3 * (W.T : ℤ) + W.B) :
    W.shoelaceArea = (W.I : ℚ) + (W.B : ℚ) / 2 - 1 :=
  W.shoelace_eq_I_add_B_div_two_sub_one V E F hV hF hEuler_planar hshake

end Picks
end EulersGem
