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
import EulersGem.PlanarTriangulation
import EulersGem.FanDisk

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

* Existence of a triangulation for an arbitrary simple lattice polygon
  (combinatorial fan existence for `n ≥ 3` landed in `FanDiskTriangulation`;
  geometric fan + algebraic shoelace identity + empty-interior Pick-form under
  fan-primitivity hyps landed in `LatticeFan.lean`; general existence /
  `empty⇒|det|=1` still open).
* Discharge of handshaking `2E = 3T + B` from a *geometric* incidence structure
  (combinatorial discharge landed in `PlanarTriangulation.lean` —
  `CombinatorialDiskTriangulation.two_E_eq_three_T_add_B`; unit-square witness
  is wired below; general polygons still open).
* Discharge of `hEuler_planar` for general polygons (unit square + fan disks
  `n ≥ 3` + disk-count axioms proved in `PlanarTriangulation.lean`;
  general EP→planar from `Euler_Poincare_full` still open).
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

/-- **Witness + combinatorial disk triangulation ⇒ shoelace Pick-form**
(handshaking discharged; Euler still EP-spine hyp).

If a geometric `PrimitiveLatticeTriangulationWitness` is paired with a
`CombinatorialDiskTriangulation` sharing `T` and `B` (`#boundaryEdges = W.B`),
handshaking is proved from incidence. `hEuler_planar` remains the open EP
discharge. **Not classical Pick.** -/
theorem shoelace_pick_form_of_witness_of_combinatorial_disk
    (W : PrimitiveLatticeTriangulationWitness)
    {α : Type*} [DecidableEq α]
    (G : CombinatorialDiskTriangulation α)
    (hT : G.T = W.T)
    (hB : G.B = W.B)
    (V F : ℤ)
    (hV : V = (W.I : ℤ) + W.B)
    (hF : F = (W.T : ℤ) + 1)
    (hEuler_planar : V - (G.E : ℤ) + F = 2) :
    W.shoelaceArea = (W.I : ℚ) + (W.B : ℚ) / 2 - 1 := by
  have hshake : (2 : ℤ) * G.E = 3 * (W.T : ℤ) + W.B := by
    have h := G.two_E_eq_three_T_add_B_int
    -- h : 2 * G.E = 3 * G.T + G.B
    rw [hT, hB] at h
    exact h
  exact W.shoelace_eq_I_add_B_div_two_sub_one V G.E F hV hF hEuler_planar hshake

/-- **Witness + combinatorial disk + disk-count axioms ⇒ shoelace Pick-form**
(handshaking **and** planar Euler discharged).

If a geometric witness pairs with a `CombinatorialDiskTriangulation` sharing
`T` and `B`, and the triangulation satisfies classical disk counts
`V = I + B` and `T = 2I + B − 2`, then planar Euler follows from
`planar_euler_of_disk_counts` (no free `hEuler_planar`). **Not classical Pick**
(existence / measure / general EP still open). -/
theorem shoelace_pick_form_of_witness_of_disk_counts
    (W : PrimitiveLatticeTriangulationWitness)
    {α : Type*} [DecidableEq α]
    (G : CombinatorialDiskTriangulation α)
    (hT : G.T = W.T)
    (hB : G.B = W.B)
    (hV : G.V = W.I + G.B)
    (hTshape : G.T + 2 = 2 * W.I + G.B) :
    W.shoelaceArea = (W.I : ℚ) + (W.B : ℚ) / 2 - 1 := by
  have hEuler : (G.V : ℤ) - (G.E : ℤ) + ((G.T : ℤ) + 1) = 2 := by
    simpa [CombinatorialDiskTriangulation.planarCounts,
      PlanarDiskEulerCounts.eulerChar, PlanarDiskEulerCounts.hF] using
      G.planar_euler_of_disk_counts W.I hV hTshape
  have hV' : (G.V : ℤ) = (W.I : ℤ) + W.B := by
    omega
  have hF : ((G.T : ℤ) + 1) = (W.T : ℤ) + 1 := by
    omega
  exact shoelace_pick_form_of_witness_of_combinatorial_disk
    W G hT hB (G.V : ℤ) ((G.T : ℤ) + 1) hV' hF hEuler

/-! ## Unit square: geometric witness ↔ combinatorial disk (Euler discharged)

Concrete bridge: a `PrimitiveLatticeTriangulationWitness` for the unit square
pairs with `UnitSquareTriangulation.unitSquare`, so
`shoelace_pick_form_of_witness_of_combinatorial_disk` applies with **proved**
planar Euler (no free `hEuler_planar`). **Not classical Pick** — one polygon
only; shoelace ≠ Haar; audit remains FAIL.
-/

namespace UnitSquareWitness

open UnitSquareTriangulation

/-- Unit square as a cyclic lattice polygon. -/
def polygon : LatticePolygon :=
  ⟨[v00, v10, v11, v01], by decide⟩

def tLowerTri : Triangle := ⟨v00, v10, v11⟩
def tUpperTri : Triangle := ⟨v00, v11, v01⟩

private lemma tLowerTri_primitive : tLowerTri.IsDetPrimitive := by
  unfold Triangle.IsDetPrimitive Triangle.det latticeDet tLowerTri v00 v10 v11
  decide

private lemma tUpperTri_primitive : tUpperTri.IsDetPrimitive := by
  unfold Triangle.IsDetPrimitive Triangle.det latticeDet tUpperTri v00 v11 v01
  decide

/-- Geometric primitive triangulation witness for the unit square. -/
def witness : PrimitiveLatticeTriangulationWitness where
  polygon := polygon
  triangles := {tLowerTri, tUpperTri}
  primitive := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact tLowerTri_primitive
    · exact tUpperTri_primitive
  verts_in_poly := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact ⟨polygon.mem_latticePointsInConvexHull_of_mem_vertices (by native_decide),
        polygon.mem_latticePointsInConvexHull_of_mem_vertices (by native_decide),
        polygon.mem_latticePointsInConvexHull_of_mem_vertices (by native_decide)⟩
    · exact ⟨polygon.mem_latticePointsInConvexHull_of_mem_vertices (by native_decide),
        polygon.mem_latticePointsInConvexHull_of_mem_vertices (by native_decide),
        polygon.mem_latticePointsInConvexHull_of_mem_vertices (by native_decide)⟩
  area_additivity := by
    have hnin : tLowerTri ∉ ({tUpperTri} : Finset Triangle) := by native_decide
    have hsum :
        ∑ t ∈ ({tLowerTri, tUpperTri} : Finset Triangle), t.shoelace =
          tLowerTri.shoelace + tUpperTri.shoelace := by
      rw [Finset.sum_insert hnin, Finset.sum_singleton]
    change polygon.shoelace = ∑ t ∈ ({tLowerTri, tUpperTri} : Finset Triangle), t.shoelace
    rw [hsum]
    native_decide
  interior := ∅
  interior_mem := by
    intro p hp
    cases hp

theorem witness_I : witness.I = 0 := by native_decide
theorem witness_B : witness.B = 4 := by native_decide
theorem witness_T : witness.T = 2 := by native_decide
theorem witness_shoelace : witness.shoelaceArea = 1 := by native_decide

theorem witness_T_eq_unitSquare : unitSquare.T = witness.T := by native_decide
theorem witness_B_eq_unitSquare : unitSquare.B = witness.B := by native_decide

/-- Witness ↔ combinatorial disk: shared `T` and `B`. -/
theorem witness_matches_unitSquare_disk :
    unitSquare.T = witness.T ∧ unitSquare.B = witness.B :=
  ⟨witness_T_eq_unitSquare, witness_B_eq_unitSquare⟩

/-- **Unit-square shoelace Pick-form with planar Euler discharged** (not classical Pick).

Uses combinatorial disk + disk-count axioms (`V = I + B`, `T = 2I + B − 2`)
so Euler is discharged by `planar_euler_of_disk_counts`. No free
`hEuler_planar`. Still not classical Pick: one polygon, shoelace not Haar,
no general existence. -/
theorem shoelace_pick_form_unit_square :
    witness.shoelaceArea = (witness.I : ℚ) + (witness.B : ℚ) / 2 - 1 := by
  have hV : unitSquare.V = witness.I + unitSquare.B := by native_decide
  have hTshape : unitSquare.T + 2 = 2 * witness.I + unitSquare.B := by native_decide
  exact shoelace_pick_form_of_witness_of_disk_counts
    witness unitSquare witness_T_eq_unitSquare witness_B_eq_unitSquare hV hTshape

end UnitSquareWitness

/-- Convenience export: unit-square shoelace Pick-form (Euler discharged). -/
theorem shoelace_pick_form_of_unit_square :
    UnitSquareWitness.witness.shoelaceArea =
      (UnitSquareWitness.witness.I : ℚ) + (UnitSquareWitness.witness.B : ℚ) / 2 - 1 :=
  UnitSquareWitness.shoelace_pick_form_unit_square


end Picks
end EulersGem
