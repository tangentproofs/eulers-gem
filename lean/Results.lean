/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.SimplexEuler
import EulersGem.Polyhedron
import EulersGem.EulerPoincare
import EulersGem.ConeSlice
import EulersGem.Embed
import EulersGem.Platonic
import EulersGem.PlatonicOfEuler
import EulersGem.PolytopeFaces
import EulersGem.EdgeVertices
import EulersGem.SimplexFaces
import EulersGem.GeometricPlatonic
import EulersGem.Octahedron
import EulersGem.Cube
import EulersGem.MetricRegular
import EulersGem.Picks
import EulersGem.PicksTriangulation
import EulersGem.PlanarTriangulation
import EulersGem.FanDisk
import EulersGem.LatticeFan
import EulersGem.LatticeFanInterior
import EulersGem.LatticeTriangleEmpty

/-!
# Paper-facing results

Only theorems that are **actually proved** appear here.
Docstrings/names must survive a Claude honesty audit: no classical theorem name
unless the *statement* matches the classical claim (lattice polygon + measure for
Pick; geometric regularity for Platonic; etc.).

## Statement discipline (Mathlib auditability)

* **Mathlib-only statements** (simplex / combinatorial / Platonic / Funkenbusch count identities): the
  *statement* uses only Mathlib vocabulary (`Nat.choose`, `Finset`, `ℤ`, `ℚ`,
  etc.). Proofs may still call `EulersGem.*` lemmas.
* **Geometric Euler–Poincaré** (separate section below): statements still need
  `EulersGem` polytope / face / `affDim` / hyperplane APIs that Mathlib lacks.
  See `MATHLIB_SURVEY.md`.

Phase B (#1535): combinatorial Platonic classification + five Schläfli
constructions, Funkenbusch / triangulation *count identities* (not Pick), and a
**witness-conditional** shoelace Pick-form on the EP spine, plus disk-count Euler discharge and a unit-square case with Euler
discharged from disk axioms (still not classical Pick).
**Classical geometric Pick's theorem is not claimed** — see `Picks.lean`,
`PicksTriangulation.lean`, `PHASE_B_PLAN.md`, `PICKS_CLAUDE_AUDIT.md`.
-/

open scoped RealInnerProductSpace
open Finset

namespace Results

/-! ## Simplex / combinatorial (Mathlib-only statements) -/

/-- Euler characteristic of an `n`-simplex (including the empty face) is `0`.
Isabelle: `euler_0simplex_eq0` / `euler_nsimplex_eq0`.
Statement is the binomial identity
`∑_{c=0}^{n+1} (-1)^c C(n+1,c) = 0`. -/
theorem results_eulerChar_simplex (n : ℕ) :
    ∑ c ∈ range (n + 2), ((-1 : ℤ) ^ c) * ((n + 1).choose c : ℤ) = 0 := by
  simpa [EulersGem.eulerChar] using EulersGem.eulerChar_simplex n

/-- Combinatorial `m`-face count of an `n`-simplex is `C(n+1, m+1)`. -/
theorem results_card_combinatorialFaces (n m : ℕ) :
    (powersetCard (m + 1) (univ : Finset (Fin (n + 1)))).card =
      (n + 1).choose (m + 1) :=
  EulersGem.card_combinatorialFaces n m

/-- Abstract 3-simplex face-count identity: `C(4,1) − C(4,2) + C(4,3) = 2`.
Not a geometric embedded tetrahedron. -/
theorem results_tetrahedron_polyhedron_numbers :
    ((4 : ℕ).choose 1 : ℤ) - (4 : ℕ).choose 2 + (4 : ℕ).choose 3 = 2 := by
  decide

/-- Bookkeeping: Euler char `0` with one empty face and one solid ⇒ polyhedron formula. -/
theorem results_polyhedron_formula_of_eulerChar (V E F : ℕ)
    (h : (1 : ℤ) - V + E - F + 1 = 0) :
    (F : ℤ) + V - E = 2 := by
  omega

/-- Alternating face counts of an abstract `n`-simplex (no empty face) equal `1`.
Paulson / Euler–Poincaré for the simplex: `∑_{d=0}^{n} (-1)^d C(n+1,d+1) = 1`. -/
theorem results_faceEulerSum_simplex_faceCount (n : ℕ) :
    ∑ d ∈ range (n + 1), (-1 : ℤ) ^ d * ((n + 1).choose (d + 1) : ℤ) = 1 := by
  simpa [EulersGem.faceCount] using EulersGem.faceEulerSum_simplex_faceCount n

/-! ## Combinatorial Schläfli / Platonic counts (not geometric regular solids)

These classify integer Schläfli pairs under Euler + double-counting. They do
**not** construct geometrically regular polyhedra in `ℝ³` (embeddings still open).
-/

/-- **Combinatorial Schläfli classification:** any combinatorially regular pair
`(s,m)` with Euler + double-counting lies in the five classical pairs.
Not a theorem about geometric Platonic solids in `ℝ³`. -/
theorem results_platonic_schlafli_classification
    (V E F s m : ℕ)
    (hs : 3 ≤ s) (hm : 3 ≤ m) (hE : 0 < E)
    (hFace : s * F = 2 * E) (hVert : m * V = 2 * E)
    (hEuler : (V : ℤ) - E + F = 2) :
    (s, m) ∈ ({(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)} : Finset (ℕ × ℕ)) := by
  simpa [EulersGem.Platonic.schlafliPairs] using
    EulersGem.Platonic.schlafli_pair_mem
      { V := V, E := E, F := F, s := s, m := m
        hs := hs, hm := hm, hE := hE, hFace := hFace, hVert := hVert
        hEuler := hEuler }

/-- Exactly five admissible Schläfli pairs. -/
theorem results_platonic_schlafli_card :
    ({(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)} : Finset (ℕ × ℕ)).card = 5 := by
  decide

/-- **Five combinatorial `(V,E,F)` witnesses** (Euler bookkeeping): each admissible
Schläfli pair has some `(V,E,F)` satisfying the count equations.
Not geometric regular embeddings. -/
theorem results_platonic_five_constructions :
    ({(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)} : Finset (ℕ × ℕ)).card = 5 ∧
      ∀ p ∈ ({(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)} : Finset (ℕ × ℕ)),
        ∃ (V E F : ℕ),
          3 ≤ p.1 ∧ 3 ≤ p.2 ∧ 0 < E ∧
            p.1 * F = 2 * E ∧ p.2 * V = 2 * E ∧
            (V : ℤ) - E + F = 2 := by
  have h := EulersGem.Platonic.exactly_five_platonic_schlafli
  refine ⟨?card, ?ex⟩
  · decide
  · intro p hp
    have hp' : p ∈ EulersGem.Platonic.schlafliPairs := by
      simpa [EulersGem.Platonic.schlafliPairs] using hp
    obtain ⟨R, hEq⟩ := h.2 p hp'
    have hs : R.s = p.1 := congrArg Prod.fst hEq
    have hm : R.m = p.2 := congrArg Prod.snd hEq
    refine ⟨R.V, R.E, R.F, ?_, ?_, R.hE, ?_, ?_, R.hEuler⟩
    · simpa [← hs] using R.hs
    · simpa [← hm] using R.hm
    · simpa [← hs] using R.hFace
    · simpa [← hm] using R.hVert

/-! ## Funkenbusch / triangulation count identities (not Pick)

Algebraic implications from Euler + Funkenbusch / triangulation handshaking.
**Not** classical Pick's theorem (no lattice polygon, no geometric area, no
triangulation existence). See `PICKS_CLAUDE_AUDIT.md`.
-/

/-- **Funkenbusch count identity** (not Pick):
Euler + `V=I+B` + `E=3I+2B−3` + `A=(F−1)/2` ⇒ `A = I + B/2 − 1`. -/
theorem results_funkenbusch_identity
    (I B V E F : ℤ) (A : ℚ)
    (heuler : V - E + F = 2)
    (hverts : V = I + B)
    (hedges : E = 3 * I + 2 * B - 3)
    (harea : A = ((F : ℚ) - 1) / 2) :
    A = (I : ℚ) + (B : ℚ) / 2 - 1 :=
  EulersGem.Picks.funkenbusch_identity I B V E F A heuler hverts hedges harea

/-- **Triangulation count identity** (not Pick):
`2E=3T+B`, Euler, `V=I+B`, `F=T+1`, `A=T/2` ⇒ `A = I + B/2 − 1`. -/
theorem results_triangulation_count_identity
    (I B V E T F : ℤ) (A : ℚ)
    (hV : V = I + B)
    (hF : F = T + 1)
    (heuler : V - E + F = 2)
    (hshake : 2 * E = 3 * T + B)
    (harea : A = (T : ℚ) / 2) :
    A = (I : ℚ) + (B : ℚ) / 2 - 1 :=
  EulersGem.Picks.triangulation_count_identity I B V E T F A hV hF heuler hshake harea

/-! ## Combinatorial disk triangulation handshaking (not Pick)

Proved from edge–triangle incidence on `CombinatorialDiskTriangulation`.
Discharges the `hshake` hyp of the triangulation count identity when a
combinatorial disk triangulation is supplied. `B` = `#boundaryEdges`.
Planar Euler / triangulation existence / classical Pick remain open.
-/

/-- **Handshaking from incidence** (not Pick):
`2E = 3T + B` for a `CombinatorialDiskTriangulation`. -/
theorem results_handshaking_of_combinatorial_disk_triangulation
    {α : Type*} [DecidableEq α]
    (G : EulersGem.Picks.CombinatorialDiskTriangulation α) :
    2 * G.E = 3 * G.T + G.B :=
  EulersGem.Picks.handshaking_of_combinatorial_disk_triangulation G

/-- **Triangulation count identity with handshaking discharged** (not Pick).

Same conclusion as `results_triangulation_count_identity`, but `2E = 3T + B`
comes from `CombinatorialDiskTriangulation` incidence rather than a free hyp.
Still assumes Euler / `V=I+B` / `F=T+1` / `A=T/2` — EP planar discharge open. -/
theorem results_triangulation_count_identity_of_disk_triangulation
    {α : Type*} [DecidableEq α]
    (G : EulersGem.Picks.CombinatorialDiskTriangulation α)
    (I V F : ℤ) (A : ℚ)
    (hV : V = I + G.B)
    (hF : F = (G.T : ℤ) + 1)
    (heuler : V - G.E + F = 2)
    (harea : A = (G.T : ℚ) / 2) :
    A = (I : ℚ) + (G.B : ℚ) / 2 - 1 :=
  EulersGem.Picks.triangulation_count_identity I G.B V G.E G.T F A
    hV hF heuler G.two_E_eq_three_T_add_B_int harea

/-- Concrete inhabited example: unit-square disk triangulation satisfies handshaking.
Not classical Pick; just shows the incidence API is realizable on a lattice square. -/
theorem results_unit_square_disk_triangulation_handshaking :
    2 * EulersGem.Picks.UnitSquareTriangulation.unitSquare.E =
      3 * EulersGem.Picks.UnitSquareTriangulation.unitSquare.T +
        EulersGem.Picks.UnitSquareTriangulation.unitSquare.B :=
  EulersGem.Picks.UnitSquareTriangulation.unitSquare_handshaking

/-- **Planar Euler for the unit-square disk** (proved, not assumed).
`V−E+F = 2` with `F = T+1`. Concrete planar-disk face of the EP spine identity;
general `Euler_Poincare_full` → planar discharge still open. Not classical Pick. -/
theorem results_unit_square_planar_euler :
    (EulersGem.Picks.UnitSquareTriangulation.unitSquare.planarCounts).eulerChar = 2 :=
  EulersGem.Picks.UnitSquareTriangulation.unitSquare_planar_euler

/-- Fan count identities ⇒ planar Euler (combinatorial face of EP arithmetic). -/
theorem results_planar_disk_euler_of_fan_counts
    (n V E T B F : ℕ)
    (hn : 3 ≤ n)
    (hV : V = n) (hB : B = n) (hT : T = n - 2)
    (hE : E = 2 * n - 3) (hF : F = T + 1) :
    (V : ℤ) - E + F = 2 :=
  EulersGem.Picks.planar_disk_euler_of_fan_counts n V E T B F hn hV hB hT hE hF

/-- Combinatorial fan disk triangulation exists for every `n ≥ 3`. -/
theorem results_exists_fan_disk_triangulation {n : ℕ} (hn : 3 ≤ n) :
    Nonempty (EulersGem.Picks.CombinatorialDiskTriangulation (Fin n)) :=
  EulersGem.Picks.FanDiskTriangulation.exists_fan_disk_triangulation n hn

/-- Planar Euler for the abstract pentagon fan triangulation. -/
theorem results_fan5_planar_euler :
    (EulersGem.Picks.FanDiskTriangulation.fan5.planarCounts).eulerChar = 2 :=
  EulersGem.Picks.FanDiskTriangulation.fan5_planar_euler

/-- Planar Euler for the abstract heptagon fan triangulation. -/
theorem results_fan7_planar_euler :
    (EulersGem.Picks.FanDiskTriangulation.fan7.planarCounts).eulerChar = 2 :=
  EulersGem.Picks.FanDiskTriangulation.fan7_planar_euler

/-- **Planar Euler from handshaking + classical disk counts** (not Pick).

`2E = 3T + B`, `V = I + B`, `T = 2I + B − 2`, `F = T + 1` ⇒ `V − E + F = 2`.
Discharges planar Euler for any combinatorial disk triangulation satisfying
these count axioms — no free `ℤ` Euler hyp. -/
theorem results_planar_disk_euler_of_disk_counts
    (V E T B F I : ℕ)
    (hshake : 2 * E = 3 * T + B)
    (hV : V = I + B)
    (hT : T + 2 = 2 * I + B)
    (hF : F = T + 1) :
    (V : ℤ) - E + F = 2 :=
  EulersGem.Picks.planar_disk_euler_of_disk_counts V E T B F I hshake hV hT hF

/-- Empty-interior specialization: `V = B`, `T = B − 2`. -/
theorem results_planar_disk_euler_of_empty_interior_disk_counts
    (V E T B F : ℕ)
    (hshake : 2 * E = 3 * T + B)
    (hV : V = B)
    (hT : T + 2 = B)
    (hF : F = T + 1) :
    (V : ℤ) - E + F = 2 :=
  EulersGem.Picks.planar_disk_euler_of_empty_interior_disk_counts
    V E T B F hshake hV hT hF

/-! ## Witness-conditional shoelace Pick-form (not classical Pick)

Geometric primitive triangulation witness + EP-spine planar Euler.
**Not** classical Pick — general triangulation existence and general EP→planar
discharge remain open; unit-square case discharges Euler below.
See `PICKS_CLAUDE_AUDIT.md`. Identifiers avoid claiming Pick proved.
-/

/-- **Shoelace Pick-form of a primitive triangulation witness** (not classical Pick).

Given a geometric `PrimitiveLatticeTriangulationWitness` and planar Euler /
handshaking hypotheses (`hEuler_planar` must eventually come from
`Euler_Poincare_full` / a planar EP instance — not a free bare-ℤ Euler claim),
conclude `shoelace = I + B/2 − 1`.

Existence of such a witness for arbitrary simple lattice polygons is open.
Claude audit: do **not** promote to a Pick-named theorem until PASS. -/
theorem results_shoelace_pick_form_of_primitive_triangulation_witness
    (W : EulersGem.Picks.PrimitiveLatticeTriangulationWitness)
    (V E F : ℤ)
    (hV : V = (W.I : ℤ) + W.B)
    (hF : F = (W.T : ℤ) + 1)
    (hEuler_planar : V - E + F = 2)
    (hshake : 2 * E = 3 * (W.T : ℤ) + W.B) :
    W.shoelaceArea = (W.I : ℚ) + (W.B : ℚ) / 2 - 1 :=
  EulersGem.Picks.shoelace_pick_form_of_primitive_triangulation_witness
    W V E F hV hF hEuler_planar hshake

/-- Witness + combinatorial disk triangulation: handshaking discharged from incidence.
Euler still EP-spine hyp. **Not classical Pick.** -/
theorem results_shoelace_pick_form_of_witness_of_combinatorial_disk
    (W : EulersGem.Picks.PrimitiveLatticeTriangulationWitness)
    {α : Type*} [DecidableEq α]
    (G : EulersGem.Picks.CombinatorialDiskTriangulation α)
    (hT : G.T = W.T)
    (hB : G.B = W.B)
    (V F : ℤ)
    (hV : V = (W.I : ℤ) + W.B)
    (hF : F = (W.T : ℤ) + 1)
    (hEuler_planar : V - (G.E : ℤ) + F = 2) :
    W.shoelaceArea = (W.I : ℚ) + (W.B : ℚ) / 2 - 1 :=
  EulersGem.Picks.shoelace_pick_form_of_witness_of_combinatorial_disk
    W G hT hB V F hV hF hEuler_planar

/-- Witness + combinatorial disk + disk-count axioms: handshaking and planar Euler
discharged. **Not classical Pick.** -/
theorem results_shoelace_pick_form_of_witness_of_disk_counts
    (W : EulersGem.Picks.PrimitiveLatticeTriangulationWitness)
    {α : Type*} [DecidableEq α]
    (G : EulersGem.Picks.CombinatorialDiskTriangulation α)
    (hT : G.T = W.T)
    (hB : G.B = W.B)
    (hV : G.V = W.I + G.B)
    (hTshape : G.T + 2 = 2 * W.I + G.B) :
    W.shoelaceArea = (W.I : ℚ) + (W.B : ℚ) / 2 - 1 :=
  EulersGem.Picks.shoelace_pick_form_of_witness_of_disk_counts
    W G hT hB hV hTshape

/-- **Unit-square shoelace Pick-form with planar Euler discharged** (not classical Pick).

Geometric witness + combinatorial disk + proved unit-square planar Euler.
No free `hEuler_planar`. Still not classical Pick (one polygon; shoelace ≠ Haar;
audit FAIL). -/
theorem results_shoelace_pick_form_of_unit_square :
    EulersGem.Picks.UnitSquareWitness.witness.shoelaceArea =
      (EulersGem.Picks.UnitSquareWitness.witness.I : ℚ) +
        (EulersGem.Picks.UnitSquareWitness.witness.B : ℚ) / 2 - 1 :=
  EulersGem.Picks.shoelace_pick_form_of_unit_square


/-- **Algebraic fan shoelace identity** (Nat-indexed; not Pick). -/
theorem results_fan_shoelace_identity (n : ℕ) (hn : 3 ≤ n) (v : ℕ → ℤ × ℤ) :
    ∑ i ∈ Finset.range n,
        EulersGem.Picks.LatticeFan.cross (v i) (v ((i + 1) % n)) =
      ∑ i ∈ Finset.range (n - 2),
        EulersGem.Picks.LatticeFan.latDet (v 0) (v (i + 1)) (v (i + 2)) :=
  EulersGem.Picks.LatticeFan.fan_shoelace_identity n hn v

/-- Polygon shoelace sum equals sum of oriented fan-triangle dets. -/
theorem results_shoelaceSum_eq_sumFanDet (P : EulersGem.Picks.LatticePolygon) :
    P.shoelaceSum = EulersGem.Picks.LatticeFan.sumFanDet P :=
  EulersGem.Picks.LatticeFan.shoelaceSum_eq_sumFanDet P

/-- Primitive boundary edges + distinct vertices ⇒ `B = n`. -/
theorem results_B_eq_nVertices_of_primitive_edges
    (P : EulersGem.Picks.LatticePolygon)
    (hprim : EulersGem.Picks.LatticeFan.PrimitiveEdges P)
    (hverts : Function.Injective P.vertex) :
    P.B = P.nVertices :=
  EulersGem.Picks.LatticeFan.B_eq_nVertices_of_primitive_edges P hprim hverts

/-- **Empty-interior shoelace Pick-form of a primitive fan** (not classical Pick).

Given distinct vertices, primitive edges, CCW fan orientation, and det-primitive
fan triangles: `shoelace = B/2 − 1`. Does **not** prove `empty⇒|det|=1`, Haar
equality, or triangulation existence for arbitrary polygons. -/
theorem results_shoelace_eq_B_div_two_sub_one_of_primitive_fan
    (P : EulersGem.Picks.LatticePolygon)
    (hverts : Function.Injective P.vertex)
    (hedge : EulersGem.Picks.LatticeFan.PrimitiveEdges P)
    (hnn : EulersGem.Picks.LatticeFan.FanDetsNonneg P)
    (hprim : EulersGem.Picks.LatticeFan.FanDetPrimitive P) :
    P.shoelace = (P.B : ℚ) / 2 - 1 :=
  EulersGem.Picks.LatticeFan.shoelace_eq_B_div_two_sub_one_of_primitive_fan
    P hverts hedge hnn hprim

/-- **Empty closed lattice triangle ⇒ `|det|=1`** (nondegenerate; not classical Pick).

Converse of `memClosedTriangle_eq_vertices_of_natAbs_det_eq_one`. Requires `det ≠ 0`
(degenerate collinear triples can be vertex-only with `det = 0`). -/
theorem results_natAbs_det_eq_one_of_memClosedTriangle_eq_vertices
    (a b c : ℤ × ℤ)
    (hne : EulersGem.Picks.LatticeTriangle.latticeDet a b c ≠ 0)
    (h : ∀ p, EulersGem.Picks.LatticeTriangle.MemClosedTriangle a b c p →
      p = a ∨ p = b ∨ p = c) :
    Int.natAbs (EulersGem.Picks.LatticeTriangle.latticeDet a b c) = 1 :=
  EulersGem.Picks.LatticeTriangle.natAbs_det_eq_one_of_memClosedTriangle_eq_vertices
    a b c hne h

/-- Fan-primitivity discharged from empty fan triangles + positive orientation. -/
theorem results_FanDetPrimitive_of_empty_fan_triangles
    (P : EulersGem.Picks.LatticePolygon)
    (hpos : EulersGem.Picks.LatticeFan.FanDetsPos P)
    (hempty : EulersGem.Picks.LatticeFan.FanTrianglesEmpty P) :
    EulersGem.Picks.LatticeFan.FanDetPrimitive P :=
  EulersGem.Picks.LatticeFan.FanDetPrimitive_of_empty_fan_triangles P hpos hempty

/-- Empty-fan shoelace Pick-form with primitivity discharged (not classical Pick). -/
theorem results_shoelace_eq_B_div_two_sub_one_of_empty_fan
    (P : EulersGem.Picks.LatticePolygon)
    (hverts : Function.Injective P.vertex)
    (hedge : EulersGem.Picks.LatticeFan.PrimitiveEdges P)
    (hpos : EulersGem.Picks.LatticeFan.FanDetsPos P)
    (hempty : EulersGem.Picks.LatticeFan.FanTrianglesEmpty P) :
    P.shoelace = (P.B : ℚ) / 2 - 1 :=
  EulersGem.Picks.LatticeFan.shoelace_eq_B_div_two_sub_one_of_empty_fan
    P hverts hedge hpos hempty



/-- Primitive edges ⇒ constructive boundary equals the listed vertex set. -/
theorem results_boundaryLatticePoints_eq_vertexFinset
    (P : EulersGem.Picks.LatticePolygon)
    (hprim : EulersGem.Picks.LatticeFan.PrimitiveEdges P)
    (hverts : Function.Injective P.vertex) :
    P.boundaryLatticePoints = P.vertexFinset :=
  EulersGem.Picks.LatticeFan.boundaryLatticePoints_eq_vertexFinset P hprim hverts

/-- **Prize (partial):** empty interior + primitive edges + extreme vertices ⇒
fan ears contain only their three vertices as lattice points (not classical Pick). -/
theorem results_FanTrianglesEmpty_of_empty_interior
    (P : EulersGem.Picks.LatticePolygon)
    (hverts : Function.Injective P.vertex)
    (hedge : EulersGem.Picks.LatticeFan.PrimitiveEdges P)
    (hI : EulersGem.Picks.LatticeFan.EmptyInterior P)
    (hext : EulersGem.Picks.LatticeFan.VerticesExtreme P) :
    EulersGem.Picks.LatticeFan.FanTrianglesEmpty P :=
  EulersGem.Picks.LatticeFan.FanTrianglesEmpty_of_empty_interior P hverts hedge hI hext

/-- Empty-interior shoelace Pick-form with `FanTrianglesEmpty` discharged from
`I=∅` + extreme vertices + CCW fan + primitive edges (not classical Pick). -/
theorem results_shoelace_eq_B_div_two_sub_one_of_empty_interior
    (P : EulersGem.Picks.LatticePolygon)
    (hverts : Function.Injective P.vertex)
    (hedge : EulersGem.Picks.LatticeFan.PrimitiveEdges P)
    (hpos : EulersGem.Picks.LatticeFan.FanDetsPos P)
    (hI : EulersGem.Picks.LatticeFan.EmptyInterior P)
    (hext : EulersGem.Picks.LatticeFan.VerticesExtreme P) :
    P.shoelace = (P.B : ℚ) / 2 - 1 :=
  EulersGem.Picks.LatticeFan.shoelace_eq_B_div_two_sub_one_of_empty_interior
    P hverts hedge hpos hI hext

/-- Strict CCW convexity ⇒ listed vertices are extreme in the vertex hull. -/
theorem results_VerticesExtreme_of_strictlyConvexCCW
    (P : EulersGem.Picks.LatticePolygon)
    (hsc : EulersGem.Picks.LatticeFan.StrictlyConvexCCW P)
    (hinj : Function.Injective P.vertex) :
    EulersGem.Picks.LatticeFan.VerticesExtreme P :=
  EulersGem.Picks.LatticeFan.VerticesExtreme_of_strictlyConvexCCW P hsc hinj

/-- Fan dets nonnegative from CCW edge half-planes. -/
theorem results_FanDetsNonneg_of_ConvexCCW
    (P : EulersGem.Picks.LatticePolygon)
    (h : EulersGem.Picks.LatticeFan.ConvexCCW P) :
    EulersGem.Picks.LatticeFan.FanDetsNonneg P :=
  EulersGem.Picks.LatticeFan.FanDetsNonneg_of_ConvexCCW P h

/-- Fan dets strictly positive from `StrictlyConvexCCW` + injective vertices. -/
theorem results_FanDetsPos_of_strictlyConvexCCW
    (P : EulersGem.Picks.LatticePolygon)
    (hsc : EulersGem.Picks.LatticeFan.StrictlyConvexCCW P)
    (hinj : Function.Injective P.vertex) :
    EulersGem.Picks.LatticeFan.FanDetsPos P :=
  EulersGem.Picks.LatticeFan.FanDetsPos_of_strictlyConvexCCW P hsc hinj

/-- Empty-interior shoelace Pick-form with `VerticesExtreme` and `FanDetsPos`
discharged from `StrictlyConvexCCW` (not classical Pick). -/
theorem results_shoelace_eq_B_div_two_sub_one_of_empty_interior_convex
    (P : EulersGem.Picks.LatticePolygon)
    (hverts : Function.Injective P.vertex)
    (hedge : EulersGem.Picks.LatticeFan.PrimitiveEdges P)
    (hI : EulersGem.Picks.LatticeFan.EmptyInterior P)
    (hsc : EulersGem.Picks.LatticeFan.StrictlyConvexCCW P) :
    P.shoelace = (P.B : ℚ) / 2 - 1 :=
  EulersGem.Picks.LatticeFan.shoelace_eq_B_div_two_sub_one_of_empty_interior_convex
    P hverts hedge hI hsc


/-! ### Interior-fan I=1 shoelace Pick-form (not classical Pick)

Fan from an interior lattice apex to each boundary edge. Algebraic identity
`∑ det(q,vᵢ,vᵢ₊₁) = shoelaceSum` is unconditional. Both `InteriorFanDetsPos` and
`InteriorFanTrianglesEmpty` discharge from `UniqueInterior` + `StrictlyConvexCCW` +
injective + `PrimitiveEdges`. Fully geometric I=1 form: `shoelace = 1 + B/2 − 1`.
Not Haar; classical Pick FAIL.
-/

/-- Unconditional algebraic identity: interior-fan dets sum to polygon shoelace sum. -/
theorem results_sum_interiorFanDet_eq_shoelaceSum
    (P : EulersGem.Picks.LatticePolygon) (q : ℤ × ℤ) :
    (∑ i : Fin P.nVertices,
        EulersGem.Picks.LatticeFan.InteriorFan.interiorFanDet P q i) =
      P.shoelaceSum :=
  EulersGem.Picks.LatticeFan.InteriorFan.sum_interiorFanDet_eq_shoelaceSum P q

/-- Interior-fan primitivity from empty ears + positive orientation. -/
theorem results_InteriorFanDetPrimitive_of_empty
    (P : EulersGem.Picks.LatticePolygon) (q : ℤ × ℤ)
    (hpos : EulersGem.Picks.LatticeFan.InteriorFan.InteriorFanDetsPos P q)
    (hempty : EulersGem.Picks.LatticeFan.InteriorFan.InteriorFanTrianglesEmpty P q) :
    EulersGem.Picks.LatticeFan.InteriorFan.InteriorFanDetPrimitive P q :=
  EulersGem.Picks.LatticeFan.InteriorFan.InteriorFanDetPrimitive_of_empty P hpos hempty

/-- **I = 1 shoelace Pick-form** via interior fan (not classical Pick).

Hyps: injective vertices, primitive edges, positively oriented empty fan from an
interior apex. Concludes `shoelace = 1 + B/2 − 1`. -/
theorem results_shoelace_eq_I_add_B_div_two_sub_one_of_interior_fan
    (P : EulersGem.Picks.LatticePolygon) (q : ℤ × ℤ)
    (hverts : Function.Injective P.vertex)
    (hedge : EulersGem.Picks.LatticeFan.PrimitiveEdges P)
    (hpos : EulersGem.Picks.LatticeFan.InteriorFan.InteriorFanDetsPos P q)
    (hempty : EulersGem.Picks.LatticeFan.InteriorFan.InteriorFanTrianglesEmpty P q) :
    P.shoelace = (1 : ℚ) + (P.B : ℚ) / 2 - 1 :=
  EulersGem.Picks.LatticeFan.InteriorFan.shoelace_eq_I_add_B_div_two_sub_one_of_interior_fan
    P hverts hedge hpos hempty

/-- `InteriorFanDetsPos` from unique interior + strict CCW + primitive edges. -/
theorem results_InteriorFanDetsPos_of_uniqueInterior
    (P : EulersGem.Picks.LatticePolygon) (q : ℤ × ℤ)
    (hsc : EulersGem.Picks.LatticeFan.StrictlyConvexCCW P)
    (hinj : Function.Injective P.vertex)
    (hedge : EulersGem.Picks.LatticeFan.PrimitiveEdges P)
    (hU : EulersGem.Picks.LatticeFan.InteriorFan.UniqueInterior P q) :
    EulersGem.Picks.LatticeFan.InteriorFan.InteriorFanDetsPos P q :=
  EulersGem.Picks.LatticeFan.InteriorFan.InteriorFanDetsPos_of_uniqueInterior
    P hsc hinj hedge hU

/-- **I = 1 shoelace Pick-form** with `InteriorFanDetsPos` discharged from
`UniqueInterior` + `StrictlyConvexCCW` (not classical Pick).

Still takes `InteriorFanTrianglesEmpty` as an optional hyp; prefer the fully
geometric form `results_shoelace_eq_I_add_B_div_two_sub_one_of_uniqueInterior`. -/
theorem results_shoelace_eq_I_add_B_div_two_sub_one_of_uniqueInterior_of_empty
    (P : EulersGem.Picks.LatticePolygon) (q : ℤ × ℤ)
    (hverts : Function.Injective P.vertex)
    (hedge : EulersGem.Picks.LatticeFan.PrimitiveEdges P)
    (hsc : EulersGem.Picks.LatticeFan.StrictlyConvexCCW P)
    (hU : EulersGem.Picks.LatticeFan.InteriorFan.UniqueInterior P q)
    (hempty : EulersGem.Picks.LatticeFan.InteriorFan.InteriorFanTrianglesEmpty P q) :
    P.shoelace = (1 : ℚ) + (P.B : ℚ) / 2 - 1 :=
  EulersGem.Picks.LatticeFan.InteriorFan.shoelace_eq_I_add_B_div_two_sub_one_of_uniqueInterior_of_empty
    P hverts hedge hsc hU hempty

/-- `InteriorFanTrianglesEmpty` from unique interior + strict CCW + primitive edges. -/
theorem results_InteriorFanTrianglesEmpty_of_uniqueInterior
    (P : EulersGem.Picks.LatticePolygon) (q : ℤ × ℤ)
    (hsc : EulersGem.Picks.LatticeFan.StrictlyConvexCCW P)
    (hinj : Function.Injective P.vertex)
    (hedge : EulersGem.Picks.LatticeFan.PrimitiveEdges P)
    (hU : EulersGem.Picks.LatticeFan.InteriorFan.UniqueInterior P q) :
    EulersGem.Picks.LatticeFan.InteriorFan.InteriorFanTrianglesEmpty P q :=
  EulersGem.Picks.LatticeFan.InteriorFan.InteriorFanTrianglesEmpty_of_uniqueInterior
    P hsc hinj hedge hU

/-- **I = 1 shoelace Pick-form** with fan hyps discharged from geometric assumptions
(not classical Pick).

Hyps: injective vertices, primitive edges, `StrictlyConvexCCW`, unique interior
lattice point. Concludes `shoelace = 1 + B/2 − 1`. No `InteriorFanTrianglesEmpty`
hyp. Still shoelace ≠ Haar; classical Pick FAIL. -/
theorem results_shoelace_eq_I_add_B_div_two_sub_one_of_uniqueInterior
    (P : EulersGem.Picks.LatticePolygon) (q : ℤ × ℤ)
    (hverts : Function.Injective P.vertex)
    (hedge : EulersGem.Picks.LatticeFan.PrimitiveEdges P)
    (hsc : EulersGem.Picks.LatticeFan.StrictlyConvexCCW P)
    (hU : EulersGem.Picks.LatticeFan.InteriorFan.UniqueInterior P q) :
    P.shoelace = (1 : ℚ) + (P.B : ℚ) / 2 - 1 :=
  EulersGem.Picks.LatticeFan.InteriorFan.shoelace_eq_I_add_B_div_two_sub_one_of_uniqueInterior
    P hverts hedge hsc hU

/-- Barycentric closed triangle ⇒ Euclidean convex hull of the three vertices. -/
theorem results_mem_convexHull_of_memClosedTriangle
    (a b c p : ℤ × ℤ)
    (h : EulersGem.Picks.LatticeTriangle.MemClosedTriangle a b c p) :
    EulersGem.Picks.LatticeTriangle.toReal p ∈
      convexHull ℝ
        ({EulersGem.Picks.LatticeTriangle.toReal a,
          EulersGem.Picks.LatticeTriangle.toReal b,
          EulersGem.Picks.LatticeTriangle.toReal c} : Set (ℝ × ℝ)) :=
  EulersGem.Picks.LatticeTriangle.mem_convexHull_of_memClosedTriangle a b c p h

/-! ## Geometric Euler–Poincaré (needs polytope API missing from Mathlib)

Mathlib lacks IsPolytope / polytope face_of / set-level affDim / hyperplane
arrangements / combinatorial faceEulerSum. Until those exist upstream, these
statements use EulersGem substrate. See MATHLIB_SURVEY.md.
-/

/-- Bookkeeping: `faceEulerSum p 3 = 1` with unique solid 3-face ⇒ `V − E + F = 2`.
Paulson `Euler_relation` arithmetic (geometric discharge of hypotheses still open
for general convex 3-polytopes). -/
theorem results_euler_relation_of_faceEulerSum
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : Set E) (V E_ F : ℕ)
    (hsum : EulersGem.faceEulerSum p 3 = 1)
    (hV : ({f : Set E | EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 0}.ncard) = V)
    (hE : ({f : Set E | EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 1}.ncard) = E_)
    (hF : ({f : Set E | EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 2}.ncard) = F)
    (hSolid : ({f : Set E | EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 3}.ncard) = 1) :
    (V : ℤ) - E_ + F = 2 :=
  EulersGem.euler_relation_of_faceEulerSum p V E_ F hsum hV hE hF hSolid

/-- Height-1 H-rep polytope (with trivial homogenized height-0 section and nonempty open dual):
Paulson `Euler_Poincare_lemma` — `faceEulerSum p (finrank - 1) = 1`. -/
theorem results_faceEulerSum_of_height_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nonempty E]
    {H : Set (EulersGem.Hyperplane E)} {i : E} {p : Set E}
    (hH : H.Finite)
    (hp : p = ⋂ h ∈ H, EulersGem.closedHalfspace h.1 h.2)
    (hht : ∀ x ∈ p, ⟪i, x⟫ = 1) (hpne : p.Nonempty) (hConv : Convex ℝ p)
    (h0sec : ∀ y, y ∈ (⋂ a ∈ EulersGem.homogenizeNormals H i, EulersGem.closedHalfspace a 0) →
      ⟪i, y⟫ = 0 → y = 0)
    (hpos : ({x : E | ∀ a ∈ EulersGem.homogenizeNormals H i \ ({0} : Set E), 0 < ⟪a, x⟫}).Nonempty)
    (hn : 1 ≤ Module.finrank ℝ E) :
    EulersGem.faceEulerSum p (Module.finrank ℝ E - 1) = 1 :=
  EulersGem.faceEulerSum_of_height_one_polytope hH hp hht hpne hConv h0sec hpos hn

/-- Paulson `Euler_Poincare_full`: full-dimensional H-rep polytope has `faceEulerSum = 1`. -/
theorem results_Euler_Poincare_full
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nonempty E]
    {H : Set (EulersGem.Hyperplane E)} {p : Set E}
    (hH : H.Finite)
    (hp : p = ⋂ h ∈ H, EulersGem.closedHalfspace h.1 h.2)
    (hP : EulersGem.IsPolytope p)
    (hdim : EulersGem.affDim p = Module.finrank ℝ E)
    (hn : 1 ≤ Module.finrank ℝ E) :
    EulersGem.faceEulerSum p (Module.finrank ℝ E) = 1 :=
  EulersGem.Euler_Poincare_full hH hp hP hdim hn

/-- Geometric `V − E + F = 2` for a full-dimensional convex 3-polytope (H+V-rep). -/
theorem results_euler_relation_convex_3polytope
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nonempty E]
    {H : Set (EulersGem.Hyperplane E)} {p : Set E}
    (hH : H.Finite)
    (hp : p = ⋂ h ∈ H, EulersGem.closedHalfspace h.1 h.2)
    (hP : EulersGem.IsPolytope p)
    (hdim : EulersGem.affDim p = 3)
    (hE : Module.finrank ℝ E = 3) :
    ({f : Set E | EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 0}.ncard : ℤ) -
      ({f : Set E | EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 1}.ncard : ℤ) +
      ({f : Set E | EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 2}.ncard : ℤ) = 2 :=
  EulersGem.euler_relation_convex_3polytope hH hp hP hdim hE

/-! ## Geometric Platonic on the Euler–Poincaré spine

Unlike `results_platonic_schlafli_classification` above (which takes Euler as a bare `ℤ`
hypothesis), the theorems in this section obtain `V − E + F = 2` from
`EulersGem.Euler_Poincare_full` via `euler_relation_convex_3polytope`, and prove the
double-counting identities from face-lattice incidence. Statements use the `EulersGem`
polytope/face API that Mathlib lacks (see `MATHLIB_SURVEY.md`).

Honesty: `results_platonic_schlafli_geometric` still assumes one *polytope fact* as an
incidence hypothesis — every edge lies in two 2-faces (the diamond property) — on top of the
genuine regularity hypotheses. "Every edge has two vertices" used to be assumed as well and is
now **proved** (`results_edge_has_two_vertices`). The diamond property is proved for each of
the three geometric solids below, so the hypothesis is not vacuous. Two of the five solids
still have no geometric construction. See `PLATONIC_CLAUDE_AUDIT.md`.
-/

/-- A polytope has finitely many faces (`F ↦ V ∩ F` is injective on faces). -/
theorem results_polytope_faces_finite
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {p : Set E} (hP : EulersGem.IsPolytope p) :
    {f : Set E | EulersGem.IsFaceOf p f}.Finite :=
  EulersGem.faces_finite_of_isPolytope hP

/-- A face of a V-polytope is the convex hull of the generators it contains. -/
theorem results_face_eq_convexHull_inter
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {V F : Set E} (hF : EulersGem.IsFaceOf (convexHull ℝ V) F) :
    F = convexHull ℝ (V ∩ F) :=
  EulersGem.face_eq_convexHull_inter hF

/-- **An edge of a polytope has exactly two vertices.** A `1`-dimensional face of a polytope
contains exactly two `0`-dimensional faces: a one-dimensional convex hull of finitely many
points is a segment, and its extreme points are its two ends. Used to be a hypothesis of the
Platonic classification. -/
theorem results_edge_has_two_vertices
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {p : Set E} (hP : EulersGem.IsPolytope p) {e : Set E}
    (he : EulersGem.IsFaceOf p e) (hdim : EulersGem.affDim e = 1) :
    {w : Set E | (EulersGem.IsFaceOf p w ∧ EulersGem.affDim w = 0) ∧ w ⊆ e}.ncard = 2 :=
  EulersGem.ncard_vertices_of_edge hP he hdim

/-- **Platonic count equations for a geometric regular convex 3-polytope, Euler from EP.**
`s·F = 2·E` and `m·V = 2·E` are proved by double counting over face incidence; `V − E + F = 2`
is discharged from `euler_relation_convex_3polytope`. No bare Euler hypothesis. -/
theorem results_platonic_counts_geometric
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nonempty E]
    {H : Set (EulersGem.Hyperplane E)} {p : Set E} {s m : ℕ}
    (hH : H.Finite)
    (hp : p = ⋂ h ∈ H, EulersGem.closedHalfspace h.1 h.2)
    (hP : EulersGem.IsPolytope p)
    (hdim : EulersGem.affDim p = 3)
    (hEdim : Module.finrank ℝ E = 3)
    (hface_edges : ∀ f ∈ EulersGem.Platonic.facesOfDim p 2,
      {e ∈ EulersGem.Platonic.facesOfDim p 1 | e ⊆ f}.ncard = s)
    (hedge_faces : ∀ e ∈ EulersGem.Platonic.facesOfDim p 1,
      {f ∈ EulersGem.Platonic.facesOfDim p 2 | e ⊆ f}.ncard = 2)
    (hvert_edges : ∀ v ∈ EulersGem.Platonic.facesOfDim p 0,
      {e ∈ EulersGem.Platonic.facesOfDim p 1 | v ⊆ e}.ncard = m) :
    s * (EulersGem.Platonic.facesOfDim p 2).ncard
        = 2 * (EulersGem.Platonic.facesOfDim p 1).ncard ∧
      m * (EulersGem.Platonic.facesOfDim p 0).ncard
        = 2 * (EulersGem.Platonic.facesOfDim p 1).ncard ∧
      ((EulersGem.Platonic.facesOfDim p 0).ncard : ℤ)
        - (EulersGem.Platonic.facesOfDim p 1).ncard
        + (EulersGem.Platonic.facesOfDim p 2).ncard = 2 :=
  EulersGem.Platonic.regular_polytope_counts hH hp hP hdim hEdim
    hface_edges hedge_faces hvert_edges

/-- **Schläfli classification with Euler discharged from Euler–Poincaré.**
A combinatorially regular convex 3-polytope (every 2-face an `s`-gon, `m` edges at each
vertex, `s,m ≥ 3`) has `(s,m)` among the five classical pairs — and Euler's relation is
*not* assumed here, it comes from `Euler_Poincare_full`. `0 < E` is derived too.

Not a claim about metrically regular solids, and not a classification of geometric solids:
see `PLATONIC_CLAUDE_AUDIT.md`. -/
theorem results_platonic_schlafli_geometric
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nonempty E]
    {H : Set (EulersGem.Hyperplane E)} {p : Set E} {s m : ℕ}
    (hH : H.Finite)
    (hp : p = ⋂ h ∈ H, EulersGem.closedHalfspace h.1 h.2)
    (hP : EulersGem.IsPolytope p)
    (hdim : EulersGem.affDim p = 3)
    (hEdim : Module.finrank ℝ E = 3)
    (hs : 3 ≤ s) (hm : 3 ≤ m)
    (hface_edges : ∀ f ∈ EulersGem.Platonic.facesOfDim p 2,
      {e ∈ EulersGem.Platonic.facesOfDim p 1 | e ⊆ f}.ncard = s)
    (hedge_faces : ∀ e ∈ EulersGem.Platonic.facesOfDim p 1,
      {f ∈ EulersGem.Platonic.facesOfDim p 2 | e ⊆ f}.ncard = 2)
    (hvert_edges : ∀ v ∈ EulersGem.Platonic.facesOfDim p 0,
      {e ∈ EulersGem.Platonic.facesOfDim p 1 | v ⊆ e}.ncard = m) :
    (s, m) ∈ ({(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)} : Finset (ℕ × ℕ)) := by
  simpa [EulersGem.Platonic.schlafliPairs] using
    EulersGem.Platonic.schlafli_pair_mem_of_regular_polytope hH hp hP hdim hEdim hs hm
      hface_edges hedge_faces hvert_edges

/-! ### The geometric tetrahedron

`EulersGem.Simplex.body b` is the convex hull of the four affinely independent points of an
affine basis `b : AffineBasis (Fin 4) ℝ E` — i.e. an arbitrary geometric tetrahedron in an
arbitrary 3-dimensional real inner product space. Its face lattice is computed in
`SimplexFaces.lean`, so all hypotheses below are discharged.
-/

/-- **The number of `d`-faces of a geometric `n`-simplex is `C(n+1, d+1)`.**
The *geometric* face counts (`IsFaceOf` + `affDim`) of the convex hull of `n+1` affinely
independent points match the combinatorial face counts of the abstract `n`-simplex. -/
theorem results_geometric_simplex_face_counts
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (b : AffineBasis (Fin (n + 1)) ℝ E) (d : ℕ) :
    (EulersGem.Platonic.facesOfDim (EulersGem.Simplex.body b) (d : ℤ)).ncard
      = (n + 1).choose (d + 1) :=
  (EulersGem.Simplex.geometric_simplex_euler_poincare b).1 d

/-- **Euler–Poincaré for a geometric simplex in every dimension.** For the convex hull of
`n+1` affinely independent points, the alternating sum of its geometric face counts is `1`.
This is the geometric counterpart of `results_faceEulerSum_simplex_faceCount`. -/
theorem results_geometric_simplex_euler_poincare
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (b : AffineBasis (Fin (n + 1)) ℝ E) :
    ∑ d ∈ range (n + 1),
      (-1 : ℤ) ^ d * ((EulersGem.Platonic.facesOfDim (EulersGem.Simplex.body b) (d : ℤ)).ncard : ℤ)
      = 1 :=
  (EulersGem.Simplex.geometric_simplex_euler_poincare b).2

/-- **Geometric tetrahedron face counts: `V = 4`, `E = 6`, `F = 4`.**
These count geometric faces (`IsFaceOf` + `affDim`), computed from the simplex face lattice. -/
theorem results_tetrahedron_face_counts
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nonempty E]
    (b : AffineBasis (Fin 4) ℝ E) :
    (EulersGem.Platonic.facesOfDim (EulersGem.Simplex.body b) 0).ncard = 4 ∧
      (EulersGem.Platonic.facesOfDim (EulersGem.Simplex.body b) 1).ncard = 6 ∧
      (EulersGem.Platonic.facesOfDim (EulersGem.Simplex.body b) 2).ncard = 4 :=
  EulersGem.Simplex.tetrahedron_face_counts b

/-- **`V − E + F = 2` for a geometric tetrahedron, from Euler–Poincaré.**
Discharged: no Euler hypothesis, no assumed face counts, no assumed incidence. -/
theorem results_tetrahedron_euler_relation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nonempty E]
    (b : AffineBasis (Fin 4) ℝ E) (hE : Module.finrank ℝ E = 3) :
    ((EulersGem.Platonic.facesOfDim (EulersGem.Simplex.body b) 0).ncard : ℤ)
        - (EulersGem.Platonic.facesOfDim (EulersGem.Simplex.body b) 1).ncard
        + (EulersGem.Platonic.facesOfDim (EulersGem.Simplex.body b) 2).ncard = 2 :=
  EulersGem.Simplex.tetrahedron_euler_relation b hE

/-- **A geometric tetrahedron is Platonic `{3,3}` on the Euler–Poincaré spine.**
Double-counting identities from face incidence, Euler from `Euler_Poincare_full`, and
`(3,3)` among the five Schläfli pairs. Every hypothesis of the general classification is
discharged for this solid, which is what makes those hypotheses non-vacuous. -/
theorem results_tetrahedron_platonic
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nonempty E]
    (b : AffineBasis (Fin 4) ℝ E) (hE : Module.finrank ℝ E = 3) :
    3 * (EulersGem.Platonic.facesOfDim (EulersGem.Simplex.body b) 2).ncard
        = 2 * (EulersGem.Platonic.facesOfDim (EulersGem.Simplex.body b) 1).ncard ∧
      3 * (EulersGem.Platonic.facesOfDim (EulersGem.Simplex.body b) 0).ncard
        = 2 * (EulersGem.Platonic.facesOfDim (EulersGem.Simplex.body b) 1).ncard ∧
      ((EulersGem.Platonic.facesOfDim (EulersGem.Simplex.body b) 0).ncard : ℤ)
        - (EulersGem.Platonic.facesOfDim (EulersGem.Simplex.body b) 1).ncard
        + (EulersGem.Platonic.facesOfDim (EulersGem.Simplex.body b) 2).ncard = 2 ∧
      ((3 : ℕ), (3 : ℕ)) ∈ ({(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)} : Finset (ℕ × ℕ)) := by
  obtain ⟨h1, h2, h3, -⟩ := EulersGem.Simplex.tetrahedron_platonic b hE
  exact ⟨h1, h2, h3, by decide⟩

/-- Every 3-dimensional real inner product space contains a geometric tetrahedron, so the
statements above are not about an empty class. -/
theorem results_exists_tetrahedron
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hE : Module.finrank ℝ E = 3) :
    Nonempty (AffineBasis (Fin 4) ℝ E) :=
  EulersGem.Simplex.exists_tetrahedron hE


/-! ### The geometric octahedron

`EulersGem.Octahedron.body b` is the cross-polytope `convexHull ℝ {±b i}` of an orthonormal
basis `b : OrthonormalBasis (Fin 3) ℝ E` — a geometric octahedron. Its face lattice is
computed in `Octahedron.lean` (faces = partial sign assignments, plus the body), so all
hypotheses below are discharged. This is the first solid here whose face lattice is *not* a
subset lattice.
-/

/-- **Geometric octahedron face counts: `V = 6`, `E = 12`, `F = 8`.** -/
theorem results_octahedron_face_counts
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis (Fin 3) ℝ E) :
    (EulersGem.Platonic.facesOfDim (EulersGem.Octahedron.body b) 0).ncard = 6 ∧
      (EulersGem.Platonic.facesOfDim (EulersGem.Octahedron.body b) 1).ncard = 12 ∧
      (EulersGem.Platonic.facesOfDim (EulersGem.Octahedron.body b) 2).ncard = 8 :=
  EulersGem.Octahedron.octahedron_face_counts b

/-- **`V − E + F = 2` for a geometric octahedron, from Euler–Poincaré.** -/
theorem results_octahedron_euler_relation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis (Fin 3) ℝ E) :
    ((EulersGem.Platonic.facesOfDim (EulersGem.Octahedron.body b) 0).ncard : ℤ)
        - (EulersGem.Platonic.facesOfDim (EulersGem.Octahedron.body b) 1).ncard
        + (EulersGem.Platonic.facesOfDim (EulersGem.Octahedron.body b) 2).ncard = 2 :=
  EulersGem.Octahedron.octahedron_euler_relation b

/-- **A geometric octahedron is Platonic `{3,4}` on the Euler–Poincaré spine.**
Double counting from face incidence, Euler from `Euler_Poincare_full`, and `(3,4)` among the
five Schläfli pairs. -/
theorem results_octahedron_platonic
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis (Fin 3) ℝ E) :
    3 * (EulersGem.Platonic.facesOfDim (EulersGem.Octahedron.body b) 2).ncard
        = 2 * (EulersGem.Platonic.facesOfDim (EulersGem.Octahedron.body b) 1).ncard ∧
      4 * (EulersGem.Platonic.facesOfDim (EulersGem.Octahedron.body b) 0).ncard
        = 2 * (EulersGem.Platonic.facesOfDim (EulersGem.Octahedron.body b) 1).ncard ∧
      ((EulersGem.Platonic.facesOfDim (EulersGem.Octahedron.body b) 0).ncard : ℤ)
        - (EulersGem.Platonic.facesOfDim (EulersGem.Octahedron.body b) 1).ncard
        + (EulersGem.Platonic.facesOfDim (EulersGem.Octahedron.body b) 2).ncard = 2 ∧
      ((3 : ℕ), (4 : ℕ)) ∈ ({(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)} : Finset (ℕ × ℕ)) := by
  obtain ⟨h1, h2, h3, -⟩ := EulersGem.Octahedron.octahedron_platonic b
  exact ⟨h1, h2, h3, by decide⟩

/-- Every 3-dimensional real inner product space contains a geometric octahedron. -/
theorem results_exists_octahedron
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hE : Module.finrank ℝ E = 3) :
    Nonempty (OrthonormalBasis (Fin 3) ℝ E) :=
  EulersGem.Octahedron.exists_octahedron_basis hE

/-- **Two of the five Platonic solids, geometrically, with Euler from EP.**
The Schläfli pairs `{3,3}` (tetrahedron) and `{3,4}` (octahedron) are each realized by a
geometric solid whose face counts, incidence counts and Euler relation are all proved.
The remaining three pairs — `{3,5}`, `{4,3}`, `{5,3}` — have no geometric construction here;
see `PLATONIC_CLAUDE_AUDIT.md`. This is **not** a classification of geometric solids. -/
theorem results_two_geometric_platonic_solids
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nonempty E] (hE : Module.finrank ℝ E = 3)
    (b : AffineBasis (Fin 4) ℝ E) (o : OrthonormalBasis (Fin 3) ℝ E) :
    (((EulersGem.Platonic.facesOfDim (EulersGem.Simplex.body b) 0).ncard : ℤ)
        - (EulersGem.Platonic.facesOfDim (EulersGem.Simplex.body b) 1).ncard
        + (EulersGem.Platonic.facesOfDim (EulersGem.Simplex.body b) 2).ncard = 2) ∧
      (((EulersGem.Platonic.facesOfDim (EulersGem.Octahedron.body o) 0).ncard : ℤ)
        - (EulersGem.Platonic.facesOfDim (EulersGem.Octahedron.body o) 1).ncard
        + (EulersGem.Platonic.facesOfDim (EulersGem.Octahedron.body o) 2).ncard = 2) ∧
      ((3 : ℕ), (3 : ℕ)) ∈ ({(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)} : Finset (ℕ × ℕ)) ∧
      ((3 : ℕ), (4 : ℕ)) ∈ ({(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)} : Finset (ℕ × ℕ)) :=
  ⟨EulersGem.Simplex.tetrahedron_euler_relation b hE,
    EulersGem.Octahedron.octahedron_euler_relation o,
    by decide, by decide⟩


/-! ### The geometric cube

`EulersGem.Cube.body b` is the convex hull of the `2^3` sign vectors `∑ ±b i` of an
orthonormal basis — a geometric cube. Its face lattice is the *subcube* lattice; the hard
direction (every face is a subcube) is `Cube.eq_face_of_isFaceOf`, proved by coordinate
transfer. All hypotheses below are discharged.
-/

/-- **Geometric cube face counts: `V = 8`, `E = 12`, `F = 6`.** -/
theorem results_cube_face_counts
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis (Fin 3) ℝ E) :
    (EulersGem.Platonic.facesOfDim (EulersGem.Cube.body b) 0).ncard = 8 ∧
      (EulersGem.Platonic.facesOfDim (EulersGem.Cube.body b) 1).ncard = 12 ∧
      (EulersGem.Platonic.facesOfDim (EulersGem.Cube.body b) 2).ncard = 6 :=
  EulersGem.Cube.cube_face_counts b

/-- **`V − E + F = 2` for a geometric cube, from Euler–Poincaré.** -/
theorem results_cube_euler_relation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis (Fin 3) ℝ E) :
    ((EulersGem.Platonic.facesOfDim (EulersGem.Cube.body b) 0).ncard : ℤ)
        - (EulersGem.Platonic.facesOfDim (EulersGem.Cube.body b) 1).ncard
        + (EulersGem.Platonic.facesOfDim (EulersGem.Cube.body b) 2).ncard = 2 :=
  EulersGem.Cube.cube_euler_relation b

/-- **A geometric cube is Platonic `{4,3}` on the Euler–Poincaré spine.** -/
theorem results_cube_platonic
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis (Fin 3) ℝ E) :
    4 * (EulersGem.Platonic.facesOfDim (EulersGem.Cube.body b) 2).ncard
        = 2 * (EulersGem.Platonic.facesOfDim (EulersGem.Cube.body b) 1).ncard ∧
      3 * (EulersGem.Platonic.facesOfDim (EulersGem.Cube.body b) 0).ncard
        = 2 * (EulersGem.Platonic.facesOfDim (EulersGem.Cube.body b) 1).ncard ∧
      ((EulersGem.Platonic.facesOfDim (EulersGem.Cube.body b) 0).ncard : ℤ)
        - (EulersGem.Platonic.facesOfDim (EulersGem.Cube.body b) 1).ncard
        + (EulersGem.Platonic.facesOfDim (EulersGem.Cube.body b) 2).ncard = 2 ∧
      ((4 : ℕ), (3 : ℕ)) ∈ ({(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)} : Finset (ℕ × ℕ)) := by
  obtain ⟨h1, h2, h3, -⟩ := EulersGem.Cube.cube_platonic b
  exact ⟨h1, h2, h3, by decide⟩

/-! ### Metric regularity: equilateral solids

The face-lattice results above are *combinatorial* regularity. These add the first metric
content: vertices on a sphere and all edges of equal length — in particular a genuinely
**regular** tetrahedron. Full metric regularity (congruent regular faces, flag-transitive
symmetry group) is still not formalized; see `PLATONIC_CLAUDE_AUDIT.md`.
-/

/-- **All edges of a geometric octahedron have the same length** (squared length `2`), and all
its vertices lie on the unit sphere. -/
theorem results_octahedron_equilateral
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis (Fin 3) ℝ E) :
    (∀ p : Fin 3 × Bool, ‖EulersGem.Octahedron.vtx b p‖ ^ 2 = 1) ∧
      (∀ c : Fin 3 → Option Bool, ∀ p ∈ EulersGem.Octahedron.vtxIdx c,
        ∀ q ∈ EulersGem.Octahedron.vtxIdx c, p ≠ q →
          ‖EulersGem.Octahedron.vtx b p - EulersGem.Octahedron.vtx b q‖ ^ 2 = 2) :=
  ⟨EulersGem.Octahedron.norm_sq_vtx b,
    fun _ _ hp _ hq hpq => EulersGem.Octahedron.edges_equilateral b hp hq hpq⟩

/-- **A regular tetrahedron is Platonic `{3,3}` on the Euler–Poincaré spine.**

`EulersGem.Cube.regularTetra b hE` is the tetrahedron on four alternating corners of the cube.
Its four vertices are pairwise equidistant (squared distance `8`) and lie on a sphere (squared
radius `3`); its geometric face counts are `4, 6, 4`; `V − E + F = 2` comes from
`Euler_Poincare_full`; and `(3,3)` is one of the five Schläfli pairs. -/
theorem results_regular_tetrahedron_platonic
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis (Fin 3) ℝ E) (hE : Module.finrank ℝ E = 3) :
    (∀ k l : Fin 4, k ≠ l →
        ‖EulersGem.Cube.regularTetra b hE k - EulersGem.Cube.regularTetra b hE l‖ ^ 2 = 8) ∧
      (∀ k : Fin 4, ‖EulersGem.Cube.regularTetra b hE k‖ ^ 2 = 3) ∧
      (EulersGem.Platonic.facesOfDim
        (EulersGem.Simplex.body (EulersGem.Cube.regularTetra b hE)) 0).ncard = 4 ∧
      (EulersGem.Platonic.facesOfDim
        (EulersGem.Simplex.body (EulersGem.Cube.regularTetra b hE)) 1).ncard = 6 ∧
      (EulersGem.Platonic.facesOfDim
        (EulersGem.Simplex.body (EulersGem.Cube.regularTetra b hE)) 2).ncard = 4 ∧
      ((EulersGem.Platonic.facesOfDim
          (EulersGem.Simplex.body (EulersGem.Cube.regularTetra b hE)) 0).ncard : ℤ)
        - (EulersGem.Platonic.facesOfDim
          (EulersGem.Simplex.body (EulersGem.Cube.regularTetra b hE)) 1).ncard
        + (EulersGem.Platonic.facesOfDim
          (EulersGem.Simplex.body (EulersGem.Cube.regularTetra b hE)) 2).ncard = 2 ∧
      ((3 : ℕ), (3 : ℕ)) ∈ ({(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)} : Finset (ℕ × ℕ)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := EulersGem.Cube.regularTetra_platonic b hE
  exact ⟨h1, h2, h3, h4, h5, h6, by decide⟩

/-- **Three of the five Platonic solids, geometrically, with Euler from EP.**

For any 3-dimensional real inner product space: the tetrahedron on an affine basis, and the
octahedron and cube on an orthonormal basis, each have their *geometric* face counts
computed, satisfy `V − E + F = 2` obtained from `Euler_Poincare_full`, and realize the
Schläfli pairs `{3,3}`, `{3,4}`, `{4,3}` respectively.

**Not** a classification of geometric solids: `{3,5}` (icosahedron) and `{5,3}`
(dodecahedron) have no geometric construction in this development, and metric regularity is
not formalized. See `PLATONIC_CLAUDE_AUDIT.md`. -/
theorem results_three_geometric_platonic_solids
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nonempty E] (hE : Module.finrank ℝ E = 3)
    (t : AffineBasis (Fin 4) ℝ E) (o : OrthonormalBasis (Fin 3) ℝ E) :
    ((EulersGem.Platonic.facesOfDim (EulersGem.Simplex.body t) 0).ncard = 4 ∧
        (EulersGem.Platonic.facesOfDim (EulersGem.Simplex.body t) 1).ncard = 6 ∧
        (EulersGem.Platonic.facesOfDim (EulersGem.Simplex.body t) 2).ncard = 4) ∧
      ((EulersGem.Platonic.facesOfDim (EulersGem.Octahedron.body o) 0).ncard = 6 ∧
        (EulersGem.Platonic.facesOfDim (EulersGem.Octahedron.body o) 1).ncard = 12 ∧
        (EulersGem.Platonic.facesOfDim (EulersGem.Octahedron.body o) 2).ncard = 8) ∧
      ((EulersGem.Platonic.facesOfDim (EulersGem.Cube.body o) 0).ncard = 8 ∧
        (EulersGem.Platonic.facesOfDim (EulersGem.Cube.body o) 1).ncard = 12 ∧
        (EulersGem.Platonic.facesOfDim (EulersGem.Cube.body o) 2).ncard = 6) ∧
      (((EulersGem.Platonic.facesOfDim (EulersGem.Simplex.body t) 0).ncard : ℤ)
          - (EulersGem.Platonic.facesOfDim (EulersGem.Simplex.body t) 1).ncard
          + (EulersGem.Platonic.facesOfDim (EulersGem.Simplex.body t) 2).ncard = 2) ∧
      (((EulersGem.Platonic.facesOfDim (EulersGem.Octahedron.body o) 0).ncard : ℤ)
          - (EulersGem.Platonic.facesOfDim (EulersGem.Octahedron.body o) 1).ncard
          + (EulersGem.Platonic.facesOfDim (EulersGem.Octahedron.body o) 2).ncard = 2) ∧
      (((EulersGem.Platonic.facesOfDim (EulersGem.Cube.body o) 0).ncard : ℤ)
          - (EulersGem.Platonic.facesOfDim (EulersGem.Cube.body o) 1).ncard
          + (EulersGem.Platonic.facesOfDim (EulersGem.Cube.body o) 2).ncard = 2) ∧
      (((3 : ℕ), (3 : ℕ)) ∈ ({(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)} : Finset (ℕ × ℕ)) ∧
        ((3 : ℕ), (4 : ℕ)) ∈ ({(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)} : Finset (ℕ × ℕ)) ∧
        ((4 : ℕ), (3 : ℕ)) ∈ ({(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)} : Finset (ℕ × ℕ))) :=
  ⟨EulersGem.Simplex.tetrahedron_face_counts t,
    EulersGem.Octahedron.octahedron_face_counts o,
    EulersGem.Cube.cube_face_counts o,
    EulersGem.Simplex.tetrahedron_euler_relation t hE,
    EulersGem.Octahedron.octahedron_euler_relation o,
    EulersGem.Cube.cube_euler_relation o,
    ⟨by decide, by decide, by decide⟩⟩


end Results
