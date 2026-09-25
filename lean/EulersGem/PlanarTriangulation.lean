/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import Mathlib.Tactic

/-!
# Combinatorial disk triangulation — handshaking from incidence

**EP-spine role:** classical Pick needs `2E = 3T + B` as a derived incidence
identity (not a free hyp). This file defines a combinatorial planar / disk
triangulation whose edge–triangle incidence fields make that identity a theorem.

**Honesty:**
* This is combinatorial (Finset incidence), not yet a geometric embedding in `ℝ²`.
* `B` here is `#boundaryEdges`. For a simple closed polygonal boundary,
  `#boundaryEdges = #boundaryVertices`, which is the Pick `B` when all boundary
  lattice points are vertices of the triangulation.
* Planar Euler `V−E+F=2` is proved for fan count identities, the unit square,
  and fan triangulations on `Fin n` for `n ≤ 5`; general EP→planar discharge
  via `Euler_Poincare_full` remains open (`planar_disk_euler_of_EP_bridge`).
* Classical Pick remains FAIL (`PICKS_CLAUDE_AUDIT.md`).

Identifiers avoid claiming classical Pick.
-/

open Finset BigOperators

namespace EulersGem
namespace Picks

/-- Combinatorial triangulation of a disk (polygon interior filled by triangles).

Fields encode the classical edge–triangle incidence used in Pick:
each triangle contributes three edges; interior edges meet two triangles;
boundary edges meet one. -/
structure CombinatorialDiskTriangulation (α : Type*) [DecidableEq α] where
  /-- Triangular faces (each a 3-element vertex set). -/
  triangles : Finset (Finset α)
  /-- All edges of the complex (each a 2-element vertex set). -/
  edges : Finset (Finset α)
  /-- Boundary edges (the outer cycle; subset of `edges`). -/
  boundaryEdges : Finset (Finset α)
  /-- Every triangle has exactly three vertices. -/
  triangle_card : ∀ t ∈ triangles, t.card = 3
  /-- Every edge has exactly two vertices. -/
  edge_card : ∀ e ∈ edges, e.card = 2
  /-- Boundary edges are edges. -/
  boundary_subset : boundaryEdges ⊆ edges
  /-- The three 2-subsets of each triangle are edges of the complex. -/
  triangle_edges_mem :
    ∀ t ∈ triangles, t.powersetCard 2 ⊆ edges
  /-- Incidence: boundary edge in exactly one triangle; interior edge in exactly two. -/
  edge_incidence :
    ∀ e ∈ edges,
      (triangles.filter (fun t => e ⊆ t)).card =
        if e ∈ boundaryEdges then 1 else 2

namespace CombinatorialDiskTriangulation

variable {α : Type*} [DecidableEq α] (G : CombinatorialDiskTriangulation α)

/-- Number of triangles `T`. -/
def T : ℕ := G.triangles.card

/-- Number of edges `E`. -/
def E : ℕ := G.edges.card

/-- Number of boundary edges `B` (equals Pick boundary-vertex count on a simple cycle
when every boundary lattice point is a graph vertex). -/
def B : ℕ := G.boundaryEdges.card

lemma B_le_E : G.B ≤ G.E :=
  Finset.card_le_card G.boundary_subset

/-- Each triangle has exactly three edges (2-subsets). -/
theorem card_powersetCard_two_of_mem_triangles {t : Finset α}
    (ht : t ∈ G.triangles) : (t.powersetCard 2).card = 3 := by
  have hc := G.triangle_card t ht
  rw [Finset.card_powersetCard, hc]
  norm_num

/-- Incidence Finset: pairs `(t, e)` with `t` a triangle and `e ⊆ t` an edge. -/
def incidences : Finset (Finset α × Finset α) :=
  (G.triangles ×ˢ G.edges).filter fun p => p.2 ⊆ p.1

private lemma card_filter_eq_sum_ite {β : Type*} [DecidableEq β]
    (s : Finset β) (p : β → Prop) [DecidablePred p] :
    (s.filter p).card = ∑ x ∈ s, if p x then (1 : ℕ) else 0 := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

private lemma edges_of_triangle {t : Finset α} (ht : t ∈ G.triangles) :
    G.edges.filter (fun e => e ⊆ t) = t.powersetCard 2 := by
  ext e
  constructor
  · intro he
    obtain ⟨heE, hesub⟩ := Finset.mem_filter.mp he
    exact Finset.mem_powersetCard.mpr ⟨hesub, G.edge_card e heE⟩
  · intro he
    exact Finset.mem_filter.mpr ⟨G.triangle_edges_mem t ht he,
      (Finset.mem_powersetCard.mp he).1⟩

/-- Left count: each of `T` triangles contributes three edges ⇒ `|I| = 3T`. -/
theorem card_incidences_eq_three_T : G.incidences.card = 3 * G.T := by
  classical
  unfold incidences T
  have hsum :
      ((G.triangles ×ˢ G.edges).filter fun p => p.2 ⊆ p.1).card =
        ∑ t ∈ G.triangles, (G.edges.filter (fun e => e ⊆ t)).card := by
    rw [card_filter_eq_sum_ite]
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun t _ => ?_
    -- ∑ e, if e ⊆ t then 1 else 0 = (edges.filter (· ⊆ t)).card
    exact (card_filter_eq_sum_ite G.edges (fun e => e ⊆ t)).symm
  rw [hsum]
  have hrew :
      ∑ t ∈ G.triangles, (G.edges.filter (fun e => e ⊆ t)).card =
        ∑ t ∈ G.triangles, (t.powersetCard 2).card :=
    Finset.sum_congr rfl fun t ht => by rw [G.edges_of_triangle ht]
  rw [hrew]
  have h3 : ∀ t ∈ G.triangles, (t.powersetCard 2).card = 3 :=
    fun t ht => G.card_powersetCard_two_of_mem_triangles ht
  rw [Finset.sum_congr rfl h3, Finset.sum_const_nat (fun _ _ => rfl), Nat.mul_comm]

/-- Right count: interior edges contribute 2, boundary 1 ⇒ `|I| = 2E − B`. -/
theorem card_incidences_eq_two_E_sub_B : G.incidences.card = 2 * G.E - G.B := by
  classical
  unfold incidences E B
  have hsum :
      ((G.triangles ×ˢ G.edges).filter fun p => p.2 ⊆ p.1).card =
        ∑ e ∈ G.edges, (G.triangles.filter (fun t => e ⊆ t)).card := by
    rw [card_filter_eq_sum_ite, Finset.sum_product, Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    exact (card_filter_eq_sum_ite G.triangles (fun t => e ⊆ t)).symm
  rw [hsum]
  have hrew :
      ∑ e ∈ G.edges, (G.triangles.filter (fun t => e ⊆ t)).card =
        ∑ e ∈ G.edges, (if e ∈ G.boundaryEdges then (1 : ℕ) else 2) :=
    Finset.sum_congr rfl fun e he => G.edge_incidence e he
  rw [hrew]
  have hsub := G.boundary_subset
  have hsplit :
      ∑ e ∈ G.edges, (if e ∈ G.boundaryEdges then (1 : ℕ) else 2) =
        G.boundaryEdges.card + 2 * (G.edges.card - G.boundaryEdges.card) := by
    have hdisj : Disjoint G.boundaryEdges (G.edges \ G.boundaryEdges) :=
      Finset.disjoint_sdiff
    have hunion : G.boundaryEdges ∪ (G.edges \ G.boundaryEdges) = G.edges :=
      Finset.union_sdiff_of_subset hsub
    calc
      ∑ e ∈ G.edges, (if e ∈ G.boundaryEdges then (1 : ℕ) else 2)
          = ∑ e ∈ G.boundaryEdges ∪ (G.edges \ G.boundaryEdges),
              (if e ∈ G.boundaryEdges then 1 else 2) := by rw [hunion]
      _ = ∑ e ∈ G.boundaryEdges, (if e ∈ G.boundaryEdges then (1 : ℕ) else 2) +
            ∑ e ∈ G.edges \ G.boundaryEdges, (if e ∈ G.boundaryEdges then 1 else 2) := by
          rw [Finset.sum_union hdisj]
      _ = G.boundaryEdges.card + 2 * (G.edges \ G.boundaryEdges).card := by
          have h1 : ∑ e ∈ G.boundaryEdges, (if e ∈ G.boundaryEdges then (1 : ℕ) else 2) =
              G.boundaryEdges.card := by
            have : ∀ e ∈ G.boundaryEdges,
                (if e ∈ G.boundaryEdges then (1 : ℕ) else 2) = 1 := fun e he => by simp [he]
            rw [Finset.sum_congr rfl this, Finset.sum_const_nat (fun _ _ => rfl), mul_one]
          have h2 : ∑ e ∈ G.edges \ G.boundaryEdges,
              (if e ∈ G.boundaryEdges then (1 : ℕ) else 2) =
                2 * (G.edges \ G.boundaryEdges).card := by
            have : ∀ e ∈ G.edges \ G.boundaryEdges,
                (if e ∈ G.boundaryEdges then (1 : ℕ) else 2) = 2 := by
              intro e he
              have : e ∉ G.boundaryEdges := (Finset.mem_sdiff.mp he).2
              simp [this]
            rw [Finset.sum_congr rfl this, Finset.sum_const_nat (fun _ _ => rfl), Nat.mul_comm]
          rw [h1, h2]
      _ = G.boundaryEdges.card + 2 * (G.edges.card - G.boundaryEdges.card) := by
          rw [Finset.card_sdiff_of_subset hsub]
  have harith :
      G.boundaryEdges.card + 2 * (G.edges.card - G.boundaryEdges.card) =
        2 * G.edges.card - G.boundaryEdges.card := by
    have : G.boundaryEdges.card ≤ G.edges.card := Finset.card_le_card hsub
    omega
  omega

/-- **Handshaking for a combinatorial disk triangulation** (proved from incidence).

`2E = 3T + B` where `B = #boundaryEdges`. This discharges the `hshake` hypothesis
of `triangulation_count_identity` whenever a `CombinatorialDiskTriangulation` is
supplied. -/
theorem two_E_eq_three_T_add_B : 2 * G.E = 3 * G.T + G.B := by
  have hL := G.card_incidences_eq_three_T
  have hR := G.card_incidences_eq_two_E_sub_B
  have hB := G.B_le_E
  omega

/-- ℤ form matching `triangulation_count_identity`'s `hshake`. -/
theorem two_E_eq_three_T_add_B_int :
    (2 : ℤ) * G.E = 3 * (G.T : ℤ) + G.B := by
  exact_mod_cast G.two_E_eq_three_T_add_B

end CombinatorialDiskTriangulation

/-- Convenience export. -/
theorem handshaking_of_combinatorial_disk_triangulation
    {α : Type*} [DecidableEq α] (G : CombinatorialDiskTriangulation α) :
    2 * G.E = 3 * G.T + G.B :=
  G.two_E_eq_three_T_add_B

/-! ## Planar / disk Euler (combinatorial face of the EP spine)

A disk cell complex with one unbounded outer face satisfies `V − E + F = 2`
when `F = T + 1` and the complex is topologically a disk.

**Relation to `Euler_Poincare_full`:** the 3D geometric root proves `V−E+F=2` for
convex 3-polytopes via `faceEulerSum`. The *planar* identity is the same numeric
story on a disk / stereographic chart. Full discharge (cone lift or 2D face-sum
API derived from EP) remains open for *arbitrary* planar complexes. Below we
prove the identity for:

* fan count bookkeeping (mirrors EP arithmetic, no free `ℤ` Euler hyp),
* the concrete unit-square disk triangulation,
* concrete fan disk triangulations on `Fin n` for small `n` (existence slice).

Identifiers avoid claiming classical Pick.
-/

/-- Combinatorial counts for a triangulated polygonal disk (including outer face). -/
structure PlanarDiskEulerCounts where
  V : ℕ
  E : ℕ
  /-- Triangular interior faces. -/
  T : ℕ
  /-- `F = T + 1` (outer face counted). -/
  F : ℕ := T + 1
  hF : F = T + 1 := by rfl

/-- Target Euler identity for a disk triangulation counting the outer face. -/
def PlanarDiskEulerCounts.eulerChar (C : PlanarDiskEulerCounts) : ℤ :=
  (C.V : ℤ) - C.E + C.F

/-- Open EP→planar bridge: if a planar disk complex is identified with the
boundary-link / stereographic image of a convex 3-polytope face lattice, then
Euler char is 2. **`hEP_bridge` is the remaining discharge** from
`Euler_Poincare_full` / `euler_relation_convex_3polytope` for general complexes.
Concrete cases below prove `eulerChar = 2` without this hyp. -/
theorem planar_disk_euler_of_EP_bridge (C : PlanarDiskEulerCounts)
    (hEP_bridge : C.eulerChar = 2) :
    (C.V : ℤ) - C.E + C.F = 2 :=
  hEP_bridge

/-- Fan / empty-interior polygon count identities ⇒ planar Euler.

When a triangulated n-gon has no interior vertices (`V = B = n`) and is a fan
(`T = n − 2`, `E = 2n − 3`), the disk Euler identity holds by arithmetic that
mirrors the EP bookkeeping (`faceEulerSum` / `V−E+F=2`). This is the planar
*combinatorial face* of the same story — not yet a call to
`Euler_Poincare_full`. -/
theorem planar_disk_euler_of_fan_counts
    (n V E T B F : ℕ)
    (hn : 3 ≤ n)
    (hV : V = n) (hB : B = n) (hT : T = n - 2)
    (hE : E = 2 * n - 3) (hF : F = T + 1) :
    (V : ℤ) - E + F = 2 := by
  omega

/-- Same conclusion packaged on `PlanarDiskEulerCounts`. -/
theorem PlanarDiskEulerCounts.eulerChar_eq_two_of_fan_counts
    (C : PlanarDiskEulerCounts) (n B : ℕ)
    (hn : 3 ≤ n)
    (hV : C.V = n) (hB : B = n) (hT : C.T = n - 2)
    (hE : C.E = 2 * n - 3) :
    C.eulerChar = 2 := by
  simpa [PlanarDiskEulerCounts.eulerChar, C.hF] using
    planar_disk_euler_of_fan_counts n C.V C.E C.T B C.F hn hV hB hT hE C.hF

namespace CombinatorialDiskTriangulation

variable {α : Type*} [DecidableEq α] (G : CombinatorialDiskTriangulation α)

/-- Vertex set recovered as the union of edge endpoints. -/
def vertexSet : Finset α := G.edges.biUnion id

/-- Number of vertices `V` from edge endpoints. -/
def V : ℕ := G.vertexSet.card

/-- Euler counts with `F = T + 1` and `V` from edge endpoints. -/
def planarCounts : PlanarDiskEulerCounts where
  V := G.V
  E := G.E
  T := G.T

end CombinatorialDiskTriangulation

/-- From a combinatorial disk triangulation, Euler counts with `F = T + 1`
and `V = #vertexSet` (edge-endpoint union). -/
def PlanarDiskEulerCounts.ofTriangulation {α : Type*} [DecidableEq α]
    (G : CombinatorialDiskTriangulation α) : PlanarDiskEulerCounts :=
  G.planarCounts

/-! ## Concrete inhabited example: unit square → two triangles

Shows `CombinatorialDiskTriangulation` is inhabited on a non-toy lattice
polygon (unit square with diagonal). Planar Euler is **proved** for this
example (not a free hyp). Does **not** prove triangulation existence for
arbitrary polygons — see `FanDiskTriangulation` for a small-n existence slice. -/

namespace UnitSquareTriangulation

/-- Vertices of the unit square. -/
def v00 : ℤ × ℤ := (0, 0)
def v10 : ℤ × ℤ := (1, 0)
def v11 : ℤ × ℤ := (1, 1)
def v01 : ℤ × ℤ := (0, 1)

/-- Lower-right triangle `{(0,0),(1,0),(1,1)}`. -/
def tLower : Finset (ℤ × ℤ) := {v00, v10, v11}

/-- Upper-left triangle `{(0,0),(1,1),(0,1)}`. -/
def tUpper : Finset (ℤ × ℤ) := {v00, v11, v01}

def e_bottom : Finset (ℤ × ℤ) := {v00, v10}
def e_right : Finset (ℤ × ℤ) := {v10, v11}
def e_top : Finset (ℤ × ℤ) := {v11, v01}
def e_left : Finset (ℤ × ℤ) := {v01, v00}
def e_diag : Finset (ℤ × ℤ) := {v00, v11}

private lemma tLower_card : tLower.card = 3 := by native_decide
private lemma tUpper_card : tUpper.card = 3 := by native_decide

/-- Combinatorial disk triangulation of the unit square (two triangles, one diagonal). -/
def unitSquare : CombinatorialDiskTriangulation (ℤ × ℤ) where
  triangles := {tLower, tUpper}
  edges := {e_bottom, e_right, e_top, e_left, e_diag}
  boundaryEdges := {e_bottom, e_right, e_top, e_left}
  triangle_card := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact tLower_card
    · exact tUpper_card
  edge_card := by native_decide
  boundary_subset := by native_decide
  triangle_edges_mem := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl <;> native_decide
  edge_incidence := by
    intro e he
    -- Five edges; decide membership and filter card by computation
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with h | h | h | h | h <;> subst h <;> native_decide

theorem unitSquare_T : unitSquare.T = 2 := by native_decide
theorem unitSquare_E : unitSquare.E = 5 := by native_decide
theorem unitSquare_B : unitSquare.B = 4 := by native_decide
theorem unitSquare_V : unitSquare.V = 4 := by native_decide

/-- Concrete check: handshaking holds on the unit square (`2·5 = 3·2 + 4`). -/
theorem unitSquare_handshaking : 2 * unitSquare.E = 3 * unitSquare.T + unitSquare.B :=
  unitSquare.two_E_eq_three_T_add_B

/-- **Planar Euler for the unit-square disk triangulation** (proved, not assumed).

`V−E+F = 4−5+3 = 2` with `F = T+1`. This is a concrete planar-disk instance of
the same `V−E+F=2` identity as `euler_relation_convex_3polytope`; the general
EP→planar discharge (`planar_disk_euler_of_EP_bridge`) remains open. -/
theorem unitSquare_planar_euler :
    (unitSquare.planarCounts).eulerChar = 2 := by
  native_decide

theorem unitSquare_planar_euler' :
    (unitSquare.V : ℤ) - unitSquare.E + (unitSquare.T + 1) = 2 := by
  simpa [PlanarDiskEulerCounts.eulerChar, PlanarDiskEulerCounts.hF,
    CombinatorialDiskTriangulation.planarCounts] using unitSquare_planar_euler

/-- Unit square matches fan counts for `n = 4` (`V=B=4`, `T=2`, `E=5`). -/
theorem unitSquare_fan_counts :
    unitSquare.V = 4 ∧ unitSquare.B = 4 ∧ unitSquare.T = 4 - 2 ∧
      unitSquare.E = 2 * 4 - 3 := by
  native_decide

/-- Recover planar Euler from fan-count arithmetic (EP-mirroring bookkeeping). -/
theorem unitSquare_planar_euler_of_fan_counts :
    (unitSquare.V : ℤ) - unitSquare.E + (unitSquare.T + 1) = 2 := by
  obtain ⟨hV, hB, hT, hE⟩ := unitSquare_fan_counts
  exact planar_disk_euler_of_fan_counts 4 unitSquare.V unitSquare.E unitSquare.T
    unitSquare.B (unitSquare.T + 1) (by omega) hV hB hT hE rfl

end UnitSquareTriangulation

/-! ## Fan disk triangulation existence (`Fin n`, small `n`)

Constructive combinatorial triangulation of an abstract n-gon by fanning from
vertex `0`. Proves inhabitedness for `n = 3,4,5` (existence slice toward
convex lattice polygons). Planar Euler follows from fan counts or direct
computation. **Not** geometric embedding / classical Pick. -/

namespace FanDiskTriangulation

/-- Boundary cycle edges `{i, i+1}` on `Fin n` (addition wraps). -/
def fanBoundary (n : ℕ) (hn : 3 ≤ n) : Finset (Finset (Fin n)) :=
  haveI : NeZero n := ⟨by omega⟩
  (Finset.univ : Finset (Fin n)).image fun i => ({i, i + 1} : Finset (Fin n))

/-- Fan triangles `{0, i+1, i+2}` for `i < n-2`. -/
def fanTriangles (n : ℕ) (hn : 3 ≤ n) : Finset (Finset (Fin n)) :=
  (Finset.range (n - 2)).attach.image fun i =>
    let i' : ℕ := i.1
    have hi : i' < n - 2 := Finset.mem_range.mp i.2
    ({⟨0, by omega⟩, ⟨i' + 1, by omega⟩, ⟨i' + 2, by omega⟩} : Finset (Fin n))

/-- Fan diagonals `{0, k}` for `2 ≤ k ≤ n-2`. -/
def fanDiagonals (n : ℕ) (hn : 3 ≤ n) : Finset (Finset (Fin n)) :=
  (Finset.range (n - 3)).attach.image fun i =>
    let i' : ℕ := i.1
    have hi : i' < n - 3 := Finset.mem_range.mp i.2
    ({⟨0, by omega⟩, ⟨i' + 2, by omega⟩} : Finset (Fin n))

def fanEdges (n : ℕ) (hn : 3 ≤ n) : Finset (Finset (Fin n)) :=
  fanBoundary n hn ∪ fanDiagonals n hn

/-- Triangle (n=3): one face, three boundary edges. -/
def fan3 : CombinatorialDiskTriangulation (Fin 3) where
  triangles := fanTriangles 3 (by omega)
  edges := fanEdges 3 (by omega)
  boundaryEdges := fanBoundary 3 (by omega)
  triangle_card := by native_decide +revert
  edge_card := by native_decide
  boundary_subset := by native_decide
  triangle_edges_mem := by native_decide +revert
  edge_incidence := by native_decide +revert

/-- Quadrilateral fan (n=4): two triangles, one diagonal. -/
def fan4 : CombinatorialDiskTriangulation (Fin 4) where
  triangles := fanTriangles 4 (by omega)
  edges := fanEdges 4 (by omega)
  boundaryEdges := fanBoundary 4 (by omega)
  triangle_card := by native_decide +revert
  edge_card := by native_decide
  boundary_subset := by native_decide
  triangle_edges_mem := by native_decide +revert
  edge_incidence := by native_decide +revert

/-- Pentagon fan (n=5): three triangles, two diagonals. -/
def fan5 : CombinatorialDiskTriangulation (Fin 5) where
  triangles := fanTriangles 5 (by omega)
  edges := fanEdges 5 (by omega)
  boundaryEdges := fanBoundary 5 (by omega)
  triangle_card := by native_decide +revert
  edge_card := by native_decide
  boundary_subset := by native_decide
  triangle_edges_mem := by native_decide +revert
  edge_incidence := by native_decide +revert

theorem fan3_T : fan3.T = 1 := by native_decide
theorem fan3_E : fan3.E = 3 := by native_decide
theorem fan3_B : fan3.B = 3 := by native_decide
theorem fan3_V : fan3.V = 3 := by native_decide

theorem fan4_T : fan4.T = 2 := by native_decide
theorem fan4_E : fan4.E = 5 := by native_decide
theorem fan4_B : fan4.B = 4 := by native_decide
theorem fan4_V : fan4.V = 4 := by native_decide

theorem fan5_T : fan5.T = 3 := by native_decide
theorem fan5_E : fan5.E = 7 := by native_decide
theorem fan5_B : fan5.B = 5 := by native_decide
theorem fan5_V : fan5.V = 5 := by native_decide

/-- Planar Euler for the abstract triangle fan (`3−3+2=2`). -/
theorem fan3_planar_euler : (fan3.planarCounts).eulerChar = 2 := by native_decide

/-- Planar Euler for the abstract quadrilateral fan (`4−5+3=2`). -/
theorem fan4_planar_euler : (fan4.planarCounts).eulerChar = 2 := by native_decide

/-- Planar Euler for the abstract pentagon fan (`5−7+4=2`). -/
theorem fan5_planar_euler : (fan5.planarCounts).eulerChar = 2 := by native_decide

/-- Existence: every n-gon with `3 ≤ n ≤ 5` admits a combinatorial fan
disk triangulation on `Fin n`. -/
theorem exists_fan_disk_triangulation {n : ℕ} (hn : 3 ≤ n) (hN : n ≤ 5) :
    Nonempty (CombinatorialDiskTriangulation (Fin n)) := by
  interval_cases n
  · exact ⟨fan3⟩
  · exact ⟨fan4⟩
  · exact ⟨fan5⟩

end FanDiskTriangulation

end Picks
end EulersGem
