/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import Mathlib.Tactic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Int.GCD
import EulersGem.LatticeTriangle

/-!
# Lattice polygon substrate (geometric I / B definitions)

Defines a cyclic lattice vertex list, constructive **boundary** lattice points
via edge gcds, and **interior** lattice points relative to the convex hull of
the vertices in `ℝ × ℝ`.

**Honesty:**
* `interiorLatticePoints` uses the convex hull of the vertex set. For non-convex
  simple polygons this is **not** the classical Pick interior; it is the correct
  geometric `I` only when the polygon is convex (or when a witness separately
  identifies the filled region with this hull).
* Polygon shoelace is the standard cyclic sum; equality with Lebesgue/Haar
  measure is **not** proved here.
* No triangulation existence, no classical Pick.

See `PICKS_CLAUDE_AUDIT.md`.
-/

namespace EulersGem
namespace Picks

open LatticeTriangle

/-- Embed a lattice point into the Euclidean plane. -/
def toReal (p : ℤ × ℤ) : ℝ × ℝ := (↑p.1, ↑p.2)

lemma toReal_injective : Function.Injective toReal := by
  intro p q h
  apply Prod.ext
  · exact Int.cast_injective (congrArg Prod.fst h)
  · exact Int.cast_injective (congrArg Prod.snd h)

/-! ## Edge lattice points (constructive) -/

/-- Lattice points on the closed segment from `p` to `q`, built from `edgeGcd`.
When `p = q` the set is `{p}`. Otherwise there are `edgeGcd p q + 1` points. -/
def edgeLatticePoints (p q : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  let d := edgeGcd p q
  if d = 0 then
    {p}
  else
    (Finset.range (d + 1)).image fun k : ℕ =>
      (p.1 + (k : ℤ) * ((q.1 - p.1) / (d : ℤ)),
       p.2 + (k : ℤ) * ((q.2 - p.2) / (d : ℤ)))

lemma edgeGcd_eq_zero_iff (p q : ℤ × ℤ) :
    edgeGcd p q = 0 ↔ p = q := by
  simp only [edgeGcd, Int.gcd_eq_zero_iff]
  constructor
  · intro h
    apply Prod.ext <;> linarith
  · intro h
    simp [h]

lemma self_mem_edgeLatticePoints (p q : ℤ × ℤ) :
    p ∈ edgeLatticePoints p q := by
  classical
  simp only [edgeLatticePoints]
  split_ifs with hd
  · simp
  · refine Finset.mem_image.mpr ⟨0, by simp, by simp⟩

lemma other_mem_edgeLatticePoints (p q : ℤ × ℤ) :
    q ∈ edgeLatticePoints p q := by
  classical
  simp only [edgeLatticePoints]
  split_ifs with hd
  · have : p = q := (edgeGcd_eq_zero_iff p q).mp hd
    simp [this]
  · refine Finset.mem_image.mpr ⟨edgeGcd p q, by simp, ?_⟩
    have hdx : (edgeGcd p q : ℤ) ∣ (q.1 - p.1) := by
      simpa [edgeGcd] using Int.gcd_dvd_left (q.1 - p.1) (q.2 - p.2)
    have hdy : (edgeGcd p q : ℤ) ∣ (q.2 - p.2) := by
      simpa [edgeGcd] using Int.gcd_dvd_right (q.1 - p.1) (q.2 - p.2)
    apply Prod.ext
    · have hx :
          (edgeGcd p q : ℤ) * ((q.1 - p.1) / (edgeGcd p q : ℤ)) = q.1 - p.1 := by
        rw [mul_comm]; exact Int.ediv_mul_cancel hdx
      calc
        p.1 + (edgeGcd p q : ℤ) * ((q.1 - p.1) / (edgeGcd p q : ℤ))
            = p.1 + (q.1 - p.1) := by rw [hx]
        _ = q.1 := by ring
    · have hy :
          (edgeGcd p q : ℤ) * ((q.2 - p.2) / (edgeGcd p q : ℤ)) = q.2 - p.2 := by
        rw [mul_comm]; exact Int.ediv_mul_cancel hdy
      calc
        p.2 + (edgeGcd p q : ℤ) * ((q.2 - p.2) / (edgeGcd p q : ℤ))
            = p.2 + (q.2 - p.2) := by rw [hy]
        _ = q.2 := by ring

/-- Card of edge lattice points equals `edgeGcd + 1` (including endpoints). -/
theorem card_edgeLatticePoints (p q : ℤ × ℤ) :
    (edgeLatticePoints p q).card = edgeGcd p q + 1 := by
  classical
  simp only [edgeLatticePoints]
  split_ifs with hd
  · simp [hd]
  · set d := edgeGcd p q
    set sx : ℤ := (q.1 - p.1) / (d : ℤ)
    set sy : ℤ := (q.2 - p.2) / (d : ℤ)
    have hinj :
        Function.Injective fun k : ℕ =>
          (p.1 + (k : ℤ) * sx, p.2 + (k : ℤ) * sy) := by
      intro k₁ k₂ h
      have hx : (k₁ : ℤ) * sx = (k₂ : ℤ) * sx := by
        have := congrArg Prod.fst h; linarith
      have hy : (k₁ : ℤ) * sy = (k₂ : ℤ) * sy := by
        have := congrArg Prod.snd h; linarith
      have hdx : (d : ℤ) ∣ (q.1 - p.1) := by
        simpa [edgeGcd, d] using Int.gcd_dvd_left (q.1 - p.1) (q.2 - p.2)
      have hdy : (d : ℤ) ∣ (q.2 - p.2) := by
        simpa [edgeGcd, d] using Int.gcd_dvd_right (q.1 - p.1) (q.2 - p.2)
      have hsx : sx * (d : ℤ) = q.1 - p.1 := by
        simpa [sx] using Int.ediv_mul_cancel hdx
      have hsy : sy * (d : ℤ) = q.2 - p.2 := by
        simpa [sy] using Int.ediv_mul_cancel hdy
      have hne : sx ≠ 0 ∨ sy ≠ 0 := by
        by_contra h0
        push Not at h0
        have hpq : p = q := by
          apply Prod.ext
          · have : q.1 - p.1 = 0 := by rw [← hsx, h0.1, zero_mul]
            linarith
          · have : q.2 - p.2 = 0 := by rw [← hsy, h0.2, zero_mul]
            linarith
        exact hd ((edgeGcd_eq_zero_iff p q).mpr hpq)
      have hk : (k₁ : ℤ) = (k₂ : ℤ) := by
        rcases hne with hsx0 | hsy0
        · have : ((k₁ : ℤ) - k₂) * sx = 0 := by linear_combination hx
          have : (k₁ : ℤ) - k₂ = 0 := (mul_eq_zero.mp this).resolve_right hsx0
          exact sub_eq_zero.mp this
        · have : ((k₁ : ℤ) - k₂) * sy = 0 := by linear_combination hy
          have : (k₁ : ℤ) - k₂ = 0 := (mul_eq_zero.mp this).resolve_right hsy0
          exact sub_eq_zero.mp this
      exact Nat.cast_injective hk
    rw [Finset.card_image_of_injective _ hinj, Finset.card_range]

/-! ## Lattice polygon structure -/

/-- A cyclic list of lattice vertices of length at least 3.
Does **not** assert simplicity (no self-intersections) or convexity; those are
left to witnesses / future predicates with honest names. -/
structure LatticePolygon where
  /-- Vertices in cyclic boundary order. -/
  vertices : List (ℤ × ℤ)
  /-- At least a triangle. -/
  length_ge : 3 ≤ vertices.length

namespace LatticePolygon

variable (P : LatticePolygon)

/-- Number of listed vertices. -/
def nVertices : ℕ := P.vertices.length

/-- The `i`-th vertex (requires `i < nVertices`). -/
def vertex (i : Fin P.nVertices) : ℤ × ℤ :=
  P.vertices.get i

/-- Next index in the cycle. -/
def nextIdx (i : Fin P.nVertices) : Fin P.nVertices :=
  ⟨(i.1 + 1) % P.nVertices, Nat.mod_lt _ (by
    have : 3 ≤ P.nVertices := P.length_ge; omega)⟩

/-- Consecutive edge pairs via indices `0..n-1`, each `(vertex i, vertex (i+1))`
with modular wrap-around for the closing edge. -/
def edgePair (i : Fin P.nVertices) : (ℤ × ℤ) × (ℤ × ℤ) :=
  (P.vertex i, P.vertex (P.nextIdx i))

/-- Constructive boundary lattice points: union of edge lattice points over the
cycle. -/
def boundaryLatticePoints : Finset (ℤ × ℤ) := by
  classical
  exact (Finset.univ : Finset (Fin P.nVertices)).biUnion fun i =>
    edgeLatticePoints (P.edgePair i).1 (P.edgePair i).2

/-- Geometric **B**: cardinality of boundary lattice points. -/
def B : ℕ := P.boundaryLatticePoints.card

/-- Vertex set as a `Finset`. -/
def vertexFinset : Finset (ℤ × ℤ) := P.vertices.toFinset

/-- Convex hull of the vertices in `ℝ × ℝ`.
For a **convex** lattice polygon this is the filled region; for non-convex
simple polygons it is typically larger than the polygonal region. -/
def convexHullRegion : Set (ℝ × ℝ) :=
  convexHull ℝ (toReal '' (P.vertexFinset : Set (ℤ × ℤ)))

/-- Lattice points lying in the convex hull of the vertices. -/
def latticePointsInConvexHull : Set (ℤ × ℤ) :=
  { p | toReal p ∈ P.convexHullRegion }

/-- Geometric **I** (convex-hull interpretation): lattice points in the convex
hull that are not on the cyclic boundary.

**Not** classical Pick `I` unless the polygon is convex (or the filled region
is otherwise identified with this hull). Left as a `Set` — finiteness of
lattice points in a bounded convex set is not discharged here. -/
def interiorLatticePoints : Set (ℤ × ℤ) :=
  { p | toReal p ∈ P.convexHullRegion ∧ p ∉ P.boundaryLatticePoints }

/-- Oriented shoelace sum `∑ (xᵢ yᵢ₊₁ − xᵢ₊₁ yᵢ)` over the cycle. -/
def shoelaceSum : ℤ := by
  classical
  exact ∑ i : Fin P.nVertices,
    let e := P.edgePair i
    e.1.1 * e.2.2 - e.2.1 * e.1.2

/-- Polygon shoelace area `|∑|/2` as a rational.
Not identified with Haar/Lebesgue measure. -/
def shoelace : ℚ := (Int.natAbs P.shoelaceSum : ℚ) / 2

lemma nVertices_pos : 0 < P.nVertices := by
  have : 3 ≤ P.nVertices := P.length_ge
  omega

/-- A lattice point is on the polygon boundary iff it lies on some cyclic edge. -/
theorem mem_boundaryLatticePoints_iff (p : ℤ × ℤ) :
    p ∈ P.boundaryLatticePoints ↔
      ∃ i : Fin P.nVertices, p ∈ edgeLatticePoints (P.edgePair i).1 (P.edgePair i).2 := by
  classical
  simp [boundaryLatticePoints]

/-- Every listed vertex appears as the start of some cyclic edge. -/
lemma exists_edge_of_mem_vertices {v : ℤ × ℤ} (hv : v ∈ P.vertices) :
    ∃ i : Fin P.nVertices, P.vertex i = v := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hv
  refine ⟨⟨i.1, ?_⟩, ?_⟩
  · simp [nVertices]
  · rfl

/-- Every polygon vertex lies on the constructive boundary. -/
theorem vertices_mem_boundary {v : ℤ × ℤ} (hv : v ∈ P.vertices) :
    v ∈ P.boundaryLatticePoints := by
  classical
  obtain ⟨i, hi⟩ := P.exists_edge_of_mem_vertices hv
  refine (P.mem_boundaryLatticePoints_iff v).mpr ⟨i, ?_⟩
  have : (P.edgePair i).1 = v := by
    simpa [edgePair] using hi
  simpa [this] using self_mem_edgeLatticePoints v (P.edgePair i).2

/-- Every listed vertex lies in the convex-hull lattice-point set.
Uses `subset_convexHull` — not Haar, not Pick. -/
theorem mem_latticePointsInConvexHull_of_mem_vertices {v : ℤ × ℤ}
    (hv : v ∈ P.vertices) : v ∈ P.latticePointsInConvexHull := by
  have hvF : v ∈ P.vertexFinset := List.mem_toFinset.mpr hv
  have himg : toReal v ∈ toReal '' (P.vertexFinset : Set (ℤ × ℤ)) :=
    Set.mem_image_of_mem toReal hvF
  exact subset_convexHull ℝ _ himg

end LatticePolygon

end Picks
end EulersGem
