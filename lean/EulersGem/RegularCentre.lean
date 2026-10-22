/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.RegularCombinatorics

/-!
# First metric consequences of regularity

Towards the geometric half of the classification (`PlatonicGaps.GAP_rigidity`). For a regular
polyhedron `P` (flag-transitive, with the general face-lattice facts `FaceLatticeFacts`):

* `IsRegularPolyhedron.exists_centre`: there is a point `c` fixed by **every** symmetry of `P`
  (the centroid of the vertices) from which all vertices are equidistant — `P` is inscribed in
  a sphere centred at `c`;
* `IsRegularPolyhedron.edges_congruent`: all edges have the same length;
* `IsRegularPolyhedron.facets_congruent`, `IsRegularPolyhedron.edges_congruent'`: any two
  facets (edges) are carried onto each other by a symmetry of `P`.

Nothing here is assumed beyond `IsRegularPolyhedron` and `FaceLatticeFacts`. Note that
`FaceLatticeFacts` is proved only for the five constructed solids (`platonic_faceLatticeFacts`);
its general proof is the gap `PlatonicGaps.GAP_faceLatticeFacts`. Edge length is measured as
`Metric.diam` (for a segment, its length).
-/

open Set
open scoped RealInnerProductSpace

namespace EulersGem

open Platonic

/-- The vertices of `P`: points `x` such that `{x}` is a `0`-face. -/
def vertexSet (P : Set R3) : Set R3 := {x | {x} ∈ facesOfDim P 0}

lemma vertexSet_finite {P : Set R3} (hP : IsPolytope P) : (vertexSet P).Finite := by
  obtain ⟨S, hS, rfl⟩ := hP
  exact hS.subset fun x hx => extremePoints_convexHull_subset
    (isExtreme_singleton.1 hx.1.isExtreme)

lemma image_vertexSet {P : Set R3} {g : R3 ≃ᵃⁱ[ℝ] R3} (hg : g '' P = P) :
    g '' vertexSet P = vertexSet P := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have := image_mem_facesOfDim hg hx
    rwa [Set.image_singleton] at this
  · intro hy
    have := image_mem_facesOfDim (symm_image_eq hg) hy
    rw [Set.image_singleton] at this
    exact ⟨g.symm y, this, by simp⟩

/-- A symmetry of `P` fixes the centroid of the vertices. -/
lemma centroid_vertexSet_fixed {P : Set R3} (hfin : (vertexSet P).Finite)
    (hne : hfin.toFinset.Nonempty) {g : R3 ≃ᵃⁱ[ℝ] R3} (hg : g '' P = P) :
    g (hfin.toFinset.centroid ℝ id) = hfin.toFinset.centroid ℝ id := by
  classical
  set T := hfin.toFinset with hT
  have hw : T.sum (T.centroidWeights ℝ) = 1 := T.sum_centroidWeights_eq_one_of_nonempty ℝ hne
  have hmap : T.map g.toAffineEquiv.toEquiv.toEmbedding = T := by
    ext y
    simp only [Finset.mem_map, hT, Set.Finite.mem_toFinset, Equiv.coe_toEmbedding]
    exact Set.ext_iff.1 (image_vertexSet hg) y
  have h1 : g (T.centroid ℝ id) = T.centroid ℝ (fun x => g x) := by
    rw [Finset.centroid_def, Finset.centroid_def]
    exact Finset.map_affineCombination T id _ hw g.toAffineEquiv.toAffineMap
  conv_rhs => rw [← hmap]
  rw [h1, Finset.centroid_map]
  rfl

/-- **A regular polyhedron has a centre.** Some point `c` (the centroid of the vertices) is
fixed by every symmetry of `P`, and all vertices of `P` are at the same distance `r` from
`c`. -/
theorem IsRegularPolyhedron.exists_centre {P : Set R3} (hP : IsRegularPolyhedron P)
    (hL : FaceLatticeFacts P) :
    ∃ c : R3, (∀ g : R3 ≃ᵃⁱ[ℝ] R3, g '' P = P → g c = c) ∧
      ∃ r : ℝ, ∀ x ∈ vertexSet P, dist x c = r := by
  obtain ⟨hpoly, -, htr⟩ := hP
  have hfin := vertexSet_finite hpoly
  obtain ⟨v0, e0, f0, h0⟩ := hL.exists_flag
  obtain ⟨x0, rfl⟩ := eq_singleton_of_affDim_eq_zero h0.1.2
  have hx0 : x0 ∈ vertexSet P := h0.1
  have hne : hfin.toFinset.Nonempty := ⟨x0, by simpa using hx0⟩
  refine ⟨_, fun g hg => centroid_vertexSet_fixed hfin hne hg,
    dist x0 (hfin.toFinset.centroid ℝ id), fun y hy => ?_⟩
  obtain ⟨e, f, hfl0⟩ := hL.vertex_in_flag _ h0.1
  obtain ⟨e', f', hfl⟩ := hL.vertex_in_flag _ hy
  obtain ⟨g, hg, hgv, -, -⟩ := htr _ _ _ _ _ _ hfl0 hfl
  rw [Set.image_singleton, Set.singleton_eq_singleton_iff] at hgv
  have := g.dist_map x0 (hfin.toFinset.centroid ℝ id)
  rw [centroid_vertexSet_fixed hfin hne hg] at this
  rw [← hgv, this]

/-- Every edge lies in a flag. -/
lemma FaceLatticeFacts.edge_in_flag {P : Set R3} (hP : IsPolytope P) (hL : FaceLatticeFacts P)
    {e : Set R3} (he : e ∈ facesOfDim P 1) : ∃ v f, IsFlag P v e f := by
  obtain ⟨v, hv, hve⟩ := nonempty_of_le_ncard (k := 2) (by omega)
    (ncard_vertices_of_edge hP he.1 he.2).ge
  obtain ⟨f, hf, hef⟩ := hL.edge_in_facet e he
  exact ⟨v, f, hv, he, hf, hve, hef⟩

/-- Any two edges of a regular polyhedron are exchanged by a symmetry. -/
theorem IsRegularPolyhedron.edges_congruent' {P : Set R3} (hP : IsRegularPolyhedron P)
    (hL : FaceLatticeFacts P) {e e' : Set R3} (he : e ∈ facesOfDim P 1)
    (he' : e' ∈ facesOfDim P 1) : ∃ g : R3 ≃ᵃⁱ[ℝ] R3, g '' P = P ∧ g '' e = e' := by
  obtain ⟨v, f, h⟩ := hL.edge_in_flag hP.1 he
  obtain ⟨v', f', h'⟩ := hL.edge_in_flag hP.1 he'
  obtain ⟨g, hg, -, hge, -⟩ := hP.2.2 _ _ _ _ _ _ h h'
  exact ⟨g, hg, hge⟩

/-- **All edges of a regular polyhedron have the same length** (`Metric.diam`, which for a
segment is its length). -/
theorem IsRegularPolyhedron.edges_congruent {P : Set R3} (hP : IsRegularPolyhedron P)
    (hL : FaceLatticeFacts P) :
    ∃ ℓ : ℝ, ∀ e ∈ facesOfDim P 1, Metric.diam e = ℓ := by
  obtain ⟨v0, e0, f0, h0⟩ := hL.exists_flag
  refine ⟨Metric.diam e0, fun e he => ?_⟩
  obtain ⟨g, -, hge⟩ := hP.edges_congruent' hL h0.2.1 he
  rw [← hge, g.diam_image]

/-- Any two facets of a regular polyhedron are exchanged by a symmetry. -/
theorem IsRegularPolyhedron.facets_congruent {P : Set R3} (hP : IsRegularPolyhedron P)
    (hL : FaceLatticeFacts P) {f f' : Set R3} (hf : f ∈ facesOfDim P 2)
    (hf' : f' ∈ facesOfDim P 2) : ∃ g : R3 ≃ᵃⁱ[ℝ] R3, g '' P = P ∧ g '' f = f' := by
  obtain ⟨v, e, h⟩ := hL.facet_in_flag f hf
  obtain ⟨v', e', h'⟩ := hL.facet_in_flag f' hf'
  obtain ⟨g, hg, -, -, hgf⟩ := hP.2.2 _ _ _ _ _ _ h h'
  exact ⟨g, hg, hgf⟩

end EulersGem
