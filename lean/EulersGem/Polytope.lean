/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.AffDim
import EulersGem.CellGeometry
import EulersGem.Hyperplane
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Polyhedra, polytopes, faces, cones (Paulson / HOL-Analysis substrate)

Mathlib has `IsExtreme` / `IsExposed` and cone faces, but not Isabelle-style
`polyhedron` / `polytope` / `face_of` for general convex sets. This module
supplies the thin set-level API needed for Euler–Poincaré.

Isabelle names: `polyhedron`, `polytope`, `face_of`, `conic`.
-/

open scoped RealInnerProductSpace
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace EulersGem

/-- Closed halfspace `{x | ⟪a, x⟫ ≤ b}`. -/
def closedHalfspace (a : E) (b : ℝ) : Set E :=
  {x | ⟪a, x⟫ ≤ b}

lemma convex_closedHalfspace (a : E) (b : ℝ) : Convex ℝ (closedHalfspace a b) :=
  convex_halfSpace_le (isLinearMap_inner a) b

/-- `S` is a polyhedron: finite intersection of closed halfspaces.
Isabelle: `polyhedron` (H-description). -/
def IsPolyhedron (S : Set E) : Prop :=
  ∃ H : Set (Hyperplane E), H.Finite ∧
    S = ⋂ h ∈ H, closedHalfspace h.1 h.2

/-- `S` is a polytope: convex hull of a finite set (V-description).
Isabelle: `polytope`. -/
def IsPolytope (S : Set E) : Prop :=
  ∃ V : Set E, V.Finite ∧ S = convexHull ℝ V

/-- Face relation: Isabelle `face_of`. Alias of Mathlib `IsExtreme ℝ`. -/
abbrev IsFaceOf (S T : Set E) : Prop := IsExtreme ℝ S T

lemma isFaceOf_refl (S : Set E) : IsFaceOf S S := IsExtreme.rfl

lemma isFaceOf_subset {S T : Set E} (h : IsFaceOf S T) : T ⊆ S := h.subset

/-- Combinatorial face Euler sum (Paulson left-hand side of Euler–Poincaré). -/
noncomputable def faceEulerSum (S : Set E) (n : ℕ) : ℤ :=
  ∑ d ∈ Finset.range (n + 1),
    (-1 : ℤ) ^ d *
      (Set.ncard {f : Set E | IsFaceOf S f ∧ affDim f = (d : ℤ)} : ℤ)

/-- `S` is a cone (conic set): closed under nonnegative scaling.
Isabelle: `conic`. -/
def IsConic (S : Set E) : Prop :=
  ∀ ⦃x⦄, x ∈ S → ∀ c : ℝ, 0 ≤ c → c • x ∈ S

lemma isConic_zero_mem {S : Set E} (h : IsConic S) (hne : S.Nonempty) : (0 : E) ∈ S := by
  obtain ⟨x, hx⟩ := hne
  simpa using h hx (0 : ℝ) le_rfl

lemma isConic_univ : IsConic (univ : Set E) := fun _ _ _ _ => mem_univ _

lemma isConic_closedHalfspace_zero (a : E) : IsConic (closedHalfspace a 0) := by
  intro x hx c hc
  change ⟪a, x⟫ ≤ 0 at hx
  change ⟪a, c • x⟫ ≤ 0
  have : ⟪a, c • x⟫ = c * ⟪a, x⟫ := by simp [inner_smul_right]
  rw [this]
  exact mul_nonpos_of_nonneg_of_nonpos hc hx

/-- Homogeneous H-description of a polyhedral cone. -/
def IsPolyhedralCone (S : Set E) : Prop :=
  ∃ As : Set E, As.Finite ∧ S = ⋂ a ∈ As, closedHalfspace a 0

lemma isPolyhedralCone_isPolyhedron {S : Set E} (h : IsPolyhedralCone S) :
    IsPolyhedron S := by
  obtain ⟨As, hAs, rfl⟩ := h
  refine ⟨(fun a => (a, (0 : ℝ))) '' As, hAs.image _, ?_⟩
  ext x
  simp [closedHalfspace]

lemma isPolyhedralCone_isConic {S : Set E} (h : IsPolyhedralCone S) : IsConic S := by
  obtain ⟨As, _, rfl⟩ := h
  intro x hx c hc
  refine mem_iInter.mpr fun a => mem_iInter.mpr fun ha =>
    isConic_closedHalfspace_zero a ?_ c hc
  exact (mem_iInter.mp ((mem_iInter.mp hx) a)) ha

/-- Arrangement associated to a homogeneous H-description: hyperplanes `(a, 0)`. -/
def coneArrangement (As : Set E) : Set (Hyperplane E) :=
  (fun a => (a, (0 : ℝ))) '' As

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma coneArrangement_finite {As : Set E} (hAs : As.Finite) :
    (coneArrangement As).Finite :=
  hAs.image _

lemma closedHalfspace_zero_eq_union (a : E) :
    closedHalfspace a 0 = {x : E | ⟪a, x⟫ = 0} ∪ {x | ⟪a, x⟫ < 0} := by
  ext x
  change ⟪a, x⟫ ≤ 0 ↔ ⟪a, x⟫ = 0 ∨ ⟪a, x⟫ < 0
  constructor
  · intro h
    rcases lt_or_eq_of_le h with hlt | heq
    · exact Or.inr hlt
    · exact Or.inl heq
  · rintro (heq | hlt)
    · exact le_of_eq heq
    · exact le_of_lt hlt

/-- A closed halfspace `{⟪a,x⟫ ≤ 0}` is a cell complex of the singleton arrangement. -/
lemma isHyperplaneCellComplex_closedHalfspace_zero (a : E) :
    IsHyperplaneCellComplex {(a, (0 : ℝ))} (closedHalfspace a 0) := by
  by_cases ha : a = 0
  · subst ha
    have : closedHalfspace (0 : E) 0 = univ := by
      ext x; change ⟪(0 : E), x⟫ ≤ 0 ↔ True; simp [inner_zero_left]
    rw [this]
    exact isHyperplaneCellComplex_univ _
  · rw [closedHalfspace_zero_eq_union]
    exact isHyperplaneCellComplex_union
      (isHyperplaneCell_cellComplex (isHyperplaneCell_eq_hyperplane ha))
      (isHyperplaneCell_cellComplex (isHyperplaneCell_eq_halfSpace_lt ha))

/-- A polyhedral cone (homogeneous H-rep) is a cell complex of its cone arrangement. -/
lemma isHyperplaneCellComplex_polyhedralCone {As : Set E} (hAs : As.Finite) :
    IsHyperplaneCellComplex (coneArrangement As)
      (⋂ a ∈ As, closedHalfspace a 0) := by
  classical
  refine Set.Finite.induction_on
    (motive := fun As' _ => As' ⊆ As →
      IsHyperplaneCellComplex (coneArrangement As)
        (⋂ a ∈ As', closedHalfspace a 0))
    As hAs ?empty ?insert subset_rfl
  · intro _hsub
    -- ⋂ over empty = univ
    have : (⋂ a ∈ (∅ : Set E), closedHalfspace a 0) = univ := by
      ext x; simp
    rw [this]
    exact isHyperplaneCellComplex_univ _
  · intro a As' _haAs' _hAs' ih hsub
    have ha : a ∈ As := hsub (Set.mem_insert a As')
    have hrest : As' ⊆ As := (subset_insert _ _).trans hsub
    have hEq : (⋂ b ∈ insert a As', closedHalfspace b 0) =
        closedHalfspace a 0 ∩ (⋂ b ∈ As', closedHalfspace b 0) := by
      ext x
      simp only [mem_iInter, mem_inter_iff, mem_insert_iff]
      constructor
      · intro hx
        exact ⟨hx a (Or.inl rfl), fun b hb => hx b (Or.inr hb)⟩
      · rintro ⟨hxa, hxAs'⟩ b hb
        rcases hb with rfl | hb
        · exact hxa
        · exact hxAs' b hb
    rw [hEq]
    exact isHyperplaneCellComplex_inter
      (isHyperplaneCellComplex_mono
        (isHyperplaneCellComplex_closedHalfspace_zero a)
        (singleton_subset_iff.mpr ⟨a, ha, rfl⟩))
      (ih hrest)

end EulersGem
