/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Basic.Sign.Defs

/-!
# Hyperplane arrangements (Paulson substrate)

Lean port of the opening of Lawrence C. Paulson's AFP
[*Euler's Polyhedron Formula*](https://isa-afp.org/entries/Euler_Polyhedron_Formula.html)
(theory `Euler_Formula`):

* `hyperplaneSide` — which side of an affine hyperplane a point lies on
* `HyperplaneEquiv` — same side of every hyperplane in an arrangement
* `IsHyperplaneCell` — equivalence classes (= cells of the arrangement)

Isabelle names: `hyperplane_side`, `hyperplane_equiv`, `hyperplane_cell`.

This file proves the elementary structural lemmas (equivalence relation, empty
arrangement, disjointness, singleton classification, convexity). Cell complexes,
Euler characteristic, and invariance come next.
-/

open scoped RealInnerProductSpace
open Set SignType

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace EulersGem

/-- An affine hyperplane given in H-description by `⟪a, x⟫ = b`.
Degenerate when `a = 0` (matches Paulson: the whole space or empty, via `sgn`). -/
abbrev Hyperplane (E : Type*) := E × ℝ

/-- Which side of the hyperplane `(a, b)` the point `x` lies on:
`sign (⟪a, x⟫ − b) ∈ {−1, 0, 1}`. Isabelle: `hyperplane_side`. -/
noncomputable def hyperplaneSide (h : Hyperplane E) (x : E) : SignType :=
  SignType.sign (⟪h.1, x⟫ - h.2)

/-- Points equivalent under arrangement `A`: same side of every hyperplane in `A`.
Isabelle: `hyperplane_equiv`. -/
def HyperplaneEquiv (A : Set (Hyperplane E)) (x y : E) : Prop :=
  ∀ h ∈ A, hyperplaneSide h x = hyperplaneSide h y

lemma hyperplaneEquiv_refl (A : Set (Hyperplane E)) (x : E) :
    HyperplaneEquiv A x x := fun _ _ => rfl

lemma hyperplaneEquiv_symm {A : Set (Hyperplane E)} {x y : E}
    (h : HyperplaneEquiv A x y) : HyperplaneEquiv A y x := by
  intro hp hpA
  exact (h hp hpA).symm

lemma hyperplaneEquiv_trans {A : Set (Hyperplane E)} {x y z : E}
    (hxy : HyperplaneEquiv A x y) (hyz : HyperplaneEquiv A y z) :
    HyperplaneEquiv A x z := by
  intro hp hpA
  exact (hxy hp hpA).trans (hyz hp hpA)

lemma hyperplaneEquiv_union (A B : Set (Hyperplane E)) (x y : E) :
    HyperplaneEquiv (A ∪ B) x y ↔ HyperplaneEquiv A x y ∧ HyperplaneEquiv B x y := by
  constructor
  · intro h
    exact ⟨fun hp hpA => h hp (Or.inl hpA), fun hp hpB => h hp (Or.inr hpB)⟩
  · rintro ⟨hA, hB⟩ hp hpAB
    cases hpAB with
    | inl h => exact hA hp h
    | inr h => exact hB hp h

/-- `C` is a cell of arrangement `A` iff it is an equivalence class of
`HyperplaneEquiv A`. Isabelle: `hyperplane_cell`. -/
def IsHyperplaneCell (A : Set (Hyperplane E)) (C : Set E) : Prop :=
  ∃ x, C = {y | HyperplaneEquiv A x y}

lemma isHyperplaneCell_iff (A : Set (Hyperplane E)) (C : Set E) :
    IsHyperplaneCell A C ↔ ∃ x, C = {y | HyperplaneEquiv A x y} :=
  Iff.rfl

lemma not_isHyperplaneCell_empty (A : Set (Hyperplane E)) :
    ¬ IsHyperplaneCell A (∅ : Set E) := by
  rintro ⟨x, hx⟩
  have : x ∈ (∅ : Set E) := by
    rw [hx]
    exact hyperplaneEquiv_refl A x
  exact this

lemma nonempty_isHyperplaneCell {A : Set (Hyperplane E)} {C : Set E}
    (h : IsHyperplaneCell A C) : C.Nonempty := by
  obtain ⟨x, rfl⟩ := h
  exact ⟨x, hyperplaneEquiv_refl A x⟩

lemma iUnion_isHyperplaneCell (A : Set (Hyperplane E)) :
    ⋃₀ {C | IsHyperplaneCell A C} = univ := by
  ext x
  constructor
  · intro; trivial
  · intro
    refine ⟨{y | HyperplaneEquiv A x y}, ?_, hyperplaneEquiv_refl A x⟩
    exact ⟨x, rfl⟩

lemma disjoint_isHyperplaneCell {A : Set (Hyperplane E)} {C₁ C₂ : Set E}
    (h₁ : IsHyperplaneCell A C₁) (h₂ : IsHyperplaneCell A C₂) (hne : C₁ ≠ C₂) :
    Disjoint C₁ C₂ := by
  obtain ⟨x₁, rfl⟩ := h₁
  obtain ⟨x₂, rfl⟩ := h₂
  rw [disjoint_iff_inter_eq_empty]
  ext y
  simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false]
  intro ⟨hy₁, hy₂⟩
  -- hy₁ : x₁ ~ y, hy₂ : x₂ ~ y  ⇒  the two classes coincide
  apply hne
  ext z
  simp only [mem_ofPred_eq]
  constructor
  · -- x₁ ~ z ⇒ x₂ ~ z   via  x₂ ~ y ~ x₁ ~ z
    intro hz
    have h_yx₁ : HyperplaneEquiv A y x₁ := hyperplaneEquiv_symm (A := A) hy₁
    have h_x₂y : HyperplaneEquiv A x₂ y := hy₂
    have h_yx₁z : HyperplaneEquiv A y z :=
      hyperplaneEquiv_trans (A := A) h_yx₁ hz
    exact hyperplaneEquiv_trans (A := A) h_x₂y h_yx₁z
  · -- x₂ ~ z ⇒ x₁ ~ z   via  x₁ ~ y ~ x₂ ~ z
    intro hz
    have h_yx₂ : HyperplaneEquiv A y x₂ := hyperplaneEquiv_symm (A := A) hy₂
    have h_x₁y : HyperplaneEquiv A x₁ y := hy₁
    have h_yx₂z : HyperplaneEquiv A y z :=
      hyperplaneEquiv_trans (A := A) h_yx₂ hz
    exact hyperplaneEquiv_trans (A := A) h_x₁y h_yx₂z

lemma isHyperplaneCell_empty_arrangement (C : Set E) :
    IsHyperplaneCell (∅ : Set (Hyperplane E)) C ↔ C = univ := by
  constructor
  · rintro ⟨x, rfl⟩
    ext y
    simp [HyperplaneEquiv]
  · intro h
    refine ⟨(0 : E), ?_⟩
    rw [h]
    ext y
    simp [HyperplaneEquiv]

/-- Linear map `x ↦ ⟪a, x⟫`. -/
lemma isLinearMap_inner (a : E) : IsLinearMap ℝ (fun x : E => ⟪a, x⟫) where
  map_add := fun x y => by simp [inner_add_right]
  map_smul := fun c x => by simp [inner_smul_right]

lemma hyperplaneSide_eq_zero_iff (a : E) (b : ℝ) (x : E) :
    hyperplaneSide (a, b) x = 0 ↔ ⟪a, x⟫ = b := by
  simp [hyperplaneSide, sign_eq_zero_iff, sub_eq_zero]

lemma hyperplaneSide_eq_one_iff (a : E) (b : ℝ) (x : E) :
    hyperplaneSide (a, b) x = 1 ↔ b < ⟪a, x⟫ := by
  simp [hyperplaneSide, sign_eq_one_iff, sub_pos]

lemma hyperplaneSide_eq_neg_one_iff (a : E) (b : ℝ) (x : E) :
    hyperplaneSide (a, b) x = -1 ↔ ⟪a, x⟫ < b := by
  simp [hyperplaneSide, sign_eq_neg_one_iff, sub_neg]

/-- Fixed hyperplane `(a,b)`: the set of points with a given side is a hyperplane
or an open half-space (hence convex). -/
lemma convex_hyperplaneSide_eq (a : E) (b : ℝ) (s : SignType) :
    Convex ℝ {y : E | hyperplaneSide (a, b) y = s} := by
  have hlin : IsLinearMap ℝ (fun x : E => ⟪a, x⟫) := isLinearMap_inner a
  rcases (trichotomy s) with hs | hs | hs
  · have : {y : E | hyperplaneSide (a, b) y = s} = {y | ⟪a, y⟫ < b} := by
      ext y; simp [hs, hyperplaneSide_eq_neg_one_iff]
    rw [this]; exact convex_halfSpace_lt hlin b
  · have : {y : E | hyperplaneSide (a, b) y = s} = {y | ⟪a, y⟫ = b} := by
      ext y; simp [hs, hyperplaneSide_eq_zero_iff]
    rw [this]; exact convex_hyperplane hlin b
  · have : {y : E | hyperplaneSide (a, b) y = s} = {y | b < ⟪a, y⟫} := by
      ext y; simp [hs, hyperplaneSide_eq_one_iff]
    rw [this]; exact convex_halfSpace_gt hlin b

/-- Cells of a singleton arrangement `{ (a,b) }` are the hyperplane or one of the
two open half-spaces. Isabelle: `hyperplane_cell_singleton_cases`. -/
lemma isHyperplaneCell_singleton_cases {a : E} {b : ℝ} {C : Set E}
    (h : IsHyperplaneCell {(a, b)} C) :
    C = {x | ⟪a, x⟫ = b} ∨ C = {x | ⟪a, x⟫ < b} ∨ C = {x | b < ⟪a, x⟫} := by
  obtain ⟨x, rfl⟩ := h
  have tri := trichotomy (hyperplaneSide (a, b) x)
  rcases tri with h0 | h0 | h0
  · refine Or.inr (Or.inl ?_)
    ext y
    simp only [mem_ofPred_eq, HyperplaneEquiv, mem_singleton_iff, forall_eq]
    constructor
    · intro hy
      exact (hyperplaneSide_eq_neg_one_iff a b y).mp (by simpa [h0] using hy.symm)
    · intro hy
      have : hyperplaneSide (a, b) y = -1 :=
        (hyperplaneSide_eq_neg_one_iff a b y).mpr hy
      simp [h0, this]
  · refine Or.inl ?_
    ext y
    simp only [mem_ofPred_eq, HyperplaneEquiv, mem_singleton_iff, forall_eq]
    constructor
    · intro hy
      exact (hyperplaneSide_eq_zero_iff a b y).mp (by simpa [h0] using hy.symm)
    · intro hy
      have : hyperplaneSide (a, b) y = 0 :=
        (hyperplaneSide_eq_zero_iff a b y).mpr hy
      simp [h0, this]
  · refine Or.inr (Or.inr ?_)
    ext y
    simp only [mem_ofPred_eq, HyperplaneEquiv, mem_singleton_iff, forall_eq]
    constructor
    · intro hy
      exact (hyperplaneSide_eq_one_iff a b y).mp (by simpa [h0] using hy.symm)
    · intro hy
      have : hyperplaneSide (a, b) y = 1 :=
        (hyperplaneSide_eq_one_iff a b y).mpr hy
      simp [h0, this]

/-- Every cell is convex. Isabelle: `hyperplane_cell_convex`. -/
lemma isHyperplaneCell_convex {A : Set (Hyperplane E)} {C : Set E}
    (hC : IsHyperplaneCell A C) : Convex ℝ C := by
  obtain ⟨c, rfl⟩ := hC
  have eq : {y | HyperplaneEquiv A c y} =
      ⋂ h ∈ A, {y | hyperplaneSide h c = hyperplaneSide h y} := by
    ext y; simp [HyperplaneEquiv]
  rw [eq]
  refine convex_iInter fun h => convex_iInter fun _ => ?_
  have : {y : E | hyperplaneSide h c = hyperplaneSide h y} =
      {y | hyperplaneSide h y = hyperplaneSide h c} := by
    ext y; constructor <;> intro hy <;> exact hy.symm
  rw [this]
  obtain ⟨a, b⟩ := h
  exact convex_hyperplaneSide_eq a b (hyperplaneSide (a, b) c)

/-- Cell complex: a union of cells of arrangement `A`.
Isabelle: `hyperplane_cellcomplex`. -/
def IsHyperplaneCellComplex (A : Set (Hyperplane E)) (S : Set E) : Prop :=
  ∃ 𝒯 : Set (Set E), (∀ C ∈ 𝒯, IsHyperplaneCell A C) ∧ S = ⋃₀ 𝒯

lemma isHyperplaneCellComplex_empty (A : Set (Hyperplane E)) :
    IsHyperplaneCellComplex A (∅ : Set E) :=
  ⟨∅, by simp⟩

lemma isHyperplaneCell_cellComplex {A : Set (Hyperplane E)} {C : Set E}
    (h : IsHyperplaneCell A C) : IsHyperplaneCellComplex A C :=
  ⟨{C}, by simp [h]⟩

lemma isHyperplaneCellComplex_univ (A : Set (Hyperplane E)) :
    IsHyperplaneCellComplex A (univ : Set E) :=
  ⟨{C | IsHyperplaneCell A C}, ⟨fun _ h => h, (iUnion_isHyperplaneCell A).symm⟩⟩

lemma isHyperplaneCellComplex_sUnion {A : Set (Hyperplane E)}
    {𝒞 : Set (Set E)} (h : ∀ S ∈ 𝒞, IsHyperplaneCellComplex A S) :
    IsHyperplaneCellComplex A (⋃₀ 𝒞) := by
  -- Flatten the witnessing cell collections.
  let 𝒯 : Set (Set E) :=
    {C | ∃ S ∈ 𝒞, ∃ ℱ, (∀ D ∈ ℱ, IsHyperplaneCell A D) ∧ S = ⋃₀ ℱ ∧ C ∈ ℱ}
  refine ⟨𝒯, ⟨?_, ?_⟩⟩
  · intro C hC
    obtain ⟨S, _, ℱ, hcells, _, hCℱ⟩ := hC
    exact hcells C hCℱ
  · ext x
    constructor
    · intro hx
      obtain ⟨S, hS, hxS⟩ := hx
      obtain ⟨ℱ, hcells, hSeq⟩ := h S hS
      have : x ∈ ⋃₀ ℱ := by simpa [hSeq] using hxS
      obtain ⟨C, hC, hxC⟩ := this
      exact ⟨C, ⟨S, hS, ℱ, hcells, hSeq, hC⟩, hxC⟩
    · intro hx
      obtain ⟨C, ⟨S, hS, ℱ, hcells, hSeq, hC⟩, hxC⟩ := hx
      refine ⟨S, hS, ?_⟩
      have : x ∈ ⋃₀ ℱ := ⟨C, hC, hxC⟩
      simpa [hSeq] using this

lemma isHyperplaneCellComplex_union {A : Set (Hyperplane E)} {S T : Set E}
    (hS : IsHyperplaneCellComplex A S) (hT : IsHyperplaneCellComplex A T) :
    IsHyperplaneCellComplex A (S ∪ T) := by
  simpa [sUnion_pair] using
    isHyperplaneCellComplex_sUnion (𝒞 := {S, T}) (by
      intro U hU
      simp only [mem_insert_iff, mem_singleton_iff] at hU
      rcases hU with rfl | rfl <;> assumption)

end EulersGem
