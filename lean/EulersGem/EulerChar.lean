/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.AffDim
import EulersGem.Hyperplane
import EulersGem.CellGeometry
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# Combinatorial Euler characteristic of a hyperplane cell complex

Lean port of Paulson AFP `Euler_characteristic`:

```
Euler_characteristic A S = ∑_{C cell of A, C ⊆ S} (-1)^{affDim C}
```

Plus additivity over disjoint cell complexes, evaluation on the empty arrangement,
and scaffolding toward **invariance under refining arrangements**. Geometric
substrate for the insert/cutting lemma lives in `EulersGem.CellGeometry`
(open∩affine, relative interior, halfspace affDim preservation).
-/

open scoped BigOperators RealInnerProductSpace
open Classical Set Finset

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace EulersGem

/-- Sign of a cell in the combinatorial Euler sum: `(-1)^{affDim C}`. -/
noncomputable def cellSign (C : Set E) : ℤ :=
  (-1 : ℤ) ^ (affDim C).toNat

/-- Combinatorial Euler characteristic of `S` relative to arrangement `A`.
Isabelle: `Euler_characteristic`. Returns `0` if there are infinitely many cells
(Paulson always assumes `finite A`). -/
noncomputable def eulerCharacteristic (A : Set (Hyperplane E)) (S : Set E) : ℤ :=
  if h : {C : Set E | IsHyperplaneCell A C ∧ C ⊆ S}.Finite then
    ∑ C ∈ h.toFinset, cellSign C
  else
    0

lemma eulerCharacteristic_of_finite {A : Set (Hyperplane E)} {S : Set E}
    (h : {C : Set E | IsHyperplaneCell A C ∧ C ⊆ S}.Finite) :
    eulerCharacteristic A S = ∑ C ∈ h.toFinset, cellSign C := by
  simp [eulerCharacteristic, h]

lemma eulerCharacteristic_eq_sum {A : Set (Hyperplane E)} {S : Set E}
    (hA : A.Finite) :
    eulerCharacteristic A S =
      ∑ C ∈ (finite_isHyperplaneCell_restrict hA (fun C => C ⊆ S)).toFinset, cellSign C :=
  eulerCharacteristic_of_finite _

@[simp] lemma eulerCharacteristic_empty (A : Set (Hyperplane E)) :
    eulerCharacteristic A (∅ : Set E) = 0 := by
  unfold eulerCharacteristic
  split_ifs with h
  · have hempty : h.toFinset = ∅ := by
      ext C
      simp only [Finite.mem_toFinset, mem_ofPred_eq, Finset.notMem_empty, iff_false]
      intro ⟨hC, hsub⟩
      obtain ⟨x, hx⟩ := nonempty_isHyperplaneCell hC
      exact hsub hx
    rw [hempty, Finset.sum_empty]
  · rfl

/-- The cells of `A` contained in a cell `C` are exactly `{C}`. -/
lemma cells_subset_cell {A : Set (Hyperplane E)} {C : Set E}
    (hC : IsHyperplaneCell A C) :
    {D : Set E | IsHyperplaneCell A D ∧ D ⊆ C} = {C} := by
  ext D
  simp only [mem_ofPred_eq, mem_singleton_iff]
  constructor
  · intro ⟨hD, hsub⟩
    by_contra hne
    obtain ⟨x, hx⟩ := nonempty_isHyperplaneCell hD
    exact (disjoint_left.mp (disjoint_isHyperplaneCell hD hC hne)) hx (hsub hx)
  · rintro rfl
    exact ⟨hC, Subset.rfl⟩

/-- Euler characteristic of a single cell is its sign. Isabelle: `Euler_characteristic_cell`. -/
lemma eulerCharacteristic_cell {A : Set (Hyperplane E)} {C : Set E}
    (hA : A.Finite) (hC : IsHyperplaneCell A C) :
    eulerCharacteristic A C = cellSign C := by
  have hfin := finite_isHyperplaneCell_restrict hA (fun D => D ⊆ C)
  rw [eulerCharacteristic_of_finite hfin]
  have hset := cells_subset_cell hC
  have : hfin.toFinset = ({C} : Finset (Set E)) := by
    ext D
    simp [hset]
  simp [this]

/-- Cells contained in a union of `A`-cells are exactly those cells. -/
lemma cells_subset_sUnion {A : Set (Hyperplane E)} {Cs : Set (Set E)}
    (hCs : ∀ C ∈ Cs, IsHyperplaneCell A C) :
    {D : Set E | IsHyperplaneCell A D ∧ D ⊆ ⋃₀ Cs} = Cs := by
  ext D
  simp only [mem_ofPred_eq]
  constructor
  · intro ⟨hD, hsub⟩
    obtain ⟨x, hx⟩ := nonempty_isHyperplaneCell hD
    obtain ⟨C, hC, hxC⟩ := hsub hx
    have hEq : D = C := by
      by_contra hne
      exact (disjoint_left.mp (disjoint_isHyperplaneCell hD (hCs C hC) hne)) hx hxC
    rwa [hEq]
  · intro hD
    exact ⟨hCs D hD, subset_sUnion_of_mem hD⟩

/-- Euler characteristic of a union of cells is the sum of their signs.
Isabelle: `Euler_characteristic_cell_Union`. -/
lemma eulerCharacteristic_cell_sUnion {A : Set (Hyperplane E)} {Cs : Set (Set E)}
    (hA : A.Finite) (hCs : ∀ C ∈ Cs, IsHyperplaneCell A C) :
    eulerCharacteristic A (⋃₀ Cs) =
      ∑ C ∈ (show Cs.Finite from
        (finite_isHyperplaneCell hA).subset fun C hC => hCs C hC).toFinset,
        cellSign C := by
  have hfinCs : Cs.Finite :=
    (finite_isHyperplaneCell hA).subset fun C hC => hCs C hC
  have hfin := finite_isHyperplaneCell_restrict hA (fun D => D ⊆ ⋃₀ Cs)
  rw [eulerCharacteristic_of_finite hfin]
  have hset := cells_subset_sUnion hCs
  congr 1
  ext D
  simp [hset]

/-- Additivity for a disjoint union of two cell complexes.
Isabelle: `Euler_characteristic_cellcomplex_Un`. -/
lemma eulerCharacteristic_cellcomplex_union {A : Set (Hyperplane E)} {S T : Set E}
    (hA : A.Finite) (hS : IsHyperplaneCellComplex A S) (hT : IsHyperplaneCellComplex A T)
    (hd : Disjoint S T) :
    eulerCharacteristic A (S ∪ T) =
      eulerCharacteristic A S + eulerCharacteristic A T := by
  have hfinST := finite_isHyperplaneCell_restrict hA (fun C => C ⊆ S ∪ T)
  have hfinS := finite_isHyperplaneCell_restrict hA (fun C => C ⊆ S)
  have hfinT := finite_isHyperplaneCell_restrict hA (fun C => C ⊆ T)
  rw [eulerCharacteristic_of_finite hfinST, eulerCharacteristic_of_finite hfinS,
    eulerCharacteristic_of_finite hfinT]
  have hEq : {C : Set E | IsHyperplaneCell A C ∧ C ⊆ S ∪ T} =
      {C | IsHyperplaneCell A C ∧ C ⊆ S} ∪ {C | IsHyperplaneCell A C ∧ C ⊆ T} := by
    ext C
    simp only [mem_union, mem_ofPred_eq]
    constructor
    · intro ⟨hC, hsub⟩
      -- C meets S or T; by cell_subset_cellcomplex it is contained in that side
      by_cases hCS : (C ∩ S).Nonempty
      · have : C ⊆ S := (cell_subset_cellcomplex hC hS).mpr hCS
        exact Or.inl ⟨hC, this⟩
      · have hCT : (C ∩ T).Nonempty := by
          obtain ⟨x, hx⟩ := nonempty_isHyperplaneCell hC
          have : x ∈ S ∨ x ∈ T := hsub hx
          cases this with
          | inl hxS => exact absurd ⟨x, hx, hxS⟩ hCS
          | inr hxT => exact ⟨x, hx, hxT⟩
        exact Or.inr ⟨hC, (cell_subset_cellcomplex hC hT).mpr hCT⟩
    · rintro (⟨hC, hS'⟩ | ⟨hC, hT'⟩)
      · exact ⟨hC, hS'.trans subset_union_left⟩
      · exact ⟨hC, hT'.trans subset_union_right⟩
  have hdisj' :
      Disjoint {C : Set E | IsHyperplaneCell A C ∧ C ⊆ S}
        {C | IsHyperplaneCell A C ∧ C ⊆ T} := by
    refine Set.disjoint_left.mpr ?_
    intro C ⟨hC, hCS⟩ ⟨_, hCT⟩
    obtain ⟨x, hx⟩ := nonempty_isHyperplaneCell hC
    exact (Set.disjoint_left.mp hd) (hCS hx) (hCT hx)
  have hfin_eq :
      hfinST.toFinset = hfinS.toFinset ∪ hfinT.toFinset := by
    ext C
    simp only [Finite.mem_toFinset, Finset.mem_union]
    simpa [Set.mem_union] using (Set.ext_iff.mp hEq C)
  have hdisjF : Disjoint hfinS.toFinset hfinT.toFinset := by
    refine Finset.disjoint_left.mpr ?_
    intro C hS' hT'
    have hS'' : C ∈ {C : Set E | IsHyperplaneCell A C ∧ C ⊆ S} :=
      (Finite.mem_toFinset _).mp hS'
    have hT'' : C ∈ {C : Set E | IsHyperplaneCell A C ∧ C ⊆ T} :=
      (Finite.mem_toFinset _).mp hT'
    exact (Set.disjoint_left.mp hdisj') hS'' hT''
  rw [hfin_eq, Finset.sum_union hdisjF]

/-- Empty arrangement: the only cell is `univ`, so Euler char of `univ` is
`(-1)^{finrank}`. -/
lemma eulerCharacteristic_empty_arrangement_univ
    [FiniteDimensional ℝ E] [Nonempty E] :
    eulerCharacteristic (∅ : Set (Hyperplane E)) (univ : Set E) =
      (-1 : ℤ) ^ Module.finrank ℝ E := by
  have hA : (∅ : Set (Hyperplane E)).Finite := finite_empty
  have hC : IsHyperplaneCell (∅ : Set (Hyperplane E)) (univ : Set E) :=
    (isHyperplaneCell_empty_arrangement univ).mpr rfl
  rw [eulerCharacteristic_cell hA hC, cellSign, affDim_univ]
  simp

/-- Trivial invariance: same arrangement. -/
lemma eulerCharacteristic_invariant_refl {A : Set (Hyperplane E)} {S : Set E} :
    eulerCharacteristic A S = eulerCharacteristic A S :=
  rfl

/-- If `A ⊆ B` and every `A`-cell inside `S` remains an `A`-cell that is also a
`B`-cell (i.e. refining does not split those cells), Euler chars agree.
Special case of refinement invariance when the new hyperplanes do not cut `S`. -/
lemma eulerCharacteristic_eq_of_same_cells {A B : Set (Hyperplane E)} {S : Set E}
    (hA : A.Finite) (hB : B.Finite)
    (hEq : {C : Set E | IsHyperplaneCell A C ∧ C ⊆ S} =
           {C : Set E | IsHyperplaneCell B C ∧ C ⊆ S}) :
    eulerCharacteristic A S = eulerCharacteristic B S := by
  rw [eulerCharacteristic_eq_sum hA, eulerCharacteristic_eq_sum hB]
  congr 1
  ext C
  simp only [Finite.mem_toFinset]
  change (IsHyperplaneCell A C ∧ C ⊆ S) ↔ (IsHyperplaneCell B C ∧ C ⊆ S)
  simpa using (Set.ext_iff.mp hEq C)

/-- Refinement invariance when `A = B` as sets of hyperplanes (finite). -/
lemma eulerCharacteristic_invariant_of_eq {A B : Set (Hyperplane E)} {S : Set E}
    (_hA : A.Finite) (_hB : B.Finite) (hEq : A = B) :
    eulerCharacteristic A S = eulerCharacteristic B S := by
  subst hEq
  rfl


/-! ### Toward refinement invariance (insert one hyperplane) -/

lemma cellSign_cell_inter_halfSpace_lt {A : Set (Hyperplane E)} {C : Set E}
    (hA : A.Finite) (hC : IsHyperplaneCell A C) (a : E) (b : ℝ)
    (hne : (C ∩ {x | ⟪a, x⟫ < b}).Nonempty) :
    cellSign (C ∩ {x | ⟪a, x⟫ < b}) = cellSign C := by
  simp only [cellSign, affDim_cell_inter_halfSpace_lt hA hC a b hne]

lemma cellSign_cell_inter_halfSpace_gt {A : Set (Hyperplane E)} {C : Set E}
    (hA : A.Finite) (hC : IsHyperplaneCell A C) (a : E) (b : ℝ)
    (hne : (C ∩ {x | b < ⟪a, x⟫}).Nonempty) :
    cellSign (C ∩ {x | b < ⟪a, x⟫}) = cellSign C := by
  simp only [cellSign, affDim_cell_inter_halfSpace_gt hA hC a b hne]

/-- If every `A`-cell inside `S` remains a cell of `insert h A`, Euler chars agree.
Special case of insert when the new hyperplane does not cut any cell of `S`. -/
lemma eulerCharacteristic_insert_of_cells_preserved {A : Set (Hyperplane E)}
    {h : Hyperplane E} {S : Set E}
    (hA : A.Finite)
    (hPres : {C : Set E | IsHyperplaneCell A C ∧ C ⊆ S} =
             {C : Set E | IsHyperplaneCell (insert h A) C ∧ C ⊆ S}) :
    eulerCharacteristic (insert h A) S = eulerCharacteristic A S := by
  have hB : (insert h A).Finite := hA.insert _
  exact eulerCharacteristic_eq_of_same_cells hB hA hPres.symm

/-- Inserting a hyperplane already in the arrangement does nothing. -/
lemma eulerCharacteristic_insert_mem {A : Set (Hyperplane E)} {h : Hyperplane E}
    {S : Set E} (_hA : A.Finite) (hh : h ∈ A) :
    eulerCharacteristic (insert h A) S = eulerCharacteristic A S := by
  have : insert h A = A := insert_eq_of_mem hh
  simp [this]

/-- Degenerate hyperplane `(0, b)` does not refine the arrangement's cells
(singleton cell is `univ`), so Euler char is unchanged on any cell complex. -/
lemma eulerCharacteristic_insert_zero {A : Set (Hyperplane E)} {b : ℝ} {S : Set E}
    (hA : A.Finite) (_hS : IsHyperplaneCellComplex A S) :
    eulerCharacteristic (insert ((0 : E), b) A) S = eulerCharacteristic A S := by
  -- Cells of insert = cells of A, via union with degenerate singleton {univ}
  -- Use: insert (0,b) A = {(0,b)} ∪ A, and cells of {(0,b)} is {univ}
  refine eulerCharacteristic_insert_of_cells_preserved hA ?_
  ext C
  constructor
  · intro ⟨hC, hsub⟩
    -- An A-cell is an (insert)-cell-complex; need it to be a single cell
    -- When the new hyperplane is degenerate, HyperplaneEquiv is unchanged
    have hEq : HyperplaneEquiv (insert ((0 : E), b) A) = HyperplaneEquiv A := by
      ext x y
      simp only [HyperplaneEquiv, mem_insert_iff]
      constructor
      · intro h hp hpA
        exact h hp (Or.inr hpA)
      · intro h hp hpA
        rcases hpA with rfl | hpA
        · -- side of (0,b) is constant
          simp [hyperplaneSide, inner_zero_left]
        · exact h hp hpA
    -- So cells coincide
    obtain ⟨x, rfl⟩ := hC
    refine ⟨⟨x, ?_⟩, hsub⟩
    ext y
    simp only [mem_ofPred_eq]
    exact Iff.of_eq (congrFun (congrFun hEq x) y).symm
  · intro ⟨hC, hsub⟩
    obtain ⟨x, rfl⟩ := hC
    refine ⟨⟨x, ?_⟩, hsub⟩
    ext y
    simp only [mem_ofPred_eq]
    have hEq : HyperplaneEquiv (insert ((0 : E), b) A) = HyperplaneEquiv A := by
      ext u v
      simp only [HyperplaneEquiv, mem_insert_iff]
      constructor
      · intro h hp hpA; exact h hp (Or.inr hpA)
      · intro h hp hpA
        rcases hpA with rfl | hpA
        · simp [hyperplaneSide, inner_zero_left]
        · exact h hp hpA
    exact Iff.of_eq (congrFun (congrFun hEq x) y)


end EulersGem
