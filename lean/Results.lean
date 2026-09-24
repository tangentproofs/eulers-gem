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

/-!
# Paper-facing results

Only theorems that are **actually proved** appear here. Parked goals (Pick's,
Platonic solids) are not claimed. Tverberg dissection remains documentation-only.
-/

open scoped RealInnerProductSpace

namespace Results

/-- Euler characteristic of an `n`-simplex (including the empty face) is `0`.
Isabelle: `euler_0simplex_eq0` / `euler_nsimplex_eq0`. -/
theorem results_eulerChar_simplex (n : ℕ) : EulersGem.eulerChar n = 0 :=
  EulersGem.eulerChar_simplex n

/-- Combinatorial `m`-face count of an `n`-simplex is `C(n+1, m+1)`. -/
theorem results_card_combinatorialFaces (n m : ℕ) :
    (EulersGem.combinatorialFaces n m).card = EulersGem.faceCount n m :=
  EulersGem.card_combinatorialFaces n m

/-- Tetrahedron satisfies `V - E + F = 2` (and thus `F + V - E = 2`). -/
theorem results_tetrahedron_polyhedron_numbers :
    (EulersGem.faceCount 3 0 : ℤ) - EulersGem.faceCount 3 1 + EulersGem.faceCount 3 2 = 2 :=
  EulersGem.tetrahedron_polyhedron_numbers

/-- Bookkeeping: Euler char `0` with one empty face and one solid ⇒ polyhedron formula. -/
theorem results_polyhedron_formula_of_eulerChar (V E F : ℕ)
    (h : (1 : ℤ) - V + E - F + 1 = 0) :
    (F : ℤ) + V - E = 2 :=
  EulersGem.polyhedron_formula_of_eulerChar V E F h

/-- Alternating face counts of an abstract `n`-simplex (no empty face) equal `1`.
Paulson / Euler–Poincaré for the simplex: `∑_{d=0}^{n} (-1)^d C(n+1,d+1) = 1`. -/
theorem results_faceEulerSum_simplex_faceCount (n : ℕ) :
    ∑ d ∈ Finset.range (n + 1), (-1 : ℤ) ^ d * (EulersGem.faceCount n d : ℤ) = 1 :=
  EulersGem.faceEulerSum_simplex_faceCount n

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

end Results
