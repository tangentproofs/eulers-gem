/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.SimplexEuler
import EulersGem.Polyhedron
import EulersGem.EulerPoincare

/-!
# Paper-facing results

Only theorems that are **actually proved** appear here. Open goals for general
polytopes / the 3D polyhedron formula / Tverberg dissection live in
`EulersGem/Polyhedron.lean` / `EulersGem/EulerPoincare.lean` as documentation
strings and are not claimed.
-/

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

end Results
