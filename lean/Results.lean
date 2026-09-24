/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.SimplexEuler
import EulersGem.Polyhedron

/-!
# Paper-facing results

Only theorems that are **actually proved** appear here. Open goals for general
polytopes / the 3D polyhedron formula / Tverberg dissection live in
`EulersGem/Polyhedron.lean` as documentation strings and are not claimed.
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

end Results
