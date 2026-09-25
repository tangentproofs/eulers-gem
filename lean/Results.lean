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
import EulersGem.Picks

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
constructions, and Funkenbusch / triangulation *count identities* (not Pick).
**Classical geometric Pick's theorem is not claimed** — see `Picks.lean`,
`PHASE_B_PLAN.md`, `PICKS_CLAUDE_AUDIT.md`.
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
  native_decide

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
  · native_decide
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

end Results
