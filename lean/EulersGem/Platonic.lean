/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import Mathlib.Tactic

/-!
# Combinatorial Schläfli classification (not geometric Platonic solids)

Following Isabelle `Poly100.thy` (`PLATONIC_SOLIDS`) and the classical Euler
*count* argument (Richeson / Schläfli pairs). This is **not** a formalization of
geometrically regular polyhedra in `ℝ³`.

If every face is an `s`-gon, exactly `m` faces meet at each vertex (`s,m ≥ 3`),
double-counting gives `s F = 2 E` and `m V = 2 E`, and Euler's formula
`V − E + F = 2` holds, then

```
(s, m) ∈ {(3,3), (3,4), (3,5), (4,3), (5,3)}
```

We also exhibit five combinatorial `(V,E,F)` witnesses (Euler bookkeeping only).

Key identity (multiply Euler by `s m` and substitute double-counting):

```
E * (2s + 2m − s m) = 2 s m
```

hence `(s−2)(m−2) < 4`, which with `s,m ≥ 3` yields exactly the five pairs.
-/

namespace EulersGem
namespace Platonic

/-- Double-counting hypotheses for a combinatorially regular 3-polyhedron. -/
structure RegularNumbers where
  V : ℕ
  E : ℕ
  F : ℕ
  s : ℕ
  m : ℕ
  hs : 3 ≤ s
  hm : 3 ≤ m
  hE : 0 < E
  hFace : s * F = 2 * E
  hVert : m * V = 2 * E
  hEuler : (V : ℤ) - E + F = 2

/-- From Euler + double-counting: `E * (2s + 2m − s*m) = 2*s*m` (as ℤ). -/
theorem mul_euler_int (R : RegularNumbers) :
    (R.E : ℤ) * ((2 * R.s + 2 * R.m : ℤ) - R.s * R.m) = 2 * R.s * R.m := by
  have hEul : (R.V : ℤ) - R.E + R.F = 2 := R.hEuler
  have hmV : (R.m : ℤ) * R.V = 2 * R.E := by exact_mod_cast R.hVert
  have hsF : (R.s : ℤ) * R.F = 2 * R.E := by exact_mod_cast R.hFace
  have hsm : (R.s * R.m : ℤ) * ((R.V : ℤ) - R.E + R.F) = 2 * R.s * R.m := by
    rw [hEul]; ring
  have hV' : (R.s * R.m : ℤ) * R.V = 2 * R.s * R.E := by
    calc
      (R.s * R.m : ℤ) * R.V = (R.s : ℤ) * ((R.m : ℤ) * R.V) := by ring
      _ = (R.s : ℤ) * (2 * R.E) := by rw [hmV]
      _ = 2 * R.s * R.E := by ring
  have hF' : (R.s * R.m : ℤ) * R.F = 2 * R.m * R.E := by
    calc
      (R.s * R.m : ℤ) * R.F = (R.m : ℤ) * ((R.s : ℤ) * R.F) := by ring
      _ = (R.m : ℤ) * (2 * R.E) := by rw [hsF]
      _ = 2 * R.m * R.E := by ring
  have hL' :
      (2 * R.s * R.E : ℤ) - (R.s * R.m : ℤ) * R.E + (2 * R.m * R.E : ℤ)
        = 2 * R.s * R.m := by
    calc
      _ = (R.s * R.m : ℤ) * R.V - (R.s * R.m : ℤ) * R.E + (R.s * R.m : ℤ) * R.F := by
            rw [← hV', ← hF']
      _ = (R.s * R.m : ℤ) * ((R.V : ℤ) - R.E + R.F) := by ring
      _ = 2 * R.s * R.m := hsm
  calc
    (R.E : ℤ) * ((2 * R.s + 2 * R.m : ℤ) - R.s * R.m)
        = (2 * R.s * R.E : ℤ) - (R.s * R.m : ℤ) * R.E + (2 * R.m * R.E : ℤ) := by ring
    _ = 2 * R.s * R.m := hL'

/-- `(s−2)(m−2) < 4` from the ℤ multiplier identity and `E > 0`. -/
theorem sub_mul_lt_four (R : RegularNumbers) :
    (R.s - 2) * (R.m - 2) < 4 := by
  have hs2 : 2 ≤ R.s := le_trans (by decide : (2 : ℕ) ≤ 3) R.hs
  have hm2 : 2 ≤ R.m := le_trans (by decide : (2 : ℕ) ≤ 3) R.hm
  have h := mul_euler_int R
  have hEpos : (0 : ℤ) < R.E := by exact_mod_cast R.hE
  have hRHSpos : (0 : ℤ) < 2 * R.s * R.m := by
    have hs : (0 : ℤ) < R.s := by
      exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℕ) < 3) R.hs)
    have hm : (0 : ℤ) < R.m := by
      exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℕ) < 3) R.hm)
    nlinarith
  have hcoeff_pos : (0 : ℤ) < (2 * R.s + 2 * R.m : ℤ) - R.s * R.m := by
    nlinarith [h, hEpos, hRHSpos]
  have hlt : R.s * R.m < 2 * R.s + 2 * R.m := by
    have : (R.s * R.m : ℤ) < 2 * R.s + 2 * R.m := by linarith
    exact_mod_cast this
  -- Expand (s-2)(m-2) via rewriting s, m
  set a := R.s - 2 with ha
  set b := R.m - 2 with hb
  have hs' : R.s = a + 2 := by omega
  have hm' : R.m = b + 2 := by omega
  -- (a+2)(b+2) < 2(a+2)+2(b+2) ⇒ ab + 2a + 2b + 4 < 2a + 4 + 2b + 4 ⇒ ab < 4
  have : (a + 2) * (b + 2) < 2 * (a + 2) + 2 * (b + 2) := by
    simpa [hs', hm'] using hlt
  have : a * b < 4 := by
    have h' : a * b + 2 * a + 2 * b + 4 < 2 * a + 2 * b + 8 := by
      convert this using 1 <;> ring
    omega
  simpa [ha, hb] using this

/-- The five admissible Schläfli pairs. -/
def schlafliPairs : Finset (ℕ × ℕ) :=
  {(3, 3), (3, 4), (3, 5), (4, 3), (5, 3)}

private theorem schlafli_of_bounds {s m : ℕ}
    (hs : 3 ≤ s) (hm : 3 ≤ m) (hlt : (s - 2) * (m - 2) < 4) :
    (s, m) ∈ schlafliPairs := by
  set a := s - 2 with ha
  set b := m - 2 with hb
  have ha1 : 1 ≤ a := by omega
  have hb1 : 1 ≤ b := by omega
  have hprod : a * b < 4 := by simpa [ha, hb] using hlt
  -- a ∈ {1,2,3}: if a ≥ 4 then a*b ≥ 4
  have ha_le : a ≤ 3 := by
    by_contra h
    have : 4 ≤ a := by omega
    have : 4 ≤ a * b :=
      calc
        4 = 4 * 1 := by ring
        _ ≤ a * 1 := Nat.mul_le_mul_right 1 this
        _ ≤ a * b := Nat.mul_le_mul_left a hb1
    omega
  have hb_le : b ≤ 3 := by
    by_contra h
    have : 4 ≤ b := by omega
    have : 4 ≤ a * b :=
      calc
        4 = 1 * 4 := by ring
        _ ≤ 1 * b := Nat.mul_le_mul_left 1 this
        _ ≤ a * b := Nat.mul_le_mul_right b ha1
    omega
  -- Case on a
  interval_cases a
  · -- a = 1 ⇒ s = 3; b ∈ {1,2,3}
    have hs3 : s = 3 := by omega
    interval_cases b
    · have hm3 : m = 3 := by omega
      simp [schlafliPairs, hs3, hm3]
    · have hm4 : m = 4 := by omega
      simp [schlafliPairs, hs3, hm4]
    · have hm5 : m = 5 := by omega
      simp [schlafliPairs, hs3, hm5]
  · -- a = 2 ⇒ s = 4; need b = 1
    have hs4 : s = 4 := by omega
    have hb1' : b = 1 := by omega
    have hm3 : m = 3 := by omega
    simp [schlafliPairs, hs4, hm3]
  · -- a = 3 ⇒ s = 5; need b = 1
    have hs5 : s = 5 := by omega
    have hb1' : b = 1 := by omega
    have hm3 : m = 3 := by omega
    simp [schlafliPairs, hs5, hm3]

/-- **Number of Platonic solids (combinatorial):** any regular Schläfli pair
satisfying Euler + double-counting is one of the five classical pairs. -/
theorem schlafli_pair_mem (R : RegularNumbers) :
    (R.s, R.m) ∈ schlafliPairs :=
  schlafli_of_bounds R.hs R.hm (sub_mul_lt_four R)

/-- There are exactly five admissible Schläfli pairs. -/
theorem card_schlafliPairs : schlafliPairs.card = 5 := by
  native_decide

/-! ## Combinatorial constructions (Euler bookkeeping for the five) -/

/-- Tetrahedron `{3,3}`: `V=4, E=6, F=4`. -/
def tetrahedron : RegularNumbers where
  V := 4; E := 6; F := 4; s := 3; m := 3
  hs := by decide
  hm := by decide
  hE := by decide
  hFace := by decide
  hVert := by decide
  hEuler := by decide

/-- Octahedron `{3,4}`: `V=6, E=12, F=8`. -/
def octahedron : RegularNumbers where
  V := 6; E := 12; F := 8; s := 3; m := 4
  hs := by decide
  hm := by decide
  hE := by decide
  hFace := by decide
  hVert := by decide
  hEuler := by decide

/-- Icosahedron `{3,5}`: `V=12, E=30, F=20`. -/
def icosahedron : RegularNumbers where
  V := 12; E := 30; F := 20; s := 3; m := 5
  hs := by decide
  hm := by decide
  hE := by decide
  hFace := by decide
  hVert := by decide
  hEuler := by decide

/-- Cube `{4,3}`: `V=8, E=12, F=6`. -/
def cube : RegularNumbers where
  V := 8; E := 12; F := 6; s := 4; m := 3
  hs := by decide
  hm := by decide
  hE := by decide
  hFace := by decide
  hVert := by decide
  hEuler := by decide

/-- Dodecahedron `{5,3}`: `V=20, E=30, F=12`. -/
def dodecahedron : RegularNumbers where
  V := 20; E := 30; F := 12; s := 5; m := 3
  hs := by decide
  hm := by decide
  hE := by decide
  hFace := by decide
  hVert := by decide
  hEuler := by decide

/-- Each of the five classical Schläfli pairs is realized by a combinatorial type. -/
theorem exists_regularNumbers_of_mem_schlafli
    {s m : ℕ} (h : (s, m) ∈ schlafliPairs) :
    ∃ R : RegularNumbers, R.s = s ∧ R.m = m := by
  simp [schlafliPairs, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨tetrahedron, rfl, rfl⟩
  · exact ⟨octahedron, rfl, rfl⟩
  · exact ⟨icosahedron, rfl, rfl⟩
  · exact ⟨cube, rfl, rfl⟩
  · exact ⟨dodecahedron, rfl, rfl⟩

/-- The five constructions realize the five distinct Schläfli pairs. -/
theorem five_schlafli_pairs :
    (tetrahedron.s, tetrahedron.m) = (3, 3) ∧
    (octahedron.s, octahedron.m) = (3, 4) ∧
    (icosahedron.s, icosahedron.m) = (3, 5) ∧
    (cube.s, cube.m) = (4, 3) ∧
    (dodecahedron.s, dodecahedron.m) = (5, 3) := by
  decide

/-- Summary: exactly five combinatorial types, each realized. -/
theorem exactly_five_platonic_schlafli :
    schlafliPairs.card = 5 ∧
      ∀ p ∈ schlafliPairs, ∃ R : RegularNumbers, (R.s, R.m) = p := by
  refine ⟨card_schlafliPairs, ?_⟩
  intro p hp
  obtain ⟨s, m⟩ := p
  obtain ⟨R, hs, hm⟩ := exists_regularNumbers_of_mem_schlafli hp
  exact ⟨R, by rw [hs, hm]⟩

end Platonic
end EulersGem
