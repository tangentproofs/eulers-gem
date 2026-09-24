/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import Mathlib.Tactic
import Mathlib.Data.Rat.Defs

/-!
# Pick's theorem — Euler → Pick (Funkenbusch / triangulation bookkeeping)

Following Isabelle `Poly100.thy` (`pick's_theorem`, Funkenbusch edge theorem)
and W. W. Funkenbusch, *From Euler's Formula to Pick's Formula Using an Edge
Theorem*, Amer. Math. Monthly 81 (1974).

For a simple lattice polygon triangulated into primitive lattice triangles:

* `V = I + B` (all lattice points become vertices),
* `E = 3 I + 2 B − 3` (Funkenbusch edge count),
* `A = (F − 1) / 2` (each of the `F−1` triangles has area `1/2`),
* `V − E + F = 2` (planar Euler),

and these imply Pick's formula `A = I + B/2 − 1`.

We prove:

1. The algebraic implication (Poly100 `pick's_theorem`) over `ℚ`.
2. The standard triangulation handshaking `2 E = 3 T + B` with `T = F − 1`,
   together with Euler and `V = I + B`, yields Funkenbusch's edge count and
   hence Pick when `A = T/2`.

**Still open (geometric):** existence of a lattice triangulation into primitive
triangles, and the area of a primitive lattice triangle `= 1/2`. Mathlib has
neither lattice-polygon interiors nor a ready Pick API (2026-09 survey).
-/

namespace EulersGem
namespace Picks

/-- **Pick from Funkenbusch hypotheses** (Poly100 `pick's_theorem`).

Given Euler, `V = I + B`, Funkenbusch `E = 3I + 2B − 3`, and area
`A = (F − 1)/2`, conclude `A = I + B/2 − 1`. -/
theorem picks_of_funkenbusch
    (I B V E F : ℤ) (A : ℚ)
    (heuler : V - E + F = 2)
    (hverts : V = I + B)
    (hedges : E = 3 * I + 2 * B - 3)
    (harea : A = ((F : ℚ) - 1) / 2) :
    A = (I : ℚ) + (B : ℚ) / 2 - 1 := by
  -- From Euler + verts + edges: solve for F
  have hF : F = 2 * I + B - 1 := by
    have : (I + B : ℤ) - E + F = 2 := by rw [← hverts]; exact heuler
    rw [hedges] at this
    omega
  have hF' : (F : ℚ) = 2 * (I : ℚ) + (B : ℚ) - 1 := by exact_mod_cast hF
  calc
    A = ((F : ℚ) - 1) / 2 := harea
    _ = ((2 * (I : ℚ) + (B : ℚ) - 1) - 1) / 2 := by rw [hF']
    _ = (2 * (I : ℚ) + (B : ℚ) - 2) / 2 := by ring
    _ = (I : ℚ) + (B : ℚ) / 2 - 1 := by ring

/-- Triangulation handshaking: `T` triangular faces, `B` boundary edges
(= boundary vertices for a simple polygonal boundary), each triangle has 3
edges, each interior edge shared by 2 triangles, each boundary edge once ⇒
`2 E = 3 T + B`. -/
theorem edges_of_triangulation (E T B : ℕ) (h : 2 * E = 3 * T + B) :
    2 * E = 3 * T + B := h

/-- From triangulation handshaking + Euler + `V = I + B` and `F = T + 1`
(one unbounded outer face), derive Funkenbusch's edge count. -/
theorem funkenbusch_of_triangulation
    (I B V E T F : ℤ)
    (hV : V = I + B)
    (hF : F = T + 1)
    (heuler : V - E + F = 2)
    (hshake : 2 * E = 3 * T + B) :
    E = 3 * I + 2 * B - 3 := by
  -- V - E + T = 1 and 3T = 2E - B
  have h1 : V - E + T = 1 := by omega
  have hT : 3 * T = 2 * E - B := by omega
  have h2 : I + B - E + T = 1 := by
    rw [hV] at h1; exact h1
  -- 3(I + B - E + T) = 3
  have h3 : 3 * I + 3 * B - 3 * E + 3 * T = 3 := by linear_combination 3 * h2
  -- Substitute 3T
  have h4 : 3 * I + 3 * B - 3 * E + (2 * E - B) = 3 := by
    rw [← hT]; exact h3
  omega

/-- **Pick from triangulation hypotheses.**

`A = T/2` (sum of primitive triangle areas), `2E = 3T + B`, Euler,
`V = I + B`, `F = T + 1` ⇒ Pick's formula. -/
theorem picks_of_triangulation
    (I B V E T F : ℤ) (A : ℚ)
    (hV : V = I + B)
    (hF : F = T + 1)
    (heuler : V - E + F = 2)
    (hshake : 2 * E = 3 * T + B)
    (harea : A = (T : ℚ) / 2) :
    A = (I : ℚ) + (B : ℚ) / 2 - 1 := by
  have hedges : E = 3 * I + 2 * B - 3 :=
    funkenbusch_of_triangulation I B V E T F hV hF heuler hshake
  have harea' : A = ((F : ℚ) - 1) / 2 := by
    have hFT : F - 1 = T := by omega
    have hFT' : (F : ℚ) - 1 = (T : ℚ) := by exact_mod_cast hFT
    rw [harea, ← hFT']
  exact picks_of_funkenbusch I B V E F A heuler hV hedges harea'

/-- Convenience: Pick's formula in the classical `I + B/2 − 1` shape with
nonnegative counts packaged as naturals (cast to `ℚ`). -/
theorem picks_formula_nat
    (I B V E T F : ℕ) (A : ℚ)
    (hV : V = I + B)
    (hF : F = T + 1)
    (heuler : (V : ℤ) - E + F = 2)
    (hshake : 2 * E = 3 * T + B)
    (harea : A = (T : ℚ) / 2) :
    A = (I : ℚ) + (B : ℚ) / 2 - 1 := by
  exact picks_of_triangulation I B V E T F A
    (by exact_mod_cast hV) (by exact_mod_cast hF) heuler
    (by exact_mod_cast hshake) harea

end Picks
end EulersGem
