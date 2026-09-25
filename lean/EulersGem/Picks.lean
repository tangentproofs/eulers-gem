/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import Mathlib.Tactic
import Mathlib.Data.Rat.Defs

/-!
# Funkenbusch / triangulation count identities (not classical Pick)

Following Isabelle `Poly100.thy` (algebraic `pick's_theorem` shape, Funkenbusch
edge theorem) and W. W. Funkenbusch, *From Euler's Formula to Pick's Formula
Using an Edge Theorem*, Amer. Math. Monthly 81 (1974).

These lemmas are **integer/rational bookkeeping**: from Euler, vertex split
`V = I + B`, and either Funkenbusch's edge count or triangulation handshaking,
together with an area hypothesis `A = (F−1)/2` or `A = T/2`, one obtains the
numeric identity `A = I + B/2 − 1`.

**This is not classical Pick's theorem.** Classical Pick requires a lattice
polygon, a geometric area (Lebesgue/Haar or shoelace proved equal to measure),
geometric interior/boundary lattice counts, and a triangulation (or equivalent).
Those gaps are documented in `PHASE_B_PLAN.md` / `PICKS_CLAUDE_AUDIT.md`.

Identifiers deliberately avoid `picks_*` so Results/README cannot be skimmed as
claiming Pick.
-/

namespace EulersGem
namespace Picks

/-- **Funkenbusch count identity** (Poly100 algebraic shape; not geometric Pick).

Given Euler, `V = I + B`, Funkenbusch `E = 3I + 2B − 3`, and
`A = (F − 1)/2`, conclude `A = I + B/2 − 1`. -/
theorem funkenbusch_identity
    (I B V E F : ℤ) (A : ℚ)
    (heuler : V - E + F = 2)
    (hverts : V = I + B)
    (hedges : E = 3 * I + 2 * B - 3)
    (harea : A = ((F : ℚ) - 1) / 2) :
    A = (I : ℚ) + (B : ℚ) / 2 - 1 := by
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

/-- From triangulation handshaking `2 E = 3 T + B` + Euler + `V = I + B` and
`F = T + 1` (one unbounded outer face), derive Funkenbusch's edge count.

The handshaking hypothesis is an assumption here. It is **proved** for
`CombinatorialDiskTriangulation` in `PlanarTriangulation.lean`
(`two_E_eq_three_T_add_B`); pass that theorem when a combinatorial disk
triangulation is available. -/
theorem funkenbusch_of_triangulation
    (I B V E T F : ℤ)
    (hV : V = I + B)
    (hF : F = T + 1)
    (heuler : V - E + F = 2)
    (hshake : 2 * E = 3 * T + B) :
    E = 3 * I + 2 * B - 3 := by
  have h1 : V - E + T = 1 := by omega
  have hT : 3 * T = 2 * E - B := by omega
  have h2 : I + B - E + T = 1 := by
    rw [hV] at h1; exact h1
  have h3 : 3 * I + 3 * B - 3 * E + 3 * T = 3 := by linear_combination 3 * h2
  have h4 : 3 * I + 3 * B - 3 * E + (2 * E - B) = 3 := by
    rw [← hT]; exact h3
  omega

/-- **Triangulation count identity** (not geometric Pick).

Assumes `2E = 3T + B`, Euler, `V = I + B`, `F = T + 1`, and `A = T/2`.
Concludes `A = I + B/2 − 1`. Does not construct a triangulation or prove area. -/
theorem triangulation_count_identity
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
  exact funkenbusch_identity I B V E F A heuler hV hedges harea'

/-- Same identity with nonnegative `ℕ` counts cast to `ℚ`. -/
theorem triangulation_count_identity_nat
    (I B V E T F : ℕ) (A : ℚ)
    (hV : V = I + B)
    (hF : F = T + 1)
    (heuler : (V : ℤ) - E + F = 2)
    (hshake : 2 * E = 3 * T + B)
    (harea : A = (T : ℚ) / 2) :
    A = (I : ℚ) + (B : ℚ) / 2 - 1 := by
  exact triangulation_count_identity I B V E T F A
    (by exact_mod_cast hV) (by exact_mod_cast hF) heuler
    (by exact_mod_cast hshake) harea

end Picks
end EulersGem
