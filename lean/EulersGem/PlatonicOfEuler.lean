/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import EulersGem.Embed
import EulersGem.Platonic
import EulersGem.PolytopeFaces
import EulersGem.EdgeVertices
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Platonic on the Euler–Poincaré spine (`PlatonicOfEuler`)

`Platonic.lean` classifies Schläfli pairs from a **hypothesis** `hEuler : V − E + F = 2`.
This module removes that hypothesis: for a geometric convex 3-polytope, Euler is
*discharged* from the Euler–Poincaré root
`EulersGem.euler_relation_convex_3polytope` (itself `Euler_Poincare_full`), and the
double-counting identities `s·F = 2·E`, `m·V = 2·E` are *proved* from face-lattice
incidence rather than assumed.

## Spine

```
Euler_Poincare_full  (Embed.lean, geometric, H+V-rep convex polytope)
  └─► euler_relation_convex_3polytope      V − E + F = 2   (geometric)
        └─► regular_polytope_counts     (this file; + incidence double counting)
              └─► schlafli_pair_mem_of_regular_polytope   (s,m) ∈ five pairs
```

## What is still hypothesis (honesty)

The *regularity* input is stated as face-lattice incidence counts:

* `hface_edges` — every 2-face has exactly `s` edges (it is an `s`-gon);
* `hvert_edges` — exactly `m` edges meet at every vertex.

One further incidence hypothesis is a *polytope fact* rather than regularity, and is assumed
here rather than derived from the polytope structure:

* `hedge_faces` — every edge lies in exactly two 2-faces (the diamond property).

It is not Euler: no bare `V − E + F = 2` hypothesis appears anywhere below.

*Derived*, not assumed:

* every edge has exactly two vertices — `ncard_vertices_of_edge` (`EdgeVertices.lean`:
  a 1-dimensional face is a segment, whose only 0-faces are its two endpoints);
* finiteness of the face set in each dimension — `facesOfDim_finite_of_isPolytope`
  (`PolytopeFaces.lean`: a face of a V-polytope is the hull of the generators it
  contains, so `F ↦ V ∩ F` is injective on faces);
* `0 < E` — from `s, m ≥ 3` + double counting + Euler (`pos_edges_of_euler`).

Geometrically regular embeddings of the five solids in `ℝ³` are still open; this file
does not claim them. See `UNIFIED_SPINE.md`.
-/

open scoped RealInnerProductSpace
open Classical Set Finset

namespace EulersGem
namespace Platonic

/-! ## Double counting for `Set.ncard` -/

/-- **Double counting** in `Set.ncard` form: if every `a ∈ A` is related to exactly `m`
elements of `B`, and every `b ∈ B` to exactly `n` elements of `A`, then
`|A| · m = |B| · n`. Mathlib's `Finset.card_mul_eq_card_mul` transported to `Set.ncard`. -/
theorem ncard_mul_eq_ncard_mul {α β : Type*} {A : Set α} {B : Set β}
    (r : α → β → Prop) (hA : A.Finite) (hB : B.Finite) {m n : ℕ}
    (hm : ∀ a ∈ A, {b ∈ B | r a b}.ncard = m)
    (hn : ∀ b ∈ B, {a ∈ A | r a b}.ncard = n) :
    A.ncard * m = B.ncard * n := by
  classical
  rw [Set.ncard_eq_toFinset_card A hA, Set.ncard_eq_toFinset_card B hB]
  refine Finset.card_mul_eq_card_mul r ?_ ?_
  · intro a ha
    have ha' : a ∈ A := hA.mem_toFinset.mp ha
    have hfin : ({b ∈ B | r a b} : Set β).Finite := hB.subset fun b hb => hb.1
    have hEq : hfin.toFinset = hB.toFinset.bipartiteAbove r a := by
      ext b
      simp [Finset.mem_bipartiteAbove]
    have h := hm a ha'
    rwa [Set.ncard_eq_toFinset_card _ hfin, hEq] at h
  · intro b hb
    have hb' : b ∈ B := hB.mem_toFinset.mp hb
    have hfin : ({a ∈ A | r a b} : Set α).Finite := hA.subset fun a ha => ha.1
    have hEq : hfin.toFinset = hA.toFinset.bipartiteBelow r b := by
      ext a
      simp [Finset.mem_bipartiteBelow]
    have h := hn b hb'
    rwa [Set.ncard_eq_toFinset_card _ hfin, hEq] at h

/-! ## `0 < E` is derived, not assumed -/

/-- With `s, m ≥ 3`, double counting plus Euler forces at least one edge.
This lets `RegularNumbers.hE` be discharged instead of assumed. -/
theorem pos_edges_of_euler {V E F s m : ℕ} (hs : 3 ≤ s) (hm : 3 ≤ m)
    (hFace : s * F = 2 * E) (hVert : m * V = 2 * E)
    (hEuler : (V : ℤ) - E + F = 2) :
    0 < E := by
  rcases Nat.eq_zero_or_pos E with hE0 | hEpos
  · subst hE0
    have hF : F = 0 := by
      have : s * F = 0 := by simpa using hFace
      rcases Nat.mul_eq_zero.mp this with h | h
      · omega
      · exact h
    have hV : V = 0 := by
      have : m * V = 0 := by simpa using hVert
      rcases Nat.mul_eq_zero.mp this with h | h
      · omega
      · exact h
    rw [hF, hV] at hEuler
    norm_num at hEuler
  · exact hEpos

/-! ## Faces of a given affine dimension -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The set of faces of `p` of affine dimension `d`. Definitionally the set-builder
used by `euler_relation_convex_3polytope`. -/
def facesOfDim (p : Set E) (d : ℤ) : Set (Set E) :=
  {f : Set E | IsFaceOf p f ∧ affDim f = d}

lemma mem_facesOfDim {p f : Set E} {d : ℤ} :
    f ∈ facesOfDim p d ↔ IsFaceOf p f ∧ affDim f = d := Iff.rfl

/-! ## Geometric regularity ⇒ Platonic counts, Euler from EP -/

section Regular

variable [FiniteDimensional ℝ E] [Nonempty E]

/-- **The three Platonic count equations for a geometric regular convex 3-polytope.**

`s·F = 2·E` and `m·V = 2·E` are *proved* by double counting over face-lattice
incidence (`ncard_mul_eq_ncard_mul`); `V − E + F = 2` is *discharged* from the
Euler–Poincaré root `euler_relation_convex_3polytope`.

No bare `V − E + F = 2` hypothesis is taken. -/
theorem regular_polytope_counts
    {H : Set (Hyperplane E)} {p : Set E} {s m : ℕ}
    (hH : H.Finite)
    (hp : p = ⋂ h ∈ H, closedHalfspace h.1 h.2)
    (hP : IsPolytope p)
    (hdim : affDim p = 3)
    (hEdim : Module.finrank ℝ E = 3)
    (hface_edges : ∀ f ∈ facesOfDim p 2, {e ∈ facesOfDim p 1 | e ⊆ f}.ncard = s)
    (hedge_faces : ∀ e ∈ facesOfDim p 1, {f ∈ facesOfDim p 2 | e ⊆ f}.ncard = 2)
    (hvert_edges : ∀ v ∈ facesOfDim p 0, {e ∈ facesOfDim p 1 | v ⊆ e}.ncard = m) :
    s * (facesOfDim p 2).ncard = 2 * (facesOfDim p 1).ncard ∧
      m * (facesOfDim p 0).ncard = 2 * (facesOfDim p 1).ncard ∧
      ((facesOfDim p 0).ncard : ℤ) - (facesOfDim p 1).ncard
        + (facesOfDim p 2).ncard = 2 := by
  -- finiteness of each face set comes from the V-representation, not a hypothesis
  have hfin0 : (facesOfDim p 0).Finite := facesOfDim_finite_of_isPolytope hP 0
  have hfin1 : (facesOfDim p 1).Finite := facesOfDim_finite_of_isPolytope hP 1
  have hfin2 : (facesOfDim p 2).Finite := facesOfDim_finite_of_isPolytope hP 2
  -- every edge has exactly two vertices: proved, not assumed
  have hedge_verts : ∀ e ∈ facesOfDim p 1, {v ∈ facesOfDim p 0 | v ⊆ e}.ncard = 2 :=
    fun e he => ncard_vertices_of_edge hP he.1 he.2
  refine ⟨?_, ?_, ?_⟩
  · -- every 2-face has `s` edges; every edge lies in `2` faces
    have h := ncard_mul_eq_ncard_mul (fun f e : Set E => e ⊆ f) hfin2 hfin1
      hface_edges hedge_faces
    rw [mul_comm s, mul_comm 2]
    exact h
  · -- `m` edges at every vertex; every edge has `2` vertices
    have h := ncard_mul_eq_ncard_mul (fun v e : Set E => v ⊆ e) hfin0 hfin1
      hvert_edges hedge_verts
    rw [mul_comm m, mul_comm 2]
    exact h
  · -- Euler from the Euler–Poincaré root
    simpa [facesOfDim] using euler_relation_convex_3polytope hH hp hP hdim hEdim

/-- **Schläfli classification of geometric regular convex 3-polytopes.**

If a full-dimensional convex 3-polytope in a 3-dimensional inner product space has
every 2-face an `s`-gon and exactly `m` edges at every vertex (`s, m ≥ 3`), then
`(s, m)` is one of the five classical pairs `{(3,3),(3,4),(3,5),(4,3),(5,3)}`.

Euler's relation is **not** assumed: it comes from `euler_relation_convex_3polytope`,
i.e. from `Euler_Poincare_full`. `0 < E` is derived, not assumed. -/
theorem schlafli_pair_mem_of_regular_polytope
    {H : Set (Hyperplane E)} {p : Set E} {s m : ℕ}
    (hH : H.Finite)
    (hp : p = ⋂ h ∈ H, closedHalfspace h.1 h.2)
    (hP : IsPolytope p)
    (hdim : affDim p = 3)
    (hEdim : Module.finrank ℝ E = 3)
    (hs : 3 ≤ s) (hm : 3 ≤ m)
    (hface_edges : ∀ f ∈ facesOfDim p 2, {e ∈ facesOfDim p 1 | e ⊆ f}.ncard = s)
    (hedge_faces : ∀ e ∈ facesOfDim p 1, {f ∈ facesOfDim p 2 | e ⊆ f}.ncard = 2)
    (hvert_edges : ∀ v ∈ facesOfDim p 0, {e ∈ facesOfDim p 1 | v ⊆ e}.ncard = m) :
    (s, m) ∈ schlafliPairs := by
  obtain ⟨hFace, hVert, hEuler⟩ :=
    regular_polytope_counts hH hp hP hdim hEdim
      hface_edges hedge_faces hvert_edges
  exact schlafli_pair_mem
    { V := (facesOfDim p 0).ncard
      E := (facesOfDim p 1).ncard
      F := (facesOfDim p 2).ncard
      s := s, m := m
      hs := hs
      hm := hm
      hE := pos_edges_of_euler hs hm hFace hVert hEuler
      hFace := hFace
      hVert := hVert
      hEuler := hEuler }

end Regular

end Platonic
end EulersGem
