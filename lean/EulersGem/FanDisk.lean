/-
Copyright (c) 2026 Michal Wallace / tangentproofs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Wallace, Grok Bot
-/
import Mathlib.Tactic
import EulersGem.PlanarTriangulation

/-!
# Fan disk triangulation — general `n ≥ 3`

Constructive combinatorial triangulation of an abstract n-gon by fanning from
vertex `0`. Incidence is proved for **general** `n ≥ 3` (Nat-indexed edges /
faces — no `native_decide` Fin-bound). Planar Euler via empty-interior disk
counts. **Not** geometric embedding / classical Pick.
-/

open Finset

namespace EulersGem
namespace Picks
namespace FanDiskTriangulation

/-- Vertex `k` as an element of `Fin n`. -/
private def v (n : ℕ) (k : ℕ) (hk : k < n) : Fin n := ⟨k, hk⟩

private lemma v_eq_iff (n : ℕ) {k₁ k₂ : ℕ} (h₁ : k₁ < n) (h₂ : k₂ < n) :
    v n k₁ h₁ = v n k₂ h₂ ↔ k₁ = k₂ := by
  simp [v, Fin.ext_iff]

private lemma v_eq (n : ℕ) {k₁ k₂ : ℕ} {h₁ : k₁ < n} {h₂ : k₂ < n}
    (h : v n k₁ h₁ = v n k₂ h₂) : k₁ = k₂ :=
  (v_eq_iff n h₁ h₂).mp h

private lemma v_ne (n : ℕ) {k₁ k₂ : ℕ} (h₁ : k₁ < n) (h₂ : k₂ < n) (hne : k₁ ≠ k₂) :
    v n k₁ h₁ ≠ v n k₂ h₂ := fun h => hne (v_eq n h)

/-- Boundary edge `{k, k+1}` with `k+1 < n` (no wrap). -/
private def bEdge (n : ℕ) (k : ℕ) (hk : k + 1 < n) : Finset (Fin n) :=
  {v n k (by omega), v n (k + 1) (by omega)}

/-- Closing boundary edge `{n-1, 0}`. -/
private def bEdgeClose (n : ℕ) (hn : 3 ≤ n) : Finset (Fin n) :=
  {v n (n - 1) (by omega), v n 0 (by omega)}

/-- Boundary cycle: consecutive Nat pairs plus the closing edge. -/
def fanBoundary (n : ℕ) (hn : 3 ≤ n) : Finset (Finset (Fin n)) :=
  (Finset.range (n - 1)).attach.image (fun k =>
    bEdge n k.1 (by have := Finset.mem_range.mp k.2; omega)) ∪
    {bEdgeClose n hn}

/-- Fan triangle `{0, i+1, i+2}` for `i < n-2`. -/
def fanTriangle (n : ℕ) (i : ℕ) (hi : i < n - 2) : Finset (Fin n) :=
  {v n 0 (by omega), v n (i + 1) (by omega), v n (i + 2) (by omega)}

def fanTriangles (n : ℕ) (_hn : 3 ≤ n) : Finset (Finset (Fin n)) :=
  (Finset.range (n - 2)).attach.image fun i =>
    fanTriangle n i.1 (Finset.mem_range.mp i.2)

/-- Fan diagonal `{0, i+2}` for `i < n-3`. -/
def fanDiagonal (n : ℕ) (i : ℕ) (hi : i < n - 3) : Finset (Fin n) :=
  {v n 0 (by omega), v n (i + 2) (by omega)}

def fanDiagonals (n : ℕ) (_hn : 3 ≤ n) : Finset (Finset (Fin n)) :=
  (Finset.range (n - 3)).attach.image fun i =>
    fanDiagonal n i.1 (Finset.mem_range.mp i.2)

def fanEdges (n : ℕ) (hn : 3 ≤ n) : Finset (Finset (Fin n)) :=
  fanBoundary n hn ∪ fanDiagonals n hn

private lemma bEdge_card (n k : ℕ) (hk : k + 1 < n) : (bEdge n k hk).card = 2 := by
  dsimp [bEdge]
  have h := v_ne n (by omega : k < n) (by omega : k + 1 < n) (by omega)
  rw [card_insert_of_notMem (by simp [h]), card_singleton]

private lemma bEdgeClose_card (n : ℕ) (hn : 3 ≤ n) : (bEdgeClose n hn).card = 2 := by
  dsimp [bEdgeClose]
  have h := v_ne n (by omega : n - 1 < n) (by omega : 0 < n) (by omega)
  rw [card_insert_of_notMem (by simp [h]), card_singleton]

private lemma fanTriangle_card (n i : ℕ) (hi : i < n - 2) :
    (fanTriangle n i hi).card = 3 := by
  dsimp [fanTriangle]
  have h01 := v_ne n (by omega : 0 < n) (by omega : i + 1 < n) (by omega)
  have h02 := v_ne n (by omega : 0 < n) (by omega : i + 2 < n) (by omega)
  have h12 := v_ne n (by omega : i + 1 < n) (by omega : i + 2 < n) (by omega)
  rw [card_insert_of_notMem (by simp [h01, h02]),
    card_insert_of_notMem (by simp [h12]), card_singleton]

private lemma fanDiagonal_card (n i : ℕ) (hi : i < n - 3) :
    (fanDiagonal n i hi).card = 2 := by
  dsimp [fanDiagonal]
  have h := v_ne n (by omega : 0 < n) (by omega : i + 2 < n) (by omega)
  rw [card_insert_of_notMem (by simp [h]), card_singleton]

private lemma mem_fanTriangles (n : ℕ) (hn : 3 ≤ n) {t : Finset (Fin n)} :
    t ∈ fanTriangles n hn ↔ ∃ (i : ℕ) (hi : i < n - 2), t = fanTriangle n i hi := by
  constructor
  · intro ht
    rcases mem_image.mp ht with ⟨⟨i, hi⟩, _, rfl⟩
    exact ⟨i, mem_range.mp hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact mem_image.mpr ⟨⟨i, mem_range.mpr hi⟩, by simp⟩

private lemma mem_fanDiagonals (n : ℕ) (hn : 3 ≤ n) {e : Finset (Fin n)} :
    e ∈ fanDiagonals n hn ↔ ∃ (i : ℕ) (hi : i < n - 3), e = fanDiagonal n i hi := by
  constructor
  · intro he
    rcases mem_image.mp he with ⟨⟨i, hi⟩, _, rfl⟩
    exact ⟨i, mem_range.mp hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact mem_image.mpr ⟨⟨i, mem_range.mpr hi⟩, by simp⟩

private lemma mem_fanBoundary (n : ℕ) (hn : 3 ≤ n) {e : Finset (Fin n)} :
    e ∈ fanBoundary n hn ↔
      (∃ (k : ℕ) (hk : k + 1 < n), e = bEdge n k hk) ∨ e = bEdgeClose n hn := by
  simp only [fanBoundary, mem_union, mem_singleton, mem_image, mem_attach, true_and]
  constructor
  · rintro (⟨⟨k, hk⟩, rfl⟩ | h)
    · exact Or.inl ⟨k, by have := mem_range.mp hk; omega, rfl⟩
    · exact Or.inr h
  · rintro (⟨k, hk, rfl⟩ | rfl)
    · exact Or.inl ⟨⟨k, mem_range.mpr (by omega)⟩, rfl⟩
    · exact Or.inr rfl

private lemma eq_of_fanTriangle_eq (n : ℕ) {i j : ℕ}
    (hi : i < n - 2) (hj : j < n - 2)
    (h : fanTriangle n i hi = fanTriangle n j hj) : i = j := by
  have hmem : v n (i + 2) (by omega) ∈ fanTriangle n j hj := by
    have : v n (i + 2) (by omega) ∈ fanTriangle n i hi := by simp [fanTriangle]
    exact h ▸ this
  simp only [fanTriangle, mem_insert, mem_singleton] at hmem
  rcases hmem with h0 | h1 | h2
  · have := v_eq n h0; omega
  · have : j = i + 1 := by have := v_eq n h1; omega
    have hmem2 : v n (j + 2) (by omega) ∈ fanTriangle n i hi := by
      have : v n (j + 2) (by omega) ∈ fanTriangle n j hj := by simp [fanTriangle]
      exact h.symm ▸ this
    simp only [fanTriangle, mem_insert, mem_singleton] at hmem2
    rcases hmem2 with c0 | c1 | c2
    · have := v_eq n c0; omega
    · have := v_eq n c1; omega
    · have := v_eq n c2; omega
  · exact Nat.add_right_cancel (v_eq n h2)

private lemma eq_of_fanDiagonal_eq (n : ℕ) {i j : ℕ}
    (hi : i < n - 3) (hj : j < n - 3)
    (h : fanDiagonal n i hi = fanDiagonal n j hj) : i = j := by
  have hmem : v n (i + 2) (by omega) ∈ fanDiagonal n j hj := by
    have : v n (i + 2) (by omega) ∈ fanDiagonal n i hi := by simp [fanDiagonal]
    exact h ▸ this
  simp only [fanDiagonal, mem_insert, mem_singleton] at hmem
  rcases hmem with h0 | h2
  · have := v_eq n h0; omega
  · exact Nat.add_right_cancel (v_eq n h2)

private lemma eq_of_bEdge_eq (n : ℕ) {k₁ k₂ : ℕ}
    (h₁ : k₁ + 1 < n) (h₂ : k₂ + 1 < n)
    (h : bEdge n k₁ h₁ = bEdge n k₂ h₂) : k₁ = k₂ := by
  have hk1mem : v n k₁ (by omega) ∈ bEdge n k₂ h₂ := by
    have : v n k₁ (by omega) ∈ bEdge n k₁ h₁ := by simp [bEdge]
    exact h ▸ this
  simp only [bEdge, mem_insert, mem_singleton] at hk1mem
  rcases hk1mem with h' | h'
  · exact v_eq n h'
  · have : v n (k₁ + 1) (by omega) ∈ bEdge n k₂ h₂ := by
      have : v n (k₁ + 1) (by omega) ∈ bEdge n k₁ h₁ := by simp [bEdge]
      exact h ▸ this
    simp only [bEdge, mem_insert, mem_singleton] at this
    rcases this with c | c
    · have h1 := v_eq n h'; have h2 := v_eq n c; omega
    · have h1 := v_eq n h'; have h2 := v_eq n c; omega

private lemma bEdge_ne_close (n : ℕ) (hn : 3 ≤ n) (k : ℕ) (hk : k + 1 < n) :
    bEdge n k hk ≠ bEdgeClose n hn := by
  intro h
  have h0 : v n 0 (by omega) ∈ bEdge n k hk := by
    have : v n 0 (by omega) ∈ bEdgeClose n hn := by simp [bEdgeClose]
    exact h.symm ▸ this
  simp only [bEdge, mem_insert, mem_singleton] at h0
  rcases h0 with h0 | h0
  · have hk0 : k = 0 := v_eq n h0.symm
    have hn1 : v n (n - 1) (by omega) ∈ bEdge n k hk := by
      have : v n (n - 1) (by omega) ∈ bEdgeClose n hn := by simp [bEdgeClose]
      exact h.symm ▸ this
    simp only [bEdge, mem_insert, mem_singleton] at hn1
    rcases hn1 with c | c
    · have := v_eq n c; omega
    · have := v_eq n c; omega
  · have := v_eq n h0; omega

private lemma not_mem_boundary_of_diagonal (n : ℕ) (hn : 3 ≤ n)
    {e : Finset (Fin n)} (he : e ∈ fanDiagonals n hn) :
    e ∉ fanBoundary n hn := by
  intro hb
  obtain ⟨i, hi, rfl⟩ := (mem_fanDiagonals n hn).mp he
  rcases (mem_fanBoundary n hn).mp hb with ⟨k, hk, heq⟩ | heq
  · have h0 : v n 0 (by omega) ∈ bEdge n k hk := by
      have : v n 0 (by omega) ∈ fanDiagonal n i hi := by simp [fanDiagonal]
      exact heq ▸ this
    simp only [bEdge, mem_insert, mem_singleton] at h0
    rcases h0 with h0 | h0
    · have hk0 : k = 0 := v_eq n h0.symm
      have hi2 : v n (i + 2) (by omega) ∈ bEdge n k hk := by
        have : v n (i + 2) (by omega) ∈ fanDiagonal n i hi := by simp [fanDiagonal]
        exact heq ▸ this
      simp only [bEdge, mem_insert, mem_singleton] at hi2
      rcases hi2 with c | c
      · have := v_eq n c; omega
      · have := v_eq n c; omega
    · have := v_eq n h0; omega
  · have hi2 : v n (i + 2) (by omega) ∈ bEdgeClose n hn := by
      have : v n (i + 2) (by omega) ∈ fanDiagonal n i hi := by simp [fanDiagonal]
      exact heq ▸ this
    simp only [bEdgeClose, mem_insert, mem_singleton] at hi2
    rcases hi2 with c | c
    · have := v_eq n c; omega
    · have := v_eq n c; omega

private lemma disjoint_boundary_diagonals (n : ℕ) (hn : 3 ≤ n) :
    Disjoint (fanBoundary n hn) (fanDiagonals n hn) :=
  disjoint_left.mpr fun _ heB heD => (not_mem_boundary_of_diagonal n hn heD) heB

private lemma mem_powersetCard_two_triple {α : Type*} [DecidableEq α]
    {a b c : α} {e : Finset α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (he : e ∈ ({a, b, c} : Finset α).powersetCard 2) :
    e = {a, b} ∨ e = {a, c} ∨ e = {b, c} := by
  obtain ⟨hsu, hcard⟩ := mem_powersetCard.mp he
  by_cases ha : a ∈ e
  · by_cases hb : b ∈ e
    · have hc : c ∉ e := by
        intro hc
        have hsub : ({a, b, c} : Finset α) ⊆ e := by
          intro x hx; simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl | rfl <;> assumption
        have h3 : ({a, b, c} : Finset α).card = 3 := by
          rw [card_insert_of_notMem (by simp [hab, hac]),
            card_insert_of_notMem (by simp [hbc]), card_singleton]
        have : 3 ≤ e.card := h3 ▸ card_le_card hsub
        omega
      refine Or.inl (Subset.antisymm ?_ ?_)
      · intro x hx
        have := hsu hx
        simp only [mem_insert, mem_singleton] at this ⊢
        rcases this with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact (hc hx).elim
      · intro x hx; simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
    · have hc : c ∈ e := by
        by_contra hc
        have hsub : e ⊆ {a} := by
          intro x hx
          have := hsu hx
          simp only [mem_insert, mem_singleton] at this ⊢
          rcases this with rfl | rfl | rfl
          · rfl
          · exact (hb hx).elim
          · exact (hc hx).elim
        have : e.card ≤ 1 := (card_le_card hsub).trans_eq (card_singleton _)
        omega
      refine Or.inr (Or.inl (Subset.antisymm ?_ ?_))
      · intro x hx
        have := hsu hx
        simp only [mem_insert, mem_singleton] at this ⊢
        rcases this with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact (hb hx).elim
        · exact Or.inr rfl
      · intro x hx; simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
  · have hb : b ∈ e := by
      by_contra hb
      by_cases hc : c ∈ e
      · have hsub : e ⊆ {c} := by
          intro x hx
          have := hsu hx
          simp only [mem_insert, mem_singleton] at this ⊢
          rcases this with rfl | rfl | rfl
          · exact (ha hx).elim
          · exact (hb hx).elim
          · rfl
        have : e.card ≤ 1 := (card_le_card hsub).trans_eq (card_singleton _)
        omega
      · have : e = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx => by
          have := hsu hx
          simp only [mem_insert, mem_singleton] at this
          rcases this with rfl | rfl | rfl <;> contradiction
        simp [this] at hcard
    have hc : c ∈ e := by
      by_contra hc
      have hsub : e ⊆ {b} := by
        intro x hx
        have := hsu hx
        simp only [mem_insert, mem_singleton] at this ⊢
        rcases this with rfl | rfl | rfl
        · exact (ha hx).elim
        · rfl
        · exact (hc hx).elim
      have : e.card ≤ 1 := (card_le_card hsub).trans_eq (card_singleton _)
      omega
    refine Or.inr (Or.inr (Subset.antisymm ?_ ?_))
    · intro x hx
      have := hsu hx
      simp only [mem_insert, mem_singleton] at this ⊢
      rcases this with rfl | rfl | rfl
      · exact (ha hx).elim
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro x hx; simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption

private lemma triangle_card_fan (n : ℕ) (hn : 3 ≤ n) :
    ∀ t ∈ fanTriangles n hn, t.card = 3 := by
  intro t ht
  obtain ⟨i, hi, rfl⟩ := (mem_fanTriangles n hn).mp ht
  exact fanTriangle_card n i hi

private lemma edge_card_fan (n : ℕ) (hn : 3 ≤ n) :
    ∀ e ∈ fanEdges n hn, e.card = 2 := by
  intro e he
  rcases mem_union.mp he with he | he
  · rcases (mem_fanBoundary n hn).mp he with ⟨k, hk, rfl⟩ | rfl
    · exact bEdge_card n k hk
    · exact bEdgeClose_card n hn
  · obtain ⟨i, hi, rfl⟩ := (mem_fanDiagonals n hn).mp he
    exact fanDiagonal_card n i hi

private lemma boundary_subset_fan (n : ℕ) (hn : 3 ≤ n) :
    fanBoundary n hn ⊆ fanEdges n hn := subset_union_left

private lemma bEdge_mem_boundary (n : ℕ) (hn : 3 ≤ n) (k : ℕ) (hk : k + 1 < n) :
    bEdge n k hk ∈ fanBoundary n hn :=
  (mem_fanBoundary n hn).mpr (Or.inl ⟨k, hk, rfl⟩)

private lemma bEdgeClose_mem_boundary (n : ℕ) (hn : 3 ≤ n) :
    bEdgeClose n hn ∈ fanBoundary n hn :=
  (mem_fanBoundary n hn).mpr (Or.inr rfl)

private lemma diagonal_mem_edges (n : ℕ) (hn : 3 ≤ n) (i : ℕ) (hi : i < n - 3) :
    fanDiagonal n i hi ∈ fanEdges n hn :=
  mem_union_right _ ((mem_fanDiagonals n hn).mpr ⟨i, hi, rfl⟩)

private lemma boundary_mem_edges (n : ℕ) (hn : 3 ≤ n) {e : Finset (Fin n)}
    (he : e ∈ fanBoundary n hn) : e ∈ fanEdges n hn :=
  mem_union_left _ he

private lemma triangle_edges_mem_fan (n : ℕ) (hn : 3 ≤ n) :
    ∀ t ∈ fanTriangles n hn, t.powersetCard 2 ⊆ fanEdges n hn := by
  intro t ht e he
  obtain ⟨i, hi, rfl⟩ := (mem_fanTriangles n hn).mp ht
  have hab := v_ne n (by omega : 0 < n) (by omega : i + 1 < n) (by omega)
  have hac := v_ne n (by omega : 0 < n) (by omega : i + 2 < n) (by omega)
  have hbc := v_ne n (by omega : i + 1 < n) (by omega : i + 2 < n) (by omega)
  have he' : e ∈ ({v n 0 (by omega), v n (i + 1) (by omega), v n (i + 2) (by omega)} :
      Finset (Fin n)).powersetCard 2 := by simpa [fanTriangle] using he
  rcases mem_powersetCard_two_triple hab hac hbc he' with h01 | h02 | h12
  · rw [h01]
    by_cases hi0 : i = 0
    · subst hi0
      change bEdge n 0 (by omega) ∈ fanEdges n hn
      exact boundary_mem_edges n hn (bEdge_mem_boundary n hn 0 (by omega))
    · have hi' : i - 1 < n - 3 := by omega
      have : ({v n 0 (by omega), v n (i + 1) (by omega)} : Finset (Fin n)) =
          fanDiagonal n (i - 1) hi' := by
        ext x
        simp only [fanDiagonal, mem_insert, mem_singleton]
        constructor
        · intro hx
          rcases hx with hx | hx
          · exact Or.inl hx
          · refine Or.inr ?_
            rw [hx]
            exact Fin.eq_of_val_eq (by simp only [v]; omega)
        · intro hx
          rcases hx with hx | hx
          · exact Or.inl hx
          · refine Or.inr ?_
            rw [hx]
            exact Fin.eq_of_val_eq (by simp only [v]; omega)
      rw [this]; exact diagonal_mem_edges n hn (i - 1) hi'
  · rw [h02]
    by_cases hlast : i + 2 = n - 1
    · have heq : v n (i + 2) (by omega) = v n (n - 1) (by omega) := Fin.eq_of_val_eq hlast
      have : ({v n 0 (by omega), v n (i + 2) (by omega)} : Finset (Fin n)) =
          bEdgeClose n hn := by dsimp [bEdgeClose]; rw [heq, pair_comm]
      rw [this]; exact boundary_mem_edges n hn (bEdgeClose_mem_boundary n hn)
    · have hi' : i < n - 3 := by omega
      change fanDiagonal n i hi' ∈ fanEdges n hn
      exact diagonal_mem_edges n hn i hi'
  · rw [h12]
    change bEdge n (i + 1) (by omega) ∈ fanEdges n hn
    exact boundary_mem_edges n hn (bEdge_mem_boundary n hn (i + 1) (by omega))

private lemma filter_triangles_diagonal (n : ℕ) (hn : 3 ≤ n) (i : ℕ) (hi : i < n - 3) :
    (fanTriangles n hn).filter (fun t => fanDiagonal n i hi ⊆ t) =
      {fanTriangle n i (by omega), fanTriangle n (i + 1) (by omega)} := by
  ext t
  simp only [mem_filter, mem_fanTriangles n hn, mem_insert, mem_singleton]
  constructor
  · rintro ⟨⟨j, hj, rfl⟩, hsub⟩
    have hk : v n (i + 2) (by omega) ∈ fanTriangle n j hj :=
      hsub (by simp [fanDiagonal])
    simp only [fanTriangle, mem_insert, mem_singleton] at hk
    rcases hk with hk0 | hk1 | hk2
    · have := v_eq n hk0; omega
    · have : j = i + 1 := by have := v_eq n hk1; omega
      subst this; exact Or.inr rfl
    · have : j = i := by have := v_eq n hk2; omega
      subst this; exact Or.inl rfl
  · rintro (rfl | rfl)
    · exact ⟨⟨i, by omega, rfl⟩, by
        intro x hx; simp only [fanDiagonal, mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> simp [fanTriangle]⟩
    · exact ⟨⟨i + 1, by omega, rfl⟩, by
        intro x hx; simp only [fanDiagonal, mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> simp [fanTriangle]⟩

private lemma card_filter_diagonal (n : ℕ) (hn : 3 ≤ n) (i : ℕ) (hi : i < n - 3) :
    ((fanTriangles n hn).filter (fun t => fanDiagonal n i hi ⊆ t)).card = 2 := by
  rw [filter_triangles_diagonal]
  have hne : fanTriangle n i (by omega) ≠ fanTriangle n (i + 1) (by omega) :=
    fun h => by have := eq_of_fanTriangle_eq n (by omega) (by omega) h; omega
  rw [card_insert_of_notMem (by simp [hne]), card_singleton]

private lemma filter_triangles_bEdge (n : ℕ) (hn : 3 ≤ n) (k : ℕ) (hk : k + 1 < n)
    (hkpos : 0 < k) :
    (fanTriangles n hn).filter (fun t => bEdge n k hk ⊆ t) =
      {fanTriangle n (k - 1) (by omega)} := by
  ext t
  simp only [mem_filter, mem_fanTriangles n hn, mem_singleton]
  constructor
  · rintro ⟨⟨j, hj, rfl⟩, hsub⟩
    have hk_mem : v n k (by omega) ∈ fanTriangle n j hj := hsub (by simp [bEdge])
    have hk1_mem : v n (k + 1) (by omega) ∈ fanTriangle n j hj := hsub (by simp [bEdge])
    simp only [fanTriangle, mem_insert, mem_singleton] at hk_mem
    rcases hk_mem with c0 | c1 | c2
    · have := v_eq n c0; omega
    · have : j = k - 1 := by have := v_eq n c1; omega
      subst this; rfl
    · simp only [fanTriangle, mem_insert, mem_singleton] at hk1_mem
      rcases hk1_mem with d0 | d1 | d2
      · have h1 := v_eq n d0; have h2 := v_eq n c2; omega
      · have h1 := v_eq n d1; have h2 := v_eq n c2; omega
      · have h1 := v_eq n d2; have h2 := v_eq n c2; omega
  · rintro rfl
    refine ⟨⟨k - 1, by omega, rfl⟩, ?_⟩
    intro x hx
    simp only [bEdge, mem_insert, mem_singleton] at hx
    have hxk := hx
    -- x is v k or v (k+1); triangle is {0, k, k+1}
    rcases hx with hx | hx
    · -- x = v k = v ((k-1)+1)
      have hx' : x = v n ((k - 1) + 1) (by omega) := by
        apply Fin.eq_of_val_eq
        have hv := congrArg Fin.val hx
        simp only [v] at hv ⊢
        omega
      simp [fanTriangle, hx']
    · have hx' : x = v n ((k - 1) + 2) (by omega) := by
        apply Fin.eq_of_val_eq
        have hv := congrArg Fin.val hx
        simp only [v] at hv ⊢
        omega
      simp [fanTriangle, hx']

private lemma filter_triangles_bEdge_zero (n : ℕ) (hn : 3 ≤ n)
    (hk : (0 : ℕ) + 1 < n) :
    (fanTriangles n hn).filter (fun t => bEdge n 0 hk ⊆ t) =
      {fanTriangle n 0 (by omega)} := by
  ext t
  simp only [mem_filter, mem_fanTriangles n hn, mem_singleton]
  constructor
  · rintro ⟨⟨j, hj, rfl⟩, hsub⟩
    have h1 : v n 1 (by omega) ∈ fanTriangle n j hj := hsub (by simp [bEdge])
    simp only [fanTriangle, mem_insert, mem_singleton] at h1
    rcases h1 with c0 | c1 | c2
    · have := v_eq n c0; omega
    · have : j = 0 := by have := v_eq n c1; omega
      subst this; rfl
    · have := v_eq n c2; omega
  · rintro rfl
    exact ⟨⟨0, by omega, rfl⟩, by
      intro x hx; simp only [bEdge, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [fanTriangle]⟩

private lemma filter_triangles_bEdgeClose (n : ℕ) (hn : 3 ≤ n) :
    (fanTriangles n hn).filter (fun t => bEdgeClose n hn ⊆ t) =
      {fanTriangle n (n - 3) (by omega)} := by
  ext t
  simp only [mem_filter, mem_fanTriangles n hn, mem_singleton]
  constructor
  · rintro ⟨⟨j, hj, rfl⟩, hsub⟩
    have hn1 : v n (n - 1) (by omega) ∈ fanTriangle n j hj :=
      hsub (by simp [bEdgeClose])
    simp only [fanTriangle, mem_insert, mem_singleton] at hn1
    rcases hn1 with c0 | c1 | c2
    · have := v_eq n c0; omega
    · have := v_eq n c1; omega
    · have : j = n - 3 := by have := v_eq n c2; omega
      subst this; rfl
  · rintro rfl
    exact ⟨⟨n - 3, by omega, rfl⟩, by
      intro x hx; simp only [bEdgeClose, mem_insert, mem_singleton] at hx
      rcases hx with hx | hx
      · -- x = v (n-1) = v ((n-3)+2)
        have hx' : x = v n ((n - 3) + 2) (by omega) := by
          apply Fin.eq_of_val_eq
          have hv := congrArg Fin.val hx
          simp only [v] at hv ⊢
          omega
        simp [fanTriangle, hx']
      · -- x = v 0
        simp [fanTriangle, hx]⟩

private lemma card_filter_bEdge (n : ℕ) (hn : 3 ≤ n) (k : ℕ) (hk : k + 1 < n) :
    ((fanTriangles n hn).filter (fun t => bEdge n k hk ⊆ t)).card = 1 := by
  by_cases hk0 : k = 0
  · subst hk0
    rw [filter_triangles_bEdge_zero, card_singleton]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    rw [filter_triangles_bEdge n hn k hk hkpos, card_singleton]

private lemma card_filter_bEdgeClose (n : ℕ) (hn : 3 ≤ n) :
    ((fanTriangles n hn).filter (fun t => bEdgeClose n hn ⊆ t)).card = 1 := by
  rw [filter_triangles_bEdgeClose, card_singleton]

private lemma edge_incidence_fan (n : ℕ) (hn : 3 ≤ n) :
    ∀ e ∈ fanEdges n hn,
      ((fanTriangles n hn).filter (fun t => e ⊆ t)).card =
        if e ∈ fanBoundary n hn then 1 else 2 := by
  intro e he
  rcases mem_union.mp he with heB | heD
  · have hif : e ∈ fanBoundary n hn := heB
    simp only [hif, ↓reduceIte]
    rcases (mem_fanBoundary n hn).mp heB with ⟨k, hk, rfl⟩ | rfl
    · exact card_filter_bEdge n hn k hk
    · exact card_filter_bEdgeClose n hn
  · obtain ⟨i, hi, rfl⟩ := (mem_fanDiagonals n hn).mp heD
    have hnot : fanDiagonal n i hi ∉ fanBoundary n hn :=
      not_mem_boundary_of_diagonal n hn ((mem_fanDiagonals n hn).mpr ⟨i, hi, rfl⟩)
    simp only [hnot, ↓reduceIte]
    exact card_filter_diagonal n hn i hi

/-- Combinatorial fan disk triangulation of the abstract `n`-gon on `Fin n`. -/
def fan (n : ℕ) (hn : 3 ≤ n) : CombinatorialDiskTriangulation (Fin n) where
  triangles := fanTriangles n hn
  edges := fanEdges n hn
  boundaryEdges := fanBoundary n hn
  triangle_card := triangle_card_fan n hn
  edge_card := edge_card_fan n hn
  boundary_subset := boundary_subset_fan n hn
  triangle_edges_mem := triangle_edges_mem_fan n hn
  edge_incidence := edge_incidence_fan n hn

private lemma card_fanTriangles (n : ℕ) (hn : 3 ≤ n) :
    (fanTriangles n hn).card = n - 2 := by
  dsimp [fanTriangles]
  rw [card_image_of_injective _ (fun a b h =>
    Subtype.ext (eq_of_fanTriangle_eq n (mem_range.mp a.2) (mem_range.mp b.2) h))]
  simp [card_attach, card_range]

private lemma card_fanDiagonals (n : ℕ) (hn : 3 ≤ n) :
    (fanDiagonals n hn).card = n - 3 := by
  dsimp [fanDiagonals]
  rw [card_image_of_injective _ (fun a b h =>
    Subtype.ext (eq_of_fanDiagonal_eq n (mem_range.mp a.2) (mem_range.mp b.2) h))]
  simp [card_attach, card_range]

private lemma card_fanBoundary (n : ℕ) (hn : 3 ≤ n) :
    (fanBoundary n hn).card = n := by
  dsimp [fanBoundary]
  have hdisj : Disjoint
      ((range (n - 1)).attach.image fun k =>
        bEdge n k.1 (by have := mem_range.mp k.2; omega))
      {bEdgeClose n hn} := by
    refine disjoint_singleton_right.mpr ?_
    intro hmem
    rcases mem_image.mp hmem with ⟨⟨k, hk⟩, _, heq⟩
    exact (bEdge_ne_close n hn k (by have := mem_range.mp hk; omega)) heq
  rw [card_union_of_disjoint hdisj, card_singleton]
  have himg :
      (((range (n - 1)).attach.image fun k =>
        bEdge n k.1 (by have := mem_range.mp k.2; omega))).card = n - 1 := by
    rw [card_image_of_injective _ (fun a b h => by
      have hk1 : a.1 + 1 < n := by have := mem_range.mp a.2; omega
      have hk2 : b.1 + 1 < n := by have := mem_range.mp b.2; omega
      exact Subtype.ext (eq_of_bEdge_eq n hk1 hk2 h))]
    simp [card_attach, card_range]
  omega

theorem fan_T (n : ℕ) (hn : 3 ≤ n) : (fan n hn).T = n - 2 := by
  change (fanTriangles n hn).card = n - 2
  exact card_fanTriangles n hn

theorem fan_B (n : ℕ) (hn : 3 ≤ n) : (fan n hn).B = n := by
  change (fanBoundary n hn).card = n
  exact card_fanBoundary n hn

theorem fan_E (n : ℕ) (hn : 3 ≤ n) : (fan n hn).E = 2 * n - 3 := by
  change (fanEdges n hn).card = 2 * n - 3
  dsimp [fanEdges]
  rw [card_union_of_disjoint (disjoint_boundary_diagonals n hn),
    card_fanBoundary n hn, card_fanDiagonals n hn]
  omega

theorem fan_V (n : ℕ) (hn : 3 ≤ n) : (fan n hn).V = n := by
  change ((fanEdges n hn).biUnion id).card = n
  apply le_antisymm
  · exact (card_le_card (fun _ _ => mem_univ _)).trans_eq (by simp [card_univ])
  · have hsub : (univ : Finset (Fin n)) ⊆ (fanEdges n hn).biUnion id := by
      intro i _
      by_cases hlast : i.val = n - 1
      · refine mem_biUnion.mpr ⟨bEdgeClose n hn,
          boundary_mem_edges n hn (bEdgeClose_mem_boundary n hn), ?_⟩
        change i ∈ ({v n (n - 1) (by omega), v n 0 (by omega)} : Finset (Fin n))
        simp only [mem_insert, mem_singleton]
        refine Or.inl ?_
        exact Fin.eq_of_val_eq (by simpa [v] using hlast)
      · have hk : i.val + 1 < n := by have := i.isLt; omega
        refine mem_biUnion.mpr ⟨bEdge n i.val hk,
          boundary_mem_edges n hn (bEdge_mem_boundary n hn i.val hk), ?_⟩
        change i ∈ ({v n i.val (by omega), v n (i.val + 1) hk} : Finset (Fin n))
        simp only [mem_insert, mem_singleton]
        refine Or.inl ?_
        exact Fin.eq_of_val_eq (by simp [v])
    have hcard : (univ : Finset (Fin n)).card = n := by simp [card_univ]
    calc
      n = #(univ : Finset (Fin n)) := hcard.symm
      _ ≤ #((fanEdges n hn).biUnion id) := card_le_card hsub

theorem fan_V_eq_B (n : ℕ) (hn : 3 ≤ n) : (fan n hn).V = (fan n hn).B := by
  rw [fan_V, fan_B]

theorem fan_T_add_two_eq_B (n : ℕ) (hn : 3 ≤ n) :
    (fan n hn).T + 2 = (fan n hn).B := by
  rw [fan_T, fan_B]; omega

theorem fan_planar_euler (n : ℕ) (hn : 3 ≤ n) :
    ((fan n hn).planarCounts).eulerChar = 2 :=
  (fan n hn).planar_euler_of_empty_interior (fan_V_eq_B n hn) (fan_T_add_two_eq_B n hn)

/-- Existence: every n-gon with `n ≥ 3` admits a combinatorial fan
disk triangulation on `Fin n`. -/
theorem exists_fan_disk_triangulation (n : ℕ) (hn : 3 ≤ n) :
    Nonempty (CombinatorialDiskTriangulation (Fin n)) :=
  ⟨fan n hn⟩

def fan3 : CombinatorialDiskTriangulation (Fin 3) := fan 3 (by omega)
def fan4 : CombinatorialDiskTriangulation (Fin 4) := fan 4 (by omega)
def fan5 : CombinatorialDiskTriangulation (Fin 5) := fan 5 (by omega)
def fan6 : CombinatorialDiskTriangulation (Fin 6) := fan 6 (by omega)
def fan7 : CombinatorialDiskTriangulation (Fin 7) := fan 7 (by omega)

theorem fan3_planar_euler : (fan3.planarCounts).eulerChar = 2 := fan_planar_euler 3 (by omega)
theorem fan4_planar_euler : (fan4.planarCounts).eulerChar = 2 := fan_planar_euler 4 (by omega)
theorem fan5_planar_euler : (fan5.planarCounts).eulerChar = 2 := fan_planar_euler 5 (by omega)
theorem fan6_planar_euler : (fan6.planarCounts).eulerChar = 2 := fan_planar_euler 6 (by omega)
theorem fan7_planar_euler : (fan7.planarCounts).eulerChar = 2 := fan_planar_euler 7 (by omega)

end FanDiskTriangulation
end Picks
end EulersGem
