---
id: Results.results_disk_pick_of_euler
title: "Given A = (2I + B − 2)/2, conclude A = I + B/2 − 1"
summary: "An arithmetic consequence: the area formula is assumed in triangle-count form and restated in Pick form. The triangulated disk and its Euler number are in the proof route, not in the statement."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "**`harea : A = ((2 * I + B - 2 : ℕ) : ℚ) / 2` is a hypothesis.** The statement assumes the area is half the triangle count and concludes it is `I + B/2 − 1`. No disk, no triangulation and no polygon is quantified over."
  - "**`n` appears only as a bound.** The hypotheses are `3 ≤ n` and `n ≤ B`, and `n` occurs nowhere else. It is there because the proof routes through `triangulated_disk_euler_from_characteristic n B I`, which starts from an `n`-gon corner cycle. Arithmetically, `3 ≤ B` would do."
  - "`2 * I + B - 2` is **truncated** natural subtraction, which is why `3 ≤ n ≤ B` matters: it guarantees `B ≥ 3`, so `2I + B ≥ 2` and nothing truncates."
  - "The proof route is real: `triangulated_disk_euler_from_characteristic` builds its Euler number from a geometric triangle's characteristic by four kinds of count-preserving move. That theorem's own statement is also an identity between numerals — see its node."
widgets:
  - type: triangulate
    title: "The hypothesis, the conclusion, and the four moves the proof uses"
    config:
      I: 3
      B: 8
      show: [counts, moves]
quiz:
  - q: "Which of these is a hypothesis of the statement?"
    type: choice
    choices:
      - "`A = ((2 * I + B - 2 : ℕ) : ℚ) / 2`"
      - "`V − E + F = 2`"
      - "that the polygon has a triangulation"
      - "`A = I + B/2 − 1`"
    answer: 0
    explain: "`(harea : A = ((2 * I + B - 2 : ℕ) : ℚ) / 2)` is the hypothesis; `A = (I : ℚ) + (B : ℚ) / 2 - 1` is the conclusion. The Euler count is in the proof (`triangulated_disk_euler_from_characteristic`), not in the statement."
  - q: "Where does `n` appear in the statement, apart from its two bounds `3 ≤ n` and `n ≤ B`?"
    type: choice
    choices: ["nowhere", "in the area formula", "in the conclusion", "as the number of triangles"]
    answer: 0
    explain: "`theorem results_disk_pick_of_euler (n B I : ℕ) (A : ℚ) (hn : 3 ≤ n) (hnB : n ≤ B) (harea : …)`. `n` is bound by `hn` and `hnB` and used nowhere else. It is a shadow of the proof route, where `n` is the number of corners of the polygon the disk triangulation grew from."
  - q: "`I = 3`, `B = 8`. What does each side come to?"
    type: choice
    choices:
      - "`A = 12/2 = 6` and `3 + 8/2 − 1 = 6`"
      - "`A = 11/2` and `3 + 8/2 − 1 = 6`"
      - "`A = 6` and `3 + 4 − 1 = 7`"
      - "`A = 14/2 = 7` and `7`"
    answer: 0
    explain: "`2I + B − 2 = 6 + 8 − 2 = 12`, so the hypothesis says `A = 6`; and `3 + 4 − 1 = 6`. `T = 12` triangles of area `1/2` is area 6, consistent."
  - q: "True or false: this theorem proves Pick's formula for a triangulated disk."
    type: choice
    choices:
      - "True"
      - "False — it converts one assumed form of the area into another; the disk, its triangulation and its Euler number are all outside the statement"
    answer: 1
    explain: "False. Compare the genuinely geometric Pick claims, [results_picks_theorem](#/node/Results.results_picks_theorem) and [results_picks_of_empty_primitive_fan](#/node/Results.results_picks_of_empty_primitive_fan), which quantify over a `LatticePolygon` and conclude a `MeasureTheory.volume`."
  - q: "What does the *proof route* genuinely establish?"
    type: choice
    choices:
      - "that the counts `V = I + B`, `E = 3I + 2B − 3`, `F = 2I + B − 1` have `V − E + F = 2`, by starting at a geometric triangle's characteristic and applying moves that preserve the count"
      - "nothing beyond the statement"
      - "that every lattice polygon has a primitive triangulation"
    answer: 0
    explain: "`pick_count_of_disk_from_characteristic` calls [triangulated_disk_euler_from_characteristic](#/node/Picks.triangulated_disk_euler_from_characteristic), whose proof chains `corner_cycle_euler_from_characteristic` with `eulerChar_insert_boundary_iter`, `eulerChar_add_diagonal_iter` and `eulerChar_stellar_iter`. Each move provably leaves `V − E + F` alone."
---

## Plain English

```lean
theorem results_disk_pick_of_euler
    (n B I : ℕ) (A : ℚ) (hn : 3 ≤ n) (hnB : n ≤ B)
    (harea : A = ((2 * I + B - 2 : ℕ) : ℚ) / 2) :
    A = (I : ℚ) + (B : ℚ) / 2 - 1
```

Read it as a sentence: *suppose a number `A` is half of `2I + B − 2`. Then `A` is `I + B/2 − 1`.*

That is a rearrangement. `(2I + B − 2)/2 = I + B/2 − 1` — divide through. The hypotheses
`3 ≤ n ≤ B` are there to keep the truncated natural subtraction `2 * I + B - 2` honest, and `n`
plays no other role.

So the statement is arithmetic. The interesting part is why it is phrased this way, and what the
proof does.

### In one breath

A triangulated patch of graph paper with `I` crossings inside and `B` on the rim has `2I + B − 2`
little triangles, each of area a half, so its area is `I + B/2 − 1`. That sentence contains a
count, a geometric fact and an algebraic rearrangement. This theorem is the rearrangement. The
count is a different theorem, and the geometric fact is a third.

## What this does and does not prove

**It does prove:** that `A = (2I + B − 2)/2` implies `A = I + B/2 − 1`, with the natural
subtraction handled correctly under `3 ≤ n ≤ B`.

**It does not prove:**

- that any disk, polygon or triangulation has `T = 2I + B − 2` triangles;
- that those triangles have area `1/2`;
- that the area of anything is `(2I + B − 2)/2` — that is the hypothesis;
- Pick's formula for a lattice polygon. For that, see
  [`results_picks_theorem`](#/node/Results.results_picks_theorem).

### What the proof route does show

`pick_count_of_disk_from_characteristic` (`DiskEuler.lean`) uses
[`triangulated_disk_euler_from_characteristic`](#/node/Picks.triangulated_disk_euler_from_characteristic),
and *that* proof is the interesting object. It builds a triangulated disk in four stages and shows
each stage preserves `V − E + F`:

| stage | what changes | lemma |
|---|---|---|
| start: the corner `n`-cycle | `V = E = n`, one inner face and the outer face | `corner_cycle_euler_from_characteristic`, itself from `triangle_disk_euler` and a fan induction |
| insert `B − n` boundary vertices | `+1` vertex, `+1` edge each | `eulerChar_insert_boundary_iter` |
| add `B − 3` diagonals | `+1` edge, `+1` face each | `eulerChar_add_diagonal_iter` |
| `I` stellar subdivisions | `+1` vertex, `+3` edges, `+2` triangles each | `eulerChar_stellar_iter` |

and the start is a *geometric* triangle, whose Euler number comes from
[`faceEulerSum = 1`](#/node/faceEulerSum) by
[`Euler_Poincare_of_isPolytope`](#/node/Euler_Poincare_of_isPolytope). So the chain back to the
Euler–Poincaré root is real. The widget above steps through those four stages.

What makes it awkward to describe is that both this theorem and the lemma it calls have statements
that are identities between numerals, with the combinatorics living entirely in the proof terms.
`lean/UNIFIED_SPINE.md` records the remaining gap in exactly those terms: discharging
`hEuler_planar` from `Euler_Poincare_full` for *general* planar disks is listed as open.

### Where it sits

- Proof: `Picks.pick_count_of_disk_from_characteristic` (`DiskEuler.lean`).
- Siblings: [`results_pick_count_of_euler`](#/node/Results.results_pick_count_of_euler),
  [`results_fan_pick_of_euler`](#/node/Results.results_fan_pick_of_euler).
- The geometric Pick claims: [`results_picks_theorem`](#/node/Results.results_picks_theorem),
  [`results_picks_of_empty_primitive_fan`](#/node/Results.results_picks_of_empty_primitive_fan).
