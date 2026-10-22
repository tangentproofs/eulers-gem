---
id: Picks.triangulated_disk_euler_from_characteristic
title: "The disk Euler number, built up from a real triangle"
summary: "An identity between numerals in `n`, `B`, `I`: `(I+B) − (3I+2B−3) + (2I+B−2+1) = 2`. Its proof starts at a geometric 2-simplex's Euler–Poincaré characteristic and applies four count-preserving moves."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "**The statement is an identity between numerals.** Written out: `((I + B : ℕ) : ℤ) - ↑(3 * I + 2 * B - 3) + ↑(2 * I + B - 2 + 1) = 2`. No disk, triangulation or polygon is quantified over; `n` appears only in the hypotheses `3 ≤ n` and `n ≤ B`. `omega` would prove it given `B ≥ 3`."
  - "**The proof, by contrast, is real.** `corner_cycle_euler_from_characteristic` traces back to `triangle_disk_euler`, which traces back to `Simplex.faceEulerSum_body_eq_one` — the genuine Euler–Poincaré characteristic of a geometric 2-simplex. The moves (`eulerChar_insert_boundary`, `eulerChar_add_diagonal`, `eulerChar_stellar`) each provably preserve the count."
  - "The natural subtractions `3*I + 2*B - 3` and `2*I + B - 2` truncate; `3 ≤ n ≤ B` is what keeps them honest."
  - "`lean/ROADMAP.md` lists \"general EP→planar from `Euler_Poincare_full`\" as still open (and `lean/UNIFIED_SPINE.md` records the same gap). This lemma is the current bridge, and its statement shape is why that item is still on the list: a theorem *about disks* with their Euler number as the conclusion would be stronger."
widgets:
  - type: triangulate
    title: "The four moves, stepped through"
    config:
      I: 2
      B: 7
      show: [counts, moves]
quiz:
  - q: "What is the conclusion, written out?"
    type: choice
    choices:
      - "`((I + B : ℕ) : ℤ) - ↑(3 * I + 2 * B - 3) + ↑(2 * I + B - 2 + 1) = 2`"
      - "every triangulated disk has `V − E + F = 2`"
      - "`faceEulerSum p 2 = 1`"
      - "`A = I + B/2 − 1`"
    answer: 0
    explain: "The numerals are `V = I + B`, `E = 3I + 2B − 3` and `F = T + 1 = 2I + B − 1`. The conclusion is that those three expressions satisfy the alternating identity. The second choice is what the proof route is *about*; it is not what the statement says."
  - q: "Where does `n` appear in the statement, besides `3 ≤ n` and `n ≤ B`?"
    type: choice
    choices: ["nowhere", "as the number of triangles", "in `E`", "in the conclusion"]
    answer: 0
    explain: "`theorem triangulated_disk_euler_from_characteristic (n B I : ℕ) (hn : 3 ≤ n) (hB : n ≤ B)`. `n` is the vertex count of the polygon the proof's corner cycle starts from, and it is eliminated along the way. Arithmetically only `3 ≤ B` is needed."
  - q: "The first stage of the proof is `corner_cycle_euler_from_characteristic n hn : (n : ℤ) - ↑n + 2 = 2`. Where does the genuine Euler content come from?"
    type: choice
    choices:
      - "`triangle_disk_euler`, which uses `Simplex.faceEulerSum_body_eq_one` for a geometric 2-simplex, then a fan induction"
      - "`decide`"
      - "`omega` on the statement"
      - "a hypothesis"
    answer: 0
    explain: "`corner_cycle_euler_from_characteristic` calls `FanDiskTriangulation.fan_eulerChar_from_characteristic`, which bottoms out at `triangle_disk_euler b` for an `AffineBasis (Fin 3) ℝ E` in a 2-dimensional space — and that is `Euler_Poincare_full` — the hypothesis-carrying form of [Euler_Poincare_of_isPolytope](#/node/Euler_Poincare_of_isPolytope) — applied to a triangle. The chain to the root is real."
  - q: "Adding a diagonal to a triangulated disk changes the counts how?"
    type: choice
    choices:
      - "`E + 1`, `F + 1`, `V` unchanged — so the alternating sum is unchanged"
      - "`E + 1`, `V + 1`"
      - "`E + 2`, `F + 1`, `V + 1`"
      - "`E + 3`, `V + 1`, `T + 2`"
    answer: 0
    explain: "`eulerChar_add_diagonal`. A diagonal splits one face into two: one more edge, one more face. The fourth choice is `eulerChar_stellar`, a subdivision at an interior point."
  - q: "A stellar subdivision at an interior lattice point changes the counts how?"
    type: choice
    choices:
      - "`V + 1`, `E + 3`, `T + 2`"
      - "`V + 1`, `E + 1`"
      - "`E + 1`, `T + 1`"
      - "`V + 1`, `E + 3`, `T + 3`"
    answer: 0
    explain: "`theorem eulerChar_stellar (V E T : ℕ) : (↑(V + 1) - ↑(E + 3) + ↑(T + 2 + 1)) = (V : ℤ) - ↑E + ↑(T + 1)`. One triangle becomes three, so `T + 2`, with three new edges to the new vertex. `(V+1) − (E+3) + (T+2+1) = V − E + T + 1`, unchanged."
  - q: "`I = 2`, `B = 7`. Compute `V`, `E`, `F` and the alternating sum."
    type: choice
    choices:
      - "`V = 9`, `E = 17`, `F = 11`, sum `3`"
      - "`V = 9`, `E = 17`, `F = 10`, sum `2`"
      - "`V = 9`, `E = 18`, `F = 11`, sum `2`"
      - "`V = 7`, `E = 15`, `F = 10`, sum `2`"
    answer: 1
    explain: "`V = I + B = 9`, `E = 3·2 + 2·7 − 3 = 17`, `T = 2·2 + 7 − 2 = 9`, `F = T + 1 = 10`. `9 − 17 + 10 = 2`."
---

## Plain English

```lean
theorem triangulated_disk_euler_from_characteristic
    (n B I : ℕ) (hn : 3 ≤ n) (hB : n ≤ B) :
    ((I + B : ℕ) : ℤ) - ↑(3 * I + 2 * B - 3) + ↑(2 * I + B - 2 + 1) = 2
```

The three expressions are the classical counts of a lattice triangulation:

> `V = I + B`,  `E = 3I + 2B − 3`,  `F = T + 1` where `T = 2I + B − 2`,

and the theorem says they satisfy `V − E + F = 2`.

As a *statement*, that is arithmetic — `omega` could do it given `B ≥ 3`. As a *proof*, it is the
Euler lane of the Pick argument, and it is worth following.

### In one breath

Start with a triangle, which you already know has Euler count two because you proved it
geometrically. Now build any triangulated patch out of it by three kinds of move: add a corner part
way along the rim, draw a diagonal, or plant a new point inside a triangle and join it to the three
corners. Each move adds the same amount to both sides of the count, so the count never budges. At
the end, read off the counts of the patch you built — and they are the formulas above.

### The four moves

| stage | counts afterwards | lemma |
|---|---|---|
| the corner `n`-cycle | `V = n`, `E = n`, one inner face + the outer face | `corner_cycle_euler_from_characteristic` |
| insert `B − n` boundary vertices | `V + 1`, `E + 1` each time | `eulerChar_insert_boundary_iter` |
| add `B − 3` diagonals | `E + 1`, `F + 1` each time | `eulerChar_add_diagonal_iter` |
| `I` stellar subdivisions | `V + 1`, `E + 3`, `T + 2` each time | `eulerChar_stellar_iter` |

Each of those `_iter` lemmas is an induction over the number of moves, and each single move is a
one-line `omega` fact. The widget above steps through the four stages for whatever `I` and `B` you
choose.

The real content is the first row. `corner_cycle_euler_from_characteristic n hn : (n : ℤ) − n + 2 = 2`
looks trivial, and its proof is not:

1. `Simplex.faceEulerSum_body_eq_one` — a geometric 2-simplex in a 2-dimensional inner product
   space has [`faceEulerSum = 1`](#/node/faceEulerSum), by `Euler_Poincare_full` applied to the
   simplex's H-representation (the hypothesis-carrying form of
   [`Euler_Poincare_of_isPolytope`](#/node/Euler_Poincare_of_isPolytope)).
2. `triangle_disk_euler` — that triangle has 3 vertices, 3 edges, 1 two-face; the only 2-face is
   the body, so adding one exterior face gives `3 − 3 + 2 = 2`.
3. `fan_eulerChar_succ` and `fan_eulerChar_from_characteristic` — every fan inherits that number by
   induction.
4. Deleting the fan's `n − 3` diagonals leaves the bare `n`-cycle, with the number intact.

So the chain back to the Euler–Poincaré root is genuine, and that is what satisfies the
repository's rule that Pick must discharge Euler rather than assume it.

### What is still missing

The statement's shape. A theorem of the form "every triangulated disk has `V − E + F = 2`" would
need a type of triangulated disks and a geometric realization theorem;
`lean/ROADMAP.md` lists exactly that as open ("general EP→planar from `Euler_Poincare_full`"), and
`lean/UNIFIED_SPINE.md` records the same gap.
What exists is this: the numbers that a triangulated disk *would* have, shown to satisfy the
identity, by an argument that starts from a real triangle.

Be precise about which of those you are claiming.

### Where it sits

Used by [`results_picks_theorem`](#/node/Results.results_picks_theorem) (to supply `hEuler'` to
[`results_pick_count_of_euler`](#/node/Results.results_pick_count_of_euler)) and by
`pick_count_of_disk_from_characteristic`, which is
[`results_disk_pick_of_euler`](#/node/Results.results_disk_pick_of_euler).
