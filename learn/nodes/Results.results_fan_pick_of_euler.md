---
id: Results.results_fan_pick_of_euler
title: "The statement is (n − 2)/2 = n/2 − 1"
summary: "Read the statement before the name: it says that for `n ≥ 3`, `(n − 2)/2 = n/2 − 1` as rationals. The fans and the Euler characteristic are in the proof route, not in the claim."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "**The statement is an arithmetic identity.** `((n - 2 : ℕ) : ℚ) / 2 = (n : ℚ) / 2 - 1`. There is no fan, no triangulation, no polygon and no Euler characteristic in it. The name and docstring describe how the proof is routed."
  - "The hypothesis `3 ≤ n` is needed only because `n - 2` is **truncated natural subtraction**: at `n = 1` the left side is `0/2 = 0` and the right side is `-1/2`. For `n ≥ 2` it is already true, so the `3` is inherited from the fan story rather than forced by the arithmetic."
  - "The proof *does* go through real content: `fan_pick_count_from_characteristic` derives the fan's `V − E + F = 2` from `triangle_disk_euler`, which derives it from `Simplex.faceEulerSum_body_eq_one` — a geometric 2-simplex's Euler–Poincaré characteristic — and then inducts over fan size. That is worth knowing, and it is not what the statement claims."
widgets:
  - type: triangulate
    title: "The fan is the I = 0 line of the table"
    config:
      I: 0
      B: 6
      show: [counts, moves]
quiz:
  - q: "What is the conclusion of the statement?"
    type: choice
    choices:
      - "`((n - 2 : ℕ) : ℚ) / 2 = (n : ℚ) / 2 - 1`"
      - "a fan triangulation of an `n`-gon has Euler number 2"
      - "a lattice `n`-gon with no interior points has area `n/2 − 1`"
      - "`V − E + F = 2` for a triangulated disk"
    answer: 0
    explain: "`theorem results_fan_pick_of_euler (n : ℕ) (hn : 3 ≤ n) : ((n - 2 : ℕ) : ℚ) / 2 = (n : ℚ) / 2 - 1`. That is the whole statement. The other three choices describe what the *proof* passes through."
  - q: "Why is the hypothesis `3 ≤ n` there?"
    type: choice
    choices:
      - "to keep `n - 2` from truncating in ℕ (and, beyond that, because the fan story needs a polygon)"
      - "because fans of 2-gons do not exist"
      - "because the identity is false for `n = 2`"
      - "it is unused"
    answer: 0
    explain: "In ℕ, `1 - 2 = 0`, so at `n = 1` the left side is `0` and the right side is `-1/2`. For `n = 2` both sides are `0`. So arithmetically `2 ≤ n` would do; the `3` comes from `LatticePolygon.length_ge` and the fan setting."
  - q: "`n = 7`. Check both sides."
    type: choice
    choices: ["`5/2` and `5/2`", "`5/2` and `7/2`", "`7/2` and `5/2`", "`2` and `2`"]
    answer: 0
    explain: "`(7 − 2)/2 = 5/2` and `7/2 − 1 = 5/2`. A fan of a heptagon has 5 triangles, each of area `1/2` if primitive, so area `5/2`; and `I + B/2 − 1 = 0 + 7/2 − 1 = 5/2`. Same number, and the statement is the equality of those two expressions."
  - q: "Does the statement establish that a fan triangulation of an `n`-gon exists?"
    type: choice
    choices:
      - "no — that is `FanDiskTriangulation.fan`, a separate construction, used in the proof"
      - "yes, for every `n ≥ 3`"
      - "yes, but only for convex polygons"
    answer: 0
    explain: "`def fan (n : ℕ) (hn : 3 ≤ n) : CombinatorialDiskTriangulation (Fin n)` in `FanDisk.lean` is the construction, and `ROADMAP.md` records \"fan combinatorial triangulation existence for **all** `n ≥ 3`\" as a separate item of work. None of it appears in this statement."
  - q: "Where does the Euler characteristic enter?"
    type: choice
    choices:
      - "only in the proof: `triangle_disk_euler` gets `3 − 3 + 2 = 2` from a geometric 2-simplex's `faceEulerSum = 1`, and an induction extends it to every fan"
      - "in the hypothesis `3 ≤ n`"
      - "in the conclusion"
      - "nowhere at all"
    answer: 0
    explain: "`fan_pick_count_from_characteristic` (DiskEuler.lean) calls `fan_eulerChar_from_characteristic`, which starts at `triangle_disk_euler b` for an `AffineBasis (Fin 3) ℝ E` and inducts with `fan_eulerChar_succ`. Genuine Euler–Poincaré content — in the proof."
---

## Plain English

```lean
theorem results_fan_pick_of_euler (n : ℕ) (hn : 3 ≤ n) :
    ((n - 2 : ℕ) : ℚ) / 2 = (n : ℚ) / 2 - 1
```

**That is the entire statement.** For a natural number `n ≥ 3`, the rational `(n − 2)/2` equals
`n/2 − 1`.

It is true, and you can see it is true at a glance. What makes it a `Results` theorem is the
*route*: the Lean proof of it goes through a geometric triangle's Euler–Poincaré characteristic.
The docstring explains that route, and the route is interesting. It is just not the claim.

### In one breath

Fan a polygon into triangles from one corner: an `n`-sided polygon gives `n − 2` of them. If each
has area a half, the total is `(n − 2)/2`. Pick's formula, for a polygon with nothing inside it,
predicts `n/2 − 1`. Those two expressions are the same expression. Noticing that they agree is
one line of algebra; knowing that the fan really has `n − 2` triangles, and that each really has
area a half, is the mathematics — and it sits in other files.

## What this does and does not prove

**It does prove:** that `(n − 2)/2 = n/2 − 1` for `n ≥ 3` in ℚ, with `n − 2` being natural
subtraction (so the hypothesis matters).

**It does not prove:**

- that an `n`-gon has a fan triangulation (that is `FanDiskTriangulation.fan`);
- that a fan has `n − 2` triangles (`fan_T`);
- that those triangles have area `1/2` each;
- that a fan triangulation has `V − E + F = 2` (that is `fan_eulerChar_from_characteristic`, and
  it *is* proved);
- Pick's formula for any polygon.

Do not describe this statement as "an empty fan's Pick count follows from the Euler
characteristic". The *proof route* can be described that way. The statement is an identity between
two ways of writing the same rational number.

### What the proof route does show

This part is real, and is the reason the theorem is here:

1. `Simplex.faceEulerSum_body_eq_one` — a geometric 2-simplex in a 2-dimensional space has
   [`faceEulerSum = 1`](#/node/faceEulerSum), by
   [`Euler_Poincare_of_isPolytope`](#/node/Euler_Poincare_of_isPolytope).
2. `triangle_disk_euler` — it has 3 vertices, 3 edges and 1 two-face; add one exterior face and
   `3 − 3 + 2 = 2`.
3. `fan_eulerChar_succ` — adding a vertex to a fan adds one vertex, two edges and one face, so the
   Euler number is unchanged.
4. `fan_eulerChar_from_characteristic` — by induction, **every** fan has disk Euler number 2.
5. `fan_pick_count_from_characteristic` — unwinding the fan's `(V, E, T, F)` turns that into the
   identity above.

Step 4 is a theorem worth having. Step 5 throws almost all of it away, because its conclusion no
longer mentions the fan. That is the gap between this statement and its proof, and it is the whole
point of reading statements rather than names.

### Where it sits

- Proof: `Picks.FanDiskTriangulation.fan_pick_count_from_characteristic` (`DiskEuler.lean`).
- Siblings in the same honest category:
  [`results_pick_count_of_euler`](#/node/Results.results_pick_count_of_euler) and
  [`results_disk_pick_of_euler`](#/node/Results.results_disk_pick_of_euler).
- The geometric Pick claims are
  [`results_picks_theorem`](#/node/Results.results_picks_theorem) and
  [`results_picks_of_empty_primitive_fan`](#/node/Results.results_picks_of_empty_primitive_fan).
