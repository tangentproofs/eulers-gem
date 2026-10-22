---
id: Results.results_pick_count_of_euler
title: "The bookkeeping step: five hypotheses in, Pick's count out"
summary: "Pure arithmetic. Given `V = I + B`, `F = T + 1`, `V − E + F = 2`, `2E = 3T + B` and `A = T/2` — all as hypotheses — it concludes `A = I + B/2 − 1`. It proves nothing about polygons by itself."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "**`heuler : (V : ℤ) − E + F = 2` is a free hypothesis on bare numbers.** So are the other four. Nothing in the statement refers to a polygon, a lattice, a triangulation, an area or a face. It is an identity among seven numbers and a rational."
  - "The docstring says \"The Euler input is not a bare hypothesis: a caller passes `results_euler_relation_dimension_three` …\". Read that as a note about *intended use*: in the statement it is a bare hypothesis, and the claim is about what callers do. [results_picks_theorem](#/node/Results.results_picks_theorem) is one such caller and does route it honestly."
  - "`I B V E T F : ℕ` but `heuler` and `hshake` mix `ℤ` and `ℕ`: `heuler` is cast to `ℤ` (so no truncated subtraction) while `hshake : 2 * E = 3 * T + B` is in `ℕ` (where it is an equation between sums, so truncation cannot bite). `A : ℚ`, so `T/2` and `B/2` are exact halves."
  - "The name contains `of_euler`, which is accurate about the hypothesis and could be misread as a claim that Euler's theorem is being applied. It is not: the hypothesis is the numeral `2`."
widgets:
  - type: triangulate
    title: "The five hypotheses, for whatever I and B you like"
    config:
      I: 2
      B: 7
      show: [counts, moves]
quiz:
  - q: "How many hypotheses does the statement have, and is `V − E + F = 2` among them?"
    type: choice
    choices:
      - "five, and yes — `heuler : (V : ℤ) - E + F = 2` is one of them"
      - "four, and Euler is derived"
      - "one, and Euler is derived"
      - "five, and Euler is the conclusion"
    answer: 0
    explain: "`(hV : V = I + B) (hF : F = T + 1) (heuler : (V : ℤ) - E + F = 2) (hshake : 2 * E = 3 * T + B) (harea : A = (T : ℚ) / 2)`. All five are hypotheses; the conclusion is `A = I + B/2 − 1`."
  - q: "Does this theorem prove Pick's theorem?"
    type: choice
    choices:
      - "yes"
      - "no — it is an arithmetic identity among numbers; nothing in it mentions a polygon, a lattice or an area"
      - "yes, for convex polygons"
      - "yes, given a triangulation"
    answer: 1
    explain: "The statement quantifies over seven numbers and concludes an equation between rationals. It applies to any numbers satisfying the five hypotheses, whether or not a polygon with those counts exists — and it says nothing about any polygon that does. The geometric content of Pick's theorem lives in `shoelace_eq_two_cardI_add_B_sub_two_div_two` (cutting a polygon into primitive triangles) and `volume_convexHullRegion_eq_ofReal_shoelace` (shoelace = Lebesgue measure)."
  - q: "`I = 2`, `B = 7`. What are `T`, `E` and the area `T/2`?"
    type: choice
    choices:
      - "`T = 9`, `E = 17`, area `9/2`"
      - "`T = 7`, `E = 15`, area `7/2`"
      - "`T = 9`, `E = 18`, area `9/2`"
      - "`T = 11`, `E = 17`, area `11/2`"
    answer: 0
    explain: "`T = 2I + B − 2 = 9`, `E = 3I + 2B − 3 = 17`, `V = I + B = 9`, `F = T + 1 = 10`. Check: `V − E + F = 9 − 17 + 10 = 2` ✓, `2E = 34 = 3·9 + 7` ✓, and `T/2 = 9/2 = 2 + 7/2 − 1` ✓."
  - q: "Where does the real geometric work of Pick's theorem happen, if not here?"
    type: choice
    choices:
      - "in `shoelace_eq_two_cardI_add_B_sub_two_div_two` (cutting the polygon into primitive triangles) and `volume_convexHullRegion_eq_ofReal_shoelace` (shoelace = Lebesgue measure)"
      - "in `triangulation_count_identity_nat`"
      - "in `funkenbusch_identity`"
      - "in this theorem's proof"
    answer: 0
    explain: "Those two, in `PickFromEuler.lean` and `LatticeArea.lean`. This theorem's proof is `EulersGem.Picks.triangulation_count_identity_nat …`, which is `omega`-and-`linear_combination` arithmetic in `Picks.lean`."
  - q: "Suppose a caller has a polygon and wants to use this theorem. What must they supply?"
    type: choice
    choices:
      - "a triangulation whose counts really are `V = I + B`, `T = 2I + B − 2`, `E = 3I + 2B − 3`, with `V − E + F = 2` and area `T/2` — all five, proved for their polygon"
      - "only the polygon"
      - "only `V − E + F = 2`"
      - "nothing; the theorem applies to every polygon"
    answer: 0
    explain: "That is exactly what `results_picks_theorem` does, in five `have`s, before calling this. The hard parts there are producing the primitive triangulation and knowing each triangle has area `1/2`; this theorem then adds up."
---

## Plain English

```lean
theorem results_pick_count_of_euler
    (I B V E T F : ℕ) (A : ℚ)
    (hV : V = I + B)
    (hF : F = T + 1)
    (heuler : (V : ℤ) - E + F = 2)
    (hshake : 2 * E = 3 * T + B)
    (harea : A = (T : ℚ) / 2) :
    A = (I : ℚ) + (B : ℚ) / 2 - 1
```

This is the arithmetic that turns Euler's formula into Pick's formula — **once somebody has done
the geometry.** Read the hypotheses:

- `V = I + B`: every vertex of the triangulation is a lattice point, inside or on the boundary.
- `F = T + 1`: the faces are the triangles plus one unbounded outer face.
- `V − E + F = 2`: Euler.
- `2E = 3T + B`: handshaking — each triangle has three edges, interior edges belong to two
  triangles and boundary edges to one.
- `A = T/2`: each triangle has area `1/2`.

Then `A = I + B/2 − 1`.

Every one of those five is a **hypothesis**, about plain numbers. Nothing in the statement knows
what a polygon is.

### In one breath

Suppose someone has already cut a shape into the smallest possible triangles, and already told you
how many corners, edges and triangles there are, and already told you Euler's count comes to two,
and already told you each triangle has area a half. Then adding it all up gives Pick's formula.
That last adding-up is this theorem, and it is the easy part. The hard part — actually cutting the
shape, and knowing the small triangles really do have area a half — is somewhere else.

## What this does and does not prove

**It does prove:**

- The algebraic identity. Substituting `hV`, `hF` and `hshake` into `heuler` forces
  `E = 3I + 2B − 3` (`funkenbusch_of_triangulation`) and then `F = 2I + B − 1`, so
  `A = T/2 = (F − 1)/2 = I + B/2 − 1` (`funkenbusch_identity`). All of it is `omega` and
  `linear_combination` over `ℤ` and `ℚ`.
- Faithfully to W. W. Funkenbusch's 1974 *Amer. Math. Monthly* argument "From Euler's Formula to
  Pick's Formula Using an Edge Theorem", which is the route the module is named after.

**It does not prove:**

- **Pick's theorem.** It is not a statement about polygons. No lattice, no area, no measure, no
  triangulation appears in it.
- **Euler's formula.** `heuler` is a hypothesis, and it is the numeral `2` on the right-hand side
  of an equation between naturals cast to `ℤ`. The honest reading of the name
  `results_pick_count_of_euler` is "the Pick count, *given* Euler".
- **That any polygon satisfies the hypotheses.** That a strictly convex lattice polygon has a
  triangulation with these counts is the content of
  `shoelace_eq_two_cardI_add_B_sub_two_div_two` in `PickFromEuler.lean`, and that `V − E + F = 2`
  for those counts is
  [`triangulated_disk_euler_from_characteristic`](#/node/Picks.triangulated_disk_euler_from_characteristic).
  Both are separate theorems; this one is downstream of neither.

### Why it is in `Results` at all

Because it is the named step of the classical argument, and because
[`results_picks_theorem`](#/node/Results.results_picks_theorem) calls it. Look at that proof: it
spends twelve lines establishing the five hypotheses for a specific polygon and one line calling
this. Having the bookkeeping step visible and separately named is what makes it possible to see
that the geometric work is elsewhere — which is the point.

`Picks.lean`'s own module docstring makes the same point, and adds that the identifiers in it
"deliberately avoid `picks_*` so Results/README cannot be skimmed as claiming Pick".

### Where it sits

- Its proof is [`Picks.triangulation_count_identity_nat`](#/node/Picks.triangulation_count_identity_nat).
- It is used by [`results_picks_theorem`](#/node/Results.results_picks_theorem).
- Its siblings in the same honest category are
  [`results_fan_pick_of_euler`](#/node/Results.results_fan_pick_of_euler) and
  [`results_disk_pick_of_euler`](#/node/Results.results_disk_pick_of_euler).
