---
id: Platonic.sub_mul_lt_four
title: "(s − 2)(m − 2) < 4, the inequality that leaves five"
summary: "From Euler plus the two double-counting identities, `(s − 2)(m − 2) < 4` in ℕ. With `s, m ≥ 3` that leaves exactly five pairs — and the cases at exactly 4 are the three flat tilings."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "The subtraction is in ℕ and so truncates, but `hs : 3 ≤ s` and `hm : 3 ≤ m` are fields of `RegularNumbers`, so `s − 2 ≥ 1` and `m − 2 ≥ 1` and no truncation occurs. The proof sets `a := s - 2`, `b := m - 2` and works with `1 ≤ a`, `1 ≤ b`."
  - "It takes a whole `RegularNumbers`, so it uses `hEuler`, `hFace`, `hVert` and `hE : 0 < E`. In particular it depends on `E > 0`: without it, `E · (2s + 2m − sm) = 2sm` would not force the coefficient positive."
  - "The companion `mul_euler_int` is the ℤ identity `E · (2s + 2m − s·m) = 2·s·m`, and `coeff = 4 − defect`, so the two statements are the same fact twice."
widgets:
  - type: schlafli
    title: "The grid of (s − 2)(m − 2), and the solve for each cell"
quiz:
  - q: "What exactly does `mul_euler_int` state?"
    type: choice
    choices:
      - "`(R.E : ℤ) * ((2 * R.s + 2 * R.m : ℤ) - R.s * R.m) = 2 * R.s * R.m`"
      - "`(R.s - 2) * (R.m - 2) < 4`"
      - "`(R.V : ℤ) - R.E + R.F = 2`"
      - "`R.s * R.F = 2 * R.E`"
    answer: 0
    explain: "`theorem mul_euler_int (R : RegularNumbers) : (R.E : ℤ) * ((2 * R.s + 2 * R.m : ℤ) - R.s * R.m) = 2 * R.s * R.m`. It is Euler multiplied by `s·m` with the two double-counting identities substituted. `sub_mul_lt_four` is its consequence."
  - q: "`2s + 2m − sm` and `(s − 2)(m − 2)` are related how?"
    type: choice
    choices:
      - "they sum to 4"
      - "they are equal"
      - "their product is 4"
      - "unrelated"
    answer: 0
    explain: "`(s−2)(m−2) = sm − 2s − 2m + 4 = 4 − (2s + 2m − sm)`. So `(s−2)(m−2) < 4` is exactly `0 < 2s + 2m − sm`, and the proof of `sub_mul_lt_four` goes through precisely that: `hcoeff_pos` then `hlt`."
  - q: "Which hypothesis makes the coefficient positive in the proof?"
    type: choice
    choices:
      - "`hE : 0 < E`, together with the right-hand side `2sm > 0`"
      - "`hs : 3 ≤ s`"
      - "`hEuler`"
      - "`hFace`"
    answer: 0
    explain: "From `E · c = 2sm` with `E > 0` and `2sm > 0`, you get `c > 0`. The Lean does it with `nlinarith [h, hEpos, hRHSpos]`. `Platonic.pos_edges_of_euler` is what supplies `0 < E` for a real polytope, so it is not an extra assumption in the end."
  - q: "`(s, m) = (3, 7)`. What is `(s − 2)(m − 2)`, and what does the identity give?"
    type: choice
    choices:
      - "`5`, and the coefficient `2·3 + 2·7 − 21 = −1`, so `E = −42`: impossible"
      - "`5`, and `E = 42`"
      - "`4`, and `E · 0 = 42`"
      - "`5`, and the pair is admissible"
    answer: 0
    explain: "`1 · 5 = 5 ≥ 4`, so the bound is violated. Solving anyway: `E · (−1) = 2·3·7 = 42` gives `E = −42`, contradicting `0 < E`. `{3,7}` is a hyperbolic tiling — infinitely many triangles, seven to a vertex."
  - q: "How many pairs with `s, m ≥ 3` satisfy `(s − 2)(m − 2) < 4`?"
    type: number
    answer: 5
    explain: "With `a = s−2 ≥ 1`, `b = m−2 ≥ 1` and `ab < 4`: `(1,1), (1,2), (1,3), (2,1), (3,1)`. Five. `schlafli_of_bounds` does this with `interval_cases a` after bounding `a, b ≤ 3`."
---

## Plain English

**Theorem.** For any [`RegularNumbers`](#/node/Platonic.RegularNumbers) `R`,

```lean
theorem sub_mul_lt_four (R : RegularNumbers) : (R.s - 2) * (R.m - 2) < 4
```

This single inequality is the whole classification. Everything before it is setting up; everything
after it is a finite case check.

### The derivation

Start with the three identities a `RegularNumbers` carries:

> `s·F = 2E`,  `m·V = 2E`,  `V − E + F = 2`.

Multiply the last by `s·m`:

> `sm·V − sm·E + sm·F = 2sm`.

Substitute: `sm·V = s·(mV) = s·2E = 2sE`, and `sm·F = m·(sF) = m·2E = 2mE`. So

> `2sE − sm·E + 2mE = 2sm`,  i.e.  `E·(2s + 2m − sm) = 2sm`.

That is `mul_euler_int`. The right-hand side is positive and `E > 0`, so the bracket must be
positive:

> `2s + 2m − sm > 0`.

And since `(s − 2)(m − 2) = 4 − (2s + 2m − sm)`, that is exactly

> `(s − 2)(m − 2) < 4`.

With `s, m ≥ 3` both factors are at least 1, so each factor is at most 3, and five cases survive:
[`schlafliPairs`](#/node/Platonic.schlafliPairs).

### In one breath

Multiply Euler's two by the number of sides per face times the number of faces per corner. Every
term turns into something you can rewrite using the two counting identities, and when the dust
settles you are left with one inequality: side-count minus two, times corner-count minus two, is
less than four. Both factors are whole numbers at least one. There are five ways to do that. Five
Platonic solids, and the proof fits on a postcard once you have Euler's formula — which is why
Euler's formula is the interesting half.

### How tight the bound is

| `(s−2)(m−2)` | what you get |
|---|---|
| `< 4` | a finite solid — five pairs |
| `= 4` | a tiling of the **flat plane**: `{4,4}`, `{3,6}`, `{6,3}` |
| `> 4` | a tiling of the **hyperbolic plane**: infinitely many pairs |

At exactly 4 the coefficient `2s + 2m − sm` is zero, so the identity reads `E · 0 = 2sm`, which no
finite `E` satisfies — the tiling has infinitely many faces. Above 4 the coefficient is negative
and `E` would have to be negative. The `schlafli` widget shows all three regimes.

The *geometric* reading of this trichotomy — spherical, Euclidean, hyperbolic — is classical and is
**not** in the Lean. What the Lean has is the inequality.

### Where it sits

- From [`RegularNumbers`](#/node/Platonic.RegularNumbers), via `mul_euler_int`.
- To [`schlafli_pair_mem`](#/node/Platonic.schlafli_pair_mem) via the private
  `schlafli_of_bounds`, and from there to
  [`results_five_platonic_solids`](#/node/Results.results_five_platonic_solids).
