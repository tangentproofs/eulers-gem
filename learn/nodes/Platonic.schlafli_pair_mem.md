---
id: Platonic.schlafli_pair_mem
title: "Every regular pair is one of the five"
summary: "`(R.s, R.m) ∈ schlafliPairs` for any `RegularNumbers R`. The inequality plus a finite case check — this is the classification, stated over numbers."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "It quantifies over [RegularNumbers](#/node/Platonic.RegularNumbers), a numeric structure. So the theorem is: *any five numbers with those three identities have `(s, m)` among the five pairs*. Turning that into a statement about polytopes is [regular_polytope_counts](#/node/Platonic.regular_polytope_counts)'s job, and it does it by proving the three identities for a real polytope."
  - "The docstring calls it \"**Number of Platonic solids (combinatorial)**\". The parenthesis is doing a lot of work and should not be dropped."
widgets:
  - type: schlafli
    title: "The five survivors, and what fails elsewhere"
quiz:
  - q: "What does `schlafli_pair_mem` take as input?"
    type: choice
    choices:
      - "a `RegularNumbers` — five numbers plus three identities"
      - "a polytope `p` with `affDim p = 3`"
      - "two numbers `s` and `m`"
      - "a `Finset (ℕ × ℕ)`"
    answer: 0
    explain: "`theorem schlafli_pair_mem (R : RegularNumbers) : (R.s, R.m) ∈ schlafliPairs := schlafli_of_bounds R.hs R.hm (sub_mul_lt_four R)`. The input is the numeric structure; no geometry appears."
  - q: "What is its one-line proof?"
    type: choice
    choices:
      - "`schlafli_of_bounds R.hs R.hm (sub_mul_lt_four R)`"
      - "`by decide`"
      - "an induction on `s`"
      - "`by omega`"
    answer: 0
    explain: "The private lemma `schlafli_of_bounds {s m : ℕ} (hs : 3 ≤ s) (hm : 3 ≤ m) (hlt : (s - 2) * (m - 2) < 4) : (s, m) ∈ schlafliPairs` does the case analysis, and [sub_mul_lt_four](#/node/Platonic.sub_mul_lt_four) supplies the inequality."
  - q: "How does `schlafli_of_bounds` bound the cases?"
    type: choice
    choices:
      - "sets `a = s − 2`, `b = m − 2`, proves `1 ≤ a, b ≤ 3` from `ab < 4`, then `interval_cases a`"
      - "`decide` over all pairs"
      - "a strong induction"
      - "by contradiction from Euler alone"
    answer: 0
    explain: "If `a ≥ 4` then `ab ≥ 4·1 = 4`, contradiction; same for `b`. Then `interval_cases a` splits into `a = 1, 2, 3` and `interval_cases b` finishes, with `simp [schlafliPairs, …]` discharging each membership."
  - q: "Does this theorem say anything about whether a solid with a given `(s, m)` exists?"
    type: choice
    choices:
      - "no — it is a one-way exclusion: *if* you have such numbers, they are one of the five"
      - "yes, it constructs one for each pair"
      - "yes, it rules out all but five solids"
    answer: 0
    explain: "A pure necessity statement. `exists_regularNumbers_of_mem_schlafli` gives the converse *for records*, and the geometric existence of three of the solids is proved in `GeometricPlatonic.lean`, `Octahedron.lean` and `Cube.lean` — not here, and not for the other two at all."
---

## Plain English

```lean
theorem schlafli_pair_mem (R : RegularNumbers) : (R.s, R.m) ∈ schlafliPairs
```

**Any five numbers satisfying the three identities have `(s, m)` among the five pairs.**

The proof is one line: [`sub_mul_lt_four`](#/node/Platonic.sub_mul_lt_four) gives
`(s − 2)(m − 2) < 4`, and a finite case analysis over `s − 2, m − 2 ∈ {1, 2, 3}` does the rest.

### In one breath

If the number of sides per face minus two, times the number of faces per corner minus two, must be
less than four, and both are whole numbers at least one, then there are five possibilities. Listing
them is the theorem. The work was getting the inequality.

### What it is and is not

It is a **necessity** statement: nothing outside the list can happen. It says nothing about
existence; for that you would need to build a polytope for each pair, and this repository builds
three of the five, in modules outside `Results`.

And it is a statement about [`RegularNumbers`](#/node/Platonic.RegularNumbers), which is a bundle
of five numbers with certificates — not a polytope. The bridge to geometry is
[`regular_polytope_counts`](#/node/Platonic.regular_polytope_counts), which *proves* the two
double-counting identities for a real convex 3-polytope and takes `V − E + F = 2` from
[the Euler relation](#/node/Results.results_euler_relation_dimension_three). Then
[`results_five_platonic_solids`](#/node/Results.results_five_platonic_solids) assembles the
`RegularNumbers` and applies this theorem.

Keeping the two apart is what lets you see where the assumptions are. Everything numeric is
airtight; the geometry carries one remaining hypothesis (the diamond property).

### Where it sits

- From [`sub_mul_lt_four`](#/node/Platonic.sub_mul_lt_four) and
  [`RegularNumbers`](#/node/Platonic.RegularNumbers).
- To [`schlafliPairs`](#/node/Platonic.schlafliPairs) membership, and from there to part 1 of
  [`results_five_platonic_solids`](#/node/Results.results_five_platonic_solids).
