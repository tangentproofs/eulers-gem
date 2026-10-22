---
id: Picks.LatticeTriangle.latticeDet
title: "latticeDet: twice the signed area of a lattice triangle"
summary: "`latticeDet a b c = (b₁−a₁)(c₂−a₂) − (b₂−a₂)(c₁−a₁)`. Positive when `c` is left of the ray `a → b`, zero when the three are collinear, negative when right."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "It is an `ℤ`, so it is exact — no rounding, no sign ambiguity. All the convexity predicates in `LatticeFan.lean` are integer sign tests on it, which is why the `pick` widget can decide them exactly rather than approximately."
  - "Swapping any two of the three arguments negates it. So the convexity conditions are genuinely orientation-sensitive, and a polygon listed clockwise fails them."
  - "`latticeDet_translate` says it depends only on the differences: `latticeDet a b c = latticeDet (0,0) (b − a) (c − a)`."
widgets:
  - type: pick
    title: "The fan determinants, one per corner-fan triangle"
    config:
      preset: pentagon
      show: [counts, fan]
quiz:
  - q: "State the definition."
    type: choice
    choices:
      - "`(b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)`"
      - "`a.1 * b.2 - a.2 * b.1`"
      - "`|b.1 - a.1| * |c.2 - a.2|`"
      - "`(b.1 - a.1) * (c.1 - a.1) + (b.2 - a.2) * (c.2 - a.2)`"
    answer: 0
    explain: "`def latticeDet (a b c : ℤ × ℤ) : ℤ := (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)` (LatticeTriangle.lean). The second choice is `LatticeFan.cross`, a two-argument relative; the fourth is a dot product."
  - q: "`latticeDet (0,0) (1,0) (0,1)`?"
    type: number
    answer: 1
    explain: "`(1−0)(1−0) − (0−0)(0−0) = 1`. The smallest positively oriented lattice triangle, with shoelace `1/2` — and `Triangle.IsDetPrimitive` holds for it."
  - q: "What does `latticeDet a b c = 0` mean?"
    type: choice
    choices:
      - "`a`, `b`, `c` are collinear"
      - "two of them are equal"
      - "the triangle has area 1"
      - "`c` is the midpoint of `a` and `b`"
    answer: 0
    explain: "The determinant of the two edge vectors vanishes exactly when they are parallel, i.e. the three points lie on a line (including the degenerate cases where two coincide). This is why [LocalCCWTurns](#/node/Picks.LatticeFan.StrictlyConvexCCW) is a strict `0 <`: a collinear listed vertex gives zero."
  - q: "What is the relation to `triangleShoelace`?"
    type: choice
    choices:
      - "`triangleShoelace a b c = |latticeDet a b c| / 2`"
      - "`triangleShoelace a b c = latticeDet a b c`"
      - "`triangleShoelace a b c = latticeDet a b c / 2`, keeping the sign"
      - "no relation"
    answer: 0
    explain: "`def triangleShoelace (a b c : ℤ × ℤ) : ℚ := (Int.natAbs (latticeDet a b c) : ℚ) / 2`. Hence `shoelace_eq_half_of_isDetPrimitive`: `|det| = 1` gives area exactly `1/2`."
  - q: "Swap `b` and `c`. What happens to `latticeDet a b c`?"
    type: choice
    choices: ["it negates", "it is unchanged", "it doubles", "it becomes zero"]
    answer: 0
    explain: "A determinant is alternating in its rows. This is exactly why orientation matters to [ConvexCCW](#/node/Picks.LatticeFan.StrictlyConvexCCW) and `FanDetsPos`: a clockwise vertex list makes every sign come out wrong."
---

## Plain English

```lean
def latticeDet (a b c : ℤ × ℤ) : ℤ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)
```

The determinant of the two edge vectors `b − a` and `c − a`. Classically, **twice the signed area**
of the triangle `abc`, and the sign tells you the orientation:

| sign | meaning |
|---|---|
| `> 0` | `c` is strictly **left** of the ray from `a` to `b`; the triangle is counterclockwise |
| `= 0` | the three points are **collinear** |
| `< 0` | `c` is strictly **right**; the triangle is clockwise |

Everything in the Pick lane that concerns shape, orientation or area is an integer sign test on
this.

### In one breath

Stand at one corner and look towards a second. Is the third corner to your left, straight ahead, or
to your right? One multiplication-and-subtract answers it, and the size of the answer is twice the
area of the triangle. Because everything is a whole number, the answer is exact — there is no
"nearly collinear".

### Where it shows up

| | uses `latticeDet` to say |
|---|---|
| [`ConvexCCW`](#/node/Picks.LatticeFan.StrictlyConvexCCW) | every vertex is weakly left of every directed edge |
| `LocalCCWTurns` | each turn is strictly left (so `≠ 0`: no collinear triple) |
| `fanDet i` | the signed area of the `i`-th corner-fan triangle |
| `FanDetsPos` | all the fan triangles are positively oriented |
| `Triangle.IsDetPrimitive` | `|det| = 1`, so the triangle has area exactly `1/2` |
| `triangleShoelace` | `|det|/2` |

And `LatticeTriangle.lean`'s harder results are about it too: `|det| = 1` implies the closed triangle
contains no lattice point other than its three vertices (by Cramer's rule on the barycentric
coordinates), and `LatticeTriangleEmpty.lean` proves the converse for nondegenerate triangles. That
pair is the number-theoretic core of Pick's theorem: **primitive triangles are the atoms**.

### Where it sits

Defined in `LatticeTriangle.lean`. Used throughout `LatticeFan.lean`, `PickFromEuler.lean`,
`LatticeArea.lean`, and in the `pick` widget's hypothesis checks.
