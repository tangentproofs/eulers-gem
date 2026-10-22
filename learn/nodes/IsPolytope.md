---
id: IsPolytope
title: "IsPolytope: the convex hull of finitely many points"
summary: "`IsPolytope S` says there is a finite set `V` with `S = convexHull ℝ V`. This is the V-description, and it is the *only* geometric hypothesis the Euler theorems need besides the dimension."
review: draft
authors: ["claude (for @tangentstorm)"]
caveats:
  - "`IsPolytope ∅` is **true**: take `V = ∅`, since `convexHull ℝ ∅ = ∅`. So is `IsPolytope {x}`. The Euler theorems rule these out with the dimension hypothesis (`affDim p = finrank E` with `1 ≤ finrank E`), not with `IsPolytope`."
  - "The witness `V` is not required to be the vertex set, or minimal, or even to consist of extreme points. Any finite set whose hull is `S` will do."
  - "Convexity of `S` is not a field of the definition — it follows, since a convex hull is convex. There is no *non*-convex `IsPolytope`, and that is why Euler's formula can fail for the polyhedra it excludes."
widgets:
  - type: polyhedron
    title: "Seven convex hulls, and one thing that is not one"
    config:
      preset: cube
      show: [counts, incidence]
quiz:
  - q: "Write out the definition of `IsPolytope S`."
    type: choice
    choices:
      - "`∃ H : Set (Hyperplane E), H.Finite ∧ S = ⋂ h ∈ H, closedHalfspace h.1 h.2`"
      - "`∃ V : Set E, V.Finite ∧ S = convexHull ℝ V`"
      - "`Convex ℝ S ∧ IsCompact S`"
      - "`∃ V : Finset E, S = ↑V`"
    answer: 1
    explain: "`def IsPolytope (S : Set E) : Prop := ∃ V : Set E, V.Finite ∧ S = convexHull ℝ V` (Polytope.lean). The first choice is [IsPolyhedron](#/node/IsPolyhedron), the H-description — a different definition, linked to this one by the *theorem* [IsPolytope.isPolyhedron](#/node/IsPolytope.isPolyhedron)."
  - q: "Is `IsPolytope` true for the empty set?"
    type: choice
    choices: ["yes, with `V = ∅`", "no, the definition requires `V.Nonempty`", "only in dimension 0"]
    answer: 0
    explain: "`V.Finite` holds for `∅` and `convexHull ℝ ∅ = ∅`. The definition says nothing about nonemptiness. `results_euler_characteristic` excludes the empty polytope through `affDim p = finrank ℝ E` together with `1 ≤ finrank ℝ E`, since `affDim ∅ = -1`."
  - q: "Is the toroidal \"picture frame\" solid — a square slab with a square hole — an `IsPolytope`?"
    type: choice
    choices:
      - "yes: it has finitely many vertices"
      - "no: it is not convex, and a convex hull always is"
      - "yes, but only in dimension 3"
      - "the definition does not decide"
    answer: 1
    explain: "A convex hull is convex, so every `IsPolytope` is convex. The picture frame is not — the segment across its hole leaves the solid — so no finite `V` has it as a hull. This is precisely why Euler's formula can fail there (`V − E + F = 0` for that solid) without contradicting [results_euler_polyhedron](#/node/Results.results_euler_polyhedron)."
  - q: "A unit disc in ℝ². Convex, compact, bounded. Is it an `IsPolytope`?"
    type: choice
    choices: ["yes", "no", "only if you allow a countable `V`"]
    answer: 1
    explain: "No: the convex hull of a finite set has finitely many extreme points, and every boundary point of a disc is extreme. So the Euler theorems say nothing about discs or balls — `IsPolytope` is a genuine restriction, not a formality."
  - q: "Must the witness `V` be exactly the set of vertices of `S`?"
    type: choice
    choices:
      - "yes, the definition forces it"
      - "no — any finite set with the right hull works, including one with interior points in it"
      - "yes, up to permutation"
    answer: 1
    explain: "The definition is a bare `∃`. Adding the centre of a cube to `V` does not change `convexHull ℝ V`, so that enlarged set is also a witness. Proofs that need the extreme points recover them separately — for instance `PolytopeFaces.face_eq_convexHull_inter`, which is how `facesOfDim_finite_of_isPolytope` gets finiteness."
---

## Plain English

`IsPolytope S` means: **`S` is what you get by taking finitely many points and filling in
everything between them.**

```lean
def IsPolytope (S : Set E) : Prop :=
  ∃ V : Set E, V.Finite ∧ S = convexHull ℝ V
```

Stretch a rubber sheet around four points in space and you get a tetrahedron. Around eight
corners, a cube. Around a hundred points scattered in a ball, a many-faced lump. All of those are
polytopes. The ball itself is not, and neither is anything with a dent in it.

This is called the **V-description** (V for vertices): you say what a polytope *is* by listing
points. The other way to describe one is the **H-description** — see
[IsPolyhedron](#/node/IsPolyhedron) — where you list inequalities and take everything satisfying
all of them. Both describe the same shapes, but that is a theorem
([`IsPolytope.isPolyhedron`](#/node/IsPolytope.isPolyhedron)), and in this repository the theorem
is proved rather than assumed. That is the point of Kim Morrison's contribution: before it, the
Euler results had to be handed an H-description as an extra hypothesis.

### In one breath

Pick a handful of pins and stick them in a board. Loop a rubber band around the lot and let go.
The shape it settles into — the pins, the taut band, and everything inside — is a polytope. Do
the same with pins in three dimensions and a shrink-wrap instead of a rubber band, and you get a
solid one. Finitely many pins is the whole condition. It is a surprisingly strong one: it rules
out balls, and it rules out any solid with a dent or a hole, because wrapping it would bridge the
gap.

### What it does and does not give you

It gives you, free:

- convexity, since hulls are convex;
- compactness (a hull of a finite set is compact), though the Lean does not need to say so;
- the H-description, by [`IsPolytope.isPolyhedron`](#/node/IsPolytope.isPolyhedron);
- finiteness of the set of faces of each dimension, by
  [`facesOfDim_finite_of_isPolytope`](#/node/facesOfDim_finite_of_isPolytope) — which matters more
  than it sounds, because `Set.ncard` is `0` on an infinite set and would silently give wrong
  counts.

It does not give you:

- nonemptiness or any dimension at all. `IsPolytope ∅` and `IsPolytope {x}` are both true.
- a canonical vertex set. The `V` is just some witness.

### Where it sits

`IsPolytope` is the hypothesis of every Euler result here:

- [`results_euler_characteristic`](#/node/Results.results_euler_characteristic): `IsPolytope p`
  plus `affDim p = finrank ℝ E` plus `1 ≤ finrank ℝ E` gives
  [`faceEulerSum p (finrank ℝ E) = 1`](#/node/faceEulerSum).
- [`results_euler_polyhedron`](#/node/Results.results_euler_polyhedron): `IsPolytope p` plus
  `affDim p = 3` gives `V − E + F = 2`. Two hypotheses, and that is all.
- [`results_five_platonic_solids`](#/node/Results.results_five_platonic_solids) carries it into the
  Schläfli argument.
