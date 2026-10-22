---
id: IsRegularPolyhedron
title: "IsRegularPolyhedron: a 3-polytope whose symmetries reach every flag"
summary: "`IsPolytope P ∧ affDim P = 3 ∧` for any two flags (vertex ⊆ edge ⊆ facet) some isometry of ℝ³ maps `P` onto itself and the first flag onto the second."
review: draft
authors: ["Grok Bot (for @tangentstorm)"]
caveats:
  - "This is the modern flag-transitive definition (Coxeter, McMullen–Schulte). Euclid's \"congruent regular faces, the same number at each vertex\" is classically equivalent for convex polyhedra; that equivalence is not formalized here."
  - "Flag-transitivity is a `∀` over flags, so a set with no flags would satisfy it vacuously. Non-vacuity comes from face counts (`HasFaceData`) or from `FaceLatticeFacts.exists_flag`."
quiz:
  - q: "Which maps count as symmetries in `IsRegularPolyhedron`?"
    type: choice
    choices:
      - "all isometries of ℝ³ (`R3 ≃ᵃⁱ[ℝ] R3`), translations and reflections included, that map `P` onto itself"
      - "rotations about the origin only"
      - "any affine bijection"
    answer: 0
    explain: "The witness is `g : R3 ≃ᵃⁱ[ℝ] R3` with `g '' P = P`."
  - q: "Does the definition mention edge lengths or angles?"
    type: choice
    choices: ["no — the metric shape is a consequence", "yes, all edges equal", "yes, all angles equal"]
    answer: 0
    explain: "Only flags and isometries. Equal edge lengths are *proved* from it (`IsRegularPolyhedron.edges_congruent`, given `FaceLatticeFacts`)."
  - q: "What is a flag, in `IsFlag P v e f`?"
    type: choice
    choices:
      - "faces `v ⊆ e ⊆ f` of `P` of affine dimensions 0, 1, 2"
      - "three vertices of `P`"
      - "a vertex and the plane of a facet"
    answer: 0
    explain: "`IsFlag P v e f := v ∈ facesOfDim P 0 ∧ e ∈ facesOfDim P 1 ∧ f ∈ facesOfDim P 2 ∧ v ⊆ e ∧ e ⊆ f`."
---

## Plain English

```lean
def IsRegularPolyhedron (P : Set R3) : Prop :=
  IsPolytope P ∧ affDim P = 3 ∧
    ∀ v e f v' e' f', IsFlag P v e f → IsFlag P v' e' f' →
      ∃ g : R3 ≃ᵃⁱ[ℝ] R3, g '' P = P ∧ g '' v = v' ∧ g '' e = e' ∧ g '' f = f'
```

`P` is a convex polytope in ℝ³ ([`IsPolytope`](#/node/IsPolytope)) of full dimension, and wherever you
stand on it — at a corner, on an edge through that corner, on a face containing that edge — some rigid
motion of space carries `P` onto itself and your position onto any other such position.

### In one breath

A solid is regular if it looks exactly the same from every corner-edge-face.
