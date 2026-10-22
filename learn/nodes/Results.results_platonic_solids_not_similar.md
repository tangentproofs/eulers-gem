---
id: Results.results_platonic_solids_not_similar
title: "The five constructed solids are pairwise non-similar"
summary: "For `i ≠ j` in `Fin 5`, `platonicSolid i` is not similar to `platonicSolid j`: a similarity preserves the number of vertices, and the five have 4, 8, 6, 20 and 12."
review: draft
authors: ["Grok Bot (for @tangentstorm)"]
caveats:
  - "This is about the five constructed sets only. It says nothing about an arbitrary regular polyhedron; that is the conditional [`results_regular_polyhedron_face_data`](#/node/Results.results_regular_polyhedron_face_data)."
  - "`Similar P Q` is `∃ g r, 0 < r ∧ Q = (r • ·) '' (g '' P)` with `g` an isometry of ℝ³. The repository does not prove that `Similar` is an equivalence relation; this theorem covers both orders of every pair anyway."
quiz:
  - q: "What invariant does the proof use?"
    type: choice
    choices:
      - "the number of vertices (faces of affine dimension 0), preserved by any similarity"
      - "the edge length"
      - "the volume"
    answer: 0
    explain: "`Similar.ncard_facesOfDim`: an injective affine map carries faces to faces bijectively, dimension by dimension (`faces_image_affine`). Vertex counts 4, 8, 6, 20, 12 are distinct."
  - q: "Index `3` of `platonicSolid` is which solid?"
    type: choice
    choices: ["dodecahedron", "icosahedron", "octahedron", "cube"]
    answer: 0
    explain: "`platonicSolid := ![tetrahedron, cube, octahedron, dodecahedron, icosahedron]`, indexed from 0."
  - q: "Does this theorem prove there are exactly five Platonic solids up to similarity?"
    type: choice
    choices:
      - "no — it shows the five built ones are distinct; that there are no others is the conditional classification"
      - "yes"
    answer: 0
    explain: "Distinctness is one of the three parts (existence, distinctness, completeness). Completeness up to similarity depends on two unproved gaps in `PlatonicGaps.lean`."
---

## Plain English

```lean
theorem results_platonic_solids_not_similar {i j : Fin 5} (hij : i ≠ j) :
    ¬ Similar (platonicSolid i) (platonicSolid j)
```

No two of the five constructed solids are similar: you cannot rotate, reflect, translate and
rescale one into another. A similarity carries vertices to vertices one-to-one, and the five solids
have 4, 8, 6, 20 and 12 vertices.

### In one breath

The five solids really are five different shapes: they do not even have the same number of corners.

## What this does and does not prove

**It does prove** that the five sets of
[`results_five_platonic_solids_constructed`](#/node/Results.results_five_platonic_solids_constructed)
are pairwise non-similar, in both orders.

**It does not prove** that every regular polyhedron is similar to one of them. That is
conditional: see [`results_regular_polyhedron_face_data`](#/node/Results.results_regular_polyhedron_face_data).

### Where it sits

- Restates `platonic_not_similar` (`EulersGem/RegularCombinatorics.lean`).
