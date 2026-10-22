---
id: FaceLatticeFacts
title: "FaceLatticeFacts: face facts of 3-polytopes — ASSUMED, not proved in general"
summary: "Seven facts every convex 3-polytope has (flags exist, each edge lies in exactly two facets, at least three edges per facet and per vertex, …). Used as a HYPOTHESIS; the general proof is the open gap `PlatonicGaps.GAP_faceLatticeFacts`."
review: draft
authors: ["Grok Bot (for @tangentstorm)"]
caveats:
  - "**Not proved for a general polytope.** It is a hypothesis of `results_regular_polyhedron_face_data` and of the metric results in `RegularCentre.lean`. The general proof is the `sorry` `GAP_faceLatticeFacts` in the quarantined `lean/PlatonicGaps.lean`."
  - "It *is* proved for the five constructed solids (`platonic_faceLatticeFacts`), so assuming it is not vacuous."
  - "It mentions no symmetry, no metric and no Platonic solid, so assuming it does not smuggle in the classification."
quiz:
  - q: "Is `FaceLatticeFacts P` proved for every convex 3-polytope in this repository?"
    type: choice
    choices:
      - "no — only for the five constructed solids; the general case is the gap `GAP_faceLatticeFacts`"
      - "yes"
      - "it is false in general"
    answer: 0
    explain: "Classically true (Ziegler §2.2, Grünbaum §3.1), not formalized. `FaceLatticeFacts.of_faceData` derives it from computed face data, which is how the five solids get it."
  - q: "Which is a field of `FaceLatticeFacts`?"
    type: choice
    choices:
      - "`edge_two_facets`: every edge lies in exactly two facets"
      - "all edges have equal length"
      - "`(s, m) ∈ schlafliPairs`"
    answer: 0
    explain: "The fields: `exists_flag`, `vertex_in_flag`, `edge_in_facet`, `facet_in_flag`, `edge_two_facets`, `facet_three_edges`, `vertex_three_edges`."
  - q: "What is the least number of edges at a vertex that `vertex_three_edges` demands?"
    type: number
    answer: 3
    explain: "`3 ≤ {e ∈ facesOfDim P 1 | v ⊆ e}.ncard` — in a 3-polytope every vertex has degree at least 3."
---

## Plain English

A structure of seven propositions about the faces of `P`: there is a flag; every vertex and every
facet lies in a flag; every edge lies in a facet, and in exactly two; every facet has at least three
edges and every vertex lies on at least three. All of these are true of every convex polytope of
dimension 3, but this repository has not yet proved them in that generality, so the results that
need them take `FaceLatticeFacts P` as an explicit hypothesis.

### In one breath

The basic bookkeeping of how corners, edges and faces of a solid fit together — taken on trust here,
and labelled as such.
