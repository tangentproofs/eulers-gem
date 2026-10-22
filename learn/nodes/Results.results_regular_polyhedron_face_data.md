---
id: Results.results_regular_polyhedron_face_data
title: "Face data of a regular polyhedron — CONDITIONAL on the face-lattice facts"
summary: "CONDITIONAL. A regular (flag-transitive) polyhedron that satisfies the general face-lattice facts `FaceLatticeFacts` has the `(V, E, F)` and `{s, m}` of one of the five Platonic solids. Full uniqueness up to similarity is stated outside `Results` and rests on two unproved gaps."
review: draft
authors: ["Grok Bot (for @tangentstorm)"]
caveats:
  - "**CONDITIONAL.** `FaceLatticeFacts P` is a **hypothesis**. It collects facts true of every convex 3-polytope (flags exist, every edge lies in exactly two facets, every facet has and every vertex meets at least three edges), but the repository does **not** prove them in general. That missing proof is the gap `PlatonicGaps.GAP_faceLatticeFacts`."
  - "**This is not uniqueness up to similarity.** It pins down the *numbers*, not the *shape*. The step from numbers to shape is the second gap, `PlatonicGaps.GAP_rigidity`."
  - "The full classification `PlatonicGaps.regular_polyhedron_classification` (every regular polyhedron is similar to one of the five) and `regular_polyhedron_classification_unique` (exactly one) live in a separate library, `lean/PlatonicGaps.lean`, outside `Results`. `#print axioms` for them shows `sorryAx`. They are **not theorems of this repository yet**."
  - "`FaceLatticeFacts` is proved for the five constructed solids (`platonic_faceLatticeFacts`), so the hypothesis is not vacuous."
widgets:
  - type: schlafli
    title: "Why only five (s, m) survive"
quiz:
  - q: "Which of these is a hypothesis of `results_regular_polyhedron_face_data`?"
    type: choice
    choices:
      - "`FaceLatticeFacts P` — general face-lattice facts that are not proved in general here"
      - "`V − E + F = 2`"
      - "`(s, m) ∈ schlafliPairs`"
      - "that `P` is similar to a Platonic solid"
    answer: 0
    explain: "The signature is `(hP : IsRegularPolyhedron P) (hL : FaceLatticeFacts P)`. Euler is derived inside the proof from the Euler–Poincaré root; the Schläfli pair is the conclusion's content."
  - q: "Does this theorem say every regular polyhedron is similar to one of the five Platonic solids?"
    type: choice
    choices:
      - "no — it only says the face counts and type are one of five; similarity needs the unproved `GAP_rigidity`"
      - "yes"
      - "yes, unconditionally"
    answer: 0
    explain: "The conclusion is a disjunction of five `HasFaceData P V E F s m`. The similarity statement is `PlatonicGaps.regular_polyhedron_classification`, which uses both `GAP_faceLatticeFacts` and `GAP_rigidity` (`sorry`)."
  - q: "Why does flag-transitivity give a single `s` and a single `m`?"
    type: choice
    choices:
      - "a symmetry maps faces to faces of the same dimension and preserves inclusion, so it preserves 'edges in this facet' and 'edges at this vertex'; any facet (vertex) can be moved to any other"
      - "it is assumed"
      - "because `V − E + F = 2`"
    answer: 0
    explain: "`IsRegularPolyhedron.uniform`, using `ncard_sub_image` / `ncard_sup_image` (counts are invariant under a symmetry) and `vertex_in_flag` / `facet_in_flag` from `FaceLatticeFacts`."
  - q: "A regular polyhedron here has 12 facets. What is `V`?"
    type: number
    answer: 20
    explain: "Among the five tuples only the dodecahedron `(V, E, F, s, m) = (20, 30, 12, 5, 3)` has `F = 12`."
  - q: "How many `sorry`s does the full similarity classification depend on, and where are they?"
    type: choice
    choices:
      - "two — `GAP_faceLatticeFacts` and `GAP_rigidity`, both in the separate `PlatonicGaps` library, outside `EulersGem` and `Results`"
      - "none"
      - "one, inside `Results.lean`"
    answer: 0
    explain: "`lean/PlatonicGaps.lean` is its own `lean_lib`, not a default target and not imported by `Results`, so `scripts/audit-axioms.sh` (which fails on any `sorry` in `EulersGem/` or `Results.lean`) stays green."
---

## Plain English

```lean
theorem results_regular_polyhedron_face_data {P : Set EulersGem.R3}
    (hP : IsRegularPolyhedron P) (hL : FaceLatticeFacts P) :
    HasFaceData P 4 6 4 3 3 ∨ HasFaceData P 8 12 6 4 3 ∨ HasFaceData P 6 12 8 3 4 ∨
      HasFaceData P 20 30 12 5 3 ∨ HasFaceData P 12 30 20 3 5
```

Take a regular polyhedron — a 3-dimensional convex polytope in ℝ³ whose isometries can move any flag
(vertex ⊆ edge ⊆ facet) to any other. **Assume** in addition the face-lattice facts `FaceLatticeFacts P`.
Then its vertex, edge and facet counts and its type `{s, m}` are those of the tetrahedron, cube,
octahedron, dodecahedron or icosahedron.

### In one breath

If a solid looks the same from every corner-edge-face, then — granting some standard facts about
how faces of any solid fit together, which this repository has not yet proved — it has the numbers
of one of the five Platonic solids. Showing it has the *shape* of one is a further step that is
still missing.

## What this does and does not prove

**It does prove**, with no `sorry`, **given `FaceLatticeFacts P`**:

- **Regular ⇒ uniform type.** Symmetries permute faces of each dimension and preserve inclusion, so
  flag-transitivity makes the number of edges per facet and per vertex constant
  (`IsRegularPolyhedron.uniform`).
- **Uniform type ⇒ one of five tuples**, via the existing Euler chain: double counting, Euler from the
  root, `(s − 2)(m − 2) < 4` (`IsRegularPolyhedron.faceData`).
- Alongside, in `EulersGem`: first metric consequences of regularity (a centre fixed by every
  symmetry with all vertices equidistant, equal edge lengths: `RegularCentre.lean`) — these also
  assume `FaceLatticeFacts`. And, unconditionally, the five constructed solids are pairwise
  non-similar ([`results_platonic_solids_not_similar`](#/node/Results.results_platonic_solids_not_similar)).

**It does not prove — the two named gaps:**

1. **`GAP_faceLatticeFacts`**: every convex 3-polytope satisfies `FaceLatticeFacts`. Classical
   (Ziegler, *Lectures on Polytopes* §2.2; Grünbaum §3.1), not formalized. It mentions no regularity
   and no Platonic solid, so assuming it does not smuggle in the answer.
2. **`GAP_rigidity`**: two regular polyhedra with the same face data are similar. Classical, not
   formalized.

With both gaps, `PlatonicGaps.regular_polyhedron_classification` states the classical theorem —
every regular convex polyhedron is similar to one of the five — and
`regular_polyhedron_classification_unique` says to exactly one. Those depend on `sorryAx` and are
**conditional**.

### Where it sits

- Restates `IsRegularPolyhedron.faceData` (`EulersGem/RegularCombinatorics.lean`).
- Uses the Euler chain of [`results_five_platonic_solids`](#/node/Results.results_five_platonic_solids).
- The solids it names are built in
  [`results_five_platonic_solids_constructed`](#/node/Results.results_five_platonic_solids_constructed).
- [Trust](#/trust) has the one-row summary.
