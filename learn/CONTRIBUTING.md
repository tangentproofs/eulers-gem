# Contributing explainers (`learn/`)

The app in `learn/` **informalizes** the Lean proof in `lean/`: for each declaration it shows the
formal statement, a plain-English explanation, an interactive illustration and a quiz with an
answer key. A reader can tick "I understand" on a node at any time;
the quiz is optional. The node shows one of three greens: lightest for "I understand" only, middle for
quiz passed only, darkest for both (the shared logic is `assets/progress.js`, identical in every
tangentproofs informalization site). A node counts as
*understood* once the reader has also understood every project declaration its statement
mentions.

It is published at `/learn/` on the Pages site, next to the browsable Lean source under
`/docs/` and the overview pages in `site/`.

**The Lean is the ground truth.** An explainer is correct only if it matches the statement
exactly as written in `lean/Results.lean` or `lean/EulersGem/*.lean`: its hypotheses, the order
of its quantifiers, `ℕ` vs `ℤ` vs `ℚ` vs `ℝ`, what is `∃` and what is `∀`, which side of an
implication a count sits on. Do not import claims from Richeson's *Euler's Gem*, from Paulson's
AFP entry, or from the README that the Lean does not make.

Humans and AI agents follow the same process.

## The honesty rules

This repository has a standing rule that a classical theorem may be *named* only when the Lean
statement really is that claim. These are the places it bites. Read the whole statement,
hypotheses included, before you write a word about it, and when in doubt **under-claim and add
a caveat**.

- **`results_euler_characteristic`, `results_euler_relation_dimension_three` and
  `results_euler_polyhedron` are the real thing** — Euler–Poincaré and Euler's polyhedron
  formula for *convex* polytopes, with `V`, `E`, `F` the cardinalities of the geometric face
  sets. Say so plainly. Also say what "convex" rules out: the toroidal picture frame has
  `V − E + F = 0`, and no theorem here covers graphs on a sphere or arbitrary surfaces.
- **`results_five_platonic_solids` is not "there are exactly five Platonic solids".** Part 1 is
  the Schläfli-pair classification of *combinatorially* regular convex 3-polytopes, and it takes
  the diamond property (every edge in exactly two 2-faces) as a hypothesis. Parts 2–6 are the
  `(V,E,F,s,m)` of five `Platonic.RegularNumbers` records: numbers, not solids. No metric
  regularity in that statement, no uniqueness up to similarity.
- **`results_five_platonic_solids_constructed` is existence**: all five solids, as convex hulls
  with `ℤ[φ]` coordinates, proved flag-transitive (`IsRegularPolyhedron`) with their face data.
  "Regular" means flag-transitive; its equivalence with Euclid's definition is not formalized.
- **`results_regular_polyhedron_face_data` is CONDITIONAL** on `FaceLatticeFacts`, a hypothesis
  not proved in general, and gives face data, not similarity. The similarity classification lives
  in `lean/PlatonicGaps.lean` with two `sorry` gaps (`GAP_faceLatticeFacts`, `GAP_rigidity`);
  never describe it as proved. (Separately, in modules but not in `Results`, the tetrahedron, octahedron and cube
  *are* built: `GeometricPlatonic.lean`, `Octahedron.lean`, `Cube.lean`, `MetricRegular.lean`.)
- **`results_picks_theorem` is Pick's theorem for strictly convex lattice polygons, with one
  remaining hypothesis.** It is stated for any `Finset S` whose coercion equals
  `P.interiorLatticePoints`, and the existence of such an `S` — finiteness of the interior
  lattice points — is not proved in this repository. Say that. It says nothing about non-convex
  simple polygons, because `interiorLatticePoints` is defined through the convex hull.
- **`results_pick_count_of_euler` is pure arithmetic.** Its `heuler : V − E + F = 2` is a free
  hypothesis on bare numbers, as are `V = I + B`, `F = T + 1`, `2E = 3T + B` and `A = T/2`. It
  proves nothing about polygons by itself.
- **`results_fan_pick_of_euler`'s statement is `(n − 2)/2 = n/2 − 1` for `n ≥ 3`**, and
  **`results_disk_pick_of_euler`'s statement** concludes `A = I + B/2 − 1` from
  `A = (2I + B − 2)/2`. For these two and the one above, say plainly what the statement says,
  and *separately* what the proof route shows. Do not describe the statement as proving anything
  about fans or disks.
- **Definitions that are easy to misread.** `affDim ∅ = -1`, so the empty face never lands among
  the dimension-0 faces, even though `IsFaceOf p ∅` is true. `IsFaceOf p f` is `IsExtreme` plus
  convexity, and includes both `∅` and `p`. `faceEulerSum p n = ∑_{d=0}^{n} (-1)^d · #{faces of
  affDim d}` — the body is in, the empty face is out. `Set.ncard` is `0` on an infinite set,
  which is why `facesOfDim_finite_of_isPolytope` has to exist (it does, and it is proved).
  `IsPolytope` is the V-description; the H-description is **proved** from it by
  `IsPolytope.isPolyhedron`, not assumed. `LatticePolygon` asserts only
  `3 ≤ vertices.length` — not simplicity, not convexity, not distinctness.
- **Do not claim axiom results.** `lean/scripts/audit-axioms.sh` is the authority, and its output
  goes on the Trust page in place of the `<!-- AXIOMS -->` marker in `learn/assets/app.js`. Do
  not write "depends only on the three standard axioms" into a node unless you ran it.

Nothing on this site is evidence for any theorem. See [`#/trust`](https://tangentproofs.github.io/eulers-gem/learn/#/trust)
for the honest accounting, and keep that page the strictest thing in the repository.

## What to work on

- `learn/dist/data/needs-explainer.json` (published as `data/needs-explainer.json`) lists every
  declaration reachable from a `Results` theorem that has no explainer yet, closest to a theorem
  first, with its *meaning dependencies*.
- Prefer nodes whose `meaningDeps` are already explained: a reader cannot mark a node understood
  until everything it mentions is explained and understood. `tools/build_site.mjs` warns about
  each unexplained meaning-dependency.
- Each stub page on the site has a ready-to-paste **agent prompt** with the statement, the source
  link and the dependencies.
- The spine, in reading order, is in `lean/UNIFIED_SPINE.md`: the definitions
  (`IsPolytope`, `IsPolyhedron`, `IsFaceOf`, `affDim`, `faceEulerSum`), the Euler–Poincaré root
  (`Euler_Poincare_of_isPolytope`, `IsPolytope.isPolyhedron`,
  `facesOfDim_finite_of_isPolytope`), the dimension-3 reading, then every `Results.*` theorem,
  then the Platonic lane and the Pick lane.

## Add or patch a node

One file per declaration: `learn/nodes/<id>.md`, where `<id>` is the declaration name without the
`EulersGem.` prefix — `IsPolytope.md`, `Platonic.schlafliPairs.md`,
`Picks.LatticeFan.StrictlyConvexCCW.md`, `Results.results_euler_polyhedron.md`. Look ids up in
`learn/data/decls.json`.

```markdown
---
id: faceEulerSum                      # = file name, must exist in data/decls.json
title: "The alternating sum of the face counts"     # ≤ 80 chars
summary: "One sentence. Markdown allowed; Lean in `backticks`."
review: draft                         # 'human-reviewed' only after a person checked it against the Lean
authors: ["claude (for @tangentstorm)"]   # agents: name the agent and the human who asked
caveats:                              # use it whenever the English is looser than the Lean
  - "Where the explanation simplifies, or what you are unsure of."
widgets:                              # optional; see the table below
  - type: face-lattice
    title: "f₀ … fₙ for the simplex and the cube"
    config: { n: 3 }
quiz:                                 # 3–6 questions; ALL must be answered correctly to pass
  - q: "Which `d` contributes the body of a 3-dimensional polytope?"
    type: number                      # choice | number | text
    answer: 3                         # choice: 0-based index · number: a number · text: accepted strings
    explain: "Why, pointing at the Lean. Shown after the reader answers."
---

## Plain English

The explanation. Markdown, tables and inline HTML are fine. Link to other nodes as
[faceEulerSum](#/node/faceEulerSum).

### In one breath

A paragraph with no notation in it at all, for a reader who has not met the definitions.
```

The schema is `learn/schema/node.schema.json`. `learn/tools/build_site.mjs` also checks that the
`id` matches the file name and is a real declaration, that every `choice` answer is a valid index
and `number` answers are numbers and `text` answers are lists, and that the body has a
`## Plain English` heading. It warns when a meaning-dependency has no explainer.

**Every node for a `Results.*` theorem must contain a section headed
`## What this does and does not prove`.** That is where the honesty rules above get spelled out
for that theorem.

### Writing good quiz questions

A quiz exists to show the reader understands the **formal statement**, not the surrounding story.
Good questions:

- test the hypotheses — what is assumed, what is concluded, which hypothesis the result would be
  false without;
- test quantifier order and the direction of an implication;
- test the edge cases the definitions decide (`affDim ∅`, the empty face, the body as a face of
  itself, `Set.ncard` of an infinite set, a polygon with a repeated vertex);
- compute a small instance (`V − E + F` of a given solid, `B` of a given lattice polygon,
  `f₂` of the 5-cube, `E` for `{5,3}`);
- use a choice question for the common misreading — "Euler's formula holds for every polyhedron",
  "the Lean proves there are five Platonic solids", "`results_pick_count_of_euler` proves Pick's
  theorem", "`faceEulerSum` counts the empty face".

Every `explain` should point at the Lean that makes the answer right.

## Widgets

Widgets are how a reader gets hands-on with a definition. They run in the browser with no
external dependency beyond the Cytoscape that `index.html` already loads for the graph, and
**every demonstration is an illustration**: each prints a line saying so, via `illustration()`
from `assets/dom.js`. (`outline` and `walkthrough` are the exceptions — they demonstrate nothing,
they lay out the proof's own steps with links.) A widget is never evidence. Where a demo can only
check finitely much — one polygon, `n ≤ 6`, a scan over a bounding box — say so under `caveats`.

| type | what it shows | config keys |
|---|---|---|
| `polyhedron` | a solid you can drag and tap: `V`, `E`, `F`, `V − E + F`, the face sizes and vertex degrees, whether every edge lies in two faces, the Schläfli pair, and whether `IsPolytope` holds at all; optionally a "cut a corner" button that truncates a vertex and leaves `V − E + F` alone | `preset`, `presets` (which to offer), `mode`: `solid` (default) or `wireframe`, `show`: any of `counts`, `incidence`, `truncate` |
| `face-lattice` | `f₀ … fₙ` for the n-simplex and the n-cube, exactly (`C(n+1,d+1)` and `2^(n−d)·C(n,d)`), the alternating sum `= 1`, and what dropping the body's term leaves | `family`: `simplex`, `cube` or both (default), `n` (0–6) |
| `schlafli` | the grid of `(s−2)(m−2)` for `s, m` in a window, the five cells that survive, and for one cell the solve `E·(2s+2m−sm) = 2sm` with `V`, `F`, plus whether the Lean builds that solid | `lo` (default 3), `hi` (default 8) |
| `pick` | a lattice grid you tap to build a polygon: `B` from the edge gcds, `I` relative to the convex hull, the shoelace number, `I + B/2 − 1`, the corner fan with its dets, and which of `Injective`/`ConvexCCW`/`LocalCCWTurns`/`PrimitiveEdges`/`EmptyInterior` hold — naming the hypothesis that fails | `preset`, `editable` (default true), `lo`/`hi` (grid range), `show`: any of `counts`, `hypotheses`, `fan` |
| `triangulate` | the counts of a primitive triangulation for given `I`, `B` — `V`, `T`, `E`, `F`, `2E = 3T + B`, `V − E + F`, `T/2`, `I + B/2 − 1` — and a stepper through the four Euler-preserving moves of `DiskEuler.lean` | `I`, `B`, `show`: any of `counts`, `moves` |
| `outline` | a vertical proof outline with links | `steps: [{text, link?, decl?, note?, hard?, gap?}]` — `decl` is a declaration id; the build resolves it from `data/decls.json` into a "File.lean lines a–b" link to the browsable source, and fails if it does not exist. `gap: true` marks a hypothesis or step that is **not proved** in the repo. |
| `walkthrough` | a proof outline you step through, with the Lean of each step and links to the nodes it uses | `steps: [{text, lean?, note?, link?, uses?, hard?}]` |

Presets, by widget:

| widget | presets |
|---|---|
| `polyhedron` | `tetrahedron` `{3,3}`, `cube` `{4,3}`, `octahedron` `{3,4}`, `dodecahedron` `{5,3}` and `icosahedron` `{3,5}` (the last two are *not* built in the Lean), `triangular-prism` and `square-pyramid` (convex but not regular, so no `(s,m)` describes them), `picture-frame` (toroidal, **not convex**, `V − E + F = 0`) |
| `pick` | `triangle`, `unit-square`, `primitive-triangle`, `pentagon`, `empty-primitive` (the shape of `results_picks_of_empty_primitive_fan`), and four that break a hypothesis: `collinear-vertex` (`LocalCCWTurns` fails), `non-convex` (`ConvexCCW` fails, and `I` counts hull points the shape excludes), `clockwise` (`ConvexCCW` fails on orientation), `repeated-vertex` (injectivity fails) |

New widget types go in `learn/assets/widgets-interactive.js` (export them from `INTERACTIVE`,
which `widgets.js` merges into `REGISTRY`) **and** the `enum` in
`learn/schema/node.schema.json`; a test asserts that those two lists agree.

Put the logic a widget shows in one of the modules that mirror the Lean, not in the widget
itself, and test it:

| module | mirrors |
|---|---|
| `learn/assets/polyhedra.js` | `Polytope.lean` and `PolytopeFaces.lean`: for the convex presets the face list is **computed** from the coordinates by supporting planes, which is `isFaceOf_convexHull_argmax`'s recipe, not typed in; plus the incidence counts of `PlatonicOfEuler` (vertex degree, edges per face, faces per edge) and a vertex truncation |
| `learn/assets/facelattice.js` | `Polytope.faceEulerSum` on the two families whose counts are exact: `EulersGem.faceCount` / `SimplexFaces.affDim_face` for the simplex, `Cube.affDim_face` for the cube; and the "drop the body" step of `euler_relation_of_isPolytope` |
| `learn/assets/schlafli.js` | `Platonic.lean`: `mul_euler_int`, `sub_mul_lt_four`, `schlafliPairs`, `pos_edges_of_euler`, and the `(V,E,F)` of the five `RegularNumbers` records |
| `learn/assets/lattice.js` | `LatticeTriangle.lean` (`edgeGcd`, `latticeDet`, `triangleShoelace`, `IsDetPrimitive`), `LatticePolygon.lean` (`edgeLatticePoints`, `boundaryLatticePoints`, `B`, `convexHullRegion`, `interiorLatticePoints`, `shoelaceSum`, `shoelace`), `LatticeFan.lean` (`ConvexCCW`, `LocalCCWTurns`, `StrictlyConvexCCW`, `PrimitiveEdges`, `EmptyInterior`, `fanTriangle`, `FanDetsPos`, `FanDetPrimitive`) and `DiskEuler.lean`'s triangulated-disk counts |
| `learn/assets/dom.js` | nothing in the Lean: shared element helpers, the `illustration()` footer and the stepper control |

Tests live in `learn/tools/test_widgets.mjs` and run under `npm test`. Assert against the Lean
statement, not against the widget's output — for example: that the computed face counts of the
cube are the `8, 12, 6` of `Cube.cube_face_counts`; that the toroidal preset has
`V − E + F = 0` and is not convex; that every edge of every preset lies in exactly two faces (the
diamond property); that truncating a vertex of degree `d` sends `(V, E, F)` to
`(V − 1 + d, E + d, F + 1)` and leaves the alternating sum alone; that `faceEulerSum` of the
n-simplex and the n-cube is `1` for every `n`; that `(s−2)(m−2) < 4` holds for exactly the five
pairs in `Platonic.schlafliPairs`; that `|edgeLatticePoints p q| = edgeGcd p q + 1`; that
`StrictlyConvexCCW` fails exactly where the presets say it does; that every strictly convex
lattice triangle in a small box satisfies `shoelace = I + B/2 − 1`; that
`2E = 3T + B` and `V − E + F = 2` for the triangulated-disk counts.

## Check locally

```sh
cd learn
npm ci
npm test              # widget-logic tests, then the node schema and cross-checks
npm run build         # writes learn/dist/
npm run serve         # builds and serves it on http://localhost:8765
```

Widgets must work at 390 px wide with no horizontal overflow, and the `polyhedron` and `pick`
widgets must respond to touch (they use pointer events) — check one on a narrow window before
opening a PR. CI runs the same checks on every PR that touches `learn/`, and `pages.yml` deploys
to GitHub Pages on every push to `main`.

## Regenerating the declaration graph

`learn/data/decls.json` comes from the compiled Lean, so it needs regenerating whenever the Lean
changes shape — a renamed declaration, a new `Results` theorem, a moved module.

```sh
cd lean
lake exe cache get                                  # Mathlib from the build cache; never build it
lake build
lake env lean ../learn/tools/ExtractDecls.lean      # writes learn/data/decls.raw.json
python3 ../learn/tools/build_decls.py               # writes learn/data/decls.json
```

The full build is long (the Pick lane has some very large modules — `LatticeFanInduction.lean` is
nearly 8000 lines) and wants a machine you can leave alone. If someone else is building in
`lean/`, wait for them rather than starting a second build.

`ExtractDecls.lean` records, for each declaration, the project constants used in its **type** and
in its **value**. `build_decls.py` turns those into:

- `meaningDeps`: what you must understand to understand the declaration. For a theorem that is
  the constants in its statement. For a definition it is the statement *and* the body, because
  the body is what it means.
- `proofDeps`: the extra constants a theorem's proof uses.

It also slices the verbatim statement text out of the source, records the anchor in the
browsable source under `docs/`, and computes each declaration's distance from the nearest
`Results` theorem. Generated helpers (recursors, `match_`/`proof_` auxiliaries, equation lemmas)
are folded into the declaration they belong to.

`npm run build` additionally writes `dist/data/informal-map.json`, a map from fully qualified
Lean name to explainer URL, which `scripts/build-source-pages.py --informal-map` uses to link the
browsable source back here.

## Discussion

Each node page has a comment thread (giscus, backed by GitHub Discussions in this repository, one
discussion per node titled `node: <id>`, in the **Announcements** category). Use it for questions
and disagreements. Use PRs for changes to the text or the quiz key.
