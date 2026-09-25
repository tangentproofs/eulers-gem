# Claude audit — Pick formalization (2026-09-24)

**Verdict: FAIL for presenting as Pick's theorem.**

Auditor: Claude (via `claude -p`), standing policy: double-check before claiming proved results.
This file is the gate: no Results/README claim that classical Pick is proved until a later audit PASSes.

## Critical FAIL points (copy from audit)

1. **Do not ship non-compiling geometry with overclaiming docs.**
   A draft `EulersGem/PicksGeometry.lean` claimed four results in the module docstring while still mid-tactic / non-building. **Deleted** rather than committed red. Any future geometry file must be `lake build`-green before commit, and docstrings may only name proved theorems.

2. **Honesty pass was insufficient while identifiers/table still said "Pick".**
   Arithmetic Funkenbusch/triangulation glue must **not** sit in a proved/landed column labeled Pick until the *statement* mentions a lattice polygon + geometric measure/area.
   Prefer names like `funkenbusch_identity` / `triangulation_count_identity`; **drop `picks` from identifiers** for the arithmetic glue.
   **Done in this train:** renamed theorems + Results exports; README/site/ROADMAP reworded; ROADMAP Pick checkbox unchecked.

3. **`Picks.lean` docstring overclaims.**
   Phrases such as "hence Pick", "classical shape", and a tautological `edges_of_triangulation` with a combinatorial docstring (identity hypothesis restated as theorem) were misleading.
   **Done:** docstrings rewritten as count identities; tautology deleted; handshaking left as an *assumption* with an explicit Mathlib gap note.

4. **ROADMAP checked box for Pick.**
   `- [x] Pick's theorem Euler→Funkenbusch bookkeeping` overclaimed.
   **Done:** unchecked / reworded to classical Pick open; only count identities landed.

5. **Real geometric path requirements (still open).**
   For an auditor-acceptable classical Pick, need all of:
   - lattice polygon definitions;
   - area as Lebesgue/Haar measure **or** shoelace proved equal to measure;
   - primitive triangle volume `= 1/2` via **det ↔ Haar** (not merely `|det|/2` arithmetic on a named `def`);
   - triangulation **existence** OR an honest witness whose fields are **geometric** (not free `ℤ` counters);
   - planar Euler **proved** (not assumed);
   - handshaking **proved** (not assumed);
   - area additivity across the triangulation.

   **ASAP acceptable target (not yet claimed in Results as Pick):**
   - primitive triangle shoelace/`|det|=1` facts, honestly labeled;
   - Pick-shaped conclusion **given** a fully geometric `PrimitiveLatticeTriangulation` witness;
   - **no** overclaim that triangulation existence is proved.

## Current status after remediation

| Item | Status |
|------|--------|
| Broken `PicksGeometry.lean` | Deleted (was red) |
| Theorem ids without `picks_*` for glue | `funkenbusch_identity`, `triangulation_count_identity` |
| Results exports | `results_funkenbusch_identity`, `results_triangulation_count_identity` |
| README / site / ROADMAP | Explicit **not Pick**; ROADMAP unchecked |
| Classical Pick in Results | **Not claimed** (gate) |
| Geometric substrate | `LatticeTriangle.lean`: shoelace/`|det|=1`/Cramer/integer-barycentric/shoelace-sum green — **not** Haar, **not** Pick |

## Candidate for a future PASS (do not promote until re-audited)

None yet in Results. When a candidate exists, paste the **exact theorem type**, file path, and `lake build Results` log excerpt below and re-run Claude before any claim commit.

Strongest Pick-*related* statements now in tree (none claimed as classical Pick in Results):

**Results (count identities only):**
```lean
theorem results_funkenbusch_identity
    (I B V E F : ℤ) (A : ℚ)
    (heuler : V - E + F = 2) (hverts : V = I + B)
    (hedges : E = 3 * I + 2 * B - 3)
    (harea : A = ((F : ℚ) - 1) / 2) :
    A = (I : ℚ) + (B : ℚ) / 2 - 1

theorem results_triangulation_count_identity
    (I B V E T F : ℤ) (A : ℚ)
    (hV : V = I + B) (hF : F = T + 1)
    (heuler : V - E + F = 2) (hshake : 2 * E = 3 * T + B)
    (harea : A = (T : ℚ) / 2) :
    A = (I : ℚ) + (B : ℚ) / 2 - 1
```

**LatticeTriangle (shoelace arithmetic, not Haar):**
```lean
theorem triangleShoelace_eq_half_of_natAbs_det_eq_one
    (a b c : ℤ × ℤ) (h : Int.natAbs (latticeDet a b c) = 1) :
    triangleShoelace a b c = 1 / 2

theorem sum_shoelace_eq_card_div_two
    (S : Finset Triangle) (h : ∀ t ∈ S, t.IsDetPrimitive) :
    (∑ t ∈ S, t.shoelace) = (S.card : ℚ) / 2
```
File: `lean/EulersGem/LatticeTriangle.lean`. Not exported in Results as Pick.



## Update 2026-09-24 (EP-spine substrate; still FAIL for classical Pick)

**Architecture:** Pick must discharge Euler from `Euler_Poincare_full` / planar EP —
not free `ℤ` Euler. Ehrhart bypasses disallowed.

Landed (honest names; **not** classical Pick in Results):

| Item | Status |
|------|--------|
| `LatticePolygon` + geometric I/B/shoelace | Green |
| `memClosedTriangle_eq_vertices_of_natAbs_det_eq_one` | Green (emptiness) |
| `PrimitiveLatticeTriangulationWitness` | Green |
| `results_shoelace_pick_form_of_primitive_triangulation_witness` | Green; **conditional** on witness + `hEuler_planar` + handshaking |
| Classical Pick | **Still FAIL** — general existence, general EP→planar, measure open |

### Candidate statement (do NOT rename to Pick until re-audit PASS)

```lean
theorem results_shoelace_pick_form_of_primitive_triangulation_witness
    (W : EulersGem.Picks.PrimitiveLatticeTriangulationWitness)
    (V E F : ℤ)
    (hV : V = (W.I : ℤ) + W.B)
    (hF : F = (W.T : ℤ) + 1)
    (hEuler_planar : V - E + F = 2)   -- EP-spine discharge pending
    (hshake : 2 * E = 3 * (W.T : ℤ) + W.B) :
    W.shoelaceArea = (W.I : ℚ) + (W.B : ℚ) / 2 - 1
```

File: `lean/EulersGem/PicksTriangulation.lean` / `lean/Results.lean`.


## Update 2026-09-24 (handshaking from incidence; still FAIL for classical Pick)

Landed in `EulersGem/PlanarTriangulation.lean` (honest names; **not** classical Pick):

```lean
theorem two_E_eq_three_T_add_B {α} [DecidableEq α]
    (G : CombinatorialDiskTriangulation α) :
    2 * G.E = 3 * G.T + G.B
```

`B` = `#boundaryEdges`. Results exports:
`results_handshaking_of_combinatorial_disk_triangulation`,
`results_triangulation_count_identity_of_disk_triangulation`
(handshaking discharged; Euler still a hyp).

| Item | Status |
|------|--------|
| Handshaking from incidence | Green (combinatorial) |
| Geometric witness → incidence structure | Partial (unit square green; general open) |
| EP → planar Euler | Partial (unit square / fan n≤5 / fan counts green; general `Euler_Poincare_full` open) |
| Triangulation existence | Partial (combinatorial fan n≤5; general open) |
| Classical Pick | **Still FAIL** |

## Update 2026-09-24 (unit-square Euler discharge + fan existence; still FAIL)

Landed (honest names; **not** classical Pick):

```lean
theorem planar_disk_euler_of_fan_counts
    (n V E T B F : ℕ) (hn : 3 ≤ n)
    (hV : V = n) (hB : B = n) (hT : T = n - 2)
    (hE : E = 2 * n - 3) (hF : F = T + 1) :
    (V : ℤ) - E + F = 2

theorem unitSquare_planar_euler :
    (unitSquare.planarCounts).eulerChar = 2

theorem exists_fan_disk_triangulation {n : ℕ} (hn : 3 ≤ n) (hN : n ≤ 5) :
    Nonempty (CombinatorialDiskTriangulation (Fin n))

theorem shoelace_pick_form_of_unit_square :
    UnitSquareWitness.witness.shoelaceArea =
      (UnitSquareWitness.witness.I : ℚ) + (UnitSquareWitness.witness.B : ℚ) / 2 - 1
```

Results exports: `results_unit_square_planar_euler`,
`results_planar_disk_euler_of_fan_counts`, `results_exists_fan_disk_triangulation`,
`results_fan5_planar_euler`, `results_shoelace_pick_form_of_unit_square`.

| Item | Status |
|------|--------|
| Handshaking from incidence | Green (combinatorial) |
| Geometric witness → incidence (unit square) | Green |
| Planar Euler (unit square + fan n≤5 + fan counts) | Green (concrete / combinatorial) |
| General EP → planar via `Euler_Poincare_full` | Open (`planar_disk_euler_of_EP_bridge`) |
| Triangulation existence (n≤5 combinatorial fan) | Green (small-n slice) |
| Triangulation existence (arbitrary lattice polygons) | Open |
| Shoelace = Haar | Open |
| Classical Pick | **Still FAIL** |

## Update 2026-09-24 (disk-count Euler + fan n≤7; still FAIL for classical Pick)

Landed (honest names; **not** classical Pick):

```lean
theorem planar_disk_euler_of_disk_counts
    (V E T B F I : ℕ)
    (hshake : 2 * E = 3 * T + B)
    (hV : V = I + B)
    (hT : T + 2 = 2 * I + B)
    (hF : F = T + 1) :
    (V : ℤ) - E + F = 2

theorem CombinatorialDiskTriangulation.planar_euler_of_disk_counts
    (G) (I : ℕ) (hV : G.V = I + G.B) (hT : G.T + 2 = 2 * I + G.B) :
    (G.planarCounts).eulerChar = 2

theorem shoelace_pick_form_of_witness_of_disk_counts
    (W) (G) (hT) (hB) (hV : G.V = W.I + G.B)
    (hTshape : G.T + 2 = 2 * W.I + G.B) :
    W.shoelaceArea = (W.I : ℚ) + (W.B : ℚ) / 2 - 1

theorem exists_fan_disk_triangulation {n : ℕ} (hn : 3 ≤ n) (hN : n ≤ 7) :
    Nonempty (CombinatorialDiskTriangulation (Fin n))
```

Unit-square planar Euler and shoelace Pick-form now discharge Euler via
empty-interior / disk-count axioms (not bare `native_decide` on the char).
Fan existence slice extended `5 → 7` (`fan6`, `fan7`); construction is uniform
in `n`, but general-`n` incidence (removing the bound) remains open.
`planar_disk_euler_of_EP_bridge` still open. Claude PlatonicOfEuler /
PolytopeFaces / Embed untouched.

| Item | Status |
|------|--------|
| Handshaking from incidence | Green |
| Planar Euler from disk-count axioms | Green (combinatorial) |
| Unit-square Euler via disk counts | Green |
| Fan existence (`3 ≤ n ≤ 7`) | Green (slice; general incidence open) |
| General EP → planar via `Euler_Poincare_full` | Open |
| Triangulation existence (arbitrary lattice polygons) | Open |
| Shoelace = Haar | Open |
| Classical Pick | **Still FAIL** |

## Update 2026-09-24 (general fan `n ≥ 3`; still FAIL for classical Pick)

Landed in `EulersGem/FanDisk.lean` (honest names; **not** classical Pick):

```lean
theorem exists_fan_disk_triangulation (n : ℕ) (hn : 3 ≤ n) :
    Nonempty (CombinatorialDiskTriangulation (Fin n))

theorem fan_planar_euler (n : ℕ) (hn : 3 ≤ n) :
    ((fan n hn).planarCounts).eulerChar = 2
```

Fan incidence proved for **all** `n ≥ 3` (Nat-indexed boundary / diagonals /
triangles — no `native_decide` Fin-bound). Planar Euler via empty-interior
disk counts. Unit-square + disk-count pathways unchanged. Classical Pick still
FAIL (geometry / Haar / general EP→planar / polygon triangulation existence
open). Claude `SimplexFaces.lean` / Embed / Platonic untouched.

| Item | Status |
|------|--------|
| Handshaking from incidence | Green |
| Planar Euler from disk-count axioms | Green |
| Fan existence (`∀ n ≥ 3`) | **Green** (combinatorial) |
| Unit-square Euler via disk counts | Green |
| General EP → planar via `Euler_Poincare_full` | Open |
| Geometric lattice-polygon triangulation existence | Open |
| Shoelace = Haar | Open |
| Classical Pick | **Still FAIL** |


## Update 2026-09-24 (geometric fan + empty-interior Pick-form; still FAIL)

Landed in `EulersGem/LatticeFan.lean` (honest names; **not** classical Pick):

```lean
theorem fan_shoelace_identity (n : ℕ) (hn : 3 ≤ n) (v : ℕ → ℤ × ℤ) :
    ∑ i ∈ range n, cross (v i) (v ((i+1)%n)) =
      ∑ i ∈ range (n-2), latDet (v 0) (v (i+1)) (v (i+2))

theorem shoelaceSum_eq_sumFanDet (P : LatticePolygon) :
    P.shoelaceSum = sumFanDet P

theorem B_eq_nVertices_of_primitive_edges
    (P) (PrimitiveEdges P) (Injective P.vertex) :
    P.B = P.nVertices

theorem shoelace_eq_B_div_two_sub_one_of_primitive_fan
    (P) (Injective P.vertex) (PrimitiveEdges P)
    (FanDetsNonneg P) (FanDetPrimitive P) :
    P.shoelace = (P.B : ℚ) / 2 - 1
```

Results exports: `results_fan_shoelace_identity`,
`results_shoelaceSum_eq_sumFanDet`,
`results_B_eq_nVertices_of_primitive_edges`,
`results_shoelace_eq_B_div_two_sub_one_of_primitive_fan`.

Geometric fan triangles `(v₀,v_{i+1},v_{i+2})` + algebraic shoelace additivity
(oriented). Empty-interior Pick-form discharges under **fan-primitivity hyps**
(not `empty⇒|det|=1`). Claude Embed / Platonic / SimplexFaces / Octahedron
untouched.

| Item | Status |
|------|--------|
| Handshaking from incidence | Green |
| Planar Euler from disk-count axioms | Green |
| Fan existence (`∀ n ≥ 3`) combinatorial | Green |
| Algebraic geometric fan shoelace identity | **Green** |
| `B = n` for primitive edges | **Green** |
| Empty-interior shoelace `= B/2−1` (fan-primitivity hyps) | **Green** |
| `empty ⇒ \|det\|=1` | Open |
| General EP → planar via `Euler_Poincare_full` | Open |
| Geometric triangulation existence (no primitivity hyp) | Open |
| Shoelace = Haar | Open |
| Classical Pick | **Still FAIL** |



## Update 2026-09-24 (empty ⇒ `|det|=1`; still FAIL for classical Pick)

Landed in `EulersGem/LatticeTriangleEmpty.lean` (honest names; **not** classical Pick):

```lean
theorem natAbs_det_eq_one_of_memClosedTriangle_eq_vertices
    (a b c : ℤ × ℤ)
    (hne : latticeDet a b c ≠ 0)
    (h : ∀ p, MemClosedTriangle a b c p → p = a ∨ p = b ∨ p = c) :
    Int.natAbs (latticeDet a b c) = 1

theorem FanDetPrimitive_of_empty_fan_triangles
    (P) (FanDetsPos P) (FanTrianglesEmpty P) :
    FanDetPrimitive P

theorem shoelace_eq_B_div_two_sub_one_of_empty_fan
    (P) (Injective P.vertex) (PrimitiveEdges P)
    (FanDetsPos P) (FanTrianglesEmpty P) :
    P.shoelace = (P.B : ℚ) / 2 - 1
```

Results exports: `results_natAbs_det_eq_one_of_memClosedTriangle_eq_vertices`,
`results_FanDetPrimitive_of_empty_fan_triangles`,
`results_shoelace_eq_B_div_two_sub_one_of_empty_fan`.

**Main prize partial:** converse of emptiness⇔`|det|=1` for **nondegenerate**
lattice triangles (companion/Bézout construction). Fan-primitivity hyp discharged
when each fan ear is empty + positively oriented. Still **not** classical Pick:
proving `FanTrianglesEmpty` from polygon-empty-interior for convex fans,
shoelace=Haar, general triangulation existence, and EP→planar remain open.
Claude Platonic / Embed / Octahedron untouched.

| Item | Status |
|------|--------|
| Handshaking from incidence | Green |
| Planar Euler from disk-count axioms | Green |
| Fan existence (`∀ n ≥ 3`) combinatorial | Green |
| Algebraic geometric fan shoelace identity | Green |
| `B = n` for primitive edges | Green |
| Empty-interior shoelace `= B/2−1` (fan-primitivity hyps) | Green |
| `empty ⇒ \|det\|=1` (nondegenerate triangle) | **Green** |
| `FanDetPrimitive` from empty fan ears + `FanDetsPos` | **Green** |
| `FanTrianglesEmpty` from polygon `I=0` (convex) | Partial — see next update |
| General EP → planar via `Euler_Poincare_full` | Open |
| Geometric triangulation existence (no emptiness hyp) | Open |
| Shoelace = Haar | Open |
| Classical Pick | **Still FAIL** |


## Update 2026-09-24 (`FanTrianglesEmpty` from `I=∅`; still FAIL for classical Pick)

Landed in `EulersGem/LatticeFan.lean` / `LatticeTriangle.lean` (honest names; **not** classical Pick):

```lean
theorem mem_convexHull_of_memClosedTriangle
    (a b c p) (MemClosedTriangle a b c p) :
    toReal p ∈ convexHull ℝ {toReal a, toReal b, toReal c}

theorem FanTrianglesEmpty_of_empty_interior
    (P) (Injective P.vertex) (PrimitiveEdges P)
    (EmptyInterior P) (VerticesExtreme P) :
    FanTrianglesEmpty P

theorem shoelace_eq_B_div_two_sub_one_of_empty_interior
    (P) (Injective P.vertex) (PrimitiveEdges P)
    (FanDetsPos P) (EmptyInterior P) (VerticesExtreme P) :
    P.shoelace = (P.B : ℚ) / 2 - 1
```

Results exports: `results_mem_convexHull_of_memClosedTriangle`,
`results_boundaryLatticePoints_eq_vertexFinset`,
`results_FanTrianglesEmpty_of_empty_interior`,
`results_shoelace_eq_B_div_two_sub_one_of_empty_interior`.

**Prize progress:** fan ears empty of extra lattice points when the polygon has
empty convex-hull interior, primitive edges, and extreme listed vertices.
`VerticesExtreme` is still a hyp (true for convex polygons; not yet discharged
from a local-turn / convexity predicate). Still **not** classical Pick: Haar,
general triangulation existence, EP→planar remain open. Claude Platonic / Embed /
Octahedron untouched.

| Item | Status |
|------|--------|
| `empty ⇒ \|det\|=1` (nondegenerate triangle) | Green |
| `FanDetPrimitive` from empty fan ears + `FanDetsPos` | Green |
| `FanTrianglesEmpty` from polygon `I=∅` + extreme vertices | **Green** (hyp `VerticesExtreme`) |
| Empty-interior shoelace `= B/2−1` under those hyps | **Green** |
| Discharge `VerticesExtreme` from convexity | Open |
| Shoelace = Haar | Open |
| Classical Pick | **Still FAIL** |


## Update 2026-09-25 (VerticesExtreme from StrictlyConvexCCW; still FAIL for classical Pick)

Landed in `EulersGem/LatticeFan.lean` / `LatticePolygon.lean` (honest names; **not** classical Pick):

```lean
def ConvexCCW : Prop :=
  ∀ i j, 0 ≤ latticeDet (vertex i) (vertex (nextIdx i)) (vertex j)

def LocalCCWTurns : Prop :=
  ∀ i, 0 < latticeDet (vertex (prevIdx i)) (vertex i) (vertex (nextIdx i))

def StrictlyConvexCCW : Prop := ConvexCCW P ∧ LocalCCWTurns P

theorem VerticesExtreme_of_strictlyConvexCCW
    (P) (StrictlyConvexCCW P) (Injective P.vertex) :
    VerticesExtreme P

theorem FanDetsNonneg_of_ConvexCCW (P) (ConvexCCW P) : FanDetsNonneg P

theorem shoelace_eq_B_div_two_sub_one_of_empty_interior_convex
    (P) (Injective P.vertex) (PrimitiveEdges P)
    (FanDetsPos P) (EmptyInterior P) (StrictlyConvexCCW P) :
    P.shoelace = (P.B : ℚ) / 2 - 1
```

Results exports: `results_VerticesExtreme_of_strictlyConvexCCW`,
`results_FanDetsNonneg_of_ConvexCCW`,
`results_shoelace_eq_B_div_two_sub_one_of_empty_interior_convex`.

**Prize progress:** `VerticesExtreme` discharged from the natural CCW convexity
predicate (edge half-planes + strict local turns) via supporting-line /
barycentric argument. Empty-interior Pick-form now takes `StrictlyConvexCCW`
instead of bare `VerticesExtreme`. Still **not** classical Pick: `FanDetsPos`
kept as orientation hyp (strict fan nondegeneracy); Haar; general triangulation
existence; EP→planar open. Claude Cube / Octahedron / Platonic / Embed untouched.

| Item | Status |
|------|--------|
| `FanTrianglesEmpty` from `I=∅` + extreme vertices | Green |
| Discharge `VerticesExtreme` from `StrictlyConvexCCW` | **Green** |
| Empty-interior shoelace with convexity predicate | **Green** |
| Discharge `FanDetsPos` from strict convexity | Open (nonneg from `ConvexCCW`) |
| Shoelace = Haar | Open |
| Classical Pick | **Still FAIL** |

## Update 2026-09-25 (FanDetsPos from StrictlyConvexCCW; still FAIL for classical Pick)

Landed in `EulersGem/LatticeFan.lean` (honest names; **not** classical Pick):

```lean
lemma exists_mem_segment_of_detR_eq_zero
    (A B C : ℝ × ℝ) (A ≠ B) (A ≠ C) (B ≠ C) (detR A B C = 0) :
    C ∈ segment ℝ A B ∨ A ∈ segment ℝ B C ∨ B ∈ segment ℝ A C

theorem not_collinear_of_VerticesExtreme
    (VerticesExtreme P) (Injective P.vertex) (i j k) (distinct) (latticeDet = 0) :
    False

theorem FanDetsPos_of_strictlyConvexCCW
    (StrictlyConvexCCW P) (Injective P.vertex) :
    FanDetsPos P

theorem shoelace_eq_B_div_two_sub_one_of_empty_interior_convex
    (Injective P.vertex) (PrimitiveEdges P)
    (EmptyInterior P) (StrictlyConvexCCW P) :
    P.shoelace = (P.B : ℚ) / 2 - 1
```

Results exports: `results_FanDetsPos_of_strictlyConvexCCW`,
`results_shoelace_eq_B_div_two_sub_one_of_empty_interior_convex` (no `FanDetsPos` hyp).

**Prize progress:** `FanDetsPos` discharged from `StrictlyConvexCCW` + injective
vertices: nonnegativity from `ConvexCCW`; vanishing would make a fan triple collinear,
hence one vertex lies on the segment of the other two, contradicting `VerticesExtreme`
(already discharged from the same convexity predicate). Empty-interior Pick-form now
takes only injective vertices + primitive edges + empty interior + `StrictlyConvexCCW`.
Still **not** classical Pick: Haar/Lebesgue equality; general triangulation existence;
EP→planar open. Claude Cube / Octahedron / Platonic / Embed / EdgeVertices untouched
in this commit.

| Item | Status |
|------|--------|
| Discharge `VerticesExtreme` from `StrictlyConvexCCW` | Green |
| Discharge `FanDetsPos` from `StrictlyConvexCCW` + injective | **Green** |
| Empty-interior shoelace with both discharged | **Green** |
| Shoelace = Haar | Open |
| Classical Pick | **Still FAIL** |

## Update 2026-09-25 (I=1 interior-fan shoelace Pick-form; still FAIL for classical Pick)

Landed in `EulersGem/LatticeFanInterior.lean` (honest names; **not** classical Pick):

```lean
theorem sum_interiorFanDet_eq_shoelaceSum (P) (q) :
    (∑ i, interiorFanDet P q i) = P.shoelaceSum

theorem InteriorFanDetPrimitive_of_empty
    (InteriorFanDetsPos P q) (InteriorFanTrianglesEmpty P q) :
    InteriorFanDetPrimitive P q

theorem shoelace_eq_I_add_B_div_two_sub_one_of_interior_fan
    (Injective P.vertex) (PrimitiveEdges P)
    (InteriorFanDetsPos P q) (InteriorFanTrianglesEmpty P q) :
    P.shoelace = (1 : ℚ) + (P.B : ℚ) / 2 - 1
```

Results exports: `results_sum_interiorFanDet_eq_shoelaceSum`,
`results_InteriorFanDetPrimitive_of_empty`,
`results_shoelace_eq_I_add_B_div_two_sub_one_of_interior_fan`.

**Prize progress:** first **I > 0** Pick-shaped shoelace identity on the EP spine.
Algebraic fan-from-interior identity is unconditional. Under positive orientation +
empty interior-fan triangles + primitive edges: `shoelace = 1 + B/2 − 1`
(= `I + B/2 − 1` with `I = 1`). Still **not** classical Pick:
`InteriorFanDetsPos` / `InteriorFanTrianglesEmpty` not yet discharged from
`UniqueInterior` + `StrictlyConvexCCW`; Haar; general I>1 triangulation;
EP→planar open. Claude Cube / Octahedron / Platonic / EdgeVertices untouched.

| Item | Status |
|------|--------|
| Empty-interior shoelace with `StrictlyConvexCCW` | Green |
| Unconditional interior-fan algebraic identity | **Green** |
| I=1 shoelace `= 1 + B/2 − 1` under fan hyps | **Green** |
| Discharge `InteriorFanDetsPos` / empty from `UniqueInterior` | Open |
| Construct `PrimitiveLatticeTriangulationWitness` from convex polygon | Open |
| Shoelace = Haar | Open |
| Classical Pick | **Still FAIL** |


## Update 2026-09-25 (InteriorFanDetsPos from UniqueInterior; still FAIL for classical Pick)

Landed in `EulersGem/LatticeFanInterior.lean` (honest names; **not** classical Pick):

```lean
theorem InteriorFanDetsPos_of_uniqueInterior
    (StrictlyConvexCCW P) (Injective P.vertex) (PrimitiveEdges P)
    (UniqueInterior P q) :
    InteriorFanDetsPos P q

theorem eq_apex_of_mem_interiorFan_of_uniqueInterior
    (UniqueInterior P q) … (p ∉ boundary) :
    p = q

theorem shoelace_eq_I_add_B_div_two_sub_one_of_uniqueInterior_of_empty
    (Injective P.vertex) (PrimitiveEdges P) (StrictlyConvexCCW P)
    (UniqueInterior P q) (InteriorFanTrianglesEmpty P q) :
    P.shoelace = (1 : ℚ) + (P.B : ℚ) / 2 - 1
```

Results exports: `results_InteriorFanDetsPos_of_uniqueInterior`,
`results_shoelace_eq_I_add_B_div_two_sub_one_of_uniqueInterior_of_empty`.

**Prize progress:** `InteriorFanDetsPos` discharged from geometric hyps (half-plane
nonnegativity on the hull + vanishing ⇒ edge segment ⇒ primitive endpoints ⇒
boundary, contradicting interior). Non-boundary lattice points in fan ears equal
the unique apex. Still **not** classical Pick: full `InteriorFanTrianglesEmpty`
needs foreign-vertex extremality renormalization (open); Haar; I>1 triangulation;
EP→planar open. Claude Cube / Octahedron / Platonic / EdgeVertices untouched.

| Item | Status |
|------|--------|
| Unconditional interior-fan algebraic identity | Green |
| I=1 shoelace under fan hyps | Green |
| Discharge `InteriorFanDetsPos` from `UniqueInterior` + CCW | **Green** |
| Non-boundary ear points = unique apex | **Green** |
| Full `InteriorFanTrianglesEmpty` (foreign vertices) | Open |
| Shoelace = Haar | Open |
| Classical Pick | **Still FAIL** |

## Update 2026-09-25 (InteriorFanTrianglesEmpty from UniqueInterior; still FAIL for classical Pick)

Landed in `EulersGem/LatticeFanInterior.lean` (honest names; **not** classical Pick):

```lean
theorem InteriorFanTrianglesEmpty_of_uniqueInterior
    (StrictlyConvexCCW P) (Injective P.vertex) (PrimitiveEdges P)
    (UniqueInterior P q) :
    InteriorFanTrianglesEmpty P q

theorem shoelace_eq_I_add_B_div_two_sub_one_of_uniqueInterior
    (Injective P.vertex) (PrimitiveEdges P) (StrictlyConvexCCW P)
    (UniqueInterior P q) :
    P.shoelace = (1 : ℚ) + (P.B : ℚ) / 2 - 1
```

Results exports: `results_InteriorFanTrianglesEmpty_of_uniqueInterior`,
`results_shoelace_eq_I_add_B_div_two_sub_one_of_uniqueInterior`.

**Prize progress:** foreign-vertex extremality closed via supporting half-plane at
the foreign vertex (CCW incoming-edge functional vanishes at the vertex, is
nonnegative on all vertices, and is strictly positive at the unique interior
apex — so the apex weight in a barycentric combination must be zero, reducing to
a primitive boundary edge). Full geometric I=1 shoelace form takes only injective
vertices + primitive edges + `StrictlyConvexCCW` + `UniqueInterior`. Still **not**
classical Pick: Haar/Lebesgue; general I>1 triangulation existence; EP→planar open.
Claude Cube / Octahedron / Platonic / EdgeVertices untouched.

| Item | Status |
|------|--------|
| Discharge `InteriorFanDetsPos` from `UniqueInterior` + CCW | Green |
| Non-boundary ear points = unique apex | Green |
| Full `InteriorFanTrianglesEmpty` (foreign vertices) | **Green** |
| I=1 shoelace under only geometric hyps | **Green** |
| Shoelace = Haar | Open |
| Classical Pick | **Still FAIL** |


## Update 2026-09-25 (I∈{0,1} Finset unification + I=2 scaffold; still FAIL for classical Pick)

Landed in `EulersGem/LatticeFanInterior.lean` (honest names; **not** classical Pick):

```lean
theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_one
    (S : Finset (ℤ × ℤ))
    (↑S = P.interiorLatticePoints) (S.card ≤ 1)
    (Injective P.vertex) (PrimitiveEdges P) (StrictlyConvexCCW P) :
    P.shoelace = (S.card : ℚ) + (P.B : ℚ) / 2 - 1

def TwoInterior (q r : ℤ × ℤ) : Prop :=
  q ≠ r ∧ P.interiorLatticePoints = {q, r}

theorem InteriorFanDetsPos_of_twoInterior_left
    (StrictlyConvexCCW P) (Injective P.vertex) (PrimitiveEdges P)
    (TwoInterior P q r) :
    InteriorFanDetsPos P q

theorem twoInterior_of_finset_card_two
    (↑S = P.interiorLatticePoints) (S.card = 2) :
    ∃ q r, TwoInterior P q r ∧ S = {q, r}
```

Results exports: `results_shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_one`,
`results_TwoInterior`, `results_InteriorFanDetsPos_of_twoInterior_left`,
`results_twoInterior_of_finset_card_two`.

**Prize progress:** empty-interior + unique-interior wired into a **single** Finset
statement covering `I ∈ {0,1}` with crystal-clear “not classical Pick” labeling.
I=2 scaffolding: `TwoInterior` + fan positivity from either apex (no uniqueness
needed — already had `InteriorFanDetsPos_of_mem_interior`). Still **not** classical
Pick: fan covering of the second interior point; ear-triangle inheritance of I=1;
B-bookkeeping across shared spokes; Haar; EP→planar open. Claude Cube / Octahedron /
Platonic / EdgeVertices / MetricRegular untouched.

| Item | Status |
|------|--------|
| I=0 shoelace under `StrictlyConvexCCW` | Green |
| I=1 shoelace under only geometric hyps | Green |
| Combined Finset `I ∈ {0,1}` shoelace | **Green** |
| `TwoInterior` + fan positivity from either apex | **Green** (scaffold) |
| Fan covering of second interior point | Open |
| Ear inheritance → I=1 on triangle polygon | Open |
| Shoelace = Haar | Open |
| Classical Pick | **Still FAIL** |


## Update 2026-09-25 (I=2 fan covering + empty-ear failure; still FAIL for classical Pick)

Landed in `EulersGem/LatticeFanInterior.lean` (honest names; **not** classical Pick):

```lean
theorem exists_mem_interiorFanTriangle_of_mem_hull
    (StrictlyConvexCCW P) (InteriorFanDetsPos P q)
    (toReal p ∈ P.convexHullRegion) :
    ∃ i, MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) p

theorem exists_mem_interiorFanTriangle_of_twoInterior
    (StrictlyConvexCCW P) (Injective P.vertex) (PrimitiveEdges P)
    (TwoInterior P q r) :
    ∃ i, MemClosedTriangle q (P.vertex i) (P.vertex (P.nextIdx i)) r

theorem not_InteriorFanTrianglesEmpty_of_twoInterior
    (StrictlyConvexCCW P) (Injective P.vertex) (PrimitiveEdges P)
    (TwoInterior P q r) :
    ¬ InteriorFanTrianglesEmpty P q

theorem memClosedTriangle_of_area_weights_nonneg
    (0 < latticeDet q v w)
    (0 ≤ latticeDet v w p) (0 ≤ latticeDet q p w) (0 ≤ latticeDet q v p) :
    MemClosedTriangle q v w p
```

Results exports: `results_exists_mem_interiorFanTriangle_of_mem_hull`,
`results_exists_mem_interiorFanTriangle_of_twoInterior`,
`results_not_InteriorFanTrianglesEmpty_of_twoInterior`.

**Prize progress:** fan covering of every hull lattice point from a positively
oriented interior apex (sector sign-change + ConvexCCW edge half-plane). Under
`TwoInterior`, the second interior point `r` occupies some closed ear from `q`,
so `InteriorFanTrianglesEmpty` necessarily fails for I=2 (as expected — do not
pursue empty-ear discharge at I=2). Still **not** classical Pick: ear inheritance
as UniqueInterior sub-polygon; B-bookkeeping across shared spokes; Haar;
EP→planar open. Claude Cube / Octahedron / Platonic / EdgeVertices / MetricRegular
untouched.

| Item | Status |
|------|--------|
| Combined Finset `I ∈ {0,1}` shoelace | Green |
| `TwoInterior` + fan positivity from either apex | Green (scaffold) |
| Fan covering of second interior point | **Green** |
| `InteriorFanTrianglesEmpty` fails for I=2 | **Green** (expected) |
| Ear inheritance → I=1 on triangle polygon | Open |
| B-bookkeeping across shared spokes | Open |
| Shoelace = Haar | Open |
| Classical Pick | **Still FAIL** |


## Update 2026-09-25 (I=2 empty-ear |det|=1 + trianglePolygon; still FAIL for classical Pick)

Landed in `EulersGem/LatticeFanInterior.lean` (honest names; **not** classical Pick):

```lean
theorem eq_vertices_or_r_of_mem_interiorFan_of_twoInterior
    (StrictlyConvexCCW P) (Injective P.vertex) (PrimitiveEdges P)
    (TwoInterior P q r) (i) (MemClosedTriangle ear p) :
    p = q ∨ p = vᵢ ∨ p = vᵢ₊₁ ∨ p = r

theorem eq_vertices_of_mem_interiorFan_of_twoInterior_of_not_mem_r
    … ( ¬ MemClosedTriangle ear r) … :
    p = q ∨ p = vᵢ ∨ p = vᵢ₊₁

theorem IsDetPrimitive_interiorFan_of_twoInterior_of_not_mem_r … :
    (interiorFanTriangle P q i).IsDetPrimitive

theorem interiorFanDet_eq_one_of_twoInterior_of_not_mem_r … :
    interiorFanDet P q i = 1

def trianglePolygon (a b c : ℤ × ℤ) : LatticePolygon
```

Results exports: `results_eq_vertices_or_r_of_mem_interiorFan_of_twoInterior`,
`results_eq_vertices_of_mem_interiorFan_of_twoInterior_of_not_mem_r`,
`results_IsDetPrimitive_interiorFan_of_twoInterior_of_not_mem_r`,
`results_interiorFanDet_eq_one_of_twoInterior_of_not_mem_r`,
`results_trianglePolygon`.

**Prize progress:** under `TwoInterior`, fan ears from `q` meet lattice points only
among `{q, vᵢ, vᵢ₊₁, r}`. Ears that do not contain `r` are empty of extras ⇒
`|det|=1`. Occupied-ear `trianglePolygon` substrate landed; UniqueInterior
inheritance for the occupied ear, triangle StrictlyConvexCCW/PrimitiveEdges,
and B-bookkeeping to reach `shoelace = 2 + B/2 − 1` still open. Still **not**
classical Pick: Haar; EP→planar; full I=2 Pick-form open. Claude Platonic /
Cube / MetricRegular / EdgeVertices untouched.

| Item | Status |
|------|--------|
| Fan covering of second interior point | Green |
| `InteriorFanTrianglesEmpty` fails for I=2 | Green (expected) |
| Ear lattice points ⊆ `{q,vᵢ,vᵢ₊₁,r}` | **Green** |
| Empty (of `r`) ears ⇒ `|det|=1` | **Green** |
| Occupied-ear `trianglePolygon` substrate | **Green** |
| Occupied-ear UniqueInterior / I=1 inheritance | Open |
| B-bookkeeping → `shoelace = 2 + B/2 − 1` | Open |
| Shoelace = Haar | Open |
| Classical Pick | **Still FAIL** |



## Update 2026-09-25 (I=2 occupied-ear UniqueInterior; still FAIL for classical Pick)

Landed in `EulersGem/LatticeFanInterior.lean` (honest names; **not** classical Pick):

```lean
def OffTriangleBoundary (a b c r : ℤ × ℤ) : Prop

theorem memClosedTriangle_of_mem_convexHull
    (toReal p ∈ convexHull {a,b,c}) : MemClosedTriangle a b c p

theorem UniqueInterior_trianglePolygon_of_twoInterior_occupied
    (StrictlyConvexCCW P) (Injective P.vertex) (PrimitiveEdges P)
    (TwoInterior P q r) (MemClosedTriangle ear r)
    (OffTriangleBoundary q vᵢ vᵢ₊₁ r) :
    UniqueInterior (trianglePolygon q vᵢ vᵢ₊₁) r
```

Results exports: `results_OffTriangleBoundary`,
`results_UniqueInterior_trianglePolygon_of_twoInterior_occupied`,
`results_memClosedTriangle_of_mem_convexHull`.

**Prize progress:** occupied ear with `r` off the three ear edges inherits
`UniqueInterior r` as a `trianglePolygon`. Next: discharge triangle
`StrictlyConvexCCW` / `PrimitiveEdges`, apply I=1 ⇒ ear shoelace
`= 1 + B_ear/2 − 1` (expect `B_ear = 3` ⇒ `det = 3`), sum with empty-ear
`det = 1` to get polygon `shoelace = 2 + B/2 − 1`. Still **not** classical Pick:
Haar; EP→planar; full I=2 Pick-form open. Claude Platonic / Cube / MetricRegular /
EdgeVertices untouched.

| Item | Status |
|------|--------|
| Empty (of `r`) ears ⇒ `|det|=1` | Green |
| Occupied-ear `trianglePolygon` substrate | Green |
| Occupied-ear UniqueInterior (off boundary) | **Green** |
| Ear StrictlyConvexCCW / PrimitiveEdges / `det=3` | Open |
| B-bookkeeping → `shoelace = 2 + B/2 − 1` | Open |
| Shoelace = Haar | Open |
| Classical Pick | **Still FAIL** |


## Update 2026-09-25 (I=2 ear CCW / PrimitiveEdges / det=3 / Pick-form under uniqueness; still FAIL for classical Pick)

Landed in `EulersGem/LatticeFanInterior.lean` (honest names; **not** classical Pick):

```lean
theorem StrictlyConvexCCW_trianglePolygon
    (0 < latticeDet a b c) : StrictlyConvexCCW (trianglePolygon a b c)

theorem StrictlyConvexCCW_PrimitiveEdges_trianglePolygon_of_twoInterior_occupied
    … (OffTriangleBoundary …) :
    StrictlyConvexCCW T ∧ PrimitiveEdges T ∧ Injective T.vertex

theorem interiorFanDet_eq_three_of_twoInterior_occupied … :
    interiorFanDet P q i = 3

theorem shoelace_eq_two_add_B_div_two_sub_one_of_twoInterior_occupied
    … (OffTriangleBoundary …)
    (∀ j, MemClosedTriangle earⱼ r → j = i) :
    P.shoelace = 2 + B/2 − 1
```

Results exports: `results_StrictlyConvexCCW_trianglePolygon`,
`results_StrictlyConvexCCW_PrimitiveEdges_trianglePolygon_of_twoInterior_occupied`,
`results_interiorFanDet_eq_three_of_twoInterior_occupied`,
`results_shoelace_eq_two_add_B_div_two_sub_one_of_twoInterior_occupied`.

**Prize progress:** Fin-3 `StrictlyConvexCCW` from positive orientation; occupied
off-boundary ear inherits `PrimitiveEdges` via four-point edge-gcd lemmas; I=1 on
the ear triangle ⇒ `det=3`. Under an explicit uniqueness hyp, empty ears `det=1`
+ occupied `det=3` bookkeep to `shoelace = 2 + B/2 − 1`. Still **not** classical
Pick: ear-uniqueness discharge (cone disjointness); on-spoke I=2; Haar;
EP→planar. Claude Platonic / Cube / MetricRegular / EdgeVertices untouched.

| Item | Status |
|------|--------|
| Occupied-ear UniqueInterior (off boundary) | Green |
| Ear StrictlyConvexCCW / PrimitiveEdges | **Green** |
| Occupied-ear `det=3` via I=1 | **Green** |
| I=2 Pick-form under uniqueness hyp | **Green** |
| Discharge ear-uniqueness from OffTriangleBoundary | Open |
| On-spoke I=2 configurations | Open |
| Shoelace = Haar | Open |
| Classical Pick | **Still FAIL** |
