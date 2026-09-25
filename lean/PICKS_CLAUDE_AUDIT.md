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


## Update 2026-09-25 (ear-uniqueness discharged under OffTriangleBoundary; still FAIL for classical Pick)

Landed in `EulersGem/EarUniqueness.lean` (honest names; **not** classical Pick):

```lean
theorem latticeDet_pos_of_memClosedTriangle_offBoundary
    … (OffTriangleBoundary …) :
    0 < latticeDet v w r ∧ 0 < latticeDet q r w ∧ 0 < latticeDet q v r

theorem eq_of_mem_interiorFan_of_twoInterior_offBoundary
    … (OffTriangleBoundary on ear i) (MemClosedTriangle ear j r) :
    j = i

theorem shoelace_eq_two_add_B_div_two_sub_one_of_twoInterior_occupied_offBoundary
    … (OffTriangleBoundary …) :  -- no uniqueness hyp
    P.shoelace = 2 + B/2 − 1
```

Results exports: `results_eq_of_mem_interiorFan_of_twoInterior_offBoundary`,
`results_shoelace_eq_two_add_B_div_two_sub_one_of_twoInterior_occupied_offBoundary`
(plus prior uniqueness-hyp form retained).

**Prize progress:** cone/half-plane disjointness of distinct ears from apex `q`
under `OffTriangleBoundary` + Plücker + `ConvexCCW` + foreign-vertex via
`eq_vertices_or_r_of_mem_interiorFan_of_twoInterior`. I=2 Pick-form without
`huniq`. Still **not** classical Pick: on-spoke I=2; Haar; EP→planar.
Claude Platonic / Cube / MetricRegular / EdgeVertices untouched.

| Item | Status |
|------|--------|
| Occupied-ear UniqueInterior (off boundary) | Green |
| Ear StrictlyConvexCCW / PrimitiveEdges / det=3 | Green |
| I=2 Pick-form under uniqueness hyp | Green |
| Discharge ear-uniqueness from OffTriangleBoundary | **Green** |
| I=2 Pick-form without uniqueness hyp (needs Off) | **Green** |
| On-spoke I=2 configurations | Open |
| Shoelace = Haar | Open |
| Classical Pick | **Still FAIL** |


## Update 2026-09-25 (on-spoke case-split + edgeGcd=2; still FAIL for classical Pick)

Landed in `EulersGem/OnSpoke.lean` (honest names; **not** classical Pick):

```lean
theorem offBoundary_or_onSpoke_of_mem_interiorFan_of_twoInterior
    (TwoInterior P q r) (MemClosedTriangle earᵢ r) :
    OffTriangleBoundary earᵢ r ∨
      r ∈ edgeLatticePoints q vᵢ ∨
        r ∈ edgeLatticePoints vᵢ₊₁ q

theorem edgeGcd_eq_two_of_twoInterior_onSpoke
    (StrictlyConvexCCW P) (Injective P.vertex) (PrimitiveEdges P)
    (TwoInterior P q r) (r ∈ edgeLatticePoints q vₖ) (r ≠ q) (r ≠ vₖ) :
    edgeGcd q vₖ = 2
```

Results exports: `results_offBoundary_or_onSpoke_of_mem_interiorFan_of_twoInterior`,
`results_edgeGcd_eq_two_of_twoInterior_onSpoke`.

**Prize progress:** covering ear for I=2 is OffTriangleBoundary (already has
Pick-form) or on-spoke; occupied spoke has exactly one strict intermediate
(`edgeGcd=2`). Still **not** classical Pick: on-spoke det bookkeeping
(adjacent ears `det=2`, others `det=1`, sum `n+2`) and unified
`TwoInterior => shoelace = 2+B/2-1` open; Haar; EP→planar. Claude Platonic /
Cube / MetricRegular / EdgeVertices untouched.

| Item | Status |
|------|--------|
| I=2 Pick-form under OffTriangleBoundary (no uniq hyp) | Green |
| Case-split Off vs on-spoke | **Green** |
| Occupied spoke `edgeGcd=2` | **Green** |
| On-spoke det bookkeeping / unified I=2 Pick-form | Open |
| Shoelace = Haar | Open |
| Classical Pick | **Still FAIL** |


## Update 2026-09-25 (on-spoke edge helpers + adjacent-ear membership; still FAIL for classical Pick)

Landed in `EulersGem/OnSpoke.lean` (honest names; **not** classical Pick):

```lean
lemma edgeGcd_comm / mem_edgeLatticePoints_comm / mem_segment_of_mem_edgeLatticePoints
lemma eq_step_one_of_mem_edgeLatticePoints_of_edgeGcd_eq_two
lemma latticeDet_eq_two_mul_of_edgeGcd_eq_two_mem
lemma edgeGcd_eq_one_left_of_edgeGcd_eq_two_mem
lemma mem_interiorFan_of_onSpoke_left / mem_interiorFan_of_onSpoke_right
```

Results exports: `results_mem_interiorFan_of_onSpoke_{left,right}`,
`results_latticeDet_eq_two_mul_of_edgeGcd_eq_two_mem` (prior Off/onSpoke +
`edgeGcd=2` retained).

**Prize progress:** occupied spoke with `edgeGcd=2` has unique midpoint; fan
determinant along that spoke doubles as `det(q,v,w)=2·det(q,r,w)`; both adjacent
ears contain `r`. Still **not** classical Pick: adjacent-ear `det=2` via small-
triangle emptiness; non-adjacent ear exclusion; unified
`TwoInterior => shoelace = 2+B/2-1`; Haar; EP→planar. Claude Platonic / Cube /
MetricRegular / EdgeVertices untouched.

| Item | Status |
|------|--------|
| Case-split Off vs on-spoke | Green |
| Occupied spoke `edgeGcd=2` | Green |
| Spoke symmetry / midpoint / det-doubling | **Green** |
| Adjacent ears contain on-spoke `r` | **Green** |
| On-spoke adjacent `det=2` / exclusion / unified I=2 | Open |
| Shoelace = Haar | Open |
| Classical Pick | **Still FAIL** |

## Update 2026-09-25 (on-spoke det=2 + unified I=2 Pick-form; still FAIL for classical Pick)

Landed in `EulersGem/OnSpoke.lean` (honest names; **not** classical Pick):

```lean
theorem natAbs_latticeDet_eq_one_of_onSpoke_left/right
    (TwoInterior P q r) (r ∈ edgeLatticePoints q vₖ) … :
    Int.natAbs (latticeDet q r w) = 1   -- half-ear emptiness

theorem interiorFanDet_eq_two_of_onSpoke_left/right … :
    interiorFanDet P q k = 2           -- / prevIdx k = 2

theorem eq_of_mem_interiorFan_of_twoInterior_onSpoke … :
    j = k ∨ j = prevIdx k              -- non-adjacent exclusion

theorem shoelace_eq_two_add_B_div_two_sub_one_of_twoInterior_onSpoke … :
    P.shoelace = 2 + B/2 - 1

theorem shoelace_eq_two_add_B_div_two_sub_one_of_twoInterior … :
    P.shoelace = 2 + B/2 - 1           -- unified Off ∨ on-spoke
```

Results exports: `results_natAbs_latticeDet_eq_one_of_onSpoke_left`,
`results_interiorFanDet_eq_two_of_onSpoke_{left,right}`,
`results_eq_of_mem_interiorFan_of_twoInterior_onSpoke`,
`results_shoelace_eq_two_add_B_div_two_sub_one_of_twoInterior_onSpoke`,
`results_shoelace_eq_two_add_B_div_two_sub_one_of_twoInterior`.

**Prize progress:** under `TwoInterior`, covering ear is Off (det=3 path) or
on-spoke (adjacent dets=2, others=1); both give fan sum `n+2` and
`shoelace = 2 + B/2 − 1`. Still **not** classical Pick: shoelace ≠ Haar;
EP→planar Euler open; no triangulation existence; I>2 open. Claude Platonic /
Cube / MetricRegular / EdgeVertices untouched.

| Item | Status |
|------|--------|
| On-spoke half-ear `|det|=1` | **Green** |
| Adjacent ears `det=2` | **Green** |
| Non-adjacent exclusion | **Green** |
| Unified I=2 Pick-form (Off ∨ on-spoke) | **Green** |
| Shoelace = Haar | Open |
| EP → planar Euler | Open |
| Classical Pick | **Still FAIL** |


## Update 2026-09-25 (I≤2 Finset unify + I=3 two-ear scaffold; still FAIL for classical Pick)

Landed in `EulersGem/LatticeFanInduction.lean` (honest names; **not** classical Pick):

```lean
theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_two
    (↑S = interiorLatticePoints) (S.card ≤ 2) … :
    P.shoelace = #S + B/2 − 1

def ThreeInterior (q r s : ℤ × ℤ) : Prop

theorem threeInterior_of_finset_card_three … :
    ∃ q r s, ThreeInterior P q r s ∧ S = {q, r, s}

theorem eq_vertices_or_interior_of_mem_interiorFan … :
    p = q ∨ p = vᵢ ∨ p = vᵢ₊₁ ∨ p ∈ interiorLatticePoints

theorem interiorFanDet_eq_one_of_no_other_interior … :
    interiorFanDet P q i = 1

theorem UniqueInterior_trianglePolygon_of_threeInterior_occupied … :
    UniqueInterior (trianglePolygon q vᵢ vᵢ₊₁) r

theorem interiorFanDet_eq_three_of_threeInterior_occupied … :
    interiorFanDet P q i = 3

theorem shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_two_occupied
    … (i ≠ j) (Off ears for r and s) (uniqueness hyps) :
    P.shoelace = 3 + B/2 − 1
```

Results exports: `results_shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_two`,
`results_ThreeInterior`, `results_threeInterior_of_finset_card_three`,
`results_eq_vertices_or_interior_of_mem_interiorFan`,
`results_interiorFanDet_eq_one_of_no_other_interior`,
`results_interiorFanDet_eq_three_of_threeInterior_occupied`,
`results_shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_two_occupied`.

**Prize progress:** I∈{0,1,2} packaged as one Finset statement. I=3 scaffold:
general ear classification (any interior apex), empty-ear `|det|=1`, and
Pick-form under two distinct Off occupied ears (each I=1 via UniqueInterior
inheritance). Still **not** classical Pick: discharge ear-uniqueness for I=3;
same-ear occupation (I=2 on ear triangle); on-spoke I=3; Haar; EP→planar.
Claude Platonic / Cube / MetricRegular / EdgeVertices untouched.

| Item | Status |
|------|--------|
| Unified I=2 Pick-form (Off ∨ on-spoke) | Green |
| I∈{0,1,2} Finset unification | **Green** |
| `ThreeInterior` + Finset card=3 | **Green** |
| General ear lattice classification | **Green** |
| Empty-ear `|det|=1` (any I) | **Green** |
| I=3 Pick-form under two Off occupied ears | **Green** (uniqueness hyps) |
| Discharge I=3 ear-uniqueness / same-ear / on-spoke | Open |
| Shoelace = Haar | Open |
| EP → planar Euler | Open |
| Classical Pick | **Still FAIL** |

## Update 2026-09-25 (I=3 Off uniqueness discharge + same-ear; still FAIL for classical Pick)

Landed in `EulersGem/EarUniqueness.lean` + `EulersGem/LatticeFanInduction.lean`
(honest names; **not** classical Pick):

```lean
theorem eq_of_mem_interiorFan_of_offBoundary
    (q ∈ interiorLatticePoints) (OffTriangleBoundary earᵢ r)
    (MemClosedTriangle earⱼ r) :
    j = i   -- general cone/half-plane uniqueness (any I)

theorem shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_two_occupied_offBoundary
    (ThreeInterior) (i ≠ j) (Off ears for r and s, each exclusive) :
    P.shoelace = 3 + B/2 − 1   -- no uniqueness hyps

theorem TwoInterior_trianglePolygon_of_threeInterior_same_ear …
theorem interiorFanDet_eq_five_of_threeInterior_same_ear …  -- det=5

theorem shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_same_ear_offBoundary
    (ThreeInterior) (both r,s Off in ear i) :
    P.shoelace = 3 + B/2 − 1
```

Results exports: `results_eq_of_mem_interiorFan_of_offBoundary`,
`results_shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_two_occupied_offBoundary`,
`results_TwoInterior_trianglePolygon_of_threeInterior_same_ear`,
`results_interiorFanDet_eq_five_of_threeInterior_same_ear`,
`results_shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_same_ear_offBoundary`
(prior uniqueness-hyp two-ear form retained).

**Prize progress:** OffBoundary ear-uniqueness generalized beyond `TwoInterior` to
any interior apex (supporting half-plane + Plücker). I=3 two-distinct-ears
Pick-form without `huniq`. Same-ear occupation: ear is `TwoInterior`
`trianglePolygon` ⇒ reuse unified I=2 ⇒ `det=5`; other ears `det=1`; fan sum
`n+4`. Still **not** classical Pick: on-spoke I=3; Haar; EP→planar.
Claude Platonic / Cube / MetricRegular / EdgeVertices untouched.

| Item | Status |
|------|--------|
| I=3 Pick-form under two Off ears (uniqueness hyps) | Green |
| Discharge I=3 ear-uniqueness from OffBoundary | **Green** |
| I=3 two-ear Pick-form without uniqueness hyps | **Green** |
| Same-ear Off occupation → TwoInterior ear / det=5 | **Green** |
| Same-ear I=3 Pick-form | **Green** |
| On-spoke I=3 | Open |
| Shoelace = Haar | Open |
| EP → planar Euler | Open |
| Classical Pick | **Still FAIL** |


## Update 2026-09-25 (I=3 Off Finset unify; still FAIL for classical Pick)

Landed in `EulersGem/OnSpoke.lean` + `EulersGem/LatticeFanInduction.lean`
(honest names; **not** classical Pick):

```lean
theorem offBoundary_or_onSpoke_of_mem_interiorFan
    (r ∈ interiorLatticePoints) (MemClosedTriangle earᵢ r) :
    OffTriangleBoundary ∨ on-spoke   -- any I (TwoInterior specializes)

theorem shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_off
    (ThreeInterior) (Off ear for r) (Off ear for s) :  -- indices may coincide
    P.shoelace = 3 + B/2 − 1   -- same-ear ∨ two-ear case-split

theorem shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_off_exists
    (ThreeInterior) (∃ Off covering r) (∃ Off covering s) :
    P.shoelace = 3 + B/2 − 1

theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_eq_three
    (↑S = interior) (S.card = 3) (StrictlyConvexCCW) (PrimitiveEdges)
    (∃ q ∈ S, ∀ r ∈ S, r ≠ q → ∃ Off covering ear from q) :
    P.shoelace = #S + B/2 − 1
```

Results exports: `results_offBoundary_or_onSpoke_of_mem_interiorFan`,
`results_shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_off`,
`results_shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_off_exists`,
`results_shoelace_eq_cardI_add_B_div_two_sub_one_of_I_eq_three`
(prior two-ear / same-ear forms retained).

**Prize progress:** All Off I=3 configurations (two distinct Off ears + same-ear
Off occupation) packaged as one Finset `card=3` statement under a single
Off-apex hyp. Off vs on-spoke case-split generalized beyond `TwoInterior`.
Still **not** classical Pick: on-spoke I=3; Haar; EP→planar.
Claude Platonic / Cube / MetricRegular / EdgeVertices untouched.

| Item | Status |
|------|--------|
| General Off/on-spoke case-split (any I) | **Green** |
| Unified Off I=3 (same-ear ∨ two-ear) | **Green** |
| Finset `card=3` under Off-apex hyp | **Green** |
| On-spoke I=3 | Open |
| Shoelace = Haar | Open |
| EP → planar Euler | Open |
| Classical Pick | **Still FAIL** |


## Update 2026-09-25 (I=3 on-spoke one+Off-nonadjacent; still FAIL for classical Pick)

Landed in `EulersGem/LatticeFanInduction.lean` (honest names; **not** classical Pick):

```lean
lemma ne_endpoints_of_threeInterior_onSpoke
theorem edgeGcd_eq_two_of_threeInterior_onSpoke
    (ThreeInterior) (r on spoke k) (s ∉ that spoke) : edgeGcd = 2
theorem exists_offBoundary_or_onSpoke_covering_of_threeInterior_left/right
theorem interiorFanDet_eq_two_of_threeInterior_onSpoke_{left,right}
    (s absent from adjacent ear) : interiorFanDet = 2
theorem shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_onSpoke_off
    (ThreeInterior) (r on spoke k) (s Off in ear j non-adjacent) :
    P.shoelace = 3 + B/2 − 1
```

Results exports: `results_ne_endpoints_of_threeInterior_onSpoke`,
`results_edgeGcd_eq_two_of_threeInterior_onSpoke`,
`results_exists_offBoundary_or_onSpoke_covering_of_threeInterior_left`,
`results_interiorFanDet_eq_two_of_threeInterior_onSpoke_{left,right}`,
`results_shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_onSpoke_off`.

**Prize progress:** I=3 on-spoke substrate: classify coverings Off/on-spoke;
occupied spoke with companion off-spoke has `edgeGcd=2`; half-ear emptiness +
doubling give adjacent `det=2`; combine with Off ear `det=3` for non-adjacent
companion ⇒ fan sum `n+4` Pick-form. Still **not** classical Pick: same-spoke
both-on-spoke / Off-in-adjacent-ear; full Finset card=3 without Off-apex hyp;
Haar; EP→planar. Claude Platonic / Cube / MetricRegular / EdgeVertices untouched.

| Item | Status |
|------|--------|
| Off/on-spoke covering classification (ThreeInterior) | **Green** |
| `edgeGcd=2` when companion off spoke | **Green** |
| Adjacent det=2 under ThreeInterior on-spoke | **Green** |
| I=3 Pick-form on-spoke + Off non-adjacent | **Green** |
| Same-spoke / both-on-spoke / Off-adjacent | Open |
| Finset card=3 without Off-apex hyp | Open |
| Shoelace = Haar | Open |
| EP → planar Euler | Open |
| Classical Pick | **Still FAIL** |


## Update 2026-09-25 (I=3 same-spoke edgeGcd=3 + adjacent det=3; still FAIL for classical Pick)

Landed in `EulersGem/OnSpoke.lean` + `EulersGem/LatticeFanInduction.lean` (honest names; **not** classical Pick):

```lean
lemma eq_steps_of_mem_edgeLatticePoints_of_edgeGcd_eq_three
lemma latticeDet_eq_three_mul_of_edgeGcd_eq_three_step_one
lemma edgeGcd_eq_one_of_edgeGcd_eq_three_step_one
theorem edgeGcd_eq_three_of_threeInterior_sameSpoke
    (ThreeInterior) (r,s both on spoke k) : edgeGcd = 3
theorem interiorFanDet_eq_three_of_threeInterior_sameSpoke_{left,right}
    : adjacent ears det = 3
```

Results exports: `results_edgeGcd_eq_three_of_threeInterior_sameSpoke`,
`results_interiorFanDet_eq_three_of_threeInterior_sameSpoke_{left,right}`.

**Prize progress:** Same-spoke I=3 substrate: both on one spoke ⇒ `edgeGcd=3`;
trisect + empty third-ear ⇒ adjacent `det=3`. Full same-spoke Pick-form (fan sum
`n+4`) still needs foreign-ear exclusion for on-spoke `{r,s}`. Still **not**
classical Pick: Off-adjacent (det=4); two-spoke; Off-free Finset card=3; Haar;
EP→planar. Claude Platonic / Cube / MetricRegular / EdgeVertices untouched.

| Item | Status |
|------|--------|
| Same-spoke `edgeGcd=3` | **Green** |
| Same-spoke adjacent `det=3` | **Green** |
| Same-spoke Pick-form (fan sum n+4) | Open (foreign-ear exclusion) |
| Off-adjacent (det=4 bookkeeping) | Open |
| Two different spokes | Open |
| Finset card=3 without Off-apex hyp | Open |
| Shoelace = Haar | Open |
| EP → planar Euler | Open |
| Classical Pick | **Still FAIL** |



## Update 2026-09-25 (I=3 same-spoke foreign-ear exclusion + Pick-form; still FAIL for classical Pick)

Landed in `EulersGem/OnSpoke.lean` + `EulersGem/LatticeFanInduction.lean` (honest names; **not** classical Pick):

```lean
lemma eq_vertex_of_mem_edgeLatticePoints_of_edgeGcd_eq_three
lemma OffTriangleBoundary_of_mem_interiorFan_of_threeInterior_sameSpoke_ne_adjacent
theorem eq_of_mem_interiorFan_of_threeInterior_sameSpoke
    -- foreign ears (not k, not prevIdx k) contain neither r nor s
theorem interiorFanDet_eq_one_of_threeInterior_sameSpoke_not_adjacent
    -- empty ⇒ det = 1
theorem shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_sameSpoke
    (ThreeInterior) (r,s both on spoke k) :
    P.shoelace = 3 + B/2 − 1   -- fan sum n+4 = 3+3+(n-2)
```

Results exports: `results_eq_of_mem_interiorFan_of_threeInterior_sameSpoke`,
`results_interiorFanDet_eq_one_of_threeInterior_sameSpoke_not_adjacent`,
`results_shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_sameSpoke`
(prior edgeGcd=3 / adjacent det=3 retained).

**Prize progress:** Same-spoke I=3 closed: foreign-ear exclusion via Off+uniqueness
(gcd=3 endpoint uniqueness; mixed gcd=2/3 forces vertex=interior contradiction or
edgeGcd=4); empty foreign ⇒ det=1; adjacent det=3 ⇒ shoelace Pick-form.
Still **not** classical Pick: Off-adjacent (det=4); two-spoke; Off-free Finset
card=3; Haar; EP→planar. Claude Platonic / Cube / MetricRegular / EdgeVertices untouched.

| Item | Status |
|------|--------|
| Same-spoke `edgeGcd=3` | **Green** |
| Same-spoke adjacent `det=3` | **Green** |
| Same-spoke foreign-ear exclusion | **Green** |
| Same-spoke Pick-form (fan sum n+4) | **Green** |
| Off-adjacent (det=4 bookkeeping) | Open |
| Two different spokes | Open |
| Finset card=3 without Off-apex hyp | Open |
| Shoelace = Haar | Open |
| EP → planar Euler | Open |
| Classical Pick | **Still FAIL** |


## Update 2026-09-25 (I=3 Finset covered unify Off∨onSpoke∨sameSpoke; still FAIL for classical Pick)

Landed in `EulersGem/LatticeFanInduction.lean` (honest names; **not** classical Pick):

```lean
def ThreeInteriorCovered (q r s : ℤ × ℤ) : Prop
    -- Off (same-ear ∨ two-ear) ∨ on-spoke+Off-nonadjacent ∨ same-spoke

theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_eq_three_covered
    (↑S = interior) (S.card = 3) (StrictlyConvexCCW) (PrimitiveEdges)
    (∃ q r s, S = {q,r,s} ∧ ThreeInteriorCovered P q r s) :
    P.shoelace = #S + B/2 − 1
```

Results exports: `results_ThreeInteriorCovered`,
`results_shoelace_eq_cardI_add_B_div_two_sub_one_of_I_eq_three_covered`
(prior Off-only Finset card=3 + sameSpoke / onSpoke_off retained).

**Prize progress:** Three green I=3 geometric configurations (all-Off, on-spoke+Off
nonadjacent, same-spoke) folded into one Finset `card=3` statement under a covered
hyp (weaker than Off-only apex). Still **not** classical Pick: Off-adjacent
(`det=4`); two distinct spokes; Off-free Finset card=3; Haar; EP→planar.
Claude Platonic / Cube / MetricRegular / EdgeVertices untouched.

| Item | Status |
|------|--------|
| Same-spoke Pick-form (fan sum n+4) | Green |
| Off I=3 (same-ear ∨ two-ear) | Green |
| On-spoke + Off nonadjacent | Green |
| Finset card=3 under covered hyp | **Green** |
| Off-adjacent (det=4 bookkeeping) | Open |
| Two different spokes | Open |
| Finset card=3 without Off/covered hyp | Open |
| Shoelace = Haar | Open |
| EP → planar Euler | Open |
| Classical Pick | **Still FAIL** |



## Update 2026-09-25 (I=3 Off-adjacent-left det=4 + Pick-form; still FAIL for classical Pick)

Landed in `EulersGem/OnSpoke.lean` + `EulersGem/LatticeFanInterior.lean` +
`EulersGem/LatticeFanInduction.lean` (honest names; **not** classical Pick):

```lean
lemma latticeDet_add_of_mem_edgeLatticePoints
lemma latticeDet_eq_two_mul_of_edgeGcd_eq_two_mem_bc
lemma memClosedTriangle_split_of_edgeGcd_eq_two_mem
theorem latticeDet_eq_three_of_subset_four_off
theorem mem_diagonal_of_threeInterior_onSpoke_off_adjacent_left
theorem edgeGcd_eq_two_of_diagonal_threeInterior_onSpoke_off_adjacent_left
theorem interiorFanDet_eq_four_of_threeInterior_onSpoke_off_adjacent_left
    -- double-doubling: spoke mid + diagonal mid ⇒ det = 4
theorem shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_onSpoke_off_adjacent_left
    -- fan sum n+4 (det 4+2+1…)
-- ThreeInteriorCovered extended with Off-adjacent-left disjunct
```

Results exports: `results_interiorFanDet_eq_four_of_threeInterior_onSpoke_off_adjacent_left`,
`results_shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_onSpoke_off_adjacent_left`,
updated `results_ThreeInteriorCovered` / covered Finset card=3.

**Prize progress:** Off-adjacent-left closed via diagonal midpoint + double-doubling.
Still **not** classical Pick: Off-adjacent-right (`s` in ear `prevIdx k`); two-spoke;
Off-free Finset card=3; Haar; EP→planar.
Claude Platonic / Cube / MetricRegular / EdgeVertices untouched.

| Item | Status |
|------|--------|
| Off-adjacent-left `det=4` + Pick-form | **Green** |
| Finset card=3 under covered (+ Off-adj-left) | **Green** |
| Off-adjacent-right | Open |
| Two different spokes | Open |
| Finset card=3 without covered hyp | Open |
| Shoelace = Haar | Open |
| EP → planar Euler | Open |
| Classical Pick | **Still FAIL** |


## Update 2026-09-25 (I=3 Off-adjacent-right det=4 + Pick-form; still FAIL for classical Pick)

Landed in `EulersGem/OnSpoke.lean` + `EulersGem/LatticeFanInduction.lean` (honest
names; **not** classical Pick). Mirror of Off-adjacent-left via AC-midpoint
helpers:

```lean
lemma latticeDet_add_of_mem_edgeLatticePoints_ac
lemma memClosedTriangle_split_of_edgeGcd_eq_two_mem_ac
lemma memClosedTriangle_of_memClosedTriangle_of_edgeGcd_eq_two_mem_ac_right
lemma mem_edgeLatticePoints_of_memClosedTriangle_both_halves_ac
theorem mem_diagonal_of_threeInterior_onSpoke_off_adjacent_right
theorem edgeGcd_eq_two_of_diagonal_threeInterior_onSpoke_off_adjacent_right
theorem interiorFanDet_eq_four_of_threeInterior_onSpoke_off_adjacent_right
    -- double-doubling on ear prevIdx k
theorem shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_onSpoke_off_adjacent_right
-- ThreeInteriorCovered extended with Off-adjacent-right disjunct
```

Results exports: `results_interiorFanDet_eq_four_of_threeInterior_onSpoke_off_adjacent_right`,
`results_shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_onSpoke_off_adjacent_right`,
updated covered Finset card=3.

**Prize progress:** Off-adjacent-right closed (mirror of left). Still **not**
classical Pick: two-spoke; Off-free Finset card=3; Haar; EP→planar.
Claude Platonic / Cube / MetricRegular / EdgeVertices untouched.

| Item | Status |
|------|--------|
| Off-adjacent-left `det=4` + Pick-form | **Green** |
| Off-adjacent-right `det=4` + Pick-form | **Green** |
| Finset card=3 under covered (+ Off-adj-left/right) | **Green** |
| Two different spokes | Open |
| Finset card=3 without covered hyp | Open |
| Shoelace = Haar | Open |
| EP → planar Euler | Open |
| Classical Pick | **Still FAIL** |


## Update 2026-09-25 (I=3 non-adjacent two-spoke Pick-form; still FAIL for classical Pick)

Landed in `EulersGem/LatticeFanInduction.lean` (honest names; **not** classical Pick):

```lean
theorem eq_of_mem_interiorFan_of_threeInterior_twoSpoke
    -- r on spoke k occupies only ears {k, prevIdx k}
theorem interiorFanDet_eq_one_of_threeInterior_twoSpoke_not_adjacent
theorem shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_twoSpoke_nonadjacent
    (ThreeInterior) (r on spoke k) (s on spoke m)
    (m ≠ k) (m ≠ nextIdx k) (m ≠ prevIdx k) :
    P.shoelace = 3 + B/2 − 1   -- four ears det=2; fan sum n+4
-- ThreeInteriorCovered extended with two-spoke-nonadjacent disjunct
```

Results exports: `results_shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_twoSpoke_nonadjacent`,
`results_eq_of_mem_interiorFan_of_threeInterior_twoSpoke`,
updated covered Finset card=3.

**Prize progress:** Non-adjacent two-spoke closed (two pairs of det=2 ears). Still **not**
classical Pick: adjacent two-spoke (shared-ear det=4); Off-free Finset card=3; Haar;
EP→planar. Claude Platonic / Cube / MetricRegular / EdgeVertices untouched.

| Item | Status |
|------|--------|
| Off-adjacent-left/right `det=4` + Pick-form | Green |
| Non-adjacent two-spoke Pick-form | **Green** |
| Finset card=3 under covered (+ two-spoke-nonadj) | **Green** |
| Adjacent two-spoke (shared-ear det=4) | Open |
| Finset card=3 without covered hyp | Open |
| Shoelace = Haar | Open |
| EP → planar Euler | Open |
| Classical Pick | **Still FAIL** |

## Update 2026-09-25 (I=3 adjacent two-spoke vacuous under PrimitiveEdges; still FAIL for classical Pick)

Landed in `EulersGem/LatticeFanInduction.lean` (honest names; **not** classical Pick):

```lean
lemma nextIdx_ne_prevIdx
lemma latticeDet_eq_zero_of_mem_edgeLatticePoints_both
lemma edgeGcd_ge_two_of_two_spoke_midpoints
    -- midpoints on two spokes ⇒ tip-chord edgeGcd ≥ 2
theorem false_of_threeInterior_twoSpoke_adjacent_next
theorem false_of_threeInterior_twoSpoke_adjacent_prev
theorem interiorFanDet_eq_four_of_threeInterior_twoSpoke_adjacent_next
    -- vacuous (False.elim); geometric intent: |det(q,r,s)|=1 + double-doubling
theorem interiorFanDet_eq_two_of_threeInterior_twoSpoke_adjacent_next_outer
theorem interiorFanDet_eq_one_of_threeInterior_twoSpoke_adjacent_next_foreign
theorem shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_twoSpoke_adjacent
    (ThreeInterior) (r on spoke k) (s on spoke m)
    (m = nextIdx k ∨ m = prevIdx k) :
    P.shoelace = 3 + B/2 − 1   -- vacuous under PrimitiveEdges
-- ThreeInteriorCovered extended with two-spoke-adjacent disjunct
```

Results exports: `results_shoelace_eq_three_add_B_div_two_sub_one_of_threeInterior_twoSpoke_adjacent`,
`results_false_of_threeInterior_twoSpoke_adjacent_next`,
`results_interiorFanDet_eq_four_of_threeInterior_twoSpoke_adjacent_next`,
updated covered Finset card=3.

**Prize progress:** Adjacent two-spoke closed under standing `PrimitiveEdges` hyp:
both spokes have unique midpoints ⇒ shared base edge has lattice midpoint ⇒
`edgeGcd ≥ 2`, contradicting primitivity; Pick-form holds vacuously. (Absent
primitivity the shared ear would be `det = 4` via `|det(q,r,s)|=1` + double-doubling,
outers `det = 2`, foreign `det = 1`, with `B = n+1` restoring Pick-form.)
Still **not** classical Pick: Off-free Finset card=3; Haar; EP→planar.
Claude Platonic / Cube / MetricRegular / EdgeVertices untouched.

| Item | Status |
|------|--------|
| Off-adjacent-left/right `det=4` + Pick-form | Green |
| Non-adjacent two-spoke Pick-form | Green |
| Adjacent two-spoke (vacuous under PrimitiveEdges) | **Green** |
| Finset card=3 under covered (+ two-spoke-adj) | **Green** |
| Finset card=3 without covered hyp | Open |
| Shoelace = Haar | Open |
| EP → planar Euler | Open |
| Classical Pick | **Still FAIL** |

## Update 2026-09-25 (I=3 Off-free Finset card=3 via Covered-of-ThreeInterior; still FAIL for classical Pick)

Landed in `EulersGem/LatticeFanInduction.lean` (honest names; **not** classical Pick):

```lean
lemma exists_onSpoke_of_covering_class
lemma off_ear_rel_of_spoke
theorem ThreeInteriorCovered_of_threeInterior
    (StrictlyConvexCCW) (Injective) (PrimitiveEdges) (ThreeInterior P q r s) :
    ThreeInteriorCovered P q r s
-- ThreeInteriorCovered extended with Off+onSpoke duals (nonadj / adj-left / adj-right)
theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_eq_three
    -- geometric only: no Off-apex / Covered witness hyp
theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_eq_three_off
    -- former Off-apex Finset theorem (renamed)
```

Results exports: `results_ThreeInteriorCovered_of_threeInterior`,
`results_shoelace_eq_cardI_add_B_div_two_sub_one_of_I_eq_three` (geometric),
`results_shoelace_eq_cardI_add_B_div_two_sub_one_of_I_eq_three_off` (Off-apex),
updated Covered docstring.

**Prize progress:** Off-free Finset `card = 3` closed — every `ThreeInterior` is
`ThreeInteriorCovered` by covering-ear + Off/on-spoke exhaustion (same/two-ear Off,
onSpoke+Off duals, sameSpoke, twoSpoke). Geometric Finset Pick-form needs only
injective + `PrimitiveEdges` + `StrictlyConvexCCW`. Still **not** classical Pick:
Haar; EP→planar; general `I`. Claude Platonic / Cube / MetricRegular / EdgeVertices
untouched.

| Item | Status |
|------|--------|
| Off-adjacent-left/right `det=4` + Pick-form | Green |
| Non-adjacent / adjacent two-spoke | Green |
| Finset card=3 under covered | Green |
| `ThreeInteriorCovered_of_threeInterior` | **Green** |
| Finset card=3 without covered hyp (geometric) | **Green** |
| Shoelace = Haar | Open |
| EP → planar Euler | Open |
| Classical Pick | **Still FAIL** |

## Update 2026-09-25 (general-I fan-ear induction scaffold; still FAIL for classical Pick)

Landed in `EulersGem/LatticeFanInduction.lean` (honest names; **not** classical Pick):

```lean
theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_three
    -- unify I∈{0,1,2,3} geometric Finset Pick-form
noncomputable def earOffInterior / spokeInterior
theorem card_earOffInterior_lt
    -- induction fuel: #(ear Off-interior) < #S when q ∈ S
theorem exists_offBoundary_or_onSpoke_covering_of_mem_interior
theorem exists_offBoundary_or_onSpoke_covering_of_mem_finset
lemma shoelace_trianglePolygon_eq_half_natAbs_det
theorem sum_ear_shoelace_eq_shoelace
    -- ∑ᵢ (trianglePolygon q vᵢ vᵢ₊₁).shoelace = P.shoelace (under InteriorFanDetsPos)
theorem pick_form_of_sum_ear_pick_forms
theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_fan_ear_IH
    -- conditional: ear IH + B/I bookkeeping ⇒ polygon Pick-form
theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_three_induction_base
```

Results exports: `results_shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_three`,
`results_earOffInterior` / `results_spokeInterior`, `results_card_earOffInterior_lt`,
`results_exists_offBoundary_or_onSpoke_covering_of_mem_interior`,
`results_sum_ear_shoelace_eq_shoelace`,
`results_shoelace_eq_cardI_add_B_div_two_sub_one_of_fan_ear_IH`.

**Prize progress:** General-I induction scaffold green — I≤3 unified as induction
base; ear/spoke partition defs + card decrease + covering; fan ear area sum;
conditional induction step assuming ear Pick-forms + bookkeeping identity.
Still **not** classical Pick: discharge ear IH for general I; prove `hbook` from
spoke/gcd B arithmetic; Haar; EP→planar.
Claude Platonic / Cube / MetricRegular / EdgeVertices untouched.

| Item | Status |
|------|--------|
| Finset card=3 geometric (Off-free) | Green |
| I≤3 Finset unify | **Green** |
| `earOffInterior` / `spokeInterior` + card↓ | **Green** |
| Covering Off/on-spoke for general interior | **Green** |
| `sum_ear_shoelace_eq_shoelace` | **Green** |
| Conditional fan-ear IH Pick-form | **Green** (hyps: ear IH + hbook) |
| Discharge ear IH / prove hbook | Open |
| Shoelace = Haar | Open |
| EP → planar Euler | Open |
| Classical Pick | **Still FAIL** |

## Update 2026-09-25 (hbook B-arithmetic substrate; still FAIL for classical Pick)

Landed in `EulersGem/LatticeFanInduction.lean` (honest names; **not** classical Pick):

```lean
lemma cross_eq_zero_of_cross_eq_zero_both
lemma eq_of_mem_edgeLatticePoints_ab_bc
lemma eq_of_mem_edgeLatticePoints_bc_ca
lemma eq_of_mem_edgeLatticePoints_ca_ab
lemma boundaryLatticePoints_trianglePolygon
lemma edgeLatticePoints_ab_inter_bc / bc_inter_ca / ca_inter_ab
theorem B_trianglePolygon_eq_sum_edgeGcd
    -- nondeg triangle: B = edgeGcd(ab)+edgeGcd(bc)+edgeGcd(ca)
theorem B_trianglePolygon_ear_of_primitive_base
    -- parent PrimitiveEdges ⇒ ear B = gcd(q,vᵢ)+gcd(vᵢ₊₁,q)+1
theorem hbook_of_partition_and_spokeGcd
    -- pure ℚ: partition + spoke cards = gcd−1 + ear B formula ⇒ hbook
theorem hbook_of_fan_ear_partition
    -- geometric: discharges ear B from PrimitiveEdges + InteriorFanDetsPos
```

Results exports: `results_B_trianglePolygon_eq_sum_edgeGcd`,
`results_B_trianglePolygon_ear_of_primitive_base`,
`results_hbook_of_partition_and_spokeGcd`,
`results_hbook_of_fan_ear_partition`.

**Prize progress:** Triangle B-arithmetic and conditional hbook identity green.
Still **not** classical Pick: discharge `hpart` (earOff⊔spoke partition of `S\\{q}`)
and `hspoke` (`#(spokeInterior)=edgeGcd−1`); ear IH for general I / I=4;
Haar; EP→planar.
Claude Platonic / Cube / MetricRegular / EdgeVertices untouched.

| Item | Status |
|------|--------|
| Conditional fan-ear IH Pick-form | Green (hyps: ear IH + hbook) |
| Triangle `B = ∑ edgeGcd` | **Green** |
| Ear B under parent PrimitiveEdges | **Green** |
| Conditional hbook (partition + spoke gcd cards) | **Green** |
| Discharge partition / spoke cards | Open |
| I=4 geometric Finset Pick-form | Open |
| Shoelace = Haar | Open |
| EP → planar Euler | Open |
| Classical Pick | **Still FAIL** |

## Update 2026-09-25 (hpart + hspoke discharged; still FAIL for classical Pick)

Landed in `EulersGem/LatticeFanInduction.lean` (honest names; **not** classical Pick):

```lean
theorem mem_interiorLatticePoints_of_mem_open_spoke
theorem card_spokeInterior_eq_edgeGcd_sub_one
theorem hspoke_of_interior_finset
    -- #(spokeInterior) = edgeGcd − 1 when S = interior
theorem eq_of_mem_edgeLatticePoints_two_spokes
theorem card_eq_one_add_earOff_add_spoke
theorem hpart_of_interior_finset
    -- S.card = 1 + ∑ earOff + ∑ spoke
theorem hbook_of_fan_ear_partition_of_interior
    -- discharged hbook under interior Finset (hpart + hspoke)
```

Results exports: `results_hspoke_of_interior_finset`,
`results_hpart_of_interior_finset`,
`results_hbook_of_fan_ear_partition_of_interior`.

**Prize progress:** fan-ear hbook arithmetic fully discharged for the geometric
interior Finset (partition + spoke-gcd cards). Conditional fan-ear Pick-form now
needs only ear IH. Still **not** classical Pick: ear IH / I=4 Finset Pick-form;
Haar; EP→planar.
Claude Platonic / Cube / MetricRegular / EdgeVertices untouched.

| Item | Status |
|------|--------|
| Conditional fan-ear IH Pick-form | Green (hyps: ear IH + hbook) |
| Triangle `B = ∑ edgeGcd` | Green |
| Ear B under parent PrimitiveEdges | Green |
| Conditional hbook (partition + spoke gcd cards) | Green |
| Discharge `hpart` (earOff⊔spoke partition) | **Green** |
| Discharge `hspoke` (`#(spokeInterior)=edgeGcd−1`) | **Green** |
| Discharged hbook for interior Finset | **Green** |
| I=4 geometric Finset Pick-form / ear IH | Open |
| Shoelace = Haar | Open |
| EP → planar Euler | Open |
| Classical Pick | **Still FAIL** |


## Update 2026-09-25 (earOff ↔ triangle interior + I=4 spokes-empty; still FAIL for classical Pick)

Landed in `EulersGem/LatticeFanInduction.lean` (honest names; **not** classical Pick):

```lean
lemma mem_interiorLatticePoints_trianglePolygon_iff
theorem coe_earOffInterior_eq_interiorLatticePoints_trianglePolygon
    -- ↑(earOffInterior q i S) = (trianglePolygon q vᵢ vᵢ₊₁).interiorLatticePoints
theorem card_earOffInterior_le_three_of_card_eq_four
theorem edgeGcd_eq_one_of_spokeInterior_empty
theorem PrimitiveEdges_trianglePolygon_ear_of_spokeInterior_empty
theorem shoelace_trianglePolygon_ear_eq_card_earOff_add_B_div_two_sub_one_of_I_le_three
    -- ear IH under empty adjacent spokes + #earOff ≤ 3 via I≤3
theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_eq_four_of_spokes_empty
theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_four_of_spokes_empty
```

Results exports: `results_coe_earOffInterior_eq_interiorLatticePoints_trianglePolygon`,
`results_card_earOffInterior_le_three_of_card_eq_four`,
`results_edgeGcd_eq_one_of_spokeInterior_empty`,
`results_PrimitiveEdges_trianglePolygon_ear_of_spokeInterior_empty`,
`results_shoelace_trianglePolygon_ear_eq_card_earOff_add_B_div_two_sub_one_of_I_le_three`,
`results_shoelace_eq_cardI_add_B_div_two_sub_one_of_I_eq_four_of_spokes_empty`,
`results_shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_four_of_spokes_empty`.

**Prize progress:** geometric identification of `earOffInterior` with ear-triangle
interior; parent `#S=4` ⇒ `#earOff≤3`; empty spokes ⇒ ear inherits `PrimitiveEdges`
⇒ apply I≤3 Pick-form on ears; discharged hbook + ear IH ⇒ I=4 (and I≤4) under
spokes-empty apex. Still **not** classical Pick: I=4 without spokes-empty hyp
(non-primitive ear sides / triangle Pick without `PrimitiveEdges`); Haar; EP→planar.
Claude Platonic / Cube / MetricRegular / EdgeVertices untouched.

| Item | Status |
|------|--------|
| Discharged hbook for interior Finset | Green |
| `earOffInterior` = triangle interior | **Green** |
| `#earOff ≤ 3` when `#S = 4` | **Green** |
| Ear `PrimitiveEdges` under empty spokes | **Green** |
| Ear I≤3 Pick-form under empty spokes | **Green** |
| I=4 / I≤4 under spokes-empty apex | **Green** |
| I=4 without spokes-empty hyp | Open |
| Shoelace = Haar | Open |
| EP → planar Euler | Open |
| Classical Pick | **Still FAIL** |


## Update 2026-09-25 (edge-split substrate toward non-primitive ears; still FAIL for classical Pick)

Landed in `EulersGem/LatticeFanTrianglePick.lean` (honest names; **not** classical Pick):

```lean
def edgeStep
lemma edgeStep_mem_edgeLatticePoints / edgeStep_ne_left / edgeStep_ne_right
lemma edgeGcd_edgeStep_left / edgeGcd_edgeStep_right
lemma latticeDet_edgeStep_mul / latticeDet_edgeStep_pos / latticeDet_edgeStep_right_pos
lemma shoelace_add_of_edgeStep
lemma B_add_of_edgeStep  -- needs edgeGcd(edgeStep,c)=1
theorem edgeGcd_eq_one_of_empty_interior_edgeStep
```

Results exports: `results_edgeStep_mem_edgeLatticePoints`,
`results_edgeGcd_edgeStep_left/right`, `results_shoelace_add_of_edgeStep`,
`results_B_add_of_edgeStep`, `results_edgeGcd_eq_one_of_empty_interior_edgeStep`.

**Prize progress:** edge-split arithmetic for dropping `PrimitiveEdges` on triangle
ears. Empty-interior ⇒ new chord after `edgeStep` is primitive. Still **not**
classical Pick / hyp-light I=4: need EmptyInterior inheritance on sub-triangles +
`|det|` induction for empty (then I≤2) triangle Pick without PrimitiveEdges; then
ear IH under nonempty spokes; then drop spokes-empty hyp on I=4.
Claude Platonic / Cube / MetricRegular / EdgeVertices untouched.

| Item | Status |
|------|--------|
| I=4 / I≤4 under spokes-empty apex | Green |
| `edgeStep` + gcd / det / shoelace split | **Green** |
| B-additivity of edge-step (prim chord) | **Green** |
| Empty-interior ⇒ `edgeGcd(edgeStep,c)=1` | **Green** |
| Empty-interior triangle Pick w/o PrimitiveEdges | Open |
| I≤2 triangle Pick w/o PrimitiveEdges | Open |
| I=4 without spokes-empty hyp | Open |
| Shoelace = Haar | Open |
| EP → planar Euler | Open |
| Classical Pick | **Still FAIL** |



## Update 2026-09-25 (empty-interior triangle Pick w/o PrimitiveEdges; still FAIL for classical Pick)

Landed in `EulersGem/LatticeFanTrianglePick.lean` (honest names; **not** classical Pick):

```lean
theorem EmptyInterior_trianglePolygon_of_edgeStep_left/right
    -- EmptyInterior inherits across edgeStep splits

theorem shoelace_eq_B_div_two_sub_one_of_empty_interior_triangle
    (0 < latticeDet a b c) (EmptyInterior (trianglePolygon a b c)) :
    (trianglePolygon a b c).shoelace = B/2 - 1
    -- no PrimitiveEdges hyp; induction on |det| via edgeStep
```

Results exports: `results_EmptyInterior_trianglePolygon_of_edgeStep_{left,right}`,
`results_shoelace_eq_B_div_two_sub_one_of_empty_interior_triangle`
(prior edgeStep substrate retained).

**Prize progress:** first triangle shoelace Pick-form that drops `PrimitiveEdges`.
Base uses existing empty-interior convex form when all edges are primitive; step
splits a non-primitive edge at `edgeStep`, inherits EmptyInterior on both
sub-triangles (det-positivity OffBoundary), applies IH on strictly smaller
`|det|`, and reassembles via shoelace/B additivity with primitive new chord.
Still **not** classical Pick: I ≤ 2 triangle without PrimitiveEdges; I = 4
Finset without spokes-empty apex; Haar; EP→planar.
Claude Platonic / Cube / MetricRegular / EdgeVertices untouched.

| Item | Status |
|------|--------|
| `edgeStep` + gcd / det / shoelace / B split | Green |
| Empty-interior ⇒ `edgeGcd(edgeStep,c)=1` | Green |
| EmptyInterior inheritance across edgeStep | **Green** |
| Empty-interior triangle Pick w/o PrimitiveEdges | **Green** |
| I≤2 triangle Pick w/o PrimitiveEdges | Open |
| I=4 without spokes-empty hyp | Open |
| Shoelace = Haar | Open |
| EP → planar Euler | Open |
| Classical Pick | **Still FAIL** |


## Update 2026-09-25 (UniqueInterior triangle substrate w/o PrimitiveEdges; still FAIL for classical Pick)

Landed in `EulersGem/LatticeFanTrianglePick.lean` (honest names; **not** classical Pick):

```lean
lemma B_add_of_edgeStep_of_gcd
    -- B₁ + B₂ = B + 2·edgeGcd(edgeStep,c)

theorem mem_interiorLatticePoints_of_strict_mem_edgeStep_chord
    -- open chord lattice points are parent-interior

theorem edgeGcd_le_two_of_uniqueInterior_edgeStep
    -- UniqueInterior ⇒ edgeGcd(edgeStep,c) ≤ 2

theorem UniqueInterior_trianglePolygon_of_edgeStep_{left,right}
theorem EmptyInterior_edgeStep_{left,right}_of_uniqueInterior_{right,left}
theorem EmptyInterior_edgeStep_both_of_uniqueInterior_edgeGcd_eq_two
    -- g=2 ⇒ both halves empty (unique point on chord)
```

Results exports: `results_B_add_of_edgeStep_of_gcd`,
`results_mem_interiorLatticePoints_of_strict_mem_edgeStep_chord`,
`results_edgeGcd_le_two_of_uniqueInterior_edgeStep`,
`results_UniqueInterior_trianglePolygon_of_edgeStep_{left,right}`,
`results_EmptyInterior_edgeStep_both_of_uniqueInterior_edgeGcd_eq_two`.

**Prize progress:** UniqueInterior edge-split substrate green (B-add for arbitrary
chord gcd; chord points interior; gcd ≤ 2; half UniqueInterior/EmptyInterior
inheritance; both-empty when chord gcd = 2). Still **not** classical Pick: full
UniqueInterior triangle Pick without PrimitiveEdges (need g=1 locate-half +
`|det|` induction reassembly); I ≤ 2 without PrimitiveEdges; I = 4 without
spokes-empty; Haar; EP→planar.
Claude Platonic / Cube / MetricRegular / EdgeVertices untouched.

| Item | Status |
|------|--------|
| Empty-interior triangle Pick w/o PrimitiveEdges | Green |
| UniqueInterior edge-split substrate (B/chord/gcd≤2/inherit/g=2 empty) | **Green** |
| UniqueInterior triangle Pick w/o PrimitiveEdges | Open (g=1 locate-half) |
| I≤2 triangle Pick w/o PrimitiveEdges | Open |
| I=4 without spokes-empty hyp | Open |
| Shoelace = Haar | Open |
| EP → planar Euler | Open |
| Classical Pick | **Still FAIL** |


## Update 2026-09-25 (UniqueInterior triangle Pick w/o PrimitiveEdges; still FAIL for classical Pick)

Landed in `EulersGem/LatticeFanTrianglePick.lean` (honest names; **not** classical Pick):

```lean
theorem mem_interior_left_or_right_of_uniqueInterior_edgeGcd_eq_one
    -- g=1 ⇒ unique interior lies in exactly one open half

theorem shoelace_eq_one_add_B_div_two_sub_one_of_unique_interior_triangle
    (0 < latticeDet a b c) (UniqueInterior (trianglePolygon a b c) q) :
    shoelace = 1 + B/2 - 1
    -- no PrimitiveEdges hyp; |det| induction via edgeStep
```

Results exports: `results_mem_interior_left_or_right_of_uniqueInterior_edgeGcd_eq_one`,
`results_shoelace_eq_one_add_B_div_two_sub_one_of_unique_interior_triangle`
(prior UniqueInterior substrate retained).

**Prize progress:** UniqueInterior triangle Pick-form drops `PrimitiveEdges`. Base
reuses existing UniqueInterior convex Pick when all edges are primitive; step
splits a non-primitive edge at `edgeStep`, uses chord `edgeGcd ≤ 2`, locates the
unique interior in one half when `g=1` (other empty) or empties both halves when
`g=2`, applies empty Pick / UniqueInterior IH on strictly smaller `|det|`, and
reassembles via shoelace/B additivity. Still **not** classical Pick: I ≤ 2
without PrimitiveEdges; I = 4 without spokes-empty apex; Haar; EP→planar.
Claude Platonic / Cube / MetricRegular / EdgeVertices untouched.

| Item | Status |
|------|--------|
| Empty-interior triangle Pick w/o PrimitiveEdges | Green |
| UniqueInterior edge-split substrate | Green |
| UniqueInterior triangle Pick w/o PrimitiveEdges | **Green** |
| I≤1 triangle Pick w/o PrimitiveEdges | **Green** |
| I=2 / I≤2 triangle Pick w/o PrimitiveEdges | Open |
| I=4 without spokes-empty hyp | Open |
| Shoelace = Haar | Open |
| EP → planar Euler | Open |
| Classical Pick | **Still FAIL** |



## Update 2026-09-25 (TwoInterior / I≤2 triangle Pick w/o PrimitiveEdges; still FAIL for classical Pick)

Landed in `EulersGem/LatticeFanTrianglePick.lean` (honest names; **not** classical Pick):

```lean
theorem mem_interior_left_or_right_or_chord_of_mem_interior_edgeStep
    -- any interior point lies in left half ∨ right half ∨ open chord

theorem edgeGcd_le_three_of_twoInterior_edgeStep
theorem EmptyInterior_edgeStep_both_of_twoInterior_edgeGcd_eq_three
    -- g=3 ⇒ both halves empty (both interiors on open chord)

theorem shoelace_eq_two_add_B_div_two_sub_one_of_two_interior_triangle
    (0 < latticeDet a b c) (TwoInterior (trianglePolygon a b c) q r) :
    shoelace = 2 + B/2 - 1
    -- no PrimitiveEdges hyp; |det| induction via edgeStep
    -- cases: g=1 empty/UniqueInterior/TwoInterior halves; g=2 UniqueInterior+Empty;
    --        g=3 both Empty

theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_two_triangle
    -- I∈{0,1,2} Finset packaging without PrimitiveEdges
```

Results exports: `results_mem_interior_left_or_right_or_chord_of_mem_interior_edgeStep`,
`results_edgeGcd_le_three_of_twoInterior_edgeStep`,
`results_EmptyInterior_edgeStep_both_of_twoInterior_edgeGcd_eq_three`,
`results_shoelace_eq_two_add_B_div_two_sub_one_of_two_interior_triangle`,
`results_shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_two_triangle`.

**Prize progress:** TwoInterior triangle Pick-form drops `PrimitiveEdges`. Base reuses
existing TwoInterior Pick under all-primitive edges; step splits a non-primitive edge
at `edgeStep`, uses chord `edgeGcd ≤ 3`, locates both interiors in halves / open chord
(g=1: (2,0)/(0,2)/(1,1); g=2: UniqueInterior+Empty; g=3: both Empty), applies empty /
UniqueInterior / TwoInterior IH on strictly smaller `|det|`, and reassembles via
shoelace/B additivity. I≤2 Finset packaging green. Still **not** classical Pick: I=4
Finset without spokes-empty apex (ears may have non-primitive sides); Haar; EP→planar.
Claude Platonic / Cube / MetricRegular / EdgeVertices untouched.

| Item | Status |
|------|--------|
| Empty-interior triangle Pick w/o PrimitiveEdges | Green |
| UniqueInterior triangle Pick w/o PrimitiveEdges | Green |
| I≤1 triangle Pick w/o PrimitiveEdges | Green |
| TwoInterior triangle Pick w/o PrimitiveEdges | **Green** |
| I≤2 triangle Pick w/o PrimitiveEdges | **Green** |
| I=4 without spokes-empty hyp | Open |
| Shoelace = Haar | Open |
| EP → planar Euler | Open |
| Classical Pick | **Still FAIL** |


## Update 2026-09-25 (I=4 / I≤4 geometric without spokes-empty; still FAIL for classical Pick)

Landed in `EulersGem/LatticeFanTrianglePick.lean` (honest names; **not** classical Pick):

```lean
theorem spokeInterior_eq_empty_of_earOffInterior_card_eq_three_of_card_eq_four
    -- parent #S=4 and #earOff=3 ⇒ every spoke from apex empty

theorem shoelace_trianglePolygon_ear_eq_card_earOff_add_B_div_two_sub_one_of_I_le_three_of_card_eq_four
    -- ear Pick for parent I=4: #earOff≤2 ⇒ triangle I≤2 (no PrimitiveEdges);
    -- #earOff=3 ⇒ adjacent spokes empty ⇒ I≤3 ear lemma

theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_eq_four
    (StrictlyConvexCCW + PrimitiveEdges parent + Injective)
    (S.card = 4) (S = interior) :
    shoelace = #S + B/2 - 1
    -- no spokes-empty hyp; any apex; ears may have non-primitive sides

theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_four
    -- I∈{0..4} packaging
```

Results exports: `results_spokeInterior_eq_empty_of_earOffInterior_card_eq_three_of_card_eq_four`,
`results_shoelace_trianglePolygon_ear_eq_card_earOff_add_B_div_two_sub_one_of_I_le_three_of_card_eq_four`,
`results_shoelace_eq_cardI_add_B_div_two_sub_one_of_I_eq_four`,
`results_shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_four`.

**Prize progress:** geometric I=4 Finset Pick-form drops the spokes-empty apex hyp.
Fan from any `q∈S`; `#earOff≤3`; apply triangle I≤2 without PrimitiveEdges on ear
sides, or inherit PrimitiveEdges when `#earOff=3` (forces all remaining interiors Off
in that ear ⇒ spokes empty). Discharged hbook closes fan-ear IH. Still **not**
classical Pick: I≥5 / general induction; Haar; EP→planar. Claude Platonic / Cube /
MetricRegular / EdgeVertices untouched. Classical Pick **FAIL** — no rename.

| Item | Status |
|------|--------|
| Empty / UniqueInterior / TwoInterior / I≤2 triangle w/o PrimitiveEdges | Green |
| I=4 under spokes-empty apex | Green (prior) |
| I=4 without spokes-empty hyp | **Green** |
| I≤4 without spokes-empty hyp | **Green** |
| I≥5 / general fan-ear induction | Open |
| Shoelace = Haar | Open |
| EP → planar Euler | Open |
| Classical Pick | **Still FAIL** |

## Update 2026-09-25 (I≤3 triangle w/o PrimitiveEdges + I=5 / I≤5 geometric; still FAIL for classical Pick)

Landed in `EulersGem/LatticeFanTrianglePick.lean` (honest names; **not** classical Pick):

```lean
theorem edgeGcd_le_four_of_card_le_three_edgeStep
theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_three_triangle
    -- I∈{0..3} Finset packaging without PrimitiveEdges; |det| induction via edgeStep
    -- partition interior into left / right / open-chord; IH on halves; B/shoelace reassembly

theorem card_earOffInterior_le_four_of_card_eq_five
theorem spokeInterior_eq_empty_of_earOffInterior_card_eq_four_of_card_eq_five
    -- parent #S=5 and #earOff=4 ⇒ every spoke from apex empty

theorem shoelace_trianglePolygon_ear_eq_card_earOff_add_B_div_two_sub_one_of_I_le_four_of_card_eq_five
    -- ear Pick for parent I=5: #earOff≤3 ⇒ triangle I≤3 (no PrimitiveEdges);
    -- #earOff=4 ⇒ adjacent spokes empty ⇒ I≤4 ear with PrimitiveEdges

theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_eq_five
    (StrictlyConvexCCW + PrimitiveEdges parent + Injective)
    (S.card = 5) (S = interior) :
    shoelace = #S + B/2 - 1
    -- no spokes-empty hyp; any apex; ears may have non-primitive sides

theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_five
    -- I∈{0..5} packaging
```

Results exports: `results_shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_three_triangle`,
`results_card_earOffInterior_le_four_of_card_eq_five`,
`results_spokeInterior_eq_empty_of_earOffInterior_card_eq_four_of_card_eq_five`,
`results_shoelace_trianglePolygon_ear_eq_card_earOff_add_B_div_two_sub_one_of_I_le_four_of_card_eq_five`,
`results_shoelace_eq_cardI_add_B_div_two_sub_one_of_I_eq_five`,
`results_shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_five`.

**Prize progress:** triangle I≤3 drops `PrimitiveEdges` via Finset `|det|` / edgeStep induction
(open-chord card cancels B-chord term). Geometric I=5 Finset Pick-form drops spokes-empty
apex hyp: fan from any `q∈S`; `#earOff≤3` uses triangle I≤3 without PE; `#earOff=4` forces
spokes empty ⇒ PE inheritance ⇒ I≤4 on ear. Discharged hbook closes fan-ear IH. Still **not**
classical Pick: I≥6 / general induction; Haar; EP→planar. Claude Platonic / Cube /
MetricRegular / EdgeVertices untouched. Classical Pick **FAIL** — no rename.

| Item | Status |
|------|--------|
| Empty / UniqueInterior / TwoInterior / I≤2 / I≤3 triangle w/o PrimitiveEdges | **Green** |
| I=4 / I≤4 without spokes-empty hyp | Green |
| I=5 without spokes-empty hyp | **Green** |
| I≤5 without spokes-empty hyp | **Green** |
| I≥6 / general fan-ear induction | Open |
| Shoelace = Haar | Open |
| EP → planar Euler | Open |
| Classical Pick | **Still FAIL** |

## Update 2026-09-25 (I≤4/I≤5 triangle w/o PE + I=6/I≤6 + strong induction; still FAIL for classical Pick)

Landed in `EulersGem/LatticeFanTrianglePick.lean` (honest names; **not** classical Pick):

```lean
theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_triangle_of_pe_ih
    -- general: PE Pick for card≤k ⇒ triangle Pick w/o PE for card≤k (|det|/edgeStep)

theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_four_triangle
theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_five_triangle
    -- I∈{0..4} / I∈{0..5} Finset packaging without PrimitiveEdges

theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_eq_six
theorem shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_six
    -- parent #S=6: all ears #earOff≤5 use triangle I≤5 w/o PE (no PE inheritance branch)

theorem shoelace_eq_cardI_add_B_div_two_sub_one
    (StrictlyConvexCCW + PrimitiveEdges parent + Injective)
    (S = interior) :
    shoelace = #S + B/2 - 1
    -- strong induction on Finset card; base I≤5; step fan_ear_IH + pe_ih triangle ears
```

Results exports: `results_shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_four_triangle`,
`results_shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_five_triangle`,
`results_card_earOffInterior_le_five_of_card_eq_six`,
`results_shoelace_trianglePolygon_ear_eq_card_earOff_add_B_div_two_sub_one_of_I_le_five_of_card_eq_six`,
`results_shoelace_eq_cardI_add_B_div_two_sub_one_of_I_eq_six`,
`results_shoelace_eq_cardI_add_B_div_two_sub_one_of_I_le_six`,
`results_shoelace_eq_cardI_add_B_div_two_sub_one`.

**Prize progress:** PE inheritance on large ears unblocked by general `pe_ih` triangle
form (`|det|` induction; primitive-edge base uses PE Pick at same card bound). Strong
induction on `#S` closes geometric Finset Pick-form for **all** interior cardinalities
under parent `PrimitiveEdges` + `StrictlyConvexCCW` + injective. I=6 / I≤6 and triangle
I≤4 / I≤5 are stepping stones / specializations. Still **not** classical Pick: Haar /
shoelace=measure; EP→planar Euler; triangulation existence for general polygons;
boundary may be non-primitive on parent (hyp requires parent PE). Claude Platonic /
Cube / MetricRegular / EdgeVertices untouched. Classical Pick **FAIL** — no rename.

| Item | Status |
|------|--------|
| Empty / UniqueInterior / TwoInterior / I≤2 / I≤3 / I≤4 / I≤5 triangle w/o PrimitiveEdges | **Green** |
| I=4 / I≤4 / I=5 / I≤5 / I=6 / I≤6 without spokes-empty hyp | **Green** |
| Strong induction on Finset card (geometric Finset Pick-form) | **Green** |
| Shoelace = Haar | Open |
| EP → planar Euler | Open |
| Classical Pick | **Still FAIL** |

## Update 2026-09-25 (Haar bridge: unit / origin triangle volume; still FAIL for classical Pick)

Landed in `EulersGem/LatticeArea.lean` (honest names; **not** classical Pick):

```lean
theorem volume_parallelepiped_eq_ofReal_abs_det (u v : ℝ × ℝ) :
    volume (parallelepiped ![u, v]) = ENNReal.ofReal |u.1 * v.2 - u.2 * v.1|

theorem volume_unitTriangle :
    volume (convexHull ℝ {(0,0),(1,0),(0,1)}) = ENNReal.ofReal (1/2)

theorem volume_convexHull_origin_triangle (u v : ℝ × ℝ) :
    volume (convexHull ℝ {0, u, v}) = ENNReal.ofReal (|det(u,v)| / 2)
```

Mathlib substrate used: `Basis.finTwoProd`, `addHaar_parallelepiped`,
`addHaar_image_linearMap`, Fubini/`prod_apply` for the unit triangle.

Results exports: `results_finTwoProd_addHaar_eq_volume`,
`results_volume_parallelepiped_eq_ofReal_abs_det`,
`results_volume_unitTriangle`,
`results_volume_convexHull_origin_triangle`.

**Still open for classical Pick:**
* lattice shoelace ↔ `|latticeDet|/2` as `ℝ` coercion + translation of hull to origin
* StrictlyConvexCCW fan additivity (shoelace sum = Haar sum)
* compose with combinatorial `shoelace_eq_cardI_add_B_div_two_sub_one`
* EP → planar Euler; triangulation existence for general polygons

Claude Platonic / Cube / MetricRegular / EdgeVertices untouched.
Classical Pick **FAIL** — no rename.


## Update 2026-09-25 (lattice triangle Haar = shoelace; still FAIL for classical Pick)

Landed in `EulersGem/LatticeArea.lean` (honest names; **not** classical Pick):

```lean
theorem triangleShoelace_coe_eq_abs_det_div_two (a b c : ℤ × ℤ) :
    (triangleShoelace a b c : ℝ) = |(latticeDet a b c : ℝ)| / 2

theorem volume_convexHull_lattice_triangle (a b c : ℤ × ℤ) :
    volume (convexHull ℝ {toReal a, toReal b, toReal c}) =
      ENNReal.ofReal (triangleShoelace a b c)

theorem volume_convexHull_trianglePolygon (a b c : ℤ × ℤ) :
    volume (trianglePolygon a b c).convexHullRegion =
      ENNReal.ofReal (trianglePolygon a b c).shoelace

theorem sum_volume_fanTriangles_eq_ofReal_shoelace
    (P) (hnn : FanDetsNonneg P) (hverts) :
    (∑ t ∈ fanTriangles P, volume (conv{t.a,t.b,t.c})) =
      ENNReal.ofReal P.shoelace

theorem volume_eq_ofReal_cardI_add_B_div_two_sub_one_of_shoelace
    (P) (S) (hvol : volume P.hull = ofReal P.shoelace)
    (hcomb : P.shoelace = #S + B/2 - 1) :
    volume P.hull = ofReal (#S + B/2 - 1)
```

Bridge: translate triangle to origin (`volume_vadd` + `convexHull_vadd`) then
reuse `volume_convexHull_origin_triangle`. `trianglePolygon` via existing
`shoelaceSum_trianglePolygon` + `trianglePolygon_convexHullRegion`.

Results exports: `results_triangleShoelace_coe_eq_abs_det_div_two`,
`results_volume_convexHull_lattice_triangle`,
`results_volume_convexHull_trianglePolygon`,
`results_shoelace_coe_eq_abs_shoelaceSum_div_two`,
`results_sum_volume_fanTriangles_eq_ofReal_shoelace`,
`results_volume_eq_ofReal_cardI_add_B_div_two_sub_one_of_shoelace`.

**Still open for classical Pick:**
* StrictlyConvexCCW polygon `convexHullRegion` = almost-disjoint union of fan
  triangles (⇒ discharge `hvol` for general polygons)
* EP → planar Euler; general triangulation existence

Claude Platonic / Cube / MetricRegular / EdgeVertices untouched.
Classical Pick **FAIL** — no rename.

Also Results compose (I ≤ 1 triangle only):

```lean
theorem results_volume_trianglePolygon_eq_ofReal_cardI_add_B_div_two_sub_one_of_I_le_one
    (a b c) (hD : 0 < latticeDet a b c) (S) (hS) (hcard : S.card ≤ 1) :
    volume (trianglePolygon a b c).convexHullRegion =
      ofReal (#S + B/2 - 1)
```

