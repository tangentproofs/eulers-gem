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

