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
| Classical Pick | **Still FAIL** — existence, EP→planar, handshaking, measure open |

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
| Geometric witness → incidence structure | Open |
| EP → planar Euler | Open (`planar_disk_euler_of_EP_bridge` records hyp) |
| Triangulation existence | Open |
| Classical Pick | **Still FAIL** |
