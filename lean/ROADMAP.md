# Lean roadmap (Paulson-first)

1. **Done (scaffold):** simplex face counts; `eulerChar_simplex = 0`; tetrahedron numbers;
   Results.lean + comparator script.
2. **Done (survey):** Mathlib survey vs Paulson — see `MATHLIB_SURVEY.md`.
3. **Done (substrate):** hyperplane cells/complexes; `affDim`; combinatorial
   `eulerCharacteristic` + refinement invariance; cell geometry; Compl/Diff of
   cell complexes.
4. **Done (cones → polytopes):** cone `faceEulerSum = 0`; ConeSliceFaceBijection;
   height-1 EP; `E×ℝ` embedding (`Embed.lean`); `Euler_Poincare_full` for full-dim
   H+V-rep polytopes; geometric 3D `V−E+F=2`.
5. **Specialize:** done for full-dim convex 3-polytopes with H+V-rep (Results).
6. **Cross-check:** against vendored AFP under `../isabelle/` once ported.
7. **Phase B (#1535) in progress:** combinatorial Platonic classification + five Schläfli
   constructions done; Pick on **EP spine** — count identities + lattice polygon I/B +
   `|det|=1` emptiness + witness-conditional shoelace Pick-form + combinatorial handshaking +
   unit-square witness↔disk with planar Euler discharged + fan existence for all `n≥3`
   + geometric fan shoelace / empty-interior Pick-form under primitivity hyps
   (not classical Pick). Landed: `empty⇒|det|=1` (nondeg); `FanTrianglesEmpty` from `I=∅`+extreme vertices.
   Landed: `VerticesExtreme` from `StrictlyConvexCCW`. Still open: general triangulation existence,
   general EP→planar from `Euler_Poincare_full`, Haar/shoelace=measure. See `PHASE_B_PLAN.md`,
   `PICKS_CLAUDE_AUDIT.md`. Platonic geometric regularity: separate lane.

Alternate Tverberg path (Poly100-notes) is documented under `../isabelle/` only.

## PR checklist (scaffold)

- [x] Dual tree `lean/` + `isabelle/`
- [x] Toolchain `v4.35.0-rc1` + Mathlib pin (lockstep)
- [x] `lake exe cache get` + green `lake build`
- [x] Results.lean claims only proved theorems
- [x] Poly100 sources archived; Paulson-first Lean strategy documented
- [x] prove2/ local milestone graph stub (no cloud auth)
- [x] Mathlib survey (`MATHLIB_SURVEY.md`)
- [x] Paulson hyperplane substrate defs + cell/complex lemmas + finiteness
- [x] Set-level `affDim` + combinatorial `eulerCharacteristic` + Un-additivity
- [x] Cell open∩affine + relative interior + halfspace affDim preservation
- [x] Refinement invariance (Paulson insert/cutting: affDim drop + general insert)
- [x] Cell-complex Compl/Diff; polyhedron/polytope/cone substrate
- [x] Halfspace-cone cell Euler char = 0; soft inclusion-exclusion
- [x] Halfspace face↔cell (`FaceCell`) + `faceEulerSum_halfspace_cone = 0`
- [x] Face lattice substrate + two-halfspace cone cell EC = 0
- [x] Indexed IE + general polyhedral-cone cell EC = 0
- [x] General cone hyper2 (cell ⊆ cone ⇒ closure is face; sign patterns)
- [x] hyper1 + RI recovery ⇒ faceEulerSum = 0 / Euler_polyhedral_cone
- [x] Cone→polytope combinatorial reduction + apex/homogenization substrate (`EulerPoincare`)
- [x] Simplex face-sum = 1 + 3D bookkeeping in Results.lean
- [x] ConeSlice geometric substrate (zero-face, face-of-conic, slice/recover, homogenize⊆)
- [x] ConeSliceFaceBijection (face-lift + affDim+1 + homogenized equality + height-1 EP)
- [x] Euler_Poincare_full via E×ℝ embedding + geometric 3D V−E+F=2
- [x] Combinatorial Schläfli classification + five `(V,E,F)` witnesses (#1535; geometric regular embeddings open)
- [ ] Classical geometric Pick's theorem (open; EP-spine route)
  - [x] Funkenbusch / triangulation *count identities* (not Pick)
  - [x] Lattice polygon structure + geometric I/B defs (`LatticePolygon.lean`)
  - [x] `|det|=1` ⇒ closed triangle has only vertex lattice points
  - [x] `PrimitiveLatticeTriangulationWitness` + shoelace Pick-form **conditional on witness + `hEuler_planar`** (not classical Pick)
  - [x] Combinatorial handshaking `2E=3T+B` from disk incidence (`PlanarTriangulation`)
  - [x] Unit-square witness ↔ combinatorial disk; planar Euler **proved** for unit square + fan disks (general EP→planar still open)
  - [x] Fan combinatorial triangulation existence for **all** `n ≥ 3` (`FanDiskTriangulation`)
  - [x] Geometric fan shoelace identity + empty-interior `shoelace = B/2−1` under fan-primitivity hyps (`LatticeFan.lean`; not classical Pick)
  - [x] Nondegenerate empty closed triangle ⇒ `|det|=1` (`LatticeTriangleEmpty.lean`); `FanDetPrimitive` from empty fan ears + `FanDetsPos`
  - [x] `FanTrianglesEmpty` from polygon `I=∅` + primitive edges + `VerticesExtreme` (`LatticeFan.lean`; not classical Pick)
  - [x] Discharge `VerticesExtreme` from `StrictlyConvexCCW` (`LatticeFan.lean`; not classical Pick)
  - [x] Discharge `FanDetsPos` from `StrictlyConvexCCW` + injective vertices (`FanDetsPos_of_strictlyConvexCCW`)
  - [x] Interior-fan I=1 shoelace `= 1 + B/2 − 1` under `InteriorFanDetsPos` + `InteriorFanTrianglesEmpty` + primitive edges (`LatticeFanInterior.lean`; not classical Pick)
  - [ ] Triangulation existence without emptiness hyp; I>0 / ear-clipping / Haar
  - [ ] Discharge `hEuler_planar` from `Euler_Poincare_full` for general planar disks
  - [ ] Shoelace = Haar/Lebesgue; Claude audit PASS before any Pick-named Results claim
