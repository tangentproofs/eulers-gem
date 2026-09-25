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
7. **Done (Phase B, #1535):** combinatorial Platonic classification + five Schläfli
   constructions; Funkenbusch / triangulation count identities (not Pick)
   (`Platonic.lean`, `Picks.lean`, `PHASE_B_PLAN.md`, `PICKS_CLAUDE_AUDIT.md`). Geometric lattice
   triangulation + primitive-triangle area `½` still open.

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
- [x] Platonic Schläfli classification + five combinatorial constructions (#1535)
- [ ] Classical geometric Pick's theorem (open; only Funkenbusch/triangulation *count identities* landed — not Pick; see `PICKS_CLAUDE_AUDIT.md`)
