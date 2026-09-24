# Lean roadmap (Paulson-first)

1. **Done (scaffold):** simplex face counts; `eulerChar_simplex = 0`; tetrahedron numbers;
   Results.lean + comparator script.
2. **Done (survey):** Mathlib survey vs Paulson — see `MATHLIB_SURVEY.md`.
3. **Done (substrate):** hyperplane cells/complexes; `affDim`; combinatorial
   `eulerCharacteristic` + refinement invariance; cell geometry; Compl/Diff of
   cell complexes.
4. **In progress (cones → polytopes):** cone `faceEulerSum = 0` green (hyper1+hyper2).
   **Cone→polytope lift** in `EulerPoincare.lean` + `ConeSlice.lean`: combinatorial
   `faceEulerSum_slice_of_cone`; geometric zero-face / face-of-conic / slice /
   recover / homogenization equality / `InjOn` / assembled `ConeSliceFaceBijection`
   + height-1 EP. Blocker: `E×ℝ` embedding for `Euler_Poincare_full`.
5. **Specialize:** convex 3-polytope ⇒ `V - E + F = 2`; re-export from Results.lean
   only when proved.
6. **Cross-check:** against vendored AFP under `../isabelle/` once ported.
7. **Parked:** Pick's theorem; Platonic solids constructions.

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
- [ ] Euler_Poincare_full via E×ℝ embedding + geometric 3D V−E+F=2
