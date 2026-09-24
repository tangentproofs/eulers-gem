# Lean roadmap (Paulson-first)

1. **Done (scaffold):** simplex face counts; `eulerChar_simplex = 0`; tetrahedron numbers;
   Results.lean + comparator script.
2. **Done (survey):** Mathlib survey vs Paulson — see `MATHLIB_SURVEY.md`.
3. **In progress:** Port Paulson substrate — `hyperplaneSide` / arrangement cells /
   cell complexes (`EulersGem.Hyperplane`); next: Euler characteristic + refinement
   invariance.
4. **Cones → polytopes:** Euler relation for full-dimensional proper polyhedral cones;
   then `Euler_Poincare_full` analogue.
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
- [ ] Paulson hyperplane substrate (definitions + cell lemmas landed; Euler char next)
