/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Codex
-/
import EulersGem.UnconditionalEuler
import EulersGem.PolytopeFaces
import Results
import Lean.Util.CollectAxioms

/-!
# Verification of the representation theorem and public geometric contracts

Audit the axiom dependencies of the new proof layers and their public applications.
The examples below also check the theorem signatures and the geometric definitions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let modules := #[`EulersGem.LinearInequalities, `EulersGem.PolyhedralRepresentation,
    `EulersGem.PolytopeHalfspaces, `EulersGem.UnconditionalEuler]
  let results := #[``Results.results_euler_characteristic,
    ``Results.results_euler_relation_dimension_three, ``Results.results_euler_polyhedron,
    ``EulersGem.facesOfDim_finite_of_isPolytope, ``Results.results_five_platonic_solids]
  let mut count : ℕ := 0
  let mut seenModules : Array Name := #[]
  for (decl, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? decl | continue
    let origin := env.header.moduleNames[idx.toNat]!
    if modules.contains origin || results.contains decl then
      count := count + 1
      if modules.contains origin && !seenModules.contains origin then
        seenModules := seenModules.push origin
      for ax in (← collectAxioms decl) do
        unless allowed.contains ax do
          throwError "{decl} depends on an unexpected axiom: {ax}"
  for module in modules do
    unless seenModules.contains module do
      throwError "Audited module contributed no declarations: {module}"
  unless count > 0 do
    throwError "No declarations were audited"
  logInfo m!"Axiom audit passed for {count} representation and Euler declarations."

#print axioms EulersGem.IsPolytope.isPolyhedron
#print axioms Results.results_euler_characteristic
#print axioms Results.results_euler_relation_dimension_three
#print axioms Results.results_euler_polyhedron
#print axioms Results.results_five_platonic_solids

example {p : Set (EuclideanSpace ℝ (Fin 3))}
    (hp : EulersGem.IsPolytope p) (hdim : EulersGem.affDim p = 3) :
    ({f : Set (EuclideanSpace ℝ (Fin 3)) |
      EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 0}.ncard : ℤ) -
    ({f : Set (EuclideanSpace ℝ (Fin 3)) |
      EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 1}.ncard : ℤ) +
    ({f : Set (EuclideanSpace ℝ (Fin 3)) |
      EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 2}.ncard : ℤ) = 2 :=
  Results.results_euler_polyhedron hp hdim

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {p : Set E} (hp : EulersGem.IsPolytope p) :
    ∃ H : Set (EulersGem.Hyperplane E), H.Finite ∧
      p = ⋂ h ∈ H, EulersGem.closedHalfspace h.1 h.2 :=
  hp.isPolyhedron

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {p : Set E} (hp : EulersGem.IsPolytope p) (d : ℤ) :
    {f : Set E | EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = d}.Finite :=
  EulersGem.facesOfDim_finite_of_isPolytope hp d

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {p : Set E} (hp : EulersGem.IsPolytope p)
    (hdim : EulersGem.affDim p = Module.finrank ℝ E) (hn : 1 ≤ Module.finrank ℝ E) :
    EulersGem.faceEulerSum p (Module.finrank ℝ E) = 1 :=
  Results.results_euler_characteristic hp hdim hn

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {p : Set E} (hp : EulersGem.IsPolytope p)
    (hdim : EulersGem.affDim p = 3) (hE : Module.finrank ℝ E = 3) :
    ({f : Set E | EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 0}.ncard : ℤ) -
      ({f : Set E | EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 1}.ncard : ℤ) +
      ({f : Set E | EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = 2}.ncard : ℤ) = 2 :=
  Results.results_euler_relation_dimension_three hp hdim hE

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {p : Set E} {s m : ℕ} (hp : EulersGem.IsPolytope p)
    (hdim : EulersGem.affDim p = 3) (hE : Module.finrank ℝ E = 3)
    (hs : 3 ≤ s) (hm : 3 ≤ m)
    (hface : ∀ f ∈ EulersGem.Platonic.facesOfDim p 2,
      {e ∈ EulersGem.Platonic.facesOfDim p 1 | e ⊆ f}.ncard = s)
    (hedge : ∀ e ∈ EulersGem.Platonic.facesOfDim p 1,
      {f ∈ EulersGem.Platonic.facesOfDim p 2 | e ⊆ f}.ncard = 2)
    (hvert : ∀ v ∈ EulersGem.Platonic.facesOfDim p 0,
      {e ∈ EulersGem.Platonic.facesOfDim p 1 | v ⊆ e}.ncard = m) :
    (s, m) ∈ EulersGem.Platonic.schlafliPairs :=
  Results.results_five_platonic_solids.1 hp hdim hE hs hm hface hedge hvert

-- Pin the geometric definitions used by the public contracts.
section GeometryDefinitions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

example (p : Set E) : EulersGem.IsPolytope p ↔
    ∃ V : Set E, V.Finite ∧ p = convexHull ℝ V := Iff.rfl

example (p f : Set E) : EulersGem.IsFaceOf p f ↔ IsExtreme ℝ p f ∧ Convex ℝ f :=
  ⟨fun h ↦ ⟨h.isExtreme, h.convex⟩, fun h ↦ ⟨h.1, h.2⟩⟩

open scoped RealInnerProductSpace in
example (a : E) (b : ℝ) : EulersGem.closedHalfspace a b = {x : E | ⟪a, x⟫ ≤ b} := rfl

example (p : Set E) : EulersGem.affDim p =
    match (affineSpan ℝ p).finDim with
    | ⊥ => -1
    | (n : ℕ) => (n : ℤ) := rfl

example (p : Set E) (n : ℕ) : EulersGem.faceEulerSum p n =
    ∑ d ∈ Finset.range (n + 1), (-1 : ℤ) ^ d *
      ({f : Set E | EulersGem.IsFaceOf p f ∧ EulersGem.affDim f = (d : ℤ)}.ncard : ℤ) := rfl

end GeometryDefinitions
