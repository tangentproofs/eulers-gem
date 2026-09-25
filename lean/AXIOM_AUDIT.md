# Axiom audit (both lanes)

Run `lean/scripts/audit-axioms.sh`. It elaborates `#print axioms` for every `theorem`/`lemma`
declared in `Results.lean`, hard-fails on `sorry` anywhere in the sources, lists every
`native_decide` occurrence, and fails if any Results declaration depends on a `native_decide`
axiom or `sorryAx`.

```
cd lean && ./scripts/audit-axioms.sh          # audit all of Results
cd lean && ./scripts/audit-axioms.sh Results.results_cube_platonic   # audit one constant
```

## Why `native_decide` matters here

`native_decide` does **not** produce a kernel-checked proof: it adds an axiom
(`<decl>._native.native_decide.ax_*`) asserting the compiler's evaluation, and that axiom then
appears in the dependency set of everything downstream. The standing bar for this repo is "no
sorry/axioms", so a Results theorem whose proof reaches a `native_decide` is *not* discharged in
the sense the bar intends, even though `lake build` is green.

Three `native_decide`s were removed from the Euler–Poincaré root for exactly this reason
(`faceEulerSum_three_expand`, `tetrahedron_euler_relation_from_faceCount`,
`Platonic.card_schlafliPairs`), and two more from Results Platonic counts. Plain `decide`
sufficed in every case.

## Status as of 2026-09-25 (commit `beb498b`)

68 declarations audited, 65 pass with `[propext, Classical.choice, Quot.sound]`.

**Platonic lane: all pass.**

**Pick lane: three declarations are not kernel-proved.**

| declaration | axiom source |
|---|---|
| `results_unit_square_planar_euler` | `Picks.UnitSquareTriangulation.unitSquare._native.native_decide.ax_*`, `tLower_card`, `tUpper_card` |
| `results_unit_square_disk_triangulation_handshaking` | same `unitSquare` axioms |
| `results_shoelace_pick_form_of_unit_square` | `Picks.UnitSquareWitness.witness._native.native_decide.ax_*`, `shoelace_pick_form_unit_square`, `witness_{B,T}_eq_unitSquare` |

Sites: `EulersGem/PlanarTriangulation.lean` ~lines 370–423 and
`EulersGem/PicksTriangulation.lean` ~lines 254–299.

This matters for the honesty story because the unit-square planar-Euler discharge is the Pick
lane's strongest EP-side result, and it is currently the one item on the "done" list that the
kernel has not checked.

Suggested fix: swap `native_decide` for `decide`. The goals are small `Fin`/`Finset`
computations. On the Platonic side `decide` handled counting over `Finset (Fin 3 × Bool)` (64
elements) and over `Fin 3 → Option Bool` (27 functions, with an inner filter over all 27) in
well under a second each; `set_option maxRecDepth 100000` was the only extra needed.

## Note on concurrent sessions

This checkout has at times been edited by two Claude sessions at once (a Platonic lane and a
Pick lane). Whole-tree `git restore` / `git checkout -- .` / bare `git stash` will silently
discard the other session's in-flight work — it did so three times, and once left `HEAD`
non-building because half of a multi-file change was committed. Scope resets to your own paths
(`git restore -- lean/EulersGem/YourFile.lean`), and `git add` a file as soon as it builds so a
worktree restore recovers your content rather than `HEAD`'s.
