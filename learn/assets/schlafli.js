// The Schläfli count argument of `EulersGem.Platonic` (`Platonic.lean`), in arithmetic.
//
// A combinatorially regular convex 3-polytope has `s` edges on every 2-face, `m` edges at
// every vertex, and two 2-faces along every edge. Double counting then gives `s·F = 2E` and
// `m·V = 2E` (`PlatonicOfEuler.regular_polytope_counts` proves both from face-lattice
// incidence), and Euler gives `V − E + F = 2` (discharged from the Euler–Poincaré root, not
// assumed). Multiply Euler by `s·m` and substitute:
//
//   `Platonic.mul_euler_int` :  E · (2s + 2m − s·m) = 2·s·m
//   `Platonic.sub_mul_lt_four`:  (s − 2)(m − 2) < 4
//   `Platonic.schlafliPairs`  :  {(3,3), (3,4), (3,5), (4,3), (5,3)}
//
// Pure arithmetic, no DOM. Nothing here constructs a solid: see `schlafliPairs` in the Lean,
// which is a `Finset (ℕ × ℕ)`.

/** `EulersGem.Platonic.schlafliPairs`, in the Lean's own order. */
export const SCHLAFLI_PAIRS = [[3, 3], [3, 4], [3, 5], [4, 3], [5, 3]];

/** `(s − 2)(m − 2)`, the quantity `Platonic.sub_mul_lt_four` bounds below 4. */
export const defect = (s, m) => (s - 2) * (m - 2);

/** `2s + 2m − s·m`, the multiplier in `Platonic.mul_euler_int`. Equals `4 − defect`. */
export const coeff = (s, m) => 2 * s + 2 * m - s * m;

/** Is `(s, m)` one of the five? `Platonic.schlafli_pair_mem` says every regular pair is. */
export const isSchlafliPair = (s, m) => SCHLAFLI_PAIRS.some(([a, b]) => a === s && b === m);

/**
 * Solve `E·(2s + 2m − s·m) = 2sm` together with `s·F = 2E` and `m·V = 2E`.
 * Returns `null` when no positive solution exists, with `why`:
 *   `flat`      — `coeff = 0`: `(s−2)(m−2) = 4`, the Euclidean tilings {4,4}, {3,6}, {6,3};
 *   `hyperbolic`— `coeff < 0`: `(s−2)(m−2) > 4`, a hyperbolic tiling; `E` would be negative.
 * Note the Lean never needs this solve step for the classification — `sub_mul_lt_four` plus
 * `s, m ≥ 3` already pins the pair down. The numbers are the content of
 * `Platonic.tetrahedron` … `Platonic.icosahedron`, five `RegularNumbers` records.
 */
export function solveCounts(s, m) {
  const c = coeff(s, m);
  if (c === 0) return { ok: false, why: "flat", coeff: c, defect: defect(s, m) };
  if (c < 0) return { ok: false, why: "hyperbolic", coeff: c, defect: defect(s, m) };
  const E = (2 * s * m) / c, F = (2 * E) / s, V = (2 * E) / m;
  const integral = [E, F, V].every((x) => Number.isInteger(x));
  return { ok: true, why: "spherical", coeff: c, defect: defect(s, m), V, E, F, integral,
    euler: V - E + F };
}

/** The grid a `schlafli` widget draws: every `(s, m)` with `lo ≤ s, m ≤ hi`. */
export function grid(lo = 3, hi = 8) {
  const rows = [];
  for (let s = lo; s <= hi; s++) {
    const row = [];
    for (let m = lo; m <= hi; m++) row.push({ s, m, ...solveCounts(s, m), pair: isSchlafliPair(s, m) });
    rows.push(row);
  }
  return rows;
}

/** Which of the five solids a pair names, and whether the Lean builds it geometrically. */
export const SOLIDS = {
  "3,3": { name: "tetrahedron", preset: "tetrahedron", geometric: "GeometricPlatonic.tetrahedron_platonic" },
  "4,3": { name: "cube", preset: "cube", geometric: "Cube.cube_platonic" },
  "3,4": { name: "octahedron", preset: "octahedron", geometric: "Octahedron.octahedron_platonic" },
  "5,3": { name: "dodecahedron", preset: "dodecahedron", geometric: null },
  "3,5": { name: "icosahedron", preset: "icosahedron", geometric: null },
};
export const solidOf = (s, m) => SOLIDS[`${s},${m}`] || null;
