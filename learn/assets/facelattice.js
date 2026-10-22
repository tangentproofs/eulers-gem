// Exact face counts of the n-simplex and the n-cube, and the alternating sum
// `EulersGem.faceEulerSum` forms out of them.
//
// Mirrors (`Polytope.lean`):
//
//   faceEulerSum S n = ∑ d ∈ range (n+1), (-1)^d * #{f | IsFaceOf S f ∧ affDim f = d}
//
// Two things about that sum are easy to get wrong, and both are visible here:
//   * the body itself is counted — it is a face of itself (`isFaceOf_refl`) of affine
//     dimension `n`, and it is the `d = n` term;
//   * the empty face is *not* counted — `IsFaceOf S ∅` holds (`isFaceOf_empty`) but
//     `affDim ∅ = -1` (`AffDim.affDim_empty`), and the sum ranges over `d ≥ 0`.
//
// Pure arithmetic: no geometry, no DOM.

/** Binomial coefficient, exact for the small values used here. */
export function binom(n, k) {
  if (k < 0 || k > n || n < 0) return 0;
  let r = 1;
  for (let i = 0; i < k; i++) r = (r * (n - i)) / (i + 1);
  return Math.round(r);
}

/**
 * `f_d` for the n-simplex, `d = 0 … n`: a face is spanned by a nonempty subset of the `n+1`
 * vertices, and a `(d+1)`-element subset spans a face of affine dimension `d`
 * (`SimplexFaces.lean`: `affDim (face b S) = S.card − 1`). So `f_d = C(n+1, d+1)`, which is
 * `EulersGem.faceCount n d` in `Faces.lean`.
 */
export const simplexFaceCounts = (n) =>
  Array.from({ length: n + 1 }, (_, d) => binom(n + 1, d + 1));

/**
 * `f_d` for the n-cube `[-1,1]^n`, `d = 0 … n`: a face fixes `n − d` coordinates to `±1` and
 * leaves `d` free (`Cube.affDim_face`: the dimension is `n − |supp c|`). Choose which
 * coordinates are fixed, then a sign for each: `f_d = 2^(n−d) · C(n, d)`.
 */
export const cubeFaceCounts = (n) =>
  Array.from({ length: n + 1 }, (_, d) => 2 ** (n - d) * binom(n, d));

/** `∑ (-1)^d f_d` over `d = 0 … n`: the Euler–Poincaré characteristic, which is 1. */
export const faceEulerSum = (counts) =>
  counts.reduce((s, c, d) => s + (d % 2 ? -c : c), 0);

/**
 * Drop the top-dimensional term (the body) from the alternating sum. For `n = 3` this turns
 * `V − E + F − 1 = 1` into `V − E + F = 2`, which is exactly how
 * `euler_relation_of_isPolytope` is proved from `Euler_Poincare_of_isPolytope`:
 * the only 3-face of a 3-dimensional polytope is the body, so its term is `−1`.
 */
export const withoutBody = (counts) => {
  const n = counts.length - 1;
  return faceEulerSum(counts) - (n % 2 ? -counts[n] : counts[n]);
};

export const FAMILIES = {
  simplex: { label: "n-simplex", counts: simplexFaceCounts,
    names: ["point", "segment", "triangle", "tetrahedron", "5-cell", "5-simplex", "6-simplex"] },
  cube: { label: "n-cube", counts: cubeFaceCounts,
    names: ["point", "segment", "square", "cube", "tesseract", "5-cube", "6-cube"] },
};

/** One row of the table a `face-lattice` widget shows. */
export function lattice(family, n) {
  const fam = FAMILIES[family] || FAMILIES.simplex;
  const counts = fam.counts(n);
  return {
    family, n, counts,
    name: fam.names[n] || `${fam.label.replace("n-", `${n}-`)}`,
    sum: faceEulerSum(counts),
    bodyCount: counts[n],
    withoutBody: withoutBody(counts),
  };
}

/** Dimension names used in the table header. */
export const DIM_NAMES = ["vertices", "edges", "2-faces", "3-faces", "4-faces", "5-faces", "6-faces"];
