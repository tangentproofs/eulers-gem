// The Pick lane in exact integer arithmetic, mirroring `EulersGem.Picks`
// (`LatticeTriangle.lean`, `LatticePolygon.lean`, `LatticeFan.lean`, `DiskEuler.lean`).
//
// Every function here is named after the Lean definition it mirrors. Points are `[x, y]` pairs
// of ordinary JS integers standing for `ℤ × ℤ`; all tests are exact integer tests, so this
// module decides the Lean's hypotheses rather than approximating them. It does *not* compute
// Lebesgue measure: `volume_convexHullRegion_eq_ofReal_shoelace` is the Lean theorem that
// identifies the shoelace number with the measure, and that is a theorem, not a computation.
//
// No DOM.

/* ------------------------------------------------------------------ `LatticeTriangle.lean` */

/** `Int.gcd`: nonnegative, and `0` only for `0 0`. */
export function igcd(a, b) {
  a = Math.abs(a); b = Math.abs(b);
  while (b) { [a, b] = [b, a % b]; }
  return a;
}

/** `edgeGcd p q = Int.gcd (q.1 − p.1) (q.2 − p.2)`; `0` exactly when `p = q`. */
export const edgeGcd = (p, q) => igcd(q[0] - p[0], q[1] - p[1]);

/** `latticeDet a b c = (b₁−a₁)(c₂−a₂) − (b₂−a₂)(c₁−a₁)`. Twice the signed area. */
export const latticeDet = (a, b, c) =>
  (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0]);

/** `triangleShoelace a b c = |latticeDet a b c| / 2`. */
export const triangleShoelace = (a, b, c) => Math.abs(latticeDet(a, b, c)) / 2;

/** `Triangle.IsDetPrimitive t ↔ |t.det| = 1` — equivalently shoelace exactly `1/2`. */
export const isDetPrimitive = (a, b, c) => Math.abs(latticeDet(a, b, c)) === 1;

/**
 * `edgeLatticePoints p q`: the lattice points of the closed segment, built from the gcd the way
 * the Lean does (`{p}` when `p = q`, otherwise `edgeGcd + 1` evenly spaced points).
 */
export function edgeLatticePoints(p, q) {
  const d = edgeGcd(p, q);
  if (d === 0) return [p.slice()];
  const sx = (q[0] - p[0]) / d, sy = (q[1] - p[1]) / d;
  return Array.from({ length: d + 1 }, (_, k) => [p[0] + k * sx, p[1] + k * sy]);
}

const key = (p) => `${p[0]},${p[1]}`;
const uniq = (pts) => { const m = new Map(); for (const p of pts) m.set(key(p), p); return [...m.values()]; };

/* ------------------------------------------------------------- hull, for `convexHullRegion` */

/** Counterclockwise convex hull of a point list (Andrew's monotone chain). Exact integers. */
export function convexHull(pts) {
  const ps = uniq(pts).sort((a, b) => a[0] - b[0] || a[1] - b[1]);
  if (ps.length < 3) return ps;
  const half = (src) => {
    const out = [];
    for (const p of src) {
      while (out.length >= 2 && latticeDet(out[out.length - 2], out[out.length - 1], p) <= 0) out.pop();
      out.push(p);
    }
    return out;
  };
  const lower = half(ps), upper = half(ps.slice().reverse());
  return [...lower.slice(0, -1), ...upper.slice(0, -1)];
}

/**
 * Is the lattice point `p` in `convexHull ℝ (toReal '' vertexFinset)`? Exactly: inside or on the
 * boundary of the hull of the *vertex set*, which is what `LatticePolygon.convexHullRegion`
 * takes the hull of — the listed vertices, not the traced-out polygon. For a non-convex polygon
 * the hull is strictly bigger than the region you would draw, and this is where the Lean's `I`
 * stops meaning the classical Pick `I`.
 */
export function inHull(hull, p) {
  if (hull.length === 0) return false;
  if (hull.length === 1) return hull[0][0] === p[0] && hull[0][1] === p[1];
  if (hull.length === 2) {
    const [a, b] = hull;
    if (latticeDet(a, b, p) !== 0) return false;
    return Math.min(a[0], b[0]) <= p[0] && p[0] <= Math.max(a[0], b[0]) &&
      Math.min(a[1], b[1]) <= p[1] && p[1] <= Math.max(a[1], b[1]);
  }
  for (let i = 0; i < hull.length; i++)
    if (latticeDet(hull[i], hull[(i + 1) % hull.length], p) < 0) return false;
  return true;
}

/* ------------------------------------------------------------------ `LatticePolygon.lean` */

/**
 * A `LatticePolygon`: a cyclic list of at least three lattice vertices, with everything the
 * Lean derives from it. The Lean structure asserts nothing but `3 ≤ vertices.length` — not
 * simplicity, not convexity, not even distinctness — so the predicates come separately.
 */
export function polygon(vertices) {
  const vs = vertices.map((p) => [p[0], p[1]]);
  const n = vs.length;
  const valid = n >= 3;
  const nextIdx = (i) => (i + 1) % n;
  const prevIdx = (i) => (i + n - 1) % n;
  const edgePair = (i) => [vs[i], vs[nextIdx(i)]];

  // `boundaryLatticePoints` = ⋃ over the cyclic edges; `B` = its cardinality.
  const boundary = valid ? uniq(vs.flatMap((_, i) => edgeLatticePoints(...edgePair(i)))) : [];
  const bset = new Set(boundary.map(key));
  const B = boundary.length;

  const hull = convexHull(vs);
  // `latticePointsInConvexHull` / `interiorLatticePoints`, by scanning the bounding box.
  const inside = [], interior = [];
  if (valid) {
    const xs = vs.map((p) => p[0]), ys = vs.map((p) => p[1]);
    for (let x = Math.min(...xs); x <= Math.max(...xs); x++)
      for (let y = Math.min(...ys); y <= Math.max(...ys); y++) {
        const p = [x, y];
        if (!inHull(hull, p)) continue;
        inside.push(p);
        if (!bset.has(key(p))) interior.push(p);
      }
  }

  // `shoelaceSum = ∑ (xᵢ yᵢ₊₁ − xᵢ₊₁ yᵢ)`, `shoelace = |shoelaceSum| / 2`.
  let shoelaceSum = 0;
  for (let i = 0; i < n; i++) {
    const [a, b] = edgePair(i);
    shoelaceSum += a[0] * b[1] - b[0] * a[1];
  }
  const shoelace = Math.abs(shoelaceSum) / 2;

  // `LatticeFan` predicates.
  const injective = new Set(vs.map(key)).size === n;
  const convexCCW = valid && vs.every((_, i) => vs.every((_, j) => latticeDet(vs[i], vs[nextIdx(i)], vs[j]) >= 0));
  const localCCWTurns = valid && vs.every((_, i) => latticeDet(vs[prevIdx(i)], vs[i], vs[nextIdx(i)]) > 0);
  const strictlyConvexCCW = convexCCW && localCCWTurns;
  const primitiveEdges = valid && vs.every((_, i) => edgeGcd(...edgePair(i)) === 1);
  const emptyInterior = interior.length === 0;

  // The corner fan of `LatticeFan.lean`: triangles `(v₀, vᵢ₊₁, vᵢ₊₂)` for `i < n − 2`.
  const fan = [];
  for (let i = 0; i + 2 < n; i++) fan.push({ i, a: vs[0], b: vs[i + 1], c: vs[i + 2],
    det: latticeDet(vs[0], vs[i + 1], vs[i + 2]), shoelace: triangleShoelace(vs[0], vs[i + 1], vs[i + 2]) });
  const fanDetsPos = fan.every((t) => t.det > 0);
  const fanDetPrimitive = fan.every((t) => Math.abs(t.det) === 1);
  const sumFanDet = fan.reduce((s, t) => s + t.det, 0);

  return {
    vertices: vs, nVertices: n, valid, nextIdx, prevIdx, edgePair,
    boundaryLatticePoints: boundary, B,
    hull, latticePointsInConvexHull: inside, interiorLatticePoints: interior, I: interior.length,
    shoelaceSum, shoelace,
    injective, convexCCW, localCCWTurns, strictlyConvexCCW, primitiveEdges, emptyInterior,
    fan, fanDetsPos, fanDetPrimitive, sumFanDet,
    pick: interior.length + B / 2 - 1,
    onBoundary: (p) => bset.has(key(p)),
  };
}

/**
 * Do the hypotheses of `Results.results_picks_theorem` hold?
 *
 *   `(P : LatticePolygon) (S : Finset (ℤ × ℤ)) (hS : ↑S = P.interiorLatticePoints)`
 *   `(hverts : Function.Injective P.vertex) (hsc : StrictlyConvexCCW P)`
 *   ⊢ `volume P.convexHullRegion = ENNReal.ofReal (S.card + P.B / 2 − 1)`
 *
 * `hS` is the one we cannot check by looking: the Lean does not prove that such a finite `S`
 * exists, so the theorem is stated for whatever `S` a caller supplies. The scan above produces
 * one for the bounded polygons here — but that is this module's arithmetic, not the Lean's.
 */
export function picksHypotheses(P) {
  const fail = [];
  if (!P.valid) fail.push("`3 ≤ vertices.length` fails — a `LatticePolygon` needs at least three listed vertices.");
  if (!P.injective) fail.push("`Function.Injective P.vertex` fails — a vertex is listed twice.");
  if (!P.convexCCW) fail.push("`ConvexCCW` fails — some listed vertex is strictly right of some directed edge, so the polygon is not convex in this order.");
  if (!P.localCCWTurns) fail.push("`LocalCCWTurns` fails — some three consecutive vertices do not turn strictly left (collinear, or a clockwise turn).");
  return {
    ok: fail.length === 0, failures: fail,
    strictlyConvexCCW: P.strictlyConvexCCW, injective: P.injective,
    // area = I + B/2 − 1 is the *conclusion*; shoelace is what the Lean computes it from
    shoelace: P.shoelace, pick: P.pick, agree: P.shoelace === P.pick,
  };
}

/* --------------------------------------------------------------------- `DiskEuler.lean` */

/**
 * The counts `triangulated_disk_euler_from_characteristic` is about, for a triangulated disk
 * with `I` interior and `B` boundary lattice points, every lattice point a vertex:
 *
 *   `V = I + B`,  `T = 2I + B − 2`,  `E = 3I + 2B − 3`,  `F = T + 1`
 *
 * `handshake` is the `2E = 3T + B` of `results_pick_count_of_euler`; `euler` is `V − E + F`,
 * which should be 2; `area` is `T/2`, each triangle being det-primitive and so of area `1/2`.
 * All of this is bookkeeping: these are formulas in `I` and `B`, not measurements.
 */
export function triangulationCounts(I, B) {
  const T = 2 * I + B - 2, V = I + B, E = 3 * I + 2 * B - 3, F = T + 1;
  return { I, B, V, E, T, F,
    handshake: 2 * E === 3 * T + B, euler: V - E + F, area: T / 2, pick: I + B / 2 - 1 };
}

/** The fan of an `n`-gon with no interior points: `I = 0`, `B = n`, `T = n − 2`. */
export const fanCounts = (n) => triangulationCounts(0, n);

/* ------------------------------------------------------------------------------ presets */

/** Polygons worth looking at, including ones where the Lean's hypotheses fail. */
export const POLYGON_PRESETS = {
  triangle: { verts: [[0, 0], [4, 0], [1, 3]],
    note: "Strictly convex, distinct vertices: `results_picks_theorem` applies. Area 6, `I = 3`, `B = 8` — and `3 + 8/2 − 1 = 6`." },
  "unit-square": { verts: [[0, 0], [1, 0], [1, 1], [0, 1]],
    note: "The smallest case. `I = 0`, `B = 4`, area `0 + 4/2 − 1 = 1`." },
  "primitive-triangle": { verts: [[0, 0], [1, 0], [0, 1]],
    note: "A det-primitive triangle: `|det| = 1`, area `1/2 = 0 + 3/2 − 1`. `Triangle.shoelace_eq_half_of_isDetPrimitive`." },
  pentagon: { verts: [[0, 0], [4, 1], [5, 4], [2, 6], [-1, 3]],
    note: "A bigger strictly convex polygon; the corner fan has three triangles." },
  "empty-primitive": { verts: [[0, 0], [1, 0], [2, 1], [1, 1]],
    note: "A parallelogram with every edge primitive and no interior lattice point: the shape `results_picks_of_empty_primitive_fan` is about. Area `B/2 − 1 = 4/2 − 1 = 1`, with no `Finset S` hypothesis needed." },
  "collinear-vertex": { verts: [[0, 0], [2, 0], [4, 0], [2, 3]],
    note: "Convex as a *region*, but `(0,0), (2,0), (4,0)` are collinear, so `LocalCCWTurns` fails and the Lean theorem does not apply. Re-list the polygon without the middle vertex and it does." },
  "non-convex": { verts: [[0, 0], [4, 0], [4, 4], [2, 1], [0, 4]],
    note: "A dart. `ConvexCCW` fails. Worse, `interiorLatticePoints` is defined through the *convex hull*, so the Lean's `I` counts points this polygon does not enclose — the formula below is not Pick's for this shape." },
  clockwise: { verts: [[0, 0], [0, 3], [4, 0]],
    note: "Convex, but listed clockwise, so every `latticeDet` comes out negative and `ConvexCCW` fails. The shoelace still has the right magnitude; the Lean asks for the counterclockwise order." },
  "repeated-vertex": { verts: [[0, 0], [3, 0], [0, 3], [0, 0]],
    note: "`Function.Injective P.vertex` fails — the first vertex is listed again at the end." },
};

export const presetPolygon = (name) =>
  polygon((POLYGON_PRESETS[name] || POLYGON_PRESETS.triangle).verts);
export const presetNote = (name) => (POLYGON_PRESETS[name] || POLYGON_PRESETS.triangle).note;
