// Polyhedron data and the face lattice read off a vertex list, mirroring how
// `EulersGem.IsPolytope` and `EulersGem.IsFaceOf` work: a polytope is the convex hull of a
// finite vertex set (`Polytope.lean`), and its faces are the sets a linear functional is
// maximized on (`PolytopeFaces.isFaceOf_convexHull_argmax`). So for the convex presets we do
// not hard-code a face list: we compute it from the coordinates with supporting planes, the
// same recipe the Lean uses. Pure arithmetic, no DOM.
//
// What this does NOT mirror: `affDim`. Here a facet is a 2-face and an edge a 1-face because
// the presets are honest 3-polytopes; the Lean computes the affine dimension of a face from its
// affine span (`AffDim.lean`) instead of assuming it.

const EPS = 1e-7;
const PHI = (1 + Math.sqrt(5)) / 2;

export const sub = (a, b) => [a[0] - b[0], a[1] - b[1], a[2] - b[2]];
export const add = (a, b) => [a[0] + b[0], a[1] + b[1], a[2] + b[2]];
export const scale = (a, k) => [a[0] * k, a[1] * k, a[2] * k];
export const dot = (a, b) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
export const cross = (a, b) => [
  a[1] * b[2] - a[2] * b[1],
  a[2] * b[0] - a[0] * b[2],
  a[0] * b[1] - a[1] * b[0],
];
export const normLen = (a) => Math.hypot(a[0], a[1], a[2]);
export const unit = (a) => { const L = normLen(a) || 1; return scale(a, 1 / L); };
export const centroid = (pts) =>
  scale(pts.reduce((s, p) => add(s, p), [0, 0, 0]), 1 / (pts.length || 1));

/** Newell normal of a polygon given as a list of points: robust for non-triangles. */
export function faceNormal(pts) {
  let n = [0, 0, 0];
  for (let i = 0; i < pts.length; i++) {
    const a = pts[i], b = pts[(i + 1) % pts.length];
    n = add(n, [(a[1] - b[1]) * (a[2] + b[2]), (a[2] - b[2]) * (a[0] + b[0]), (a[0] - b[0]) * (a[1] + b[1])]);
  }
  return n;
}

/**
 * Order a set of coplanar vertex indices into a cycle, counterclockwise seen from outside.
 * `nrm` must be the plane's normal, supplied by the caller: deriving it from the points in
 * their incoming order is not safe, since that order can trace a self-crossing path whose
 * Newell normal vanishes (the four corners of a cube face in index order do exactly that).
 */
function cycleInPlane(verts, idx, inside, nrm) {
  const pts = idx.map((i) => verts[i]);
  const c = centroid(pts);
  const n = unit(nrm);
  // normal pointing away from the body
  const out = dot(sub(c, inside), n) < 0 ? scale(n, -1) : n;
  let u = unit(sub(pts[0], c));
  if (normLen(sub(pts[0], c)) < EPS) u = unit(sub(pts[1], c));
  const v = cross(out, u);
  const ang = idx.map((i) => {
    const d = sub(verts[i], c);
    return [Math.atan2(dot(d, v), dot(d, u)), i];
  });
  ang.sort((a, b) => a[0] - b[0]);
  return ang.map(([, i]) => i);
}

/**
 * Facets (2-faces) of the convex hull of `verts`, by supporting planes: a triple spans a
 * candidate plane, and it is a facet when every other vertex lies weakly on one side. The
 * facet is then every vertex *on* that plane — which is exactly the argmax set of the
 * functional, i.e. a face in the sense of `IsFaceOf` (`PolytopeFaces.lean`).
 * Returns cyclically ordered index lists, counterclockwise seen from outside.
 */
export function facetsOfHull(verts) {
  const inside = centroid(verts);
  const n = verts.length;
  const seen = new Map();
  for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) for (let k = j + 1; k < n; k++) {
    const nrm = cross(sub(verts[j], verts[i]), sub(verts[k], verts[i]));
    if (normLen(nrm) < EPS) continue;                       // degenerate triple
    const nu = unit(nrm), c = dot(nu, verts[i]);
    let lo = 0, hi = 0;
    for (let t = 0; t < n; t++) { const d = dot(nu, verts[t]) - c; if (d < -EPS) lo++; else if (d > EPS) hi++; }
    if (lo && hi) continue;                                 // not a supporting plane
    const on = [];
    for (let t = 0; t < n; t++) if (Math.abs(dot(nu, verts[t]) - c) <= EPS) on.push(t);
    const key = on.join(",");
    if (!seen.has(key)) seen.set(key, cycleInPlane(verts, on, inside, nu));
  }
  return [...seen.values()];
}

/** Unordered edge list `[i, j]` (i < j) read off a face list. */
export function edgesOfFaces(faces) {
  const set = new Set();
  for (const f of faces) for (let i = 0; i < f.length; i++) {
    const a = f[i], b = f[(i + 1) % f.length];
    set.add(a < b ? `${a},${b}` : `${b},${a}`);
  }
  return [...set].map((s) => s.split(",").map(Number)).sort((x, y) => x[0] - y[0] || x[1] - y[1]);
}

/**
 * Make every face agree on orientation by walking the dual graph, then flip the whole thing if
 * the enclosed signed volume came out negative (so every face ends up counterclockwise seen
 * from outside). Works for the toroidal preset too, where "away from the centroid" does not.
 */
export function orientConsistently(verts, faces) {
  const fs = faces.map((f) => f.slice());
  const dirKey = (a, b) => `${a}>${b}`;
  const owner = new Map();                       // directed edge -> face index
  const put = (fi) => { for (let i = 0; i < fs[fi].length; i++) owner.set(dirKey(fs[fi][i], fs[fi][(i + 1) % fs[fi].length]), fi); };
  const undirected = new Map();                  // "min,max" -> [face indices]
  faces.forEach((f, fi) => { for (let i = 0; i < f.length; i++) {
    const a = f[i], b = f[(i + 1) % f.length], k = a < b ? `${a},${b}` : `${b},${a}`;
    if (!undirected.has(k)) undirected.set(k, []);
    undirected.get(k).push(fi);
  } });
  const done = new Set([0]);
  put(0);
  const queue = [0];
  while (queue.length) {
    const fi = queue.shift();
    const f = fs[fi];
    for (let i = 0; i < f.length; i++) {
      const a = f[i], b = f[(i + 1) % f.length];
      const k = a < b ? `${a},${b}` : `${b},${a}`;
      for (const gi of undirected.get(k) || []) {
        if (gi === fi || done.has(gi)) continue;
        // consistent orientation means the shared edge is traversed in opposite directions
        if (owner.get(dirKey(a, b)) === fi && fs[gi].some((_, j) => fs[gi][j] === a && fs[gi][(j + 1) % fs[gi].length] === b))
          fs[gi].reverse();
        done.add(gi); put(gi); queue.push(gi);
      }
    }
  }
  let vol = 0;
  for (const f of fs) for (let i = 1; i + 1 < f.length; i++)
    vol += dot(verts[f[0]], cross(verts[f[i]], verts[f[i + 1]])) / 6;
  if (vol < 0) fs.forEach((f) => f.reverse());
  return fs;
}

/** A polyhedron record: vertices, oriented faces, derived edges and the Euler number. */
export function mk({ verts, faces, name, convex, note }) {
  const fs = orientConsistently(verts, faces);
  const edges = edgesOfFaces(fs);
  return {
    name, verts, faces: fs, edges, convex: !!convex, note: note || "",
    V: verts.length, E: edges.length, F: fs.length,
    euler: verts.length - edges.length + fs.length,
  };
}

/** Build a convex preset from coordinates alone (faces computed, never typed in). */
const hull = (name, verts, note) => mk({ verts, faces: facetsOfHull(verts), name, convex: true, note });

const signs3 = (f) => {
  const out = [];
  for (const a of [-1, 1]) for (const b of [-1, 1]) for (const c of [-1, 1]) out.push(f(a, b, c));
  return out;
};
const cyc3 = (x, y, z) => [[x, y, z], [y, z, x], [z, x, y]];
const evenPerms = (x, y, z) => {
  const out = [];
  for (const s of [1, -1]) for (const t of [1, -1]) for (const p of cyc3(0, 1, 2)) {
    const v = [0, 0, 0];
    v[p[0]] = x; v[p[1]] = s * y; v[p[2]] = t * z;
    out.push(v);
  }
  return out;
};

/** The toroidal "picture frame": a square slab with a square hole. Not convex. */
function pictureFrame() {
  const O = 1.5, I = 0.5, Z = 0.33;
  const oc = [[-O, -O], [O, -O], [O, O], [-O, O]];
  const ic = [[-I, -I], [I, -I], [I, I], [-I, I]];
  const verts = [
    ...oc.map(([x, y]) => [x, y, Z]), ...ic.map(([x, y]) => [x, y, Z]),
    ...oc.map(([x, y]) => [x, y, -Z]), ...ic.map(([x, y]) => [x, y, -Z]),
  ];
  const nx = (k) => (k + 1) % 4;
  const faces = [];
  for (let k = 0; k < 4; k++) faces.push([k, nx(k), 4 + nx(k), 4 + k]);            // top annulus
  for (let k = 0; k < 4; k++) faces.push([8 + k, 8 + nx(k), 12 + nx(k), 12 + k]);  // bottom annulus
  for (let k = 0; k < 4; k++) faces.push([k, nx(k), 8 + nx(k), 8 + k]);            // outer wall
  for (let k = 0; k < 4; k++) faces.push([4 + k, 4 + nx(k), 12 + nx(k), 12 + k]);  // hole wall
  return mk({ verts, faces, name: "picture frame (toroidal)", convex: false,
    note: "A solid square frame with a square hole: 16 − 32 + 16 = 0, not 2. It is a polyhedron but it is **not convex**, so it is not the convex hull of its vertices and `EulersGem.IsPolytope` is false for it. The Lean theorems say nothing about it." });
}

export const PRESETS = {
  tetrahedron: () => hull("tetrahedron {3,3}", [[1, 1, 1], [1, -1, -1], [-1, 1, -1], [-1, -1, 1]],
    "The 3-simplex. Face lattice computed in `SimplexFaces.lean`; geometric Euler relation in `GeometricPlatonic.tetrahedron_euler_relation`."),
  cube: () => hull("cube {4,3}", signs3((a, b, c) => [a, b, c]),
    "`Cube.lean` proves the H-representation, the face lattice (faces are subcubes), `V=8, E=12, F=6` and `V − E + F = 2` from Euler–Poincaré."),
  octahedron: () => hull("octahedron {3,4}", [[1, 0, 0], [-1, 0, 0], [0, 1, 0], [0, -1, 0], [0, 0, 1], [0, 0, -1]],
    "The cross-polytope. `Octahedron.lean` proves its H-representation (a padding trick), its face lattice, `V=6, E=12, F=8` and Euler from the root."),
  dodecahedron: () => hull("dodecahedron {5,3}",
    [...signs3((a, b, c) => [a, b, c]), ...evenPerms(0, 1 / PHI, PHI)],
    "**Not constructed in the Lean.** It exists in `Platonic.lean` only as the `RegularNumbers` record `(V,E,F,s,m) = (20,30,12,5,3)` — Euler bookkeeping, not a polytope. This picture is just a picture."),
  icosahedron: () => hull("icosahedron {3,5}", evenPerms(0, 1, PHI),
    "**Not constructed in the Lean** either: `Platonic.icosahedron` is the record `(12,30,20,3,5)`. Golden-ratio coordinates put the face lattice out of reach of `decide`."),
  "triangular-prism": () => hull("triangular prism",
    [0, 1, 2].flatMap((k) => [1, -1].map((z) => [Math.cos((2 * Math.PI * k) / 3 + Math.PI / 2), Math.sin((2 * Math.PI * k) / 3 + Math.PI / 2), z])),
    "A convex 3-polytope that is not regular: two triangles, three squares. `V − E + F = 6 − 9 + 5 = 2` all the same — the Lean theorem asks only for `IsPolytope` and `affDim = 3`."),
  "square-pyramid": () => hull("square pyramid", [...[[-1, -1, 0], [1, -1, 0], [1, 1, 0], [-1, 1, 0]], [0, 0, 1.4]],
    "Another non-regular convex example: `5 − 8 + 5 = 2`. Its vertices have different degrees, so no single `m` works and the Schläfli argument does not apply to it."),
  "picture-frame": pictureFrame,
};

export const CONVEX_PRESETS = Object.keys(PRESETS).filter((k) => k !== "picture-frame");

// `facetsOfHull` is cubic in the vertex count, so build each preset once.
const cache = new Map();
export function preset(name) {
  const k = PRESETS[name] ? name : "tetrahedron";
  if (!cache.has(k)) cache.set(k, PRESETS[k]());
  return cache.get(k);
}

/** Degree of a vertex: how many edges meet it. The Schläfli `m`, when it is the same at each. */
export const vertexDegree = (poly, vi) => poly.edges.filter(([a, b]) => a === vi || b === vi).length;
/** Faces meeting a vertex. */
export const facesAt = (poly, vi) => poly.faces.map((f, i) => [f, i]).filter(([f]) => f.includes(vi));
/** How many faces each edge lies in — the diamond property of `PlatonicOfEuler` says 2. */
export function edgeFaceCounts(poly) {
  const m = new Map(poly.edges.map(([a, b]) => [`${a},${b}`, 0]));
  for (const f of poly.faces) for (let i = 0; i < f.length; i++) {
    const a = f[i], b = f[(i + 1) % f.length], k = a < b ? `${a},${b}` : `${b},${a}`;
    m.set(k, (m.get(k) || 0) + 1);
  }
  return m;
}
/** The Schläfli pair, when every face has the same size and every vertex the same degree. */
export function schlafliOf(poly) {
  const sizes = new Set(poly.faces.map((f) => f.length));
  const degs = new Set(poly.verts.map((_, i) => vertexDegree(poly, i)));
  if (sizes.size !== 1 || degs.size !== 1) return null;
  return [[...sizes][0], [...degs][0]];
}

/**
 * Cut a corner off: truncate the vertex `vi`, replacing it by one new vertex per incident edge
 * and one new face. `V ↦ V − 1 + d`, `E ↦ E + d`, `F ↦ F + 1`, so `V − E + F` is unchanged —
 * which is the point. Still a convex polytope when the original was and `t` is small.
 */
export function truncateVertex(poly, vi, t = 0.34) {
  const inc = poly.faces.filter((f) => f.includes(vi));
  if (!inc.length) return poly;
  const nbrs = [];
  const corner = new Map();                                    // neighbour index -> new vertex index
  const verts = poly.verts.filter((_, i) => i !== vi).map((p) => p.slice());
  const shift = (i) => (i > vi ? i - 1 : i);                   // index after dropping vi
  for (const f of inc) {
    const k = f.indexOf(vi);
    const p = f[(k - 1 + f.length) % f.length], s = f[(k + 1) % f.length];
    for (const u of [p, s]) if (!corner.has(u)) {
      corner.set(u, verts.length);
      verts.push(add(poly.verts[vi], scale(sub(poly.verts[u], poly.verts[vi]), t)));
      nbrs.push(u);
    }
  }
  const faces = [];
  for (const f of poly.faces) {
    if (!f.includes(vi)) { faces.push(f.map(shift)); continue; }
    const k = f.indexOf(vi);
    const p = f[(k - 1 + f.length) % f.length], s = f[(k + 1) % f.length];
    const out = [];
    for (let i = 0; i < f.length; i++) {
      const u = f[(k + 1 + i) % f.length];                      // start just after vi
      if (u === vi) { out.push(corner.get(p), corner.get(s)); } else out.push(shift(u));
    }
    faces.push(out);
  }
  // the new face: the corner polygon, in the order the incident faces fan around vi
  const succOf = new Map(inc.map((f) => {
    const k = f.indexOf(vi);
    return [f[(k - 1 + f.length) % f.length], f[(k + 1) % f.length]];
  }));
  const ring = [];
  let u = nbrs[0];
  for (let i = 0; i < nbrs.length && u != null && !ring.includes(u); i++) { ring.push(u); u = succOf.get(u); }
  faces.push((ring.length === nbrs.length ? ring : nbrs).map((x) => corner.get(x)));
  return mk({ verts, faces, name: `${poly.name}, one corner cut`, convex: poly.convex,
    note: `Truncating a vertex of degree ${nbrs.length}: one vertex out, ${nbrs.length} in, ${nbrs.length} new edges, one new face. The alternating sum cannot notice.` });
}
