// Tests for the widget logic modules, each assertion keyed to the Lean definition it
// mirrors. Run by `npm test`. No browser: the modules are pure, and `dom.js`/`widgets.js`
// only touch `document` inside their functions.
import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import * as PH from "../assets/polyhedra.js";
import * as FL from "../assets/facelattice.js";
import * as SC from "../assets/schlafli.js";
import * as LT from "../assets/lattice.js";
import { stepper, clampStep } from "../assets/dom.js";
import { WIDGET_TYPES, mountWidget } from "../assets/widgets.js";
import yaml from "js-yaml";

const SITE = path.dirname(path.dirname(fileURLToPath(import.meta.url)));
let n = 0;
const t = (name, f) => { f(); n++; };
const eq = (a, b, m) => assert.deepEqual(a, b, m);

// ================================================= Polytope.lean / PolytopeFaces.lean
// The convex presets' faces are not typed in: they are computed from the coordinates by
// supporting planes, which is `PolytopeFaces.isFaceOf_convexHull_argmax`'s recipe. So these
// assertions test that the recipe reproduces the face lattices the Lean proves.

t("every convex preset has V − E + F = 2, with the V/E/F the Lean proves where it proves them", () => {
  const expect = {
    tetrahedron: [4, 6, 4],        // GeometricPlatonic.tetrahedron_face_counts
    cube: [8, 12, 6],              // Cube.cube_face_counts
    octahedron: [6, 12, 8],        // Octahedron.octahedron_face_counts
    dodecahedron: [20, 30, 12],    // Platonic3.dodecahedron_faceData
    icosahedron: [12, 30, 20],     // Platonic3.icosahedron_faceData
    "triangular-prism": [6, 9, 5],
    "square-pyramid": [5, 8, 5],
  };
  for (const k of PH.CONVEX_PRESETS) {
    const p = PH.preset(k);
    eq([p.V, p.E, p.F], expect[k], `${k} face counts`);
    assert.equal(p.euler, 2, `${k}: V − E + F = 2, results_euler_polyhedron`);
    assert.ok(p.convex, `${k} is a convex hull, so IsPolytope holds for it`);
  }
});

t("the toroidal preset is the honest non-example: V − E + F = 0 and not a convex hull", () => {
  const p = PH.preset("picture-frame");
  eq([p.V, p.E, p.F], [16, 32, 16]);
  assert.equal(p.euler, 0, "a torus has characteristic 0, so the Lean theorem cannot apply");
  assert.equal(p.convex, false, "IsPolytope is 'convex hull of a finite set' — this is not one");
});

t("faces are consistently oriented: every edge is traversed once each way (the diamond property)", () => {
  for (const k of Object.keys(PH.PRESETS)) {
    const p = PH.preset(k);
    const dir = new Map();
    for (const f of p.faces) for (let i = 0; i < f.length; i++) {
      const a = f[i], b = f[(i + 1) % f.length];
      assert.ok(!dir.has(`${a}>${b}`), `${k}: edge ${a}→${b} traversed twice the same way`);
      dir.set(`${a}>${b}`, true);
    }
    for (const [a, b] of p.edges) {
      assert.ok(dir.has(`${a}>${b}`) && dir.has(`${b}>${a}`), `${k}: edge ${a}-${b} needs both directions`);
    }
    // the diamond property: every edge lies in exactly two 2-faces (assumed as `hedge_faces`
    // in PlatonicOfEuler.regular_polytope_counts, proved there only for the three built solids)
    for (const c of PH.edgeFaceCounts(p).values()) assert.equal(c, 2, `${k}: every edge in two faces`);
  }
});

t("the Schläfli pair of each regular preset is the one Platonic.lean names", () => {
  eq(PH.schlafliOf(PH.preset("tetrahedron")), [3, 3]);
  eq(PH.schlafliOf(PH.preset("cube")), [4, 3]);
  eq(PH.schlafliOf(PH.preset("octahedron")), [3, 4]);
  eq(PH.schlafliOf(PH.preset("dodecahedron")), [5, 3]);
  eq(PH.schlafliOf(PH.preset("icosahedron")), [3, 5]);
  // the two non-regular convex presets have no pair at all, so the argument says nothing
  assert.equal(PH.schlafliOf(PH.preset("triangular-prism")), null);
  assert.equal(PH.schlafliOf(PH.preset("square-pyramid")), null);
  for (const k of ["tetrahedron", "cube", "octahedron", "dodecahedron", "icosahedron"]) {
    const [s, m] = PH.schlafliOf(PH.preset(k));
    assert.ok(SC.isSchlafliPair(s, m), `${k} is one of Platonic.schlafliPairs`);
  }
});

t("cutting a corner changes V, E, F but never V − E + F", () => {
  for (const k of ["tetrahedron", "cube", "octahedron", "triangular-prism", "square-pyramid"]) {
    const p = PH.preset(k);
    for (let vi = 0; vi < p.V; vi++) {
      const d = PH.vertexDegree(p, vi);
      const q = PH.truncateVertex(p, vi);
      eq([q.V, q.E, q.F], [p.V - 1 + d, p.E + d, p.F + 1], `${k}: truncating vertex ${vi} of degree ${d}`);
      assert.equal(q.euler, 2, `${k}: truncation keeps V − E + F = 2`);
    }
  }
  // twice over, to check the result is still a usable polyhedron
  let p = PH.preset("cube");
  for (let i = 0; i < 3; i++) { p = PH.truncateVertex(p, 0); assert.equal(p.euler, 2); }
});

// ================================================= Polytope.lean: faceEulerSum
t("faceEulerSum of the n-simplex and the n-cube is 1, body counted, empty face not", () => {
  for (let n2 = 0; n2 <= 8; n2++) {
    const s = FL.simplexFaceCounts(n2), c = FL.cubeFaceCounts(n2);
    assert.equal(s.length, n2 + 1);
    assert.equal(FL.faceEulerSum(s), 1, `simplex n=${n2}: Euler_Poincare_of_isPolytope says 1`);
    assert.equal(FL.faceEulerSum(c), 1, `cube n=${n2}: the same`);
    assert.equal(s[n2], 1, "the body is the unique top-dimensional face");
    assert.equal(c[n2], 1, "the body is the unique top-dimensional face");
    assert.equal(s[0], n2 + 1, "EulersGem.faceCount n 0 = n + 1");
    assert.equal(c[0], 2 ** n2, "the n-cube has 2^n vertices");
  }
  // exact counts, against EulersGem.faceCount / Cube.affDim_face
  eq(FL.simplexFaceCounts(3), [4, 6, 4, 1]);
  eq(FL.cubeFaceCounts(3), [8, 12, 6, 1]);
  eq(FL.cubeFaceCounts(4), [16, 32, 24, 8, 1]);
  for (let n2 = 0; n2 <= 8; n2++) for (let d = 0; d <= n2; d++)
    assert.equal(FL.simplexFaceCounts(n2)[d], FL.binom(n2 + 1, d + 1));
});

t("dropping the body turns the characteristic 1 into V − E + F = 2, exactly when n = 3", () => {
  for (const fam of ["simplex", "cube"]) {
    const L = FL.lattice(fam, 3);
    assert.equal(L.sum, 1);
    assert.equal(L.bodyCount, 1, "the only 3-face of a 3-polytope is the body");
    assert.equal(L.withoutBody, 2, "euler_relation_of_isPolytope: remove −1 from 1");
    eq([L.counts[0], L.counts[1], L.counts[2]].reduce((a, b, i) => a + (i === 1 ? -b : b), 0) - L.counts[0], 2 - L.counts[0]);
  }
  // in dimension 2 the same move gives V − E = 1 + 1 = ... let's state it plainly:
  assert.equal(FL.lattice("simplex", 2).withoutBody, 0, "a triangle: 3 − 3 = 0, and 0 + 1 = 1");
  assert.equal(FL.lattice("simplex", 4).withoutBody, 0, "in dimension 4 the body's sign is +, so removing it gives 0");
});

// ================================================= Platonic.lean
t("Platonic.mul_euler_int and sub_mul_lt_four, as arithmetic", () => {
  // coeff = 4 − defect, i.e. (s−2)(m−2) < 4 ↔ 0 < 2s + 2m − sm
  for (let s = 3; s <= 12; s++) for (let m = 3; m <= 12; m++) {
    assert.equal(SC.coeff(s, m), 4 - SC.defect(s, m), `coeff = 4 − (s−2)(m−2) at ${s},${m}`);
    assert.equal(SC.defect(s, m) < 4, SC.coeff(s, m) > 0);
    // sub_mul_lt_four: with s,m ≥ 3 the bound (s−2)(m−2) < 4 holds for exactly the five pairs
    assert.equal(SC.defect(s, m) < 4, SC.isSchlafliPair(s, m), `${s},${m}: defect < 4 iff one of the five`);
  }
  eq(SC.SCHLAFLI_PAIRS, [[3, 3], [3, 4], [3, 5], [4, 3], [5, 3]]);
  assert.equal(SC.SCHLAFLI_PAIRS.length, 5, "Platonic.card_schlafliPairs = 5");
});

t("the solved (V, E, F) of each Schläfli pair are the five RegularNumbers records", () => {
  const want = { "3,3": [4, 6, 4], "4,3": [8, 12, 6], "3,4": [6, 12, 8], "5,3": [20, 30, 12], "3,5": [12, 30, 20] };
  for (const [s, m] of SC.SCHLAFLI_PAIRS) {
    const r = SC.solveCounts(s, m);
    assert.ok(r.ok && r.integral, `${s},${m} must solve in positive integers`);
    eq([r.V, r.E, r.F], want[`${s},${m}`], `{${s},${m}}`);
    assert.equal(r.euler, 2, "RegularNumbers.hEuler");
    assert.equal(s * r.F, 2 * r.E, "RegularNumbers.hFace: s·F = 2E");
    assert.equal(m * r.V, 2 * r.E, "RegularNumbers.hVert: m·V = 2E");
    assert.equal(r.E * SC.coeff(s, m), 2 * s * m, "Platonic.mul_euler_int");
    assert.ok(r.E > 0, "Platonic.pos_edges_of_euler");
  }
  // the flat and hyperbolic pairs have no solution at all
  for (const [s, m] of [[4, 4], [3, 6], [6, 3]]) assert.equal(SC.solveCounts(s, m).why, "flat");
  for (const [s, m] of [[4, 5], [5, 4], [5, 5], [3, 7], [7, 3]]) assert.equal(SC.solveCounts(s, m).why, "hyperbolic");
  // and every pair the Lean admits is one the geometric presets realize or the records record
  for (const [s, m] of SC.SCHLAFLI_PAIRS) assert.ok(SC.solidOf(s, m), `{${s},${m}} names a solid`);
  const built = SC.SCHLAFLI_PAIRS.filter(([s, m]) => SC.solidOf(s, m).geometric).length;
  assert.equal(built, 5, "all five are built geometrically in the Lean (PlatonicSolids.lean)");
});

// ================================================= LatticeTriangle.lean
t("edgeGcd and edgeLatticePoints", () => {
  assert.equal(LT.edgeGcd([0, 0], [0, 0]), 0, "edgeGcd_eq_zero_iff: 0 exactly when p = q");
  assert.equal(LT.edgeGcd([0, 0], [3, 0]), 3);
  assert.equal(LT.edgeGcd([1, 1], [4, 7]), 3);
  assert.equal(LT.edgeGcd([0, 0], [2, 1]), 1, "a primitive edge");
  assert.equal(LT.edgeGcd([5, 2], [2, 5]), 3);
  // card_edgeLatticePoints: the segment carries edgeGcd + 1 lattice points, endpoints included
  for (const [p, q] of [[[0, 0], [6, 3]], [[1, 1], [1, 5]], [[-2, 3], [4, -3]], [[0, 0], [1, 0]], [[2, 2], [2, 2]]]) {
    const pts = LT.edgeLatticePoints(p, q);
    assert.equal(pts.length, Math.max(1, LT.edgeGcd(p, q) + 1), `|edgeLatticePoints| for ${p}-${q}`);
    assert.ok(pts.some((r) => r[0] === p[0] && r[1] === p[1]), "self_mem_edgeLatticePoints");
    assert.ok(pts.some((r) => r[0] === q[0] && r[1] === q[1]), "other_mem_edgeLatticePoints");
    for (const r of pts) assert.equal(LT.latticeDet(p, q, r), 0, "every point is on the line");
  }
});

t("latticeDet is twice the signed area, and |det| = 1 means area exactly 1/2", () => {
  assert.equal(LT.latticeDet([0, 0], [1, 0], [0, 1]), 1);
  assert.equal(LT.latticeDet([0, 0], [0, 1], [1, 0]), -1, "swapping two vertices flips the sign");
  assert.equal(LT.latticeDet([0, 0], [2, 0], [4, 0]), 0, "collinear");
  assert.ok(LT.isDetPrimitive([0, 0], [1, 0], [0, 1]));
  assert.equal(LT.triangleShoelace([0, 0], [1, 0], [0, 1]), 1 / 2,
    "Triangle.shoelace_eq_half_of_isDetPrimitive");
  assert.equal(LT.triangleShoelace([0, 0], [4, 0], [0, 3]), 6);
  // latticeDet_translate: it only depends on the differences
  for (const d of [[3, -2], [-5, 7]])
    assert.equal(LT.latticeDet([0, 0], [2, 1], [1, 3]),
      LT.latticeDet([d[0], d[1]], [2 + d[0], 1 + d[1]], [1 + d[0], 3 + d[1]]));
});

// ================================================= LatticePolygon.lean / LatticeFan.lean
t("B is the gcd count on the cyclic edges; I is relative to the convex hull", () => {
  const sq = LT.polygon([[0, 0], [3, 0], [3, 3], [0, 3]]);
  assert.equal(sq.B, 12, "four edges of gcd 3 each, endpoints shared");
  assert.equal(sq.I, 4, "the interior 2×2 block");
  assert.equal(sq.shoelace, 9);
  assert.equal(sq.pick, 4 + 12 / 2 - 1);
  assert.equal(sq.shoelace, sq.pick, "Pick holds for it");
  const unit = LT.polygon([[0, 0], [1, 0], [1, 1], [0, 1]]);
  eq([unit.I, unit.B, unit.shoelace], [0, 4, 1]);
  const prim = LT.polygon([[0, 0], [1, 0], [0, 1]]);
  eq([prim.I, prim.B, prim.shoelace], [0, 3, 1 / 2]);
  assert.ok(prim.primitiveEdges && prim.emptyInterior, "results_picks_of_empty_primitive_fan's shape");
  const tri = LT.presetPolygon("triangle");
  eq([tri.I, tri.B, tri.shoelace], [3, 8, 6], "the `triangle` preset's note must match");
  // the preset named for results_picks_of_empty_primitive_fan must meet all four of its hypotheses
  const ep = LT.presetPolygon("empty-primitive");
  assert.ok(ep.injective && ep.primitiveEdges && ep.strictlyConvexCCW && ep.emptyInterior);
  eq([ep.I, ep.B, ep.shoelace], [0, 4, 1]);
  assert.equal(ep.shoelace, ep.B / 2 - 1, "area = B/2 − 1 when I = 0");
});

t("StrictlyConvexCCW = ConvexCCW ∧ LocalCCWTurns, and each half can fail on its own", () => {
  const ccw = LT.polygon([[0, 0], [4, 0], [1, 3]]);
  assert.ok(ccw.convexCCW && ccw.localCCWTurns && ccw.strictlyConvexCCW);
  const cw = LT.polygon([[0, 0], [0, 3], [4, 0]]);
  assert.equal(cw.convexCCW, false, "listed clockwise: ConvexCCW fails");
  assert.equal(cw.shoelace, 6, "the shoelace magnitude does not care about the order");
  const coll = LT.polygon([[0, 0], [2, 0], [4, 0], [2, 3]]);
  assert.ok(coll.convexCCW, "a convex region, so no vertex is right of an edge");
  assert.equal(coll.localCCWTurns, false, "but three consecutive vertices are collinear");
  assert.equal(coll.strictlyConvexCCW, false, "so results_picks_theorem does not apply");
  const relisted = LT.polygon([[0, 0], [4, 0], [2, 3]]);
  assert.ok(relisted.strictlyConvexCCW, "drop the middle collinear vertex and it does");
  assert.equal(relisted.shoelace, coll.shoelace, "same region, same area");
  const dart = LT.polygon([[0, 0], [4, 0], [4, 4], [2, 1], [0, 4]]);
  assert.equal(dart.convexCCW, false, "a non-convex dart");
  assert.ok(dart.I > 0);
  // the honesty point: I is taken in the convex hull, so it counts points the dart excludes
  assert.ok(dart.latticePointsInConvexHull.some((p) => !LT.inHull(LT.convexHull(dart.vertices.slice(0, 3)), p)));
  assert.notEqual(dart.shoelace, dart.pick, "so I + B/2 − 1 is not the dart's area");
});

t("picksHypotheses names the failing hypothesis of results_picks_theorem", () => {
  for (const name of ["triangle", "unit-square", "primitive-triangle", "pentagon", "empty-primitive"]) {
    const P = LT.presetPolygon(name), hyp = LT.picksHypotheses(P);
    assert.ok(hyp.ok, `${name}: the hypotheses hold`);
    assert.equal(P.shoelace, P.pick, `${name}: area = I + B/2 − 1`);
  }
  for (const name of ["collinear-vertex", "non-convex", "clockwise", "repeated-vertex"]) {
    const hyp = LT.picksHypotheses(LT.presetPolygon(name));
    assert.equal(hyp.ok, false, `${name}: at least one hypothesis fails`);
    assert.ok(hyp.failures.length >= 1);
  }
  assert.ok(LT.picksHypotheses(LT.presetPolygon("repeated-vertex")).failures
    .some((f) => f.includes("Injective")), "a repeated vertex breaks injectivity");
});

t("Pick's identity holds for every strictly convex lattice polygon we can enumerate", () => {
  // every triangle with vertices in a small box: when the Lean's hypotheses hold, so does
  // shoelace = I + B/2 − 1 (which is what results_picks_theorem concludes, for the measure)
  let checked = 0;
  const R = [0, 1, 2, 3];
  for (const ax of R) for (const ay of R) for (const bx of R) for (const by of R) for (const cx of R) for (const cy of R) {
    const P = LT.polygon([[ax, ay], [bx, by], [cx, cy]]);
    if (!P.strictlyConvexCCW || !P.injective) continue;
    assert.equal(P.shoelace, P.pick, `triangle ${ax},${ay} ${bx},${by} ${cx},${cy}`);
    checked++;
  }
  assert.ok(checked > 200, `expected many triangles, got ${checked}`);
  // and the corner fan of a strictly convex polygon is positively oriented (FanDetsPos, which
  // LatticeFan.FanDetsPos_of_strictlyConvexCCW discharges from StrictlyConvexCCW + injectivity)
  for (const name of ["triangle", "pentagon", "unit-square", "empty-primitive"]) {
    const P = LT.presetPolygon(name);
    assert.ok(P.fanDetsPos, `${name}: FanDetsPos`);
    assert.equal(P.fan.length, P.nVertices - 2, "a fan of an n-gon has n − 2 triangles");
    assert.equal(P.fan.reduce((s, x) => s + x.shoelace, 0), P.shoelace,
      "LatticeFan: the fan shoelaces add up to the polygon shoelace");
  }
});

// ================================================= DiskEuler.lean
t("the triangulated-disk counts satisfy handshaking and V − E + F = 2", () => {
  for (let I = 0; I <= 12; I++) for (let B = 3; B <= 20; B++) {
    const c = LT.triangulationCounts(I, B);
    assert.ok(c.handshake, `2E = 3T + B at I=${I}, B=${B}`);
    assert.equal(c.euler, 2, `triangulated_disk_euler_from_characteristic at I=${I}, B=${B}`);
    assert.equal(c.area, c.pick, "results_pick_count_of_euler: T/2 = I + B/2 − 1");
    assert.equal(c.F, c.T + 1, "hF: the triangles plus the outer face");
    assert.equal(c.V, I + B, "hV");
  }
  // results_fan_pick_of_euler is exactly the I = 0 line: (n−2)/2 = n/2 − 1
  for (let nn = 3; nn <= 20; nn++) {
    const c = LT.fanCounts(nn);
    assert.equal(c.T, nn - 2);
    assert.equal(c.area, nn / 2 - 1, "results_fan_pick_of_euler");
  }
});

// ================================================= plumbing
// Several widgets re-render themselves from the stepper's callback, so the stepper must not
// fire it while being constructed — that recursed forever in an earlier revision.
t("stepper clamps, and does not fire onset on construction", () => {
  const mk = () => ({ children: [], className: "", textContent: "", nodeType: 1,
    setAttribute() {}, addEventListener() {}, append(...k) { this.children.push(...k); } });
  globalThis.document = { createElement: mk, createTextNode: (s) => ({ nodeType: 3, textContent: String(s) }) };
  assert.equal(clampStep(-3, 5), 0);
  assert.equal(clampStep(9, 5), 5);
  const calls = [];
  const st = stepper(3, (i) => calls.push(i), 7);
  eq(calls, [], "onset must not fire during construction");
  assert.equal(st.index, 3, "i0 is clamped to total");
  st.go(1); st.go(-5); st.go(99);
  eq(calls, [1, 0, 3]);
  delete globalThis.document;
});

t("every widget type the schema allows is implemented, and no extras", () => {
  const schema = JSON.parse(fs.readFileSync(path.join(SITE, "schema/node.schema.json"), "utf8"));
  const allowed = schema.properties.widgets.items.properties.type.enum;
  eq(WIDGET_TYPES.slice().sort(), allowed.slice().sort(), "widgets.js registry = the schema enum");
});

// Mount every widget spec that any node actually asks for, against a stub DOM. This catches a
// runtime error or a bad config in a node's frontmatter, which the schema cannot see.
t("every widget spec in every node mounts without throwing", () => {
  const mkEl = (tag) => ({
    tagName: tag, children: [], className: "", _attrs: {}, style: {}, value: "",
    nodeType: 1, textContent: "", _html: "",
    setAttribute(k, v) { this._attrs[k] = v; }, getAttribute(k) { return this._attrs[k]; },
    addEventListener() {}, removeEventListener() {}, setPointerCapture() {},
    append(...k) { for (const c of k.flat()) if (c != null) this.children.push(c); },
    appendChild(c) { this.children.push(c); return c; },
    querySelectorAll() { return []; }, querySelector() { return null; },
    get innerHTML() { return this._html; }, set innerHTML(v) { this._html = v; this.children = []; },
  });
  globalThis.document = {
    createElement: mkEl, createElementNS: (_ns, tag) => mkEl(tag),
    createTextNode: (s) => ({ nodeType: 3, textContent: String(s) }),
    getElementById: () => mkEl("div"),
  };
  try {
    const dir = path.join(SITE, "nodes");
    let mounted = 0;
    for (const f of fs.existsSync(dir) ? fs.readdirSync(dir).filter((x) => x.endsWith(".md")) : []) {
      const src = fs.readFileSync(path.join(dir, f), "utf8");
      const m = src.match(/^---\n([\s\S]*?)\n---\n/);
      if (!m) continue;
      const fm = yaml.load(m[1]);
      for (const spec of fm.widgets || []) {
        const box = mkEl("div");
        mountWidget(box, spec);
        // mountWidget swallows exceptions into a <p class="err"> child; catch that too
        const err = box.children.flatMap((c) => c.children || []).find((c) => c.className === "err");
        assert.ok(!err, `${f}: widget '${spec.type}' failed: ${err?.children?.[0]?.textContent}`);
        mounted++;
      }
    }
    assert.ok(mounted > 30, `expected many widget instances, mounted ${mounted}`);
  } finally { delete globalThis.document; }
});

t("every widget config a node asks for names a real preset", () => {
  const dir = path.join(SITE, "nodes");
  if (!fs.existsSync(dir)) return;
  for (const f of fs.readdirSync(dir).filter((x) => x.endsWith(".md"))) {
    const src = fs.readFileSync(path.join(dir, f), "utf8");
    for (const m of src.matchAll(/^\s*(?:preset|solid):\s*([a-z0-9-]+)\s*$/gim)) {
      const v = m[1];
      assert.ok(PH.PRESETS[v] || LT.POLYGON_PRESETS[v], `${f}: unknown preset '${v}'`);
    }
  }
});

console.log(`widget logic: all ${n} test groups passed`);
