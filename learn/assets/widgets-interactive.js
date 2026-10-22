// The drawing-heavy widgets: rotatable polyhedra, face-lattice tables, the Schläfli grid, a
// lattice-polygon playground and a triangulation counter. The arithmetic each one shows lives
// in the modules that mirror the Lean (polyhedra.js, facelattice.js, schlafli.js, lattice.js);
// these functions only draw it and wire up the controls.
//
// Every one of them is an *illustration* and says so. A picture of a cube is not a proof about
// convex polytopes, and a scan over a bounding box is not a theorem about lattice points.
import { h, svg, esc, field, row, btn, yes, select, num, illustration, stepper } from "./dom.js";
import * as PH from "./polyhedra.js";
import * as FL from "./facelattice.js";
import * as SC from "./schlafli.js";
import * as LT from "./lattice.js";

const BLUE = [102, 217, 239], GREEN = [166, 226, 46], PINK = [249, 38, 114], ORANGE = [253, 151, 31];
const rgb = (c, k = 1) => `rgb(${c.map((x) => Math.round(Math.min(255, x * k))).join(",")})`;
const frac = (q) => (Number.isInteger(q) ? String(q) : `${Math.round(q * 2)}/2`);

// ---------------------------------------------------------------- polyhedron
function polyhedronWidget(el, cfg = {}) {
  const show = cfg.show || ["counts", "incidence"];
  const allowed = cfg.presets || Object.keys(PH.PRESETS);
  let name = allowed.includes(cfg.preset) ? cfg.preset : allowed[0];
  let base = PH.preset(name), poly = base;
  let yaw = 0.62, pitch = -0.38, mode = cfg.mode === "wireframe" ? "wireframe" : "solid";
  let sel = null, cuts = 0;
  const box = h("div");
  el.append(box);

  const S = 300, R = 112;
  const project = (p) => {
    const cy = Math.cos(yaw), sy = Math.sin(yaw), cp = Math.cos(pitch), sp = Math.sin(pitch);
    const x1 = p[0] * cy + p[2] * sy, z1 = -p[0] * sy + p[2] * cy;
    const y2 = p[1] * cp - z1 * sp, z2 = p[1] * sp + z1 * cp;
    return [x1, y2, z2];
  };
  const radius = () => Math.max(1, Math.max(...poly.verts.map((p) => PH.normLen(p))));
  const screen = (p) => { const [x, y] = project(p), k = R / radius(); return [S / 2 + x * k, S / 2 - y * k]; };

  function paint(sv) {
    sv.innerHTML = "";
    const depth = poly.faces.map((f) => PH.centroid(f.map((i) => poly.verts[i]))).map((c) => project(c)[2]);
    const order = poly.faces.map((_, i) => i).sort((a, b) => depth[a] - depth[b]);
    const selFace = sel?.kind === "face" ? sel.i : null;
    const front = new Set();                        // vertices/edges on a face pointing at us
    poly.faces.forEach((f, i) => {
      const nz = project(PH.unit(PH.faceNormal(f.map((j) => poly.verts[j]))))[2];
      if (nz > 0) { for (const j of f) front.add(j); }
    });
    for (const i of order) {
      const f = poly.faces[i];
      const nz = project(PH.unit(PH.faceNormal(f.map((j) => poly.verts[j]))))[2];
      const lit = 0.3 + 0.7 * Math.max(0, nz);
      const pts = f.map((j) => screen(poly.verts[j]).join(",")).join(" ");
      if (mode === "solid" || i === selFace)
        sv.append(svg("polygon", { points: pts, class: "pick",
          fill: i === selFace ? rgb(PINK, 0.85) : rgb(BLUE, lit * 0.75),
          "fill-opacity": mode === "solid" ? (i === selFace ? 0.95 : 0.88) : 0.5,
          stroke: "#1e1f1c", "stroke-width": 1,
          onclick: () => { if (!drag.moved) { sel = sel?.kind === "face" && sel.i === i ? null : { kind: "face", i }; run(); } } }));
      else
        sv.append(svg("polygon", { points: pts, fill: "none", stroke: "none" }));
    }
    for (const [a, b] of poly.edges) {
      const [x1, y1] = screen(poly.verts[a]), [x2, y2] = screen(poly.verts[b]);
      const hidden = !(front.has(a) && front.has(b));
      const on = sel?.kind === "edge" && sel.a === a && sel.b === b;
      sv.append(svg("line", { x1, y1, x2, y2, class: "pick",
        stroke: on ? rgb(ORANGE) : hidden ? "#5c5b4f" : "#a59f85",
        "stroke-width": on ? 3.4 : hidden ? 1 : 1.8,
        "stroke-dasharray": hidden && mode === "wireframe" ? "3 3" : null,
        "stroke-linecap": "round",
        onclick: () => { if (!drag.moved) { sel = on ? null : { kind: "edge", a, b }; run(); } } }));
    }
    poly.verts.forEach((p, i) => {
      const [x, y] = screen(p);
      const on = sel?.kind === "vertex" && sel.i === i;
      sv.append(svg("circle", { cx: x, cy: y, r: on ? 6.5 : 4.5, class: "pick",
        fill: on ? rgb(ORANGE) : rgb(GREEN), stroke: "#1e1f1c", "stroke-width": 1,
        onclick: () => { if (!drag.moved) { sel = on ? null : { kind: "vertex", i }; run(); } } }));
    });
  }

  const drag = { on: false, moved: false, x: 0, y: 0 };
  function wire(sv) {
    const down = (e) => { drag.on = true; drag.moved = false; drag.x = e.clientX; drag.y = e.clientY; sv.setPointerCapture?.(e.pointerId); };
    const move = (e) => {
      if (!drag.on) return;
      const dx = e.clientX - drag.x, dy = e.clientY - drag.y;
      if (Math.abs(dx) + Math.abs(dy) > 4) drag.moved = true;
      drag.x = e.clientX; drag.y = e.clientY;
      yaw += dx * 0.012;
      pitch = Math.max(-1.45, Math.min(1.45, pitch + dy * 0.012));
      paint(sv);
      e.preventDefault();
    };
    const up = () => { drag.on = false; setTimeout(() => { drag.moved = false; }, 0); };
    sv.addEventListener("pointerdown", down);
    sv.addEventListener("pointermove", move);
    sv.addEventListener("pointerup", up);
    sv.addEventListener("pointercancel", up);
    sv.addEventListener("pointerleave", up);
  }

  function run() {
    box.innerHTML = "";
    const sv = svg("svg", { viewBox: `0 0 ${S} ${S}`, class: "diagram-svg", style: `max-width:${S}px;touch-action:none;cursor:grab` });
    const controls = [field("solid", select(allowed, name, (v) => {
      name = v; base = PH.preset(v); poly = base; sel = null; cuts = 0; run();
    }, allowed.map((k) => PH.preset(k).name)))];
    controls.push(btn(mode === "solid" ? "wireframe" : "solid", () => { mode = mode === "solid" ? "wireframe" : "solid"; run(); }));
    if (show.includes("truncate")) {
      controls.push(btn(sel?.kind === "vertex" ? `cut corner ${sel.i}` : "cut a corner", () => {
        poly = PH.truncateVertex(poly, sel?.kind === "vertex" ? sel.i : 0, 0.3 + 0.08 * (cuts % 2));
        cuts++; sel = null; run();
      }, { class: "primary" }));
      if (cuts) controls.push(btn("undo all cuts", () => { poly = base; cuts = 0; sel = null; run(); }));
    }
    box.append(row(...controls), sv,
      h("p", { class: "small muted", html: "Drag (or swipe) to turn it. Tap a vertex, an edge or a face to pick it out." }));
    paint(sv); wire(sv);

    const facts = [];
    if (show.includes("counts")) {
      facts.push(`<p><b>V = ${poly.V}</b> &nbsp; <b>E = ${poly.E}</b> &nbsp; <b>F = ${poly.F}</b> &nbsp;⟶&nbsp;
        <b>V − E + F = ${poly.euler}</b> ${poly.euler === 2
          ? `<span style="color:var(--green)">= 2</span>`
          : `<span style="color:var(--pink)">≠ 2</span>`}</p>`);
      facts.push(`<p class="small">Convex hull of its vertices (so <code>IsPolytope</code>): ${yes(poly.convex)}.
        ${poly.convex
          ? `With <code>affDim p = 3</code>, <a href="#/node/Results.results_euler_polyhedron"><code>results_euler_polyhedron</code></a> applies and forces the 2.`
          : `<b style="color:var(--pink)">The Lean theorems do not apply.</b> <code>IsPolytope</code> is "convex hull of a finite set", and this is not one.`}</p>`);
    }
    if (show.includes("incidence")) {
      const sizes = {}; for (const f of poly.faces) sizes[f.length] = (sizes[f.length] || 0) + 1;
      const degs = {}; poly.verts.forEach((_, i) => { const d = PH.vertexDegree(poly, i); degs[d] = (degs[d] || 0) + 1; });
      const ef = [...PH.edgeFaceCounts(poly).values()];
      const pair = PH.schlafliOf(poly);
      facts.push(`<p class="small">Face sizes: ${Object.entries(sizes).map(([k, v]) => `${v}×${k}-gon`).join(", ")}
        · vertex degrees: ${Object.entries(degs).map(([k, v]) => `${v}×${k}`).join(", ")}
        · every edge in exactly two faces (the <i>diamond property</i>, a hypothesis in
        <a href="#/node/Platonic.regular_polytope_counts"><code>regular_polytope_counts</code></a>):
        ${yes(ef.every((c) => c === 2))}</p>`);
      facts.push(`<p class="small">Schläfli pair: ${pair
        ? `<code>{${pair[0]},${pair[1]}}</code> — ${SC.isSchlafliPair(pair[0], pair[1]) ? `one of <a href="#/node/Platonic.schlafliPairs">the five</a>` : `<b style="color:var(--pink)">not</b> one of the five`}`
        : `<span class="muted">none: the faces or the vertices are not all alike, so no <code>(s, m)</code> describes it</span>`}</p>`);
    }
    if (sel?.kind === "vertex") facts.push(`<p class="small">Vertex ${sel.i} at (${poly.verts[sel.i].map((x) => x.toFixed(2)).join(", ")}), degree ${PH.vertexDegree(poly, sel.i)}, on ${PH.facesAt(poly, sel.i).length} faces. <span class="muted">A 0-dimensional face: <code>affDim {x} = 0</code> (<code>AffDim.affDim_singleton</code>).</span></p>`);
    if (sel?.kind === "edge") facts.push(`<p class="small">Edge ${sel.a}–${sel.b}, in ${PH.edgeFaceCounts(poly).get(`${sel.a},${sel.b}`)} faces. <span class="muted">A 1-dimensional face; <code>EdgeVertices.ncard_vertices_of_edge</code> proves in general that it has exactly two vertices.</span></p>`);
    if (sel?.kind === "face") facts.push(`<p class="small">Face ${sel.i}: ${poly.faces[sel.i].length} vertices (${poly.faces[sel.i].join(", ")}), ${poly.faces[sel.i].length} edges. <span class="muted">A 2-dimensional face.</span></p>`);
    box.append(h("div", { html: facts.join("") }));
    if (poly.note) box.append(h("p", { class: "small muted", html: mdish(poly.note) }));
    box.append(illustration("Illustration. The counts here come from the coordinates — for the convex presets the faces are computed by supporting planes, the recipe of `PolytopeFaces.isFaceOf_convexHull_argmax`, in floating point. The Lean counts `IsFaceOf`/`affDim` face *sets* exactly."));
  }
  run();
}
const mdish = (s) => esc(s).replace(/`([^`]+)`/g, "<code>$1</code>").replace(/\*\*([^*]+)\*\*/g, "<b>$1</b>").replace(/\*([^*]+)\*/g, "<i>$1</i>");

// ---------------------------------------------------------------- face-lattice
function faceLatticeWidget(el, cfg = {}) {
  const fams = cfg.family === "simplex" || cfg.family === "cube" ? [cfg.family] : ["simplex", "cube"];
  let n = Number.isInteger(cfg.n) ? cfg.n : 3;
  const box = h("div");
  el.append(box);

  function table(fam) {
    const L = FL.lattice(fam, n);
    const head = h("tr", {}, h("th", {}, "d"), ...L.counts.map((_, d) => h("th", {}, String(d))), h("th", {}, "Σ (−1)ᵈ fᵈ"));
    const dims = h("tr", {}, h("th", {}, ""), ...L.counts.map((_, d) =>
      h("td", { class: "small muted" }, d === n ? "the body" : (FL.DIM_NAMES[d] || `${d}-faces`))), h("td", {}, ""));
    const vals = h("tr", {}, h("th", {}, "fᵈ"),
      ...L.counts.map((c, d) => h("td", { class: d === n ? "acc" : null }, (d % 2 ? "−" : "") + c)),
      h("td", { class: "acc" }, String(L.sum)));
    return h("div", {},
      h("h4", {}, `${L.name} (n = ${n})`),
      h("div", { class: "scroll" }, h("table", { class: "t" }, h("tbody", {}, head, dims, vals))),
      h("p", { class: "small", html:
        `<code>faceEulerSum = ${L.counts.map((c, d) => `${d ? (d % 2 ? "− " : "+ ") : ""}${c}`).join(" ")} = <b>${L.sum}</b></code>
         ${L.sum === 1 ? `<span style="color:var(--green)"> — the Euler–Poincaré characteristic, as <code>results_euler_characteristic</code> says</span>` : ""}` }),
      h("p", { class: "small", html:
        `Drop the <code>d = ${n}</code> term, the body itself (its coefficient is <code>(−1)<sup>${n}</sup> = ${n % 2 ? "−1" : "+1"}</code>):
         the rest adds up to <b>${L.withoutBody}</b>.${n === 3 ? ` That is <code>V − E + F = ${L.withoutBody}</code>, Euler's polyhedron formula.` : ""}` }));
  }

  function run() {
    box.innerHTML = "";
    box.append(row(field("n", num(n, 0, 6, (v) => { n = Math.max(0, Math.min(6, v)); run(); })),
      h("span", { class: "small muted", html: "affine dimension of the whole thing" })));
    for (const f of fams) box.append(h("div", { class: "sect" }), table(f));
    box.append(h("p", { class: "small muted", html:
      `Counts are exact: <code>C(n+1, d+1)</code> for the simplex (a face is a nonempty set of vertices — <code>EulersGem.faceCount</code>,
       and <code>SimplexFaces.affDim_face</code> says a <code>(d+1)</code>-element set spans a <code>d</code>-dimensional face) and
       <code>2<sup>n−d</sup>·C(n, d)</code> for the cube (fix <code>n − d</code> coordinates to <code>±1</code> — <code>Cube.affDim_face</code>).` }),
      h("p", { class: "small muted", html:
        `The empty face is missing on purpose. <code>IsFaceOf p ∅</code> is true (<code>isFaceOf_empty</code>), but <code>affDim ∅ = −1</code>
         (<code>affDim_empty</code>) and <code>faceEulerSum</code> sums over <code>d ∈ range (n+1)</code>, i.e. <code>d ≥ 0</code>. Put the empty
         face back in with its sign <code>(−1)<sup>−1</sup></code> and you get the 0 of the <i>reduced</i> characteristic instead.` }),
      illustration("Illustration. These are binomial identities about two named families; `results_euler_characteristic` is about every full-dimensional convex polytope, and nothing here proves it."));
  }
  run();
}

// ---------------------------------------------------------------- schlafli
function schlafliWidget(el, cfg = {}) {
  const lo = cfg.lo ?? 3, hi = cfg.hi ?? 8;
  let sel = null;
  const box = h("div");
  el.append(box);

  function run() {
    box.innerHTML = "";
    const rows = SC.grid(lo, hi);
    const head = h("tr", {}, h("th", {}, "s \\ m"), ...rows[0].map((c) => h("th", {}, String(c.m))));
    const body = rows.map((r) => h("tr", {}, h("th", {}, String(r[0].s)),
      ...r.map((c) => h("td", { class: `pick${c.pair ? " hit" : ""}`,
        style: "cursor:pointer", title: `(s−2)(m−2) = ${c.defect}`,
        onclick: () => { sel = c; run(); } },
        c.pair ? `${c.defect}` : `${c.defect}`))));
    box.append(h("p", { class: "small", html:
      `Each cell is <code>(s − 2)(m − 2)</code>. <a href="#/node/Platonic.sub_mul_lt_four"><code>Platonic.sub_mul_lt_four</code></a>
       proves this is <b>&lt; 4</b> for any combinatorially regular convex 3-polytope, and with <code>s, m ≥ 3</code> only the five
       highlighted cells survive. Tap a cell.` }),
      h("div", { class: "scroll" }, h("table", { class: "t" }, h("tbody", {}, head, ...body))));
    const c = sel || SC.grid(3, 3)[0][0];
    const sol = SC.solveCounts(c.s, c.m), solid = SC.solidOf(c.s, c.m);
    const lines = [`<p><b>{${c.s},${c.m}}</b>: <code>(s−2)(m−2) = ${c.defect}</code>, so <code>2s + 2m − sm = 4 − ${c.defect} = ${c.coeff}</code>.</p>`];
    if (sol.ok) {
      lines.push(`<p><code>E · ${c.coeff} = 2·${c.s}·${c.m} = ${2 * c.s * c.m}</code> &nbsp;⟶&nbsp;
        <code>E = ${sol.E}</code>, then <code>F = 2E/s = ${sol.F}</code> and <code>V = 2E/m = ${sol.V}</code>.
        Check: <code>V − E + F = ${sol.V} − ${sol.E} + ${sol.F} = ${sol.euler}</code>.</p>`);
      lines.push(`<p>${c.pair
        ? `This is <b>${solid.name}</b> ${solid.geometric
          ? `— and the Lean builds it geometrically: <code>${solid.geometric}</code>.`
          : `— but the Lean <b>does not build it</b>. <code>Platonic.${solid.name}</code> is only the record <code>(V,E,F,s,m) = (${sol.V},${sol.E},${sol.F},${c.s},${c.m})</code>, five numbers satisfying Euler and the double counts.`}`
        : `<span class="muted">Positive integers come out, but this pair is excluded anyway, because <code>sub_mul_lt_four</code> rules it out before any solving happens.</span>`}</p>`);
    } else if (sol.why === "flat") {
      lines.push(`<p><code>2s + 2m − sm = 0</code>, so <code>E · 0 = ${2 * c.s * c.m}</code> — <b>impossible</b>. Geometrically: <code>{${c.s},${c.m}}</code> tiles the flat plane, not a sphere, and a tiling of the plane has infinitely many faces.</p>`);
    } else {
      lines.push(`<p><code>2s + 2m − sm = ${c.coeff} &lt; 0</code>, so the identity would force <code>E &lt; 0</code> — <b>impossible</b>, since <code>Platonic.pos_edges_of_euler</code> gives <code>0 &lt; E</code>. Geometrically: a hyperbolic tiling.</p>`);
    }
    box.append(h("div", { html: lines.join("") }));
    if (c.pair && solid) box.append(h("p", { class: "small" }, "", ...[
      h("a", { href: `#/node/Results.results_five_platonic_solids` }, "What results_five_platonic_solids actually proves →")]));
    box.append(h("p", { class: "small muted", html:
      `The two inputs the argument needs are regularity — every 2-face an <code>s</code>-gon, <code>m</code> edges at every vertex — and
       <code>V − E + F = 2</code>. The Euler input is <b>not</b> a free hypothesis in the Lean: <code>regular_polytope_counts</code> takes it
       from <a href="#/node/Results.results_euler_relation_dimension_three">the geometric Euler relation</a>. A third input,
       <i>every edge lies in exactly two 2-faces</i>, <b>is</b> still a hypothesis.` }),
      illustration("Illustration. This is the arithmetic of `Platonic.mul_euler_int` and `sub_mul_lt_four` for a finite window of `(s, m)`. The Lean proves the bound for all of them at once, and proves nothing at all about the existence of the solids."));
  }
  run();
}

// ---------------------------------------------------------------- pick
function pickWidget(el, cfg = {}) {
  const show = cfg.show || ["counts", "hypotheses", "fan"];
  const editable = cfg.editable !== false;
  let name = LT.POLYGON_PRESETS[cfg.preset] ? cfg.preset : "triangle";
  let verts = LT.POLYGON_PRESETS[name].verts.map((p) => p.slice());
  let custom = false;
  const lo = cfg.lo ?? -2, hi = cfg.hi ?? 6;
  const box = h("div");
  el.append(box);

  const S = 300;
  const span = hi - lo;
  const px = (x) => ((x - lo) / span) * (S - 36) + 18;
  const py = (y) => S - (((y - lo) / span) * (S - 36) + 18);

  function draw(P) {
    const sv = svg("svg", { viewBox: `0 0 ${S} ${S}`, class: "diagram-svg", style: `max-width:${S}px;touch-action:manipulation` });
    for (let x = lo; x <= hi; x++) sv.append(svg("line", { x1: px(x), y1: py(lo), x2: px(x), y2: py(hi), stroke: "#2f302a", "stroke-width": 1 }));
    for (let y = lo; y <= hi; y++) sv.append(svg("line", { x1: px(lo), y1: py(y), x2: px(hi), y2: py(y), stroke: "#2f302a", "stroke-width": 1 }));
    if (P.valid && show.includes("fan") && P.fan.length)
      for (const t of P.fan)
        sv.append(svg("polygon", { points: [t.a, t.b, t.c].map((p) => `${px(p[0])},${py(p[1])}`).join(" "),
          fill: t.det > 0 ? "rgba(102,217,239,.13)" : "rgba(249,38,114,.16)", stroke: "#3e3d32", "stroke-width": 1 }));
    if (P.valid)
      sv.append(svg("polygon", { points: P.vertices.map((p) => `${px(p[0])},${py(p[1])}`).join(" "),
        fill: show.includes("fan") ? "none" : "rgba(102,217,239,.12)", stroke: rgb(BLUE), "stroke-width": 2.2 }));
    const bset = new Set(P.boundaryLatticePoints.map((p) => `${p[0]},${p[1]}`));
    const iset = new Set(P.interiorLatticePoints.map((p) => `${p[0]},${p[1]}`));
    const vset = new Set(P.vertices.map((p) => `${p[0]},${p[1]}`));
    for (let x = lo; x <= hi; x++) for (let y = lo; y <= hi; y++) {
      const k = `${x},${y}`;
      const isV = vset.has(k), isB = bset.has(k), isI = iset.has(k);
      sv.append(svg("circle", { cx: px(x), cy: py(y), r: isV ? 5.5 : isB || isI ? 4.5 : 3, class: "pick",
        fill: isV ? rgb(PINK) : isB ? rgb(ORANGE) : isI ? rgb(GREEN) : "#4b4a40",
        stroke: isV ? "#1e1f1c" : "none", "stroke-width": 1,
        onclick: editable ? () => {
          const at = verts.findIndex((p) => p[0] === x && p[1] === y);
          if (at >= 0) verts.splice(at, 1); else verts.push([x, y]);
          custom = true; run();
        } : null }));
    }
    return sv;
  }

  function run() {
    const P = LT.polygon(verts);
    box.innerHTML = "";
    const controls = [field("polygon", select([...Object.keys(LT.POLYGON_PRESETS), ...(custom ? ["(yours)"] : [])],
      custom ? "(yours)" : name, (v) => {
        if (v === "(yours)") return;
        name = v; verts = LT.POLYGON_PRESETS[v].verts.map((p) => p.slice()); custom = false; run();
      }))];
    if (editable) controls.push(btn("clear", () => { verts = []; custom = true; run(); }));
    box.append(row(...controls), draw(P),
      h("p", { class: "small muted", html: editable
        ? "Tap a grid point to add it to the end of the cyclic vertex list, or tap a vertex to remove it. <span class='sw' style='background:" + rgb(PINK) + "'></span>listed vertex · <span class='sw' style='background:" + rgb(ORANGE) + "'></span>boundary lattice point (<code>B</code>) · <span class='sw' style='background:" + rgb(GREEN) + "'></span>interior lattice point (<code>I</code>)"
        : "<span class='sw' style='background:" + rgb(PINK) + "'></span>listed vertex · <span class='sw' style='background:" + rgb(ORANGE) + "'></span>boundary (<code>B</code>) · <span class='sw' style='background:" + rgb(GREEN) + "'></span>interior (<code>I</code>)" }));
    if (!P.valid) {
      box.append(h("p", { class: "err" }, `A LatticePolygon needs 3 ≤ vertices.length; this list has ${P.nVertices}.`),
        illustration("Illustration — not part of the Lean proof."));
      return;
    }
    const facts = [];
    if (show.includes("counts")) {
      facts.push(`<p><b>I = ${P.I}</b> &nbsp; <b>B = ${P.B}</b> &nbsp;⟶&nbsp; <code>I + B/2 − 1 = ${frac(P.pick)}</code>
        &nbsp;·&nbsp; shoelace <code>|${P.shoelaceSum}|/2 = ${frac(P.shoelace)}</code>
        ${P.shoelace === P.pick ? `<span style="color:var(--green)">— they agree</span>`
          : `<span style="color:var(--pink)">— they disagree</span>`}</p>`);
      facts.push(`<p class="small"><code>B</code> is the number of lattice points on the cyclic edges, counted through
        <code>edgeGcd</code>: edge <code>i</code> contributes <code>gcd(Δx, Δy) + 1</code> points, endpoints shared
        (${P.vertices.map((_, i) => `<code>${LT.edgeGcd(...P.edgePair(i))}</code>`).join(" + ")} = ${P.B}).
        <code>I</code> counts lattice points in the <b>convex hull of the vertex set</b> that are not on those edges —
        that is <code>LatticePolygon.interiorLatticePoints</code>, hull and all.</p>`);
    }
    if (show.includes("hypotheses")) {
      const hyp = LT.picksHypotheses(P);
      facts.push(`<p class="small"><code>Function.Injective P.vertex</code>: ${yes(P.injective)}
        · <code>ConvexCCW</code>: ${yes(P.convexCCW)}
        · <code>LocalCCWTurns</code>: ${yes(P.localCCWTurns)}
        ⟶ <code>StrictlyConvexCCW</code>: ${yes(P.strictlyConvexCCW)}
        · <code>PrimitiveEdges</code>: ${yes(P.primitiveEdges)}
        · <code>EmptyInterior</code>: ${yes(P.emptyInterior)}</p>`);
      facts.push(hyp.ok
        ? `<p class="small" style="color:var(--green)"><b><a href="#/node/Results.results_picks_theorem"><code>results_picks_theorem</code></a> applies</b> (given a <code>Finset S</code> equal to the interior points, which the Lean does not construct): the Lebesgue area of the convex hull is <code>${frac(P.pick)}</code>.</p>`
        : `<p class="small" style="color:var(--pink)"><b><code>results_picks_theorem</code> does not apply.</b></p><ul class="tight small">${hyp.failures.map((f) => `<li>${mdish(f)}</li>`).join("")}</ul>`);
      if (!P.convexCCW)
        facts.push(`<p class="small note-added">Because <code>interiorLatticePoints</code> is taken relative to the <i>convex hull</i>, the
          <code>I</code> above counts points outside the shape you can see whenever the polygon is not convex. For a non-convex polygon,
          <code>I + B/2 − 1</code> is not the classical Pick count of the region either, and the Lean says nothing about it.</p>`);
      if (P.primitiveEdges && P.emptyInterior && P.strictlyConvexCCW && P.injective)
        facts.push(`<p class="small" style="color:var(--green)">Primitive edges and no interior point:
          <a href="#/node/Results.results_picks_of_empty_primitive_fan"><code>results_picks_of_empty_primitive_fan</code></a> applies too, giving
          <code>B/2 − 1 = ${frac(P.B / 2 - 1)}</code>.</p>`);
    }
    if (show.includes("fan")) {
      facts.push(`<p class="small">Corner fan (<code>LatticeFan.fanTriangle</code>, triangles <code>(v₀, vᵢ₊₁, vᵢ₊₂)</code>):
        ${P.fan.length} of them, dets ${P.fan.map((t) => `<code>${t.det}</code>`).join(" ")}
        ${P.fanDetsPos ? `<span style="color:var(--green)">(all &gt; 0: <code>FanDetsPos</code>)</span>` : `<span style="color:var(--pink)">(not all &gt; 0)</span>`},
        shoelaces summing to <code>${frac(P.fan.reduce((s, t) => s + t.shoelace, 0))}</code>
        ${P.fanDetPrimitive ? `· every det is <code>±1</code>, so every triangle has area exactly <code>1/2</code> (<code>Triangle.shoelace_eq_half_of_isDetPrimitive</code>)` : ""}.</p>`);
    }
    box.append(h("div", { html: facts.join("") }));
    if (!custom) box.append(h("p", { class: "small muted", html: mdish(LT.presetNote(name)) }));
    box.append(illustration("Illustration. Every test here is exact integer arithmetic on the definitions — `edgeGcd`, `latticeDet`, `ConvexCCW` — but finding `I` by scanning a bounding box is this page's arithmetic. The Lean does not prove the interior lattice points are finite; `results_picks_theorem` takes a `Finset S` equal to them as a hypothesis."));
  }
  run();
}

// ---------------------------------------------------------------- triangulate
function triangulateWidget(el, cfg = {}) {
  let I = cfg.I ?? 1, B = cfg.B ?? 6;
  const show = cfg.show || ["counts", "moves"];
  const box = h("div");
  el.append(box);

  const MOVES = (B0, I0) => {
    const n = 3;
    const steps = [
      { text: `the corner 3-cycle: a triangle and the outside`, V: n, E: n, T: 1, F: 2,
        why: "`corner_cycle_euler_from_characteristic`: the fan on three vertices *is* a geometric 2-simplex, and its disk Euler number is the Euler–Poincaré characteristic of that simplex plus one exterior face (`triangle_disk_euler`)." },
      { text: `insert ${Math.max(0, B0 - n)} boundary vertices`, V: B0, E: B0, T: 1, F: 2,
        why: "`eulerChar_insert_boundary`: one vertex and one edge each time, so `V − E + F` cannot move." },
      { text: `add ${Math.max(0, B0 - 3)} diagonals`, V: B0, E: 2 * B0 - 3, T: B0 - 2, F: B0 - 1,
        why: "`eulerChar_add_diagonal`: one edge and one face each time." },
      { text: `${I0} stellar subdivision${I0 === 1 ? "" : "s"} at the interior points`, V: I0 + B0, E: 3 * I0 + 2 * B0 - 3, T: 2 * I0 + B0 - 2, F: 2 * I0 + B0 - 1,
        why: "`eulerChar_stellar`: one vertex, three edges, two extra triangles." },
    ];
    return steps.map((s) => ({ ...s, euler: s.V - s.E + s.F }));
  };

  function run() {
    box.innerHTML = "";
    box.append(row(field("I", num(I, 0, 40, (v) => { I = Math.max(0, v); run(); })),
      field("B", num(B, 3, 40, (v) => { B = Math.max(3, v); run(); })),
      h("span", { class: "small muted" }, "interior and boundary lattice points")));
    const c = LT.triangulationCounts(I, B);
    if (show.includes("counts")) {
      box.append(h("div", { class: "sect" }), h("h4", {}, "The counts of a primitive triangulation"),
        h("div", { class: "scroll" }, h("table", { class: "t left" }, h("tbody", {},
          ...[["V = I + B", c.V, "`hV` of `results_pick_count_of_euler`"],
            ["T = 2I + B − 2", c.T, "the number of triangles"],
            ["E = 3I + 2B − 3", c.E, "Funkenbusch's edge count"],
            ["F = T + 1", c.F, "`hF`: the triangles plus the one outer face"],
            ["2E = 3T + B", `${2 * c.E} = ${3 * c.T + c.B}`, "`hshake`, handshaking: each triangle has 3 edges, interior edges counted twice, boundary edges once"],
            ["V − E + F", c.euler, "`heuler`: must be 2"],
            ["A = T/2", frac(c.area), "`harea`: every primitive triangle has area 1/2"],
            ["I + B/2 − 1", frac(c.pick), "the conclusion"]].map(([a, b, note]) =>
            h("tr", {}, h("th", { html: mdish(String(a)) }), h("td", { html: `<b>${b}</b>` }), h("td", { class: "small muted", html: mdish(String(note)) })))))),
        h("p", { class: "small", html:
          `Handshaking: ${c.handshake ? `<span style="color:var(--green)">holds</span>` : `<span style="color:var(--pink)">fails</span>`}
           · Euler number: <b>${c.euler}</b> ${c.euler === 2 ? `<span style="color:var(--green)">= 2</span>` : `<span style="color:var(--pink)">≠ 2</span>`}
           · <code>T/2 = ${frac(c.area)}</code> and <code>I + B/2 − 1 = ${frac(c.pick)}</code>
           ${c.area === c.pick ? `<span style="color:var(--green)">— equal, which is all <code>results_pick_count_of_euler</code> says</span>` : ""}` }),
        h("p", { class: "small note-added", html:
          `This table is <b>arithmetic in <code>I</code> and <code>B</code></b>. <a href="#/node/Results.results_pick_count_of_euler"><code>results_pick_count_of_euler</code></a>
           takes <code>V = I + B</code>, <code>F = T + 1</code>, <code>V − E + F = 2</code>, <code>2E = 3T + B</code> and <code>A = T/2</code>
           as <i>hypotheses</i> and concludes <code>A = I + B/2 − 1</code>. It proves nothing about any polygon by itself: a caller has to supply
           a triangulation whose counts really are these, and that is the hard part.` }));
    }
    if (show.includes("moves")) {
      const steps = MOVES(B, I);
      box.append(h("div", { class: "sect" }), h("h4", {}, "Why the Euler number is 2, as DiskEuler.lean does it"));
      const detail = h("div");
      const render = (k) => {
        const s = steps[k];
        detail.innerHTML = `
          <div class="flow">${steps.map((x, j) => `${j ? '<div class="arrow">↓</div>' : ""}<div class="step${j === k ? " on" : " off"}">${mdish(x.text)}
            <div class="small muted">V = ${x.V}, E = ${x.E}, T = ${x.T}, F = ${x.F} &nbsp;⟶&nbsp; V − E + F = <b style="color:${x.euler === 2 ? "var(--green)" : "var(--pink)"}">${x.euler}</b></div></div>`).join("")}</div>
          <p class="small">${mdish(s.why)}</p>`;
      };
      const st = stepper(steps.length - 1, render, 0);
      box.append(st.bar, detail);
      render(0);
      box.append(h("p", { class: "small muted", html:
        `This is the route of <a href="#/node/Picks.triangulated_disk_euler_from_characteristic"><code>triangulated_disk_euler_from_characteristic</code></a>.
         Read the Lean statement carefully though: it is an identity between numerals built from <code>n</code>, <code>B</code> and <code>I</code>
         (<code>(I+B) − (3I+2B−3) + (2I+B−2+1) = 2</code>), not a theorem about a triangulation of your polygon. What the <i>proof</i> shows is
         that the moves above each preserve the number, starting from a real geometric triangle.` }));
    }
    box.append(illustration("Illustration. The table is the bookkeeping; `results_pick_count_of_euler` is that bookkeeping and nothing more. The geometric work — that a strictly convex lattice polygon really has a primitive triangulation with these counts, and that the shoelace number is the Lebesgue area — is in `PickFromEuler.lean` and `LatticeArea.lean`."));
  }
  run();
}

export const INTERACTIVE = {
  polyhedron: polyhedronWidget,
  "face-lattice": faceLatticeWidget,
  schlafli: schlafliWidget,
  pick: pickWidget,
  triangulate: triangulateWidget,
};
