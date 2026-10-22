import { highlight, linkMap } from "./lean.js";
import { mountWidget } from "./widgets.js";

const REPO = "tangentproofs/eulers-gem";
const BLOB = `https://github.com/${REPO}/blob/main`;
const GISCUS = { repo: REPO, repoId: "R_kgDOUoT00w", category: "Announcements", categoryId: "DIC_kwDOUoT0084DJW1F" };
const MATHLIB_DOCS = (n) => `https://leanprover-community.github.io/mathlib4_docs/find/?pattern=${encodeURIComponent(n)}#doc`;
// The roots of the graph are the paper-facing theorems of lean/Results.lean.
let ROOTS = [];
const MAIN = "Results.results_euler_polyhedron";
// The browsable, syntax-highlighted Lean (scripts/build-source-pages.py) lives at ../docs/.
const DOCS = (d) => `../${d.docs}`;
const app = document.getElementById("app");
const esc = (s) => String(s).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");

const [decls, nodes] = await Promise.all([
  fetch("data/decls.json").then((r) => r.json()),
  fetch("data/nodes.json").then((r) => r.json()),
]);
const byId = new Map(decls.map((d) => [d.id, d]));
ROOTS = decls.filter((d) => d.module === "Results" && d.kind === "theorem").map((d) => d.id);
const reachable = decls.filter((d) => d.depth !== null);
const fileCount = new Set(decls.map((d) => d.file)).size;

// ------------------------------------------------------------------ progress
// localStorage schema v1: { v: 1, nodes: { [id]: { viewed?, quizPassed?, signedOff?, answers? } } }
const KEY = "eulers-gem-progress-v1";
let P = (() => { try { return JSON.parse(localStorage.getItem(KEY)) || { v: 1, nodes: {} }; } catch { return { v: 1, nodes: {} }; } })();
const save = () => localStorage.setItem(KEY, JSON.stringify(P));
const rec = (id) => (P.nodes[id] ??= {});

// signed: sign-off recorded AND the node's quiz passed (stubs have no quiz, so cannot be signed).
const signed = (id) => !!(nodes[id] && P.nodes[id]?.signedOff && P.nodes[id]?.quizPassed);
// understood: signed AND every meaning-dependency understood (Mathlib is taken as given).
const memo = new Map();
function understood(id, stack = new Set()) {
  if (memo.has(id)) return memo.get(id);
  if (stack.has(id)) return false;
  stack.add(id);
  const r = signed(id) && byId.get(id).meaningDeps.every((d) => understood(d, stack));
  stack.delete(id);
  memo.set(id, r);
  return r;
}
function status(id) {
  if (understood(id)) return "understood";
  if (signed(id)) return "signed";
  if (P.nodes[id]?.quizPassed) return "quiz";
  if (nodes[id]) return "explained";
  return "stub";
}
const STATUS_LABEL = { understood: "understood", signed: "signed off (deps pending)", quiz: "quiz passed", explained: "has explainer", stub: "needs explainer" };
const COLORS = { understood: "#a6e22e", signed: "#c3e88d", quiz: "#e6db74", explained: "#66d9ef", stub: "#75715e" };
function refresh() { memo.clear(); }

// The proof is understood when the theorem is, and every declaration its proof uses is too.
function proofCoverage() {
  const n = reachable.filter((d) => understood(d.id)).length;
  return { n, total: reachable.length };
}

// Reading order shown on the graph page (ids that do not exist are skipped).
const START_HERE = [
  ["IsPolytope", "what a polytope is here"],
  ["IsFaceOf", "what counts as a face"],
  ["affDim", "how faces get a dimension"],
  ["faceEulerSum", "the alternating sum"],
  ["Results.results_euler_characteristic", "the root theorem: the sum is 1"],
  ["Results.results_euler_polyhedron", "V − E + F = 2 in ℝ³"],
  ["Results.results_five_platonic_solids", "a consequence: the five Schläfli pairs"],
  ["Results.results_picks_theorem", "a consequence: Pick's formula"],
];

// ------------------------------------------------------------------ router
const routes = [
  [/^#?\/?$/, graphPage],
  [/^#\/node\/(.+)$/, (id) => nodePage(decodeURIComponent(id))],
  [/^#\/nodes(?:\?.*)?$/, () => listPage()],
  [/^#\/playground$/, playgroundPage],
  [/^#\/about$/, aboutPage],
  [/^#\/trust$/, trustPage],
];
function route() {
  refresh();
  const hsh = location.hash || "#/";
  app.className = "";
  document.querySelectorAll("header nav a").forEach((a) => a.classList.toggle("on", a.getAttribute("href") === hsh));
  for (const [re, f] of routes) { const m = hsh.match(re); if (m) { f(...m.slice(1)); window.scrollTo(0, 0); return; } }
  app.innerHTML = `<p>Not found. <a href="#/">Home</a></p>`;
}
addEventListener("hashchange", route);

// ------------------------------------------------------------------ graph page
let graphView = "spine";
function graphPage() {
  app.className = "wide";
  const cov = proofCoverage();
  const spine = Object.keys(nodes);
  const spineDone = spine.filter((id) => understood(id)).length;
  app.innerHTML = `
    <div class="graph-wrap">
      <div>
        <h1>Euler's Gem, in Lean, read back into English</h1>
        <p class="muted">The <a href="../index.html">Euler's Gem formalization</a> proves Euler's polyhedron formula and some of its
        consequences in Lean 4 (<a href="../docs/Results.html">browse the code</a>). Lean checks the proofs. This part of the site
        goes the other way: <b>you</b> are the checker. A node turns green when you've passed its quiz and signed off on its formal
        statement <i>and</i> on everything that statement mentions, just as Lean won't accept a statement whose ingredients it doesn't
        know. Orange rings mark the paper-facing theorems of <code>Results.lean</code>; <a href="#/trust">Trust</a> says exactly what each one proves.</p>
        <div class="toolbar">
          <button data-v="spine">Explained spine (${spine.length})</button>
          <button data-v="neighborhood">Spine + direct deps</button>
          <button data-v="files">Files (${fileCount})</button>
          <button data-v="all">All declarations (${decls.length})</button>
          <input id="find" type="text" placeholder="find a declaration…" style="max-width:16rem">
        </div>
        <div id="cy"></div>
        <p class="small muted">Click a node to open it. Solid edge = used in the statement/definition (needed to <i>understand</i> it); dashed = used only in the proof. Arrows point from a declaration to what it uses.</p>
      </div>
      <aside id="side">
        <div class="panel">
          <h3>Your progress</h3>
          <div>Spine: <b>${spineDone}</b> / ${spine.length} understood</div>
          <div class="progress-bar"><div style="width:${spine.length ? (100 * spineDone) / spine.length : 0}%"></div></div>
          <div>Everything the Results theorems use: <b>${cov.n}</b> / ${cov.total} declarations understood</div>
          <div class="progress-bar"><div style="width:${(100 * cov.n) / cov.total}%"></div></div>
          <p class="small muted">${understood(MAIN) ? "You understand the <b>statement</b> of Euler's polyhedron formula as Lean states it." : `To understand the statement of <a href="#/node/${MAIN}">Euler's formula in ℝ³</a>, sign off on it and on everything it mentions.`}</p>
        </div>
        <div class="panel legend">
          <h3>Legend</h3>
          ${Object.entries(STATUS_LABEL).map(([k, v]) => `<div><span class="sw" style="background:${COLORS[k]}"></span>${v}</div>`).join("")}
          <div><span class="sw" style="background:transparent;border:2px solid #f92672"></span>V − E + F = 2 in ℝ³</div>
          <div><span class="sw" style="background:transparent;border:2px solid #fd971f"></span>a Results theorem</div>
        </div>
        <div class="panel small">
          <h3>Start here</h3>
          <div id="starthere"></div>
          <p><a href="#/playground">Play with polyhedra and lattice polygons →</a> · <a href="#/trust">What each result really proves →</a></p>
        </div>
        <div class="panel small">
          <h3>Progress file</h3>
          <button id="export">Export</button> <button id="import">Import</button> <button id="reset">Reset</button>
          <p class="muted">Stored only in this browser (localStorage).</p>
        </div>
      </aside>
    </div>`;
  app.querySelectorAll("[data-v]").forEach((b) => {
    b.classList.toggle("on", b.dataset.v === graphView);
    b.onclick = () => { graphView = b.dataset.v; graphPage(); };
  });
  wireProgressButtons();
  document.getElementById("starthere").innerHTML = START_HERE.filter(([id]) => byId.has(id))
    .map(([id, what]) => `<div>· <a href="#/node/${encodeURIComponent(id)}">${esc(nodes[id]?.title || id)}</a> <span class="muted">— ${what}</span></div>`).join("");
  drawGraph(graphView);
}

function wireProgressButtons() {
  document.getElementById("export").onclick = () => {
    const a = document.createElement("a");
    a.href = URL.createObjectURL(new Blob([JSON.stringify(P, null, 1)], { type: "application/json" }));
    a.download = "eulers-gem-progress.json"; a.click();
  };
  document.getElementById("import").onclick = () => {
    const i = document.createElement("input"); i.type = "file"; i.accept = ".json";
    i.onchange = async () => { try { P = JSON.parse(await i.files[0].text()); save(); route(); } catch (e) { alert("Could not read: " + e.message); } };
    i.click();
  };
  document.getElementById("reset").onclick = () => { if (confirm("Forget all sign-offs and quiz results in this browser?")) { P = { v: 1, nodes: {} }; save(); route(); } };
}

function drawGraph(view) {
  if (!window.cytoscape) { document.getElementById("cy").innerHTML = "<p class='err'>Graph library failed to load.</p>"; return; }
  if (window.cytoscapeDagre && !drawGraph.reg) { cytoscape.use(window.cytoscapeDagre); drawGraph.reg = true; }
  const els = [];
  let ids;
  if (view === "files") {
    const mods = [...new Set(decls.map((d) => d.module))];
    const modOf = new Map(decls.map((d) => [d.id, d.module]));
    const cnt = new Map(), expl = new Map(), und = new Map();
    for (const d of decls) {
      cnt.set(d.module, (cnt.get(d.module) || 0) + 1);
      if (nodes[d.id]) expl.set(d.module, (expl.get(d.module) || 0) + 1);
      if (understood(d.id)) und.set(d.module, (und.get(d.module) || 0) + 1);
    }
    for (const m of mods) {
      const u = und.get(m) || 0, c = cnt.get(m);
      const st = u === c ? "understood" : u ? "signed" : expl.get(m) ? "explained" : "stub";
      els.push({ data: { id: "m:" + m, label: `${m}\n${u}/${c}`, color: COLORS[st], size: 20 + Math.sqrt(c) * 6, file: m } });
    }
    const seen = new Set();
    for (const d of decls) for (const [deps, kind] of [[d.meaningDeps, "m"], [d.proofDeps, "p"]]) for (const x of deps) {
      const a = d.module, b = modOf.get(x);
      if (a !== b && !seen.has(a + ">" + b)) { seen.add(a + ">" + b); els.push({ data: { id: `e:${a}>${b}`, source: "m:" + a, target: "m:" + b, kind: "p" } }); }
    }
  } else {
    if (view === "spine") ids = new Set(Object.keys(nodes));
    else if (view === "neighborhood") {
      ids = new Set(Object.keys(nodes));
      for (const id of Object.keys(nodes)) for (const x of [...byId.get(id).meaningDeps, ...byId.get(id).proofDeps]) ids.add(x);
    } else ids = new Set(decls.map((d) => d.id));
    for (const id of ids) {
      const d = byId.get(id), st = status(id);
      els.push({ data: { id, label: id.split(".").pop(), color: COLORS[st], size: nodes[id] ? 26 : 12, main: id === MAIN ? 1 : 0, root: ROOTS.includes(id) ? 1 : 0, explained: nodes[id] ? 1 : 0 } });
    }
    for (const id of ids) {
      const d = byId.get(id);
      for (const x of d.meaningDeps) if (ids.has(x)) els.push({ data: { id: `${id}>${x}`, source: id, target: x, kind: "m" } });
      for (const x of d.proofDeps) if (ids.has(x)) els.push({ data: { id: `${id}>>${x}`, source: id, target: x, kind: "p" } });
    }
  }
  const big = els.length > 1500;
  const cy = cytoscape({
    container: document.getElementById("cy"),
    elements: els,
    wheelSensitivity: 0.3,
    style: [
      { selector: "node", style: { "background-color": "data(color)", width: "data(size)", height: "data(size)", label: "data(label)", color: "#f8f8f2", "font-size": view === "all" ? 6 : 10, "text-wrap": "wrap", "text-valign": "bottom", "text-margin-y": 3, "text-outline-color": "#1e1f1c", "text-outline-width": 2 } },
      { selector: "node[explained = 0]", style: { "font-size": view === "all" ? 0 : 7, color: "#a59f85" } },
      { selector: "node[root = 1]", style: { "border-width": 2, "border-color": "#fd971f" } },
      { selector: "node[main = 1]", style: { "border-width": 3, "border-color": "#f92672", "font-weight": "bold" } },
      { selector: "edge", style: { width: 1.2, "line-color": "#5c5b4f", "target-arrow-color": "#5c5b4f", "target-arrow-shape": "triangle", "arrow-scale": 0.7, "curve-style": big ? "haystack" : "bezier", opacity: 0.8 } },
      { selector: "edge[kind = 'p']", style: { "line-style": "dashed", opacity: 0.45 } },
      { selector: ".hl", style: { "border-width": 4, "border-color": "#fd971f" } },
      { selector: ".faded", style: { opacity: 0.12 } },
    ],
    layout: view === "all" ? { name: "cose", animate: false, nodeRepulsion: 4000, idealEdgeLength: 30, numIter: 600 }
      : { name: window.cytoscapeDagre ? "dagre" : "breadthfirst", rankDir: "TB", nodeSep: 50, rankSep: 60, animate: false },
  });
  cy.on("tap", "node", (e) => {
    const id = e.target.id();
    if (id.startsWith("m:")) { location.hash = "#/nodes?file=" + id.slice(2); return; }
    location.hash = "#/node/" + encodeURIComponent(id);
  });
  cy.on("mouseover", "node", (e) => { const n = e.target; cy.elements().addClass("faded"); n.closedNeighborhood().removeClass("faded"); });
  cy.on("mouseout", "node", () => cy.elements().removeClass("faded"));
  const find = document.getElementById("find");
  find.oninput = () => {
    cy.nodes().removeClass("hl");
    const q = find.value.trim().toLowerCase();
    if (!q) return;
    const hits = cy.nodes().filter((n) => n.id().toLowerCase().includes(q));
    hits.addClass("hl");
    if (hits.length && hits.length < 30) cy.fit(hits, 60);
  };
  find.onkeydown = (e) => {
    if (e.key !== "Enter") return;
    const q = find.value.trim().toLowerCase();
    const d = decls.find((d) => d.id.toLowerCase() === q) || decls.find((d) => d.id.toLowerCase().includes(q));
    if (d) location.hash = "#/node/" + encodeURIComponent(d.id);
  };
}

// ------------------------------------------------------------------ node page
function depLinks(list) {
  if (!list.length) return `<span class="muted small">none in this project</span>`;
  return list.map((id) => `<a class="st-${status(id)}" href="#/node/${encodeURIComponent(id)}" title="${STATUS_LABEL[status(id)]}">${esc(id)}</a>`).join("");
}
function agentPrompt(d) {
  return `You are writing an informal explainer for one declaration of the Euler's Gem Lean 4 formalization
(${REPO}, Apache-2.0). The Lean in lean/ is the ground truth.

Target: ${d.name}  (${d.kind})
Source: ${BLOB}/${d.file}#L${d.line}-L${d.endLine}
Browsable: https://tangentproofs.github.io/eulers-gem/${d.docs}
Section variables in scope: ${d.variables.join(" ") || "(none)"}
Formal statement:
${d.statement}

It mentions these project declarations (explain them by name, link to them): ${d.meaningDeps.join(", ") || "none"}
Its proof uses: ${d.proofDeps.join(", ") || "n/a"}

Write learn/nodes/${d.id}.md following CONTRIBUTING.md and learn/schema/node.schema.json:
YAML frontmatter (id, title, summary, review: draft, authors, caveats, quiz of 3-6 questions with answers and
explanations, optional widgets) and a Markdown body with a '## Plain English' section.
Be faithful to the Lean statement as written: every hypothesis, the quantifier order, ℕ vs ℤ vs ℚ, what is
assumed versus proved. Only name a classical theorem (Euler, Pick, Platonic solids, ...) if the Lean statement
really is that claim; otherwise say exactly what it proves and which hypotheses remain. List anything you are
unsure of under caveats. Run 'cd learn && npm ci && npm test' before opening a PR.`;
}
function nodePage(id) {
  const d = byId.get(id);
  if (!d) { app.innerHTML = `<p>No declaration <code>${esc(id)}</code>. <a href="#/nodes">All nodes</a></p>`; return; }
  const n = nodes[id];
  const r = rec(id);
  if (!r.viewed) { r.viewed = Date.now(); save(); }
  const st = status(id);
  const links = linkMap([...d.meaningDeps, ...d.proofDeps, id]);
  const src = `${BLOB}/${d.file}#L${d.line}-L${d.endLine}`;
  const editUrl = n ? `https://github.com/${REPO}/edit/main/learn/nodes/${encodeURIComponent(id)}.md`
    : `https://github.com/${REPO}/new/main/learn/nodes?filename=${encodeURIComponent(id)}.md`;
  const pendingDeps = d.meaningDeps.filter((x) => !understood(x));
  app.innerHTML = `
    <div class="node-head">
      <p class="small"><a href="#/">← graph</a></p>
      <h1>${n ? esc(n.title) : esc(id)}</h1>
      <div><span class="pill kind-${d.kind}">${d.kind}</span><span class="pill st-${st}">${STATUS_LABEL[st]}</span>${n ? `<span class="pill ${n.review === "draft" ? "draft" : ""}">${n.review}</span>` : ""}
      <span class="name">${esc(d.name)}</span></div>
      ${n ? `<p class="eli5" style="margin:.6rem 0">${n.summaryHtml}</p>` : ""}
    </div>
    <h2>Formal statement</h2>
    <pre class="lean">${highlight(d.statement, links)}${d.truncated ? `<span class="cm"> := … (proof omitted — <a href="${DOCS(d)}">see it in the source</a>)</span>` : ""}</pre>
    <p class="small muted"><a class="srclink" href="${DOCS(d)}"><b>Read it in the browsable source →</b></a> · <a href="${src}" target="_blank" rel="noopener">${esc(d.file)} lines ${d.line}–${d.endLine} on GitHub</a>
    ${d.variables.length ? ` · section variables in scope: <code>${esc(d.variables.join("  "))}</code>` : ""}</p>
    <div class="small">
      <div><b>Mentions</b> (understand these first): <div class="deps">${depLinks(d.meaningDeps)}</div></div>
      ${d.kind === "theorem" ? `<div><b>Proof uses</b>: <div class="deps">${depLinks(d.proofDeps)}</div></div>` : ""}
      <div><b>Used by</b>: <div class="deps">${depLinks(d.usedBy.slice(0, 40))}${d.usedBy.length > 40 ? `<span>+${d.usedBy.length - 40} more</span>` : ""}</div></div>
      ${d.mathlib.length ? `<div><b>From Mathlib</b> (taken as given): <div class="deps">${d.mathlib.map((m) => `<a href="${MATHLIB_DOCS(m)}" target="_blank" rel="noopener">${esc(m)}</a>`).join("")}</div></div>` : ""}
    </div>
    <div id="content"></div>`;
  const c = document.getElementById("content");
  if (!n) {
    c.innerHTML = `
      <div class="panel stub"><h3>Needs explainer</h3>
      <p>Nobody has written a plain-English explanation and quiz for this declaration yet, so it can't be signed off.
      <a href="${editUrl}" target="_blank" rel="noopener">Write one on GitHub</a> (see <a href="https://github.com/${REPO}/blob/main/CONTRIBUTING.md">CONTRIBUTING.md</a>).</p>
      <details><summary>Prompt for an AI agent</summary><textarea class="prompt" readonly>${esc(agentPrompt(d))}</textarea></details></div>`;
  } else {
    c.innerHTML = `
      <div class="eli5">${n.bodyHtml}</div>
      <div id="widgets"></div>
      ${n.caveatsHtml.length ? `<div class="panel caveats"><h3>Faithfulness notes</h3><ul>${n.caveatsHtml.map((x) => `<li>${x}</li>`).join("")}</ul></div>` : ""}
      <h2>Check your understanding</h2>
      <div class="panel quiz" id="quiz"></div>
      <div class="panel signoff" id="signoff"></div>
      <p class="small muted">Spotted an error or have a better explanation? <a href="${editUrl}" target="_blank" rel="noopener">Edit this node on GitHub</a>
      · <details style="display:inline"><summary>agent prompt</summary><textarea class="prompt" readonly>${esc(agentPrompt(d))}</textarea></details></p>`;
    const w = document.getElementById("widgets");
    for (const spec of n.widgets || []) mountWidget(w, spec);
    renderQuiz(id, n);
  }
  c.insertAdjacentHTML("beforeend", `<h2>Discussion</h2><div class="giscus-wrap" id="giscus"></div>`);
  mountGiscus(id);
  // pendingDeps is shown in the sign-off panel
  nodePage.pending = pendingDeps;
}

const norm = (s) => String(s).toLowerCase().replace(/\s+/g, "").replace(/[`'"]/g, "");
function renderQuiz(id, n) {
  const qz = document.getElementById("quiz");
  const r = rec(id);
  const answers = r.answers || {};
  qz.innerHTML = n.quiz.map((q, i) => {
    let input;
    if (q.type === "choice") input = q.choicesHtml.map((c, j) => `<label class="choice"><input type="radio" name="q${i}" value="${j}" ${answers[i] === j ? "checked" : ""}> ${c}</label>`).join("");
    else input = `<input type="text" name="q${i}" value="${answers[i] != null ? esc(answers[i]) : ""}" placeholder="${q.type === "number" ? "a number" : "your answer"}">`;
    return `<div class="q" data-i="${i}"><div><b>Q${i + 1}.</b> ${q.qHtml}</div>${input}<div class="verdict"></div><div class="explain">${q.explainHtml}</div></div>`;
  }).join("") + `<button class="primary" id="check">Check answers</button> <span id="qres"></span>`;
  const check = () => {
    let right = 0;
    const ans = {};
    n.quiz.forEach((q, i) => {
      const box = qz.querySelector(`.q[data-i="${i}"]`);
      let ok = false, given;
      if (q.type === "choice") { const s = box.querySelector("input:checked"); given = s ? +s.value : null; ok = given === q.answer; }
      else {
        given = box.querySelector("input").value;
        ok = q.type === "number" ? given.trim() !== "" && Number(given) === q.answer : q.answer.some((a) => norm(a) === norm(given));
      }
      ans[i] = given;
      if (given === null || given === "") { box.classList.remove("answered"); box.querySelector(".verdict").innerHTML = ""; return; }
      box.classList.add("answered");
      box.querySelector(".verdict").innerHTML = ok ? `<span class="ok">✓ correct</span>` : `<span class="bad">✗ not quite — read the explanation and try again</span>`;
      if (ok) right++;
    });
    r.answers = ans;
    const passed = right === n.quiz.length;
    if (passed && !r.quizPassed) r.quizPassed = Date.now();
    save();
    document.getElementById("qres").innerHTML = passed ? `<b class="ok" style="color:var(--green)">All ${right} correct. Quiz passed.</b>` : `${right} / ${n.quiz.length} correct`;
    renderSignoff(id);
  };
  document.getElementById("check").onclick = check;
  if (r.answers) check(); else renderSignoff(id);
}
function renderSignoff(id) {
  refresh();
  const box = document.getElementById("signoff");
  const r = rec(id), d = byId.get(id);
  const pending = d.meaningDeps.filter((x) => !understood(x));
  const can = !!r.quizPassed;
  box.classList.toggle("locked", !can);
  box.innerHTML = `
    <label><input type="checkbox" id="so" ${r.signedOff ? "checked" : ""} ${can ? "" : "disabled"}>
    <b>I understand the formal statement</b> — I could explain what the Lean above says, including its hypotheses, to someone else.</label>
    <p class="small muted">${can ? "" : "Pass the quiz above to unlock the sign-off. "}
    ${understood(id) ? `<span class="status-line" style="color:var(--green)">✓ Understood: you've signed off on this and on everything it mentions.</span>`
      : r.signedOff && can ? `Signed off. It becomes <b>understood</b> once these are understood too: ${pending.map((x) => `<a href="#/node/${encodeURIComponent(x)}">${esc(x)}</a>`).join(", ")}.`
      : pending.length ? `Mentions still to understand: ${pending.map((x) => `<a href="#/node/${encodeURIComponent(x)}">${esc(x)}</a>`).join(", ")}.` : ""}</p>`;
  const so = document.getElementById("so");
  if (so) so.onchange = () => { if (so.checked) r.signedOff = Date.now(); else delete r.signedOff; save(); renderSignoff(id); updateHeaderPill(id); };
  updateHeaderPill(id);
}
function updateHeaderPill(id) {
  refresh();
  const p = document.querySelector(".node-head .pill[class*='st-']");
  if (p) { const st = status(id); p.className = `pill st-${st}`; p.textContent = STATUS_LABEL[st]; }
}

function mountGiscus(id) {
  const el = document.getElementById("giscus");
  if (location.protocol === "file:") { el.innerHTML = `<p class="muted small">Comments load on the published site.</p>`; return; }
  const s = document.createElement("script");
  s.src = "https://giscus.app/client.js";
  Object.entries({
    "data-repo": GISCUS.repo, "data-repo-id": GISCUS.repoId, "data-category": GISCUS.category, "data-category-id": GISCUS.categoryId,
    "data-mapping": "specific", "data-term": `node: ${id}`, "data-strict": "1", "data-reactions-enabled": "1",
    "data-emit-metadata": "0", "data-input-position": "top", "data-theme": "dark", "data-lang": "en", "data-loading": "lazy",
  }).forEach(([k, v]) => s.setAttribute(k, v));
  s.crossOrigin = "anonymous"; s.async = true;
  el.append(s);
}

// ------------------------------------------------------------------ list page
function listPage(fileFilter) {
  const q = new URLSearchParams(location.hash.split("?")[1] || "");
  const file = fileFilter || q.get("file");
  const rows = decls.filter((d) => !file || d.module === file)
    .sort((a, b) => (!!nodes[b.id] - !!nodes[a.id]) || ((a.depth ?? 99) - (b.depth ?? 99)) || a.id.localeCompare(b.id));
  app.innerHTML = `<h1>${file ? `Declarations in ${esc(file)}.lean` : "All declarations"}</h1>
    <p class="muted">${Object.keys(nodes).length} with explainers, ${decls.length - Object.keys(nodes).length} awaiting one. ${file ? `<a href="#/nodes">show all</a>` : ""}
    Agents: the work list is <a href="data/needs-explainer.json">data/needs-explainer.json</a>.</p>
    <input type="text" id="flt" placeholder="filter…" style="max-width:20rem">
    <div class="table-wrap"><table class="node-list"><thead><tr><th>declaration</th><th>kind</th><th>status</th><th>distance from the theorem</th><th>file</th></tr></thead>
    <tbody>${rows.map((d) => `<tr data-id="${esc(d.id.toLowerCase())}"><td><a href="#/node/${encodeURIComponent(d.id)}">${esc(d.id)}</a></td><td><span class="pill kind-${d.kind}">${d.kind}</span></td><td><span class="pill st-${status(d.id)}">${STATUS_LABEL[status(d.id)]}</span></td><td>${d.depth ?? "—"}</td><td class="small muted">${d.module}</td></tr>`).join("")}</tbody></table></div>`;
  document.getElementById("flt").oninput = (e) => {
    const v = e.target.value.toLowerCase();
    app.querySelectorAll("tbody tr").forEach((tr) => (tr.style.display = tr.dataset.id.includes(v) ? "" : "none"));
  };
}

// ------------------------------------------------------------------ playground
function playgroundPage() {
  app.innerHTML = `<h1>Playground</h1>
    <p class="muted">Five things to push on: a map you colour by hand, the hypermaps the proof actually works with,
    Kempe's colour interchange, the trace numbers the certificates are built from, and a reducibility check.
    Everything here is an illustration — the Lean is the ground truth, and these are small decidable models of it.</p>
    <h2>Colour a map</h2>
    <p class="muted">A <a href="#/node/SimpleMap">SimpleMap</a> of the plane has open connected regions, and two of them are
    <a href="#/node/Adjacent">Adjacent</a> when they share a border point that is not a corner. Diagonal regions of a
    checkerboard meet only at a corner, so they may share a colour; the four regions of
    <code>FourColor/Nonvacuity.lean</code> are pairwise adjacent, so four colours really are needed.</p>
    <div id="pg1"></div>
    <h2>Hypermaps</h2>
    <p class="muted">The proof leaves the plane almost immediately. A <a href="#/node/Hypermap">Hypermap</a> is three
    permutations of a set of darts with <code>node * face * edge = 1</code>; planarity is the Euler-formula condition
    <a href="#/node/Hypermap.genus">genus</a> <code>= 0</code>.</p>
    <div id="pg2"></div>
    <h2>Kempe chains</h2>
    <p class="muted">Swapping two colours along a chain keeps a colouring proper. Kempe's 1879 proof that this always
    repairs a pentagon was wrong, and repairing that gap is what the 633 configurations are for.</p>
    <div id="pg3"></div>
    <h2>Traces as numbers</h2>
    <p class="muted">The colourings of a ring of <i>n</i> faces are recorded by their <code>trace</code> — the sums of
    adjacent colours — and a trace is stored as a base-3 number, so a whole set of them is one number with
    3<sup>n−1</sup> bits.</p>
    <div id="pg4"></div>
    <h2>Reducibility</h2>
    <p class="muted">A configuration is reducible when every colouring of its ring can be made to extend into it. The
    Birkhoff diamond can; a lone pentagon cannot.</p>
    <div id="pg5"></div>`;
  mountWidget(document.getElementById("pg1"), { type: "map-color", title: "Colour the regions",
    config: { preset: "checkerboard", show: ["adjacency", "solve", "corners", "connected"] } });
  mountWidget(document.getElementById("pg2"), { type: "hypermap", title: "Hypermap explorer",
    config: { preset: "tetrahedron", show: ["cycles", "relation", "euler", "planar", "plain", "cubic", "connected", "coloring"] } });
  mountWidget(document.getElementById("pg3"), { type: "kempe", title: "Tait colours and Kempe chains", config: { preset: "cube" } });
  mountWidget(document.getElementById("pg4"), { type: "trace-bits", title: "One number per trace", config: { n: 5 } });
  mountWidget(document.getElementById("pg5"), { type: "reducible", title: "Is it reducible?", config: { config: "birkhoff-diamond" } });
}

// ------------------------------------------------------------------ about
function aboutPage() {
  app.innerHTML = `<h1>About this site</h1>
  <div class="eli5">
  <p>Formalization usually goes from English to Lean: the job is done when Lean accepts the proof. This site goes the
  other way — <b>informalization</b>. The Lean proof of the Four Colour Theorem is finished and checks. The job here is
  done when a <b>reader</b> accepts it: when you can say what each formal statement means and back that up by passing
  a quiz.</p>

  <h2>What is being read</h2>
  <p>Chris Emery's <a href="https://github.com/corun1024/4ct" target="_blank" rel="noopener">corun1024/4ct</a>, a complete
  Lean 4 proof of the Four Colour Theorem over Mathlib, following the architecture of Georges Gonthier and Benjamin
  Werner's Coq proof. It is vendored unmodified in this repository's <code>4ct/</code> directory at upstream commit
  <code>3db71e0</code> (Lean v4.34.0-rc2), so every file path on this site is a path inside <code>4ct/</code>.</p>
  <p>The statement is in <a href="#/node/FourColorTheorem"><code>4ct/FourColor/RealPlane.lean</code></a>, a 195-line file
  that imports three Mathlib topology modules and no module of the development:
  <code>def FourColorTheorem : Prop := ∀ m : PlaneMap, SimpleMap m → ColorableWith 4 m</code>.
  A <a href="#/node/PlaneMap">map</a> assigns a region to each point; a <a href="#/node/PlainMap">plain</a> map is a
  partial equivalence relation, whose classes are its regions; a <a href="#/node/SimpleMap">simple map</a> is a plain map
  whose classes are open and connected; and a <a href="#/node/Coloring">colouring</a> is a coarser map that separates
  regions sharing a non-corner border point.</p>

  <h2>How “understood” works</h2>
  <ul>
  <li>Each node is one Lean declaration. ${decls.length} of them are listed here, ${reachable.length} of them reachable
  from <code>fourColorTheorem</code>, extracted from the compiled proof (plus a few rows read from source — see
  <a href="#/trust">Trust</a>).</li>
  <li>A node with an explainer has the verbatim Lean, a plain-English reading, sometimes an interactive illustration,
  and a quiz with an answer key.</li>
  <li>You can sign off on a node only after passing its quiz. It counts as <b>understood</b> once you've signed off on
  it <i>and</i> every project declaration its statement mentions is understood. For a definition the body counts as
  part of the statement, because the body is what it means. For a theorem only the statement counts, because which
  proof you use doesn't change what is being claimed.</li>
  <li>Mathlib's definitions are taken as given and linked to their documentation.</li>
  <li>Understanding the <i>proof</i> means understanding every declaration it uses. The progress bar on the graph page
  tracks that.</li>
  </ul>
  <p>Every demonstration widget on this site is an <b>illustration</b>: a small decidable model, a drawing, or a
  brute-force search over a finite case. None of them is evidence for the theorem, and each prints a line saying so.
  (The <code>outline</code> and <code>walkthrough</code> widgets are not demonstrations at all — they are linked
  summaries of the proof's own steps.)</p>

  <h2>Contributing (humans and AI agents)</h2>
  <p>Every explainer is one Markdown file, <code>site/nodes/&lt;id&gt;.md</code>, with YAML frontmatter that holds the quiz
  key. See <a href="https://github.com/${REPO}/blob/main/CONTRIBUTING.md">CONTRIBUTING.md</a>. CI validates each file
  against a JSON schema and against the extracted Lean declarations. Each stub page has a ready-made agent prompt, and
  <a href="data/needs-explainer.json">data/needs-explainer.json</a> lists the open work, nearest the theorem first.</p>

  <h2>Credits</h2>
  <ul>
  <li><b>The Lean proof: Chris Emery</b>, <a href="https://github.com/corun1024/4ct" target="_blank" rel="noopener">corun1024/4ct</a>,
  MIT, Copyright (c) 2026 Chris Emery. Vendored here unmodified.</li>
  <li><b>The mathematics: Georges Gonthier and Benjamin Werner</b>, whose Coq proof
  (<a href="https://github.com/rocq-community/fourcolor" target="_blank" rel="noopener">rocq-community/fourcolor</a>, CeCILL-B)
  this development follows — the same reduction to finite planar hypermaps, the same 633 reducible configurations, the
  same seven discharging presentations. No Coq source text is copied into the Lean repository, but three kinds of
  <i>data</i> are mechanical translations of it and say so in their headers: <code>FourColor/Configurations.lean</code>
  (from <code>configurations.v</code>), the <code>FourColor/Present*.lean</code> scripts (from <code>present*.v</code>),
  and the quiz data computed from the configurations.</li>
  <li><b><a href="https://github.com/leanprover-community/mathlib4" target="_blank" rel="noopener">Mathlib</a></b>, Apache-2.0,
  which supplies ℝ, the permutation and topology theory, and much else.</li>
  <li><b>AI disclosure, upstream.</b> The 4ct README states that the development was written with heavy use of AI —
  Claude Fable 5.1 produced essentially all of the Lean proofs, the certificate engines and the generators, and Claude
  Opus 5 the repository layout and build tooling — and asks readers not to take the theorem on the author's authority
  or the model's, but to read the statement and run the checker.</li>
  <li><b>This site.</b> The explanations, quizzes and widgets here are community work: written by AI agents for
  Michal Wallace (<a href="https://github.com/tangentstorm" target="_blank" rel="noopener">tangentstorm</a>). They are
  <b>not endorsed by Chris Emery</b>, are not part of the proof, and may be wrong. When this site and the Lean disagree,
  the Lean is right.</li>
  </ul>
  </div>`;
}

// ------------------------------------------------------------------ trust
function trustPage() {
  app.innerHTML = `<h1>Trust: what was checked, and where</h1>
  <div class="eli5">
  <p>A formal proof is only worth what its statement says and what actually checked it. Here is the honest accounting
  for this site, separating <b>upstream's claim</b>, <b>what this repository's maintainers re-checked on their own
  machine</b>, and <b>what nobody here checked</b>.</p>

  <h2>The statement</h2>
  <p><code>4ct/FourColor/RealPlane.lean</code> is 195 lines and imports three Mathlib topology modules and nothing from
  the development. It defines everything the statement needs elementarily — <code>IsOpenRegion</code>,
  <code>regionClosure</code>, <code>IsConnectedRegion</code>, <code>PlainMap</code>, <a href="#/node/SimpleMap">SimpleMap</a>,
  <code>border</code>, <code>notCorner</code>, <a href="#/node/Adjacent">Adjacent</a>, <a href="#/node/Coloring">Coloring</a>,
  <a href="#/node/ColorableWith">ColorableWith</a> — and ends with
  <code>def FourColorTheorem : Prop := ∀ m : PlaneMap, SimpleMap m → ColorableWith 4 m</code> (followed only by
  <code>FourColorTheoremFinite</code>, the finite version the compactness step uses). Two of the elementary notions are
  proved to be Mathlib's in that same file — <code>isOpenRegion_iff</code> (<code>IsOpenRegion = IsOpen</code>) and
  <code>regionClosure_eq</code> (<code>regionClosure = closure</code>), both unconditional. The 61-line
  <code>FourColor/RealPlaneMathlib.lean</code> adds the third, <code>isConnectedRegion_iff_isPreconnected</code>, which
  takes <code>IsOpenRegion r</code> as a hypothesis, and restates the whole hypothesis as <code>simpleMap_iff</code>. So
  the statement can be read in either vocabulary. It is stated over Mathlib's ℝ; Gonthier's Coq statement is over any
  model of the reals.</p>
  <p>The statement is not vacuous. <code>FourColor/Nonvacuity.lean</code> exhibits four open connected regions of the
  plane — the unit square, the strip to its right, the quadrant above it, and the complement of the closed first
  quadrant — which are pairwise <code>Adjacent</code>, so <code>Adjacent</code> is satisfiable and, by pigeonhole, the
  map is not <code>ColorableWith 3</code>. The four is tight. (That file was not built here; it is read from source.)</p>

  <h2>Built and checked on this box</h2>
  <ul>
  <li><b>FourColor.Main</b> and its import closure, 60 modules: the whole mathematics layer. <code>#print axioms</code>
  on <code>fourColorTheorem_of_checks</code>, <code>fourColorTheorem_of_unavoidability</code>,
  <code>fourColorTheorem_of_finite</code>, <code>discretize</code>, <code>redpartSound_theRedpart</code>,
  <code>Hypermap.not_minimalCounterExample</code> and <code>simpleMap_iff</code> each gives exactly
  <code>[propext, Classical.choice, Quot.sound]</code> — Lean's three standard axioms and nothing else.</li>
  <li><b>FourColor.RealPlaneMathlib</b>, the bridge between the elementary statement and Mathlib's topology.</li>
  <li><b>Five of the seven unavoidability presentations</b>: <code>Present5</code>, <code>Present6</code>, <code>Present9</code>,
  <code>Present10</code> and <code>Present11</code> with their generated check modules (149 modules, about an hour on two cores).
  <code>#print axioms</code> on <code>exclude5</code>, <code>exclude6</code>, <code>exclude9</code>, <code>exclude10</code> and
  <code>exclude11</code> gives <code>[propext, Classical.choice, Quot.sound]</code>.</li>
  </ul>

  <h2>Not built here — upstream's claim</h2>
  <ul>
  <li>The <b>633 reducibility certificates</b> (<code>FourColor.Bulk.Cfg.*</code>, <code>FourColor.Mask.*</code>,
  <code>FourColor.Reduce.All</code>), the presentations for hub arities <b>7 and 8</b> (<code>Present7</code>,
  <code>Present8</code>: one of their check modules peaks at 9.2 GB), and <b><code>FourColor.Complete</code> itself</b>, which is where
  <code>fourColorTheorem</code> is stated. One certificate module peaks at <b>20.5 GB</b> of RAM and this machine has
  15 GB, so they were not re-run. The axioms of <code>fourColorTheorem</code> itself are therefore upstream's claim, not
  a local re-verification. Upstream's README reports
  <code>FourColor.fourColorTheorem : FourColor.FourColorTheorem depends only on [propext, Classical.choice, Quot.sound]</code>
  and <code>checked 115342 FourColor declarations: no sorries, no extra axioms</code>.</li>
  <li>In short: <b>this site's maintainers re-checked the mathematics layer and five of the seven presentations, but not the
  reducibility certificates.</b></li>
  </ul>

  <h2>Kernel evaluation, not native code</h2>
  <p>Every computation in the development is <code>decide +kernel</code> — about fifty thousand uses — and not
  <code>native_decide</code>. The difference matters: <code>native_decide</code> compiles the computation and trusts the
  compiler and the runtime, while <code>decide +kernel</code> makes Lean's own kernel evaluate it. A grep of the
  committed sources finds no <code>sorry</code>, no <code>native_decide</code>, no <code>ofReduceBool</code>, no
  <code>axiom</code>, and no <code>unsafe</code>, <code>partial</code>, <code>opaque</code> or
  <code>implemented_by</code> declaration. Upstream's <code>scripts/check.sh</code> enforces that on every build.</p>

  <h2>Where the reducibility check differs from Coq's</h2>
  <p>Coq settled reducibility by running a Kempe-chain closure program on a bytecode machine added to Coq for the
  purpose. Lean has no such machine, and <code>native_decide</code> was ruled out, so the computation was redesigned:
  the traces of a ring of size <i>n</i> are packed into a single natural number with 3<sup>n−1</sup> bits, and Kempe
  flips and colour permutations become shift-and-mask operations on GMP-accelerated <code>Nat</code> literals. A
  one-chord rule settles 523 of the 633 configurations; a guided “mask walk” with witnesses supplied as data settles
  the other 110. The soundness of both is proved once, generically, in <code>FourColor/Bulk/</code> and
  <code>FourColor/Mask*.lean</code>. The certificates themselves are produced by <b>untrusted</b> scripts
  (<code>scripts/gen_certificates.sh</code>) and then kernel-checked, so nothing in the proof depends on the generator
  being correct. This is the one place where the development genuinely deviates from the Coq proof rather than
  re-expressing it.</p>

  <h2>Two results deliberately not ported</h2>
  <p><code>Jordan_planar</code> and <code>Jordan_WalkupE</code> — the converse direction, Jordan ⟹ planar — are not
  ported, because nothing uses them. Every use of planarity in the development is planar ⟹ Jordan, which is proved
  (<code>Hypermap.Planar.jordan</code>).</p>

  <h2>Rows added by hand</h2>
  <p>The declaration graph was extracted from the compiled proof, so declarations in modules that were not compiled
  here are missing from it. Rows for <code>fourColorTheorem</code>, <code>reducibility</code>,
  <code>theConfigs_length</code>, <code>reducible_all</code> and <code>exclude5</code>…<code>exclude11</code> were added
  by reading the source instead; their pages say so. <code>reducible_all</code> lives in a <i>generated</i> module that
  is not committed upstream at all.</p>

  <h2>And this site</h2>
  <p>The explanations, quizzes and interactive widgets here were written by AI agents for Michal Wallace
  (tangentstorm). They are not reviewed by Chris Emery, are not part of the proof, and carry no weight whatsoever as
  evidence. Each node lists its own faithfulness caveats; nodes marked <code>draft</code> have not yet been checked by
  a human against the Lean. If an explanation and the Lean disagree, the Lean is right —
  <a href="https://github.com/${REPO}/issues">please report it</a>.</p>
  </div>`;
}

route();
