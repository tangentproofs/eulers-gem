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

Write learn/nodes/${d.id}.md following learn/CONTRIBUTING.md and learn/schema/node.schema.json:
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
      <a href="${editUrl}" target="_blank" rel="noopener">Write one on GitHub</a> (see <a href="https://github.com/${REPO}/blob/main/learn/CONTRIBUTING.md">learn/CONTRIBUTING.md</a>).</p>
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
    <p class="muted">Five things to push on: a solid you can turn in your hands, the alternating sum that
    <i>is</i> Euler's formula in every dimension, the count that leaves five Schläfli pairs, a lattice polygon whose
    hypotheses you can break, and the bookkeeping behind Pick's formula.
    Everything here is an <b>illustration</b> — the Lean in <code>lean/</code> is the ground truth, and these are small
    computable models of it. Each widget says so at the bottom.</p>

    <h2>Turn a polyhedron</h2>
    <p class="muted">Drag it. Tap a vertex, an edge or a face. <a href="#/node/Results.results_euler_polyhedron">Euler's
    polyhedron formula</a> asks for exactly two things of a set <code>p</code> in ℝ³:
    <a href="#/node/IsPolytope"><code>IsPolytope p</code></a> — it is the convex hull of finitely many points — and
    <a href="#/node/affDim"><code>affDim p = 3</code></a>. Then <code>V − E + F = 2</code>, where <code>V</code>,
    <code>E</code>, <code>F</code> count the <a href="#/node/IsFaceOf">faces</a> of affine dimension 0, 1 and 2.
    The last preset is a <b>picture frame</b>: a genuine polyhedron with a square hole, where
    <code>V − E + F = 0</code>. It is not convex, so it is not a convex hull of its vertices, so
    <code>IsPolytope</code> is false and the theorem has nothing to say about it. Euler's formula is not a fact about
    all polyhedra — it is a fact about convex ones.</p>
    <div id="pg1"></div>
    <p class="muted small">The "cut a corner" button truncates a vertex of degree <i>d</i>: one vertex leaves,
    <i>d</i> arrive, <i>d</i> edges and one face are added. <code>V − E + F</code> cannot notice.</p>

    <h2>The alternating sum</h2>
    <p class="muted"><a href="#/node/faceEulerSum"><code>faceEulerSum p n</code></a> is
    <code>∑ d ∈ range (n+1), (−1)ᵈ · #{faces of affDim d}</code>, and
    <a href="#/node/Results.results_euler_characteristic"><code>results_euler_characteristic</code></a> says it is
    <b>1</b> for every full-dimensional convex polytope, in every dimension. Two details are worth staring at: the
    body counts (a polytope is a face of itself, of the top dimension), and the empty set does not
    (<code>affDim ∅ = −1</code>, and the sum starts at <code>d = 0</code>). In dimension 3 the body's term is
    <code>−1</code>, and moving it to the other side is the whole of the step from <code>= 1</code> to
    <code>V − E + F = 2</code>.</p>
    <div id="pg2"></div>

    <h2>Five pairs</h2>
    <p class="muted">If every face of a convex 3-polytope is an <i>s</i>-gon and <i>m</i> edges meet at every vertex,
    double counting gives <code>s·F = 2E</code> and <code>m·V = 2E</code>; feed those and <code>V − E + F = 2</code>
    into each other and you get <code>E·(2s + 2m − s·m) = 2·s·m</code>, hence
    <a href="#/node/Platonic.sub_mul_lt_four"><code>(s−2)(m−2) &lt; 4</code></a>. With <code>s, m ≥ 3</code> that leaves
    five pairs. Note what this is and is not: a classification of <i>pairs of numbers</i>, not of solids.
    <a href="#/node/Results.results_five_platonic_solids">The Results theorem</a> proves the five pairs, plus the
    <code>(V,E,F)</code> of five numeric records. The solids themselves — all five, golden-ratio ones included — are
    built and proved regular in <a href="#/node/Results.results_five_platonic_solids_constructed">a separate
    theorem</a>; that every regular polyhedron has the face counts and type of one of them is only
    <a href="#/node/Results.results_regular_polyhedron_face_data">conditional</a>.</p>
    <div id="pg3"></div>

    <h2>Lattice polygons</h2>
    <p class="muted">Tap grid points to build your own polygon, or pick one of the presets — several of them are there
    to <i>fail</i> the hypotheses of <a href="#/node/Results.results_picks_theorem"><code>results_picks_theorem</code></a>
    and show what goes wrong. <code>B</code> is read off the edge gcds; <code>I</code> counts lattice points of the
    <b>convex hull of the vertex list</b> that are not on the edges, which is what
    <a href="#/node/Picks.LatticePolygon.interiorLatticePoints">the Lean definition</a> says — so for a non-convex
    polygon the Lean's <code>I</code> counts points the shape does not enclose.</p>
    <div id="pg4"></div>

    <h2>Counting a triangulation</h2>
    <p class="muted">Cut a lattice polygon into triangles of area ½. Then <code>T = 2I + B − 2</code>,
    <code>V = I + B</code>, <code>F = T + 1</code> and <code>2E = 3T + B</code>, and <code>V − E + F = 2</code> makes
    the area <code>T/2</code> equal <code>I + B/2 − 1</code>. That last step is
    <a href="#/node/Results.results_pick_count_of_euler"><code>results_pick_count_of_euler</code></a>, and it is
    <i>only</i> that step: it takes all five of those as hypotheses. Producing a triangulation whose counts really are
    these, for a given polygon, is the work.</p>
    <div id="pg5"></div>`;
  mountWidget(document.getElementById("pg1"), { type: "polyhedron", title: "A convex polytope, and one non-example",
    config: { preset: "cube", show: ["counts", "incidence", "truncate"] } });
  mountWidget(document.getElementById("pg2"), { type: "face-lattice", title: "f₀ … fₙ and the alternating sum",
    config: { n: 3 } });
  mountWidget(document.getElementById("pg3"), { type: "schlafli", title: "(s − 2)(m − 2) < 4" });
  mountWidget(document.getElementById("pg4"), { type: "pick", title: "A lattice polygon you can break",
    config: { preset: "triangle", show: ["counts", "hypotheses", "fan"] } });
  mountWidget(document.getElementById("pg5"), { type: "triangulate", title: "The counts, and why they add to 2",
    config: { I: 1, B: 6 } });
}

// ------------------------------------------------------------------ about
function aboutPage() {
  app.innerHTML = `<h1>About this site</h1>
  <div class="eli5">
  <p>Formalization goes from English to Lean: the job is done when Lean accepts the proof. This site goes the other
  way — <b>informalization</b>. The job here is done when a <b>reader</b> accepts it: when you can say what each
  formal statement means, hypotheses included, and back that up by passing a quiz.</p>

  <h2>What is being read</h2>
  <p><a href="https://github.com/${REPO}" target="_blank" rel="noopener">tangentproofs/eulers-gem</a>, a Lean 4
  formalization of <b>Euler's polyhedron formula</b> and the Euler–Poincaré characteristic of convex polytopes
  (Freek Wiedijk's <a href="https://www.cs.ru.nl/~freek/100/" target="_blank" rel="noopener">#13</a>), together with two
  of its classical consequences: the Schläfli-pair count behind the five Platonic solids, and Pick's formula for the
  area of a lattice polygon. The paper-facing statements are the ${ROOTS.length} theorems of
  <a href="../docs/Results.html"><code>lean/Results.lean</code></a>; everything else lives in
  <code>lean/EulersGem/</code>. The graph here covers the ${decls.length} declarations in the ${fileCount} modules
  that <code>Results.lean</code> imports; a few modules outside that closure — the geometric cube and octahedron,
  the metric-regularity file, and the quarantined <code>PlatonicGaps.lean</code> (which contains <code>sorry</code>)
  — are mentioned in the explainers but are not in the graph.</p>
  <p>The root is <a href="#/node/Results.results_euler_characteristic"><code>results_euler_characteristic</code></a>:
  a convex polytope filling its ambient dimension has <a href="#/node/faceEulerSum"><code>faceEulerSum = 1</code></a>.
  <a href="#/node/Results.results_euler_polyhedron"><code>results_euler_polyhedron</code></a> is the dimension-3
  reading, <code>V − E + F = 2</code>. The Platonic and Pick lanes hang below it — see
  <a href="#/trust">Trust</a> for exactly how much of each is actually discharged from that root, because it is not
  all of it.</p>

  <h2>How “understood” works</h2>
  <ul>
  <li>Each node is one Lean declaration. ${decls.length} are listed here, ${reachable.length} of them reachable from
  a <code>Results</code> theorem, extracted from the compiled proof by
  <a href="https://github.com/${REPO}/blob/main/learn/tools/ExtractDecls.lean"><code>ExtractDecls.lean</code></a>.</li>
  <li>A node with an explainer has the verbatim Lean, a plain-English reading, usually an interactive illustration,
  and a quiz with an answer key.</li>
  <li>You can sign off on a node only after passing its quiz. It counts as <b>understood</b> once you've signed off on
  it <i>and</i> every project declaration its statement mentions is understood. For a definition the body counts as
  part of the statement, because the body is what it means. For a theorem only the statement counts, because which
  proof you use doesn't change what is being claimed.</li>
  <li>Mathlib's definitions are taken as given and linked to their documentation. There is a lot of Mathlib here:
  <code>convexHull</code>, <code>IsExtreme</code>, <code>AffineSubspace.finDim</code>, <code>MeasureTheory.volume</code>
  and the inner-product-space hierarchy are all Mathlib's.</li>
  <li>Understanding the <i>proof</i> means understanding every declaration it uses. The second progress bar on the
  graph page tracks that.</li>
  </ul>
  <p>Every demonstration widget on this site is an <b>illustration</b>: a drawing, an exact computation on one example,
  or a table of small cases. None of them is evidence for a theorem, and each prints a line saying so. (The
  <code>outline</code> and <code>walkthrough</code> widgets are not demonstrations at all — they are linked summaries
  of the proof's own steps.)</p>

  <h2>Contributing (humans and AI agents)</h2>
  <p>Every explainer is one Markdown file, <code>learn/nodes/&lt;id&gt;.md</code>, with YAML frontmatter that holds the
  quiz key. See <a href="https://github.com/${REPO}/blob/main/learn/CONTRIBUTING.md">learn/CONTRIBUTING.md</a>. CI
  validates each file against a JSON schema and against the extracted Lean declarations. Each stub page has a
  ready-made agent prompt, and <a href="data/needs-explainer.json">data/needs-explainer.json</a> lists the open work,
  nearest a <code>Results</code> theorem first.</p>

  <h2>Credits</h2>
  <ul>
  <li><b>The proof strategy: Lawrence C. Paulson</b>, whose Isabelle/HOL AFP entry
  <a href="https://isa-afp.org/entries/Euler_Polyhedron_Formula.html" target="_blank" rel="noopener"><i>Euler's
  Polyhedron Formula</i></a> (2023, BSD; itself a port from HOL Light) this development follows: hyperplane
  arrangements, cell complexes, and invariance of the Euler characteristic under refinement. That entry is vendored
  for comparison under <code>isabelle/</code>, and <a href="../lean-afp.html">the Lean ↔ AFP map</a> lines the two up
  theorem by theorem.</li>
  <li><b>The mathematics: Jim Lawrence</b>, <i>A Short Proof of Euler's Relation for Convex Polytopes</i>, Canad.
  Math. Bull. 40 (1997) — the argument Paulson formalized and this repository re-formalizes.</li>
  <li><b>Kim Morrison</b> (<a href="https://github.com/kim-em" target="_blank" rel="noopener">kim-em</a>) contributed
  the finite-vertex-to-finite-halfspace representation theorem
  (<a href="#/node/IsPolytope.isPolyhedron"><code>IsPolytope.isPolyhedron</code></a>,
  <code>EulersGem/LinearInequalities.lean</code>, <code>PolyhedralRepresentation.lean</code>,
  <code>PolytopeHalfspaces.lean</code>, <code>UnconditionalEuler.lean</code>) and the contract and axiom checks, in
  <a href="https://github.com/${REPO}/pull/2" target="_blank" rel="noopener">PR #2</a>. That is what removed the
  halfspace-presentation hypothesis from the public Euler results: the H-description is now <i>proved</i> from the
  V-description rather than assumed.</li>
  <li><b><a href="https://github.com/leanprover-community/mathlib4" target="_blank" rel="noopener">Mathlib</a></b>,
  Apache-2.0, which supplies ℝ, convexity, extreme sets, affine dimension, Lebesgue measure and much else.</li>
  <li><b>David Richeson</b>, <i>Euler's Gem: The Polyhedron Formula and the Birth of Topology</i> (Princeton, 2008) —
  the book this repository is named after, and the source of the story the explainers tell. It is <i>literature</i>:
  nothing from it is stated in the Lean, and where the book proves something the Lean does not, the Lean wins here.</li>
  <li><b>AI disclosure.</b> The Lean in this repository was written by AI agents working for Michal Wallace
  (<a href="https://github.com/tangentstorm" target="_blank" rel="noopener">tangentstorm</a>), as were the
  explanations, quizzes and widgets on this site. They may be wrong. When this site and the Lean disagree, the Lean is
  right; when the Lean and the mathematics disagree, Lean's kernel still has the last word on what has been
  <i>proved</i>, which is why <a href="#/trust">Trust</a> is the page that matters.</li>
  </ul>
  </div>`;
}

// ------------------------------------------------------------------ trust
function trustPage() {
  app.innerHTML = `<h1>Trust: what each result proves, and what it does not</h1>
  <div class="eli5">
  <p>A formal proof is worth exactly what its statement says. This page is the honest accounting, theorem by theorem,
  for the ${ROOTS.length} paper-facing results of <a href="../docs/Results.html"><code>lean/Results.lean</code></a>.
  Three of them are genuine classical theorems. Three are arithmetic identities whose classical story lives in the
  <i>proof</i>, not the statement. Two are geometric statements about lattice polygons under restrictive
  hypotheses — and one of those hypotheses, a finite enumeration of the interior lattice points, is not proved
  anywhere here. One is a combinatorial classification that is routinely mis-stated as something stronger. Three
  are about regular polyhedra in ℝ³: the five solids built and proved regular, their pairwise non-similarity, and
  a <b>conditional</b> classification of the face data of any regular polyhedron.</p>
  <p>Where this page and <a href="../index.html">the overview page</a> or the README differ in emphasis, read the Lean.
  Every row below links to the statement.</p>

  <h2>The short table</h2>
  <div class="table-wrap"><table>
  <thead><tr><th>theorem</th><th>what it proves</th><th>what it does <i>not</i></th></tr></thead>
  <tbody>
  <tr><td><a href="#/node/Results.results_euler_characteristic"><code>results_euler_characteristic</code></a></td>
      <td><b>Euler–Poincaré, for real.</b> <code>IsPolytope p</code> (a finite convex hull) in a finite-dimensional
      real inner product space, with <code>affDim p = finrank E</code> and <code>1 ≤ finrank E</code>, gives
      <code>faceEulerSum p (finrank E) = 1</code> — the alternating sum over the geometric face sets.</td>
      <td>Nothing about non-convex bodies, or about a polytope that does <i>not</i> fill its ambient space (the
      full-dimensionality hypothesis is used; apply it inside the affine span instead), or about convex bodies that
      are not finite hulls (a ball).</td></tr>
  <tr><td><a href="#/node/Results.results_euler_relation_dimension_three"><code>results_euler_relation_dimension_three</code></a></td>
      <td><b>Euler's polyhedron formula.</b> In any 3-dimensional real inner product space, a polytope with
      <code>affDim p = 3</code> has <code>V − E + F = 2</code>, with <code>V, E, F</code> the cardinalities of the
      actual face sets <code>{f | IsFaceOf p f ∧ affDim f = d}</code> for <code>d = 0, 1, 2</code>.</td>
      <td>Not non-convex polyhedra (the picture frame in the <a href="#/playground">playground</a> has
      <code>V − E + F = 0</code>), not graphs drawn on a sphere, not arbitrary surfaces, not a genus formula.</td></tr>
  <tr><td><a href="#/node/Results.results_euler_polyhedron"><code>results_euler_polyhedron</code></a></td>
      <td>The same, specialized to <code>EuclideanSpace ℝ (Fin 3)</code>, with exactly two hypotheses:
      <code>IsPolytope p</code> and <code>affDim p = 3</code>. No halfspace presentation is supplied — it is proved.</td>
      <td>Same limits as the row above.</td></tr>
  <tr><td><a href="#/node/Results.results_five_platonic_solids"><code>results_five_platonic_solids</code></a></td>
      <td><b>The Schläfli-pair classification.</b> Part 1: a convex 3-polytope in which every 2-face has
      <code>s</code> edges, every vertex lies on <code>m</code> edges, <i>and every edge lies in exactly two
      2-faces</i>, has <code>(s, m) ∈ {(3,3), (3,4), (3,5), (4,3), (5,3)}</code>. Euler is discharged from the root,
      not assumed. Parts 2–6: the <code>(V,E,F,s,m)</code> of five numeric records.</td>
      <td><b>Not “there are exactly five Platonic solids”.</b> No metric regularity (equal edges, equal angles,
      congruent faces) in this statement, and no construction of any solid (parts 2–6 are
      <code>RegularNumbers</code> records; the solids are built in the next row). No uniqueness up to similarity.
      And the diamond property (two 2-faces per edge) is a <i>hypothesis</i>.</td></tr>
  <tr><td><a href="#/node/Results.results_five_platonic_solids_constructed"><code>results_five_platonic_solids_constructed</code></a></td>
      <td><b>The five Platonic solids exist.</b> Five explicit convex hulls in ℝ³ (coordinates in
      <code>ℤ[φ]</code>, <code>φ = Real.goldenRatio</code>), each proved a <i>regular polyhedron</i> —
      3-dimensional, with its isometries transitive on flags — with the classical <code>V, E, F</code> and
      <code>{s, m}</code>. Face lattices computed by the kernel.</td>
      <td>Existence only, not uniqueness. "Regular" is flag-transitivity; its equivalence with Euclid's
      "congruent regular faces" is classical but not formalized.</td></tr>
  <tr><td><a href="#/node/Results.results_regular_polyhedron_face_data"><code>results_regular_polyhedron_face_data</code></a></td>
      <td><b>CONDITIONAL.</b> A regular polyhedron satisfying <code>FaceLatticeFacts</code> (general facts about
      faces of 3-polytopes) has the <code>(V, E, F, s, m)</code> of one of the five.</td>
      <td><code>FaceLatticeFacts</code> is a <b>hypothesis</b>, not proved in general (gap
      <code>GAP_faceLatticeFacts</code>). Not uniqueness up to similarity: that also needs the unproved
      <code>GAP_rigidity</code>. The similarity classification is stated in <code>lean/PlatonicGaps.lean</code>,
      outside <code>Results</code>, and depends on <code>sorryAx</code>.</td></tr>
  <tr><td><a href="#/node/Results.results_platonic_solids_not_similar"><code>results_platonic_solids_not_similar</code></a></td>
      <td>The five constructed solids are pairwise non-similar (4, 8, 6, 20, 12 vertices).</td>
      <td>Nothing about polyhedra other than these five.</td></tr>
  <tr><td><a href="#/node/Results.results_picks_theorem"><code>results_picks_theorem</code></a></td>
      <td><b>Pick's theorem for strictly convex lattice polygons.</b> For a <code>LatticePolygon P</code> with
      distinct vertices and <code>StrictlyConvexCCW P</code>, and <i>any</i> <code>Finset S</code> whose coercion
      equals <code>P.interiorLatticePoints</code>, the Lebesgue measure of <code>P.convexHullRegion</code> is
      <code>ofReal (S.card + P.B/2 − 1)</code>. Real measure, real lattice-point counts.</td>
      <td>The existence of that <code>S</code> — finiteness of the interior lattice points — is <b>not proved</b>
      here; it is a hypothesis. If no such <code>S</code> existed for some polygon, the statement would be vacuous
      for it. Nothing about non-convex simple polygons: <code>interiorLatticePoints</code> is defined through the
      convex hull, so for a non-convex polygon the Lean's <code>I</code> is not the classical one. A convex polygon
      listed with collinear vertices fails <code>LocalCCWTurns</code> and must be re-listed first.</td></tr>
  <tr><td><a href="#/node/Results.results_picks_of_empty_primitive_fan"><code>results_picks_of_empty_primitive_fan</code></a></td>
      <td>Geometric, with no free Euler hypothesis: a strictly convex lattice polygon with distinct vertices,
      primitive edges and <b>no</b> interior lattice points has measure <code>ofReal (B/2 − 1)</code>.</td>
      <td>The special case <code>I = 0</code> only. The primitive-edge and empty-interior hypotheses are both real
      restrictions.</td></tr>
  <tr><td><a href="#/node/Results.results_pick_count_of_euler"><code>results_pick_count_of_euler</code></a></td>
      <td><b>Pure arithmetic.</b> From <code>V = I + B</code>, <code>F = T + 1</code>,
      <code>V − E + F = 2</code>, <code>2E = 3T + B</code> and <code>A = T/2</code> — all five
      <i>hypotheses</i> — it concludes <code>A = I + B/2 − 1</code>.</td>
      <td>Nothing about polygons, lattices, areas or Euler. The <code>heuler</code> input is a free hypothesis on
      bare numbers. It is the bookkeeping step, and it is honest about being one.</td></tr>
  <tr><td><a href="#/node/Results.results_fan_pick_of_euler"><code>results_fan_pick_of_euler</code></a></td>
      <td><b>The statement is <code>(n − 2)/2 = n/2 − 1</code> for <code>n ≥ 3</code>.</b> That is all it says.</td>
      <td>The statement proves nothing about fans or triangulations. The Euler characteristic appears in how the
      <i>proof</i> is routed (through a geometric triangle's characteristic and an induction over fans), not in what
      is claimed.</td></tr>
  <tr><td><a href="#/node/Results.results_disk_pick_of_euler"><code>results_disk_pick_of_euler</code></a></td>
      <td><b>Given <code>A = (2I + B − 2)/2</code> as a hypothesis</b> and <code>3 ≤ n ≤ B</code>, concludes
      <code>A = I + B/2 − 1</code>. An arithmetic consequence.</td>
      <td>The "triangulated disk" is in the proof route, not the statement; <code>n</code> appears only as a bound.
      No disk, no triangulation and no polygon is quantified over.</td></tr>
  </tbody></table></div>

  <h2>What is genuinely on the Euler–Poincaré spine</h2>
  <p>The repository's own rule (<code>lean/UNIFIED_SPINE.md</code>) is that the Platonic and Pick lanes must
  <i>discharge</i> Euler from the root rather than assume it. Where that stands:</p>
  <ul>
  <li><b>The root itself is clean.</b>
  <a href="#/node/Euler_Poincare_of_isPolytope"><code>Euler_Poincare_of_isPolytope</code></a> takes
  <code>IsPolytope</code>, full dimension and <code>1 ≤ finrank</code>, and nothing else. It gets the halfspace
  presentation it needs from <a href="#/node/IsPolytope.isPolyhedron"><code>IsPolytope.isPolyhedron</code></a>, and
  the finiteness of each face set from
  <a href="#/node/facesOfDim_finite_of_isPolytope"><code>facesOfDim_finite_of_isPolytope</code></a>. Both are theorems.</li>
  <li><b>Platonic: Euler is discharged.</b>
  <a href="#/node/Platonic.regular_polytope_counts"><code>regular_polytope_counts</code></a> proves
  <code>s·F = 2E</code> and <code>m·V = 2E</code> by double counting over face-lattice incidence and takes
  <code>V − E + F = 2</code> from the geometric relation. No bare Euler hypothesis survives. One polytope fact — the
  diamond property — is still assumed.</li>
  <li><b>Pick: partly.</b> <a href="#/node/Results.results_picks_theorem"><code>results_picks_theorem</code></a> is
  geometric and routes through
  <a href="#/node/Picks.triangulated_disk_euler_from_characteristic"><code>triangulated_disk_euler_from_characteristic</code></a>,
  whose proof starts at a geometric triangle's Euler–Poincaré characteristic and applies moves that preserve the
  count. But the <i>statement</i> of that lemma is an identity between numerals, and the three
  <code>*_of_euler</code> results above are arithmetic. The genuinely geometric Pick claims are
  <code>results_picks_theorem</code> and <code>results_picks_of_empty_primitive_fan</code>.</li>
  </ul>

  <h2>Definitions you have to accept for the statements to mean what they seem to</h2>
  <ul>
  <li><a href="#/node/IsPolytope"><code>IsPolytope p</code></a> is <code>∃ V, V.Finite ∧ p = convexHull ℝ V</code> —
  the V-description. The H-description, <a href="#/node/IsPolyhedron"><code>IsPolyhedron</code></a>, is a finite
  intersection of closed halfspaces, and the two are linked by a <i>theorem</i>, not by fiat.</li>
  <li><a href="#/node/IsFaceOf"><code>IsFaceOf p f</code></a> is Mathlib's <code>IsExtreme ℝ p f</code> together with
  convexity of <code>f</code>. It includes <code>f = ∅</code> and <code>f = p</code>. The empty face stays out of the
  counts only because <code>affDim ∅ = −1</code>.</li>
  <li><a href="#/node/affDim"><code>affDim s</code></a> is <code>−1</code> on <code>∅</code> and the
  <code>finDim</code> of the affine span otherwise, as an <code>ℤ</code>. It has a junk value of <code>0</code> when
  the direction is infinite-dimensional, which is why the Euler results carry
  <code>[FiniteDimensional ℝ E]</code>.</li>
  <li><code>Set.ncard</code> is <code>0</code> on an infinite set. So a count of <code>0</code> could in principle
  mean "infinitely many" — which is exactly why
  <a href="#/node/facesOfDim_finite_of_isPolytope"><code>facesOfDim_finite_of_isPolytope</code></a> has to be proved,
  and it is.</li>
  <li><a href="#/node/Picks.LatticePolygon"><code>Picks.LatticePolygon</code></a> asserts only
  <code>3 ≤ vertices.length</code>. It does not assert simplicity, convexity or even distinct vertices; those arrive
  as separate hypotheses.</li>
  </ul>

  <h2>Axioms</h2>
  <p>Lean reports, for each theorem, which axioms its proof depends on. Three are standard and expected
  (<code>propext</code>, <code>Classical.choice</code>, <code>Quot.sound</code>). Two are not:
  <code>sorryAx</code> would mean a hole, and a <code>native_decide</code> axiom would mean the compiler and the
  runtime were trusted instead of the kernel. <code>lean/scripts/audit-axioms.sh</code> checks every declaration in
  <code>Results.lean</code> and fails on either. The table below is that script's output.</p>
<div class="table-wrap"><table class="node-list"><thead><tr><th>Results theorem</th><th><code>#print axioms</code></th></tr></thead><tbody><tr><td><a href="#/node/Results.results_euler_characteristic"><code>results_euler_characteristic</code></a></td><td><code>[propext, Classical.choice, Quot.sound]</code></td></tr><tr><td><a href="#/node/Results.results_euler_relation_dimension_three"><code>results_euler_relation_dimension_three</code></a></td><td><code>[propext, Classical.choice, Quot.sound]</code></td></tr><tr><td><a href="#/node/Results.results_euler_polyhedron"><code>results_euler_polyhedron</code></a></td><td><code>[propext, Classical.choice, Quot.sound]</code></td></tr><tr><td><a href="#/node/Results.results_five_platonic_solids"><code>results_five_platonic_solids</code></a></td><td><code>[propext, Classical.choice, Quot.sound]</code></td></tr><tr><td><a href="#/node/Results.results_picks_theorem"><code>results_picks_theorem</code></a></td><td><code>[propext, Classical.choice, Quot.sound]</code></td></tr><tr><td><a href="#/node/Results.results_picks_of_empty_primitive_fan"><code>results_picks_of_empty_primitive_fan</code></a></td><td><code>[propext, Classical.choice, Quot.sound]</code></td></tr><tr><td><a href="#/node/Results.results_pick_count_of_euler"><code>results_pick_count_of_euler</code></a></td><td><code>[propext, Classical.choice, Quot.sound]</code></td></tr><tr><td><a href="#/node/Results.results_fan_pick_of_euler"><code>results_fan_pick_of_euler</code></a></td><td><code>[propext, Classical.choice, Quot.sound]</code></td></tr><tr><td><a href="#/node/Results.results_disk_pick_of_euler"><code>results_disk_pick_of_euler</code></a></td><td><code>[propext, Classical.choice, Quot.sound]</code></td></tr></tbody></table></div>
  <p class="small">Recorded on 2026-10-22 from a fresh <code>lake build</code> of this branch (Lean v4.35.0-rc1, Mathlib <code>09a9e06</code>):
  <code>lean/scripts/audit-axioms.sh</code> reports <b>AUDIT PASS</b> (no <code>sorry</code> in the sources; the
  <code>native_decide</code>s that remain, in the unit-square witnesses of <code>PlanarTriangulation.lean</code> and
  <code>PicksTriangulation.lean</code>, are not reached by any Results theorem), and <code>lean/EulerAudit.lean</code>
  reports its axiom audit passed for 76 representation and Euler declarations. These are Lean's three standard axioms
  and nothing else. <b>Not reproduced here:</b> the independent kernel replay
  (<code>lake env leanchecker EulersGem Results</code>, part of <code>lean/scripts/verify-euler.sh</code>) ran out of
  memory on the 15&nbsp;GB build machine, so it was not re-run for this build.</p>
  <p class="small muted"><code>lean/AXIOM_AUDIT.md</code> records the history, including three
  <code>native_decide</code>s that were removed from the Euler–Poincaré root for exactly this reason, and
  the earlier unit-square Pick declarations that did depend on one and are no longer exported.</p>

  <h2>And this site</h2>
  <p>The explanations, quizzes and interactive widgets here were written by AI agents for Michal Wallace
  (tangentstorm). They are not part of the proof and carry no weight as evidence. Nodes marked <code>draft</code> have
  not been checked by a human against the Lean. Each node lists its own faithfulness caveats. Every widget is an
  illustration and says so. If an explanation and the Lean disagree, the Lean is right —
  <a href="https://github.com/${REPO}/issues">please report it</a>.</p>
  </div>`;
}

route();
