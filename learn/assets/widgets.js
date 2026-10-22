// Interactive demos. Each widget is mount(el, config) and is self-contained.
// The drawing-heavy ones live in widgets-interactive.js; the logic they share lives in
// small pure modules (see tools/test_widgets.mjs), which mirror the Lean definitions.
import { h, esc, btn } from "./dom.js";
import { INTERACTIVE } from "./widgets-interactive.js";

// A step's `link` may be a declaration id or an already-written route.
const nodeHref = (link) => (String(link).startsWith("#") ? String(link) : `#/node/${encodeURIComponent(link)}`);

// ---------------------------------------------------------------- outline
// A static proof outline. Each step may carry:
//   link: the explainer node it uses; decl: a declaration id, which the build resolves
//   into `src` (file, line range, browsable-source anchor) from data/decls.json;
//   hard: the step that carries the real content; gap: a hypothesis or step NOT proved here.
const srcLink = (src) => src
  ? `<div class="small src"><a class="srclink" href="../${esc(src.docs)}">${esc(src.file.replace(/^lean\//, ""))} lines ${src.line}–${src.endLine}</a></div>`
  : "";
function outlineWidget(el, cfg = {}) {
  el.append(h("div", { class: "flow", html: (cfg.steps || []).map((s, i) =>
    `${i ? '<div class="arrow">↓</div>' : ""}<div class="step${s.hard ? " hard" : ""}${s.gap ? " gap" : ""}">${s.gap ? '<span class="gaptag">not proved here</span> ' : ""}${s.link ? `<a href="${nodeHref(s.link)}">${esc(s.text)}</a>` : esc(s.text)}${s.note ? `<div class="small muted">${esc(s.note)}</div>` : ""}${srcLink(s.src)}</div>`).join("") }));
}

// ---------------------------------------------------------------- walkthrough
// A proof outline you step through, one line at a time, with the nodes each step uses.
function walkthroughWidget(el, cfg = {}) {
  const steps = cfg.steps || [];
  const listBox = h("div", { class: "flow wt" }), detail = h("div", { class: "wtdetail" });
  const bar = h("div");
  let i = 0, all = false;
  el.append(bar, listBox, detail);
  function run() {
    bar.innerHTML = "";
    bar.append(h("div", { class: "row steps" },
      btn("⏮", () => { i = 0; run(); }),
      btn("◀ back", () => { i = Math.max(0, i - 1); run(); }, { disabled: i === 0 ? "" : null }),
      btn("next ▶", () => { i = Math.min(steps.length - 1, i + 1); run(); }, { class: "primary", disabled: i >= steps.length - 1 ? "" : null }),
      h("span", { class: "small muted" }, ` step ${i + 1} / ${steps.length}`),
      btn(all ? "step through" : "show all", () => { all = !all; run(); })));
    listBox.innerHTML = steps.map((s, j) => {
      const on = all || j === i;
      return `${j ? '<div class="arrow">↓</div>' : ""}<div class="step${s.hard ? " hard" : ""}${j === i ? " on" : ""}${on ? "" : " off"}" data-j="${j}">${s.link ? `<a href="${nodeHref(s.link)}">${esc(s.text)}</a>` : esc(s.text)}</div>`;
    }).join("");
    listBox.querySelectorAll(".step").forEach((d) => d.addEventListener("click", (ev) => { if (ev.target.tagName !== "A") { i = +d.dataset.j; run(); } }));
    const s = steps[i] || {};
    const uses = [...(s.uses || []), ...(s.link ? [s.link] : [])].filter((v, k, a) => a.indexOf(v) === k);
    detail.innerHTML = `
      ${s.note ? `<p>${esc(s.note)}</p>` : ""}
      ${s.lean ? `<pre class="lean"><span class="var">${esc(s.lean)}</span></pre>` : ""}
      ${uses.length ? `<div class="small"><b>Nodes used here:</b> <span class="deps">${uses.map((u) => `<a href="${nodeHref(u)}">${esc(String(u).replace(/^#\/node\//, ""))}</a>`).join("")}</span></div>` : ""}`;
  }
  run();
}

const REGISTRY = { outline: outlineWidget, walkthrough: walkthroughWidget, ...INTERACTIVE };

export function mountWidget(container, spec) {
  const box = h("div", { class: "widget" });
  if (spec.title) box.append(h("h3", {}, spec.title));
  container.append(box);
  const f = REGISTRY[spec.type];
  if (!f) { box.append(h("p", { class: "err" }, `unknown widget ${spec.type}`)); return; }
  try { f(box, spec.config || {}); } catch (e) { box.append(h("p", { class: "err" }, e.message)); }
}
export const WIDGET_TYPES = Object.keys(REGISTRY);
