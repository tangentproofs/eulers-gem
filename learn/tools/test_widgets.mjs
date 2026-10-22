// Tests for the widget logic modules, each assertion keyed to the Lean definition it
// mirrors. Run by `npm test`. No browser: the modules are pure, and `dom.js`/`widgets.js`
// only touch `document` inside their functions.
import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { stepper, clampStep } from "../assets/dom.js";
import { WIDGET_TYPES } from "../assets/widgets.js";

const SITE = path.dirname(path.dirname(fileURLToPath(import.meta.url)));
let n = 0;
const t = (name, f) => { f(); n++; };
const eq = (a, b, m) => assert.deepEqual(a, b, m);

// ================================================================ widget logic tests go here

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

console.log(`widget logic: all ${n} test groups passed`);
