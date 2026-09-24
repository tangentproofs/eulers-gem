# Prove2.me tracking (local-first)

Track the Euler's Gem Lean formalization as a **declaration / milestone graph**
in-repo. The prove2.me **database itself is cloud API–only** (no self-hosted DB
found); local tracking means a workspace-style layout and JSON graph here, not
a mirror of their Postgres.

## What “local” means

| Layer | Role |
|-------|------|
| **This dir (`prove2/`)** | Milestone graph + notes; commit-friendly; no secrets |
| **`$HOME/prove2me_workspace`** (optional, machine-local) | Upstream [prove2me_workspace](https://github.com/prove2me/prove2me_workspace) layout (`Definitions/`, `Theorems/`, `Solutions/`) for local Lean checks against platform shapes |
| **prove2.me API** | Cloud verification / missions only — **do not** register or call authenticated endpoints from CI agents unless Michal opts in |

## Planned wiring (later, non-blocking)

1. Keep `milestones.json` in sync with `lean/Results.lean` + open goals in
   `lean/EulersGem/Polyhedron.lean` (Paulson-first roadmap).
2. Optional: private prove2.me mission or `upload_full_project` once `lake build`
   is green and statements are stable — see
   https://prove2.me/references/upload_full_project.md
3. Prefer **sketches / reductions** on prove2 for Paulson substrate lemmas
   (hyperplane cells → Euler char invariance → cones → polytopes).

## Do not

- Commit `credentials.json` / API keys
- Block Lean PRs on prove2 account setup
- Treat Poly100 Tverberg notes as the Lean mission tree (Paulson is primary)

See also: `lean/PROVE2.md`, root README “Tracking” section.
