# Prove2.me notes (Lean tree)

Local tracking lives in [`../prove2/`](../prove2/) (`milestones.json`).

- **Primary strategy:** Paulson AFP (hyperplane arrangements / cell complexes).
- **Cloud DB:** prove2.me API only — optional private mission / `upload_full_project`
  after the scaffold is green; no authenticated calls from this repo’s CI by default.
- **Local workspace:** optional clone of `prove2me/prove2me_workspace` at
  `$HOME/prove2me_workspace` for platform-shaped `Theorems/` + `Solutions/` checks.
  Keep that out of this git repo (or gitignore credentials).

Update `../prove2/milestones.json` when Results.lean claims change.
