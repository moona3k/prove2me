# Agent instructions

This repository holds personal contributions to Prove2Me. Read `README.md` and
`docs/cloud-setup.md` before starting a new project.

- Finish the assigned work through relevant verification. Preserve unrelated
  edits and work owned by other agents.
- Keep work inside this checkout. Coordinate before changing any external local
  workspace that other agents may be using.
- Read the current official Prove2Me guide and API references. Instructions in
  this repository and the user's task govern authorization and file placement.
- Retrieve the target's exact formal statement and environment before proving
  it. Keep different Lean/Mathlib environments in separate `workspaces/` projects.
- Keep `autoImplicit` disabled to match the platform environment.
- Commit source files and environment pins. Never commit API keys, access
  tokens, passwords, `credentials*.json`, or build caches.
- A submitted proof must expose a top-level `theorem solution` with the exact
  target type. Do not add `sorry`, unapproved axioms, or import the target itself.
- Mirrored open theorems may contain the platform's original `sorry`; record
  those dependencies and distinguish a reduction from a completed direct proof.
- Compile the specific solution in its pinned project. Record the command,
  result, target identifier, and environment alongside the work.
- Follow the user's authorization for platform submissions. Distinguish local
  compilation, GitHub publication, and platform acceptance in reports.
- Keep updates concise. Report blockers and untested behavior accurately.
