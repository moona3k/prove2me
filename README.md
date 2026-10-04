# Prove2Me contributions

Personal workspace for Lean 4 proofs, mission notes, and agent work on
[Prove2Me](https://prove2.me). This repository gives cloud coding agents a
GitHub project to work in.

This is a starter repository. It contains instructions and setup notes; proof
files, Lean projects, and build verification will be added when a target is
selected. See [cloud setup](docs/cloud-setup.md) to start a Claude Code session.

## Layout

- [AGENTS.md](AGENTS.md): working rules for agents.
- [CLAUDE.md](CLAUDE.md): Claude Code entry point.
- [workspaces/](workspaces/README.md): projects grouped by pinned Mathlib revision.
- [docs/](docs/cloud-setup.md): setup and migration guidance.

## Working on a target

1. Read the [official onboarding](https://prove2.me/start.md) and
   [agent guide](https://prove2.me/skill.md).
2. Select a mission or theorem and retrieve its exact statement, dependencies,
   and environment. Use its pinned Lean toolchain and Mathlib revision.
3. Create or reuse the matching project under `workspaces/`. Preserve the
   `Definitions/`, `Theorems/`, and `Solutions/` module layout inside it.
4. Commit the Lean sources, `lean-toolchain`, Lake configuration, and
   `lake-manifest.json`. Keep credentials and downloaded build artifacts local.
5. Compile the solution and record the target, dependency status, command, and
   result. Record a platform submission ID and verdict only after submission.

## Bringing existing work over

Keep the existing local agent workspace in place while agents are using it.
After a coordinated handoff, copy selected sources, dependencies, notes, and
environment pins into the matching project here. Keep different Mathlib
revisions in separate projects. Review notes and scripts for secrets and local
paths before publishing them.

Avoid copying `.git/`, `.lake/`, credentials, or an entire live directory. The
upstream workspace ignores its local environment configuration; this repository
deliberately tracks those files so cloud agents can reproduce a project.

## References

- [Prove2Me workflow and verification contract](https://prove2.me/about)
- [Official workspace and API references](https://github.com/prove2me/prove2me_workspace)
- [Claude Code cloud quickstart](https://code.claude.com/docs/en/web-quickstart)
