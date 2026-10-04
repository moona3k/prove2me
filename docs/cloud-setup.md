# Claude Code cloud setup

## Select this repository

Open [Claude Code with this repository selected](https://claude.ai/code?repositories=moona3k%2Fprove2me),
connect GitHub if prompted, and choose `moona3k/prove2me` and branch `main`.
If the repository is missing from the selector, check the GitHub connection and
its repository access, then refresh the selector. Follow the
[official cloud quickstart](https://code.claude.com/docs/en/web-quickstart).

Repository creation does not configure your Claude account or install Lean in
the cloud environment. Allow network access to Prove2Me and the required Lean,
Mathlib, GitHub, and cache download endpoints in the cloud environment settings.
Use the current official setup references to identify required hosts.

## First task

Replace the placeholder with a specific mission or theorem:

```text
Read CLAUDE.md and AGENTS.md. Read https://prove2.me/start.md and the current
official Prove2Me guide. Work on <mission or theorem name/URL>. Retrieve the
target's exact statement and pinned Lean/Mathlib environment. Set up the matching
project under workspaces/ in this repository, preserve the platform module
layout, and compile your solution locally. Save sources, environment pins, and
verification notes on your task branch for review. Do not submit to Prove2Me
during this task. Never put credentials in Git or in the verification notes.
```

No Prove2Me account registration or submission is part of this repository's
initial setup. Supply any required API credentials privately through your cloud
environment. If credentials are unavailable, record the limitation and continue
only with publicly accessible material.

## Prepare a Lean project

Read the official [Lean setup reference](https://prove2.me/references/lean-setup.md).
Check for `elan` before installing it. For the selected target, create a project
under `workspaces/<mathlib-revision-prefix>/` with its exact `lean-toolchain`,
Lake configuration, and the three module directories. Match the server's
`autoImplicit false` setting.

For a new project, resolve dependencies with `lake update`, download the Mathlib
cache with `lake exe cache get`, and build the specific solution. For a project
with a committed lockfile, preserve its pins unless an update is required by
the target. Record successful and failed verification accurately.

## Later local migration

Wait for the agents using the source folder to finish or hand off their work.
Copy a reviewed set of Lean sources and their imported modules into the matching
project. Include its existing `lean-toolchain`, Lake configuration, and
`lake-manifest.json`; do not merge files from another revision into that project.
Copy useful notes separately after checking them for private data.

Keep the original folder available until the copied project has been verified.
Review `git status`, the proposed file list, and the staged diff before committing
and pushing. This task creates the skeleton only; no existing proofs or local
account data have been imported.
