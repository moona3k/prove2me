# Proof workspaces

Create one Lean project per pinned Mathlib revision. A project can hold several
missions when they share that environment:

```text
workspaces/<mathlib-revision-prefix>/
  lean-toolchain
  lakefile.lean                 # or lakefile.toml
  lake-manifest.json
  Definitions/
  Theorems/
  Solutions/
  notes/
```

The folder name is a convenience; the full revision in the Lake configuration
and lockfile is authoritative. Run Lake commands from that project's directory.
Track all imported Lean modules needed to reproduce a solution, together with
the source and environment pins. `.lake/` and credentials remain ignored.

In the project notes, record the mission/theorem identifier and URL, full Mathlib
revision, Lean version, proof status, unresolved dependencies, and verification
command and result. Include submission IDs and platform verdicts if authorized
submissions occur. Verify contributor handles and contributions before adding
attribution.
