# Environment 0df444a

- Platform environment: Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`,
  Lean `leanprover/lean4:v4.33.1` (platform default per the official
  `prove2me_workspace` references; confirm with `GET /api/v1/environments`).
- Target: none selected yet.
- `lake-manifest.json`: not yet committed; `lake update` was still running
  when this skeleton was pushed.

## Cloud setup status (2026-10-04)

- The environment network policy denies `prove2.me`, `release.lean-lang.org`,
  and the Mathlib cache hosts tried so far (`lakecache.blob.core.windows.net`,
  `mathlib4.lean-cache.cloud`). GitHub is reachable.
- Workaround used for the toolchain: installed elan from
  `raw.githubusercontent.com/leanprover/elan/master/elan-init.sh`, then
  downloaded `lean-4.33.1-linux.tar.zst` from GitHub releases and extracted it
  to `~/.elan/toolchains/leanprover--lean4---v4.33.1`.
- No Prove2Me API key is available in this environment.

## Verification

- `lake build Solutions.SmokeTest`: not yet run.
