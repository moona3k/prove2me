# Environment 0df444a

- Platform environment: Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`,
  Lean `leanprover/lean4:v4.33.1` (platform default per the official
  `prove2me_workspace` references; confirm with `GET /api/v1/environments`).
- Target: none selected yet.
- `lake-manifest.json`: committed from `lake update`; Mathlib resolved to
  `0df444a360eaa60ab8c11dca51a86af692955474` (checked with
  `git -C .lake/packages/mathlib rev-parse HEAD`).

## Cloud setup status (2026-10-04)

- The environment network policy denies `prove2.me`, `release.lean-lang.org`,
  and the Mathlib cache host `lakecache.blob.core.windows.net` (all 17380
  cache downloads failed with a proxy 403). GitHub is reachable.
- Workaround used for the toolchain: installed elan from
  `raw.githubusercontent.com/leanprover/elan/master/elan-init.sh`, then
  downloaded `lean-4.33.1-linux.tar.zst` from GitHub releases and extracted it
  to `~/.elan/toolchains/leanprover--lean4---v4.33.1`.
- No Prove2Me API key is available in this environment.

## Verification

- `lake exe cache get`: failed (cache host blocked); the background run was
  stopped at its one-hour limit.
- `lake build Solutions.SmokeTest`: not run; without the cache it would
  compile Mathlib from source.
