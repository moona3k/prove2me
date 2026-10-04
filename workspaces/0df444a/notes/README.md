# Workspace 0df444a — verification notes

Environment (platform default):

- Lean toolchain: `leanprover/lean4:v4.33.1`
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- `autoImplicit false`

Setup: `lake update && lake exe cache get` (cache hit; no Mathlib rebuild).
Mirrored `Theorems/` files keep the platform's `sorry` placeholder; `Definitions/`
files are copied verbatim from the platform.

Verification command for each solution (run from this directory):

```
lake build Solutions.<module>
```

plus a type-match check `example : type_of% @<target> := @solution` and
`#print axioms solution` (both done in a scratch file outside the repo).

## Solutions

| Target | Theorem ID | Status | Local result |
|---|---|---|---|
| `KonyaginUnitVectors.sum_norm_le_of_triangle_free` (Lovász Problem 11.8, Konyagin's upper bound) | `672c9770-ae08-4dcf-8113-f2a32db8580f` | Open on platform | Builds; type matches; axioms `propext, Classical.choice, Quot.sound` |
| `CoresConvexGames.Stability.core_is_unique_stable_set` (Shapley 1971, Thm 8) | `1fdc7c19-f93b-4e4c-92e0-dafd8eac2353` | Open on platform | Builds; type matches; axioms `propext, Classical.choice, Quot.sound` |

No platform submissions have been made from this workspace yet.
