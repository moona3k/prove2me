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
| `TheoryOfGames.Utility.utility_existence_uniqueness` (von Neumann–Morgenstern utility theorem, (A:V)+(A:W)) | `25ec0115-3057-4016-b9cc-e88105b23a81` | Open on platform | Builds; type matches; axioms `propext, Classical.choice, Quot.sound` |

No platform submissions have been made from this workspace yet.

## Proof sketches

- **Konyagin.** Let `S = Σ uᵢ`, `s = ‖S‖`, `αⱼ = ⟪uⱼ, S⟫`. Neighbours of a vertex
  in the non-orthogonality graph are pairwise orthogonal (triangle-freeness), so
  Bessel gives `Σ_{j∈N(i)} αⱼ² ≤ s²` and `(Σ_{k∈N(j)} ⟪uⱼ,uₖ⟫)² ≤ |N(j)|`. Since
  `αⱼ = 1 + Σ_{k∈N(j)} ⟪uⱼ,uₖ⟫`, summing gives `Σ (αⱼ² − αⱼ)² ≤ n s²`; with
  `Σ αⱼ = s²` and Cauchy–Schwarz twice, `s³ ≤ n² + n s`, hence `s ≤ 2 n^{2/3}`.
  This avoids the Lovász theta function that the mission description anticipated.
- **Shapley.** Core vectors are undominated. A feasible `b` outside the core is
  dominated by a core vector built from a coalition `S` maximizing
  `(f S − b(S))/|S|`: raise `b` uniformly on `S`, then extend to a core vector one
  player at a time with marginal contributions (supermodularity). Uniqueness
  follows from these two facts.
- **vNM utility.** From (3:A)–(3:C): `mix α u u = u`; the mixture algebra on a
  segment `P c d α`; strict monotonicity and (via a supremum and (3:B:c,d))
  surjectivity of `α ↦ P c d α` onto `[c, d]`. Coordinates on nested segments are
  affinely related, so normalizing at fixed `a ≺ b` gives a well-defined utility.
  Uniqueness: `v' − ω₀ v − ω₁` is affine on segments and vanishes at `a, b`.

## Statement issues found

- `HighDimStat.Rkhs.thm12_11_moore_aronszajn` (`d1739662-…`): the existence clause
  asks for `∃ H : Type` (universe 0) while `X : Type*` is universe-polymorphic. For
  `X : Type 1` with more elements than any small type (e.g. `X = Type`) and the
  delta kernel (PSD), the feature map `X → H` of any RKHS is injective
  (orthonormal images), which is impossible for `H : Type`. So the statement is not
  provable as written; `H : Type*` at `X`'s universe (or `X : Type`) would fix it.
