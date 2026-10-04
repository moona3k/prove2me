import Mathlib
import Definitions.Def_TheoryOfGames_Utility_UtilitySystem

namespace TheoryOfGames.Utility

/-- A numerical utility `v : U → ℝ` for a utility system `S` (3.5.1 and (A:V)):
(i) Monotony (3:1:a): `u > v` implies `v(u) > v(v)`;
(ii) (3:1:b), in the form of (A:V)(ii): for `0 < γ < 1` and any `u, v`,
`v((1 − γ)u + γv) = (1 − γ)v(u) + γv(v)`. -/
def IsNumericalUtility {U : Type*} (S : UtilitySystem U) (v : U → ℝ) : Prop :=
  (∀ u w : U, S.gt u w → v w < v u) ∧
    ∀ (γ : OpenUnit) (u w : U),
      v (S.cmb γ u w) = (1 - (γ : ℝ)) * v u + (γ : ℝ) * v w

end TheoryOfGames.Utility
