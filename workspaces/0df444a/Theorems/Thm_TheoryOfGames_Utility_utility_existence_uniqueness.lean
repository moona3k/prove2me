import Mathlib
import Definitions.Def_TheoryOfGames_Utility_UtilitySystem
import Definitions.Def_TheoryOfGames_Utility_IsNumericalUtility
namespace TheoryOfGames.Utility

/-- (A:V) and (A:W): for every system `U` of utilities satisfying (3:A)–(3:C), there exists a
mapping `v` of all utilities to numbers with (i) Monotony, `u > v ⇒ v(u) > v(v)`, and
(ii) `v((1 − γ)u + γv) = (1 − γ)v(u) + γv(v)` for `0 < γ < 1` and any `u, v`; and for any two
such mappings `v`, `v'` there are fixed numbers `ω₀ > 0`, `ω₁` with `v'(w) = ω₀v(w) + ω₁` for
all `w`. -/
theorem utility_existence_uniqueness {U : Type*} (S : UtilitySystem U) :
    (∃ v : U → ℝ, IsNumericalUtility S v) ∧
      ∀ v v' : U → ℝ, IsNumericalUtility S v → IsNumericalUtility S v' →
        ∃ ω₀ ω₁ : ℝ, 0 < ω₀ ∧ ∀ w : U, v' w = ω₀ * v w + ω₁ := by sorry

end TheoryOfGames.Utility

