import Mathlib
import Definitions.Def_CoresConvexGames_Stability_IsFeasible
import Definitions.Def_CoresConvexGames_Stability_Dominates

namespace CoresConvexGames.Stability

/-- Shapley (1971), p. 24, §4.3: a set `V` of feasible payoff vectors is *stable* if every
feasible payoff vector is either a member of `V` or dominated by a member of `V`, but not
both. -/
def IsStableSet {n : ℕ} (f : Finset (Fin n) → ℝ) (V : Set (Fin n → ℝ)) : Prop :=
  (∀ a ∈ V, IsFeasible f a) ∧
    ∀ b : Fin n → ℝ, IsFeasible f b → (b ∈ V ↔ ¬ ∃ a ∈ V, Dominates f a b)

end CoresConvexGames.Stability
