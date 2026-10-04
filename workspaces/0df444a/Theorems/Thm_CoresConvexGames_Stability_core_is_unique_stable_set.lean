import Mathlib
import Definitions.Def_Supermodularity_Cooperative_IsConvexGame
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_CoresConvexGames_Stability_IsStableSet
namespace CoresConvexGames.Stability

open Supermodularity.Cooperative

/-- Shapley (1971), p. 24, Theorem 8: the core of a convex game is stable, and it is the
unique stable set (von Neumann–Morgenstern solution). -/
theorem core_is_unique_stable_set {n : ℕ} (f : Finset (Fin n) → ℝ) (hf : IsConvexGame f) :
    IsStableSet f (Core Finset.univ f) ∧
      ∀ V : Set (Fin n → ℝ), IsStableSet f V → V = Core Finset.univ f := by sorry

end CoresConvexGames.Stability
