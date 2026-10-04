import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn

namespace Supermodularity.Cooperative

/-- `IsConvexGame f` says the cooperative game with player set `Fin n` and
characteristic function `f` is a convex game (Topkis p. 207-208): `f ∅ = 0` and `f`
is supermodular on the Boolean lattice of subsets of the player set (`⊔ = ∪`,
`⊓ = ∩`). Since a supermodular `f` with `f ∅ = 0` is automatically superadditive
(Topkis p. 209), this already carries the book's standing "cooperative game"
hypotheses. -/
def IsConvexGame {n : ℕ} (f : Finset (Fin n) → ℝ) : Prop :=
  f ∅ = 0 ∧ Supermodularity.Monotonicity.SupermodularOn f Set.univ

end Supermodularity.Cooperative
