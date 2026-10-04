import Mathlib

namespace CoresConvexGames.Stability

/-- Shapley (1971), p. 16, §3: a payoff vector `a ∈ E^N` is *feasible* for the game `v`
if `a(N) ≤ v(N)`. Players are `Fin n`, a game is `f : Finset (Fin n) → ℝ`, and
`a(S) = ∑ i ∈ S, a i`. -/
def IsFeasible {n : ℕ} (f : Finset (Fin n) → ℝ) (a : Fin n → ℝ) : Prop :=
  ∑ i, a i ≤ f Finset.univ

end CoresConvexGames.Stability
