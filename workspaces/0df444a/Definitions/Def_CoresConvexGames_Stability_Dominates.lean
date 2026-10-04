import Mathlib

namespace CoresConvexGames.Stability

/-- Shapley (1971), p. 24, §4.3, (21): `Dominates f a b` says the payoff vector `b` is
*dominated* by the payoff vector `a`: there is a nonempty coalition `S` with
`a(S) ≤ v(S)` and `a_i > b_i` for all `i ∈ S`. -/
def Dominates {n : ℕ} (f : Finset (Fin n) → ℝ) (a b : Fin n → ℝ) : Prop :=
  ∃ S : Finset (Fin n), S.Nonempty ∧ ∑ i ∈ S, a i ≤ f S ∧ ∀ i ∈ S, b i < a i

end CoresConvexGames.Stability
