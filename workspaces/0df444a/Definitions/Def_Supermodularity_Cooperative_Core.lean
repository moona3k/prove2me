import Mathlib

namespace Supermodularity.Cooperative

/-- `Core U f` is the core of the cooperative game with characteristic function `f`
restricted to the coalition `U ⊆ Fin n` (Topkis p. 209): the payoff vectors `y` that
are feasible on `U` (`∑_{i∈U} y i = f U`) and acceptable on `U`
(`f S ≤ ∑_{i∈S} y i` for every `S ⊆ U`). `Core Finset.univ f` is the core of the
whole game; `Core U f` for `U ⊊ Finset.univ` is the core of the subgame `(U, f)`. -/
def Core {n : ℕ} (U : Finset (Fin n)) (f : Finset (Fin n) → ℝ) : Set (Fin n → ℝ) :=
  {y : Fin n → ℝ | (∑ i ∈ U, y i) = f U ∧ ∀ S ⊆ U, f S ≤ ∑ i ∈ S, y i}

end Supermodularity.Cooperative
