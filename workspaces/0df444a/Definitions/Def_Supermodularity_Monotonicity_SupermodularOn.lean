import Mathlib

namespace Supermodularity.Monotonicity

/-- `SupermodularOn f S` says the real-valued function `f` on a lattice `X` is
supermodular on `S ⊆ X`: `f x + f y ≤ f (x ⊔ y) + f (x ⊓ y)` for all `x y ∈ S`. Taking
`S = Set.univ` recovers Topkis's plain "`f` is supermodular on `X`". -/
def SupermodularOn {X : Type*} [Lattice X] (f : X → ℝ) (S : Set X) : Prop :=
  ∀ ⦃x : X⦄, x ∈ S → ∀ ⦃y : X⦄, y ∈ S → f x + f y ≤ f (x ⊔ y) + f (x ⊓ y)

end Supermodularity.Monotonicity
