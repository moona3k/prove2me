import Mathlib

namespace HighDimStat.Rkhs

open scoped RealInnerProductSpace

/-- A positive semidefinite (PSD) kernel function (Definition 12.6, p. 386): a symmetric
bivariate function `K : X × X → ℝ` such that for every finite collection of points and
weights, the associated quadratic form is nonnegative -- equivalently, the `n × n` Gram
matrix `K(xᵢ, xⱼ)` is positive semidefinite for every `n` and every choice of points. -/
def IsPSDKernel {X : Type*} (K : X → X → ℝ) : Prop :=
  (∀ x y, K x y = K y x) ∧
    ∀ (n : ℕ) (x : Fin n → X) (α : Fin n → ℝ), 0 ≤ ∑ i, ∑ j, α i * α j * K (x i) (x j)

/-- A Hilbert space `H`, presented via an injective linear embedding `toFun` into the space
of real-valued functions on `X`, has bounded evaluation functionals (Definition 12.12,
p. 390) if, for every point `x ∈ X`, the evaluation functional `f ↦ (toFun f) x` is a
bounded linear functional on `H`. -/
def HasBoundedEvalFunctionals {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) : Prop :=
  ∀ x : X, ∃ M : ℝ, ∀ f : H, |toFun f x| ≤ M * ‖f‖

/-- `H` (with embedding `toFun : H →ₗ[ℝ] (X → ℝ)` into functions on `X`) is a reproducing
kernel Hilbert space for the kernel `K`, with feature map `feature : X → H` picking out the
element `K(·, x) ∈ H` for every `x` (Eq. (12.3), p. 388): `toFun` is injective (so `H`
genuinely is a space of functions), `toFun (feature x)` really is the function `K(·, x)`,
and the reproducing property `⟨f, K(·,x)⟩_H = f(x)` holds for every `f ∈ H`, `x ∈ X`. -/
structure IsRKHS {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : X → X → ℝ) (toFun : H →ₗ[ℝ] (X → ℝ)) (feature : X → H) : Prop where
  toFun_injective : Function.Injective toFun
  feature_eq : ∀ x : X, toFun (feature x) = fun z => K z x
  reproducing : ∀ (f : H) (x : X), ⟪f, feature x⟫ = toFun f x

end HighDimStat.Rkhs
