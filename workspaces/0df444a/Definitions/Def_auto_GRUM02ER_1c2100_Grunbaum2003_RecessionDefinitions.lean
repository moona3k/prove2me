import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Group.Pointwise.Set.Basic

set_option autoImplicit false
open scoped Pointwise

namespace Grunbaum2003

/-- No straight line is contained in K: §2.5, printed p.24 / PDF p.42.
A nonzero direction parametrizes a genuine line, with all real parameters.
Local expression adapter; not a published Prove2Me definition. -/
def IsLineFree {d : ℕ} (K : Set (Fin d → ℝ)) : Prop :=
  ¬ ∃ x v : Fin d → ℝ, v ≠ 0 ∧ ∀ t : ℝ, x + t • v ∈ K

/-- The characteristic cone cc K of §2.5, p.24 / PDF p.42.
For nonempty closed convex K, the source's basepoint definition is independent
of the point x ∈ K. Universal quantification expresses that same cone without
choosing a basepoint. For the empty set it gives the whole space; this explicit
totalization does not change the representation since conv(ext ∅) is empty.
Local expression adapter; not a published Prove2Me definition. -/
def characteristicCone {d : ℕ} (K : Set (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  {v | ∀ x ∈ K, ∀ t : ℝ, 0 ≤ t → x + t • v ∈ K}

end Grunbaum2003
