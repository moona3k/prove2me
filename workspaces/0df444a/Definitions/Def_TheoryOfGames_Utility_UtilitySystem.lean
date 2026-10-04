import Mathlib

namespace TheoryOfGames.Utility

/-- The open unit interval `0 < α < 1`, the only range of the book's mixing weights
(3.6.1, footnote 4: "the α, β, γ occurring here are always > 0, < 1"). -/
abbrev OpenUnit : Type := Set.Ioo (0 : ℝ) 1

/-- `α ↦ 1 − α` on the open unit interval. -/
def OpenUnit.oneSub (α : OpenUnit) : OpenUnit :=
  ⟨1 - (α : ℝ), by
    obtain ⟨h0, h1⟩ := α.2
    exact ⟨by linarith, by linarith⟩⟩

/-- The product `αβ` of two weights in the open unit interval. -/
def OpenUnit.mul (α β : OpenUnit) : OpenUnit :=
  ⟨(α : ℝ) * (β : ℝ), by
    obtain ⟨ha0, ha1⟩ := α.2
    obtain ⟨hb0, hb1⟩ := β.2
    exact ⟨mul_pos ha0 hb0, by nlinarith⟩⟩

/-- A system `U` of (abstract) utilities in the sense of von Neumann–Morgenstern, 3.6.1:
a relation `gt u v` ("u > v", u is preferable to v) and, for every number `0 < α < 1`, an
operation `mix α u v`, written `αu + (1 − α)v` in the book, subject to the axioms
(3:A)–(3:C). Equality is true identity (A.1.2). No linear structure is assumed: `mix` is a
formal operation satisfying only the axioms below, and it is not defined for `α = 0, 1`. -/
structure UtilitySystem (U : Type*) where
  /-- The relation `u > v`. -/
  gt : U → U → Prop
  /-- The operation `αu + (1 − α)v`, for `0 < α < 1`. -/
  mix : OpenUnit → U → U → U
  /-- (3:A:a) For any two `u, v` one and only one of `u = v`, `u > v`, `u < v` holds. -/
  complete : ∀ u v : U,
    (u = v ∧ ¬ gt u v ∧ ¬ gt v u) ∨ (gt u v ∧ u ≠ v ∧ ¬ gt v u) ∨
      (gt v u ∧ u ≠ v ∧ ¬ gt u v)
  /-- (3:A:b) `u > v`, `v > w` imply `u > w`. -/
  trans : ∀ u v w : U, gt u v → gt v w → gt u w
  /-- (3:B:a) `u < v` implies `u < αu + (1 − α)v`. -/
  lt_mix_of_lt : ∀ (α : OpenUnit) (u v : U), gt v u → gt (mix α u v) u
  /-- (3:B:b) `u > v` implies `u > αu + (1 − α)v`. -/
  mix_lt_of_gt : ∀ (α : OpenUnit) (u v : U), gt u v → gt u (mix α u v)
  /-- (3:B:c) `u < w < v` implies the existence of an `α` with `αu + (1 − α)v < w`. -/
  exists_mix_lt : ∀ u v w : U, gt w u → gt v w → ∃ α : OpenUnit, gt w (mix α u v)
  /-- (3:B:d) `u > w > v` implies the existence of an `α` with `αu + (1 − α)v > w`. -/
  exists_mix_gt : ∀ u v w : U, gt u w → gt w v → ∃ α : OpenUnit, gt (mix α u v) w
  /-- (3:C:a) `αu + (1 − α)v = (1 − α)v + αu`. -/
  mix_comm : ∀ (α : OpenUnit) (u v : U), mix α u v = mix (OpenUnit.oneSub α) v u
  /-- (3:C:b) `α(βu + (1 − β)v) + (1 − α)v = γu + (1 − γ)v` where `γ = αβ`. -/
  mix_mix : ∀ (α β : OpenUnit) (u v : U), mix α (mix β u v) v = mix (OpenUnit.mul α β) u v

namespace UtilitySystem

variable {U : Type*} (S : UtilitySystem U)

/-- `u < v`, i.e. `v > u`. -/
def lt (u v : U) : Prop := S.gt v u

/-- `u ≦ v`, i.e. `u = v` or `u < v`. -/
def le (u v : U) : Prop := u = v ∨ S.gt v u

/-- The appendix's notation `(1 − γ)u + γv`, i.e. the book's operation `αu + (1 − α)v`
with `α = 1 − γ`. -/
def cmb (γ : OpenUnit) (u v : U) : U := S.mix (OpenUnit.oneSub γ) u v

end UtilitySystem

end TheoryOfGames.Utility
