import Mathlib
open scoped RealInnerProductSpace

namespace KonyaginUnitVectorsProof

variable {d n : ℕ}

/-- Bessel's inequality for a finite family of pairwise orthogonal unit vectors. -/
theorem bessel {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type*}
    (F : Finset ι) (w : ι → E) (hn : ∀ k ∈ F, ‖w k‖ = 1)
    (ho : ∀ j ∈ F, ∀ k ∈ F, j ≠ k → ⟪w j, w k⟫ = 0) (x : E) :
    ∑ k ∈ F, ⟪w k, x⟫ ^ 2 ≤ ‖x‖ ^ 2 := by
  have hon : Orthonormal ℝ (fun k : F => w k) := by
    refine ⟨fun k => hn k k.2, ?_⟩
    intro j k hjk
    exact ho j j.2 k k.2 (fun h => hjk (Subtype.ext h))
  have h := hon.sum_inner_products_le (s := Finset.univ) (x := x)
  simp only [Real.norm_eq_abs, sq_abs] at h
  rw [← Finset.sum_coe_sort F]
  exact h

/-- Neighbourhood of `i` in the non-orthogonality graph. -/
noncomputable def nbr (u : Fin n → EuclideanSpace ℝ (Fin d)) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => j ≠ i ∧ ⟪u i, u j⟫ ≠ 0)

theorem mem_nbr (u : Fin n → EuclideanSpace ℝ (Fin d)) (i j : Fin n) :
    j ∈ nbr u i ↔ j ≠ i ∧ ⟪u i, u j⟫ ≠ 0 := by
  simp [nbr]

theorem mem_nbr_symm (u : Fin n → EuclideanSpace ℝ (Fin d)) (i j : Fin n) :
    j ∈ nbr u i ↔ i ∈ nbr u j := by
  rw [mem_nbr, mem_nbr, real_inner_comm]
  exact ⟨fun ⟨h1, h2⟩ => ⟨Ne.symm h1, h2⟩, fun ⟨h1, h2⟩ => ⟨Ne.symm h1, h2⟩⟩

/-- Triangle-freeness: neighbours of a vertex are pairwise orthogonal. -/
theorem orth_nbr (u : Fin n → EuclideanSpace ℝ (Fin d))
    (htri : ∀ i j k : Fin n, i ≠ j → j ≠ k → i ≠ k →
      ⟪u i, u j⟫ = 0 ∨ ⟪u j, u k⟫ = 0 ∨ ⟪u i, u k⟫ = 0)
    (i : Fin n) : ∀ j ∈ nbr u i, ∀ k ∈ nbr u i, j ≠ k → ⟪u j, u k⟫ = 0 := by
  intro j hj k hk hjk
  rw [mem_nbr] at hj hk
  rcases htri i j k (Ne.symm hj.1) hjk (Ne.symm hk.1) with h | h | h
  · exact absurd h hj.2
  · exact h
  · exact absurd h hk.2

/-- `⟪u j, ∑ u⟫ = 1 + ∑_{k ∈ N(j)} ⟪u j, u k⟫`. -/
theorem inner_sum_eq (u : Fin n → EuclideanSpace ℝ (Fin d)) (hu : ∀ i, ‖u i‖ = 1) (j : Fin n) :
    ⟪u j, ∑ i, u i⟫ = 1 + ∑ k ∈ nbr u j, ⟪u j, u k⟫ := by
  rw [inner_sum]
  have h2 : ∀ k, ⟪u j, u k⟫ = (if k = j then ⟪u j, u k⟫ else 0) +
      (if k ∈ nbr u j then ⟪u j, u k⟫ else 0) := by
    intro k
    by_cases hkj : k = j
    · subst hkj
      have : k ∉ nbr u k := by rw [mem_nbr]; tauto
      simp [this]
    · by_cases hz : ⟪u j, u k⟫ = 0
      · simp [hz]
      · have : k ∈ nbr u j := (mem_nbr u j k).2 ⟨hkj, hz⟩
        simp [hkj, this]
  rw [Finset.sum_congr rfl (fun k _ => h2 k), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ j, Finset.sum_ite_mem, Finset.univ_inter]
  simp only [Finset.mem_univ, if_true, real_inner_self_eq_norm_sq, hu j, one_pow]

/-- `(∑_{k ∈ N(j)} ⟪u j, u k⟫)^2 ≤ |N(j)|`. -/
theorem nbr_sum_sq_le (u : Fin n → EuclideanSpace ℝ (Fin d)) (hu : ∀ i, ‖u i‖ = 1)
    (htri : ∀ i j k : Fin n, i ≠ j → j ≠ k → i ≠ k →
      ⟪u i, u j⟫ = 0 ∨ ⟪u j, u k⟫ = 0 ∨ ⟪u i, u k⟫ = 0) (j : Fin n) :
    (∑ k ∈ nbr u j, ⟪u j, u k⟫) ^ 2 ≤ ((nbr u j).card : ℝ) := by
  have hcs := sq_sum_le_card_mul_sum_sq (s := nbr u j) (f := fun k => ⟪u j, u k⟫)
  have hbes := bessel (nbr u j) u (fun k _ => hu k) (orth_nbr u htri j) (u j)
  rw [hu j, one_pow] at hbes
  have hbes' : ∑ k ∈ nbr u j, ⟪u j, u k⟫ ^ 2 ≤ 1 := by
    simpa only [real_inner_comm] using hbes
  calc (∑ k ∈ nbr u j, ⟪u j, u k⟫) ^ 2
      ≤ ((nbr u j).card : ℝ) * ∑ k ∈ nbr u j, ⟪u j, u k⟫ ^ 2 := hcs
    _ ≤ ((nbr u j).card : ℝ) * 1 := by gcongr
    _ = ((nbr u j).card : ℝ) := mul_one _

/-- Summed Bessel: `∑_j |N(j)| ⟪u j, S⟫^2 ≤ n ‖S‖^2`. -/
theorem deg_weighted_le (u : Fin n → EuclideanSpace ℝ (Fin d)) (hu : ∀ i, ‖u i‖ = 1)
    (htri : ∀ i j k : Fin n, i ≠ j → j ≠ k → i ≠ k →
      ⟪u i, u j⟫ = 0 ∨ ⟪u j, u k⟫ = 0 ∨ ⟪u i, u k⟫ = 0) (x : EuclideanSpace ℝ (Fin d)) :
    ∑ j, ((nbr u j).card : ℝ) * ⟪u j, x⟫ ^ 2 ≤ n * ‖x‖ ^ 2 := by
  have h1 : ∀ i, ∑ j ∈ nbr u i, ⟪u j, x⟫ ^ 2 ≤ ‖x‖ ^ 2 := fun i =>
    bessel (nbr u i) u (fun k _ => hu k) (orth_nbr u htri i) x
  have h2 : ∑ i, ∑ j ∈ nbr u i, ⟪u j, x⟫ ^ 2 = ∑ j, ((nbr u j).card : ℝ) * ⟪u j, x⟫ ^ 2 := by
    calc ∑ i, ∑ j ∈ nbr u i, ⟪u j, x⟫ ^ 2
        = ∑ i, ∑ j, (if j ∈ nbr u i then ⟪u j, x⟫ ^ 2 else 0) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_ite_mem, Finset.univ_inter]
      _ = ∑ j, ∑ i, (if j ∈ nbr u i then ⟪u j, x⟫ ^ 2 else 0) := Finset.sum_comm
      _ = ∑ j, ∑ i, (if i ∈ nbr u j then ⟪u j, x⟫ ^ 2 else 0) := by
          refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
          exact if_congr (mem_nbr_symm u i j) rfl rfl
      _ = ∑ j, ((nbr u j).card : ℝ) * ⟪u j, x⟫ ^ 2 := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  rw [← h2]
  calc ∑ i, ∑ j ∈ nbr u i, ⟪u j, x⟫ ^ 2 ≤ ∑ _i : Fin n, ‖x‖ ^ 2 :=
        Finset.sum_le_sum (fun i _ => h1 i)
    _ = n * ‖x‖ ^ 2 := by simp

/-- Real-variable inequalities: from `∑ α = s²`, `∑ (α² - α)² ≤ n s²` deduce `s⁴ ≤ n (n s + s²)`. -/
theorem quartic_bound (α : Fin n → ℝ) (s : ℝ) (hs0 : 0 ≤ s)
    (hsum : ∑ j, α j = s ^ 2) (hc2 : ∑ j, (α j ^ 2 - α j) ^ 2 ≤ n * s ^ 2) :
    s ^ 4 ≤ n * (n * s + s ^ 2) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hc1 : ∑ j, (α j ^ 2 - α j) ≤ n * s := by
    have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
      (f := fun j => α j ^ 2 - α j)
    simp only [Finset.card_univ, Fintype.card_fin] at hcs
    have hsq : (∑ j, (α j ^ 2 - α j)) ^ 2 ≤ (n * s) ^ 2 := by
      calc (∑ j, (α j ^ 2 - α j)) ^ 2 ≤ n * ∑ j, (α j ^ 2 - α j) ^ 2 := hcs
        _ ≤ n * (n * s ^ 2) := by gcongr
        _ = (n * s) ^ 2 := by ring
    exact (abs_le_of_sq_le_sq' hsq (mul_nonneg hn0 hs0)).2
  have hα2 : ∑ j, α j ^ 2 ≤ n * s + s ^ 2 := by
    have : ∑ j, (α j ^ 2 - α j) = ∑ j, α j ^ 2 - ∑ j, α j := Finset.sum_sub_distrib _ _
    linarith
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := α)
  simp only [Finset.card_univ, Fintype.card_fin] at hcs
  rw [hsum] at hcs
  calc s ^ 4 = (s ^ 2) ^ 2 := by ring
    _ ≤ n * ∑ j, α j ^ 2 := hcs
    _ ≤ n * (n * s + s ^ 2) := by gcongr

/-- From `s⁴ ≤ n (n s + s²)` with `n ≥ 1`, deduce `s ≤ 2 n^{2/3}`. -/
theorem final_bound (n s : ℝ) (hn1 : 1 ≤ n) (hs_pos : 0 < s)
    (hs4 : s ^ 4 ≤ n * (n * s + s ^ 2)) : s ≤ 2 * n ^ ((2 : ℝ) / 3) := by
  have hn0 : 0 ≤ n := by linarith
  set t : ℝ := n ^ ((2 : ℝ) / 3) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg hn0 _
  have ht3 : t ^ 3 = n ^ 2 := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hn0]
    norm_num
  have ht2 : n ≤ t ^ 2 := by
    by_contra hlt
    push Not at hlt
    have h6 : (t ^ 2) ^ 3 < n ^ 3 := pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
    have : (t ^ 2) ^ 3 = n ^ 4 := by
      calc (t ^ 2) ^ 3 = (t ^ 3) ^ 2 := by ring
        _ = n ^ 4 := by rw [ht3]; ring
    rw [this] at h6
    have : n ^ 3 ≤ n ^ 4 := pow_le_pow_right₀ hn1 (by norm_num)
    linarith
  have hs3 : s ^ 3 ≤ n ^ 2 + n * s := by
    have : s * s ^ 3 ≤ s * (n ^ 2 + n * s) := by nlinarith
    exact le_of_mul_le_mul_left this hs_pos
  by_contra hgt
  push Not at hgt
  have hsq : 4 * n < s ^ 2 := by nlinarith
  have hcube : 8 * n ^ 2 < s ^ 3 := by
    have : (2 * t) ^ 3 < s ^ 3 := pow_lt_pow_left₀ hgt (by positivity) (by norm_num)
    nlinarith
  nlinarith

end KonyaginUnitVectorsProof

open KonyaginUnitVectorsProof in
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (d n : ℕ) (u : Fin n → EuclideanSpace ℝ (Fin d)),
      (∀ i, ‖u i‖ = 1) →
      (∀ i j k : Fin n, i ≠ j → j ≠ k → i ≠ k →
        ⟪u i, u j⟫ = 0 ∨ ⟪u j, u k⟫ = 0 ∨ ⟪u i, u k⟫ = 0) →
      ‖∑ i, u i‖ ≤ C * (n : ℝ) ^ ((2 : ℝ) / 3) := by
  refine ⟨2, by norm_num, ?_⟩
  intro d n u hu htri
  have hs0 : 0 ≤ ‖∑ i, u i‖ := norm_nonneg _
  have hsum : ∑ j, ⟪u j, ∑ i, u i⟫ = ‖∑ i, u i‖ ^ 2 := by
    rw [← sum_inner, real_inner_self_eq_norm_sq]
  have hc2 : ∑ j, (⟪u j, ∑ i, u i⟫ ^ 2 - ⟪u j, ∑ i, u i⟫) ^ 2 ≤ n * ‖∑ i, u i‖ ^ 2 := by
    refine le_trans ?_ (deg_weighted_le u hu htri (∑ i, u i))
    refine Finset.sum_le_sum (fun j _ => ?_)
    have hb := nbr_sum_sq_le u hu htri j
    have he := inner_sum_eq u hu j
    have : (⟪u j, ∑ i, u i⟫ ^ 2 - ⟪u j, ∑ i, u i⟫) ^ 2 =
        ⟪u j, ∑ i, u i⟫ ^ 2 * (∑ k ∈ nbr u j, ⟪u j, u k⟫) ^ 2 := by
      rw [he]; ring
    rw [this, mul_comm (((nbr u j).card : ℝ))]
    exact mul_le_mul_of_nonneg_left hb (sq_nonneg _)
  have hs4 := quartic_bound (fun j => ⟪u j, ∑ i, u i⟫) _ hs0 hsum hc2
  rcases eq_or_lt_of_le hs0 with hs_eq | hs_pos
  · rw [← hs_eq]; positivity
  have hn1 : (1 : ℝ) ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp at hs_pos
    · exact_mod_cast h
  exact final_bound n _ hn1 hs_pos hs4
