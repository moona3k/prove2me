import Mathlib
import Definitions.Def_Supermodularity_Cooperative_IsConvexGame
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_CoresConvexGames_Stability_IsStableSet

open Supermodularity.Cooperative CoresConvexGames.Stability

namespace ShapleyCoreProof

variable {n : ℕ} {f : Finset (Fin n) → ℝ}

theorem supermod (hf : IsConvexGame f) (X Y : Finset (Fin n)) :
    f X + f Y ≤ f (X ∪ Y) + f (X ∩ Y) :=
  hf.2 (Set.mem_univ X) (Set.mem_univ Y)

/-- Adding one player `i` to a coalition `U` on which `y` is a core vector of the
subgame, with payoff equal to the marginal contribution `f (U ∪ {i}) - f U`. -/
theorem extend_one (hf : IsConvexGame f) (U : Finset (Fin n)) (i : Fin n) (hi : i ∉ U)
    (y : Fin n → ℝ) (hy1 : ∀ T ⊆ U, f T ≤ ∑ j ∈ T, y j) (hy2 : ∑ j ∈ U, y j = f U) :
    ∃ y' : Fin n → ℝ, (∀ j ∈ U, y' j = y j) ∧
      (∀ T ⊆ insert i U, f T ≤ ∑ j ∈ T, y' j) ∧
      ∑ j ∈ insert i U, y' j = f (insert i U) := by
  refine ⟨Function.update y i (f (insert i U) - f U), ?_, ?_, ?_⟩
  · intro j hj
    have : j ≠ i := fun h => hi (h ▸ hj)
    simp [Function.update_of_ne this]
  · have hsumU : ∀ T ⊆ U, ∑ j ∈ T, Function.update y i (f (insert i U) - f U) j =
        ∑ j ∈ T, y j := by
      intro T hT
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have : j ≠ i := fun h => hi (h ▸ hT hj)
      simp [Function.update_of_ne this]
    intro T hT
    by_cases hiT : i ∈ T
    · have hT' : T.erase i ⊆ U := by
        intro j hj
        rcases Finset.mem_insert.1 (hT (Finset.mem_of_mem_erase hj)) with h | h
        · exact absurd h (Finset.ne_of_mem_erase hj)
        · exact h
      have hunion : T ∪ U = insert i U := by
        ext j; simp only [Finset.mem_union, Finset.mem_insert]
        constructor
        · rintro (h | h)
          · exact Finset.mem_insert.1 (hT h)
          · exact Or.inr h
        · rintro (h | h)
          · exact Or.inl (h ▸ hiT)
          · exact Or.inr h
      have hinter : T ∩ U = T.erase i := by
        ext j; simp only [Finset.mem_inter, Finset.mem_erase]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨fun h => hi (h ▸ h2), h1⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h2, hT' (Finset.mem_erase.2 ⟨h1, h2⟩)⟩
      have hsm := supermod hf T U
      rw [hunion, hinter] at hsm
      rw [← Finset.add_sum_erase T _ hiT, hsumU _ hT', Function.update_self]
      have := hy1 _ hT'
      linarith
    · have hTU : T ⊆ U := by
        intro j hj
        rcases Finset.mem_insert.1 (hT hj) with h | h
        · exact absurd (h ▸ hj) hiT
        · exact h
      rw [hsumU _ hTU]
      exact hy1 T hTU
  · rw [Finset.sum_insert hi, Function.update_self]
    have : ∑ j ∈ U, Function.update y i (f (insert i U) - f U) j = ∑ j ∈ U, y j := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have : j ≠ i := fun h => hi (h ▸ hj)
      simp [Function.update_of_ne this]
    rw [this, hy2]
    ring

/-- A core vector of the subgame on `S` extends to a core vector of the whole game. -/
theorem extend (hf : IsConvexGame f) (S : Finset (Fin n)) (x : Fin n → ℝ)
    (hx1 : ∀ T ⊆ S, f T ≤ ∑ j ∈ T, x j) (hx2 : ∑ j ∈ S, x j = f S) :
    ∃ y : Fin n → ℝ, (∀ j ∈ S, y j = x j) ∧ y ∈ Core Finset.univ f := by
  have key : ∀ D : Finset (Fin n), Disjoint S D → ∃ y : Fin n → ℝ, (∀ j ∈ S, y j = x j) ∧
      (∀ T ⊆ S ∪ D, f T ≤ ∑ j ∈ T, y j) ∧ ∑ j ∈ S ∪ D, y j = f (S ∪ D) := by
    intro D
    induction D using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨x, fun _ _ => rfl, by simpa using hx1, by simpa using hx2⟩
    | insert a D haD ih =>
      intro hdisj
      have hdisj' : Disjoint S D := Finset.disjoint_of_subset_right (Finset.subset_insert _ _) hdisj
      have haS : a ∉ S := fun h => Finset.disjoint_left.1 hdisj h (Finset.mem_insert_self a D)
      obtain ⟨y, hyS, hy1, hy2⟩ := ih hdisj'
      have haU : a ∉ S ∪ D := by
        rw [Finset.mem_union]; rintro (h | h)
        · exact haS h
        · exact haD h
      obtain ⟨y', hy'U, hy'1, hy'2⟩ := extend_one hf (S ∪ D) a haU y hy1 hy2
      refine ⟨y', fun j hj => (hy'U j (Finset.mem_union_left _ hj)).trans (hyS j hj), ?_, ?_⟩
      · rw [Finset.union_insert]; exact hy'1
      · rw [Finset.union_insert]; exact hy'2
  obtain ⟨y, hyS, hy1, hy2⟩ := key (Finset.univ \ S) Finset.disjoint_sdiff
  rw [Finset.union_sdiff_of_subset (Finset.subset_univ S)] at hy1 hy2
  exact ⟨y, hyS, hy2, fun T hT => hy1 T hT⟩

/-- No vector with `c(S) ≤ f S` on a nonempty `S` strictly beats a core vector on `S`. -/
theorem core_undominated (a : Fin n → ℝ) (ha : a ∈ Core Finset.univ f) (c : Fin n → ℝ) :
    ¬ Dominates f c a := by
  rintro ⟨S, hSne, hcS, hlt⟩
  have h1 : ∑ i ∈ S, a i < ∑ i ∈ S, c i := Finset.sum_lt_sum_of_nonempty hSne hlt
  have h2 := ha.2 S (Finset.subset_univ S)
  linarith

/-- Every feasible vector outside the core is dominated by a core vector. -/
theorem exists_core_dominating (hf : IsConvexGame f) (b : Fin n → ℝ) (hb : IsFeasible f b)
    (hbC : b ∉ Core Finset.univ f) : ∃ a ∈ Core Finset.univ f, Dominates f a b := by
  have hex : ∃ S : Finset (Fin n), ∑ i ∈ S, b i < f S := by
    by_contra h
    push Not at h
    exact hbC ⟨le_antisymm hb (h Finset.univ), fun S _ => h S⟩
  obtain ⟨S0, hS0⟩ := hex
  have hS0ne : S0.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp [hf.1] at hS0
  set P : Finset (Finset (Fin n)) := Finset.univ.filter (fun S => S.Nonempty) with hP
  have hS0P : S0 ∈ P := by simp [hP, hS0ne]
  obtain ⟨S, hSP, hmax⟩ := Finset.exists_max_image P
    (fun S => (f S - ∑ i ∈ S, b i) / (S.card : ℝ)) ⟨S0, hS0P⟩
  have hSne : S.Nonempty := by simpa [hP] using hSP
  have hcardpos : ∀ T : Finset (Fin n), T.Nonempty → (0 : ℝ) < T.card := fun T hT => by
    exact_mod_cast hT.card_pos
  set e : ℝ := (f S - ∑ i ∈ S, b i) / (S.card : ℝ) with he
  have he0 : 0 < e := by
    have h1 := hmax S0 hS0P
    have h2 : 0 < (f S0 - ∑ i ∈ S0, b i) / (S0.card : ℝ) :=
      div_pos (by linarith) (hcardpos S0 hS0ne)
    linarith
  set x : Fin n → ℝ := fun j => b j + e with hx
  have hsumx : ∀ T : Finset (Fin n), ∑ j ∈ T, x j = ∑ j ∈ T, b j + T.card * e := by
    intro T
    simp [hx, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have hx1 : ∀ T ⊆ S, f T ≤ ∑ j ∈ T, x j := by
    intro T _
    rw [hsumx]
    rcases Finset.eq_empty_or_nonempty T with hT | hT
    · subst hT; simp [hf.1]
    · have hTP : T ∈ P := by simp [hP, hT]
      have h1 := hmax T hTP
      have h2 : f T - ∑ i ∈ T, b i ≤ T.card * e := by
        rw [div_le_iff₀ (hcardpos T hT)] at h1
        linarith
      linarith
  have hx2 : ∑ j ∈ S, x j = f S := by
    rw [hsumx, he, mul_div_cancel₀ _ (ne_of_gt (hcardpos S hSne))]
    ring
  obtain ⟨a, haS, haC⟩ := extend hf S x hx1 hx2
  refine ⟨a, haC, S, hSne, ?_, ?_⟩
  · rw [Finset.sum_congr rfl haS, hx2]
  · intro i hi
    rw [haS i hi, hx]
    linarith

end ShapleyCoreProof

open ShapleyCoreProof in
theorem solution {n : ℕ} (f : Finset (Fin n) → ℝ) (hf : IsConvexGame f) :
    IsStableSet f (Core Finset.univ f) ∧
      ∀ V : Set (Fin n → ℝ), IsStableSet f V → V = Core Finset.univ f := by
  have hfeas : ∀ a ∈ Core Finset.univ f, IsFeasible f a := fun a ha => le_of_eq ha.1
  have hstable : IsStableSet f (Core Finset.univ f) := by
    refine ⟨hfeas, fun b hb => ⟨?_, ?_⟩⟩
    · rintro hbC ⟨a, _, hdom⟩
      exact core_undominated b hbC a hdom
    · intro hnd
      by_contra hbC
      exact hnd (exists_core_dominating hf b hb hbC)
  refine ⟨hstable, fun V hV => ?_⟩
  have hCV : Core Finset.univ f ⊆ V := by
    intro b hbC
    refine ((hV.2 b (hfeas b hbC)).2 ?_)
    rintro ⟨a, _, hdom⟩
    exact core_undominated b hbC a hdom
  ext b
  constructor
  · intro hbV
    by_contra hbC
    obtain ⟨a, haC, hdom⟩ := exists_core_dominating hf b (hV.1 b hbV) hbC
    exact ((hV.2 b (hV.1 b hbV)).1 hbV) ⟨a, hCV haC, hdom⟩
  · intro hbC
    exact hCV hbC
