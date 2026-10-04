import Mathlib
import Definitions.Def_TheoryOfGames_Utility_UtilitySystem
import Definitions.Def_TheoryOfGames_Utility_IsNumericalUtility

open TheoryOfGames.Utility

namespace VNMProof

variable {U : Type*} (S : UtilitySystem U)

/-! ### Order basics -/

theorem irrefl (u : U) : ¬ S.gt u u := by
  rcases S.complete u u with h | h | h
  · exact h.2.1
  · exact absurd rfl h.2.1
  · exact absurd rfl h.2.1

theorem asymm {u v : U} (h : S.gt u v) : ¬ S.gt v u := by
  rcases S.complete u v with h' | h' | h'
  · exact h'.2.2
  · exact h'.2.2
  · exact absurd h h'.2.2

theorem ne_of_gt' {u v : U} (h : S.gt u v) : u ≠ v := by
  rintro rfl; exact irrefl S u h

theorem trich (u v : U) : u = v ∨ S.gt u v ∨ S.gt v u := by
  rcases S.complete u v with h | h | h
  · exact Or.inl h.1
  · exact Or.inr (Or.inl h.1)
  · exact Or.inr (Or.inr h.1)

/-! ### Weights -/

theorem mix_congr {α β : OpenUnit} (h : (α : ℝ) = (β : ℝ)) (u v : U) :
    S.mix α u v = S.mix β u v := by
  rw [Subtype.ext h]

theorem mix_comm' (α : OpenUnit) (u v : U) (β : OpenUnit) (hβ : (β : ℝ) = 1 - α) :
    S.mix α u v = S.mix β v u := by
  rw [S.mix_comm]; exact mix_congr S (by simp [OpenUnit.oneSub, hβ]) v u

theorem mix_mix' (α β γ : OpenUnit) (hγ : (γ : ℝ) = α * β) (u v : U) :
    S.mix α (S.mix β u v) v = S.mix γ u v := by
  rw [S.mix_mix]; exact mix_congr S (by simp [OpenUnit.mul, hγ]) u v

/-- `mix t x (mix μ x y) = mix (t + μ - tμ) x y`. -/
theorem mix_mix_left (t μ ν : OpenUnit) (hν : (ν : ℝ) = t + μ - t * μ) (x y : U) :
    S.mix t x (S.mix μ x y) = S.mix ν x y := by
  obtain ⟨t0, t1⟩ := t.2
  obtain ⟨μ0, μ1⟩ := μ.2
  have h1 : S.mix t x (S.mix μ x y) = S.mix (OpenUnit.oneSub t) (S.mix μ x y) x :=
    S.mix_comm _ _ _
  have h2 : S.mix μ x y = S.mix (OpenUnit.oneSub μ) y x := S.mix_comm _ _ _
  rw [h1, h2]
  let p : OpenUnit := ⟨(1 - t) * (1 - μ), by
    constructor
    · exact mul_pos (by linarith) (by linarith)
    · nlinarith⟩
  rw [mix_mix' S _ _ p (by simp [OpenUnit.oneSub, p]) y x]
  exact mix_comm' S p y x ν (by simp [p, hν]; ring)

/-! ### `mix α u u = u` -/

theorem mix_self_aux (u : U) (R : U → U → Prop) (hirr : ∀ x, ¬ R x x)
    (m : ℝ → U) (hsym : ∀ γ, m γ = m (1 - γ))
    (hstep : ∀ β, 0 < β → β < 1 → R (m β) u → ∀ γ, 0 < γ → γ < β → R (m β) (m γ) ∧ R (m γ) u)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) : ¬ R (m β) u := by
  have big : ∀ β, 1 / 2 < β → β < 1 → ¬ R (m β) u := by
    intro β h1 h2 hR
    have := (hstep β (by linarith) h2 hR (1 - β) (by linarith) (by linarith)).1
    rw [← hsym β] at this
    exact hirr _ this
  intro hR
  by_cases hb : 1 / 2 < β
  · exact big β hb hβ1 hR
  · push Not at hb
    have h2 := (hstep β hβ0 hβ1 hR (β / 2) (by linarith) (by linarith)).2
    rw [hsym] at h2
    exact big (1 - β / 2) (by linarith) (by linarith) h2

theorem mix_self (α : OpenUnit) (u : U) : S.mix α u u = u := by
  classical
  let m : ℝ → U := fun γ => if h : 0 < γ ∧ γ < 1 then S.mix ⟨γ, h.1, h.2⟩ u u else u
  have hm : ∀ (γ : ℝ) (h0 : 0 < γ) (h1 : γ < 1), m γ = S.mix ⟨γ, h0, h1⟩ u u := by
    intro γ h0 h1; simp [m, h0, h1]
  have hsym : ∀ γ, m γ = m (1 - γ) := by
    intro γ
    by_cases h : 0 < γ ∧ γ < 1
    · rw [hm γ h.1 h.2, hm (1 - γ) (by linarith [h.2]) (by linarith [h.1])]
      exact mix_comm' S _ u u _ rfl
    · have h' : ¬ (0 < 1 - γ ∧ 1 - γ < 1) := by
        rintro ⟨h1, h2⟩; exact h ⟨by linarith, by linarith⟩
      show (if h : 0 < γ ∧ γ < 1 then _ else u) = (if h : 0 < 1 - γ ∧ 1 - γ < 1 then _ else u)
      rw [dif_neg h, dif_neg h']
  -- mixing `m β` with `u`
  have hmix : ∀ (t : OpenUnit) (β : ℝ) (h0 : 0 < β) (h1 : β < 1),
      S.mix t (m β) u = m (t * β) := by
    intro t β h0 h1
    obtain ⟨t0, t1⟩ := t.2
    rw [hm β h0 h1, hm (t * β) (mul_pos t0 h0) (by nlinarith)]
    exact mix_mix' S _ _ _ rfl u u
  have hmix' : ∀ (t : OpenUnit) (β : ℝ) (h0 : 0 < β) (h1 : β < 1),
      S.mix t u (m β) = m ((1 - t) * β) := by
    intro t β h0 h1
    rw [S.mix_comm, hmix _ β h0 h1]
    rfl
  have hstep_gt : ∀ β, 0 < β → β < 1 → S.gt (m β) u → ∀ γ, 0 < γ → γ < β →
      S.gt (m β) (m γ) ∧ S.gt (m γ) u := by
    intro β h0 h1 hR γ g0 g1
    constructor
    · have := S.mix_lt_of_gt ⟨γ / β, div_pos g0 h0, (div_lt_one h0).2 g1⟩ (m β) u hR
      rwa [hmix _ β h0 h1, show (γ / β) * β = γ by field_simp] at this
    · have := S.lt_mix_of_lt ⟨1 - γ / β, by
          have : γ / β < 1 := (div_lt_one h0).2 g1
          linarith, by
          have : 0 < γ / β := div_pos g0 h0
          linarith⟩ u (m β) hR
      rwa [hmix' _ β h0 h1, show (1 - (1 - γ / β)) * β = γ by field_simp; ring] at this
  have hstep_lt : ∀ β, 0 < β → β < 1 → S.gt u (m β) → ∀ γ, 0 < γ → γ < β →
      S.gt (m γ) (m β) ∧ S.gt u (m γ) := by
    intro β h0 h1 hR γ g0 g1
    constructor
    · have := S.lt_mix_of_lt ⟨γ / β, div_pos g0 h0, (div_lt_one h0).2 g1⟩ (m β) u hR
      rwa [hmix _ β h0 h1, show (γ / β) * β = γ by field_simp] at this
    · have := S.mix_lt_of_gt ⟨1 - γ / β, by
          have : γ / β < 1 := (div_lt_one h0).2 g1
          linarith, by
          have : 0 < γ / β := div_pos g0 h0
          linarith⟩ u (m β) hR
      rwa [hmix' _ β h0 h1, show (1 - (1 - γ / β)) * β = γ by field_simp; ring] at this
  obtain ⟨a0, a1⟩ := α.2
  have h1 := mix_self_aux u S.gt (irrefl S) m hsym hstep_gt α a0 a1
  have h2 := mix_self_aux u (fun x y => S.gt y x) (irrefl S) m hsym
    (fun β h0 h1 hR γ g0 g1 => (hstep_lt β h0 h1 hR γ g0 g1)) α a0 a1
  have hα : m α = S.mix α u u := hm α a0 a1
  rw [← hα]
  rcases trich S (m α) u with h | h | h
  · exact h
  · exact absurd h h1
  · exact absurd h h2

/-! ### Points on a segment -/

/-- `P c d α` is the point `α d + (1 - α) c` for `0 ≤ α ≤ 1`. -/
noncomputable def P (c d : U) (α : ℝ) : U :=
  if h : 0 < α ∧ α < 1 then S.mix ⟨α, h.1, h.2⟩ d c else if α ≤ 0 then c else d

theorem P_of (c d : U) (α : ℝ) (h0 : 0 < α) (h1 : α < 1) :
    P S c d α = S.mix ⟨α, h0, h1⟩ d c := by
  simp [P, h0, h1]

theorem P_zero (c d : U) : P S c d 0 = c := by simp [P]

theorem P_one (c d : U) : P S c d 1 = d := by simp [P]

/-- (K1) Mixing a segment point with the endpoint `c`. -/
theorem mix_P_c (c d : U) (t : OpenUnit) (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    S.mix t (P S c d α) c = P S c d (t * α) := by
  obtain ⟨t0, t1⟩ := t.2
  rcases eq_or_lt_of_le h0 with h | h0'
  · subst h; rw [P_zero, mul_zero, P_zero, mix_self]
  rcases eq_or_lt_of_le h1 with h | h1'
  · subst h; rw [P_one, mul_one, P_of S c d t t0 t1]
  rw [P_of S c d α h0' h1', P_of S c d (t * α) (mul_pos t0 h0') (by nlinarith)]
  exact mix_mix' S _ _ _ rfl d c

/-- (K4) The mixture algebra on a segment. -/
theorem mix_P_P (c d : U) (t : OpenUnit) (α β : ℝ) (ha0 : 0 ≤ α) (ha1 : α ≤ 1)
    (hb0 : 0 ≤ β) (hb1 : β ≤ 1) :
    S.mix t (P S c d α) (P S c d β) = P S c d (t * α + (1 - t) * β) := by
  obtain ⟨t0, t1⟩ := t.2
  -- the case `β < α`
  have main : ∀ (t : OpenUnit) (α β : ℝ), 0 ≤ α → α ≤ 1 → 0 ≤ β → β < α →
      S.mix t (P S c d α) (P S c d β) = P S c d (t * α + (1 - t) * β) := by
    intro t α β ha0 ha1 hb0 hba
    obtain ⟨t0, t1⟩ := t.2
    have hα : 0 < α := lt_of_le_of_lt hb0 hba
    rcases eq_or_lt_of_le hb0 with hb | hb
    · subst hb
      rw [P_zero, mix_P_c S c d t α ha0 ha1]; ring_nf
    · let μ : OpenUnit := ⟨β / α, div_pos hb hα, (div_lt_one hα).2 hba⟩
      have hPβ : P S c d β = S.mix μ (P S c d α) c := by
        rw [mix_P_c S c d μ α ha0 ha1]; congr 1; simp [μ]; field_simp
      have hμ0 : 0 < β / α := div_pos hb hα
      have hμ1 : β / α < 1 := (div_lt_one hα).2 hba
      let ν : OpenUnit := ⟨t + β / α - t * (β / α), by nlinarith, by nlinarith⟩
      rw [hPβ, mix_mix_left S t μ ν rfl, mix_P_c S c d ν α ha0 ha1]
      congr 1; simp [ν]; field_simp; ring
  rcases lt_trichotomy β α with h | h | h
  · exact main t α β ha0 ha1 hb0 h
  · subst h; rw [mix_self]; congr 1; ring
  · rw [S.mix_comm, main _ β α hb0 hb1 ha0 h]
    congr 1; simp [OpenUnit.oneSub]; ring

variable {S}

/-- On a nondegenerate segment, points strictly increase with the weight. -/
theorem P_gt_c {c d : U} (hcd : S.gt d c) (β : ℝ) (h0 : 0 < β) (h1 : β ≤ 1) :
    S.gt (P S c d β) c := by
  rcases eq_or_lt_of_le h1 with h | h1'
  · subst h; rw [P_one]; exact hcd
  rw [P_of S c d β h0 h1', S.mix_comm]
  exact S.lt_mix_of_lt _ c d hcd

theorem P_strictMono {c d : U} (hcd : S.gt d c) {α β : ℝ} (ha0 : 0 ≤ α) (hab : α < β)
    (hb1 : β ≤ 1) : S.gt (P S c d β) (P S c d α) := by
  have hb0 : 0 < β := lt_of_le_of_lt ha0 hab
  rcases eq_or_lt_of_le ha0 with h | ha0'
  · subst h; rw [P_zero]; exact P_gt_c hcd β hb0 hb1
  have hPα : P S c d α = S.mix ⟨α / β, div_pos ha0' hb0, (div_lt_one hb0).2 hab⟩ (P S c d β) c := by
    rw [mix_P_c S c d _ β hb0.le hb1]; congr 1; simp; field_simp
  rw [hPα]
  exact S.mix_lt_of_gt _ _ _ (P_gt_c hcd β hb0 hb1)

theorem P_inj {c d : U} (hcd : S.gt d c) {α β : ℝ} (ha0 : 0 ≤ α) (ha1 : α ≤ 1)
    (hb0 : 0 ≤ β) (hb1 : β ≤ 1) (h : P S c d α = P S c d β) : α = β := by
  rcases lt_trichotomy α β with hab | hab | hab
  · have := P_strictMono hcd ha0 hab hb1
    rw [h] at this; exact absurd this (irrefl S _)
  · exact hab
  · have := P_strictMono hcd hb0 hab ha1
    rw [h] at this; exact absurd this (irrefl S _)

/-- `x ≼ y`. -/
def le' (S : UtilitySystem U) (x y : U) : Prop := x = y ∨ S.gt y x

/-- Every point between `c` and `d` lies on the segment. -/
theorem P_surj {c d : U} (hcd : S.gt d c) {w : U} (hcw : le' S c w) (hwd : le' S w d) :
    ∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 ∧ P S c d α = w := by
  rcases hcw with rfl | hcw
  · exact ⟨0, le_refl _, zero_le_one, P_zero S _ _⟩
  rcases hwd with rfl | hwd
  · exact ⟨1, zero_le_one, le_refl _, P_one S _ _⟩
  set A : Set ℝ := {α | 0 ≤ α ∧ α ≤ 1 ∧ S.gt w (P S c d α)} with hA
  have h0A : (0 : ℝ) ∈ A := ⟨le_refl _, zero_le_one, by rw [P_zero]; exact hcw⟩
  have hbdd : BddAbove A := ⟨1, fun x hx => hx.2.1⟩
  set s := sSup A with hs
  have hs0 : 0 ≤ s := le_csSup hbdd h0A
  have hs1 : s ≤ 1 := csSup_le ⟨0, h0A⟩ (fun x hx => hx.2.1)
  refine ⟨s, hs0, hs1, ?_⟩
  rcases trich S (P S c d s) w with h | h | h
  · exact h
  · -- `P s ≻ w`: push a little to the left
    exfalso
    have hs0' : 0 < s := by
      rcases eq_or_lt_of_le hs0 with e | e
      · rw [← e, P_zero] at h; exact absurd hcw (asymm S h)
      · exact e
    obtain ⟨lam, hlam⟩ := S.exists_mix_gt (P S c d s) c w h hcw
    obtain ⟨l0, l1⟩ := lam.2
    rw [mix_P_c S c d lam s hs0 hs1] at hlam
    have hub : ∀ x ∈ A, x ≤ lam * s := by
      intro x hx
      by_contra hlt
      push Not at hlt
      have h1 := P_strictMono hcd (by nlinarith) hlt hx.2.1
      exact asymm S hx.2.2 (S.trans _ _ _ h1 hlam)
    have := csSup_le ⟨0, h0A⟩ hub
    nlinarith

  · -- `w ≻ P s`: push a little to the right
    exfalso
    have hs1' : s < 1 := by
      rcases eq_or_lt_of_le hs1 with e | e
      · rw [e, P_one] at h; exact absurd hwd (asymm S h)
      · exact e
    obtain ⟨lam, hlam⟩ := S.exists_mix_lt (P S c d s) d w h hwd
    obtain ⟨l0, l1⟩ := lam.2
    have hmx : S.mix lam (P S c d s) d = P S c d (lam * s + (1 - lam) * 1) := by
      rw [← mix_P_P S c d lam s 1 hs0 hs1 zero_le_one (le_refl _), P_one]
    rw [hmx] at hlam
    have hmem : lam * s + (1 - lam) * 1 ∈ A :=
      ⟨by nlinarith, by nlinarith, hlam⟩
    have := le_csSup hbdd hmem
    nlinarith
/-! ### Coordinates on a segment -/

theorem le'_refl (x : U) : le' S x x := Or.inl rfl

theorem le'_of_gt {x y : U} (h : S.gt y x) : le' S x y := Or.inr h

theorem gt_of_le'_of_gt {x y z : U} (h1 : le' S x y) (h2 : S.gt z y) : S.gt z x := by
  rcases h1 with rfl | h1
  · exact h2
  · exact S.trans _ _ _ h2 h1

theorem gt_of_gt_of_le' {x y z : U} (h1 : S.gt y x) (h2 : le' S y z) : S.gt z x := by
  rcases h2 with rfl | h2
  · exact h1
  · exact S.trans _ _ _ h2 h1

theorem le'_trans {x y z : U} (h1 : le' S x y) (h2 : le' S y z) : le' S x z := by
  rcases h1 with rfl | h1
  · exact h2
  · exact Or.inr (gt_of_gt_of_le' h1 h2)

theorem le'_P_left {c d : U} (hcd : S.gt d c) {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    le' S c (P S c d α) := by
  rcases eq_or_lt_of_le h0 with h | h
  · subst h; rw [P_zero]; exact le'_refl c
  · exact Or.inr (P_gt_c hcd α h h1)

theorem le'_P_right {c d : U} (hcd : S.gt d c) {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    le' S (P S c d α) d := by
  rcases eq_or_lt_of_le h1 with h | h
  · subst h; rw [P_one]; exact le'_refl d
  · have := P_strictMono hcd h0 h (le_refl 1)
    rw [P_one] at this
    exact Or.inr this

variable (S)

/-- The coordinate of `w` on the segment from `c` to `d`. -/
noncomputable def F (c d w : U) : ℝ := by
  classical exact if h : ∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 ∧ P S c d α = w then Classical.choose h else 0

variable {S}

theorem F_spec {c d : U} (hcd : S.gt d c) {w : U} (hcw : le' S c w) (hwd : le' S w d) :
    0 ≤ F S c d w ∧ F S c d w ≤ 1 ∧ P S c d (F S c d w) = w := by
  have h := P_surj hcd hcw hwd
  unfold F
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem F_P {c d : U} (hcd : S.gt d c) {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    F S c d (P S c d α) = α := by
  obtain ⟨f0, f1, hf⟩ := F_spec hcd (le'_P_left hcd h0 h1) (le'_P_right hcd h0 h1)
  exact P_inj hcd f0 f1 h0 h1 hf

theorem F_lt {c d : U} (hcd : S.gt d c) {y z : U} (hcy : le' S c y) (hyd : le' S y d)
    (hcz : le' S c z) (hzd : le' S z d) (hyz : S.gt z y) : F S c d y < F S c d z := by
  obtain ⟨y0, y1, hy⟩ := F_spec hcd hcy hyd
  obtain ⟨z0, z1, hz⟩ := F_spec hcd hcz hzd
  by_contra hle
  push Not at hle
  rcases eq_or_lt_of_le hle with e | e
  · rw [← hy, ← hz, e] at hyz; exact irrefl S _ hyz
  · have := P_strictMono hcd z0 e y1
    rw [hy, hz] at this
    exact asymm S hyz this

/-- A segment inside a segment is an affine reparametrization. -/
theorem P_sub (c d : U) {α' β' t : ℝ} (ha0 : 0 ≤ α') (ha1 : α' ≤ 1) (hb0 : 0 ≤ β')
    (hb1 : β' ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    P S (P S c d α') (P S c d β') t = P S c d (α' + t * (β' - α')) := by
  rcases eq_or_lt_of_le ht0 with h | ht0'
  · subst h; rw [P_zero]; congr 1; ring
  rcases eq_or_lt_of_le ht1 with h | ht1'
  · subst h; rw [P_one]; congr 1; ring
  rw [P_of S _ _ t ht0' ht1', mix_P_P S c d _ β' α' hb0 hb1 ha0 ha1]
  congr 1; simp; ring

/-- The normalized coordinate: `a ↦ 0`, `b ↦ 1`. -/
noncomputable def G (S : UtilitySystem U) (a b c d w : U) : ℝ :=
  (F S c d w - F S c d a) / (F S c d b - F S c d a)

theorem G_consistent {a b c d c' d' x : U} (hab : S.gt b a) (hcd : S.gt d c)
    (hcc' : le' S c c') (hd'd : le' S d' d) (hc'd' : S.gt d' c')
    (hc'a : le' S c' a) (hbd' : le' S b d') (hc'x : le' S c' x) (hxd' : le' S x d') :
    G S a b c d x = G S a b c' d' x := by
  have hc'd : le' S c' d := le'_trans (le'_of_gt hc'd') hd'd
  have hcd' : le' S c d' := le'_trans hcc' (le'_of_gt hc'd')
  obtain ⟨a0, a1, ha⟩ := F_spec hcd hcc' hc'd
  obtain ⟨b0, b1, hb⟩ := F_spec hcd hcd' hd'd
  set α' := F S c d c'
  set β' := F S c d d'
  have hαβ : α' < β' := F_lt hcd hcc' hc'd hcd' hd'd hc'd'
  have key : ∀ y, le' S c' y → le' S y d' → F S c d y = α' + F S c' d' y * (β' - α') := by
    intro y hc'y hyd'
    obtain ⟨t0, t1, ht⟩ := F_spec hc'd' hc'y hyd'
    have e1 := P_sub (S := S) c d a0 a1 b0 b1 t0 t1
    rw [ha, hb, ht] at e1
    calc F S c d y = F S c d (P S c d (α' + F S c' d' y * (β' - α'))) := by
          congr 1
      _ = α' + F S c' d' y * (β' - α') := F_P hcd (by nlinarith) (by nlinarith)
  have hxa := key a hc'a (le'_trans (le'_of_gt hab) hbd')
  have hxb := key b (le'_trans hc'a (le'_of_gt hab)) hbd'
  have hxx := key x hc'x hxd'
  have hab' : F S c' d' a < F S c' d' b :=
    F_lt hc'd' hc'a (le'_trans (le'_of_gt hab) hbd') (le'_trans hc'a (le'_of_gt hab)) hbd' hab
  unfold G
  rw [hxa, hxb, hxx]
  have hne : F S c' d' b - F S c' d' a ≠ 0 := by linarith
  have hne' : β' - α' ≠ 0 := by linarith
  rw [show α' + F S c' d' x * (β' - α') - (α' + F S c' d' a * (β' - α')) =
      (F S c' d' x - F S c' d' a) * (β' - α') by ring,
    show α' + F S c' d' b * (β' - α') - (α' + F S c' d' a * (β' - α')) =
      (F S c' d' b - F S c' d' a) * (β' - α') by ring,
    mul_div_mul_right _ _ hne']

/-! ### Minimum and maximum of two utilities -/

variable (S)

noncomputable def lo (x y : U) : U := by
  classical exact if S.gt x y then y else x

noncomputable def hi (x y : U) : U := by
  classical exact if S.gt x y then x else y

variable {S}

theorem lo_le_left (x y : U) : le' S (lo S x y) x := by
  classical
  unfold lo
  split_ifs with h
  · exact Or.inr h
  · exact le'_refl x

theorem lo_le_right (x y : U) : le' S (lo S x y) y := by
  classical
  unfold lo
  split_ifs with h
  · exact le'_refl y
  · rcases trich S x y with e | e | e
    · rw [e]; exact le'_refl y
    · exact absurd e h
    · exact Or.inr e

theorem le_hi_left (x y : U) : le' S x (hi S x y) := by
  classical
  unfold hi
  split_ifs with h
  · exact le'_refl x
  · rcases trich S x y with e | e | e
    · rw [e]; exact le'_refl y
    · exact absurd e h
    · exact Or.inr e

theorem le_hi_right (x y : U) : le' S y (hi S x y) := by
  classical
  unfold hi
  split_ifs with h
  · exact Or.inr h
  · exact le'_refl y

theorem le_lo {c x y : U} (hx : le' S c x) (hy : le' S c y) : le' S c (lo S x y) := by
  classical
  unfold lo; split_ifs <;> assumption

theorem hi_le {d x y : U} (hx : le' S x d) (hy : le' S y d) : le' S (hi S x y) d := by
  classical
  unfold hi; split_ifs <;> assumption

/-! ### The utility function -/

variable (S)

/-- The numerical utility normalized by `v a = 0`, `v b = 1`. -/
noncomputable def V (a b w : U) : ℝ := G S a b (lo S a w) (hi S b w) w

variable {S}

theorem V_eq_G {a b c d x : U} (hab : S.gt b a) (hca : le' S c a) (hcx : le' S c x)
    (hbd : le' S b d) (hxd : le' S x d) :
    V S a b x = G S a b c d x := by
  have hc'd' : S.gt (hi S b x) (lo S a x) :=
    gt_of_le'_of_gt (lo_le_left a x) (gt_of_gt_of_le' hab (le_hi_left b x))
  have hcd : S.gt d c := gt_of_le'_of_gt hca (gt_of_gt_of_le' hab hbd)
  unfold V
  exact (G_consistent hab hcd (le_lo hca hcx) (hi_le hbd hxd) hc'd' (lo_le_left a x)
    (le_hi_left b x) (lo_le_right a x) (le_hi_right b x)).symm

theorem V_isNumericalUtility {a b : U} (hab : S.gt b a) : IsNumericalUtility S (V S a b) := by
  -- a common segment containing `a, b, u, w`
  have common : ∀ u w : U, ∃ c d : U, S.gt d c ∧ le' S c a ∧ le' S c u ∧ le' S c w ∧
      le' S b d ∧ le' S u d ∧ le' S w d := by
    intro u w
    refine ⟨lo S (lo S a u) w, hi S (hi S b u) w, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact gt_of_le'_of_gt (le'_trans (lo_le_left _ _) (lo_le_left _ _))
        (gt_of_gt_of_le' hab (le'_trans (le_hi_left b u) (le_hi_left _ _)))
    · exact le'_trans (lo_le_left _ _) (lo_le_left _ _)
    · exact le'_trans (lo_le_left _ _) (lo_le_right _ _)
    · exact lo_le_right _ _
    · exact le'_trans (le_hi_left b u) (le_hi_left _ _)
    · exact le'_trans (le_hi_right b u) (le_hi_left _ _)
    · exact le_hi_right _ _
  have hca_b : ∀ c d : U, le' S c a → le' S b d → le' S c b ∧ le' S a d := fun c d h1 h2 =>
    ⟨le'_trans h1 (le'_of_gt hab), le'_trans (le'_of_gt hab) h2⟩
  constructor
  · intro u w huw
    obtain ⟨c, d, hcd, hca, hcu, hcw, hbd, hud, hwd⟩ := common u w
    obtain ⟨hcb, had⟩ := hca_b c d hca hbd
    rw [V_eq_G hab hca hcu hbd hud, V_eq_G hab hca hcw hbd hwd]
    unfold G
    have hFab := F_lt hcd hca had hcb hbd hab
    have hFwu := F_lt hcd hcw hwd hcu hud huw
    exact div_lt_div_of_pos_right (by linarith) (by linarith)
  · intro γ u w
    obtain ⟨c, d, hcd, hca, hcu, hcw, hbd, hud, hwd⟩ := common u w
    obtain ⟨hcb, had⟩ := hca_b c d hca hbd
    obtain ⟨u0, u1, hu⟩ := F_spec hcd hcu hud
    obtain ⟨w0, w1, hw⟩ := F_spec hcd hcw hwd
    obtain ⟨g0, g1⟩ := γ.2
    set t : ℝ := 1 - (γ : ℝ)
    have hm : S.cmb γ u w = P S c d (t * F S c d u + (1 - t) * F S c d w) := by
      unfold UtilitySystem.cmb
      conv_lhs => rw [← hu, ← hw]
      rw [mix_P_P S c d _ _ _ u0 u1 w0 w1]
      rfl
    have hm0 : 0 ≤ t * F S c d u + (1 - t) * F S c d w := by
      have : 0 ≤ t := by simp [t]; linarith
      have : 0 ≤ 1 - t := by simp [t]; linarith
      positivity
    have hm1 : t * F S c d u + (1 - t) * F S c d w ≤ 1 := by
      have : 0 ≤ t := by simp [t]; linarith
      have : 0 ≤ 1 - t := by simp [t]; linarith
      nlinarith
    have hcm : le' S c (S.cmb γ u w) := by rw [hm]; exact le'_P_left hcd hm0 hm1
    have hmd : le' S (S.cmb γ u w) d := by rw [hm]; exact le'_P_right hcd hm0 hm1
    rw [V_eq_G hab hca hcm hbd hmd, V_eq_G hab hca hcu hbd hud, V_eq_G hab hca hcw hbd hwd]
    unfold G
    rw [hm, F_P hcd hm0 hm1]
    have hFab := F_lt hcd hca had hcb hbd hab
    have hne : F S c d b - F S c d a ≠ 0 := by linarith
    simp only [t]
    field_simp
    try ring

/-! ### Uniqueness -/

theorem nu_P {nu : U → ℝ} (hnu : IsNumericalUtility S nu) (c d : U) {α : ℝ} (h0 : 0 ≤ α)
    (h1 : α ≤ 1) : nu (P S c d α) = α * nu d + (1 - α) * nu c := by
  rcases eq_or_lt_of_le h0 with h | h0'
  · subst h; rw [P_zero]; ring
  rcases eq_or_lt_of_le h1 with h | h1'
  · subst h; rw [P_one]; ring
  rw [P_of S c d α h0' h1']
  have := hnu.2 ⟨1 - α, by linarith, by linarith⟩ d c
  unfold UtilitySystem.cmb at this
  rw [mix_congr S (β := ⟨α, h0', h1'⟩) (by simp [OpenUnit.oneSub]) d c] at this
  rw [this]; simp

end VNMProof

open VNMProof in
theorem solution {U : Type*} (S : UtilitySystem U) :
    (∃ v : U → ℝ, IsNumericalUtility S v) ∧
      ∀ v v' : U → ℝ, IsNumericalUtility S v → IsNumericalUtility S v' →
        ∃ ω₀ ω₁ : ℝ, 0 < ω₀ ∧ ∀ w : U, v' w = ω₀ * v w + ω₁ := by
  by_cases hpair : ∃ a b : U, S.gt b a
  · obtain ⟨a, b, hab⟩ := hpair
    refine ⟨⟨V S a b, V_isNumericalUtility hab⟩, ?_⟩
    intro v v' hv hv'
    have hvab : v a < v b := hv.1 b a hab
    set ω₀ := (v' b - v' a) / (v b - v a) with hω₀
    have hv'ab : v' a < v' b := hv'.1 b a hab
    refine ⟨ω₀, v' a - ω₀ * v a, div_pos (by linarith) (by linarith), ?_⟩
    intro w
    -- `h x = v' x - ω₀ v x - ω₁` is affine on segments and vanishes at `a` and `b`
    set h : U → ℝ := fun x => v' x - ω₀ * v x - (v' a - ω₀ * v a) with hh
    have hP : ∀ (c d : U) (α : ℝ), 0 ≤ α → α ≤ 1 →
        h (P S c d α) = α * h d + (1 - α) * h c := by
      intro c d α h0 h1
      simp only [hh, nu_P hv c d h0 h1, nu_P hv' c d h0 h1]; ring
    have ha : h a = 0 := by simp [hh]
    have hb : h b = 0 := by
      have hω : ω₀ * (v b - v a) = v' b - v' a := div_mul_cancel₀ _ (by linarith)
      simp only [hh]
      linear_combination (-1 : ℝ) * hω
    suffices h w = 0 by simp only [hh] at this; linarith
    rcases trich S w b with e | e | e
    · rw [e, hb]
    · -- `a ≺ b ≺ w`
      obtain ⟨β, b0, b1, hβ⟩ := P_surj (S.trans _ _ _ e hab) (le'_of_gt hab) (le'_of_gt e)
      have := hP a w β b0 b1
      rw [hβ, hb, ha] at this
      have hβ0 : β ≠ 0 := by
        rintro rfl; rw [P_zero] at hβ; exact ne_of_gt' S hab hβ.symm
      have : β * h w = 0 := by linarith
      rcases mul_eq_zero.1 this with h1 | h1
      · exact absurd h1 hβ0
      · exact h1
    · rcases trich S w a with e' | e' | e'
      · rw [e', ha]
      · -- `a ≺ w ≺ b`
        obtain ⟨α, a0, a1, hα⟩ := P_surj hab (le'_of_gt e') (le'_of_gt e)
        have := hP a b α a0 a1
        rw [hα, ha, hb] at this
        linarith
      · -- `w ≺ a ≺ b`
        obtain ⟨β, b0, b1, hβ⟩ := P_surj (S.trans _ _ _ hab e') (le'_of_gt e') (le'_of_gt hab)
        have := hP w b β b0 b1
        rw [hβ, hb, ha] at this
        have hβ1 : β ≠ 1 := by
          rintro rfl; rw [P_one] at hβ; exact ne_of_gt' S hab hβ
        have : (1 - β) * h w = 0 := by linarith
        rcases mul_eq_zero.1 this with h1 | h1
        · exact absurd (by linarith : β = 1) hβ1
        · exact h1
  · push Not at hpair
    have hall : ∀ x y : U, x = y := by
      intro x y
      rcases trich S x y with e | e | e
      · exact e
      · exact absurd e (hpair y x)
      · exact absurd e (hpair x y)
    refine ⟨⟨fun _ => 0, fun u w h => absurd h (hpair w u), fun _ _ _ => by ring⟩, ?_⟩
    intro v v' _ _
    by_cases hne : Nonempty U
    · obtain ⟨w₀⟩ := hne
      refine ⟨1, v' w₀ - v w₀, one_pos, fun w => ?_⟩
      rw [hall w w₀]; ring
    · exact ⟨1, 0, one_pos, fun w => absurd ⟨w⟩ hne⟩
