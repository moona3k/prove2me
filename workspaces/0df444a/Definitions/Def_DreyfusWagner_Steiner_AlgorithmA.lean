import Mathlib
import Definitions.Def_DreyfusWagner_Steiner_SteinerProblem

namespace DreyfusWagner.Steiner

variable {V : Type*}

/-- The subsets `E` enumerated in lines (10) and (18) of Algorithm A for a node set `D`:
`D[1] ∈ E ∧ E ⊊ D`, where `D[1]` is the first (least) element of `D` in the fixed order of the
nodes (Dreyfus–Wagner 1971, §4, pp. 202–203). Empty when `D` is empty. -/
def splits [LinearOrder V] (D : Finset V) : Finset (Finset V) :=
  if h : D.Nonempty then D.powerset.filter (fun E => D.min' h ∈ E ∧ E ≠ D) else ∅

theorem mem_splits [LinearOrder V] {D E : Finset V} :
    E ∈ splits D ↔ ∃ h : D.Nonempty, E ⊆ D ∧ D.min' h ∈ E ∧ E ≠ D := by
  unfold splits
  split_ifs with h
  · simp [h]
  · simp [h]

theorem card_lt_of_mem_splits [LinearOrder V] {D E : Finset V} (hE : E ∈ splits D) :
    E.card < D.card := by
  obtain ⟨_, hsub, _, hne⟩ := mem_splits.1 hE
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hsub, hne⟩)

theorem card_sdiff_lt_of_mem_splits [LinearOrder V] {D E : Finset V} (hE : E ∈ splits D) :
    (D \ E).card < D.card := by
  obtain ⟨h, _, hmin, _⟩ := mem_splits.1 hE
  refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨Finset.sdiff_subset, ?_⟩)
  intro heq
  rw [Finset.sdiff_eq_self_iff_disjoint] at heq
  exact Finset.disjoint_left.1 heq (D.min'_mem h) hmin

/-- The table `S[D, I]` of Algorithm A (Dreyfus–Wagner 1971, §4, p. 203), computed from a
distance table `d` (the paper's `D(i,j)`), by recursion on `‖D‖`:
* `‖D‖ = 1`, `D = {t}`: `S[{t}, I] = d(t, I)` (lines (1)–(3));
* `‖D‖ ≥ 2`: `S[D, I] = min_J ( d(I, J) + min_{E : D[1] ∈ E ⊊ D} (S[E, J] + S[D − E, J]) )`
  (lines (5)–(14));
* `D = ∅`: `∞` (never used by the algorithm).
Minima over empty index sets are `⊤ = ∞`, as in lines (7) and (9). -/
noncomputable def tableA [Fintype V] [LinearOrder V] (d : V → V → WithTop ℝ) (D : Finset V)
    (I : V) : WithTop ℝ :=
  if _h : D.card ≤ 1 then
    if hne : D.Nonempty then d (D.min' hne) I else ⊤
  else
    Finset.univ.inf fun J => d I J +
      (splits D).attach.inf fun E => tableA d E.1 J + tableA d (D \ E.1) J
termination_by D.card
decreasing_by
  · exact card_lt_of_mem_splits E.2
  · exact card_sdiff_lt_of_mem_splits E.2

/-- Algorithm A of Dreyfus–Wagner (1971, §4, p. 203): with `C = Y − {q}` and `D(i,j)` the
shortest-path length `pathDist G ℓ i j`, the returned value is
`v = min_J ( D(q, J) + min_{E : C[1] ∈ E ⊊ C} (S[E, J] + S[C − E, J]) )` (lines (15)–(20)),
where `S` is the table `tableA` built from `D`. -/
noncomputable def algorithmA [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ℓ : Sym2 V → ℝ) (Y : Finset V) (q : V) : WithTop ℝ :=
  Finset.univ.inf fun J => pathDist G ℓ q J +
    (splits (Y.erase q)).inf fun E =>
      tableA (pathDist G ℓ) E J + tableA (pathDist G ℓ) (Y.erase q \ E) J

end DreyfusWagner.Steiner
