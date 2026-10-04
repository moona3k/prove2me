import Mathlib

namespace DreyfusWagner.Steiner

variable {V : Type*}

/-- Total length `|S| = ∑_{s ∈ S} |s|` of a finite set `S` of arcs, where `ℓ` gives the length
of each arc (Dreyfus–Wagner 1971, §1, p. 195, condition (2)). -/
def arcLength (ℓ : Sym2 V → ℝ) (S : Finset (Sym2 V)) : ℝ :=
  ∑ e ∈ S, ℓ e

/-- The arc set `S` connects the node set `X`: any two members of `X` are joined by a path
composed only of arcs in `S` (Dreyfus–Wagner 1971, §1, p. 195, condition (1)). -/
def Connects (S : Finset (Sym2 V)) (X : Finset V) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, (SimpleGraph.fromEdgeSet (S : Set (Sym2 V))).Reachable x y

/-- `S` is a Steiner path (Steiner tree) connecting `X` in `G` with arc lengths `ℓ`: `S` is a set
of arcs of `G` that connects `X` and has minimum total length among all such arc sets
(Dreyfus–Wagner 1971, §1, pp. 195–196). -/
def IsSteinerTree [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ℓ : Sym2 V → ℝ) (X : Finset V) (S : Finset (Sym2 V)) : Prop :=
  S ⊆ G.edgeFinset ∧ Connects S X ∧
    ∀ S' ⊆ G.edgeFinset, Connects S' X → arcLength ℓ S ≤ arcLength ℓ S'

open Classical in
/-- The length of the Steiner path connecting `X` in `G`: the minimum of `|S|` over all arc sets
`S ⊆ A` connecting `X`, as an element of `WithTop ℝ` (it is `⊤ = ∞` exactly when no arc set of `G`
connects `X`). -/
noncomputable def steinerLength [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ) (X : Finset V) : WithTop ℝ :=
  (G.edgeFinset.powerset.filter (fun S => Connects S X)).inf
    (fun S => ((arcLength ℓ S : ℝ) : WithTop ℝ))

open Classical in
/-- `D(i,j)`: the length of the shortest path in `G` from `i` to `j` (Dreyfus–Wagner 1971, §4,
p. 202), i.e. the minimum of the sum of the arc lengths along a path `i → j` of `G`, as an
element of `WithTop ℝ` (`⊤ = ∞` when there is no such path). Every path of `G` has fewer than
`Fintype.card V` arcs, so the minimum ranges over all paths from `i` to `j`. -/
noncomputable def pathDist [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ℓ : Sym2 V → ℝ) (i j : V) : WithTop ℝ :=
  (Finset.range (Fintype.card V)).inf fun n =>
    ((G.finsetWalkLength n i j).filter (fun p => p.IsPath)).inf
      fun p => (((p.edges.map ℓ).sum : ℝ) : WithTop ℝ)

end DreyfusWagner.Steiner
