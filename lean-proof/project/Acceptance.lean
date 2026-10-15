import Family173

open OAI.SeymourSecondNeighborhood
open OAI.SeymourSecondNeighborhood.Bipartite

/-- Acceptance statement spells out all three incidence relations and the
ordinary integer budget. It does not assume an order, orientation, maximal
input matching, minimum input cover, or the selector laws. -/
theorem exact_published_CC {X : Type*} [Fintype X] [DecidableEq X]
    (r : X → X → Prop) (R C W : Finset (X × X)) (hWR : W ⊆ R)
    (α : Finset (↥W × ↥(Pruning.Z r R C)))
    (hα : IsMatching
      (fun (w : W) (z : Pruning.Z r R C) => w.val.2 = z.val.2 ∧ r w.val.1 z.val.1) α)
    (hSat : leftVertices α = Finset.univ)
    (U : Finset ↥W) (V : Finset ↥(Pruning.H r R C))
    (hKB : IsVertexCover
      (fun (w : W) (h : Pruning.H r R C) => w.val.1 = h.val.1 ∧ r h.val.2 w.val.2) U V) :
    ∃ A : Finset ↥(Pruning.Z r R C), ∃ D : Finset ↥C,
      IsVertexCover
        (fun (z : Pruning.Z r R C) (c : C) => c.val.1 = z.val.1 ∧ r c.val.2 z.val.2) A D ∧
      ((A.card + D.card : ℕ) : ℤ) ≤
        ((Pruning.Z r R C).card : ℤ) - (W.card : ℤ) + ((U.card + V.card : ℕ) : ℤ) := by
  obtain ⟨A, D, hN, hBudget⟩ :=
    Family173.cover_conversion r R C W hWR α hα hSat U V hKB
  refine ⟨A, D, hN, ?_⟩
  exact (Family173.additive_budget_iff_integer_budget
    (A.card + D.card) W.card (Pruning.Z r R C).card (U.card + V.card)).mp (by omega)

#print Family173.cover_conversion
#print exact_published_CC
#print axioms Family173.cover_conversion_of_order
#print axioms Family173.cover_conversion
#print axioms exact_published_CC
