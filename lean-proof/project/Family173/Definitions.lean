import OAI.Combinatorics.SecondNeighborhood.PruningDefinitions
import OAI.Combinatorics.SecondNeighborhood.MatchingExchange

namespace Family173

open OAI.SeymourSecondNeighborhood
open Bipartite

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The two argument positions are distinct graph roles, even for equal coordinates. -/
def L0 (r : X → X → Prop) (W Z : Finset (X × X)) (w : W) (z : Z) : Prop :=
  Pruning.LeftCovers r w.val z.val

def B0 (r : X → X → Prop) (W H : Finset (X × X)) (w : W) (h : H) : Prop :=
  w.val.1 = h.val.1 ∧ r h.val.2 w.val.2

def N0 (r : X → X → Prop) (Z C : Finset (X × X)) (z : Z) (c : C) : Prop :=
  Pruning.RightCovers r c.val z.val

noncomputable section

/-- Full published CC target. This is a statement definition, not a proved theorem.
The corners always come from the original R,C. No relation restriction, maximum
input matching, or minimum input cover is assumed. The additive budget expresses
ordinary integer subtraction without natural-number truncation. -/
def CoverConversionStatement (r : X → X → Prop) (R C : Finset (X × X)) : Prop :=
  ∀ W : Finset (X × X), W ⊆ R →
  ∀ α : Finset (↥W × ↥(Pruning.Z r R C)),
    IsMatching (L0 r W (Pruning.Z r R C)) α → leftVertices α = Finset.univ →
  ∀ U : Finset ↥W, ∀ V : Finset ↥(Pruning.H r R C),
    IsVertexCover (B0 r W (Pruning.H r R C)) U V →
    ∃ A : Finset ↥(Pruning.Z r R C), ∃ D : Finset ↥C,
      IsVertexCover (N0 r (Pruning.Z r R C) C) A D ∧
      A.card + D.card + W.card ≤ (Pruning.Z r R C).card + U.card + V.card

theorem additive_budget_iff_integer_budget (a w z b : ℕ) :
    a + w ≤ z + b ↔ (a : ℤ) ≤ (z : ℤ) - (w : ℤ) + (b : ℤ) := by
  omega

omit [Fintype X] in
theorem saturating_matching_card {W Z : Finset (X × X)}
    {α : Finset (↥W × ↥Z)} {E : ↥W → ↥Z → Prop}
    (hα : IsMatching E α) (hSat : leftVertices α = Finset.univ) :
    α.card = W.card := by
  have h := matching_card_leftVertices hα
  rw [hSat] at h
  simpa only [Finset.card_univ, Fintype.card_coe] using h.symm

omit [Fintype X] in
theorem saturating_matching_card_le_right {W Z : Finset (X × X)}
    {α : Finset (↥W × ↥Z)} {E : ↥W → ↥Z → Prop}
    (hα : IsMatching E α) (hSat : leftVertices α = Finset.univ) :
    W.card ≤ Z.card := by
  have h := Finset.card_le_card (Finset.subset_univ (rightVertices α))
  rw [matching_card_rightVertices hα, saturating_matching_card hα hSat] at h
  simpa only [Finset.card_univ, Fintype.card_coe] using h

theorem original_conflict_corners (r : X → X → Prop) (R C W : Finset (X × X))
    (hWR : W ⊆ R) (w : W) (c : C)
    (hpi : r w.val.1 c.val.1) (hsj : r c.val.2 w.val.2) :
    (c.val.1, w.val.2) ∈ Pruning.Z r R C ∧
    (w.val.1, c.val.2) ∈ Pruning.H r R C := by
  exact ⟨Pruning.conflict_corner_mem_Z (hWR w.property) c.property ⟨hpi, hsj⟩,
    Pruning.conflict_corner_mem_H (hWR w.property) c.property ⟨hpi, hsj⟩⟩

theorem cover_forces_original_H_corner (r : X → X → Prop)
    (R C W : Finset (X × X)) (hWR : W ⊆ R)
    (U : Finset ↥W) (V : Finset ↥(Pruning.H r R C))
    (hCover : IsVertexCover (B0 r W (Pruning.H r R C)) U V)
    (w : W) (c : C) (hw : w ∉ U)
    (hpi : r w.val.1 c.val.1) (hsj : r c.val.2 w.val.2) :
    ∃ h ∈ V, h.val = (w.val.1, c.val.2) := by
  let h : ↥(Pruning.H r R C) :=
    ⟨(w.val.1, c.val.2), (original_conflict_corners r R C W hWR w c hpi hsj).2⟩
  have hEdge : B0 r W (Pruning.H r R C) w h := ⟨rfl, hsj⟩
  exact ⟨h, (hCover w h hEdge).resolve_left hw, rfl⟩

end
end Family173
