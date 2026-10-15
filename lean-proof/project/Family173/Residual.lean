import Family173.CoverConversion
import OAI.Combinatorics.SecondNeighborhood.MatchingCover

namespace Family173
open OAI.SeymourSecondNeighborhood
open Bipartite
variable {X : Type*} [Fintype X] [DecidableEq X]

theorem generalized_residual_bound (r : X → X → Prop) (R C W : Finset (X × X))
    (hW : W ⊆ R) (α : Finset (↥W × ↥(Pruning.Z r R C)))
    (hα : IsMatching (L0 r W (Pruning.Z r R C)) α)
    (hSat : leftVertices α = Finset.univ) :
    matchingNumber (N0 r (Pruning.Z r R C) C) + W.card ≤
      (Pruning.Z r R C).card + matchingNumber (B0 r W (Pruning.H r R C)) := by
  classical
  obtain ⟨U,V,hCover,hCard,_,_⟩ := exists_vertexCover_card_eq_of_isMaximumMatching
    (maximumMatching_spec (B0 r W (Pruning.H r R C)))
  obtain ⟨A,D,hN,hBudget⟩ := cover_conversion r R C W hW α hα hSat U V hCover
  have hNbound := matching_card_le_cover_card
    (maximumMatching_spec (N0 r (Pruning.Z r R C) C)).1 hN
  change U.card + V.card = matchingNumber (B0 r W (Pruning.H r R C)) at hCard
  change matchingNumber (N0 r (Pruning.Z r R C) C) ≤ A.card+D.card at hNbound
  omega
end Family173
