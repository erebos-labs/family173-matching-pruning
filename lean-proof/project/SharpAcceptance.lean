import Family173.CoefficientSharpness
import PruningAcceptance

namespace FinalPruningAudit
open OAI.SeymourSecondNeighborhood
open Bipartite Pruning Family173

/-- All positive published sizes are n=k+1; no finite upper bound on k. -/
theorem exact_arbitrary_size_family (k : ℕ) :
    (Z (Sharp.edge k) (Sharp.R k) (Sharp.C k)).card=1 ∧
    (H (Sharp.edge k) (Sharp.R k) (Sharp.C k)).card=(k+1)*(k+1) ∧
    matchingNumber (B0 (Sharp.edge k) (Sharp.R k) (H (Sharp.edge k) (Sharp.R k) (Sharp.C k)))=k+1 ∧
    matchingNumber (A0 (Sharp.edge k) (H (Sharp.edge k) (Sharp.R k) (Sharp.C k)) (Sharp.C k))=k+1 ∧
    matchingNumber (AugmentedEdge (Sharp.edge k) (Sharp.R k) (Sharp.C k))=(k+1)+1 ∧
    minimumPruningObjective (Sharp.edge k) (Sharp.R k) (Sharp.C k)=((k+1 : ℕ) : ℤ) ∧
    IsOriented (Sharp.edge k) ∧
    (∀ x y z, Sharp.edge k x y → ¬ Sharp.edge k y z) :=
  ⟨Sharp.Z_card k,Sharp.H_card k,Sharp.B_number k,Sharp.A_number k,
    Sharp.Gamma_number k,sharp_minimum_value k,Sharp.oriented k,Sharp.no_two_step k⟩

/-- Exactly the uniform real-coefficient obstruction, including ANY fixed real
additive constant and EVERY admissible pruning of the constructed input. -/
theorem exact_real_coefficient_one_sharpness (c K : ℝ) (hc : c<1) :
    ∃ k : ℕ, ∀ R' C' : Finset (Sharp.X k × Sharp.X k),
      AdmissibleNote (Sharp.edge k) (Sharp.R k) (Sharp.C k) R' C' →
      (((Sharp.R k \ R').card+(Sharp.C k \ C').card : ℕ) : ℝ) >
        c * ((min
          (matchingNumber (B0 (Sharp.edge k) (Sharp.R k) (H (Sharp.edge k) (Sharp.R k) (Sharp.C k))))
          (matchingNumber (A0 (Sharp.edge k) (H (Sharp.edge k) (Sharp.R k) (Sharp.C k)) (Sharp.C k))) : ℕ) : ℝ) +
        ((qNote (Sharp.edge k) (Sharp.R k) (Sharp.C k) R' C').card : ℝ) + K := by
  obtain ⟨k,h⟩ := coefficient_one_sharp c K hc
  refine ⟨k,?_⟩
  intro R' C' hAd
  have hBad := h R' C' ((admissible_exact _ _ _ _ _).mp hAd)
  rw [qNote_exact]
  exact hBad

#print exact_arbitrary_size_family
#print exact_real_coefficient_one_sharpness
#print axioms exact_arbitrary_size_family
#print axioms exact_real_coefficient_one_sharpness
end FinalPruningAudit
