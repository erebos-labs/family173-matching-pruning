import SharpAcceptance

namespace LocalFinalAudit
open OAI.SeymourSecondNeighborhood
open Bipartite Pruning Family173 FinalPruningAudit

variable {X : Type*} [Fintype X] [DecidableEq X]

noncomputable def literalObjective (r : X → X → Prop) (R C R' C' : Finset (X × X)) : ℤ :=
  (((R \ R').card+(C \ C').card : ℕ) : ℤ)-((qNote r R C R' C').card : ℤ)

theorem literalObjective_exact (r : X → X → Prop) (R C R' C' : Finset (X × X)) :
    literalObjective r R C R' C'=pruningObjective r R C R' C' := by
  unfold literalObjective
  rw [qNote_exact]
  rfl

/-- Validate actual minimum semantics directly via the finite objective set,
without using the matching-number formula for the value. -/
theorem actual_minimum_semantics (r : X → X → Prop) (R C : Finset (X × X)) :
    (∃ R' C', AdmissibleNote r R C R' C' ∧
      literalObjective r R C R' C'=minimumPruningObjective r R C) ∧
    ∀ R' C', AdmissibleNote r R C R' C' →
      minimumPruningObjective r R C ≤ literalObjective r R C R' C' := by
  have hMem : minimumPruningObjective r R C ∈ admissibleObjectives r R C :=
    Finset.min'_mem _ _
  obtain ⟨R',C',hAd,hValue⟩ := (mem_admissibleObjectives r R C _).mp hMem
  constructor
  · exact ⟨R',C',(admissible_exact r R C R' C').mpr hAd,
      (literalObjective_exact r R C R' C').trans hValue⟩
  · intro S T hLiteral
    have hVal : pruningObjective r R C S T ∈ admissibleObjectives r R C :=
      (mem_admissibleObjectives r R C _).mpr
        ⟨S,T,(admissible_exact r R C S T).mp hLiteral,rfl⟩
    have hMin : minimumPruningObjective r R C ≤ pruningObjective r R C S T :=
      Finset.min'_le _ _ hVal
    rw [literalObjective_exact]
    exact hMin

/-- Convert the k+1 parameter to every explicitly requested positive size n. -/
theorem every_positive_size (n : ℕ) (hn : 1≤n) :
    ∃ k : ℕ, k+1=n ∧ (Sharp.R k).card=n ∧ (Sharp.C k).card=n ∧
      (Z (Sharp.edge k) (Sharp.R k) (Sharp.C k)).card=1 ∧
      (H (Sharp.edge k) (Sharp.R k) (Sharp.C k)).card=n*n ∧
      matchingNumber (B0 (Sharp.edge k) (Sharp.R k) (H (Sharp.edge k) (Sharp.R k) (Sharp.C k)))=n ∧
      matchingNumber (A0 (Sharp.edge k) (H (Sharp.edge k) (Sharp.R k) (Sharp.C k)) (Sharp.C k))=n ∧
      matchingNumber (AugmentedEdge (Sharp.edge k) (Sharp.R k) (Sharp.C k))=n+1 ∧
      minimumPruningObjective (Sharp.edge k) (Sharp.R k) (Sharp.C k)=(n : ℤ) := by
  let k := n-1
  have hk : k+1=n := Nat.sub_add_cancel hn
  exact ⟨k,hk,(Sharp.R_card k).trans hk,(Sharp.C_card k).trans hk,Sharp.Z_card k,
    (Sharp.H_card k).trans (congrArg (fun m : ℕ => m*m) hk),
    (Sharp.B_number k).trans hk,(Sharp.A_number k).trans hk,
    (Sharp.Gamma_number k).trans (congrArg (fun m : ℕ => m+1) hk),
    (sharp_minimum_value k).trans (congrArg (fun m : ℕ => (m : ℤ)) hk)⟩

/-- The coefficient obstruction's universal pruning quantifier is nonvacuous. -/
theorem real_counterexample_nonvacuous (c K : ℝ) (hc : c<1) :
    ∃ k : ℕ,
      (∃ R' C', AdmissibleNote (Sharp.edge k) (Sharp.R k) (Sharp.C k) R' C') ∧
      ∀ R' C', AdmissibleNote (Sharp.edge k) (Sharp.R k) (Sharp.C k) R' C' →
        (((Sharp.R k \ R').card+(Sharp.C k \ C').card : ℕ) : ℝ) >
          c * ((min
            (matchingNumber (B0 (Sharp.edge k) (Sharp.R k) (H (Sharp.edge k) (Sharp.R k) (Sharp.C k))))
            (matchingNumber (A0 (Sharp.edge k) (H (Sharp.edge k) (Sharp.R k) (Sharp.C k)) (Sharp.C k))) : ℕ) : ℝ) +
          ((qNote (Sharp.edge k) (Sharp.R k) (Sharp.C k) R' C').card : ℝ) + K := by
  obtain ⟨k,hBad⟩ := exact_real_coefficient_one_sharpness c K hc
  obtain ⟨R',C',hAd,_⟩ := exists_admissible_optimal (Sharp.edge k) (Sharp.R k) (Sharp.C k)
  exact ⟨k,⟨R',C',(admissible_exact _ _ _ _ _).mpr hAd⟩,hBad⟩

#print axioms literalObjective_exact
#print axioms actual_minimum_semantics
#print axioms every_positive_size
#print axioms real_counterexample_nonvacuous
end LocalFinalAudit
