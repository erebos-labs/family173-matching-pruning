import Family173.PruningMinimum
import CapacityAcceptance

namespace FinalPruningAudit
open OAI.SeymourSecondNeighborhood
open Bipartite Pruning
open Family173
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Literal published admissibility, with no cost/bound in the predicate. -/
def AdmissibleNote (r : X → X → Prop) (R C R' C' : Finset (X × X)) : Prop :=
  R' ⊆ R ∧ C' ⊆ C ∧
    (∀ a ∈ R', ∀ b ∈ C', ¬ (r a.1 b.1 ∧ r b.2 a.2)) ∧
    (∀ a ∈ R, (∀ b ∈ C, ¬ (r a.1 b.1 ∧ r b.2 a.2)) → a ∈ R') ∧
    (∀ b ∈ C, (∀ a ∈ R, ¬ (r a.1 b.1 ∧ r b.2 a.2)) → b ∈ C')

theorem admissible_exact (r : X → X → Prop) (R C R' C' : Finset (X × X)) :
    AdmissibleNote r R C R' C' ↔ AdmissiblePruning r R C R' C' := by
  constructor
  · rintro ⟨hR,hC,hFree,hRetR,hRetC⟩
    exact ⟨hR,hC,hFree,hRetR,hRetC⟩
  · intro h
    exact ⟨h.subset_left,h.subset_right,h.no_conflicts,h.retain_left,h.retain_right⟩

/-- DISTINCT points of ORIGINAL Z covered by neither retained side. -/
noncomputable def qNote (r : X → X → Prop) (R C R' C' : Finset (X × X)) : Finset (X × X) := by
  classical
  exact (FinalAudit.Znote r R C).filter (fun z =>
    ¬ (∃ p, (p,z.2) ∈ R' ∧ r p z.1) ∧ ¬ (∃ s, (z.1,s) ∈ C' ∧ r s z.2))

theorem qNote_exact (r : X → X → Prop) (R C R' C' : Finset (X × X)) :
    qNote r R C R' C'=uncoveredZ r R C R' C' := by
  classical
  ext z
  simp only [qNote,uncoveredZ,Finset.mem_filter,Covered,mem_leftImage,mem_rightImage,
    FinalAudit.Znote_eq,not_or]

theorem exact_published_optimum_and_attainment (r : X → X → Prop) (R C : Finset (X × X)) :
    minimumPruningObjective r R C =
      (matchingNumber (AugmentedEdge r R C) : ℤ)-((FinalAudit.Znote r R C).card : ℤ) ∧
    minimumPruningObjective r R C ≤
      ((min (matchingNumber (B0 r R (FinalAudit.Hnote r R C)))
        (matchingNumber (A0 r (FinalAudit.Hnote r R C) C)) : ℕ) : ℤ) ∧
    (∃ R' C', AdmissibleNote r R C R' C' ∧
      (((R \ R').card+(C \ C').card : ℕ) : ℤ)-((qNote r R C R' C').card : ℤ)=
        minimumPruningObjective r R C ∧
      (R \ R').card+(C \ C').card ≤
        min (matchingNumber (B0 r R (FinalAudit.Hnote r R C)))
          (matchingNumber (A0 r (FinalAudit.Hnote r R C) C))+(qNote r R C R' C').card) := by
  refine ⟨minimum_pruning_identity r R C,minimum_pruning_le_beta r R C,?_⟩
  obtain ⟨R',C',hAd,hObj⟩ := exists_admissible_optimal r R C
  have hEq : pruningObjective r R C R' C'=minimumPruningObjective r R C :=
    hObj.trans (minimum_pruning_identity r R C).symm
  have hBudget : deletions R C R' C' ≤
      min (matchingNumber (B0 r R (H r R C))) (matchingNumber (A0 r (H r R C) C))+
        (uncoveredZ r R C R' C').card := by
    have hCap := matching_capacity r R C
    have arithmetic (d q g z b : ℕ) : (d : ℤ)-(q : ℤ)=(g : ℤ)-(z : ℤ) → g≤z+b → d≤b+q := by omega
    exact arithmetic _ _ _ _ _ hObj hCap
  refine ⟨R',C',(admissible_exact r R C R' C').mpr hAd,?_,?_⟩
  · rw [qNote_exact]
    exact hEq
  · rw [qNote_exact]
    exact hBudget

#print exact_published_optimum_and_attainment
#print axioms exact_published_optimum_and_attainment
#print axioms admissible_exact
#print axioms qNote_exact
end FinalPruningAudit
