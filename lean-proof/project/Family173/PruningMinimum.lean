import Family173.PruningOptimum
namespace Family173
open OAI.SeymourSecondNeighborhood
open Bipartite Pruning
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Enumerate exactly the integer objectives of all admissible subfamily pairs. -/
noncomputable def admissibleObjectives (r : X → X → Prop) (R C : Finset (X × X)) : Finset ℤ := by
  classical
  exact ((R.powerset ×ˢ C.powerset).filter (fun a => AdmissiblePruning r R C a.1 a.2)).image
    (fun a => pruningObjective r R C a.1 a.2)

theorem mem_admissibleObjectives (r : X → X → Prop) (R C : Finset (X × X)) (v : ℤ) :
    v ∈ admissibleObjectives r R C ↔
      ∃ R' C', AdmissiblePruning r R C R' C' ∧ pruningObjective r R C R' C'=v := by
  classical
  constructor
  · intro hv
    obtain ⟨a,ha,hav⟩ := Finset.mem_image.mp hv
    exact ⟨a.1,a.2,(Finset.mem_filter.mp ha).2,hav⟩
  · rintro ⟨R',C',hAd,hv⟩
    exact Finset.mem_image.mpr ⟨(R',C'),Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr hAd.subset_left,
        Finset.mem_powerset.mpr hAd.subset_right⟩,hAd⟩,hv⟩

theorem admissibleObjectives_nonempty (r : X → X → Prop) (R C : Finset (X × X)) :
    (admissibleObjectives r R C).Nonempty := by
  obtain ⟨R',C',hAd,_⟩ := exists_admissible_optimal r R C
  exact ⟨pruningObjective r R C R' C',(mem_admissibleObjectives r R C _).mpr ⟨R',C',hAd,rfl⟩⟩

/-- The actual finite minimum, defined independently of the matching formula. -/
noncomputable def minimumPruningObjective (r : X → X → Prop) (R C : Finset (X × X)) : ℤ :=
  (admissibleObjectives r R C).min' (admissibleObjectives_nonempty r R C)

theorem minimum_pruning_identity (r : X → X → Prop) (R C : Finset (X × X)) :
    minimumPruningObjective r R C =
      (matchingNumber (AugmentedEdge r R C) : ℤ)-((Z r R C).card : ℤ) := by
  apply le_antisymm
  · obtain ⟨R',C',hAd,hObj⟩ := exists_admissible_optimal r R C
    exact Finset.min'_le _ _ ((mem_admissibleObjectives r R C _).mpr ⟨R',C',hAd,hObj⟩)
  · have hmem : minimumPruningObjective r R C ∈ admissibleObjectives r R C :=
      Finset.min'_mem _ _
    obtain ⟨R',C',hAd,hObj⟩ := (mem_admissibleObjectives r R C _).mp hmem
    rw [← hObj]
    exact pruning_objective_lower r R C R' C' hAd

theorem minimum_pruning_le_beta (r : X → X → Prop) (R C : Finset (X × X)) :
    minimumPruningObjective r R C ≤
      ((min (matchingNumber (B0 r R (H r R C))) (matchingNumber (A0 r (H r R C) C)) : ℕ) : ℤ) := by
  rw [minimum_pruning_identity]
  have h := matching_capacity r R C
  omega

end Family173
