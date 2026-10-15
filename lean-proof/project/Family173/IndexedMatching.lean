import Family173.PruningOptimum
namespace Family173
open OAI.SeymourSecondNeighborhood.Bipartite
variable {L R A : Type*} [Fintype L] [Fintype R] [Fintype A]
    [DecidableEq L] [DecidableEq R]

theorem indexed_matching_lower (E : L → R → Prop) (f : A → L) (g : A → R)
    (hf : Function.Injective f) (hg : Function.Injective g) (hE : ∀ a, E (f a) (g a)) :
    Fintype.card A ≤ matchingNumber E := by
  classical
  let φ : A → L × R := fun a => (f a,g a)
  let M := Finset.univ.image φ
  have hM : IsMatching E M := by
    refine ⟨?_,?_,?_⟩
    · intro e he
      obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp he
      exact hE a
    · intro e he k hk h
      obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hk
      exact congrArg φ (hf h)
    · intro e he k hk h
      obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hk
      exact congrArg φ (hg h)
  have h := matching_card_le_number hM
  have hφ : Function.Injective φ := fun _ _ he => hf (congrArg Prod.fst he)
  have hc : M.card=Fintype.card A := by
    rw [Finset.card_image_of_injective _ hφ,Finset.card_univ]
  omega

theorem matchingNumber_le_card_left (E : L → R → Prop) : matchingNumber E ≤ Fintype.card L := by
  classical
  let M := maximumMatching E
  have h := Finset.card_le_card (Finset.subset_univ (leftVertices M))
  rw [matching_card_leftVertices (maximumMatching_spec E).1,Finset.card_univ] at h
  exact h

theorem matchingNumber_le_card_right (E : L → R → Prop) : matchingNumber E ≤ Fintype.card R := by
  classical
  let M := maximumMatching E
  have h := Finset.card_le_card (Finset.subset_univ (rightVertices M))
  rw [matching_card_rightVertices (maximumMatching_spec E).1,Finset.card_univ] at h
  exact h
end Family173
