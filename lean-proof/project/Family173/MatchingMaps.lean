import Family173.MatchingNumber
namespace Family173
open OAI.SeymourSecondNeighborhood.Bipartite
variable {L R L' R' : Type*} [Fintype L] [Fintype R] [Fintype L'] [Fintype R']
    [DecidableEq L] [DecidableEq R] [DecidableEq L'] [DecidableEq R']

theorem matchingNumber_le_flip {E : L → R → Prop} {F : L' → R' → Prop}
    (f : L → R') (g : R → L') (hf : Function.Injective f) (hg : Function.Injective g)
    (hEF : ∀ l r, E l r → F (g r) (f l)) : matchingNumber E ≤ matchingNumber F := by
  classical
  let M := maximumMatching E
  let φ : L × R → L' × R' := fun e => (g e.2,f e.1)
  have hφ : Function.Injective φ := by
    intro a b h
    exact Prod.ext (hf (congrArg Prod.snd h)) (hg (congrArg Prod.fst h))
  have hM : IsMatching E M := (maximumMatching_spec E).1
  have hN : IsMatching F (M.image φ) := by
    refine ⟨?_,?_,?_⟩
    · intro e he
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
      exact hEF a.1 a.2 (hM.1 a ha)
    · intro e he k hk h
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hk
      exact congrArg φ (hM.2.2 ha hb (hg h))
    · intro e he k hk h
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hk
      exact congrArg φ (hM.2.1 ha hb (hf h))
  have h := matching_card_le_number hN
  rw [Finset.card_image_of_injective M hφ] at h
  exact h
end Family173
