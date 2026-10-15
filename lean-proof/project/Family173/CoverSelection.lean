import Family173.Residual

namespace Family173
open OAI.SeymourSecondNeighborhood
open Bipartite

section Generic
variable {L R : Type*} [DecidableEq L] [DecidableEq R]

theorem tight_cover_left_saturated {E : L → R → Prop} {M : Finset (L × R)}
    {A : Finset L} {B : Finset R} (hM : IsMatching E M) (hC : IsVertexCover E A B)
    (hCard : A.card+B.card=M.card) : A ⊆ leftVertices M := by
  classical
  intro x hx
  by_contra hn
  let E' : L → R → Prop := fun l r => (l,r) ∈ M
  have hM' : IsMatching E' M := ⟨fun _ h => h,hM.2⟩
  have hC' : IsVertexCover E' (A.erase x) B := by
    intro l r he
    rcases hC l r (hM.1 (l,r) he) with hl | hr
    · left
      refine Finset.mem_erase.mpr ⟨?_,hl⟩
      intro h
      exact hn (h ▸ mem_leftVertices.mpr ⟨r,he⟩)
    · exact Or.inr hr
  have hb := matching_card_le_cover_card hM' hC'
  have he := Finset.card_erase_add_one hx
  omega

theorem tight_cover_right_saturated {E : L → R → Prop} {M : Finset (L × R)}
    {A : Finset L} {B : Finset R} (hM : IsMatching E M) (hC : IsVertexCover E A B)
    (hCard : A.card+B.card=M.card) : B ⊆ rightVertices M := by
  classical
  intro y hy
  by_contra hn
  let E' : L → R → Prop := fun l r => (l,r) ∈ M
  have hM' : IsMatching E' M := ⟨fun _ h => h,hM.2⟩
  have hC' : IsVertexCover E' A (B.erase y) := by
    intro l r he
    rcases hC l r (hM.1 (l,r) he) with hl | hr
    · exact Or.inl hl
    · right
      refine Finset.mem_erase.mpr ⟨?_,hr⟩
      intro h
      exact hn (h ▸ mem_rightVertices.mpr ⟨l,he⟩)
  have hb := matching_card_le_cover_card hM' hC'
  have he := Finset.card_erase_add_one hy
  omega
end Generic

variable {X : Type*} [Fintype X] [DecidableEq X]
section Ordered
variable [LinearOrder X]

theorem tight_restricted_cover_right_selected (r : X → X → Prop) (P I A B : Finset X)
    (hC : IsVertexCover (restricted r P I) A B) (hCard : A.card+B.card=nu r P I)
    (hB : B ⊆ I) : B ⊆ selector r P I := by
  intro i hi
  apply (mem_selector_iff_not_exposable r P I i).mpr
  refine ⟨hB hi,?_⟩
  intro hex
  have hpref : prefixLE I i ⊆ I := Finset.filter_subset _ _
  have hex' := rightExposable_mono_right r P hpref i
    (Finset.mem_filter.mpr ⟨hB hi,le_rfl⟩) hex
  obtain ⟨M,hM,hMc,hfree⟩ := hex'
  exact hfree ((tight_cover_right_saturated hM hC (hCard.trans hMc.symm)) hi)


theorem saturated_fiber_number (r : X → X → Prop) (W Z : Finset (X × X))
    (α : Finset (↥W × ↥Z)) (hα : IsMatching (L0 r W Z) α)
    (hSat : leftVertices α = Finset.univ) (j : X) :
    nu r (fiber W j) (fiber Z j) = (fiber W j).card := by
  let M := flattenMatching α
  have hM := flattenMatching_isMatching r W Z α hα
  have hL := flattenMatching_saturates W Z α hSat
  exact nu_eq_card_of_saturation r (fiber W j) (fiber Z j)
    (coordinateEdges_matching r W Z M j hM hL (flattenMatching_right_mem W Z α))
    (coordinateEdges_saturates W M j hL)

theorem fiber_cover (r : X → X → Prop) (W Z : Finset (X × X))
    (U : Finset ↥W) (V : Finset ↥Z) (hC : IsVertexCover (L0 r W Z) U V) (j : X) :
    IsVertexCover (restricted r (fiber W j) (fiber Z j))
      (fiber (rawSet U) j) (fiber (rawSet V) j) := by
  intro p i he
  let w : W := ⟨(p,j),(mem_fiber W j p).mp he.1⟩
  let z : Z := ⟨(i,j),(mem_fiber Z j i).mp he.2.1⟩
  rcases hC w z ⟨rfl,he.2.2⟩ with hw | hz
  · left
    exact (mem_fiber _ j p).mpr ((mem_rawSet U (p,j)).mpr ⟨w,hw,rfl⟩)
  · right
    exact (mem_fiber _ j i).mpr ((mem_rawSet V (i,j)).mpr ⟨z,hz,rfl⟩)

theorem tight_L_cover_right_selected (r : X → X → Prop) (W Z : Finset (X × X))
    (α : Finset (↥W × ↥Z)) (hα : IsMatching (L0 r W Z) α)
    (hSat : leftVertices α = Finset.univ)
    (U : Finset ↥W) (V : Finset ↥Z) (hC : IsVertexCover (L0 r W Z) U V)
    (hCard : U.card+V.card=W.card) : rawSet V ⊆ selectFibers r W Z := by
  classical
  have hnu (j : X) := saturated_fiber_number r W Z α hα hSat j
  have hle (j : X) : (fiber W j).card ≤
      (fiber (rawSet U) j).card+(fiber (rawSet V) j).card := by
    have h := matching_card_le_cover_card
      (maximumMatching_spec (restricted r (fiber W j) (fiber Z j))).1 (fiber_cover r W Z U V hC j)
    change nu r (fiber W j) (fiber Z j) ≤ _ at h
    rw [hnu j] at h
    exact h
  have hsum : (∑ j : X, (fiber W j).card) =
      ∑ j : X, ((fiber (rawSet U) j).card+(fiber (rawSet V) j).card) := by
    rw [← card_eq_sum_fiber W,Finset.sum_add_distrib,
      ← card_eq_sum_fiber (rawSet U),← card_eq_sum_fiber (rawSet V),rawSet_card U,rawSet_card V]
    exact hCard.symm
  have heach (j : X) : (fiber (rawSet U) j).card+(fiber (rawSet V) j).card = (fiber W j).card :=
    ((Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).mp hsum j (Finset.mem_univ j)).symm
  intro z hz
  apply (mem_selectFibers r W Z z).mpr
  apply tight_restricted_cover_right_selected r (fiber W z.2) (fiber Z z.2)
    (fiber (rawSet U) z.2) (fiber (rawSet V) z.2) (fiber_cover r W Z U V hC z.2)
    ((heach z.2).trans (hnu z.2).symm)
  · intro i hi
    exact (mem_fiber Z z.2 i).mpr (rawSet_subset V ((mem_fiber _ z.2 i).mp hi))
  · exact (mem_fiber _ z.2 z.1).mpr hz

end Ordered
end Family173
