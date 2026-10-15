import Family173.UsedLeft
import OAI.Combinatorics.SecondNeighborhood.AugmentedGraph

namespace Family173
open OAI.SeymourSecondNeighborhood
open Bipartite
open Pruning
variable {X : Type*} [Fintype X] [DecidableEq X]
section Ordered
variable [LinearOrder X]

/-- Lift any B0 cover to a Gamma cover, using the original corners. -/
theorem gamma_cover_of_B_cover (r : X → X → Prop) (R C : Finset (X × X))
    (U : Finset ↥R) (V : Finset ↥(Pruning.H r R C))
    (hB : IsVertexCover (B0 r R (Pruning.H r R C)) U V) :
    ∃ GL : Finset (LeftVertex r R C), ∃ GR : Finset (RightVertex r R C),
      IsVertexCover (AugmentedEdge r R C) GL GR ∧
      GL.card+GR.card ≤ (Pruning.Z r R C).card+U.card+V.card := by
  classical
  let Z := Pruning.Z r R C
  let P := R \ rawSet U
  let M := maximumMatching (L0 r P Z)
  have hM : IsMatching (L0 r P Z) M := (maximumMatching_spec _).1
  obtain ⟨AL,BZ,hL,hLCost,_,_⟩ := exists_vertexCover_card_eq_of_isMaximumMatching
    (maximumMatching_spec (L0 r P Z))
  change AL.card+BZ.card=M.card at hLCost
  let W := usedLeft M
  let α := onUsedLeft M
  have hα : IsMatching (L0 r W Z) α := onUsedLeft_matching r P Z M hM
  have hSat : leftVertices α=Finset.univ := onUsedLeft_saturates P Z M
  have hWP : W ⊆ P := usedLeft_subset M
  have hPR : P ⊆ R := Finset.sdiff_subset
  have hWR : W ⊆ R := hWP.trans hPR
  have hWCard : W.card=M.card := usedLeft_card r P Z M hM
  have hALW : rawSet AL ⊆ W := by
    intro a ha
    obtain ⟨l,hl,rfl⟩ := (mem_rawSet AL a).mp ha
    exact (mem_rawSet (leftVertices M) l.val).mpr
      ⟨l,tight_cover_left_saturated hM hL hLCost hl,rfl⟩
  let AW := liftSet W (rawSet AL)
  have hAWCard : AW.card=AL.card := by
    rw [liftSet_card W (rawSet AL) hALW,rawSet_card AL]
  have hLW : IsVertexCover (L0 r W Z) AW BZ := by
    intro w z he
    let p : P := ⟨w.val,hWP w.property⟩
    rcases hL p z he with hp | hz
    · left
      exact (mem_liftSet W (rawSet AL) w).mpr ((mem_rawSet AL w.val).mpr ⟨p,hp,rfl⟩)
    · exact Or.inr hz
  let Q := selectFibers r W Z
  let D := selectFibers r (rawSet V) C
  let A := Z \ Q
  have hQsub : Q ⊆ Z := selectFibers_subset r W Z
  have hDsub : D ⊆ C := selectFibers_subset r (rawSet V) C
  have hAsub : A ⊆ Z := Finset.sdiff_subset
  have hQCard : Q.card=W.card := selected_corners_card r W Z W α hα hSat (Finset.Subset.refl W)
  have hDCard : D.card≤V.card := by
    have h := selectFibers_card_le r (rawSet V) C
    rw [rawSet_card V] at h
    exact h
  have hBQ : rawSet BZ ⊆ Q := tight_L_cover_right_selected r W Z α hα hSat AW BZ hLW
    (by rw [hAWCard,hLCost,hWCard])
  have hContain : ∀ j s, r s j →
      selector r (fiber W j) (fiber Z j) ∩ fiber C s ⊆
        selector r (fiber (rawSet V) s) (fiber C s) := by
    intro j s hsj
    apply selector_containment
    intro p hp i hi hpi
    have hpW := (mem_fiber W j p).mp hp
    have hpP := hWP hpW
    obtain ⟨hpR,hpU⟩ := Finset.mem_sdiff.mp hpP
    let w : R := ⟨(p,j),hpR⟩
    let c : C := ⟨(i,s),(mem_fiber C s i).mp hi⟩
    have hwU : w ∉ U := by
      intro h
      exact hpU ((mem_rawSet U (p,j)).mpr ⟨w,h,rfl⟩)
    have hCorners := original_conflict_corners r R C R (Finset.Subset.refl R) w c hpi hsj
    obtain ⟨h,hhV,hpair⟩ := cover_forces_original_H_corner r R C R
      (Finset.Subset.refl R) U V hB w c hwU hpi hsj
    exact ⟨(mem_fiber Z j i).mpr hCorners.1,
      (mem_fiber (rawSet V) s p).mpr ((mem_rawSet V (p,s)).mpr ⟨h,hhV,hpair⟩)⟩
  have hN : IsVertexCover (N0 r Z C) (liftSet Z A) (liftSet C D) := by
    intro z c he
    by_cases hzQ : z.val ∈ Q
    · right
      apply (mem_liftSet C D c).mpr
      have hzSel := (mem_selectFibers r W Z z.val).mp hzQ
      have hcFiber : z.val.1 ∈ fiber C c.val.2 := by
        apply (mem_fiber C c.val.2 z.val.1).mpr
        have hpair : (z.val.1,c.val.2)=c.val := Prod.ext he.1.symm rfl
        rw [hpair]
        exact c.property
      have hpicked := hContain z.val.2 c.val.2 he.2 (Finset.mem_inter.mpr ⟨hzSel,hcFiber⟩)
      apply (mem_selectFibers r (rawSet V) C c.val).mpr
      rw [he.1]
      exact hpicked
    · left
      exact (mem_liftSet Z A z).mpr (Finset.mem_sdiff.mpr ⟨z.property,hzQ⟩)
  let AR := liftSet R (rawSet AL)
  have hARCard : AR.card=AL.card := by
    rw [liftSet_card R (rawSet AL) (hALW.trans hWR),rawSet_card AL]
  let GL := (U ∪ AR).disjSum (liftSet Z A)
  let GR := (liftSet C D).disjSum BZ
  refine ⟨GL,GR,?_,?_⟩
  · intro l c he
    cases l with
    | inl w =>
      by_cases hwU : w ∈ U
      · left
        exact Finset.inl_mem_disjSum.mpr (Finset.mem_union_left _ hwU)
      have hwP : w.val ∈ P := Finset.mem_sdiff.mpr ⟨w.property,by
        intro h
        obtain ⟨u,hu,heq⟩ := (mem_rawSet U w.val).mp h
        exact hwU ((Subtype.ext heq) ▸ hu)⟩
      let p : P := ⟨w.val,hwP⟩
      cases c with
      | inr z =>
        rcases hL p z he with hp | hz
        · left
          apply Finset.inl_mem_disjSum.mpr
          apply Finset.mem_union_right
          exact (mem_liftSet R (rawSet AL) w).mpr ((mem_rawSet AL w.val).mpr ⟨p,hp,rfl⟩)
        · exact Or.inr (Finset.inr_mem_disjSum.mpr hz)
      | inl c =>
        let z : Z := ⟨(c.val.1,w.val.2),(original_conflict_corners r R C R
          (Finset.Subset.refl R) w c he.1 he.2).1⟩
        rcases hL p z ⟨rfl,he.1⟩ with hp | hz
        · left
          apply Finset.inl_mem_disjSum.mpr
          apply Finset.mem_union_right
          exact (mem_liftSet R (rawSet AL) w).mpr ((mem_rawSet AL w.val).mpr ⟨p,hp,rfl⟩)
        · have hzQ : z.val ∈ Q := hBQ ((mem_rawSet BZ z.val).mpr ⟨z,hz,rfl⟩)
          rcases hN z c ⟨rfl,he.2⟩ with hzA | hcD
          · have hzA' := (mem_liftSet Z A z).mp hzA
            exact False.elim ((Finset.mem_sdiff.mp hzA').2 hzQ)
          · exact Or.inr (Finset.inl_mem_disjSum.mpr hcD)
    | inr z =>
      cases c with
      | inr _ => exact False.elim he
      | inl c =>
        rcases hN z c he with hzA | hcD
        · exact Or.inl (Finset.inr_mem_disjSum.mpr hzA)
        · exact Or.inr (Finset.inl_mem_disjSum.mpr hcD)
  · have hUnion := Finset.card_union_le U AR
    have hACard : A.card+Q.card=Z.card := Finset.card_sdiff_add_card_eq_card hQsub
    change ((U ∪ AR).disjSum (liftSet Z A)).card + ((liftSet C D).disjSum BZ).card ≤ _
    rw [Finset.card_disjSum,Finset.card_disjSum,
      liftSet_card Z A hAsub,liftSet_card C D hDsub] 
    rw [hARCard] at hUnion
    change (U ∪ AR).card + A.card + (D.card+BZ.card) ≤ Z.card+U.card+V.card
    omega

end Ordered

theorem capacity_B (r : X → X → Prop) (R C : Finset (X × X)) :
    matchingNumber (AugmentedEdge r R C) ≤ (Pruning.Z r R C).card +
      matchingNumber (B0 r R (Pruning.H r R C)) := by
  classical
  letI : LinearOrder X := LinearOrder.lift' (Fintype.equivFin X) (Fintype.equivFin X).injective
  obtain ⟨U,V,hB,hCard,_,_⟩ := exists_vertexCover_card_eq_of_isMaximumMatching
    (maximumMatching_spec (B0 r R (Pruning.H r R C)))
  obtain ⟨GL,GR,hG,hBound⟩ := gamma_cover_of_B_cover r R C U V hB
  have h := matching_card_le_cover_card (maximumMatching_spec (AugmentedEdge r R C)).1 hG
  change matchingNumber (AugmentedEdge r R C) ≤ GL.card+GR.card at h
  change U.card+V.card=matchingNumber (B0 r R (Pruning.H r R C)) at hCard
  omega

end Family173
