import IndependentAcceptance

namespace FinalAudit
open OAI.SeymourSecondNeighborhood
open Bipartite

-- A true relation on Fin 2 contains both loops and both opposite arrows.
def totalRelation (_ _ : Fin 2) : Prop := True
def Rfixture : Finset (Fin 2 × Fin 2) := Finset.univ
def Cfixture : Finset (Fin 2 × Fin 2) := Finset.univ.filter (fun a => a.2 = 0)
theorem Zfixture : Pruning.Z totalRelation Rfixture Cfixture = Finset.univ := by
  classical
  ext z
  simp only [Pruning.mem_Z, Finset.mem_univ, iff_true]
  exact ⟨0,0,by simp [Rfixture],by simp [Cfixture],True.intro,True.intro⟩
theorem Hfixture : Pruning.H totalRelation Rfixture Cfixture = Cfixture := by
  classical
  ext h
  simp only [Pruning.mem_H]
  constructor
  · rintro ⟨i,j,_,hi,_,_⟩
    simpa [Cfixture] using hi
  · intro hh
    exact ⟨0,0,by simp [Rfixture],by simpa [Cfixture] using hh,True.intro,True.intro⟩
noncomputable def zcopy (w : Rfixture) : Pruning.Z totalRelation Rfixture Cfixture :=
  ⟨w.val,by rw [Zfixture]; exact Finset.mem_univ _⟩
noncomputable def αfixture : Finset (↥Rfixture × ↥(Pruning.Z totalRelation Rfixture Cfixture)) := by
  classical
  exact Finset.univ.image (fun w => (w,zcopy w))
theorem fixture_matching : IsMatching
    (Family173.L0 totalRelation Rfixture (Pruning.Z totalRelation Rfixture Cfixture)) αfixture := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro e he
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp he
    exact ⟨rfl,True.intro⟩
  · intro e he f hf h
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hf
    exact congrArg (fun w => (w,zcopy w)) h
  · intro e he f hf h
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hf
    have hwv : w = v := Subtype.ext (congrArg (fun (z : Pruning.Z totalRelation Rfixture Cfixture) => z.val) h)
    exact congrArg (fun w => (w,zcopy w)) hwv
theorem fixture_saturated : leftVertices αfixture = Finset.univ := by
  classical
  ext w
  constructor
  · intro _; exact Finset.mem_univ _
  · intro _
    exact mem_leftVertices.mpr ⟨zcopy w,Finset.mem_image.mpr ⟨w,Finset.mem_univ _,rfl⟩⟩
theorem fixture_cover : IsVertexCover
    (Family173.B0 totalRelation Rfixture (Pruning.H totalRelation Rfixture Cfixture))
    ∅ Finset.univ := by
  intro _ h _
  exact Or.inr (Finset.mem_univ h)
theorem fixture_nontrivial :
    Rfixture.card = 4 ∧ (Pruning.Z totalRelation Rfixture Cfixture).card = 4 ∧
    (Pruning.H totalRelation Rfixture Cfixture).card = 2 := by
  rw [Zfixture,Hfixture]
  decide
-- Actual application with |K_B|=2 < |W|=4; the bound is 2, not the whole-Z cover 4.
theorem fixture_CC :
    ∃ A : Finset ↥(Pruning.Z totalRelation Rfixture Cfixture), ∃ D : Finset ↥Cfixture,
      IsVertexCover (Family173.N0 totalRelation (Pruning.Z totalRelation Rfixture Cfixture) Cfixture) A D ∧
      A.card + D.card ≤ 2 := by
  obtain ⟨A,D,hN,hB⟩ := Family173.cover_conversion totalRelation Rfixture Cfixture
    Rfixture (Finset.Subset.refl _) αfixture fixture_matching fixture_saturated
    ∅ Finset.univ fixture_cover
  have hW := fixture_nontrivial.1
  have hZ := fixture_nontrivial.2.1
  have hH := fixture_nontrivial.2.2
  simp only [Finset.card_empty,Finset.card_univ,Fintype.card_coe] at hB
  rw [hW,hZ,hH] at hB
  exact ⟨A,D,hN,by omega⟩
-- Empty finite type still has a satisfiable input, without Nonempty X.
theorem empty_CC : Family173.CoverConversionStatement (fun (_ _ : Fin 0) => False) ∅ ∅ :=
  Family173.cover_conversion _ _ _

#print axioms fixture_matching
#print axioms fixture_saturated
#print axioms fixture_cover
#print axioms fixture_nontrivial
#print axioms fixture_CC
#print axioms empty_CC
end FinalAudit
