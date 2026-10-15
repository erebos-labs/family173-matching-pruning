import Family173.CoverSelection
namespace Family173
open OAI.SeymourSecondNeighborhood
open Bipartite
variable {X : Type*} [Fintype X] [DecidableEq X]

noncomputable def usedLeft {P Z : Finset (X × X)} (M : Finset (↥P × ↥Z)) : Finset (X × X) :=
  rawSet (leftVertices M)

theorem usedLeft_subset {P Z : Finset (X × X)} (M : Finset (↥P × ↥Z)) : usedLeft M ⊆ P :=
  rawSet_subset _

noncomputable def onUsedLeft {P Z : Finset (X × X)} (M : Finset (↥P × ↥Z)) :
    Finset (↥(usedLeft M) × ↥Z) := by
  classical
  exact M.attach.image (fun e =>
    (⟨e.val.1.val,(mem_rawSet (leftVertices M) e.val.1.val).mpr
      ⟨e.val.1,mem_leftVertices.mpr ⟨e.val.2,e.property⟩,rfl⟩⟩,e.val.2))

theorem onUsedLeft_matching (r : X → X → Prop) (P Z : Finset (X × X))
    (M : Finset (↥P × ↥Z)) (hM : IsMatching (L0 r P Z) M) :
    IsMatching (L0 r (usedLeft M) Z) (onUsedLeft M) := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro e he
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp he
    exact hM.1 a.val a.property
  · intro e he f hf hef
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hf
    have hab : a.val.1=b.val.1 := Subtype.ext (congrArg (fun (w : usedLeft M) => w.val) hef)
    have heq := hM.2.1 a.property b.property hab
    have hatt : a=b := Subtype.ext heq
    subst b
    rfl
  · intro e he f hf hef
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hf
    have heq := hM.2.2 a.property b.property hef
    have hatt : a=b := Subtype.ext heq
    subst b
    rfl

theorem onUsedLeft_saturates (P Z : Finset (X × X)) (M : Finset (↥P × ↥Z)) :
    leftVertices (onUsedLeft M) = Finset.univ := by
  classical
  ext w
  constructor
  · intro _;exact Finset.mem_univ _
  · intro _
    obtain ⟨a,ha,haw⟩ := (mem_rawSet (leftVertices M) w.val).mp w.property
    obtain ⟨z,haz⟩ := mem_leftVertices.mp ha
    apply mem_leftVertices.mpr
    refine ⟨z,Finset.mem_image.mpr ⟨⟨(a,z),haz⟩,Finset.mem_attach _ _,?_⟩⟩
    apply Prod.ext
    · exact Subtype.ext haw
    · rfl

theorem usedLeft_card (r : X → X → Prop) (P Z : Finset (X × X))
    (M : Finset (↥P × ↥Z)) (hM : IsMatching (L0 r P Z) M) :
    (usedLeft M).card=M.card := by
  rw [usedLeft,rawSet_card]
  exact matching_card_leftVertices hM

end Family173
