import Family173.Definitions
import Family173.Fibers

namespace Family173
open OAI.SeymourSecondNeighborhood
open Bipartite

variable {X : Type*} [Fintype X] [DecidableEq X]

noncomputable def coordinateEdges (M : Finset ((X × X) × (X × X))) (j : X) :
    Finset (X × X) := by
  classical
  exact (M.filter (fun e => e.1.2 = j)).image (fun e => (e.1.1, e.2.1))

theorem coordinateEdges_matching (r : X → X → Prop) (W Z : Finset (X × X))
    (M : Finset ((X × X) × (X × X))) (j : X)
    (hM : IsMatching (Pruning.LeftCovers r) M) (hLeft : leftVertices M = W)
    (hRight : ∀ e ∈ M, e.2 ∈ Z) :
    IsMatching (restricted r (fiber W j) (fiber Z j)) (coordinateEdges M j) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    change e ∈ (M.filter (fun a => a.1.2 = j)).image
      (fun a => (a.1.1, a.2.1)) at he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    rcases a with ⟨⟨p, k⟩, ⟨i, l⟩⟩
    obtain ⟨heM, hk⟩ := Finset.mem_filter.mp ha
    have hEdge := hM.1 ((p, k), (i, l)) heM
    have hkl : k = l := hEdge.1
    change k = j at hk
    subst k
    subst l
    have hpW : (p, j) ∈ W := by
      rw [← hLeft]
      exact mem_leftVertices.mpr ⟨(i, j), heM⟩
    exact ⟨(mem_fiber W j p).mpr hpW,
      (mem_fiber Z j i).mpr (hRight _ heM), hEdge.2⟩
  · intro e he f hf hef
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨haM, haJ⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbM, hbJ⟩ := Finset.mem_filter.mp hb
    have hab : a.1 = b.1 := Prod.ext hef (haJ.trans hbJ.symm)
    exact congrArg (fun q : (X × X) × (X × X) => (q.1.1, q.2.1))
      (hM.2.1 haM hbM hab)
  · intro e he f hf hef
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨haM, haJ⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbM, hbJ⟩ := Finset.mem_filter.mp hb
    have ha2 : a.2.2 = j := (hM.1 a haM).1.symm.trans haJ
    have hb2 : b.2.2 = j := (hM.1 b hbM).1.symm.trans hbJ
    have hab : a.2 = b.2 := Prod.ext hef (ha2.trans hb2.symm)
    exact congrArg (fun q : (X × X) × (X × X) => (q.1.1, q.2.1))
      (hM.2.2 haM hbM hab)

theorem coordinateEdges_saturates (W : Finset (X × X))
    (M : Finset ((X × X) × (X × X))) (j : X) (hLeft : leftVertices M = W) :
    leftVertices (coordinateEdges M j) = fiber W j := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨i, hi⟩ := mem_leftVertices.mp hp
    obtain ⟨a, ha, hEq⟩ := Finset.mem_image.mp hi
    obtain ⟨haM, haJ⟩ := Finset.mem_filter.mp ha
    have hpW : a.1 ∈ W := by
      rw [← hLeft]
      exact mem_leftVertices.mpr ⟨a.2, haM⟩
    apply (mem_fiber W j p).mpr
    have hPair : (p, j) = a.1 :=
      Prod.ext (congrArg Prod.fst hEq).symm haJ.symm
    rw [hPair]
    exact hpW
  · intro hp
    have hpW := (mem_fiber W j p).mp hp
    rw [← hLeft] at hpW
    obtain ⟨z, hz⟩ := mem_leftVertices.mp hpW
    exact mem_leftVertices.mpr ⟨z.1, Finset.mem_image.mpr
      ⟨((p, j), z), Finset.mem_filter.mpr ⟨hz, rfl⟩, rfl⟩⟩

noncomputable def flattenMatching {W Z : Finset (X × X)}
    (α : Finset (↥W × ↥Z)) : Finset ((X × X) × (X × X)) := by
  classical
  exact α.image (fun e => (e.1.val, e.2.val))

theorem flattenMatching_isMatching (r : X → X → Prop) (W Z : Finset (X × X))
    (α : Finset (↥W × ↥Z)) (hα : IsMatching (L0 r W Z) α) :
    IsMatching (Pruning.LeftCovers r) (flattenMatching α) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    exact hα.1 a ha
  · intro e he f hf hef
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hf
    exact congrArg (fun q : ↥W × ↥Z => (q.1.val, q.2.val))
      (hα.2.1 ha hb (Subtype.ext hef))
  · intro e he f hf hef
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hf
    exact congrArg (fun q : ↥W × ↥Z => (q.1.val, q.2.val))
      (hα.2.2 ha hb (Subtype.ext hef))

theorem flattenMatching_right_mem (W Z : Finset (X × X))
    (α : Finset (↥W × ↥Z)) : ∀ e ∈ flattenMatching α, e.2 ∈ Z := by
  classical
  intro e he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
  exact a.2.property

theorem flattenMatching_saturates (W Z : Finset (X × X))
    (α : Finset (↥W × ↥Z)) (hSat : leftVertices α = Finset.univ) :
    leftVertices (flattenMatching α) = W := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨z, hz⟩ := mem_leftVertices.mp hw
    obtain ⟨a, ha, hEq⟩ := Finset.mem_image.mp hz
    have hval : a.1.val = w := congrArg Prod.fst hEq
    rw [← hval]
    exact a.1.property
  · intro hw
    let a : W := ⟨w, hw⟩
    have ha : a ∈ leftVertices α := by rw [hSat]; exact Finset.mem_univ a
    obtain ⟨z, hz⟩ := mem_leftVertices.mp ha
    exact mem_leftVertices.mpr ⟨z.val, Finset.mem_image.mpr ⟨(a, z), hz, rfl⟩⟩

section Ordered
variable [LinearOrder X]

theorem selected_corners_card (r : X → X → Prop) (W Z W' : Finset (X × X))
    (α : Finset (↥W × ↥Z)) (hα : IsMatching (L0 r W Z) α)
    (hSat : leftVertices α = Finset.univ) (hW' : W' ⊆ W) :
    (selectFibers r W' Z).card = W'.card := by
  classical
  let M := (flattenMatching α).filter (fun e => e.1 ∈ W')
  have hM : IsMatching (Pruning.LeftCovers r) M :=
    (flattenMatching_isMatching r W Z α hα).submatching (Finset.filter_subset _ _)
  have hRight : ∀ e ∈ M, e.2 ∈ Z := fun e he =>
    flattenMatching_right_mem W Z α e (Finset.mem_filter.mp he).1
  have hLeft : leftVertices M = W' := by
    ext w
    constructor
    · intro hw
      obtain ⟨z, hz⟩ := mem_leftVertices.mp hw
      exact (Finset.mem_filter.mp hz).2
    · intro hw
      have hOld : w ∈ leftVertices (flattenMatching α) := by
        rw [flattenMatching_saturates W Z α hSat]
        exact hW' hw
      obtain ⟨z, hz⟩ := mem_leftVertices.mp hOld
      exact mem_leftVertices.mpr ⟨z, Finset.mem_filter.mpr ⟨hz, hw⟩⟩
  apply selectFibers_card_of_fiber_saturation
  intro j
  exact selector_card_of_saturation r (fiber W' j) (fiber Z j)
    (coordinateEdges_matching r W' Z M j hM hLeft hRight)
    (coordinateEdges_saturates W' M j hLeft)

end Ordered
end Family173
