import Family173.Selector
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Family173
open scoped BigOperators

variable {X : Type*} [Fintype X] [DecidableEq X]

noncomputable def fiber (T : Finset (X × X)) (j : X) : Finset X := by
  classical
  exact Finset.univ.filter (fun p => (p, j) ∈ T)

theorem mem_fiber (T : Finset (X × X)) (j p : X) : p ∈ fiber T j ↔ (p, j) ∈ T := by
  classical
  simp [fiber]

theorem fiber_card (T : Finset (X × X)) (j : X) :
    (T.filter (fun a => a.2 = j)).card = (fiber T j).card := by
  classical
  have hImage : (fiber T j).image (fun p => (p, j)) = T.filter (fun a => a.2 = j) := by
    ext a
    constructor
    · intro ha
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_filter.mpr ⟨(mem_fiber T j p).mp hp, rfl⟩
    · intro ha
      obtain ⟨haT, haj⟩ := Finset.mem_filter.mp ha
      have hEq : (a.1, j) = a := Prod.ext rfl haj.symm
      refine Finset.mem_image.mpr ⟨a.1, (mem_fiber T j a.1).mpr ?_, hEq⟩
      rw [hEq]
      exact haT
  rw [← hImage]
  apply Finset.card_image_of_injective
  intro p q h
  exact congrArg Prod.fst h

theorem card_eq_sum_fiber (T : Finset (X × X)) :
    T.card = ∑ j : X, (fiber T j).card := by
  have h := Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (s := T)
    (t := (Finset.univ : Finset X)) (by intro a _; exact Finset.mem_univ a.2)
  simpa only [fiber_card] using h

section Ordered
variable [LinearOrder X]

noncomputable def selectFibers (r : X → X → Prop) (P I : Finset (X × X)) :
    Finset (X × X) := by
  classical
  exact Finset.univ.filter (fun a => a.1 ∈ selector r (fiber P a.2) (fiber I a.2))

theorem mem_selectFibers (r : X → X → Prop) (P I : Finset (X × X)) (a : X × X) :
    a ∈ selectFibers r P I ↔ a.1 ∈ selector r (fiber P a.2) (fiber I a.2) := by
  classical
  simp [selectFibers]

theorem selectFibers_subset (r : X → X → Prop) (P I : Finset (X × X)) :
    selectFibers r P I ⊆ I := by
  intro a ha
  exact (mem_fiber I a.2 a.1).mp
    (selector_subset_right r (fiber P a.2) (fiber I a.2) ((mem_selectFibers r P I a).mp ha))

theorem fiber_selectFibers (r : X → X → Prop) (P I : Finset (X × X)) (j : X) :
    fiber (selectFibers r P I) j = selector r (fiber P j) (fiber I j) := by
  ext i
  rw [mem_fiber, mem_selectFibers]

theorem selectFibers_card_le (r : X → X → Prop) (P I : Finset (X × X)) :
    (selectFibers r P I).card ≤ P.card := by
  rw [card_eq_sum_fiber, card_eq_sum_fiber P]
  apply Finset.sum_le_sum
  intro j _
  rw [fiber_selectFibers]
  exact selector_card_le_left r (fiber P j) (fiber I j)

theorem selectFibers_card_of_fiber_saturation (r : X → X → Prop)
    (P I : Finset (X × X))
    (hSat : ∀ j, (selector r (fiber P j) (fiber I j)).card = (fiber P j).card) :
    (selectFibers r P I).card = P.card := by
  rw [card_eq_sum_fiber, card_eq_sum_fiber P]
  apply Finset.sum_congr rfl
  intro j _
  rw [fiber_selectFibers, hSat j]

theorem selector_containment (r : X → X → Prop) (P I V C : Finset X)
    (hGeom : ∀ p ∈ P, ∀ i ∈ C, r p i → i ∈ I ∧ p ∈ V) :
    selector r P I ∩ C ⊆ selector r V C := by
  intro i hi
  obtain ⟨hiS, hiC⟩ := Finset.mem_inter.mp hi
  have hiI := selector_subset_right r P I hiS
  have hiInter : i ∈ selector r P (I ∩ C) :=
    selector_restrict_right r P Finset.inter_subset_left
      (Finset.mem_inter.mpr ⟨hiS, Finset.mem_inter.mpr ⟨hiI, hiC⟩⟩)
  have hRight : selector r P C = selector r P (I ∩ C) :=
    selector_remove_isolated_right r P Finset.inter_subset_right
      (fun p hp j hj hr => Finset.mem_inter.mpr ⟨(hGeom p hp j hj hr).1, hj⟩)
  have hLeft : selector r P C = selector r (P ∩ V) C :=
    selector_remove_isolated_left r C Finset.inter_subset_left
      (fun p hp j hj hr => Finset.mem_inter.mpr ⟨hp, (hGeom p hp j hj hr).2⟩)
  have hiCsel : i ∈ selector r P C := by
    rw [hRight]
    exact hiInter
  rw [hLeft] at hiCsel
  exact selector_mono_left r Finset.inter_subset_right hiCsel

end Ordered
end Family173
