import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Powerset

namespace Family173
variable {Y : Type*} [DecidableEq Y]

noncomputable def rawSet {T : Finset Y} (S : Finset ↥T) : Finset Y := by
  classical
  exact S.image Subtype.val

theorem rawSet_subset {T : Finset Y} (S : Finset ↥T) : rawSet S ⊆ T := by
  classical
  intro y hy
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
  exact s.property

theorem rawSet_card {T : Finset Y} (S : Finset ↥T) : (rawSet S).card = S.card := by
  classical
  apply Finset.card_image_of_injective
  exact Subtype.val_injective

theorem mem_rawSet {T : Finset Y} (S : Finset ↥T) (y : Y) :
    y ∈ rawSet S ↔ ∃ s ∈ S, s.val = y := by
  classical
  exact Finset.mem_image

noncomputable def liftSet (T S : Finset Y) : Finset ↥T := by
  classical
  exact Finset.univ.filter (fun t => t.val ∈ S)

theorem mem_liftSet (T S : Finset Y) (t : T) : t ∈ liftSet T S ↔ t.val ∈ S := by
  classical
  simp [liftSet]

theorem rawSet_liftSet (T S : Finset Y) (hS : S ⊆ T) : rawSet (liftSet T S) = S := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨t, ht, hty⟩ := (mem_rawSet _ _).mp hy
    have htS := (mem_liftSet T S t).mp ht
    rw [hty] at htS
    exact htS
  · intro hy
    let t : T := ⟨y, hS hy⟩
    exact (mem_rawSet _ _).mpr ⟨t, (mem_liftSet T S t).mpr hy, rfl⟩

theorem liftSet_card (T S : Finset Y) (hS : S ⊆ T) : (liftSet T S).card = S.card := by
  have h := rawSet_card (liftSet T S)
  rw [rawSet_liftSet T S hS] at h
  exact h.symm

end Family173
