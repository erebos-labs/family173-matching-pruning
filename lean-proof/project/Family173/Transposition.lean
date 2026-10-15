import Family173.CapacityCover
import Family173.MatchingMaps
namespace Family173
open OAI.SeymourSecondNeighborhood
open Bipartite Pruning
variable {X : Type*} [Fintype X] [DecidableEq X]

def tau (S : Finset (X × X)) : Finset (X × X) := S.image Prod.swap
@[simp] theorem mem_tau (S : Finset (X × X)) (a : X × X) : a ∈ tau S ↔ a.swap ∈ S := by
  constructor
  · intro h
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp h
    simpa using hb
  · intro h
    exact Finset.mem_image.mpr ⟨a.swap,h,by simp⟩
theorem tau_card (S : Finset (X × X)) : (tau S).card=S.card := by
  apply Finset.card_image_of_injective
  intro a b h
  simpa using congrArg Prod.swap h

theorem transpose_Z (r : X → X → Prop) (R C : Finset (X × X)) :
    Pruning.Z r (tau C) (tau R)=tau (Pruning.Z r R C) := by
  ext z
  simp only [Pruning.mem_Z,mem_tau]
  constructor
  · rintro ⟨p,s,hp,hs,hpi,hsj⟩
    exact ⟨s,p,hs,hp,hsj,hpi⟩
  · rintro ⟨p,s,hp,hs,hpi,hsj⟩
    exact ⟨s,p,hs,hp,hsj,hpi⟩

theorem transpose_H (r : X → X → Prop) (R C : Finset (X × X)) :
    Pruning.H r (tau C) (tau R)=tau (Pruning.H r R C) := by
  ext h
  simp only [Pruning.mem_H,mem_tau]
  constructor
  · rintro ⟨i,j,hR,hC,hpi,hsj⟩
    exact ⟨j,i,hC,hR,hsj,hpi⟩
  · rintro ⟨i,j,hR,hC,hpi,hsj⟩
    exact ⟨j,i,hC,hR,hsj,hpi⟩

def toTau (S : Finset (X × X)) (a : S) : tau S :=
  ⟨a.val.swap,(mem_tau S _).mpr (by simpa using a.property)⟩
def fromTau (S : Finset (X × X)) (a : tau S) : S :=
  ⟨a.val.swap,(mem_tau S _).mp a.property⟩
theorem toTau_injective (S : Finset (X × X)) : Function.Injective (toTau S) := by
  intro a b h
  apply Subtype.ext
  have h' := congrArg (fun x : tau S => x.val.swap) h
  simpa [toTau] using h'
theorem fromTau_injective (S : Finset (X × X)) : Function.Injective (fromTau S) := by
  intro a b h
  apply Subtype.ext
  have h' := congrArg (fun x : S => x.val.swap) h
  simpa [fromTau] using h'

noncomputable def toTauZ (r : X → X → Prop) (R C : Finset (X × X))
    (z : Pruning.Z r R C) : Pruning.Z r (tau C) (tau R) :=
  ⟨z.val.swap,by rw [transpose_Z]; exact (toTau (Pruning.Z r R C) z).property⟩
theorem toTauZ_injective (r : X → X → Prop) (R C : Finset (X × X)) :
    Function.Injective (toTauZ r R C) := by
  intro a b h
  apply Subtype.ext
  have h' := congrArg (fun z : Pruning.Z r (tau C) (tau R) => z.val.swap) h
  simpa [toTauZ] using h'

theorem sum_map_injective {A B C D : Type*} (f : A → C) (g : B → D)
    (hf : Function.Injective f) (hg : Function.Injective g) : Function.Injective (Sum.map f g) := by
  intro a b h
  cases a <;> cases b
  · exact congrArg Sum.inl (hf (Sum.inl.inj h))
  · cases h
  · cases h
  · exact congrArg Sum.inr (hg (Sum.inr.inj h))

/-- The input relation is unchanged; only coordinate roles and bipartition sides swap. -/
theorem gamma_transpose_le (r : X → X → Prop) (R C : Finset (X × X)) :
    matchingNumber (AugmentedEdge r R C) ≤ matchingNumber (AugmentedEdge r (tau C) (tau R)) := by
  apply matchingNumber_le_flip
    (Sum.map (toTau R) (toTauZ r R C)) (Sum.map (toTau C) (toTauZ r R C))
    (sum_map_injective _ _ (toTau_injective R) (toTauZ_injective r R C))
    (sum_map_injective _ _ (toTau_injective C) (toTauZ_injective r R C))
  intro l c he
  cases l <;> cases c
  · exact ⟨he.2,he.1⟩
  · exact ⟨he.1,he.2⟩
  · exact ⟨he.1,he.2⟩
  · exact False.elim he

def A0 (r : X → X → Prop) (H C : Finset (X × X)) (h : H) (c : C) : Prop :=
  h.val.2=c.val.2 ∧ r h.val.1 c.val.1

noncomputable def fromTauH (r : X → X → Prop) (R C : Finset (X × X))
    (h : Pruning.H r (tau C) (tau R)) : Pruning.H r R C :=
  ⟨h.val.swap,by
    have hh : h.val ∈ tau (Pruning.H r R C) :=
      Eq.mp (congrArg (fun S : Finset (X × X) => h.val ∈ S) (transpose_H r R C)) h.property
    exact (mem_tau _ _).mp hh⟩
theorem fromTauH_injective (r : X → X → Prop) (R C : Finset (X × X)) :
    Function.Injective (fromTauH r R C) := by
  intro a b h
  apply Subtype.ext
  have h' := congrArg (fun z : Pruning.H r R C => z.val.swap) h
  simpa [fromTauH] using h'

theorem B_transpose_le_A (r : X → X → Prop) (R C : Finset (X × X)) :
    matchingNumber (B0 r (tau C) (Pruning.H r (tau C) (tau R))) ≤
      matchingNumber (A0 r (Pruning.H r R C) C) := by
  apply matchingNumber_le_flip (fromTau C) (fromTauH r R C)
    (fromTau_injective C) (fromTauH_injective r R C)
  intro c h he
  exact ⟨he.1.symm,he.2⟩

theorem capacity_A (r : X → X → Prop) (R C : Finset (X × X)) :
    matchingNumber (AugmentedEdge r R C) ≤ (Pruning.Z r R C).card +
      matchingNumber (A0 r (Pruning.H r R C) C) := by
  have hG := gamma_transpose_le r R C
  have hB := capacity_B r (tau C) (tau R)
  have hA := B_transpose_le_A r R C
  have hZ : (Pruning.Z r (tau C) (tau R)).card=(Pruning.Z r R C).card := by
    rw [transpose_Z,tau_card]
  omega

theorem matching_capacity (r : X → X → Prop) (R C : Finset (X × X)) :
    matchingNumber (AugmentedEdge r R C) ≤ (Pruning.Z r R C).card +
      min (matchingNumber (B0 r R (Pruning.H r R C)))
        (matchingNumber (A0 r (Pruning.H r R C) C)) := by
  have hB := capacity_B r R C
  have hA := capacity_A r R C
  omega
end Family173
