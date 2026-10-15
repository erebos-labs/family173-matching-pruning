import Family173.IndexedMatching
import Mathlib.Data.Fintype.Option

namespace Family173
open OAI.SeymourSecondNeighborhood
open Bipartite Pruning
namespace Sharp

/-- Parameter k represents the published family size n=k+1 >= 1. -/
abbrev X (k : ℕ) := (Unit ⊕ Unit) ⊕ (Fin (k+1) ⊕ Fin (k+1))
def i (k : ℕ) : X k := Sum.inl (Sum.inl ())
def j (k : ℕ) : X k := Sum.inl (Sum.inr ())
def p {k : ℕ} (a : Fin (k+1)) : X k := Sum.inr (Sum.inl a)
def s {k : ℕ} (b : Fin (k+1)) : X k := Sum.inr (Sum.inr b)
def edge (k : ℕ) (x y : X k) : Prop :=
  (∃ a, x=p a ∧ y=i k) ∨ (∃ b, x=s b ∧ y=j k)
def R (k : ℕ) : Finset (X k × X k) := Finset.univ.image (fun a => (p a,j k))
def C (k : ℕ) : Finset (X k × X k) := Finset.univ.image (fun b => (i k,s b))

theorem R_card (k : ℕ) : (R k).card=k+1 := by
  have h : Function.Injective (fun (a : Fin (k+1)) => (p a,j k)) := by
    intro a b h
    simpa [p] using congrArg Prod.fst h
  rw [R,Finset.card_image_of_injective _ h]
  simp

theorem C_card (k : ℕ) : (C k).card=k+1 := by
  have h : Function.Injective (fun (b : Fin (k+1)) => (i k,s b)) := by
    intro a b h
    simpa [s] using congrArg Prod.snd h
  rw [C,Finset.card_image_of_injective _ h]
  simp

theorem Z_eq (k : ℕ) : Z (edge k) (R k) (C k) = {(i k,j k)} := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨q,t,hR,hC,_,_⟩ := mem_Z.mp hz
    obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hR
    obtain ⟨b,_,hb⟩ := Finset.mem_image.mp hC
    exact Finset.mem_singleton.mpr (Prod.ext (congrArg Prod.fst hb).symm (congrArg Prod.snd ha).symm)
  · intro hz
    have heq := Finset.mem_singleton.mp hz
    subst z
    apply mem_Z.mpr
    exact ⟨p (0 : Fin (k+1)),s (0 : Fin (k+1)),
      Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩,
      Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩,by simp [edge,p,s,i,j],by simp [edge,p,s,i,j]⟩

theorem H_eq (k : ℕ) : H (edge k) (R k) (C k) =
    (Finset.univ : Finset (Fin (k+1) × Fin (k+1))).image (fun ab => (p ab.1,s ab.2)) := by
  classical
  ext h
  constructor
  · intro hh
    obtain ⟨u,v,hR,hC,_,_⟩ := mem_H.mp hh
    obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hR
    obtain ⟨b,_,hb⟩ := Finset.mem_image.mp hC
    have hpa : p a=h.1 := congrArg Prod.fst ha
    have hsb : s b=h.2 := congrArg Prod.snd hb
    exact Finset.mem_image.mpr ⟨(a,b),Finset.mem_univ _,Prod.ext hpa hsb⟩
  · intro hh
    obtain ⟨ab,_,rfl⟩ := Finset.mem_image.mp hh
    apply mem_H.mpr
    exact ⟨i k,j k,Finset.mem_image.mpr ⟨ab.1,Finset.mem_univ _,rfl⟩,
      Finset.mem_image.mpr ⟨ab.2,Finset.mem_univ _,rfl⟩,
      by simp [edge,p,s,i,j],by simp [edge,p,s,i,j]⟩

theorem Z_card (k : ℕ) : (Z (edge k) (R k) (C k)).card=1 := by rw [Z_eq,Finset.card_singleton]
theorem H_card (k : ℕ) : (H (edge k) (R k) (C k)).card=(k+1)*(k+1) := by
  have h : Function.Injective (fun (ab : Fin (k+1) × Fin (k+1)) => (p ab.1,s ab.2)) := by
    intro a b he
    exact Prod.ext (by simpa [p] using congrArg Prod.fst he) (by simpa [s] using congrArg Prod.snd he)
  rw [H_eq,Finset.card_image_of_injective _ h]
  simp

def ra (k : ℕ) (a : Fin (k+1)) : R k :=
  ⟨(p a,j k),Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩⟩
def cb (k : ℕ) (b : Fin (k+1)) : C k :=
  ⟨(i k,s b),Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩⟩
noncomputable def hab (k : ℕ) (a b : Fin (k+1)) : H (edge k) (R k) (C k) :=
  ⟨(p a,s b),by rw [H_eq];exact Finset.mem_image.mpr ⟨(a,b),Finset.mem_univ _,rfl⟩⟩
noncomputable def z (k : ℕ) : Z (edge k) (R k) (C k) :=
  ⟨(i k,j k),by rw [Z_eq];exact Finset.mem_singleton_self _⟩
theorem ra_injective (k : ℕ) : Function.Injective (ra k) := by
  intro a b h
  simpa [ra,p] using congrArg (fun w : R k => w.val.1) h
theorem cb_injective (k : ℕ) : Function.Injective (cb k) := by
  intro a b h
  simpa [cb,s] using congrArg (fun w : C k => w.val.2) h

theorem B_number (k : ℕ) : matchingNumber (B0 (edge k) (R k) (H (edge k) (R k) (C k)))=k+1 := by
  apply Nat.le_antisymm
  · have h := matchingNumber_le_card_left (B0 (edge k) (R k) (H (edge k) (R k) (C k)))
    simpa only [Fintype.card_coe,R_card] using h
  · have hLower := indexed_matching_lower (B0 (edge k) (R k) (H (edge k) (R k) (C k)))
      (ra k) (fun a => hab k a 0) (ra_injective k)
      (by
        intro a b h
        simpa [hab,p] using congrArg (fun w : H (edge k) (R k) (C k) => w.val.1) h)
      (by
        intro a
        exact ⟨rfl,by simp [edge,ra,hab,p,s,i,j]⟩)
    simpa only [Fintype.card_fin] using hLower

theorem A_number (k : ℕ) : matchingNumber (A0 (edge k) (H (edge k) (R k) (C k)) (C k))=k+1 := by
  apply Nat.le_antisymm
  · have h := matchingNumber_le_card_right (A0 (edge k) (H (edge k) (R k) (C k)) (C k))
    simpa only [Fintype.card_coe,C_card] using h
  · have hLower := indexed_matching_lower (A0 (edge k) (H (edge k) (R k) (C k)) (C k))
      (fun b => hab k 0 b) (cb k)
      (by
        intro a b h
        simpa [hab,s] using congrArg (fun w : H (edge k) (R k) (C k) => w.val.2) h)
      (cb_injective k)
      (by
        intro b
        exact ⟨rfl,by simp [edge,cb,hab,p,s,i,j]⟩)
    simpa only [Fintype.card_fin] using hLower

noncomputable def gammaLeft (k : ℕ) : Option (Fin (k+1)) → LeftVertex (edge k) (R k) (C k)
  | none => Sum.inr (z k)
  | some a => Sum.inl (ra k a)
noncomputable def gammaRight (k : ℕ) : Option (Fin (k+1)) → RightVertex (edge k) (R k) (C k)
  | none => Sum.inl (cb k 0)
  | some a => if a=0 then Sum.inr (z k) else Sum.inl (cb k a)

theorem gammaLeft_injective (k : ℕ) : Function.Injective (gammaLeft k) := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b => cases h
  | some a =>
    cases b with
    | none => cases h
    | some b => exact congrArg some (ra_injective k (Sum.inl.inj h))

theorem gammaRight_injective (k : ℕ) : Function.Injective (gammaRight k) := by
  classical
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      by_cases hb : b=0
      · simp [gammaRight,hb] at h
      · have h0b : (0 : Fin (k+1))=b := cb_injective k (by simpa [gammaRight,hb] using h)
        exact False.elim (hb h0b.symm)
  | some a =>
    cases b with
    | none =>
      by_cases ha : a=0
      · simp [gammaRight,ha] at h
      · have ha0 : a=(0 : Fin (k+1)) := cb_injective k (by simpa [gammaRight,ha] using h)
        exact False.elim (ha ha0)
    | some b =>
      by_cases ha : a=0
      · by_cases hb : b=0
        · exact congrArg some (ha.trans hb.symm)
        · simp [gammaRight,ha,hb] at h
      · by_cases hb : b=0
        · simp [gammaRight,ha,hb] at h
        · exact congrArg some (cb_injective k (by simpa [gammaRight,ha,hb] using h))

theorem gamma_matching_edges (k : ℕ) (a : Option (Fin (k+1))) :
    AugmentedEdge (edge k) (R k) (C k) (gammaLeft k a) (gammaRight k a) := by
  classical
  cases a with
  | none => exact ⟨rfl,by simp [edge,cb,z,p,s,i,j]⟩
  | some a =>
    by_cases ha : a=0
    · simp [gammaLeft,gammaRight,ha,AugmentedEdge,LeftCovers,ra,z,edge,p,s,i,j]
    · simp [gammaLeft,gammaRight,ha,AugmentedEdge,Conflict,ra,cb,edge,p,s,i,j]

theorem Gamma_number (k : ℕ) : matchingNumber (AugmentedEdge (edge k) (R k) (C k))=(k+1)+1 := by
  classical
  have hLower := indexed_matching_lower (AugmentedEdge (edge k) (R k) (C k))
    (gammaLeft k) (gammaRight k) (gammaLeft_injective k) (gammaRight_injective k) (gamma_matching_edges k)
  have hUpper := matching_capacity (edge k) (R k) (C k)
  rw [Z_card,B_number,A_number,min_self] at hUpper
  simp only [Fintype.card_option,Fintype.card_fin] at hLower
  omega

theorem no_two_step (k : ℕ) (x y w : X k) (hxy : edge k x y) : ¬ edge k y w := by
  rcases hxy with ⟨a,_,rfl⟩ | ⟨b,_,rfl⟩ <;> simp [edge,i,j,p,s]

theorem oriented (k : ℕ) : IsOriented (edge k) := by
  refine ⟨?_,?_⟩
  · intro x hx
    exact no_two_step k x x x hx hx
  · intro x y hxy hyx
    exact no_two_step k x y x hxy hyx

theorem optimum_value (k : ℕ) :
    (∃ R' C', AdmissiblePruning (edge k) (R k) (C k) R' C' ∧
      pruningObjective (edge k) (R k) (C k) R' C' = ((k+1 : ℕ) : ℤ)) ∧
    ∀ R' C', AdmissiblePruning (edge k) (R k) (C k) R' C' →
      ((k+1 : ℕ) : ℤ) ≤ pruningObjective (edge k) (R k) (C k) R' C' := by
  have h := pruning_optimum_identity (edge k) (R k) (C k)
  have hValue : (matchingNumber (AugmentedEdge (edge k) (R k) (C k)) : ℤ)-
      ((Z (edge k) (R k) (C k)).card : ℤ)=((k+1 : ℕ) : ℤ) := by
    rw [Gamma_number,Z_card]
    omega
  rw [hValue] at h
  exact h

theorem pruning_lower_natural (k : ℕ) (R' C' : Finset (X k × X k))
    (hAd : AdmissiblePruning (edge k) (R k) (C k) R' C') :
    (k+1)+(uncoveredZ (edge k) (R k) (C k) R' C').card ≤ deletions (R k) (C k) R' C' := by
  have h := (optimum_value k).2 R' C' hAd
  change ((k+1 : ℕ) : ℤ) ≤ (deletions (R k) (C k) R' C' : ℤ)-
    ((uncoveredZ (edge k) (R k) (C k) R' C').card : ℤ) at h
  omega

end Sharp
end Family173
