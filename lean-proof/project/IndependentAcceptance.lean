import Acceptance

namespace FinalAudit
open OAI.SeymourSecondNeighborhood
open Bipartite
variable {X : Type*} [Fintype X] [DecidableEq X]
noncomputable def Znote (r : X → X → Prop) (R C : Finset (X × X)) : Finset (X × X) := by
  classical
  exact Finset.univ.filter (fun z => ∃ p s, (p,z.2) ∈ R ∧ (z.1,s) ∈ C ∧ r p z.1 ∧ r s z.2)
noncomputable def Hnote (r : X → X → Prop) (R C : Finset (X × X)) : Finset (X × X) := by
  classical
  exact Finset.univ.filter (fun h => ∃ i j, (h.1,j) ∈ R ∧ (i,h.2) ∈ C ∧ r h.1 i ∧ r h.2 j)
theorem Znote_eq (r : X → X → Prop) (R C : Finset (X × X)) : Znote r R C = Pruning.Z r R C := rfl
theorem Hnote_eq (r : X → X → Prop) (R C : Finset (X × X)) : Hnote r R C = Pruning.H r R C := rfl

/-- Independent spelling of NOTE section 1, without the Family173 statement or relation wrappers. -/
theorem independent_CC (r : X → X → Prop) (R C W : Finset (X × X)) (hW : W ⊆ R)
    (α : Finset (↥W × ↥(Znote r R C)))
    (hα : (∀ e ∈ α, e.1.val.2 = e.2.val.2 ∧ r e.1.val.1 e.2.val.1) ∧
      Set.InjOn Prod.fst (α : Set (↥W × ↥(Znote r R C))) ∧ Set.InjOn Prod.snd (α : Set (↥W × ↥(Znote r R C))))
    (hSat : α.image Prod.fst = Finset.univ)
    (U : Finset ↥W) (V : Finset ↥(Hnote r R C))
    (hKB : ∀ (w : W) (h : Hnote r R C),
      w.val.1 = h.val.1 ∧ r h.val.2 w.val.2 → w ∈ U ∨ h ∈ V) :
    ∃ A : Finset ↥(Znote r R C), ∃ D : Finset ↥C,
      (∀ (z : Znote r R C) (c : C),
        c.val.1 = z.val.1 ∧ r c.val.2 z.val.2 → z ∈ A ∨ c ∈ D) ∧
      ((A.card : ℤ) + (D.card : ℤ)) ≤
        ((Znote r R C).card : ℤ) - (W.card : ℤ) + (U.card : ℤ) + (V.card : ℤ) := by
  obtain ⟨A,D,hN,hB⟩ := exact_published_CC r R C W hW α hα hSat U V hKB
  have convert_budget (a d z w u v : ℕ) :
      ((a+d : ℕ) : ℤ) ≤ (z : ℤ) - (w : ℤ) + ((u+v : ℕ) : ℤ) →
      (a : ℤ) + (d : ℤ) ≤ (z : ℤ) - (w : ℤ) + (u : ℤ) + (v : ℤ) := by omega
  exact ⟨A,D,hN,convert_budget A.card D.card (Znote r R C).card W.card U.card V.card hB⟩

#print independent_CC
#print axioms independent_CC
#print axioms Znote_eq
#print axioms Hnote_eq
end FinalAudit
