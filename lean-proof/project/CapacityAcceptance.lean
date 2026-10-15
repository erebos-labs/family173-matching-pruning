import Family173.Transposition
import IndependentAcceptance

open OAI.SeymourSecondNeighborhood
open Bipartite

/-- Exactly the full matching-capacity inequality, with literal graph relations,
original conflict corners, separate Sum tags and no auxiliary premise. -/
theorem exact_published_matching_capacity {X : Type*} [Fintype X] [DecidableEq X]
    (r : X → X → Prop) (R C : Finset (X × X)) :
    Family173.matchingNumber
      (fun (a : ↥R ⊕ ↥(FinalAudit.Znote r R C))
           (b : ↥C ⊕ ↥(FinalAudit.Znote r R C)) =>
        match a,b with
        | Sum.inl w,Sum.inl c => r w.val.1 c.val.1 ∧ r c.val.2 w.val.2
        | Sum.inl w,Sum.inr z => w.val.2=z.val.2 ∧ r w.val.1 z.val.1
        | Sum.inr z,Sum.inl c => c.val.1=z.val.1 ∧ r c.val.2 z.val.2
        | Sum.inr _,Sum.inr _ => False) ≤
      (FinalAudit.Znote r R C).card +
        min (Family173.matchingNumber
          (fun (w : R) (h : FinalAudit.Hnote r R C) => w.val.1=h.val.1 ∧ r h.val.2 w.val.2))
          (Family173.matchingNumber
          (fun (h : FinalAudit.Hnote r R C) (c : C) => h.val.2=c.val.2 ∧ r h.val.1 c.val.1)) :=
  Family173.matching_capacity r R C

/-- CC's full residual corollary, with an ordinary signed-integer budget. -/
theorem exact_generalized_residual {X : Type*} [Fintype X] [DecidableEq X]
    (r : X → X → Prop) (R C W : Finset (X × X)) (hW : W ⊆ R)
    (α : Finset (↥W × ↥(FinalAudit.Znote r R C)))
    (hα : IsMatching (fun (w : W) (z : FinalAudit.Znote r R C) =>
      w.val.2=z.val.2 ∧ r w.val.1 z.val.1) α)
    (hSat : leftVertices α=Finset.univ) :
    ((Family173.matchingNumber (fun (w : W) (h : FinalAudit.Hnote r R C) =>
      w.val.1=h.val.1 ∧ r h.val.2 w.val.2) : ℕ) : ℤ) ≥
      (W.card : ℤ) +
        ((Family173.matchingNumber (fun (z : FinalAudit.Znote r R C) (c : C) =>
          c.val.1=z.val.1 ∧ r c.val.2 z.val.2) : ℕ) : ℤ) -
        ((FinalAudit.Znote r R C).card : ℤ) := by
  have h := Family173.generalized_residual_bound r R C W hW α hα hSat
  have arithmetic (n w z b : ℕ) : n+w≤z+b → (b : ℤ)≥(w : ℤ)+(n : ℤ)-(z : ℤ) := by omega
  exact arithmetic _ _ _ _ h

#print exact_published_matching_capacity
#print exact_generalized_residual
#print axioms exact_published_matching_capacity
#print axioms exact_generalized_residual
