import Family173.Transposition

namespace Family173
open OAI.SeymourSecondNeighborhood
open Bipartite Pruning
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Exactly the published admissibility conditions, with no deletion bound included. -/
structure AdmissiblePruning (r : X → X → Prop) (R C R' C' : Finset (X × X)) : Prop where
  subset_left : R' ⊆ R
  subset_right : C' ⊆ C
  no_conflicts : ConflictFree r R' C'
  retain_left : ∀ a ∈ R, (∀ b ∈ C, ¬ Conflict r a b) → a ∈ R'
  retain_right : ∀ b ∈ C, (∀ a ∈ R, ¬ Conflict r a b) → b ∈ C'

def deletions (R C R' C' : Finset (X × X)) : ℕ := (R \ R').card+(C \ C').card
noncomputable def pruningObjective (r : X → X → Prop) (R C R' C' : Finset (X × X)) : ℤ :=
  (deletions R C R' C' : ℤ)-((uncoveredZ r R C R' C').card : ℤ)

theorem canonical_cover_bound (r : X → X → Prop) (R C R' C' : Finset (X × X))
    (hR : R' ⊆ R) (hC : C' ⊆ C) (hFree : ConflictFree r R' C') :
    matchingNumber (AugmentedEdge r R C)+(uncoveredZ r R C R' C').card ≤
      deletions R C R' C'+(Z r R C).card := by
  classical
  let ZL := (Z r R C).filter (fun z => z ∈ rightImage r C')
  let ZR := (Z r R C).filter (fun z => z ∈ leftImage r R')
  let T := (Z r R C).filter (Covered r R' C')
  have hdis : Disjoint ZL ZR := by
    apply Finset.disjoint_left.mpr
    intro z hzL hzR
    obtain ⟨a,ha,haz⟩ := exists_leftCovers_iff.mpr (Finset.mem_filter.mp hzR).2
    obtain ⟨b,hb,hbz⟩ := exists_rightCovers_iff.mpr (Finset.mem_filter.mp hzL).2
    apply hFree a ha b hb
    exact ⟨by rw [hbz.1];exact haz.2,by rw [haz.1];exact hbz.2⟩
  have hunion : ZL ∪ ZR=T := by
    ext z
    simp only [ZL,ZR,T,Covered,Finset.mem_union,Finset.mem_filter]
    tauto
  have hpartition : ZL.card+ZR.card+(uncoveredZ r R C R' C').card=(Z r R C).card := by
    rw [← Finset.card_union_of_disjoint hdis,hunion]
    exact Finset.card_filter_add_card_filter_not (Covered r R' C')
  let A := (liftSet R (R \ R')).disjSum (liftSet (Z r R C) ZL)
  let B := (liftSet C (C \ C')).disjSum (liftSet (Z r R C) ZR)
  have hCover : IsVertexCover (AugmentedEdge r R C) A B := by
    intro a b he
    cases a with
    | inl a =>
      by_cases ha : a.val ∈ R'
      · cases b with
        | inl b =>
          have hb : b.val ∉ C' := fun hb => hFree a.val ha b.val hb he
          right
          exact Finset.inl_mem_disjSum.mpr ((mem_liftSet C _ b).mpr (Finset.mem_sdiff.mpr ⟨b.property,hb⟩))
        | inr z =>
          right
          apply Finset.inr_mem_disjSum.mpr
          apply (mem_liftSet _ _ z).mpr
          exact Finset.mem_filter.mpr ⟨z.property,exists_leftCovers_iff.mp ⟨a.val,ha,he⟩⟩
      · left
        exact Finset.inl_mem_disjSum.mpr ((mem_liftSet R _ a).mpr (Finset.mem_sdiff.mpr ⟨a.property,ha⟩))
    | inr z =>
      cases b with
      | inr _ => exact False.elim he
      | inl b =>
        by_cases hb : b.val ∈ C'
        · left
          apply Finset.inr_mem_disjSum.mpr
          apply (mem_liftSet _ _ z).mpr
          exact Finset.mem_filter.mpr ⟨z.property,exists_rightCovers_iff.mp ⟨b.val,hb,he⟩⟩
        · right
          exact Finset.inl_mem_disjSum.mpr ((mem_liftSet C _ b).mpr (Finset.mem_sdiff.mpr ⟨b.property,hb⟩))
  have hBound := matching_card_le_cover_card (maximumMatching_spec (AugmentedEdge r R C)).1 hCover
  change matchingNumber (AugmentedEdge r R C) ≤ A.card+B.card at hBound
  have hACard : A.card=(R \ R').card+ZL.card := by
    rw [Finset.card_disjSum,liftSet_card R _ Finset.sdiff_subset,
      liftSet_card (Z r R C) ZL (Finset.filter_subset _ _)]
  have hBCard : B.card=(C \ C').card+ZR.card := by
    rw [Finset.card_disjSum,liftSet_card C _ Finset.sdiff_subset,
      liftSet_card (Z r R C) ZR (Finset.filter_subset _ _)]
  rw [hACard,hBCard] at hBound
  unfold deletions
  omega

/- The following construction adapts pinned openai/math CoverPruning.lean,
with its Apache-2.0 attribution retained; it keeps the exact charge instead
of replacing it with the coarser H bound. -/
theorem admissible_pruning_of_cover
    (r : X → X → Prop) (R C : Finset (X × X))
    (A : Finset (LeftVertex r R C)) (B : Finset (RightVertex r R C))
    (hcover : IsVertexCover (AugmentedEdge r R C) A B)
    (hA : ∀ a ∈ A, ∃ b, AugmentedEdge r R C a b)
    (hB : ∀ b ∈ B, ∃ a, AugmentedEdge r R C a b) :
    ∃ R' C', AdmissiblePruning r R C R' C' ∧
      deletions R C R' C'+(Z r R C).card ≤ A.card+B.card+(uncoveredZ r R C R' C').card := by
  classical
  let DR : Finset (X × X) := A.toLeft.image (fun a : R => (a : X × X))
  let DC : Finset (X × X) := B.toLeft.image (fun b : C => (b : X × X))
  let R' : Finset (X × X) := R \ DR
  let C' : Finset (X × X) := C \ DC
  have hDR : DR ⊆ R := by
    intro a ha
    obtain ⟨a', _, rfl⟩ := Finset.mem_image.mp ha
    exact a'.property
  have hDC : DC ⊆ C := by
    intro b hb
    obtain ⟨b', _, rfl⟩ := Finset.mem_image.mp hb
    exact b'.property
  have hR' : R' ⊆ R := Finset.sdiff_subset
  have hC' : C' ⊆ C := Finset.sdiff_subset
  have hsurvL (a : R) (ha : (a : X × X) ∈ R') : Sum.inl a ∉ A := by
    intro haA
    exact (Finset.mem_sdiff.mp ha).2
      (Finset.mem_image_of_mem _ (Finset.mem_toLeft.mpr haA))
  have hsurvR (b : C) (hb : (b : X × X) ∈ C') : Sum.inl b ∉ B := by
    intro hbB
    exact (Finset.mem_sdiff.mp hb).2
      (Finset.mem_image_of_mem _ (Finset.mem_toLeft.mpr hbB))
  have hconflictFree : ConflictFree r R' C' := by
    intro a ha b hb hab
    let a' : R := ⟨a, hR' ha⟩
    let b' : C := ⟨b, hC' hb⟩
    rcases hcover (Sum.inl a') (Sum.inl b') hab with haA | hbB
    · exact hsurvL a' ha haA
    · exact hsurvR b' hb hbB
  have hretainL : ∀ a ∈ R, (∀ b ∈ C, ¬ Conflict r a b) → a ∈ R' := by
    intro a ha hfree
    apply Finset.mem_sdiff.mpr
    refine ⟨ha, ?_⟩
    intro haDR
    obtain ⟨a', haA, hval⟩ := Finset.mem_image.mp haDR
    obtain ⟨b, hab⟩ := hA (Sum.inl a') (Finset.mem_toLeft.mp haA)
    cases b with
    | inl b =>
        change Conflict r (a' : X × X) (b : X × X) at hab
        apply hfree b b.property
        simpa only [hval] using hab
    | inr z =>
        change LeftCovers r (a' : X × X) (z : X × X) at hab
        apply conflictFree_left_not_covers_Z hfree z.property
        simpa only [hval] using hab
  have hretainR : ∀ b ∈ C, (∀ a ∈ R, ¬ Conflict r a b) → b ∈ C' := by
    intro b hb hfree
    apply Finset.mem_sdiff.mpr
    refine ⟨hb, ?_⟩
    intro hbDC
    obtain ⟨b', hbB, hval⟩ := Finset.mem_image.mp hbDC
    obtain ⟨a, hab⟩ := hB (Sum.inl b') (Finset.mem_toLeft.mp hbB)
    cases a with
    | inl a =>
        change Conflict r (a : X × X) (b' : X × X) at hab
        apply hfree a a.property
        simpa only [hval] using hab
    | inr z =>
        change RightCovers r (b' : X × X) (z : X × X) at hab
        apply conflictFree_right_not_covers_Z hfree z.property
        simpa only [hval] using hab
  let T : Finset (X × X) := (Z r R C).filter (Covered r R' C')
  have hcharged : T ⊆ (A.toRight ∪ B.toRight).image
      (fun z : Z r R C => (z : X × X)) := by
    intro z hz
    obtain ⟨hzZ, hzcovered⟩ := Finset.mem_filter.mp hz
    let z' : Z r R C := ⟨z, hzZ⟩
    apply Finset.mem_image.mpr
    refine ⟨z', ?_, rfl⟩
    rcases hzcovered with hzL | hzR
    · obtain ⟨a, ha, haz⟩ := exists_leftCovers_iff.mpr hzL
      let a' : R := ⟨a, hR' ha⟩
      have hzB : Sum.inr z' ∈ B :=
        (hcover (Sum.inl a') (Sum.inr z') haz).resolve_left (hsurvL a' ha)
      exact Finset.mem_union_right _ (Finset.mem_toRight.mpr hzB)
    · obtain ⟨b, hb, hbz⟩ := exists_rightCovers_iff.mpr hzR
      let b' : C := ⟨b, hC' hb⟩
      have hzA : Sum.inr z' ∈ A :=
        (hcover (Sum.inr z') (Sum.inl b') hbz).resolve_right (hsurvR b' hb)
      exact Finset.mem_union_left _ (Finset.mem_toRight.mpr hzA)
  have hTcard : T.card ≤ A.toRight.card + B.toRight.card := by
    calc
      T.card ≤ ((A.toRight ∪ B.toRight).image
          (fun z : Z r R C => (z : X × X))).card := Finset.card_le_card hcharged
      _ = (A.toRight ∪ B.toRight).card :=
        Finset.card_image_of_injective _ Subtype.val_injective
      _ ≤ A.toRight.card + B.toRight.card := Finset.card_union_le _ _
  have hpartition : T.card + (uncoveredZ r R C R' C').card = (Z r R C).card := by
    exact Finset.card_filter_add_card_filter_not
      (s := Z r R C) (Covered r R' C')
  have hdelL : (R \ R').card = A.toLeft.card := by
    change (R \ (R \ DR)).card = A.toLeft.card
    rw [Finset.sdiff_sdiff_eq_self hDR]
    exact Finset.card_image_of_injective _ Subtype.val_injective
  have hdelR : (C \ C').card = B.toLeft.card := by
    change (C \ (C \ DC)).card = B.toLeft.card
    rw [Finset.sdiff_sdiff_eq_self hDC]
    exact Finset.card_image_of_injective _ Subtype.val_injective
  have hAsplit : A.toLeft.card + A.toRight.card = A.card :=
    Finset.card_toLeft_add_card_toRight
  have hBsplit : B.toLeft.card + B.toRight.card = B.card :=
    Finset.card_toLeft_add_card_toRight
  refine ⟨R', C', ⟨hR', hC', hconflictFree, hretainL, hretainR⟩, ?_⟩
  unfold deletions
  rw [hdelL,hdelR]
  omega


theorem pruning_objective_lower (r : X → X → Prop) (R C R' C' : Finset (X × X))
    (h : AdmissiblePruning r R C R' C') :
    (matchingNumber (AugmentedEdge r R C) : ℤ)-((Z r R C).card : ℤ) ≤
      pruningObjective r R C R' C' := by
  have hb := canonical_cover_bound r R C R' C' h.subset_left h.subset_right h.no_conflicts
  have arithmetic (g q d z : ℕ) : g+q≤d+z → (g : ℤ)-(z : ℤ)≤(d : ℤ)-(q : ℤ) := by omega
  exact arithmetic _ _ _ _ hb

theorem exists_admissible_optimal (r : X → X → Prop) (R C : Finset (X × X)) :
    ∃ R' C', AdmissiblePruning r R C R' C' ∧
      pruningObjective r R C R' C' =
        (matchingNumber (AugmentedEdge r R C) : ℤ)-((Z r R C).card : ℤ) := by
  classical
  obtain ⟨A,B,hCover,hCard,hA,hB⟩ := exists_vertexCover_card_eq_of_isMaximumMatching
    (maximumMatching_spec (AugmentedEdge r R C))
  obtain ⟨R',C',hAd,hCharge⟩ := admissible_pruning_of_cover r R C A B hCover hA hB
  change A.card+B.card=matchingNumber (AugmentedEdge r R C) at hCard
  rw [hCard] at hCharge
  have hLower := pruning_objective_lower r R C R' C' hAd
  refine ⟨R',C',hAd,le_antisymm ?_ hLower⟩
  have arithmetic (d z g q : ℕ) : d+z≤g+q → (d : ℤ)-(q : ℤ)≤(g : ℤ)-(z : ℤ) := by omega
  exact arithmetic _ _ _ _ hCharge

/-- Exact minimum semantics: the claimed value is attained and is a lower bound
for every admissible pruning. No truncated subtraction or clipped q occurs. -/
theorem pruning_optimum_identity (r : X → X → Prop) (R C : Finset (X × X)) :
    (∃ R' C', AdmissiblePruning r R C R' C' ∧
      pruningObjective r R C R' C' =
        (matchingNumber (AugmentedEdge r R C) : ℤ)-((Z r R C).card : ℤ)) ∧
    ∀ R' C', AdmissiblePruning r R C R' C' →
      (matchingNumber (AugmentedEdge r R C) : ℤ)-((Z r R C).card : ℤ) ≤
        pruningObjective r R C R' C' :=
  ⟨exists_admissible_optimal r R C,fun R' C' h => pruning_objective_lower r R C R' C' h⟩

theorem exists_beta_pruning (r : X → X → Prop) (R C : Finset (X × X)) :
    ∃ R' C', AdmissiblePruning r R C R' C' ∧
      deletions R C R' C' ≤
        min (matchingNumber (B0 r R (H r R C))) (matchingNumber (A0 r (H r R C) C)) +
          (uncoveredZ r R C R' C').card := by
  obtain ⟨R',C',hAd,hObj⟩ := exists_admissible_optimal r R C
  have hCapacity := matching_capacity r R C
  refine ⟨R',C',hAd,?_⟩
  have arithmetic (d q g z b : ℕ) : (d : ℤ)-(q : ℤ)=(g : ℤ)-(z : ℤ) →
      g≤z+b → d≤b+q := by omega
  exact arithmetic _ _ _ _ _ hObj hCapacity

end Family173
