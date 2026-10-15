import Family173.FiberMatching
import Family173.SubtypeSets

namespace Family173
open OAI.SeymourSecondNeighborhood
open Bipartite

variable {X : Type*} [Fintype X] [DecidableEq X]

section Ordered
variable [LinearOrder X]

/-- The full shared-order construction, with no minimum-cover or maximum-alpha premise. -/
theorem cover_conversion_of_order (r : X → X → Prop) (R C : Finset (X × X)) :
    CoverConversionStatement r R C := by
  classical
  intro W hWR α hα hSat U V hCover
  let Uraw := rawSet U
  let Vraw := rawSet V
  let W' := W \ Uraw
  let Z := Pruning.Z r R C
  let Q := selectFibers r W' Z
  let D := selectFibers r Vraw C
  let A := Z \ Q
  have hUsub : Uraw ⊆ W := rawSet_subset U
  have hW'sub : W' ⊆ W := Finset.sdiff_subset
  have hQsub : Q ⊆ Z := selectFibers_subset r W' Z
  have hDsub : D ⊆ C := selectFibers_subset r Vraw C
  have hAsub : A ⊆ Z := Finset.sdiff_subset
  have hQcard : Q.card = W'.card := selected_corners_card r W Z W' α hα hSat hW'sub
  have hDcard : D.card ≤ V.card := by
    have h := selectFibers_card_le r Vraw C
    change D.card ≤ (rawSet V).card at h
    rw [rawSet_card V] at h
    exact h
  have hW'card : W'.card + U.card = W.card := by
    have h := Finset.card_sdiff_add_card_eq_card hUsub
    change W'.card + (rawSet U).card = W.card at h
    rw [rawSet_card U] at h
    exact h
  have hAcard : A.card + Q.card = Z.card := Finset.card_sdiff_add_card_eq_card hQsub
  have hContain : ∀ j s, r s j →
      selector r (fiber W' j) (fiber Z j) ∩ fiber C s ⊆
        selector r (fiber Vraw s) (fiber C s) := by
    intro j s hsj
    apply selector_containment
    intro p hp i hi hpi
    have hpW' := (mem_fiber W' j p).mp hp
    obtain ⟨hpW, hpU⟩ := Finset.mem_sdiff.mp hpW'
    let w : W := ⟨(p, j), hpW⟩
    let c : C := ⟨(i, s), (mem_fiber C s i).mp hi⟩
    have hwU : w ∉ U := by
      intro h
      exact hpU ((mem_rawSet U (p, j)).mpr ⟨w, h, rfl⟩)
    have hCorners := original_conflict_corners r R C W hWR w c hpi hsj
    obtain ⟨h, hhV, hpair⟩ :=
      cover_forces_original_H_corner r R C W hWR U V hCover w c hwU hpi hsj
    have hpV : (p, s) ∈ Vraw := (mem_rawSet V (p, s)).mpr ⟨h, hhV, hpair⟩
    exact ⟨(mem_fiber Z j i).mpr hCorners.1, (mem_fiber Vraw s p).mpr hpV⟩
  refine ⟨liftSet Z A, liftSet C D, ?_, ?_⟩
  · intro z c hN
    by_cases hzQ : z.val ∈ Q
    · right
      apply (mem_liftSet C D c).mpr
      have hzSel : z.val.1 ∈ selector r (fiber W' z.val.2) (fiber Z z.val.2) :=
        (mem_selectFibers r W' Z z.val).mp hzQ
      have hcFiber : z.val.1 ∈ fiber C c.val.2 := by
        apply (mem_fiber C c.val.2 z.val.1).mpr
        have hpair : (z.val.1, c.val.2) = c.val := Prod.ext hN.1.symm rfl
        rw [hpair]
        exact c.property
      have hPicked := hContain z.val.2 c.val.2 hN.2
        (Finset.mem_inter.mpr ⟨hzSel, hcFiber⟩)
      apply (mem_selectFibers r Vraw C c.val).mpr
      rw [hN.1]
      exact hPicked
    · left
      apply (mem_liftSet Z A z).mpr
      exact Finset.mem_sdiff.mpr ⟨z.property, hzQ⟩
  · rw [liftSet_card Z A hAsub, liftSet_card C D hDsub]
    change A.card + D.card + W.card ≤ Z.card + U.card + V.card
    omega

end Ordered

/-- The published CC statement for any finite X and any binary relation. -/
theorem cover_conversion (r : X → X → Prop) (R C : Finset (X × X)) :
    CoverConversionStatement r R C := by
  classical
  letI : LinearOrder X := LinearOrder.lift' (Fintype.equivFin X) (Fintype.equivFin X).injective
  exact cover_conversion_of_order r R C

end Family173
