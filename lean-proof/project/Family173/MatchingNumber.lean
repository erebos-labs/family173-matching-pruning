import OAI.Combinatorics.SecondNeighborhood.MatchingExchange

namespace Family173

open OAI.SeymourSecondNeighborhood.Bipartite

variable {L R : Type*} [Fintype L] [Fintype R]

noncomputable def maximumMatching (E : L → R → Prop) : Finset (L × R) :=
  Classical.choose (exists_maximum_matching E)

theorem maximumMatching_spec (E : L → R → Prop) :
    IsMaximumMatching E (maximumMatching E) :=
  Classical.choose_spec (exists_maximum_matching E)

noncomputable def matchingNumber (E : L → R → Prop) : ℕ :=
  (maximumMatching E).card

theorem matching_card_le_number {E : L → R → Prop} {M : Finset (L × R)}
    (hM : IsMatching E M) : M.card ≤ matchingNumber E :=
  (maximumMatching_spec E).2 M hM

theorem matchingNumber_mono {E F : L → R → Prop}
    (hEF : ∀ l r, E l r → F l r) : matchingNumber E ≤ matchingNumber F :=
  matching_card_le_number ((maximumMatching_spec E).1.mono_relation hEF)

section DecidableEq
variable [DecidableEq L] [DecidableEq R]

omit [Fintype L] [Fintype R] in
theorem matching_swap {E : L → R → Prop} {M : Finset (L × R)}
    (hM : IsMatching E M) : IsMatching (fun r l => E l r) (M.image Prod.swap) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    exact hM.1 a ha
  · intro e he f hf h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hf
    exact congrArg Prod.swap (hM.2.2 ha hb h)
  · intro e he f hf h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hf
    exact congrArg Prod.swap (hM.2.1 ha hb h)

omit [Fintype L] [Fintype R] in
theorem swap_card (M : Finset (L × R)) : (M.image Prod.swap).card = M.card := by
  apply Finset.card_image_of_injective
  intro a b h
  simpa using congrArg Prod.swap h

/-- Transposed upstream exchange preserves right endpoints, not original edges. -/
theorem exists_matching_saturating_right {E : L → R → Prop}
    {M N : Finset (L × R)} (hM : IsMatching E M) (hN : IsMatching E N)
    (hcard : M.card < N.card) :
    ∃ Q : Finset (L × R), IsMatching E Q ∧ Q.card = N.card ∧
      rightVertices M ⊆ rightVertices Q := by
  obtain ⟨Q, hQ, hQcard, hQM⟩ :=
    exists_matching_saturating_left_of_card_lt (matching_swap hM) (matching_swap hN)
      (by simpa only [swap_card] using hcard)
  refine ⟨Q.image Prod.swap, ?_, ?_, ?_⟩
  · simpa only [Finset.image_image, Prod.swap_swap_eq, Finset.image_id] using
      matching_swap hQ
  · simpa only [swap_card] using hQcard
  · simpa [rightVertices, Finset.image_image, Function.comp_def] using hQM

end DecidableEq

section Restricted
variable {X : Type*} [Fintype X] [DecidableEq X]

def restricted (r : X → X → Prop) (P I : Finset X) (p i : X) : Prop :=
  p ∈ P ∧ i ∈ I ∧ r p i

noncomputable def nu (r : X → X → Prop) (P I : Finset X) : ℕ :=
  matchingNumber (restricted r P I)

omit [DecidableEq X] in
theorem nu_mono (r : X → X → Prop) {P P' I I' : Finset X}
    (hP : P ⊆ P') (hI : I ⊆ I') : nu r P I ≤ nu r P' I' :=
  matchingNumber_mono fun _ _ h => ⟨hP h.1, hI h.2.1, h.2.2⟩

omit [DecidableEq X] in
theorem nu_empty_right (r : X → X → Prop) (P : Finset X) : nu r P ∅ = 0 := by
  classical
  let M := maximumMatching (restricted r P ∅)
  have hM : IsMatching (restricted r P ∅) M := (maximumMatching_spec _).1
  have hEmpty : M = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro e he
    simpa using (hM.1 e he).2.1
  change M.card = 0
  rw [hEmpty, Finset.card_empty]

theorem nu_card_le_left (r : X → X → Prop) (P I : Finset X) : nu r P I ≤ P.card := by
  classical
  let M := maximumMatching (restricted r P I)
  have hM : IsMatching (restricted r P I) M := (maximumMatching_spec _).1
  have hsub : leftVertices M ⊆ P := by
    intro p hp
    obtain ⟨i, hi⟩ := mem_leftVertices.mp hp
    exact (hM.1 (p, i) hi).1
  have h := Finset.card_le_card hsub
  rw [matching_card_leftVertices hM] at h
  exact h

theorem nu_eq_card_of_saturation (r : X → X → Prop) (P I : Finset X)
    {M : Finset (X × X)} (hM : IsMatching (restricted r P I) M)
    (hSat : leftVertices M = P) : nu r P I = P.card := by
  have hc := matching_card_leftVertices hM
  rw [hSat] at hc
  have hlo : M.card ≤ nu r P I := matching_card_le_number hM
  have hhi := nu_card_le_left r P I
  omega

theorem nu_remove_isolated_left (r : X → X → Prop) (I : Finset X)
    {P Q : Finset X} (hQ : Q ⊆ P)
    (hIso : ∀ p ∈ P, ∀ i ∈ I, r p i → p ∈ Q) : nu r P I = nu r Q I := by
  have hE : restricted r P I = restricted r Q I := by
    funext p i
    apply propext
    constructor
    · rintro ⟨hp, hi, hr⟩
      exact ⟨hIso p hp i hi hr, hi, hr⟩
    · rintro ⟨hp, hi, hr⟩
      exact ⟨hQ hp, hi, hr⟩
  unfold nu
  rw [hE]

theorem nu_remove_isolated_right (r : X → X → Prop) (P : Finset X)
    {I J : Finset X} (hJ : J ⊆ I)
    (hIso : ∀ p ∈ P, ∀ i ∈ I, r p i → i ∈ J) : nu r P I = nu r P J := by
  have hE : restricted r P I = restricted r P J := by
    funext p i
    apply propext
    constructor
    · rintro ⟨hp, hi, hr⟩
      exact ⟨hp, hIso p hp i hi hr, hr⟩
    · rintro ⟨hp, hi, hr⟩
      exact ⟨hp, hJ hi, hr⟩
  unfold nu
  rw [hE]

theorem nu_insert_right_le (r : X → X → Prop) (P I : Finset X) (w : X) :
    nu r P (insert w I) ≤ nu r P I + 1 := by
  classical
  let M := maximumMatching (restricted r P (insert w I))
  have hM := (maximumMatching_spec (restricted r P (insert w I))).1
  let A := M.filter (fun e => e.2 ≠ w)
  let B := M.filter (fun e => e.2 = w)
  have hA : IsMatching (restricted r P I) A := by
    refine ⟨?_, (hM.submatching (Finset.filter_subset _ _)).2⟩
    intro e he
    obtain ⟨he, hne⟩ := Finset.mem_filter.mp he
    obtain ⟨hp, hi, hr⟩ := hM.1 e he
    exact ⟨hp, (Finset.mem_insert.mp hi).resolve_left hne, hr⟩
  have hBcard : B.card ≤ 1 := by
    have h := Finset.card_le_card_of_injOn Prod.snd
      (s := B) (t := {w})
      (by intro e he; exact Finset.mem_singleton.mpr (Finset.mem_filter.mp he).2)
      (by
        intro e he f hf h
        exact hM.2.2 (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp hf).1 h)
    simpa using h
  have hAcard : A.card ≤ nu r P I := matching_card_le_number hA
  have hsum : B.card + A.card = M.card := by
    simpa [A, B] using Finset.card_filter_add_card_filter_not (s := M) (fun e => e.2 = w)
  change M.card ≤ nu r P I + 1
  omega

def RightExposable (r : X → X → Prop) (P I : Finset X) (v : X) : Prop :=
  ∃ M : Finset (X × X), IsMatching (restricted r P I) M ∧
    M.card = nu r P I ∧ v ∉ rightVertices M

omit [Fintype X] in
theorem matching_insert_free {E : X → X → Prop} {M : Finset (X × X)}
    (hM : IsMatching E M) (x w : X) (hEdge : E x w)
    (hx : ∀ e ∈ M, e.1 ≠ x) (hw : ∀ e ∈ M, e.2 ≠ w) :
    IsMatching E (insert (x, w) M) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact hEdge
    · exact hM.1 e he
  · intro e he f hf hef
    rcases Finset.mem_insert.mp he with rfl | he
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · rfl
      · exact False.elim (hx f hf hef.symm)
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · exact False.elim (hx e he hef)
      · exact hM.2.1 he hf hef
  · intro e he f hf hef
    rcases Finset.mem_insert.mp he with rfl | he
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · rfl
      · exact False.elim (hw f hf hef.symm)
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · exact False.elim (hw e he hef)
      · exact hM.2.2 he hf hef

theorem rightExposable_insert_right (r : X → X → Prop) (P I : Finset X)
    (v w : X) (hv : v ∈ I) (hw : w ∉ I)
    (hex : RightExposable r P I v) : RightExposable r P (insert w I) v := by
  classical
  obtain ⟨M, hM, hMcard, hMv⟩ := hex
  have hMnew : IsMatching (restricted r P (insert w I)) M :=
    hM.mono_relation fun _ _ h => ⟨h.1, Finset.mem_insert_of_mem h.2.1, h.2.2⟩
  have hlo : M.card ≤ nu r P (insert w I) := matching_card_le_number hMnew
  by_cases heq : M.card = nu r P (insert w I)
  · exact ⟨M, hMnew, heq, hMv⟩
  let N := maximumMatching (restricted r P (insert w I))
  have hN := (maximumMatching_spec (restricted r P (insert w I))).1
  obtain ⟨Q, hQ, hQcard, hQM⟩ :=
    exists_matching_saturating_right hMnew hN (by change M.card < nu r P (insert w I); omega)
  change Q.card = nu r P (insert w I) at hQcard
  have hwQ : w ∈ rightVertices Q := by
    by_contra hnw
    have hQold : IsMatching (restricted r P I) Q := by
      refine ⟨?_, hQ.2⟩
      intro e he
      obtain ⟨hp, hi, hr⟩ := hQ.1 e he
      have hne : e.2 ≠ w := by
        intro h
        have hmem : e.2 ∈ rightVertices Q := Finset.mem_image.mpr ⟨e, he, rfl⟩
        exact hnw (h ▸ hmem)
      exact ⟨hp, (Finset.mem_insert.mp hi).resolve_left hne, hr⟩
    have h := matching_card_le_number hQold
    change Q.card ≤ nu r P I at h
    omega
  have hwM : w ∉ rightVertices M := by
    intro hm
    obtain ⟨p, hp⟩ := mem_rightVertices.mp hm
    exact hw (hM.1 (p, w) hp).2.1
  have hc : Q.card = M.card + 1 := by
    have hupper := nu_insert_right_le r P I w
    omega
  have hsub : insert w (rightVertices M) ⊆ rightVertices Q :=
    Finset.insert_subset_iff.mpr ⟨hwQ, hQM⟩
  have hequal : insert w (rightVertices M) = rightVertices Q := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [matching_card_rightVertices hQ, Finset.card_insert_of_notMem hwM,
      matching_card_rightVertices hM, hc]
  refine ⟨Q, hQ, hQcard, ?_⟩
  rw [← hequal]
  simp only [Finset.mem_insert, not_or]
  exact ⟨fun h => hw (h ▸ hv), hMv⟩

theorem rightExposable_erase_left (r : X → X → Prop) (P I : Finset X)
    (v x : X) (hex : RightExposable r P I v) :
    RightExposable r (P.erase x) I v := by
  classical
  obtain ⟨M, hM, hMcard, hMv⟩ := hex
  have hupper : nu r (P.erase x) I ≤ nu r P I :=
    nu_mono r (Finset.erase_subset x P) (Finset.Subset.refl I)
  by_cases hx : x ∈ leftVertices M
  · obtain ⟨w, hw⟩ := mem_leftVertices.mp hx
    let A := M.erase (x, w)
    have hAM : A ⊆ M := Finset.erase_subset (x, w) M
    have hA : IsMatching (restricted r (P.erase x) I) A := by
      refine ⟨?_, (hM.submatching hAM).2⟩
      intro e he
      obtain ⟨hp, hi, hr⟩ := hM.1 e (hAM he)
      have hne : e.1 ≠ x := by
        intro h
        exact (Finset.mem_erase.mp he).1 (hM.2.1 (hAM he) hw h)
      exact ⟨Finset.mem_erase.mpr ⟨hne, hp⟩, hi, hr⟩
    have hAcard : A.card + 1 = M.card := Finset.card_erase_add_one hw
    have hlo : A.card ≤ nu r (P.erase x) I := matching_card_le_number hA
    by_cases heq : A.card = nu r (P.erase x) I
    · refine ⟨A, hA, heq, ?_⟩
      intro hvA
      obtain ⟨p, hp⟩ := mem_rightVertices.mp hvA
      exact hMv (mem_rightVertices.mpr ⟨p, hAM hp⟩)
    let N := maximumMatching (restricted r (P.erase x) I)
    have hN := (maximumMatching_spec (restricted r (P.erase x) I)).1
    obtain ⟨Q, hQ, hQcard, hQA⟩ := exists_matching_saturating_right hA hN
      (by change A.card < nu r (P.erase x) I; omega)
    change Q.card = nu r (P.erase x) I at hQcard
    have hnew : nu r (P.erase x) I = M.card := by omega
    have hQold : IsMatching (restricted r P I) Q :=
      hQ.mono_relation fun _ _ h => ⟨(Finset.mem_erase.mp h.1).2, h.2⟩
    have hxQ : ∀ e ∈ Q, e.1 ≠ x := fun e he =>
      (Finset.mem_erase.mp (hQ.1 e he).1).1
    have hwQ : w ∈ rightVertices Q := by
      by_contra hnw
      have hwfree : ∀ e ∈ Q, e.2 ≠ w := by
        intro e he h
        have hm : e.2 ∈ rightVertices Q := Finset.mem_image.mpr ⟨e, he, rfl⟩
        exact hnw (h ▸ hm)
      have hS := matching_insert_free hQold x w (hM.1 (x, w) hw) hxQ hwfree
      have hbound := matching_card_le_number hS
      have hnot : (x, w) ∉ Q := fun he => hxQ (x, w) he rfl
      rw [Finset.card_insert_of_notMem hnot] at hbound
      change Q.card + 1 ≤ nu r P I at hbound
      omega
    have hsubset : rightVertices M ⊆ rightVertices Q := by
      intro y hy
      obtain ⟨p, hp⟩ := mem_rightVertices.mp hy
      by_cases hyw : y = w
      · exact hyw.symm ▸ hwQ
      have hnot : (p, y) ≠ (x, w) := fun h => hyw (congrArg Prod.snd h)
      exact hQA (mem_rightVertices.mpr ⟨p, Finset.mem_erase.mpr ⟨hnot, hp⟩⟩)
    have hequal : rightVertices M = rightVertices Q := by
      apply Finset.eq_of_subset_of_card_le hsubset
      rw [matching_card_rightVertices hM, matching_card_rightVertices hQ, hQcard, hnew]
    exact ⟨Q, hQ, hQcard, by simpa only [← hequal] using hMv⟩
  · have hMnew : IsMatching (restricted r (P.erase x) I) M := by
      refine ⟨?_, hM.2⟩
      intro e he
      obtain ⟨hp, hi, hr⟩ := hM.1 e he
      have hne : e.1 ≠ x := by
        intro h
        have hm : e.1 ∈ leftVertices M := Finset.mem_image.mpr ⟨e, he, rfl⟩
        exact hx (h ▸ hm)
      exact ⟨Finset.mem_erase.mpr ⟨hne, hp⟩, hi, hr⟩
    have hlo : M.card ≤ nu r (P.erase x) I := matching_card_le_number hMnew
    exact ⟨M, hMnew, by omega, hMv⟩

end Restricted
end Family173
