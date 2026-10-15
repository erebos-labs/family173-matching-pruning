import Family173.MatchingNumber

namespace Family173
open OAI.SeymourSecondNeighborhood.Bipartite

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem rightExposable_union_right (r : X → X → Prop) (P I D : Finset X)
    (v : X) (hv : v ∈ I) (hex : RightExposable r P I v) :
    RightExposable r P (I ∪ D) v := by
  classical
  induction D using Finset.induction_on with
  | empty => simpa using hex
  | @insert w D _ ih =>
    have heq : I ∪ insert w D = insert w (I ∪ D) := by
      ext y
      simp
    rw [heq]
    by_cases hw : w ∈ I ∪ D
    · simpa only [Finset.insert_eq_of_mem hw] using ih
    · exact rightExposable_insert_right r P (I ∪ D) v w
        (Finset.mem_union.mpr (Or.inl hv)) hw ih

theorem rightExposable_mono_right (r : X → X → Prop) (P : Finset X)
    {I I' : Finset X} (hI : I ⊆ I') (v : X) (hv : v ∈ I)
    (hex : RightExposable r P I v) : RightExposable r P I' v := by
  have h := rightExposable_union_right r P I I' v hv hex
  rw [Finset.union_eq_right.mpr hI] at h
  exact h

theorem rightExposable_sdiff_left (r : X → X → Prop) (P I D : Finset X)
    (v : X) (hex : RightExposable r P I v) : RightExposable r (P \ D) I v := by
  classical
  induction D using Finset.induction_on with
  | empty => simpa using hex
  | @insert x D _ ih =>
    have heq : P \ insert x D = (P \ D).erase x := by
      ext y
      simp [and_left_comm]
    rw [heq]
    exact rightExposable_erase_left r (P \ D) I v x ih

theorem rightExposable_antimono_left (r : X → X → Prop) {P P' : Finset X}
    (hP : P' ⊆ P) (I : Finset X) (v : X) (hex : RightExposable r P I v) :
    RightExposable r P' I v := by
  classical
  have h := rightExposable_sdiff_left r P I (P \ P') v hex
  have heq : P \ (P \ P') = P' := by
    ext y
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨hy, hn⟩
      by_contra hy'
      exact hn ⟨hy, hy'⟩
    · intro hy
      exact ⟨hP hy, fun hn => hn.2 hy⟩
  rw [heq] at h
  exact h

theorem insert_increases_iff_not_exposable (r : X → X → Prop)
    (P I : Finset X) (w : X) (hw : w ∉ I) :
    nu r P (insert w I) = nu r P I + 1 ↔ ¬ RightExposable r P (insert w I) w := by
  classical
  constructor
  · intro hEq hex
    obtain ⟨M, hM, hMcard, hMw⟩ := hex
    have hOld : IsMatching (restricted r P I) M := by
      refine ⟨?_, hM.2⟩
      intro e he
      obtain ⟨hp, hi, hr⟩ := hM.1 e he
      have hne : e.2 ≠ w := by
        intro h
        have hm : e.2 ∈ rightVertices M := Finset.mem_image.mpr ⟨e, he, rfl⟩
        exact hMw (h ▸ hm)
      exact ⟨hp, (Finset.mem_insert.mp hi).resolve_left hne, hr⟩
    have hc : M.card ≤ nu r P I := matching_card_le_number hOld
    omega
  · intro hn
    have hlo := nu_mono r (Finset.Subset.refl P) (Finset.subset_insert w I)
    have hupper := nu_insert_right_le r P I w
    by_contra hneq
    have heq : nu r P (insert w I) = nu r P I := by omega
    let M := maximumMatching (restricted r P I)
    have hM : IsMatching (restricted r P I) M := (maximumMatching_spec _).1
    have hMnew : IsMatching (restricted r P (insert w I)) M :=
      hM.mono_relation fun _ _ h => ⟨h.1, Finset.mem_insert_of_mem h.2.1, h.2.2⟩
    have hMc : M.card = nu r P (insert w I) := heq.symm
    apply hn
    refine ⟨M, hMnew, hMc, ?_⟩
    intro hm
    obtain ⟨p, hp⟩ := mem_rightVertices.mp hm
    exact hw (hM.1 (p, w) hp).2.1

section Ordered
variable [LinearOrder X]

def prefixLE (I : Finset X) (i : X) : Finset X := I.filter (fun x => x ≤ i)
def prefixLT (I : Finset X) (i : X) : Finset X := I.filter (fun x => x < i)

noncomputable def selector (r : X → X → Prop) (P I : Finset X) : Finset X := by
  classical
  exact I.filter (fun i => nu r P (prefixLE I i) = nu r P (prefixLT I i) + 1)

omit [Fintype X] in
theorem prefixLE_eq_insert_prefixLT {I : Finset X} {i : X} (hi : i ∈ I) :
    prefixLE I i = insert i (prefixLT I i) := by
  ext x
  simp only [prefixLE, prefixLT, Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hx, hle⟩
    rcases lt_or_eq_of_le hle with hlt | hEq
    · exact Or.inr ⟨hx, hlt⟩
    · exact Or.inl hEq
  · rintro (rfl | ⟨hx, hlt⟩)
    · exact ⟨hi, le_rfl⟩
    · exact ⟨hx, hlt.le⟩

theorem mem_selector_iff_not_exposable (r : X → X → Prop) (P I : Finset X) (i : X) :
    i ∈ selector r P I ↔ i ∈ I ∧ ¬ RightExposable r P (prefixLE I i) i := by
  classical
  simp only [selector, Finset.mem_filter]
  constructor
  · rintro ⟨hi, hnum⟩
    refine ⟨hi, ?_⟩
    rw [prefixLE_eq_insert_prefixLT hi] at hnum ⊢
    exact (insert_increases_iff_not_exposable r P (prefixLT I i) i
      (by simp [prefixLT])).mp hnum
  · rintro ⟨hi, hn⟩
    refine ⟨hi, ?_⟩
    rw [prefixLE_eq_insert_prefixLT hi] at hn ⊢
    exact (insert_increases_iff_not_exposable r P (prefixLT I i) i
      (by simp [prefixLT])).mpr hn

theorem selector_mono_left (r : X → X → Prop) {P P' I : Finset X}
    (hP : P ⊆ P') : selector r P I ⊆ selector r P' I := by
  intro i hi
  obtain ⟨hiI, hn⟩ := (mem_selector_iff_not_exposable r P I i).mp hi
  apply (mem_selector_iff_not_exposable r P' I i).mpr
  exact ⟨hiI, fun h => hn (rightExposable_antimono_left r hP (prefixLE I i) i h)⟩

theorem selector_restrict_right (r : X → X → Prop) (P : Finset X)
    {I I' : Finset X} (hI : I' ⊆ I) : selector r P I ∩ I' ⊆ selector r P I' := by
  intro i hi
  obtain ⟨hiS, hiI'⟩ := Finset.mem_inter.mp hi
  obtain ⟨_, hn⟩ := (mem_selector_iff_not_exposable r P I i).mp hiS
  apply (mem_selector_iff_not_exposable r P I' i).mpr
  refine ⟨hiI', fun h => hn (rightExposable_mono_right r P ?_ i ?_ h)⟩
  · intro x hx
    obtain ⟨hxI, hxi⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hI hxI, hxi⟩
  · exact Finset.mem_filter.mpr ⟨hiI', le_rfl⟩

omit [DecidableEq X] in
theorem selector_subset_right (r : X → X → Prop) (P I : Finset X) :
    selector r P I ⊆ I := by
  classical
  exact Finset.filter_subset _ _

theorem selector_insert_max (r : X → X → Prop) (P I : Finset X) (w : X)
    (hw : ∀ x ∈ I, x < w) :
    selector r P (insert w I) =
      if nu r P (insert w I) = nu r P I + 1 then insert w (selector r P I)
      else selector r P I := by
  classical
  have hwI : w ∉ I := fun h => (lt_irrefl w) (hw w h)
  have hLE : prefixLE (insert w I) w = insert w I := by
    apply Finset.filter_eq_self.mpr
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact le_rfl
    · exact (hw x hx).le
  have hLT : prefixLT (insert w I) w = I := by
    ext x
    simp only [prefixLT, Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨rfl | hx, hlt⟩
      · exact False.elim ((lt_irrefl _) hlt)
      · exact hx
    · intro hx
      exact ⟨Or.inr hx, hw x hx⟩
  ext i
  by_cases hiw : i = w
  · subst i
    by_cases hinc : nu r P (insert w I) = nu r P I + 1
    · simp [selector, hLE, hLT, hinc]
    · simp [selector, hLE, hLT, hinc, hwI]
  by_cases hi : i ∈ I
  · have hLEi : prefixLE (insert w I) i = prefixLE I i := by
      simp [prefixLE, Finset.filter_insert, not_le.mpr (hw i hi)]
    have hLTi : prefixLT (insert w I) i = prefixLT I i := by
      simp [prefixLT, Finset.filter_insert, not_lt_of_ge (hw i hi).le]
    by_cases hinc : nu r P (insert w I) = nu r P I + 1
    · simp [selector, hLEi, hLTi, hinc, hiw, hi]
    · simp [selector, hLEi, hLTi, hinc, hiw, hi]
  · by_cases hinc : nu r P (insert w I) = nu r P I + 1 <;>
      simp [selector, hi, hiw, hinc]

theorem selector_card (r : X → X → Prop) (P I : Finset X) :
    (selector r P I).card = nu r P I := by
  classical
  induction I using Finset.induction_on_max with
  | empty => simp [selector, nu_empty_right]
  | insert w I hw ih =>
    have hwI : w ∉ I := fun h => (lt_irrefl w) (hw w h)
    have hwS : w ∉ selector r P I := fun h => hwI (selector_subset_right r P I h)
    rw [selector_insert_max r P I w hw]
    by_cases hinc : nu r P (insert w I) = nu r P I + 1
    · rw [ite_eq_left hinc, Finset.card_insert_of_notMem hwS, ih, hinc]
    · rw [ite_eq_right hinc, ih]
      have hlo := nu_mono r (Finset.Subset.refl P) (Finset.subset_insert w I)
      have hupper := nu_insert_right_le r P I w
      omega

theorem selector_card_le_left (r : X → X → Prop) (P I : Finset X) :
    (selector r P I).card ≤ P.card := by
  rw [selector_card]
  exact nu_card_le_left r P I

theorem selector_card_of_saturation (r : X → X → Prop) (P I : Finset X)
    {M : Finset (X × X)} (hM : IsMatching (restricted r P I) M)
    (hSat : leftVertices M = P) : (selector r P I).card = P.card := by
  rw [selector_card, nu_eq_card_of_saturation r P I hM hSat]

theorem selector_remove_isolated_left (r : X → X → Prop) (I : Finset X)
    {P Q : Finset X} (hQ : Q ⊆ P)
    (hIso : ∀ p ∈ P, ∀ i ∈ I, r p i → p ∈ Q) : selector r P I = selector r Q I := by
  classical
  ext i
  have hLE := nu_remove_isolated_left r (prefixLE I i) hQ
    (fun p hp j hj hr => hIso p hp j (Finset.mem_filter.mp hj).1 hr)
  have hLT := nu_remove_isolated_left r (prefixLT I i) hQ
    (fun p hp j hj hr => hIso p hp j (Finset.mem_filter.mp hj).1 hr)
  simp only [selector, Finset.mem_filter, hLE, hLT]

theorem selector_remove_isolated_right (r : X → X → Prop) (P : Finset X)
    {I J : Finset X} (hJ : J ⊆ I)
    (hIso : ∀ p ∈ P, ∀ i ∈ I, r p i → i ∈ J) : selector r P I = selector r P J := by
  classical
  have hSub : selector r P I ⊆ J := by
    intro i hi
    obtain ⟨hiI, hn⟩ := (mem_selector_iff_not_exposable r P I i).mp hi
    by_contra hiJ
    apply hn
    let M := maximumMatching (restricted r P (prefixLE I i))
    have hM : IsMatching (restricted r P (prefixLE I i)) M := (maximumMatching_spec _).1
    refine ⟨M, hM, rfl, ?_⟩
    intro hm
    obtain ⟨p, hp⟩ := mem_rightVertices.mp hm
    exact hiJ (hIso p (hM.1 (p, i) hp).1 i hiI (hM.1 (p, i) hp).2.2)
  ext i
  by_cases hiJ : i ∈ J
  · have hiI := hJ hiJ
    have hLE : nu r P (prefixLE I i) = nu r P (prefixLE J i) := by
      apply nu_remove_isolated_right r P
      · intro j hj
        exact Finset.mem_filter.mpr ⟨hJ (Finset.mem_filter.mp hj).1, (Finset.mem_filter.mp hj).2⟩
      · intro p hp j hj hr
        obtain ⟨hjI, hji⟩ := Finset.mem_filter.mp hj
        exact Finset.mem_filter.mpr ⟨hIso p hp j hjI hr, hji⟩
    have hLT : nu r P (prefixLT I i) = nu r P (prefixLT J i) := by
      apply nu_remove_isolated_right r P
      · intro j hj
        exact Finset.mem_filter.mpr ⟨hJ (Finset.mem_filter.mp hj).1, (Finset.mem_filter.mp hj).2⟩
      · intro p hp j hj hr
        obtain ⟨hjI, hji⟩ := Finset.mem_filter.mp hj
        exact Finset.mem_filter.mpr ⟨hIso p hp j hjI hr, hji⟩
    simp only [selector, Finset.mem_filter, hLE, hLT, hiI, hiJ]
  · have hnOld : i ∉ selector r P I := fun h => hiJ (hSub h)
    have hnNew : i ∉ selector r P J := fun h => hiJ (selector_subset_right r P J h)
    simp only [hnOld, hnNew]

end Ordered
end Family173
