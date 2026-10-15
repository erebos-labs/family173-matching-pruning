import Family173.SharpFamily
import Family173.PruningMinimum
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Family173
open OAI.SeymourSecondNeighborhood
open Bipartite Pruning


theorem sharp_minimum_value (k : ℕ) :
    minimumPruningObjective (Sharp.edge k) (Sharp.R k) (Sharp.C k)=((k+1 : ℕ) : ℤ) := by
  rw [minimum_pruning_identity,Sharp.Gamma_number,Sharp.Z_card]
  omega

/-- For every real coefficient c<1 and fixed real additive K, one published
family input defeats the proposed bound for EVERY admissible pruning. -/
theorem coefficient_one_sharp (c K : ℝ) (hc : c<1) :
    ∃ k : ℕ, ∀ R' C' : Finset (Sharp.X k × Sharp.X k),
      AdmissiblePruning (Sharp.edge k) (Sharp.R k) (Sharp.C k) R' C' →
      (deletions (Sharp.R k) (Sharp.C k) R' C' : ℝ) >
        c * ((min
          (matchingNumber (B0 (Sharp.edge k) (Sharp.R k) (H (Sharp.edge k) (Sharp.R k) (Sharp.C k))))
          (matchingNumber (A0 (Sharp.edge k) (H (Sharp.edge k) (Sharp.R k) (Sharp.C k)) (Sharp.C k))) : ℕ) : ℝ) +
        ((uncoveredZ (Sharp.edge k) (Sharp.R k) (Sharp.C k) R' C').card : ℝ) + K := by
  have hδ : 0<1-c := sub_pos.mpr hc
  obtain ⟨k,hk⟩ := exists_nat_gt (K/(1-c))
  have hK : K<(k : ℝ)*(1-c) := (div_lt_iff₀ hδ).mp hk
  have hkn : (k : ℝ)≤((k+1 : ℕ) : ℝ) := Nat.cast_le.mpr (Nat.le_succ k)
  have hKN : K<((k+1 : ℕ) : ℝ)*(1-c) := hK.trans_le (mul_le_mul_of_nonneg_right hkn hδ.le)
  have hBad : c*((k+1 : ℕ) : ℝ)+K < ((k+1 : ℕ) : ℝ) := by
    calc
      c*((k+1 : ℕ) : ℝ)+K < c*((k+1 : ℕ) : ℝ)+((k+1 : ℕ) : ℝ)*(1-c) := by linarith only [hKN]
      _ = ((k+1 : ℕ) : ℝ) := by
        rw [mul_sub,mul_one,mul_comm ((k+1 : ℕ) : ℝ) c,← add_sub_assoc,add_sub_cancel_left]
  refine ⟨k,?_⟩
  intro R' C' hAd
  have hNat := Sharp.pruning_lower_natural k R' C' hAd
  have hReal : ((k+1 : ℕ) : ℝ)+((uncoveredZ (Sharp.edge k) (Sharp.R k) (Sharp.C k) R' C').card : ℝ) ≤
      (deletions (Sharp.R k) (Sharp.C k) R' C' : ℝ) := by
    exact_mod_cast hNat
  rw [Sharp.B_number,Sharp.A_number,min_self]
  apply lt_of_lt_of_le ?_ hReal
  calc
    c*((k+1 : ℕ) : ℝ)+((uncoveredZ (Sharp.edge k) (Sharp.R k) (Sharp.C k) R' C').card : ℝ)+K =
      (c*((k+1 : ℕ) : ℝ)+K)+((uncoveredZ (Sharp.edge k) (Sharp.R k) (Sharp.C k) R' C').card : ℝ) := by ac_rfl
    _ < ((k+1 : ℕ) : ℝ)+((uncoveredZ (Sharp.edge k) (Sharp.R k) (Sharp.C k) R' C').card : ℝ) :=
      by linarith only [hBad]

end Family173
