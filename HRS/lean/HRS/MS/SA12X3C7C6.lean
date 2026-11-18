import HRS.MS.SA12X3C7C5

/-!
# S.A.12 C7 (SA12X3), part C6 (7C): `L²` norms as integrals
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MH.AdjointRd

variable {d : ℕ}

/-- `‖f‖₂² = ∫ f²` for a function with square integrable. -/
theorem sa12x3_eLp_sq {f : Euc d → ℝ} (hm : AEStronglyMeasurable f volume) (hi : Integrable (fun x => f x ^ 2)) :
    (eLpNorm f 2 volume) ^ 2 = ENNReal.ofReal (∫ x, f x ^ 2) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hm]
  simp only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  have : (1 / (2 : ℝ)) * ((2 : ℕ) : ℝ) = 1 := by norm_num
  rw [this, ENNReal.rpow_one, ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => sq_nonneg _)]
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal_abs]
  rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
  congr 1
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]

/-- The `L²` norm of an indicator on a set. -/
theorem sa12x3_eLp_ind {ψ : Euc d → ℝ} (hψ : Continuous ψ) {A : Set (Euc d)} (hA : MeasurableSet A)
    (hAb : Bornology.IsBounded A) :
    (eLpNorm (A.indicator ψ) 2 volume) ^ 2 = ENNReal.ofReal (∫ x in A, ψ x ^ 2) := by
  have hm : AEStronglyMeasurable (A.indicator ψ) volume := (hψ.aestronglyMeasurable).indicator hA
  have hsq : (fun x => (A.indicator ψ x) ^ 2) = A.indicator (fun x => ψ x ^ 2) := by
    funext x; by_cases hx : x ∈ A <;> simp [hx]
  have hint : Integrable (fun x => (A.indicator ψ x) ^ 2) := by
    rw [hsq]
    refine (integrable_indicator_iff hA).2 ?_
    obtain ⟨R, hR⟩ := hAb.subset_closedBall (0 : Euc d)
    exact ((hψ.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall (0 : Euc d) R)).mono_set hR
  rw [sa12x3_eLp_sq hm hint, hsq, integral_indicator hA]

end HRS.MH.AdjointRd.Phase2SA12Near
