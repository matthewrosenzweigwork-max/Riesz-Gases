import HRS.MS.SA16Y5Cv2

/-!
# S.A.16 (SA16Y5) Cv3: associativity of the convolution and derivatives of a composite convolution

`sa16y5_cv_assoc`: `k₁ ⋆ (k₂ ⋆ φ) = (k₁ ⋆ k₂) ⋆ φ` for integrable `k₁, k₂` and `φ ∈ C_c^∞`.
`sa16y5_cv_locInt`: `k₁ ⋆ k₂` is integrable.
`sa16y5_cv_pd`: `∂^idx (k ⋆ φ) = k ⋆ ∂^idx φ` for locally integrable `k` and `φ ∈ C_c^∞`.
`sa16y5_pd_cv_cv`: `∂^idx (k₁ ⋆ (k₂ ⋆ φ)) = k₁ ⋆ (k₂ ⋆ ∂^idx φ)`.
`sa16y5_cv_cv_contDiff`: `k₁ ⋆ (k₂ ⋆ φ)` is smooth.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Cv3
variable {d : ℕ}

lemma sa16y5_cv_locInt {k₁ k₂ : Euc d → ℝ} (h1 : Integrable k₁) (h2 : Integrable k₂) :
    Integrable (sa16r_cv k₁ k₂) := by
  rw [sa16r_cv_eq_conv]
  exact h1.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) h2

lemma sa16y5_cv_assoc {k₁ k₂ φ : Euc d → ℝ} (h1 : Integrable k₁) (h2 : Integrable k₂) (hφ : IsCcInfty φ)
    (x : Euc d) :
    sa16r_cv k₁ (sa16r_cv k₂ φ) x = sa16r_cv (sa16r_cv k₁ k₂) φ x := by
  have L := ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)
  have h := convolution_assoc (ContinuousLinearMap.lsmul ℝ ℝ) (ContinuousLinearMap.lsmul ℝ ℝ)
    (ContinuousLinearMap.lsmul ℝ ℝ) (ContinuousLinearMap.lsmul ℝ ℝ)
    (f := k₁) (g := k₂) (k := φ) (μ := volume) (ν := volume) (x₀ := x)
    (fun a b c => smul_assoc a b c) h1.aestronglyMeasurable h2.aestronglyMeasurable
    hφ.1.continuous.aestronglyMeasurable
    (h1.ae_convolution_exists _ h2)
    (h2.norm.ae_convolution_exists (ContinuousLinearMap.mul ℝ ℝ)
      (hφ.1.continuous.integrable_of_hasCompactSupport hφ.2).norm)
    (by
      obtain ⟨Bφ, hBφ⟩ := sa16r_cc_bdd hφ
      have hcont : Continuous ((fun x => ‖k₂ x‖) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] fun x => ‖φ x‖) :=
        (hφ.2.norm).continuous_convolution_right (ContinuousLinearMap.mul ℝ ℝ) h2.norm.locallyIntegrable
          hφ.1.continuous.norm
      have hbd : ∀ y, ‖((fun x => ‖k₂ x‖) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] fun x => ‖φ x‖) y‖ ≤
          (∫ z, ‖k₂ z‖) * Bφ := by
        intro y
        simp only [convolution, ContinuousLinearMap.mul_apply']
        calc ‖∫ z, ‖k₂ z‖ * ‖φ (y - z)‖‖ ≤ ∫ z, ‖k₂ z‖ * Bφ := by
              refine norm_integral_le_of_norm_le (h2.norm.mul_const Bφ) (Eventually.of_forall fun z => ?_)
              rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
              exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hBφ (y - z)) (norm_nonneg _)
          _ = _ := by rw [integral_mul_const]
      show Integrable (fun t => ‖k₁ t‖ * ((fun x => ‖k₂ x‖) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
        fun x => ‖φ x‖) (x - t)) volume
      refine Integrable.mono' (h1.norm.mul_const ((∫ z, ‖k₂ z‖) * Bφ)) ?_ (Eventually.of_forall fun t => ?_)
      · exact h1.norm.aestronglyMeasurable.mul ((hcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      · rw [norm_mul, norm_norm]
        exact mul_le_mul_of_nonneg_left (hbd _) (norm_nonneg _))
  simpa [sa16r_cv_eq_conv] using h.symm

end Cv3

end HRS.Whole.AppendixA.Phase2SA16R
