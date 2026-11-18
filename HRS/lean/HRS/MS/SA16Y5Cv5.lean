import HRS.MS.SA16Y5Gs1
import HRS.MS.SA16Y5Lb1

/-!
# S.A.16 (SA16Y5) Cv5: associativity of the convolution for a bounded continuous function (K3 helper)

`sa16y5_cv_assoc_bdd`: `k₁ ⋆ (k₂ ⋆ φ) = (k₁ ⋆ k₂) ⋆ φ` for integrable `k₁, k₂` and `φ` continuous and bounded.
`sa16y5_gg_conv`: `g_a ⋆ (g_b ⋆ φ) = g_{a+b} ⋆ φ`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA

section Cv5
variable {d : ℕ}

lemma sa16y5_cv_assoc_bdd {k₁ k₂ φ : Euc d → ℝ} (h1 : Integrable k₁) (h2 : Integrable k₂)
    (hφ : Continuous φ) {B : ℝ} (hB : ∀ y, |φ y| ≤ B) (x : Euc d) :
    sa16r_cv k₁ (sa16r_cv k₂ φ) x = sa16r_cv (sa16r_cv k₁ k₂) φ x := by
  have h := convolution_assoc (ContinuousLinearMap.lsmul ℝ ℝ) (ContinuousLinearMap.lsmul ℝ ℝ)
    (ContinuousLinearMap.lsmul ℝ ℝ) (ContinuousLinearMap.lsmul ℝ ℝ)
    (f := k₁) (g := k₂) (k := φ) (μ := volume) (ν := volume) (x₀ := x)
    (fun a b c => smul_assoc a b c) h1.aestronglyMeasurable h2.aestronglyMeasurable
    hφ.aestronglyMeasurable
    (h1.ae_convolution_exists _ h2)
    (Eventually.of_forall fun y => by
      show Integrable (fun t => ‖k₂ t‖ * ‖φ (y - t)‖) volume
      exact sa16y5_int_bdd h2.norm hφ.norm (B := B) (fun z => by simpa [Real.norm_eq_abs] using hB z) y)
    (by
      have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
      have hcont : Continuous ((fun x => ‖k₂ x‖) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] fun x => ‖φ x‖) := by
        have : ((fun x => ‖k₂ x‖) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] fun x => ‖φ x‖) =
            fun y => ∫ z, ‖k₂ z‖ * ‖φ (y - z)‖ := by
          funext y
          simp only [convolution, ContinuousLinearMap.mul_apply']
        rw [this]
        refine continuous_of_dominated (bound := fun z => ‖k₂ z‖ * B) (fun y => ?_) (fun y => ?_)
          (h2.norm.mul_const B) (Eventually.of_forall fun z => ?_)
        · exact h2.norm.1.mul ((hφ.norm.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
        · refine Eventually.of_forall fun z => ?_
          rw [norm_mul, norm_norm, norm_norm]
          exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hB (y - z)) (norm_nonneg _)
        · exact (continuous_const.mul (hφ.norm.comp (continuous_id.sub continuous_const)))
      have hbd : ∀ y, ‖((fun x => ‖k₂ x‖) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] fun x => ‖φ x‖) y‖ ≤
          (∫ z, ‖k₂ z‖) * B := by
        intro y
        simp only [convolution, ContinuousLinearMap.mul_apply']
        calc ‖∫ z, ‖k₂ z‖ * ‖φ (y - z)‖‖ ≤ ∫ z, ‖k₂ z‖ * B := by
              refine norm_integral_le_of_norm_le (h2.norm.mul_const B) (Eventually.of_forall fun z => ?_)
              rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
              exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hB (y - z)) (norm_nonneg _)
          _ = _ := by rw [integral_mul_const]
      show Integrable (fun t => ‖k₁ t‖ * ((fun x => ‖k₂ x‖) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
        fun x => ‖φ x‖) (x - t)) volume
      refine Integrable.mono' (h1.norm.mul_const ((∫ z, ‖k₂ z‖) * B)) ?_ (Eventually.of_forall fun t => ?_)
      · exact h1.norm.aestronglyMeasurable.mul ((hcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      · rw [norm_mul, norm_norm]
        exact mul_le_mul_of_nonneg_left (hbd _) (norm_nonneg _))
  simpa [sa16r_cv_eq_conv] using h.symm

lemma sa16y5_gg_conv {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {φ : Euc d → ℝ} (hφ : Continuous φ) {B : ℝ}
    (hB : ∀ y, |φ y| ≤ B) (x : Euc d) :
    sa16r_cv (sa16r_g d a) (sa16r_cv (sa16r_g d b) φ) x = sa16r_cv (sa16r_g d (a + b)) φ x := by
  rw [sa16y5_cv_assoc_bdd (sa16r_g_int ha) (sa16r_g_int hb) hφ hB x]
  congr 1
  funext y
  exact sa16y5_g_conv ha hb y

end Cv5

end HRS.Whole.AppendixA.Phase2SA16R
