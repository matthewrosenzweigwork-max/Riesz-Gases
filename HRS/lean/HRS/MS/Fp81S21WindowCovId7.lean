import HRS.MS.Fp81S21WindowCovId6
import HRS.MC.E213O1

/-! Variation of a covariance cumulative under physical restriction. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MC.E213O

/-- Restricting projective covariance tensors to the physical window is a
contraction. -/
theorem fp81s21_windowCovarianceMap_norm_le (p : Parameters) (a : ℝ) (ha : 0 ≤ a) :
    ‖fp81s21_windowCovarianceMap p a ha‖ ≤ 1 := by
  let W := HRS.MS.ProClosureS111.physicalWindowRestriction
    (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T) (H := a + p.T) ha le_rfl
  have hW : ‖W‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [one_mul] using
      HRS.MS.ProClosureS111.physicalWindowRestriction_norm_le ha le_rfl x
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  change ‖tensorPow' 2 W (v : TensorDual (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2)‖ ≤ 1 * ‖v‖
  calc
    _ ≤ ‖W‖ ^ 2 * ‖(v : TensorDual (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2)‖ := tensorPow'_norm_le 2 W v
    _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right
      (pow_le_one₀ (norm_nonneg W) hW) (norm_nonneg v)

/-- A continuous BV covariance path remains continuous and BV on restriction,
with no increase in its variation. -/
theorem fp81s21_windowCovarianceMap_bv (p : Parameters) (a : ℝ) (ha : 0 ≤ a)
    (F : ℝ → projTensor (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2)
    (S : Set ℝ) (hcont : ContinuousOn F S) (hbv : BoundedVariationOn F S) :
    ContinuousOn (fun t => fp81s21_windowCovarianceMap p a ha (F t)) S ∧
    BoundedVariationOn (fun t => fp81s21_windowCovarianceMap p a ha (F t)) S ∧
    eVariationOn (fun t => fp81s21_windowCovarianceMap p a ha (F t)) S ≤
      eVariationOn F S := by
  let L := fp81s21_windowCovarianceMap p a ha
  have hlip : LipschitzWith 1 L :=
    ContinuousLinearMap.lipschitzWith_of_opNorm_le (fp81s21_windowCovarianceMap_norm_le p a ha)
  refine ⟨L.continuous.comp_continuousOn hcont, hlip.comp_boundedVariationOn hbv, ?_⟩
  have h := hlip.lipschitzOnWith.comp_eVariationOn_le (mapsTo_univ F S)
  change eVariationOn (L ∘ F) S ≤ eVariationOn F S
  simpa using h

end HRS.Fp81.S21
end
#print axioms HRS.Fp81.S21.fp81s21_windowCovarianceMap_norm_le
#print axioms HRS.Fp81.S21.fp81s21_windowCovarianceMap_bv
