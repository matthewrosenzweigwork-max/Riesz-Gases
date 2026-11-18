import HRS.MS.Fp81S21RespRecon2
import HRS.MC.E213O1

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.MS.S21E HRS.MC.E213O

/-- Cubic Bochner tensors commute with a continuous linear map. -/
theorem fp81s21_respRecon_tensor_map
    {E B B' : Type*} [MeasurableSpace E] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup B'] [NormedSpace ℝ B']
    (μ : Measure E) [IsProbabilityMeasure μ] (S : B →L[ℝ] B') (v : E → B)
    (hv : AEStronglyMeasurable v μ)
    (hi : Integrable (fun x => ‖v x‖ * ‖v x‖ * ‖v x‖) μ) :
    tensorPow' 3 S (s21eKappa0 μ v) = s21eKappa0 μ (fun x => S (v x)) := by
  have hm : AEStronglyMeasurable (fun x => S (v x)) μ :=
    S.continuous.comp_aestronglyMeasurable hv
  have him : Integrable (fun x => ‖S (v x)‖ * ‖S (v x)‖ * ‖S (v x)‖) μ := by
    have hbound : Integrable (fun x => ‖S‖ ^ 3 * (‖v x‖ * ‖v x‖ * ‖v x‖)) μ :=
      hi.const_mul _
    apply hbound.mono' ((hm.norm.mul hm.norm).mul hm.norm)
    filter_upwards with x
    change ‖‖S (v x)‖ * ‖S (v x)‖ * ‖S (v x)‖‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      ‖S (v x)‖ * ‖S (v x)‖ * ‖S (v x)‖ ≤
          (‖S‖ * ‖v x‖) * (‖S‖ * ‖v x‖) * (‖S‖ * ‖v x‖) := by
        gcongr <;> exact S.le_opNorm (v x)
      _ = ‖S‖ ^ 3 * (‖v x‖ * ‖v x‖ * ‖v x‖) := by ring
  ext M
  rw [tensorPow'_apply, s21e_kappa0_apply μ hv hi, s21e_kappa0_apply μ hm him]
  apply integral_congr_ae
  filter_upwards with x
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

#print axioms fp81s21_respRecon_tensor_map

end HRS.Fp81.S21
end
