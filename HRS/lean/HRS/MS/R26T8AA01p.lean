import HRS.MS.R26T8AA01o

/-!
# S8.2 T8A A01 (part p): integrability of `ρ ⟨∇g(u-·), W⟩` on exterior regions and the centred force limit
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_a01_ext_int_inner (hd : 2 ≤ d) {rho : Euc d → ℝ} (hrho0 : ∀ x, 0 ≤ rho x)
    (hρm : AEStronglyMeasurable rho volume) {W : Euc d → Euc d} (hWm : AEStronglyMeasurable W volume)
    (hWi : Integrable (fun z => rho z * ‖W z‖)) (u : Euc d) {ε : ℝ} (hε : 0 < ε) (S : Set (Euc d))
    (hS : MeasurableSet S) (hSε : ∀ z ∈ S, ε < ‖u - z‖) :
    Integrable (Set.indicator S (fun z => rho z * inner ℝ (rieszKernelGrad d (criticalS d) (u - z)) (W z))) := by
  have hs0 : 0 < criticalS d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    unfold criticalS; linarith
  have hGm : AEStronglyMeasurable (fun z => rieszKernelGrad d (criticalS d) (u - z)) volume :=
    ((HRS.Whole.movtr_rieszKernelGrad_measurable (d := d) (criticalS d)).comp
      (measurable_const.sub measurable_id)).aestronglyMeasurable
  refine Integrable.mono' (hWi.const_mul (criticalS d * ε ^ (-criticalS d - 1)))
    ((hρm.mul (hGm.inner hWm)).indicator hS) (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ S
  · rw [Set.indicator_of_mem hz, norm_mul, Real.norm_of_nonneg (hrho0 z)]
    have hu : u - z ≠ 0 := sub_ne_zero.2 (fun h => by have := hSε z hz; rw [h, sub_self, norm_zero] at this; linarith)
    have hG := r26t8a_norm_rieszGrad hs0 hu
    have hn := hSε z hz
    have hrp : ‖u - z‖ ^ (-criticalS d - 1) ≤ ε ^ (-criticalS d - 1) :=
      Real.rpow_le_rpow_of_nonpos hε hn.le (by linarith)
    calc rho z * ‖inner ℝ (rieszKernelGrad d (criticalS d) (u - z)) (W z)‖
        ≤ rho z * (‖rieszKernelGrad d (criticalS d) (u - z)‖ * ‖W z‖) :=
          mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs]; exact abs_real_inner_le_norm _ _) (hrho0 z)
      _ ≤ rho z * ((criticalS d * ε ^ (-criticalS d - 1)) * ‖W z‖) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)) (hrho0 z)
          rw [hG]; exact mul_le_mul_of_nonneg_left hrp hs0.le
      _ = (criticalS d * ε ^ (-criticalS d - 1)) * (rho z * ‖W z‖) := by ring
  · rw [Set.indicator_of_notMem hz]; simp only [norm_zero]
    exact mul_nonneg (mul_nonneg hs0.le (Real.rpow_nonneg hε.le _)) (mul_nonneg (hrho0 z) (norm_nonneg _))

end HRS.MS.R26T8A
