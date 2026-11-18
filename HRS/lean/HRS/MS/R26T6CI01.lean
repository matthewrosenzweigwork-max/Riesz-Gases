import HRS.MS.ThCorrSmAux1

/-! R26-T6C.I01: polynomial moments under a Gaussian density envelope. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace HRS.MS.R26T6C
open HRS HRS.Whole HRS.MS.Tc5 HRS.MS.TcR HRS.MS.Thm
variable {d : ℕ}

theorem r26t6c_gaussian_moments (rho : Euc d → ℝ)
    (hrho : HRS.Whole.IsProbDensity rho) (M c : ℝ) (hc : 0 < c)
    (hb : ∀ x, rho x ≤ M * Real.exp (-c * ‖x‖ ^ 2)) (k : ℕ) :
    Integrable (fun x : Euc d => (1 + ‖x‖) ^ k) (HRS.Whole.withDensityReal rho) ∧
    Integrable (fun x : Euc d => ‖x‖ ^ k) (HRS.Whole.withDensityReal rho) := by
  have hM0 : 0 ≤ M := tc2_M0_nonneg hrho hb
  have hK0 : 0 ≤ tc5_Kp (c / 2) k := tc5_Kp_nonneg _ _
  have hg : Integrable (fun x : Euc d =>
      (M * tc5_Kp (c / 2) k) * Real.exp (-(c / 2) * ‖x‖ ^ 2)) :=
    (t012_integrable_exp_neg_sq (d := d) (b := c / 2) (by positivity)).const_mul _
  have hfirst : Integrable (fun x : Euc d => (1 + ‖x‖) ^ k) (HRS.Whole.withDensityReal rho) := by
    rw [tc2_integrable_nu hrho]
    refine Integrable.mono' hg
      ((hrho.measurable.mul ((measurable_const.add measurable_norm).pow_const k)).aestronglyMeasurable)
      (ae_of_all _ fun x => ?_)
    have hA0 : 0 ≤ (1 + ‖x‖) ^ k := by positivity
    have hp := tc5_poly (c := c / 2) (by positivity) k (norm_nonneg x)
    have hE : Real.exp (-c * ‖x‖ ^ 2) =
        Real.exp (-(c / 2) * ‖x‖ ^ 2) * Real.exp (-(c / 2) * ‖x‖ ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have he0 : 0 ≤ Real.exp (-(c / 2) * ‖x‖ ^ 2) := (Real.exp_pos _).le
    have hpoint : rho x * (1 + ‖x‖) ^ k ≤
        (M * tc5_Kp (c / 2) k) * Real.exp (-(c / 2) * ‖x‖ ^ 2) := calc
      _ ≤ (M * Real.exp (-c * ‖x‖ ^ 2)) * (1 + ‖x‖) ^ k :=
        mul_le_mul_of_nonneg_right (hb x) hA0
      _ = (M * Real.exp (-(c / 2) * ‖x‖ ^ 2)) *
          ((1 + ‖x‖) ^ k * Real.exp (-(c / 2) * ‖x‖ ^ 2)) := by
        rw [hE]
        ring
      _ ≤ (M * Real.exp (-(c / 2) * ‖x‖ ^ 2)) * tc5_Kp (c / 2) k :=
        mul_le_mul_of_nonneg_left hp (mul_nonneg hM0 he0)
      _ = _ := by ring
    rw [Real.norm_of_nonneg (mul_nonneg (hrho.nonneg x) hA0)]
    exact hpoint
  refine ⟨hfirst, ?_⟩
  refine Integrable.mono' hfirst
    (((continuous_norm : Continuous (fun x : Euc d => ‖x‖)).pow k).aestronglyMeasurable)
    (ae_of_all _ fun x => ?_)
  simp only [Real.norm_of_nonneg (pow_nonneg (norm_nonneg x) k)]
  exact pow_le_pow_left₀ (norm_nonneg x) (by linarith) k

end HRS.MS.R26T6C
