import HRS.MS.R26T8AP11g14

/-!
# S8.2 T8A P11g (part 15): `jb^M'` is integrable for the thermal measure
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_g15_jb_int (hd : 2 ≤ d) {M' : ℝ} (hM' : 0 ≤ M') {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {rho : Euc d → ℝ} (hrho : IsThermalEquilibrium d (criticalS d) a β rho) :
    Integrable (fun x : Euc d => jbracket x ^ M') (HRS.Whole.withDensityReal rho) := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨hdiff, C, c, hC, hc, hb⟩ := HRS.MS.Wad.s84_thermal_gaussReg hd ha hβ hrho
  have hρs : ContDiff ℝ ∞ rho :=
    (HRS.MS.Mov0.mv0_hgauss hd (by unfold criticalS; linarith) (by unfold criticalS; linarith) ha hβ
      hrho).1
  have hprob : HRS.Whole.IsProbDensity rho := hrho.1.1
  obtain ⟨Cp, hCp0, hCp⟩ := r26t8a_p10a_poly_gauss M' hc
  have hb' : ∀ y, rho y * jbracket y ^ M' ≤ C * Cp * Real.exp (-(c / 2) * ‖y‖ ^ 2) := by
    intro y
    have h1 : jbracket y ^ M' ≤ (1 + ‖y‖) ^ M' :=
      Real.rpow_le_rpow (s83_jb_pos y).le (s83_jb_le_one_add y) hM'
    have h2 := hCp ‖y‖ (norm_nonneg _)
    have h3 : rho y ≤ C * Real.exp (-c * ‖y‖ ^ 2) := (le_abs_self _).trans (hb y).1
    calc rho y * jbracket y ^ M' ≤ (C * Real.exp (-c * ‖y‖ ^ 2)) * (1 + ‖y‖) ^ M' :=
          mul_le_mul h3 h1 (Real.rpow_nonneg (s83_jb_pos y).le _) (by positivity)
      _ = C * ((1 + ‖y‖) ^ M' * Real.exp (-c * ‖y‖ ^ 2)) := by ring
      _ ≤ C * (Cp * Real.exp (-(c / 2) * ‖y‖ ^ 2)) := mul_le_mul_of_nonneg_left h2 hC
      _ = _ := by ring
  rw [r26t8a_f25_wd_integrable hprob]
  refine Integrable.mono' ((r26t8a_p10a_gauss_int (d := d) (b := c / 2) (by linarith)).const_mul (C * Cp))
    (hρs.continuous.mul (s85_jb_rpow_continuous M')).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (hprob.nonneg y) (Real.rpow_nonneg (s83_jb_pos y).le _))]
  exact hb' y

end HRS.MS.R26T8A
