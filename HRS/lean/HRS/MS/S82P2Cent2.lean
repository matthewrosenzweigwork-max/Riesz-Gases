import HRS.MS.S82P2Cent1
import HRS.MS.CritForceMom3

/-!
# S8.2 (S82P2): small-ball integral of the corrector envelope against the thermal measure
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

/-- `∫_{B(c,r)} (1 + |c - z|^{1-s}) dmu ≤ G κ (r^d/d + r^{s+1}/(s+1))`. -/
lemma s82p2_ball_integral {d : ℕ} (hd : 2 ≤ d) (G c : ℝ) (hG : 0 < G) (hc : 0 < c)
    (rho : Euc d → ℝ) (hρ : HRS.Whole.IsProbDensity rho)
    (hρG : HRS.Whole.HasR2GaussianUpper G c rho) (c0 : Euc d) (r0 : ℝ) (hr0 : 0 < r0) :
    ∫⁻ z in Metric.ball c0 r0, ENNReal.ofReal (1 + ‖c0 - z‖ ^ (1 - criticalS d))
        ∂HRS.Whole.withDensityReal rho ≤
      ENNReal.ofReal (G * ((d : ℝ) * (volume : Measure (Euc d)).real (Metric.ball (0 : Euc d) 1) *
        (r0 ^ d / d + r0 ^ (criticalS d + 1) / (criticalS d + 1)))) := by
  have hs0 : 0 < criticalS d := by
    unfold criticalS
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsd : criticalS d = (d : ℝ) / 2 := rfl
  set f : Euc d → ℝ := fun z => 1 + ‖c0 - z‖ ^ (1 - criticalS d) with hf
  have hfm : Measurable f := by
    have : Measurable (fun z : Euc d => ‖c0 - z‖) := (measurable_const.sub measurable_id).norm
    exact measurable_const.add (this.pow_const _)
  have hρm' : Measurable (fun y : Euc d => ENNReal.ofReal (rho y)) :=
    ENNReal.measurable_ofReal.comp hρ.measurable
  have hAm : MeasurableSet (Metric.ball c0 r0) := Metric.isOpen_ball.measurableSet
  have hwd : ∫⁻ y in Metric.ball c0 r0, ENNReal.ofReal (f y) ∂(HRS.Whole.withDensityReal rho) =
      ∫⁻ y in Metric.ball c0 r0, ENNReal.ofReal (rho y) * ENNReal.ofReal (f y) := by
    unfold HRS.Whole.withDensityReal
    have hgm' : Measurable (fun y : Euc d => ENNReal.ofReal (f y)) :=
      ENNReal.measurable_ofReal.comp hfm
    rw [restrict_withDensity hAm, lintegral_withDensity_eq_lintegral_mul _ hρm' hgm']
    rfl
  have hf0 : ∀ z, 0 ≤ f z := fun z => by
    simp only [hf]; have := Real.rpow_nonneg (norm_nonneg (c0 - z)) (1 - criticalS d); linarith
  rw [show (fun z => ENNReal.ofReal (1 + ‖c0 - z‖ ^ (1 - criticalS d))) =
      fun z => ENNReal.ofReal (f z) from rfl, hwd]
  have hexp1 : ∀ y : Euc d, Real.exp (-c * ‖y‖ ^ 2) ≤ 1 := fun y => by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg ‖y‖]
  calc ∫⁻ y in Metric.ball c0 r0, ENNReal.ofReal (rho y) * ENNReal.ofReal (f y)
      ≤ ∫⁻ y in Metric.ball c0 r0, ENNReal.ofReal G * ENNReal.ofReal (f y) := by
        refine setLIntegral_mono' hAm fun y hy => ?_
        have h1 : rho y ≤ G := (hρG.2 y).trans (by nlinarith [hexp1 y])
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal h1) le_rfl
    _ = ENNReal.ofReal G * ∫⁻ y in Metric.ball c0 r0, ENNReal.ofReal (f y) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal G * ENNReal.ofReal ((d : ℝ) *
          (volume : Measure (Euc d)).real (Metric.ball (0 : Euc d) 1) *
          (r0 ^ d / d + r0 ^ (criticalS d + 1) / (criticalS d + 1))) := by
        gcongr
        have htr := HRS.MS.S82N.s82n_lintegral_ball_translate c0 r0
          (fun r => ENNReal.ofReal (1 + r ^ (1 - criticalS d)))
        have hh : ∫⁻ y in Metric.ball c0 r0, ENNReal.ofReal (f y) =
            ∫⁻ y in Metric.ball c0 r0, (fun r => ENNReal.ofReal (1 + r ^ (1 - criticalS d))) ‖c0 - y‖ :=
          rfl
        rw [hh, htr]
        have hpol := HRS.MS.S82N.s82n_polar_ub (d := d) (by omega) r0 hr0
          (fun r => 1 + r ^ (1 - criticalS d)) (fun r => r ^ (d - 1) + r ^ criticalS d)
          (fun r hr => by have := Real.rpow_nonneg hr (1 - criticalS d); linarith)
          (measurable_const.add (measurable_id.pow_const _))
          ((Continuous.add (continuous_pow _) (Real.continuous_rpow_const hs0.le)).intervalIntegrable _ _)
          (fun r hr => by
            have hr' : 0 < r := hr.1
            have e : r ^ (d - 1) * r ^ (1 - criticalS d) = r ^ criticalS d := by
              rw [← Real.rpow_natCast, ← Real.rpow_add hr']
              congr 1
              have : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
                rw [Nat.cast_sub (by omega)]; simp
              rw [this]; rw [hsd]; ring
            exact le_of_eq (calc r ^ (d - 1) * (1 + r ^ (1 - criticalS d))
                = r ^ (d - 1) + r ^ (d - 1) * r ^ (1 - criticalS d) := by ring
              _ = r ^ (d - 1) + r ^ criticalS d := by rw [e]))
        refine hpol.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
        congr 1
        rw [intervalIntegral.integral_add ((continuous_pow (d - 1)).intervalIntegrable 0 r0)
          ((Real.continuous_rpow_const hs0.le).intervalIntegrable 0 r0), integral_pow, integral_rpow
          (Or.inl (by linarith))]
        have hdd : d - 1 + 1 = d := by omega
        have h0d : (0 : ℝ) ^ d = 0 := zero_pow (by omega)
        have h0s : (0 : ℝ) ^ (criticalS d + 1) = 0 := Real.zero_rpow (by linarith)
        have hcast : ((d - 1 : ℕ) : ℝ) + 1 = d := by
          rw [Nat.cast_sub (by omega)]; simp
        rw [hdd, h0d, h0s, hcast]
        ring
    _ = ENNReal.ofReal (G * ((d : ℝ) * (volume : Measure (Euc d)).real (Metric.ball (0 : Euc d) 1) *
          (r0 ^ d / d + r0 ^ (criticalS d + 1) / (criticalS d + 1)))) := by
        rw [← ENNReal.ofReal_mul hG.le]

end HRS.MS.S82P2
