import HRS.MS.S82VG3
import HRS.MS.CritForceNF3
import HRS.MS.S111X1F1
import HRS.MS.QsfCorr2

/-!
# S8.2 A02 (S82V), part 6: the thermal data feeding the stationarity lemma
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82V
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

/-- Thermal facts about the critical drift `b = -F_mu - a x` used in the stationarity step. -/
theorem s82v_stat_data (hd : 2 ≤ d) {a beta : ℝ} (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) :
    HRS.Whole.IsProbDensity rho ∧ ContDiff ℝ 1 rho ∧
    (∃ G c : ℝ, 0 < G ∧ HasR2GaussianUpper G c rho) ∧
    Measurable ((critCoeff d a beta rho).drift 0) ∧
    (∀ x, (critCoeff d a beta rho).ν • gradient rho x = rho x • (critCoeff d a beta rho).drift 0 x) ∧
    ∃ c0 : ℝ, 0 ≤ c0 ∧ ∀ x, ‖(critCoeff d a beta rho).drift 0 x‖ ≤ c0 * (1 + ‖x‖) := by
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) ≤ criticalS d := by unfold criticalS; positivity
  have hsd : criticalS d < d := by unfold criticalS; linarith
  have hρeq : rho = HRS.Whole.thermalDensity d (criticalS d) a beta := critical_thermal_eq d hd a beta ha hbeta hrho
  obtain ⟨C, c, BU, hT⟩ := S45.s45_thermal_data hd hs0 hsd ha hbeta
  set U := HRS.Whole.convMeasure (rieszKernel d (criticalS d)) (HRS.Whole.thermalMeasure d (criticalS d) a beta) with hU
  have hdrift : ∀ x, (critCoeff d a beta rho).drift 0 x = -gradient U x - a • x := by
    intro x
    rw [s82v_drift]
    have := HRS.MS.S21.s21_gradU_eq hd hs0 hsd ha hbeta hrho x
    show -convGradConvW (rieszKernelGrad d (criticalS d)) rho x - a • x = _
    rw [this]
  have hUc : ContDiff ℝ 2 U := hT.Usmooth.of_le (by norm_num)
  have hgc : Continuous (gradient U) := (S45.s45_contDiff_gradient hUc).continuous
  refine ⟨hρeq ▸ hT.prob, hρeq ▸ hT.smooth.of_le (by norm_num), ⟨max C 1, c, lt_of_lt_of_le one_pos
    (le_max_right _ _), hT.hc, fun x => ?_⟩, ?_, fun x => ?_, ⟨BU + |a|, add_nonneg hT.BU0 (abs_nonneg _),
    fun x => ?_⟩⟩
  · rw [hρeq]
    have h1 := (le_abs_self _).trans (hT.h0 x)
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · have : (critCoeff d a beta rho).drift 0 = fun x => -gradient U x - a • x := funext hdrift
    rw [this]
    exact (hgc.neg.sub ((continuous_const : Continuous fun _ : Euc d => a).smul continuous_id)).measurable
  · rw [hdrift, hρeq]
    have h := hT.grad_rho x
    show beta⁻¹ • gradient (HRS.Whole.thermalDensity d (criticalS d) a beta) x = _
    rw [h, smul_comm beta⁻¹ (HRS.Whole.thermalDensity d (criticalS d) a beta x)]
    congr 1
    rw [smul_add, smul_smul, smul_smul]
    have e1 : beta⁻¹ * -(a * beta) = -a := by field_simp
    have e2 : beta⁻¹ * -beta = -1 := by field_simp
    rw [e1, e2, neg_smul, neg_smul, one_smul]
    abel
  · rw [hdrift]
    have h1 : ‖-gradient U x - a • x‖ ≤ ‖gradient U x‖ + ‖a • x‖ := by
      calc ‖-gradient U x - a • x‖ ≤ ‖-gradient U x‖ + ‖a • x‖ := norm_sub_le _ _
        _ = _ := by rw [norm_neg]
    have h2 : ‖a • x‖ = |a| * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs]
    have h3 : ‖gradient U x‖ ≤ BU := hT.gradU_le x
    have h6 := mul_nonneg hT.BU0 (norm_nonneg x)
    have h4 := abs_nonneg a
    have h5 := norm_nonneg x
    rw [h2] at h1
    nlinarith

end HRS.MS.S82V

end
