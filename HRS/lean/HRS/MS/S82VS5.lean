import HRS.MS.S82VS4

/-!
# S8.2 A02 (S82V), part 10: the stationarity instantiation `∫ L₀ Q(·,y) dμ = 0`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82V
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

/-- Stationarity of the local mean-field generator against a row of the corrector. -/
theorem s82v_row_stat (hd : 2 ≤ d) {a beta M A : ℝ} (ha : 0 < a) (hbeta : 0 < beta)
    {rho : Euc d → ℝ} (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) (y : Euc d) :
    Integrable (fun w => (critCoeff d a beta rho).ν * Laplacian.laplacian (fun x => Q x y) w +
        inner ℝ ((critCoeff d a beta rho).drift 0 w) (gradient (fun x => Q x y) w))
      (HRS.Whole.withDensityReal rho) ∧
    ∫ w, ((critCoeff d a beta rho).ν * Laplacian.laplacian (fun x => Q x y) w +
        inner ℝ ((critCoeff d a beta rho).drift 0 w) (gradient (fun x => Q x y) w))
      ∂(HRS.Whole.withDensityReal rho) = 0 := by
  obtain ⟨hρp, hρ1, ⟨G, c, hG, hGauss⟩, hbm, hbρ, c0, hc0, hb⟩ := s82v_stat_data hd ha hbeta hrho
  obtain ⟨hφ, hA, hg, hH⟩ := s82v_row_hyps hQ y
  have hM : 0 ≤ max M 0 := le_max_right _ _
  obtain ⟨hint, hzero⟩ := HRS.MS.S82P.s82p_stationary hd (ν := (critCoeff d a beta rho).ν)
    (inv_pos.2 hbeta) hρp hρ1 hG hGauss hbm hbρ hc0 hb y hφ hA hM hg hH
  refine ⟨?_, ?_⟩
  · rw [s82v_wd_integrable_iff hρp.measurable hρp.nonneg]; exact hint
  · rw [s82v_wd_integral hρp.measurable hρp.nonneg]; exact hzero

end HRS.MS.S82V

end
