import HRS.MS.CritForceAssemblyMaj
import HRS.MS.S82P2Mom
import HRS.MS.MovLinAux9
import HRS.MS.S82RA2

/-!
# S8.2 observed-time layer, packet T8A.F01a: `√ρ` is a Schwartz function with Gaussian derivative bounds

From the merged `mv0_sqrt_gauss_thermal` (`√ρ ∈ C^∞` and `‖D^k √ρ‖ ≤ C_k e^{-c|x|²}`) and `movc1_G_schwartz`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_thermal_sqrt (d : ℕ) (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) :
    ∃ sigma : SchwartzMap (Euc d) ℝ, (∀ x, sigma x = Real.sqrt (rho x)) ∧
      ∃ rate : ℝ, 0 < rate ∧ ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
        ‖iteratedFDeriv ℝ n sigma x‖ ≤ C * Real.exp (-rate * ‖x‖ ^ 2) := by
  have hd1 : 1 ≤ d := by omega
  have hs0 : 0 < criticalS d := HRS.MS.S82R.s82r_criticalS_pos hd1
  have hsd : criticalS d < d := HRS.MS.S82R.s82r_criticalS_lt hd1
  obtain ⟨h1, -, c, hc, hk⟩ := HRS.MS.Mov0.mv0_sqrt_gauss_thermal hd hs0.le hsd ha hbeta hrho
  obtain ⟨sigma, hsig⟩ := HRS.MS.MovC1.movc1_G_schwartz (d := d)
    (f := fun x => Real.sqrt (rho x)) ⟨h1, c, hc, hk⟩
  refine ⟨sigma, fun x => by rw [hsig], c, hc, fun n => ?_⟩
  obtain ⟨C, hC⟩ := hk n
  refine ⟨|C|, abs_nonneg _, fun x => ?_⟩
  rw [hsig]
  exact (hC x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)

end HRS.MS.R26T8A

end
