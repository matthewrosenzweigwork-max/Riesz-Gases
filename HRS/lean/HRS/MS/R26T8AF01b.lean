import HRS.MS.CritForceAssemblyMaj
import HRS.MS.S82P2Mom
import HRS.MS.UlTail
import HRS.MS.FeatDecAux3
import HRS.MS.S82RA2

/-!
# S8.2 observed-time layer, packet T8A.F01b: thermal force jets and their Euler-weighted derivatives

`F = forceMean ρ = ∇g * ρ` is smooth, and for every `k` both `D^k F` and `x · D^{k+1} F` are bounded.
Route: merged `Ul.tail_conv` (`‖D^b F‖ ≤ C (1+|x|)^{-(s+1+b)}`) for the Schwartz thermal density, `s = d/2`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_thermal_force (d : ℕ) (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) :
    ContDiff ℝ ∞ (forceMean rho) ∧ ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      ‖iteratedFDeriv ℝ k (forceMean rho) x‖ +
      ‖fderiv ℝ (iteratedFDeriv ℝ k (forceMean rho)) x x‖ ≤ C := by
  have hd1 : 1 ≤ d := by omega
  have hs0 : 0 < criticalS d := HRS.MS.S82R.s82r_criticalS_pos hd1
  have hsd : criticalS d < d := HRS.MS.S82R.s82r_criticalS_lt hd1
  have hρ : rho = HRS.Whole.thermalDensity d (criticalS d) a beta :=
    critical_thermal_eq d hd a beta ha hbeta hrho
  obtain ⟨-, ψ, hψ⟩ := HRS.MS.S85.s85_thermal_schwartz hd hs0 hsd ha hbeta
  have hρψ : rho = ⇑ψ := by rw [hρ, hψ]
  obtain ⟨-, hsm, hdec, -, -⟩ := HRS.MS.Ul.tail_conv hd hs0.le hsd ψ
  have hF : forceMean rho = convGradConvW (rieszKernelGrad d (criticalS d)) ⇑ψ := by
    unfold forceMean; rw [hρψ]
  rw [hF]
  refine ⟨hsm, fun k => ?_⟩
  obtain ⟨C1, hC1, h1⟩ := hdec k
  obtain ⟨C2, hC2, h2⟩ := hdec (k + 1)
  refine ⟨C1 + C2, add_nonneg hC1 hC2, fun x => ?_⟩
  have hn : ‖fderiv ℝ (iteratedFDeriv ℝ k (convGradConvW (rieszKernelGrad d (criticalS d)) ⇑ψ)) x‖ =
      ‖iteratedFDeriv ℝ (k + 1) (convGradConvW (rieszKernelGrad d (criticalS d)) ⇑ψ) x‖ :=
    norm_fderiv_iteratedFDeriv
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  have hb1 : (1 + ‖x‖) ^ (-(criticalS d + 1 + (k : ℝ))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith)
  have hb2 : ‖x‖ * (1 + ‖x‖) ^ (-(criticalS d + 1 + ((k + 1 : ℕ) : ℝ))) ≤ 1 := by
    have e : (1 + ‖x‖) ^ (-(criticalS d + 1 + ((k + 1 : ℕ) : ℝ))) =
        (1 + ‖x‖) ^ (-(criticalS d + 1 + (k : ℝ)) ) * (1 + ‖x‖)⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add (by linarith)]
      congr 1; push_cast; ring
    have hk0 : (1 + ‖x‖) ^ (-(criticalS d + 1 + (k : ℝ))) ≤ 1 := hb1
    have hpos : 0 < (1 + ‖x‖) := by linarith
    rw [e]
    have : ‖x‖ * (1 + ‖x‖)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hpos]; linarith
    calc ‖x‖ * ((1 + ‖x‖) ^ (-(criticalS d + 1 + (k : ℝ))) * (1 + ‖x‖)⁻¹)
        = (1 + ‖x‖) ^ (-(criticalS d + 1 + (k : ℝ))) * (‖x‖ * (1 + ‖x‖)⁻¹) := by ring
      _ ≤ 1 * 1 := mul_le_mul hk0 this (by positivity) zero_le_one
      _ = 1 := one_mul 1
  have t1 : ‖iteratedFDeriv ℝ k (convGradConvW (rieszKernelGrad d (criticalS d)) ⇑ψ) x‖ ≤ C1 :=
    (h1 x).trans (by nlinarith [hb1])
  have t2 : ‖fderiv ℝ (iteratedFDeriv ℝ k (convGradConvW (rieszKernelGrad d (criticalS d)) ⇑ψ)) x x‖ ≤ C2 := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [hn]
    calc _ ≤ (C2 * (1 + ‖x‖) ^ (-(criticalS d + 1 + ((k + 1 : ℕ) : ℝ)))) * ‖x‖ :=
          mul_le_mul_of_nonneg_right (h2 x) hx
      _ = C2 * (‖x‖ * (1 + ‖x‖) ^ (-(criticalS d + 1 + ((k + 1 : ℕ) : ℝ)))) := by ring
      _ ≤ C2 * 1 := mul_le_mul_of_nonneg_left hb2 hC2
      _ = C2 := mul_one _
  linarith

end HRS.MS.R26T8A

end
