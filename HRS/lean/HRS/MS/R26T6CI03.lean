import HRS.MS.R26T6CI02

/-!
# R26-T6C.I03: polynomially weighted Riesz row integrability

Under the Gaussian equilibrium envelope, all polynomial moments exist.
Combining the order-2k moment with the square-integrable Riesz row gives
integrability of the polynomially weighted singular row. This is a local
input toward the initial tensor construction, not a proof of K4V01All.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace HRS.MS.R26T6C
open HRS HRS.Whole HRS.Whole.Q34
variable {d : ℕ}

theorem r26t6c_weighted_riesz_row_integrable
    (hd : 2 ≤ d) (s M c : ℝ) (hs : 0 < s)
    (h2s : 2 * s < d) (hc : 0 < c) (rho : Euc d → ℝ)
    (hrho : HRS.Whole.IsProbDensity rho)
    (hb : ∀ x, rho x ≤ M * Real.exp (-c * ‖x‖ ^ 2))
    (hM : ∀ x, rho x ≤ M) (x : Euc d) (k : ℕ) :
    Integrable (fun y : Euc d =>
      (1 + ‖y‖) ^ k * HRS.Whole.rieszKernel d s (x-y))
      (HRS.Whole.withDensityReal rho) := by
  let μ : Measure (Euc d) := HRS.Whole.withDensityReal rho
  letI : IsProbabilityMeasure μ := Q34.isProbabilityMeasure_nu hrho
  have hMoment : Integrable (fun y : Euc d => (1 + ‖y‖) ^ (2 * k)) μ :=
    (r26t6c_gaussian_moments rho hrho M c hc hb (2 * k)).1
  have hpolynomial_meas : AEStronglyMeasurable
      (fun y : Euc d => (1 + ‖y‖) ^ k) μ :=
    ((continuous_const.add continuous_norm).pow k).aestronglyMeasurable
  have hMomentSq : Integrable
      (fun y : Euc d => ((1 + ‖y‖) ^ k) ^ 2) μ := by
    convert hMoment using 1
    funext y
    calc
      ((1 + ‖y‖) ^ k) ^ 2 = (1 + ‖y‖) ^ (k * 2) := (pow_mul _ k 2).symm
      _ = (1 + ‖y‖) ^ (2 * k) := by rw [mul_comm]
  have hPolynomial : MemLp (fun y : Euc d => (1 + ‖y‖) ^ k) 2 μ :=
    (memLp_two_iff_integrable_sq hpolynomial_meas).2 hMomentSq
  have hKernel : MemLp (fun y : Euc d =>
      HRS.Whole.rieszKernel d s (x-y)) 2 μ :=
    (r26t6c_riesz_row_L2 hd s M hs h2s rho hrho hM x).1
  exact hPolynomial.integrable_mul hKernel

end HRS.MS.R26T6C
