import HRS.MS.S82UD2

/-!
# S8.2 A01 (S82U): `J1` in grouped form and its `μ`-mean (Q-specific)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82U
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2 HRS.MS.S82T HRS.MH.PairingRd

theorem u_LE_Q {d : ℕ} (hd : 2 ≤ d) {a beta M A : ℝ} {rho : Euc d → ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} {Λ Gc c : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hQ : PairCorrector a beta rho M A f Q) (hF : UForce d rho Λ) (hG : 0 ≤ Gc) (hc : 0 < c)
    (hρG : HRS.Whole.HasR2GaussianUpper Gc c rho) {x y : Euc d} (hxy : x ≠ y) :
    s82t_J1 (critCoeff d a beta rho) (s82p2_gt Q) x y =
      (∫ z, inner ℝ (rieszKernelGrad d (criticalS d) (x - z)) (s82p2_gt Q z y - s82p2_gt Q x y)
        ∂(HRS.Whole.withDensityReal rho)) +
      inner ℝ (s82p2_gt Q x y) (forceMean rho x) := by
  rw [u_J1_eq]
  have hx := u_int_dens hF.prob (u_edge_int hd hM hA hQ hG hc hF.prob hρG hxy)
  have := u_JE hd hF (u_gt_section_measurable Q y) hx
  rw [this, HRS.MH.DualityRd.dc1a_integral_withDensity hF.prob.measurable hF.prob.nonneg]

theorem u_jmean_Q {d : ℕ} (hd : 2 ≤ d) {a beta M A : ℝ} {rho : Euc d → ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} {Λ Gc c : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hQ : PairCorrector a beta rho M A f Q) (hF : UForce d rho Λ) (hG : 0 ≤ Gc) (hc : 0 < c)
    (hρG : HRS.Whole.HasR2GaussianUpper Gc c rho) (y : Euc d) :
    ∫ x, s82t_J1 (critCoeff d a beta rho) (s82p2_gt Q) x y ∂(HRS.Whole.withDensityReal rho) =
      -∫ z, inner ℝ (s82p2_gt Q z y) (forceMean rho z) ∂(HRS.Whole.withDensityReal rho) := by
  obtain ⟨h1, h2⟩ := u_psi_ok hd hM hA hQ hG hc hF.prob hρG y
  have := u_jmean hd hF (u_gt_section_measurable Q y) h1 h2
  rw [HRS.MH.DualityRd.dc1a_integral_withDensity hF.prob.measurable hF.prob.nonneg,
    HRS.MH.DualityRd.dc1a_integral_withDensity hF.prob.measurable hF.prob.nonneg]
  simp_rw [u_J1_eq]
  exact this

end HRS.MS.S82U
