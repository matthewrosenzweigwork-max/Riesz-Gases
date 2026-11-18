import HRS.MS.PROS13WickIdentificationAut5
import HRS.MS.S21T4ProdBF

/-!
# S15d: identify a physical Wick quadratic with the actual S13 Gaussian quadratic

A nonempty family of admissible zero-mean test orthonormal bases is essential.
For the physical Riesz setting, this is supplied separately by the smooth
positive-density hypotheses. The theorem does not assert the spectral
diagonalization or the original R26-T3.S15d conclusion.
-/

set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS.Whole

theorem s15d_physical_wick_identifies_actual
    {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
    (I : ProductGaussian μ) (h : HRS.Euc d → HRS.Euc d → ℝ)
    (hh : MemLp (fun z : HRS.Euc d × HRS.Euc d => h z.1 z.2) 2 (μ.prod μ))
    (hs : ∀ x y, h x y = h y x)
    (Qg : I.Ω → ℝ)
    (hBasis : ∃ a : ℕ → HRS.Euc d → ℝ, IsR2ZeroMeanONB μ a)
    (hW : ∀ a, IsR2ZeroMeanONB μ a →
      IsR2WickChaos I.P μ a (fun j => I.η (a j))
        (r2CenterKernel μ h) (fun ω => 2 * Qg ω)) :
    ∃ Q : I.Ω → ℝ,
      HasActualProductQuadraticLimit I h Q ∧ Qg =ᵐ[I.P] Q := by
  obtain ⟨Q, hQ⟩ := pro_s13_actual_product_quadratic_exists I h hh hs
  obtain ⟨a, ha⟩ := hBasis
  have hWQ := pro_s13_actual_product_quadratic_all_ONB_wick
    I h hh hs Q hQ a ha
  have hEqual := s21t4_product_wick_ae_unique I a ha
    (r2CenterKernel μ h) (fun ω => 2 * Qg ω) (fun ω => 2 * Q ω)
    (hW a ha) hWQ
  refine ⟨Q, hQ, ?_⟩
  filter_upwards [hEqual] with ω hw
  linarith

end HRS.MS.R26T3
