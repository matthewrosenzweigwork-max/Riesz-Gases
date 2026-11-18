import HRS.MS.S21T4ProdC

/-! A single scalar second-Wiener-chaos variable exists on the ORIGINAL product-Gaussian probability space. -/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MC.E213U13 HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_product_scalar_wick (I : ProductGaussian μ)
    (h : HRS.Euc d → HRS.Euc d → ℝ)
    (hh : MemLp (fun z : HRS.Euc d × HRS.Euc d => h z.1 z.2) 2 (μ.prod μ))
    (hs : ∀ x y, h x y = h y x) :
    ∃ Q : I.Ω → ℝ, InSecondChaos I.P I.ξ 3 Q ∧
      (∀ a, IsR2ZeroMeanONB μ a →
        IsR2WickChaos I.P μ a (fun j => I.η (a j))
          (r2CenterKernel μ h) (fun ω => 2 * Q ω)) ∧
      (∫ ω, ‖Q ω‖ ^ 2 ∂I.P) ≤
        ((1 : ℝ) ^ 2 / 2) * ∫ z : HRS.Euc d × HRS.Euc d, ‖h z.1 z.2‖ ^ 2 ∂(μ.prod μ) := by
  letI := I.mΩ
  letI := I.prob
  obtain ⟨Q, hQm, hQsecond, hQwick, hQbd⟩ :=
    r26t3_vector_wick μ I.P I.ξ I.standard I.η I.first
      (s21t4_eta_linear I) (s21t4_eta_const I) 1 (by norm_num)
      (fun f hf => by simpa only [one_mul] using s21t4_eta_contract I f hf) h hh hs
  refine ⟨Q, hQsecond, ?_, hQbd⟩
  intro a ha
  have h1 := hQwick (ContinuousLinearMap.id ℝ ℝ) a ha
  simpa only [ContinuousLinearMap.id_apply] using h1

end HRS.MS.R26T3
