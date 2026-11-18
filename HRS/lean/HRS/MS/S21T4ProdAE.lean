import HRS.MS.S21T4ProdAD
import HRS.MS.S21L_G11C

/-! S13: identify finite-rank chaos with the actual quadratic polynomial of the CLT. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_finite_rank_explicit_wick (I : ProductGaussian μ)
    (a : ℕ → Euc d → ℝ) (ha : IsR2ZeroMeanONB μ a)
    {m : ℕ} (c : Fin m → Fin m → ℝ) (u : Fin m → Euc d → ℝ)
    (hdata : IsR2FiniteRankData c u) :
    s94WickL2 I.P μ a (fun i ω => I.η (a i) ω)
      (r2CenterKernel μ (r2FiniteRankKernel c u))
      (fun ω => ∑ α, ∑ β, c α β *
        (I.η (u α) ω * I.η (u β) ω -
          ∫ ζ, I.η (u α) ζ * I.η (u β) ζ ∂I.P)) := by
  letI := I.mΩ
  letI := I.prob
  exact s21l_wick_finiteRank (s21t4_product_eta_bundle I) zero_le_one
    ha.1 ha.2.1 ha.2.2 c
    (fun α => ⟨hdata.smooth α, hdata.compactSupport α⟩)

end HRS.MS.R26T3
