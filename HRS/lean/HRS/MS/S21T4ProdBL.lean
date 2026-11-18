import HRS.MS.S21T4ProdBK
import HRS.MS.S21L_G11B

/-!
# R26-T3.S13: Wick limits are unchanged by double centering

Wick coefficients depend only on the doubly centered kernel for all integrable
kernels. The equivalence holds at the level of the actual L²-limit predicate,
not merely at the level of formal coefficients.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos

variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_wick_center_iff
    (I : ProductGaussian μ) (a : ℕ → Euc d → ℝ)
    (ha : ∀ i, IsR2Test (a i))
    (k : Euc d → Euc d → ℝ)
    (hk : Integrable (fun z : Euc d × Euc d => k z.1 z.2) (μ.prod μ))
    (Q : I.Ω → ℝ) :
    IsR2WickChaos I.P μ a (fun i => I.η (a i))
      (r2CenterKernel μ k) Q ↔
    IsR2WickChaos I.P μ a (fun i => I.η (a i))
      k Q := by
  have hc : (fun i j => r2WickCoeff μ a (r2CenterKernel μ k) i j) =
      (fun i j => r2WickCoeff μ a k i j) := by
    funext i j
    exact s21l_coeff_center ha hk i j
  change TendstoL2 I.P
    (s94Sec I.P (fun i => I.η (a i))
      (fun i j => r2WickCoeff μ a (r2CenterKernel μ k) i j)) Q ↔
    TendstoL2 I.P
      (s94Sec I.P (fun i => I.η (a i))
        (fun i j => r2WickCoeff μ a k i j)) Q
  rw [hc]

end HRS.MS.R26T3
