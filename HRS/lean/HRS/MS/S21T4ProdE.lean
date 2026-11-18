import HRS.MS.S21T4ProdD

/-! A common probability space for any finite family of singular-product quadratic Wick limits. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole
variable {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_product_wick_finite (I : ProductGaussian μ) (m : ℕ)
    (h : Fin m → HRS.Euc d → HRS.Euc d → ℝ)
    (hh : ∀ i, MemLp (fun z : HRS.Euc d × HRS.Euc d => h i z.1 z.2) 2 (μ.prod μ))
    (hs : ∀ i x y, h i x y = h i y x) :
    ∃ Q : Fin m → I.Ω → ℝ,
      (∀ i, InSecondChaos I.P I.ξ 3 (Q i)) ∧
      (∀ a, IsR2ZeroMeanONB μ a → ∀ i,
        IsR2WickChaos I.P μ a (fun j => I.η (a j))
          (r2CenterKernel μ (h i)) (fun ω => 2 * Q i ω)) ∧
      (∀ i, (∫ ω, ‖Q i ω‖ ^ 2 ∂I.P) ≤
        ((1 : ℝ) ^ 2 / 2) * ∫ z : HRS.Euc d × HRS.Euc d,
          ‖h i z.1 z.2‖ ^ 2 ∂(μ.prod μ)) := by
  classical
  choose Q hQ using (fun i : Fin m => s21t4_product_scalar_wick I (h i) (hh i) (hs i))
  exact ⟨Q, (fun i => (hQ i).1), (fun a ha i => (hQ i).2.1 a ha),
    (fun i => (hQ i).2.2)⟩

end HRS.MS.R26T3
