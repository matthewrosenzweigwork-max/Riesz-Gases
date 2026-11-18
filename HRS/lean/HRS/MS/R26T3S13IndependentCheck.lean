import HRS.MS.R26T3S13

/-!
# Independent frozen-contract check: R26-T3.S13

This consumer reproduces the original 2026-10-30 pinned frozen contract
rather than relying on a self-referential type_of%.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.MS.R26T3
open HRS HRS.Whole

theorem reviewer_r26t3_product_singular_exact_type
    {d : ℕ} (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (I : ProductGaussian μ) (n m : ℕ)
    (f : Fin n → Euc d → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (h : Fin m → Euc d → Euc d → ℝ)
    (hh : ∀ i, MemLp
      (fun z : Euc d × Euc d => h i z.1 z.2) 2 (μ.prod μ))
    (hs : ∀ i x y, h i x y = h i y x) :
    ∃ Q : Fin m → I.Ω → ℝ,
      (∀ i, MemLp (Q i) 2 I.P) ∧
      (∀ a, IsR2ZeroMeanONB μ a → ∀ i,
        IsR2WickChaos I.P μ a (fun j => I.η (a j))
          (r2CenterKernel μ (h i)) (fun ω => 2 * Q i ω)) ∧
      TendstoInDistribution
        (fun N (X : EucConfig d N) =>
          ((fun i : Fin n => Real.sqrt N *
            (HRS.Whole.pair (HRS.Whole.empirical X) (f i) - HRS.Whole.pair μ (f i))),
           (fun j : Fin m => (N : ℝ) * pairEnergy (h j) X μ))) atTop
        (fun ω => ((fun i : Fin n => I.η (f i) ω),
          (fun j : Fin m => Q j ω -
            (1 / 2 : ℝ) * ∫ x, ∫ y, h j x y ∂μ ∂μ)))
        (fun N => Measure.pi fun _ : Fin N => μ) I.P := by
  exact r26t3_product_singular μ I n m f hf h hh hs

#print axioms reviewer_r26t3_product_singular_exact_type
#print axioms r26t3_product_singular
end HRS.MS.R26T3
