import HRS.MS.S21T4ProdT
import HRS.MS.S21G2_S12

/-! R26-T3.S13: finite-rank joint CLT on the original product-Gaussian space. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_finite_rank_joint_common
    (I : ProductGaussian μ) {n m : ℕ}
    (f : Fin n → Euc d → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (c : Fin m → Fin m → ℝ) (u : Fin m → Euc d → ℝ)
    (hu : IsR2FiniteRankData c u) :
    TendstoInDistribution
      (fun N (X : EucConfig d N) =>
        ((fun i => Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) (f i) - HRS.Whole.pair μ (f i))),
         (N : ℝ) * pairEnergy (r2FiniteRankKernel c u) X μ)) atTop
      (fun z => (z.1,
        (1 / 2) * ∑ i, ∑ j, c i j *
          (z.2 i * z.2 j - HRS.Whole.pair μ (fun x => u i x * u j x))))
      (fun N => Measure.pi fun _ : Fin N => μ)
      (I.P.map (fun ω =>
        ((fun i => I.η (f i) ω), (fun j => I.η (u j) ω)))) := by
  letI := I.mΩ
  letI := I.prob
  have hu2 : ∀ j, MemLp (u j) 2 μ := fun j =>
    (hu.smooth j).continuous.memLp_of_hasCompactSupport (hu.compactSupport j)
  obtain ⟨G, hGP, hG, hcov, hconv⟩ :=
    r26t3_product_finite_rank μ f hf c u hu
  have hGid := s21t4_finite_rank_gaussian_identification I f u hf hu2 G hG hcov
  subst G
  exact hconv

end HRS.MS.R26T3
