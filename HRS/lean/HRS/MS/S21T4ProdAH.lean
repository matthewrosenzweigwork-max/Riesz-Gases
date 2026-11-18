import HRS.MS.S21T4ProdAG
import HRS.MS.R2ChaosAux15

/-! S13: finite-rank centered pair-energy limit is one-half the explicit Wick polynomial. -/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_finite_rank_wick_offset (I : ProductGaussian μ)
    {m : ℕ} (c : Fin m → Fin m → ℝ) (u : Fin m → Euc d → ℝ)
    (hu : IsR2FiniteRankData c u) (ω : I.Ω) :
    (1 / 2 : ℝ) * ∑ i : Fin m, ∑ j : Fin m, c i j *
        (I.η (u i) ω * I.η (u j) ω - HRS.Whole.pair μ (fun x => u i x * u j x)) +
      (1 / 2 : ℝ) * ∫ x, ∫ y, r2FiniteRankKernel c u x y ∂μ ∂μ =
    (1 / 2 : ℝ) * ∑ i : Fin m, ∑ j : Fin m, c i j *
        (I.η (u i) ω * I.η (u j) ω -
          ∫ ζ, I.η (u i) ζ * I.η (u j) ζ ∂I.P) := by
  letI := I.mΩ
  letI := I.prob
  have ht : ∀ i, IsR2Test (u i) := fun i => ⟨hu.smooth i, hu.compactSupport i⟩
  rw [s94_integral_finiteRank_both (μ := μ) (c := c) ht]
  have hm : ∀ i : Fin m, MemLp (u i) 2 μ := fun i =>
    (hu.smooth i).continuous.memLp_of_hasCompactSupport (hu.compactSupport i)
  have hcov : ∀ i j : Fin m,
      (∫ ζ, I.η (u i) ζ * I.η (u j) ζ ∂I.P) =
      HRS.Whole.pair μ (fun x => u i x * u j x) -
        HRS.Whole.pair μ (u i) * HRS.Whole.pair μ (u j) := by
    intro i j
    have h := s21t4_product_covariance_shift I (u i) (u j) (hm i) (hm j)
    linarith
  have hp : ∀ i j : Fin m,
      c i j * (I.η (u i) ω * I.η (u j) ω -
        (HRS.Whole.pair μ (fun x => u i x * u j x) -
          HRS.Whole.pair μ (u i) * HRS.Whole.pair μ (u j))) =
        c i j * (I.η (u i) ω * I.η (u j) ω -
          HRS.Whole.pair μ (fun x => u i x * u j x)) +
        c i j * HRS.Whole.pair μ (u i) * HRS.Whole.pair μ (u j) := by
    intros; ring
  simp_rw [hcov, hp, Finset.sum_add_distrib]
  ring

end HRS.MS.R26T3
