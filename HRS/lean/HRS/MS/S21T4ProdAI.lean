import HRS.MS.S21T4ProdAH

/-! R26-T3.S13: centered finite-rank joint CLT with canonical half-Wick limit. -/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_finite_rank_centered_joint_clt
    (I : ProductGaussian μ) {n m : ℕ}
    (f : Fin n → Euc d → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (c : Fin m → Fin m → ℝ) (u : Fin m → Euc d → ℝ)
    (hu : IsR2FiniteRankData c u) :
    TendstoInDistribution
      (fun N (X : EucConfig d N) =>
        ((fun i => Real.sqrt N *
          (HRS.Whole.pair (HRS.Whole.empirical X) (f i) - HRS.Whole.pair μ (f i))),
         (N : ℝ) * pairEnergy (r2FiniteRankKernel c u) X μ +
           (1 / 2) * ∫ x, ∫ y, r2FiniteRankKernel c u x y ∂μ ∂μ)) atTop
      (fun ω : I.Ω =>
        ((fun i => I.η (f i) ω),
         (1 / 2) * ∑ i : Fin m, ∑ j : Fin m, c i j *
           (I.η (u i) ω * I.η (u j) ω -
             ∫ ζ, I.η (u i) ζ * I.η (u j) ζ ∂I.P)))
      (fun N => Measure.pi fun _ : Fin N => μ) I.P := by
  letI := I.mΩ
  letI := I.prob
  let b : ℝ := (1 / 2) * ∫ x, ∫ y, r2FiniteRankKernel c u x y ∂μ ∂μ
  let F : ((Fin n → ℝ) × ℝ) → (Fin n → ℝ) × ℝ :=
    fun z => (z.1, z.2 + b)
  have hF : Continuous F := continuous_fst.prodMk (continuous_snd.add continuous_const)
  have h := (s21t4_finite_rank_joint_one_space I f hf c u hu).continuous_comp hF
  have hX : (fun N (X : EucConfig d N) =>
        ((fun i => Real.sqrt N *
          (HRS.Whole.pair (HRS.Whole.empirical X) (f i) - HRS.Whole.pair μ (f i))),
         (N : ℝ) * pairEnergy (r2FiniteRankKernel c u) X μ +
           (1 / 2) * ∫ x, ∫ y, r2FiniteRankKernel c u x y ∂μ ∂μ)) =
      (fun N (X : EucConfig d N) =>
        F ((fun i => Real.sqrt N *
          (HRS.Whole.pair (HRS.Whole.empirical X) (f i) - HRS.Whole.pair μ (f i))),
           (N : ℝ) * pairEnergy (r2FiniteRankKernel c u) X μ)) := rfl
  have hZ : (fun ω : I.Ω =>
        ((fun i => I.η (f i) ω),
         (1 / 2) * ∑ i : Fin m, ∑ j : Fin m, c i j *
           (I.η (u i) ω * I.η (u j) ω -
             ∫ ζ, I.η (u i) ζ * I.η (u j) ζ ∂I.P))) =
    (fun ω : I.Ω =>
      F ((fun i => I.η (f i) ω),
        (1 / 2) * ∑ i : Fin m, ∑ j : Fin m, c i j *
          (I.η (u i) ω * I.η (u j) ω - HRS.Whole.pair μ (fun x => u i x * u j x)))) := by
    funext ω
    apply Prod.ext
    · rfl
    · exact (s21t4_finite_rank_wick_offset I c u hu ω).symm
  rw [hX, hZ]
  exact h

end HRS.MS.R26T3
