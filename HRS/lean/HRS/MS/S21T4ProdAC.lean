import HRS.MS.S21T4ProdAB
import HRS.MS.R2ChaosAux57

/-! S13: verify the genuine Wick-continuity domain for singular approximants. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ}

theorem s21t4_finite_rank_KOK {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    {m : ℕ} (c : Fin m → Fin m → ℝ) (u : Fin m → Euc d → ℝ)
    (hu : IsR2FiniteRankData c u) : S94KOK μ (r2FiniteRankKernel c u) := by
  have ht : ∀ a, IsR2Test (u a) := fun a => ⟨hu.smooth a, hu.compactSupport a⟩
  obtain ⟨hrow, _, hc⟩ := s94_finiteRank_integrable_facts (μ := μ) (c := c) ht
  exact ⟨s94_finiteRank_measurable ht,
    s21t4_finite_rank_symmetric c u hu,
    s21t4_finite_rank_memLp c u hu,
    hrow, hc⟩

theorem s21t4_singular_kernel_KOK {s M L B : ℝ} {ρ : Euc d → ℝ}
    (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (hρ : IsRound2Density d s M L ρ)
    {h : Euc d → Euc d → ℝ} (hh : IsBoundedPairKernel s B h) :
    S94KOK (HRS.Whole.withDensityReal ρ) h := by
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  obtain ⟨hrow, _, hc⟩ := s94_env_facts hd hs0 hs hρ hh
  exact ⟨hh.measurable, hh.symm, s94_env_memLp hd hs0 hs hρ hh, hrow, hc⟩

end HRS.MS.R26T3
