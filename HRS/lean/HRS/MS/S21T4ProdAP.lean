import HRS.MS.S21T4ProdAO

/-! S13: additivity of the twofold mean, with all Bochner-integrability hypotheses checked. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ}

theorem s21t4_round2_mean_sub {s M L B C : ℝ}
    {ρ : Euc d → ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (hρ : IsRound2Density d s M L ρ)
    {h : Euc d → Euc d → ℝ} (hh : IsBoundedPairKernel s B h)
    {hj : ℕ → Euc d → Euc d → ℝ}
    (hA : IsRound2Approx s C B (HRS.Whole.withDensityReal ρ) h hj)
    (j : ℕ) :
    (∫ x, ∫ y, (hj j x y - h x y)
      ∂(HRS.Whole.withDensityReal ρ)
      ∂(HRS.Whole.withDensityReal ρ)) =
    (∫ x, ∫ y, hj j x y
      ∂(HRS.Whole.withDensityReal ρ)
      ∂(HRS.Whole.withDensityReal ρ)) -
    (∫ x, ∫ y, h x y
      ∂(HRS.Whole.withDensityReal ρ)
      ∂(HRS.Whole.withDensityReal ρ)) := by
  let μ := HRS.Whole.withDensityReal ρ
  letI : IsProbabilityMeasure μ := HRS.Whole.U1.u1_isProb hρ.prob
  have hH : S94KOK μ h := s21t4_singular_kernel_KOK hd hs0 hs hρ hh
  obtain ⟨m, c, u, hdata, heq⟩ := hA.finiteRank j
  have hHj : S94KOK μ (hj j) := by
    rw [heq]
    exact s21t4_finite_rank_KOK c u hdata
  have hsub : (∫ x, ∫ y, (hj j x y - h x y) ∂μ ∂μ) =
      (∫ x, ∫ y, hj j x y ∂μ ∂μ) -
      (∫ x, ∫ y, h x y ∂μ ∂μ) := by
    rw [← integral_sub hHj.hc hH.hc]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x =>
      integral_sub (hHj.row x) (hH.row x)
  exact hsub

end HRS.MS.R26T3
