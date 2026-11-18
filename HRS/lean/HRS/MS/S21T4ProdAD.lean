import HRS.MS.S21T4ProdAC
import HRS.MS.R2ChaosAux56

/-! S13: Gaussian Wick limit follows continuously from native S9.1 approximation. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ}

theorem s21t4_round2_gaussian_chaos_approx {s M L B C : ℝ}
    {ρ : Euc d → ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (hρ : IsRound2Density d s M L ρ)
    {h : Euc d → Euc d → ℝ} (hh : IsBoundedPairKernel s B h)
    {hj : ℕ → Euc d → Euc d → ℝ}
    (hA : IsRound2Approx s C B (HRS.Whole.withDensityReal ρ) h hj)
    (I : ProductGaussian (HRS.Whole.withDensityReal ρ))
    (a : ℕ → Euc d → ℝ)
    (ha : IsR2ZeroMeanONB (HRS.Whole.withDensityReal ρ) a) :
    ∃ (Q : I.Ω → ℝ) (Qj : ℕ → I.Ω → ℝ),
      s94WickL2 I.P (HRS.Whole.withDensityReal ρ) a
        (fun i ω => I.η (a i) ω)
        (r2CenterKernel (HRS.Whole.withDensityReal ρ) h) Q ∧
      (∀ j, s94WickL2 I.P (HRS.Whole.withDensityReal ρ) a
        (fun i ω => I.η (a i) ω)
        (r2CenterKernel (HRS.Whole.withDensityReal ρ) (hj j)) (Qj j)) ∧
      Tendsto (fun j => eLpNorm (fun ω => Qj j ω - Q ω) 2 I.P)
        atTop (𝓝 0) := by
  letI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  letI := I.mΩ
  letI := I.prob
  let μ := HRS.Whole.withDensityReal ρ
  have hz : S94GSeq I.P (fun i ω => I.η (a i) ω) 1 :=
    s21l_gseq (s21t4_product_eta_bundle I) ha.1 ha.2.1
  choose m c u hdata heq using hA.finiteRank
  have hK : ∀ j, S94KOK μ (hj j) := by
    intro j
    rw [heq j]
    exact s21t4_finite_rank_KOK (c j) (u j) (hdata j)
  have hK0 : S94KOK μ h := s21t4_singular_kernel_KOK hd hs0 hs hρ hh
  have hcen : ∀ j, MemLp
      (fun z : Euc d × Euc d => r2CenterKernel μ (hj j) z.1 z.2) 2
      (μ.prod μ) := by
    intro j
    exact lt_of_le_of_lt (s94_eLpNorm_center_le (hK j).meas)
      (ENNReal.mul_lt_top (by norm_num) (lt_top_iff_ne_top.mpr (hK j).memLp.eLpNorm_ne_top))
  have hQexists : ∀ j, ∃ Q : I.Ω → ℝ,
      s94WickL2 I.P μ a (fun i ω => I.η (a i) ω)
        (r2CenterKernel μ (hj j)) Q := by
    intro j
    obtain ⟨Q, hQ, _⟩ := s94_wick_exists hz zero_le_one ha.1 ha.2.1
      (s94_center_measurable (hK j).meas)
      (s94_center_symm (hK j).symm) (hcen j)
    exact ⟨Q, hQ⟩
  choose Qj hQj using hQexists
  obtain ⟨Q, hQ, hlim⟩ := s94_chaos_conv hz zero_le_one ha.1 ha.2.1
    hK hK0 hQj (by
      simpa only [ENNReal.ofReal_ofNat] using
        hA.converges 2 (by norm_num) (by nlinarith))
  exact ⟨Q, Qj, hQ, hQj, hlim⟩

end HRS.MS.R26T3
