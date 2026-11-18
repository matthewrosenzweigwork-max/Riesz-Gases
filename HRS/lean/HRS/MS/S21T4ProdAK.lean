import HRS.MS.S21T4ProdAJ
import HRS.MS.R2ChaosAux57

/-! S13: quantitative Gaussian Wick comparison in the physical S9.1 kernel class. -/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ}

theorem s21t4_round2_gaussian_sq_bound {s M L B C : ℝ}
    {ρ : Euc d → ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (hρ : IsRound2Density d s M L ρ)
    {h : Euc d → Euc d → ℝ} (hh : IsBoundedPairKernel s B h)
    {hj : ℕ → Euc d → Euc d → ℝ}
    (hA : IsRound2Approx s C B (HRS.Whole.withDensityReal ρ) h hj)
    (I : ProductGaussian (HRS.Whole.withDensityReal ρ))
    (a : ℕ → Euc d → ℝ)
    (ha : IsR2ZeroMeanONB (HRS.Whole.withDensityReal ρ) a)
    (Q : I.Ω → ℝ) (Qj : ℕ → I.Ω → ℝ)
    (hQ : s94WickL2 I.P (HRS.Whole.withDensityReal ρ) a
      (fun i ω => I.η (a i) ω)
      (r2CenterKernel (HRS.Whole.withDensityReal ρ) h) Q)
    (hQj : ∀ j, s94WickL2 I.P (HRS.Whole.withDensityReal ρ) a
      (fun i ω => I.η (a i) ω)
      (r2CenterKernel (HRS.Whole.withDensityReal ρ) (hj j)) (Qj j))
    (j : ℕ) :
    (∫ ω, (Qj j ω - Q ω) ^ 2 ∂I.P) ≤
      32 * ∫ z : Euc d × Euc d, (hj j z.1 z.2 - h z.1 z.2) ^ 2
        ∂((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)) := by
  letI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) :=
    HRS.Whole.U1.u1_isProb hρ.prob
  letI := I.mΩ
  letI := I.prob
  let μ := HRS.Whole.withDensityReal ρ
  obtain ⟨m, c, u, hdata, heq⟩ := hA.finiteRank j
  have hht : ∀ i, IsR2Test (u i) := fun i =>
    ⟨hdata.smooth i, hdata.compactSupport i⟩
  have hHj : S94KOK μ (hj j) := by
    rw [heq]
    exact s21t4_finite_rank_KOK c u hdata
  have hH : S94KOK μ h := s21t4_singular_kernel_KOK hd hs0 hs hρ hh
  have hcenter : eLpNorm
      (fun z : Euc d × Euc d =>
        r2CenterKernel μ h z.1 z.2 - r2CenterKernel μ (hj j) z.1 z.2)
      2 (μ.prod μ) ≤
      4 * eLpNorm (fun z : Euc d × Euc d =>
        h z.1 z.2 - hj j z.1 z.2) 2 (μ.prod μ) := by
    rw [heq]
    exact s94_center_diff_le hd hs0 hs hρ hh hht
  have hm : MemLp (fun z : Euc d × Euc d => h z.1 z.2 - hj j z.1 z.2)
      2 (μ.prod μ) := hH.memLp.sub hHj.memLp
  have hcm : MemLp (fun z : Euc d × Euc d =>
      r2CenterKernel μ h z.1 z.2 - r2CenterKernel μ (hj j) z.1 z.2)
      2 (μ.prod μ) :=
    (s21h2_c_memLp μ hH.memLp).sub (s21h2_c_memLp μ hHj.memLp)
  set D : ℝ≥0∞ :=
    eLpNorm (fun z : Euc d × Euc d => h z.1 z.2 - hj j z.1 z.2) 2 (μ.prod μ)
  have hDfin : D ≠ ⊤ := hm.eLpNorm_ne_top
  have hb : eLpNorm
      (fun z : Euc d × Euc d =>
        r2CenterKernel μ h z.1 z.2 - r2CenterKernel μ (hj j) z.1 z.2)
      2 (μ.prod μ) ≤ ENNReal.ofReal (4 * D.toReal) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hDfin]
    simpa [D] using hcenter
  have hcenter2 : (∫ z : Euc d × Euc d,
      (r2CenterKernel μ h z.1 z.2 -
        r2CenterKernel μ (hj j) z.1 z.2) ^ 2 ∂(μ.prod μ)) ≤
        (4 * D.toReal) ^ 2 :=
    s94_integral_sq_le_of_eLpNorm hcm.aestronglyMeasurable
      (by positivity) hb
  have hwick : (∫ ω, (Qj j ω - Q ω) ^ 2 ∂I.P) ≤
      2 * (1 : ℝ) ^ 2 * (∫ z : Euc d × Euc d,
        (r2CenterKernel μ (hj j) z.1 z.2 -
          r2CenterKernel μ h z.1 z.2) ^ 2 ∂(μ.prod μ)) :=
    s94_wick_lipschitz
      (s21l_gseq (s21t4_product_eta_bundle I) ha.1 ha.2.1)
      zero_le_one ha.1 ha.2.1
      (s94_center_measurable hHj.meas) (s94_center_symm hHj.symm)
      (s21h2_c_memLp μ hHj.memLp)
      (s94_center_measurable hH.meas) (s94_center_symm hH.symm)
      (s21h2_c_memLp μ hH.memLp)
      (hQj j) hQ
  have hdiff2 : (∫ z : Euc d × Euc d,
      (r2CenterKernel μ (hj j) z.1 z.2 -
        r2CenterKernel μ h z.1 z.2) ^ 2 ∂(μ.prod μ)) =
      ∫ z : Euc d × Euc d,
      (r2CenterKernel μ h z.1 z.2 -
        r2CenterKernel μ (hj j) z.1 z.2) ^ 2 ∂(μ.prod μ) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by ring
  rw [hdiff2] at hwick
  have hD : D.toReal ^ 2 =
      (∫ z : Euc d × Euc d, (hj j z.1 z.2 - h z.1 z.2) ^ 2 ∂(μ.prod μ)) := by
    rw [← s21t4_integral_sq_of_eLpNorm (f := fun z : Euc d × Euc d =>
      h z.1 z.2 - hj j z.1 z.2) hm]
    congr 1
    funext z
    ring
  nlinarith

end HRS.MS.R26T3
