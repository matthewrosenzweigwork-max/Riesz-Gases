import HRS.MS.S21T4ProdAE

/-! S13: explicit finite-rank Gaussian polynomials converge to the singular Wick limit. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ}

theorem s21t4_round2_explicit_wick_approx {s M L B C : ℝ}
    {ρ : Euc d → ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (hρ : IsRound2Density d s M L ρ)
    {h : Euc d → Euc d → ℝ} (hh : IsBoundedPairKernel s B h)
    {hj : ℕ → Euc d → Euc d → ℝ}
    (hA : IsRound2Approx s C B (HRS.Whole.withDensityReal ρ) h hj)
    (I : ProductGaussian (HRS.Whole.withDensityReal ρ))
    (a : ℕ → Euc d → ℝ)
    (ha : IsR2ZeroMeanONB (HRS.Whole.withDensityReal ρ) a) :
    ∃ (m : ℕ → ℕ) (c : ∀ j, Fin (m j) → Fin (m j) → ℝ)
      (u : ∀ j, Fin (m j) → Euc d → ℝ) (Q : I.Ω → ℝ),
      (∀ j, IsR2FiniteRankData (c j) (u j) ∧ hj j = r2FiniteRankKernel (c j) (u j)) ∧
      s94WickL2 I.P (HRS.Whole.withDensityReal ρ) a
        (fun i ω => I.η (a i) ω)
        (r2CenterKernel (HRS.Whole.withDensityReal ρ) h) Q ∧
      Tendsto (fun j => eLpNorm (fun ω =>
        (∑ α : Fin (m j), ∑ β : Fin (m j), c j α β *
          (I.η (u j α) ω * I.η (u j β) ω -
            ∫ ζ, I.η (u j α) ζ * I.η (u j β) ζ ∂I.P)) - Q ω) 2 I.P)
        atTop (𝓝 0) := by
  letI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  letI := I.mΩ
  letI := I.prob
  let μ := HRS.Whole.withDensityReal ρ
  choose m c u hdata heq using hA.finiteRank
  have hz : S94GSeq I.P (fun i ω => I.η (a i) ω) 1 :=
    s21l_gseq (s21t4_product_eta_bundle I) ha.1 ha.2.1
  have hK : ∀ j, S94KOK μ (hj j) := by
    intro j
    rw [heq j]
    exact s21t4_finite_rank_KOK (c j) (u j) (hdata j)
  have hK0 : S94KOK μ h := s21t4_singular_kernel_KOK hd hs0 hs hρ hh
  let Qj : ℕ → I.Ω → ℝ := fun j ω =>
    ∑ α : Fin (m j), ∑ β : Fin (m j), c j α β *
      (I.η (u j α) ω * I.η (u j β) ω -
        ∫ ζ, I.η (u j α) ζ * I.η (u j β) ζ ∂I.P)
  have hWj : ∀ j, s94WickL2 I.P μ a (fun i ω => I.η (a i) ω)
      (r2CenterKernel μ (hj j)) (Qj j) := by
    intro j
    rw [heq j]
    exact s21t4_finite_rank_explicit_wick I a ha (c j) (u j) (hdata j)
  obtain ⟨Q, hQ, hlim⟩ := s94_chaos_conv hz zero_le_one ha.1 ha.2.1
    hK hK0 hWj (by
      simpa only [ENNReal.ofReal_ofNat] using
        hA.converges 2 (by norm_num) (by nlinarith))
  exact ⟨m, c, u, Q, fun j => ⟨hdata j, heq j⟩, hQ, hlim⟩

end HRS.MS.R26T3
