import HRS.MS.Fp81S21WickApprox4
import HRS.MS.Fp81S21WickMomRep8

/-! Supplied-Gaussian fixed-time finite-rank replacement. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- The Gaussian profile uses the same rank family as the particle bound and
compares to the coherent chart-action field for every compact test separately. -/
theorem fp81s21_wick_rankKernel_profile (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4),
      ∀ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
      ∀ Λ : ℝ, 0 ≤ Λ →
      ∀ D : HRS.MS.R2S11.s11V p.d Λ → ℕ → fp81s21_RankKernel p.d,
      ∀ B C : ℝ, 0 ≤ B → 0 ≤ C →
      IsR2UniformApprox p.s C B (HRS.Whole.withDensityReal R.ρβ)
        (fun θ => commutatorKernel p.d p.s θ.1) (fun θ k => (D θ k).kernel) →
      ∃ τ : ℕ → ℝ, (∀ k, 0 ≤ τ k) ∧ Tendsto τ atTop (𝓝 0) ∧
      ∀ G : GaussianRealization R,
      ∃ W : ℝ → Lp ℝ 2 ((HRS.Whole.withDensityReal R.ρβ).prod
        (HRS.Whole.withDensityReal R.ρβ)) →L[ℝ] Lp ℝ 2 G.P,
      ∃ q : ℝ → G.Ω → r26t6_Coeff, ∃ M : ℝ,
        fp81s21_MomentRep Es G.P (fp81s21_wickChartField Es q) q M ∧
        ∀ u : ℝ, 0 ≤ u → ∀ f : Euc p.d → ℝ, IsR2Test f →
        ∀ θ : HRS.MS.R2S11.s11V p.d Λ, θ.1 = gradient f → ∀ k : ℕ,
          ∃ hf : MemLp (fun xy : Euc p.d × Euc p.d => (D θ k).kernel xy.1 xy.2) 2
            ((HRS.Whole.withDensityReal R.ρβ).prod (HRS.Whole.withDensityReal R.ρβ)),
          fp81s21_SqErr G.P
            (fun ω => W u (hf.toLp (fun xy => (D θ k).kernel xy.1 xy.2)) ω)
            (fun ω => fp81s21_wickChartField Es q u ω f) (τ k) := by
  obtain ⟨δ0, hδ0, hhalf, hphysical⟩ := fp81s21_wick_momentRep_physical p
  refine ⟨δ0, hδ0, hhalf, ?_⟩
  intro δ hδ hδle R Es E Λ hΛ D B C hB hC happrox
  obtain ⟨Kstar, Bstar, hKstar, hBstar, hG⟩ := hphysical δ hδ hδle R Es E
  let K : ℝ := Kstar ^ 2 / Real.sqrt 2
  have hK : 0 ≤ K := div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  obtain ⟨τ, hτ, hτlim, hprofile⟩ :=
    fp81s21_rankKernel_operator_profile p R Λ hΛ D B C K hB hC hK happrox
  refine ⟨τ, hτ, hτlim, ?_⟩
  intro G
  obtain ⟨T, W, q, hW, hT, hs, hw, hag, hfirst⟩ := hG G
  refine ⟨W, q, Kstar ^ 4 * Bstar / 2, hs, ?_⟩
  intro u hu f hf θ hθ k
  let μ := HRS.Whole.withDensityReal R.ρβ
  letI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  have hdata : ∀ i, IsR2Test ((D θ k).u i) :=
    fun i => ⟨(D θ k).valid.smooth i, (D θ k).valid.compactSupport i⟩
  have hfr : MemLp (fun xy : Euc p.d × Euc p.d => (D θ k).kernel xy.1 xy.2)
      2 (μ.prod μ) := HRS.MS.R2Chaos.s94_finiteRank_memLp hdata
  obtain ⟨hg, hfield⟩ := hag u hu f hf
  have hg' : MemLp (fun xy : Euc p.d × Euc p.d =>
      commutatorKernel p.d p.s θ.1 xy.1 xy.2) 2 (μ.prod μ) := by
    simpa [hθ, μ] using hg
  obtain ⟨hL, hJ, hWu⟩ := hW u hu
  have hWuNorm : ‖W u‖ ≤ K := by
    rw [hWu]
    simpa [K, fp81s21_wickFam_operator, μ] using
      fp81s21_wickB311_operator_norm (T u) Kstar hL hJ
  have hsquare := hprofile k θ G.P (W u) hWuNorm hfr hg'
  have htarget : (fun ω => W u (hg'.toLp (fun xy =>
      commutatorKernel p.d p.s θ.1 xy.1 xy.2)) ω) =ᵐ[G.P]
      (fun ω => fp81s21_wickChartField Es q u ω f) := by
    simpa [hθ, μ] using hfield.symm
  refine ⟨hfr, ?_⟩
  have heq : (fun ω => ‖W u (hfr.toLp (fun xy => (D θ k).kernel xy.1 xy.2)) ω -
      W u (hg'.toLp (fun xy => commutatorKernel p.d p.s θ.1 xy.1 xy.2)) ω‖ ^ 2) =ᵐ[G.P]
      (fun ω => ‖W u (hfr.toLp (fun xy => (D θ k).kernel xy.1 xy.2)) ω -
        fp81s21_wickChartField Es q u ω f‖ ^ 2) := by
    filter_upwards [htarget] with ω hω
    rw [hω]
  exact ⟨hsquare.1.congr heq, by rw [← integral_congr_ae heq]; exact hsquare.2⟩

#print axioms fp81s21_wick_rankKernel_profile
end HRS.Fp81.S21
end
