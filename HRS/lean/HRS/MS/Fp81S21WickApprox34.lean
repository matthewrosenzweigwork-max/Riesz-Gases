import HRS.MS.Fp81S21WickApprox33
import HRS.MS.Fp81S21WickApprox4

/-! Operator approximation for the already selected physical Wick family. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- The generic operator estimate applies simultaneously to every supplied
physical realization, without reselecting its Wick operator or coefficients. -/
theorem fp81s21_quadraticPhysical31_rankKernel_profile
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (ε : ℕ → ℝ) (S : fp81s21_QuadraticPhysical31 p R Es E ε)
    (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (D : HRS.MS.R2S11.s11V p.d Λ → ℕ → fp81s21_RankKernel p.d)
    (B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (happrox : IsR2UniformApprox p.s C B (HRS.Whole.withDensityReal R.ρβ)
      (fun θ => commutatorKernel p.d p.s θ.1) (fun θ k => (D θ k).kernel)) :
    ∃ τ : ℕ → ℝ, (∀ k, 0 ≤ τ k) ∧ Tendsto τ atTop (𝓝 0) ∧
    ∀ G : GaussianRealization R, ∀ u : ℝ, 0 ≤ u →
    ∀ f : Euc p.d → ℝ, IsR2Test f →
    ∀ θ : HRS.MS.R2S11.s11V p.d Λ, θ.1 = gradient f → ∀ k : ℕ,
      ∃ hf : MemLp (fun xy : Euc p.d × Euc p.d => (D θ k).kernel xy.1 xy.2)
        2 ((HRS.Whole.withDensityReal R.ρβ).prod
          (HRS.Whole.withDensityReal R.ρβ)),
      fp81s21_SqErr G.P
        (fun ω => S.W G u (hf.toLp (fun xy => (D θ k).kernel xy.1 xy.2)) ω)
        (fun ω => fp81s21_wickChartField Es (S.qs G) u ω f) (τ k) := by
  let K : ℝ := S.Kstar ^ 2 / Real.sqrt 2
  have hK : 0 ≤ K := div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  obtain ⟨τ, hτ, hτlim, hprofile⟩ :=
    fp81s21_rankKernel_operator_profile p R Λ hΛ D B C K hB hC hK happrox
  refine ⟨τ, hτ, hτlim, ?_⟩
  intro G u hu f hf θ hθ k
  obtain ⟨hW, hT, hqe, hs, hw, hag, hrest⟩ := S.payload G
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
  have hWuNorm : ‖S.W G u‖ ≤ K := by
    rw [hWu]
    simpa [K, fp81s21_wickFam_operator, μ] using
      fp81s21_wickB311_operator_norm (S.T G u) S.Kstar hL hJ
  have hsquare := hprofile k θ G.P (S.W G u) hWuNorm hfr hg'
  have htarget :
      (fun ω => S.W G u (hg'.toLp (fun xy =>
        commutatorKernel p.d p.s θ.1 xy.1 xy.2)) ω) =ᵐ[G.P]
      (fun ω => fp81s21_wickChartField Es (S.qs G) u ω f) := by
    simpa [hθ, μ] using hfield.symm
  refine ⟨hfr, ?_⟩
  have heq :
      (fun ω => ‖S.W G u (hfr.toLp (fun xy => (D θ k).kernel xy.1 xy.2)) ω -
        S.W G u (hg'.toLp (fun xy => commutatorKernel p.d p.s θ.1 xy.1 xy.2)) ω‖ ^ 2) =ᵐ[G.P]
      (fun ω => ‖S.W G u (hfr.toLp (fun xy => (D θ k).kernel xy.1 xy.2)) ω -
        fp81s21_wickChartField Es (S.qs G) u ω f‖ ^ 2) := by
    filter_upwards [htarget] with ω hω
    rw [hω]
  exact ⟨hsquare.1.congr heq, by rw [← integral_congr_ae heq]; exact hsquare.2⟩

#print axioms fp81s21_quadraticPhysical31_rankKernel_profile
end HRS.Fp81.S21
end
