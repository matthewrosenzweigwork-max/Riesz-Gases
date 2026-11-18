import HRS.MS.Fp81S21WickApprox6
import HRS.MS.Fp81S21WickFam16

/-! Jointly measurable supplied-Gaussian finite-rank kernel outputs. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- The rank-kernel approximants have jointly measurable representatives on
 the supplied Gaussian space, with every nonnegative-time section representing
 the same operator used for the coherent chart field and the uniform profile. -/
theorem fp81s21_wick_rankKernel_joint_profile (p : Parameters) :
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
        ∀ (θ : HRS.MS.R2S11.s11V p.d Λ) (k : ℕ),
        ∃ hf : MemLp (fun xy : Euc p.d × Euc p.d => (D θ k).kernel xy.1 xy.2) 2
          ((HRS.Whole.withDensityReal R.ρβ).prod (HRS.Whole.withDensityReal R.ρβ)),
        ∃ F : ℝ × G.Ω → ℝ, Measurable F ∧
          (∀ u : ℝ, 0 ≤ u →
            MemLp (fun ω => F (u, ω)) 2 G.P ∧
            (fun ω => F (u, ω)) =ᵐ[G.P]
              (W u (hf.toLp (fun xy => (D θ k).kernel xy.1 xy.2)) : G.Ω → ℝ)) ∧
          ∀ u : ℝ, 0 ≤ u → ∀ f : Euc p.d → ℝ, IsR2Test f →
            θ.1 = gradient f →
            fp81s21_SqErr G.P (fun ω => F (u, ω))
              (fun ω => fp81s21_wickChartField Es q u ω f) (τ k) := by
  obtain ⟨δa, hδa, hδah, ha⟩ := fp81s21_wick_rankKernel_supplied_profile p
  obtain ⟨δb, hδb, hδbh, hb⟩ := fp81s21_wickFam_linear_family_continuous p
  refine ⟨min δa δb, lt_min hδa hδb, (min_le_left _ _).trans hδah, ?_⟩
  intro δ hδ hδle R Es E Λ hΛ D B C hB hC happrox
  obtain ⟨K, hK, τ, hτ, hτlim, hG⟩ :=
    ha δ hδ (hδle.trans (min_le_left _ _)) R Es E Λ hΛ D B C hB hC happrox
  refine ⟨τ, hτ, hτlim, ?_⟩
  intro G
  obtain ⟨T, W, q, M, hW, hag, hrep, herr⟩ := hG G
  have hc := hb δ hδ (hδle.trans (min_le_right _ _)) R G T K
    (fun u hu => (hW u hu).choose)
    (fun u hu α hα => hag u hu _ (HRS.MS.GenPath.s56_isOscTest _ α) hα)
  have hjoint := fp81s21_wickFam_supplied_wick_continuous_joint p R K G T W hW hag hc
  refine ⟨W, q, M, hrep, ?_⟩
  intro θ k
  let μ := HRS.Whole.withDensityReal R.ρβ
  letI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  have hdata : ∀ i, IsR2Test ((D θ k).u i) :=
    fun i => ⟨(D θ k).valid.smooth i, (D θ k).valid.compactSupport i⟩
  have hf : MemLp (fun xy : Euc p.d × Euc p.d => (D θ k).kernel xy.1 xy.2)
      2 (μ.prod μ) := HRS.MS.R2Chaos.s94_finiteRank_memLp hdata
  obtain ⟨F, hFm, hF⟩ := (hjoint (hf.toLp (fun xy => (D θ k).kernel xy.1 xy.2))).2
  refine ⟨hf, F, hFm, hF, ?_⟩
  intro u hu f htest hθ
  obtain ⟨hf', hs⟩ := herr u hu f htest θ hθ k
  have heq : (fun ω => ‖F (u, ω) - fp81s21_wickChartField Es q u ω f‖ ^ 2) =ᵐ[G.P]
      (fun ω => ‖W u (hf'.toLp (fun xy => (D θ k).kernel xy.1 xy.2)) ω -
        fp81s21_wickChartField Es q u ω f‖ ^ 2) := by
    filter_upwards [(hF u hu).2] with ω hω
    rw [hω]
  exact ⟨hs.1.congr heq.symm, by rw [integral_congr_ae heq]; exact hs.2⟩

#print axioms fp81s21_wick_rankKernel_joint_profile
end HRS.Fp81.S21
end
