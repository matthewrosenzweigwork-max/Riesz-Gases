import HRS.MS.Fp81S21JointN4

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- One shared rank family gives the particle joint error, with a diagonal
constant uniform in particle count, as well as the Gaussian joint error. -/
theorem fp81s21_jointN_sqerr_physical (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
    ∀ εN εG εB : ℕ → ℝ,
    (∀ m, 0 ≤ εN m) → (∀ m, 0 ≤ εG m) → (∀ m, 0 ≤ εB m) →
    ∀ S : fp81s21_Physical31 p R Es E εN εG εB,
    ∀ m : ℕ, ∃ Λ : ℝ, ∃ θ : Fin m → HRS.MS.R2S11.s11V p.d Λ,
    ∃ D : HRS.MS.R2S11.s11V p.d Λ → ℕ → fp81s21_RankKernel p.d,
    0 ≤ Λ ∧ (∀ j, (θ j).1 = gradient (E.test j)) ∧
    ∃ τN τG : ℕ → ℝ, (∀ k, 0 ≤ τN k) ∧ (∀ k, 0 ≤ τG k) ∧
    Tendsto τN atTop (𝓝 0) ∧ Tendsto τG atTop (𝓝 0) ∧
    (∀ H : ℝ, ∀ hH : 0 < H, ∀ k : ℕ, ∃ Ddiag : ℝ, 0 ≤ Ddiag ∧
      ∀ N : ℕ, ∀ hN : 2 ≤ N, ∀ A : Particle R N, ∀ a : ℝ, 0 ≤ a →
      ∀ Uη UB : A.Ω → fp81s21_jointP_U H,
      fp81s21_TimeL2Rep A.P
        (fun u ω => fp81s21_particle_embedField p Es E (S.qsηN N hN A u ω)) S.MN a H Uη →
      fp81s21_TimeL2Rep A.P
        (fun u ω => fp81s21_particle_embedField p Es E (S.qsBN N hN A u ω)) S.MN a H UB →
      fp81s21_SqErr A.P (fun ω => (Uη ω, UB ω))
        (fun ω => fp81s21_jointP_map H hH E m (fun j => D (θ j) k)
            (flucPathW (wholeSpaceIndex p.d : ℝ) H a (Real.sqrt (N : ℝ)) A.X R.ρ ω) -
          fp81s21_jointC_partialCenter H (∫ ω',
            fp81s21_jointP_map H hH E m (fun j => D (θ j) k)
              (flucPathW (wholeSpaceIndex p.d : ℝ) H a (Real.sqrt (N : ℝ)) A.X R.ρ ω') ∂A.P))
        (Real.sqrt (H * S.MN) * εN m + Real.sqrt (H * S.MN) * εN m +
          Real.sqrt (H * (m : ℝ)) * τN k + Ddiag / Real.sqrt (N : ℝ))) ∧
    (∀ H : ℝ, ∀ hH : 0 < H, ∀ G : GaussianRealization R, ∀ a : ℝ, 0 ≤ a →
      ∀ Vη VB : G.Ω → fp81s21_jointP_U H,
      fp81s21_TimeL2Rep G.P
        (fp81s21_gaussian_embedFamily p Es E (S.gaussian.qsηG G)) S.gaussian.MηG a H Vη →
      fp81s21_TimeL2Rep G.P (S.gaussian.quadratic.qe G)
        (S.gaussian.quadratic.Kstar ^ 4 * S.gaussian.quadratic.B / 2) a H VB →
      ∀ k : ℕ,
        fp81s21_SqErr G.P (fun ω => (Vη ω, VB ω))
          (fun ω => fp81s21_jointP_map H hH E m (fun j => D (θ j) k)
              (processWindow (wholeSpaceIndex p.d : ℝ) H a G.Z ω) -
            fp81s21_jointG_partialCenter H (∫ ω',
              fp81s21_jointP_map H hH E m (fun j => D (θ j) k)
                (processWindow (wholeSpaceIndex p.d : ℝ) H a G.Z ω') ∂G.P))
          (Real.sqrt (H * S.gaussian.MηG) * εG m +
            Real.sqrt (H * (S.gaussian.quadratic.Kstar ^ 4 * S.gaussian.quadratic.B / 2)) * εB m +
            Real.sqrt (H * (m : ℝ)) * τG k + 0)) := by
  obtain ⟨δa, ha, hah, hfixed⟩ := fp81s21_jointN_sqerr_physical_fixed_rank p Es E
  obtain ⟨δb, hb, hbh, hboth⟩ := fp81s21_jointG_physical31_both_time p
  refine ⟨min δa δb, lt_min ha hb, (min_le_left _ _).trans hah, ?_⟩
  intro δ hδ hδle R εN εG εB hεN hεG hεB S m
  have hf := hfixed δ hδ (hδle.trans (min_le_left _ _)) R εN εG εB S m (hεN m)
  obtain ⟨Λ, θ, D, hΛ, hθ, τN, τG, hτN, hτG, hτNlim, hτGlim, hp, hg⟩ :=
    hboth δ hδ (hδle.trans (min_le_right _ _)) R Es E εN εG εB hεG hεB S m
  refine ⟨Λ, θ, D, hΛ, hθ, τN, τG, hτN, hτG, hτNlim, hτGlim, ?_, hg⟩
  intro H hH k
  obtain ⟨Ddiag, hDdiag, hbound⟩ := hf Λ θ D k H hH
  refine ⟨Ddiag, hDdiag, ?_⟩
  intro N hN A a ha Uη UB hUη hUB
  obtain ⟨Ur, hUr, hker⟩ := hp H hH N hN A a ha UB hUB k
  exact hbound N hN A a ha Uη UB hUη hUB (τN k) (hτN k) Ur hUr hker

#print axioms fp81s21_jointN_sqerr_physical
end HRS.Fp81.S21
end
