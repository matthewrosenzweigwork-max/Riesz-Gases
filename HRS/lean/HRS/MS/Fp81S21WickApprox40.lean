import HRS.MS.Fp81S21WickApprox39

/-! The shared-rank approximation for fixed physical selections. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- A genuine particle time section of the selected finite-rank kernels. -/
def fp81s21_ParticleRankTime31 (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (m : ℕ) (Λ : ℝ) (θ : Fin m → HRS.MS.R2S11.s11V p.d Λ)
    (D : HRS.MS.R2S11.s11V p.d Λ → ℕ → fp81s21_RankKernel p.d)
    (k N : ℕ) (A : Particle R N) (a H : ℝ)
    (U : A.Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) : Prop :=
  ∃ Mq : ℝ, ∃ q : ℝ → A.Ω → r26t6_Coeff,
    Measurable (Function.uncurry q) ∧
    (∀ᵐ ω ∂A.P, ∀ u, 0 ≤ u → q u ω = ∑ j : Fin m,
      fp81s21_particleQuad A u (D (θ j) k).kernel ω • fp81s21_coeffBasis j) ∧
    fp81s21_TimeL2Rep A.P q Mq a H U

/-- A genuine Gaussian time section using the already selected Wick operator. -/
def fp81s21_GaussianRankTime31 (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (ε : ℕ → ℝ) (S : fp81s21_QuadraticPhysical31 p R Es E ε)
    (m : ℕ) (Λ : ℝ) (θ : Fin m → HRS.MS.R2S11.s11V p.d Λ)
    (D : HRS.MS.R2S11.s11V p.d Λ → ℕ → fp81s21_RankKernel p.d)
    (k : ℕ) (G : GaussianRealization R) (a H : ℝ)
    (U : G.Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) : Prop :=
  ∃ Mq : ℝ, ∃ q : ℝ → G.Ω → r26t6_Coeff,
    Measurable (Function.uncurry q) ∧
    (∀ u, 0 ≤ u → ∀ᵐ ω ∂G.P, ∀ j : ℕ,
      q u ω j = if hj : j < m then
        (S.W G u (fp81s21_rankKernelLp R (D (θ ⟨j, hj⟩) k)) : G.Ω → ℝ) ω
      else 0) ∧
    fp81s21_TimeL2Rep G.P q Mq a H U

/-- One rank family works for arbitrary representatives of the fixed physical
particle and Gaussian quadratic coefficient fields. -/
theorem fp81s21_physical31_both_time (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
    ∀ Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4),
    ∀ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
    ∀ εN εG εB : ℕ → ℝ, ∀ S : fp81s21_Physical31 p R Es E εN εG εB,
    ∀ m : ℕ, ∃ Λ : ℝ, ∃ θ : Fin m → HRS.MS.R2S11.s11V p.d Λ,
    ∃ D : HRS.MS.R2S11.s11V p.d Λ → ℕ → fp81s21_RankKernel p.d,
    0 ≤ Λ ∧ (∀ j, (θ j).1 = gradient (E.test j)) ∧
    ∃ τN τG : ℕ → ℝ, (∀ k, 0 ≤ τN k) ∧ (∀ k, 0 ≤ τG k) ∧
    Tendsto τN atTop (𝓝 0) ∧ Tendsto τG atTop (𝓝 0) ∧
    (∀ H : ℝ, 0 < H → ∀ N : ℕ, ∀ hN : 2 ≤ N, ∀ A : Particle R N,
      ∀ a : ℝ, 0 ≤ a →
      ∀ V : A.Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)),
      fp81s21_TimeL2Rep A.P
        (fun u ω => fp81s21_particle_embedField p Es E (S.qsBN N hN A u ω)) S.MN a H V →
      ∀ k : ℕ, ∃ U, fp81s21_ParticleRankTime31 p R m Λ θ D k N A a H U ∧
        fp81s21_SqErr A.P U (fun ω => fp81s21_timeProject H m (V ω))
          (Real.sqrt (H * (m : ℝ)) * τN k)) ∧
    (∀ H : ℝ, 0 < H → ∀ G : GaussianRealization R, ∀ a : ℝ, 0 ≤ a →
      ∀ V : G.Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)),
      fp81s21_TimeL2Rep G.P (S.gaussian.quadratic.qe G)
        (S.gaussian.quadratic.Kstar ^ 4 * S.gaussian.quadratic.B / 2) a H V →
      ∀ k : ℕ, ∃ U,
        fp81s21_GaussianRankTime31 p R Es E εB S.gaussian.quadratic m Λ θ D k G a H U ∧
        fp81s21_SqErr G.P U (fun ω => fp81s21_timeProject H m (V ω))
          (Real.sqrt (H * (m : ℝ)) * τG k)) := by
  obtain ⟨δ0, hδ0, hhalf, hboth⟩ := fp81s21_quadraticPhysical31_both_time p
  refine ⟨δ0, hδ0, hhalf, ?_⟩
  intro δ hδ hδle R Es E εN εG εB S m
  obtain ⟨Λ, θ, D, hΛ, hθ, τN, τG, hτN, hτG, hτNlim, hτGlim, hn, hg⟩ :=
    hboth δ hδ hδle R Es E εB S.gaussian.quadratic m
  refine ⟨Λ, θ, D, hΛ, hθ, τN, τG, hτN, hτG, hτNlim, hτGlim, ?_, ?_⟩
  · intro H hH N hN A a ha V hV k
    have hrep := (S.particle N hN A).2.2.2.2.2.1
    obtain ⟨Mq, q, hq, hqeq, U, hU, herr⟩ :=
      hn N hN A _ S.MN a H ha hH.le hrep V hV k
    exact ⟨U, ⟨Mq, q, hq, hqeq, hU⟩, herr⟩
  · intro H hH G a ha V hV k
    obtain ⟨Mq, q, hq, hqeq, U, hU, herr⟩ := hg G a H ha hH.le V hV k
    exact ⟨U, ⟨Mq, q, hq, hqeq, hU⟩, herr⟩

#print axioms fp81s21_ParticleRankTime31
#print axioms fp81s21_GaussianRankTime31
#print axioms fp81s21_physical31_both_time
end HRS.Fp81.S21
end
