import HRS.MS.Fp81S21TimeRep14
import HRS.MS.Fp81S21WindowSup27
import HRS.MS.Fp81S21RankKernel

/-! Jointly measurable physical particle rank-kernel outputs. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory
open scoped NNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3

/-- Each finite-rank particle statistic has a jointly measurable modification,
with a single event valid at every nonnegative time. -/
theorem fp81s21_particle_rankKernel_joint (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
      ∀ N : ℕ, ∀ A : Particle R N, ∀ D : fp81s21_RankKernel p.d,
      ∃ F : ℝ × A.Ω → ℝ, Measurable F ∧
        ∀ᵐ ω ∂A.P, ∀ u : ℝ, 0 ≤ u →
          F (u, ω) = fp81s21_particleQuad A u D.kernel ω := by
  obtain ⟨δ₀, hδ₀, hδhalf, hUniform⟩ := fp81s21_uniform_density_moments p
  refine ⟨δ₀, hδ₀, hδhalf, ?_⟩
  intro δ hδ hδle R N A D
  obtain ⟨pinf, K, C₀, c₀, M, L, Mρ, Cm, hpinf, hc₀,
    hGaussian, hRound2, hMoment, hParticle⟩ := hUniform δ hδ hδle R
  let ρ : ℝ → Euc p.d → ℝ := fun u x => R.ρ ((max u 0).toNNReal) x
  have hρ : Measurable (fun z : ℝ × Euc p.d => ρ z.1 z.2) := by
    exact (fp81s21_particle_density_clip_continuous p R hδ (hδle.trans hδhalf)).measurable
  have hρ0 : ∀ u x, 0 ≤ ρ u x := by
    intro u x
    simpa [ρ, Real.coe_toNNReal _ (le_max_right u 0)] using
      (hRound2 (max u 0) (le_max_right _ _)).prob.nonneg x
  have hk : Measurable (fun z : ℝ × Euc p.d × Euc p.d => D.kernel z.2.1 z.2.2) := by
    have h := HRS.MS.R2Mt.s92_finiteRank_meas D.valid
    exact h.comp (measurable_snd.fst.prodMk measurable_snd.snd)
  obtain ⟨F, hF, hFe⟩ := fp81s21_param_centered_pairEnergy_particle_modification
    A.P A.X (A.strong (1 : ℝ)).adapted (A.strong (1 : ℝ)).cont
    id measurable_id ρ (fun _ => D.kernel) hρ hρ0 hk
  refine ⟨F, hF, ?_⟩
  filter_upwards [hFe] with ω hω u hu
  have he := hω u
  have hρeq : ρ u = R.ρ u := by
    simp [ρ, max_eq_left hu, Real.coe_toNNReal _ hu]
  rw [hρeq] at he
  change F (u, ω) = (N : ℝ) *
    (pairEnergy D.kernel (A.X u.toNNReal ω) (r26t3_mu R u) -
      ∫ ω', pairEnergy D.kernel (A.X u.toNNReal ω') (r26t3_mu R u) ∂A.P) at he
  rw [he]
  simp only [fp81s21_particleQuad, fp81s21_center, integral_const_mul]
  ring

#print axioms fp81s21_particle_rankKernel_joint
end HRS.Fp81.S21
end
