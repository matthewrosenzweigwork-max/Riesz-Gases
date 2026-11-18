import HRS.MS.Fp81S21TimeRep14
import HRS.MS.Fp81S21WeightedMomentsB
import HRS.MS.Fp81S21RankKernel
import HRS.MS.R2S11Aux10

/-! Joint particle rank-kernel modifications without a window-supremum dependency. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory
open scoped NNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3

private theorem fp81s21_centered_pairEnergy_joint2
    {d N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (X : ℝ × Ω → EucConfig d N) (hX : Measurable X)
    (ρ : ℝ → Euc d → ℝ) (hρ : Measurable (fun z : ℝ × Euc d => ρ z.1 z.2))
    (hρ0 : ∀ u x, 0 ≤ ρ u x) (k : Euc d → Euc d → ℝ)
    (hk : Measurable (fun z : ℝ × Euc d × Euc d => k z.2.1 z.2.2)) :
    Measurable (fun z : ℝ × Ω => (N : ℝ) *
      (pairEnergy k (X z) (HRS.Whole.withDensityReal (ρ z.1)) -
        ∫ ω', pairEnergy k (X (z.1, ω')) (HRS.Whole.withDensityReal (ρ z.1)) ∂P)) := by
  let g : ℝ × Ω → ℝ := fun z => pairEnergy k (X z) (HRS.Whole.withDensityReal (ρ z.1))
  have hgm : Measurable g :=
    fp81s21_moving_pairEnergy_process_joint_meas (d := d) (N := N)
      (ρ := ρ) (k := fun _ => k) hρ hρ0 hk hX
  have hi : Measurable (fun u => ∫ ω, g (u, ω) ∂P) :=
    hgm.stronglyMeasurable.integral_prod_right'.measurable
  exact measurable_const.mul (hgm.sub (hi.comp measurable_fst))

/-- The centered particle rank-kernel statistic has a jointly measurable
modification equal to the physical statistic at every nonnegative time. -/
theorem fp81s21_particle_rankKernel_joint2 (p : Parameters) :
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
  have hρ : Measurable (fun z : ℝ × Euc p.d => ρ z.1 z.2) :=
    (fp81s21_particle_density_clip_continuous p R hδ (hδle.trans hδhalf)).measurable
  have hρ0 : ∀ u x, 0 ≤ ρ u x := by
    intro u x
    simpa [ρ, Real.coe_toNNReal _ (le_max_right u 0)] using
      (hRound2 (max u 0) (le_max_right _ _)).prob.nonneg x
  have hk : Measurable (fun z : ℝ × Euc p.d × Euc p.d => D.kernel z.2.1 z.2.2) := by
    have h := HRS.MS.R2Mt.s92_finiteRank_meas D.valid
    exact h.comp (measurable_snd.fst.prodMk measurable_snd.snd)
  obtain ⟨X, hX, hXe⟩ := HRS.MS.R2S11.s11_X_joint
    (A.strong (1 : ℝ)).adapted (A.strong (1 : ℝ)).cont
  let g : ℝ × A.Ω → ℝ := fun z =>
    pairEnergy D.kernel (X z) (HRS.Whole.withDensityReal (ρ z.1))
  let F : ℝ × A.Ω → ℝ := fun z => (N : ℝ) * (g z - ∫ ω', g (z.1, ω') ∂A.P)
  have hF : Measurable F := fp81s21_centered_pairEnergy_joint2 A.P X hX ρ hρ hρ0 D.kernel hk
  refine ⟨F, hF, ?_⟩
  filter_upwards [hXe] with ω hω u hu
  have hρeq : ρ u = R.ρ u := by
    simp [ρ, max_eq_left hu, Real.coe_toNNReal _ hu]
  have hg : ∀ᵐ ω' ∂A.P, g (u, ω') =
      pairEnergy D.kernel (A.X u.toNNReal ω') (r26t3_mu R u) := by
    filter_upwards [hXe] with ω' hω'
    simp [g, hω' u, hρeq, r26t3_mu]
  have hgω : g (u, ω) = pairEnergy D.kernel (A.X u.toNNReal ω) (r26t3_mu R u) := by
    simp [g, hω u, hρeq, r26t3_mu]
  dsimp [F]
  rw [hgω, integral_congr_ae hg]
  simp only [fp81s21_particleQuad, fp81s21_center, integral_const_mul]
  ring

#print axioms fp81s21_particle_rankKernel_joint2
end HRS.Fp81.S21
end
