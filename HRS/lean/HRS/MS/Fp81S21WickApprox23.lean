import HRS.MS.Fp81S21WickApprox22
import HRS.MS.Fp81S21EmbedField12
import HRS.MS.Fp81S21TimeRep9

/-! Particle finite-rank random time sections. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

private theorem fp81s21_second_of_sixth
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf : Measurable f) (M : ℝ) (hM : 0 ≤ M)
    (h6 : SixthBound P f M) :
    MemLp f 2 P ∧ (∫ ω, ‖f ω‖ ^ 2 ∂P) ≤ 1 + M := by
  have hpoint : ∀ ω, ‖f ω‖ ^ 2 ≤ 1 + ‖f ω‖ ^ 6 := by
    intro ω
    by_cases h : ‖f ω‖ ≤ 1
    · have hs : ‖f ω‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (f ω)]
      nlinarith [sq_nonneg (‖f ω‖ ^ 3)]
    · have h1 : 1 ≤ ‖f ω‖ := le_of_not_ge h
      have h4 : 1 ≤ ‖f ω‖ ^ 4 := one_le_pow₀ h1
      have hmul := mul_le_mul_of_nonneg_left h4 (sq_nonneg ‖f ω‖)
      nlinarith [show ‖f ω‖ ^ 2 * ‖f ω‖ ^ 4 = ‖f ω‖ ^ 6 by ring]
  have hmajor : Integrable (fun ω => 1 + ‖f ω‖ ^ 6) P :=
    (integrable_const 1).add h6.1
  have hsq : Integrable (fun ω => ‖f ω‖ ^ 2) P := by
    apply Integrable.mono' hmajor ((hf.norm.pow_const 2).aestronglyMeasurable)
    filter_upwards [] with ω
    simpa [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖f ω‖ ^ 2)] using hpoint ω
  refine ⟨(memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).2 hsq, ?_⟩
  calc
    _ ≤ ∫ ω, (1 + ‖f ω‖ ^ 6) ∂P := integral_mono hsq hmajor hpoint
    _ = 1 + ∫ ω, ‖f ω‖ ^ 6 ∂P := by rw [integral_add (integrable_const 1) h6.1]; simp
    _ ≤ 1 + M := by linarith [h6.2]

/-- A single finite-rank particle statistic has a measurable coefficient-valued
version and genuine random time-L² sections, uniformly over shifts and horizons. -/
theorem fp81s21_particle_rankKernel_time_field2 (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
      ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N, ∀ D : fp81s21_RankKernel p.d,
      ∀ j : ℕ, ∃ M : ℝ, ∃ q : ℝ → A.Ω → r26t6_Coeff,
        Measurable (Function.uncurry q) ∧
        (∀ᵐ ω ∂A.P, ∀ u : ℝ, 0 ≤ u →
          q u ω = fp81s21_particleQuad A u D.kernel ω • fp81s21_coeffBasis j) ∧
        (∀ u, 0 ≤ u → MemLp (q u) 2 A.P ∧
          (∫ ω, ‖q u ω‖ ^ 2 ∂A.P) ≤ M) ∧
        ∀ a : ℝ, 0 ≤ a → ∀ H : ℝ, 0 ≤ H →
          ∃ U : A.Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)),
            fp81s21_TimeL2Rep A.P q M a H U := by
  obtain ⟨δa, hδa, hδah, ha⟩ := fp81s21_particle_rankKernel_joint2 p
  obtain ⟨δb, hδb, hδbh, hb⟩ := fp81s21_particle_sixth_slices p
  refine ⟨min δa δb, lt_min hδa hδb, (min_le_left _ _).trans hδah, ?_⟩
  intro δ hδ hδle R N hN A D j
  obtain ⟨F, hF, hFe⟩ := ha δ hδ (hδle.trans (min_le_left _ _)) R N A D
  obtain ⟨C, hC, hSix⟩ := hb δ hδ (hδle.trans (min_le_right _ _)) R
  have hdata : ∀ i, IsR2Test (D.u i) := fun i => ⟨D.valid.smooth i, D.valid.compactSupport i⟩
  obtain ⟨B₀, hB₀⟩ := HRS.MS.R2Chaos.s94_finiteRank_bounded (c := D.c) hdata
  let B : ℝ := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hkernel : IsBoundedPairKernel p.s B D.kernel := by
    refine ⟨HRS.MS.R2Mt.s92_finiteRank_meas D.valid,
      HRS.MS.R2Mt.s92_finiteRank_symm D.valid, ?_⟩
    intro x y hxy
    have hw := HRS.MS.R2S11.s11_rieszWeight_nonneg (d := p.d) p.s (x - y)
    have hk : |D.kernel x y| ≤ B := (hB₀ x y).trans (le_max_left _ _)
    nlinarith
  let M : ℝ := 1 + C * B ^ 6
  let q : ℝ → A.Ω → r26t6_Coeff := fun u ω => F (u, ω) • fp81s21_coeffBasis j
  have hqm : Measurable (Function.uncurry q) := hF.smul measurable_const
  have hsec : ∀ u, 0 ≤ u → MemLp (q u) 2 A.P ∧
      (∫ ω, ‖q u ω‖ ^ 2 ∂A.P) ≤ M := by
    intro u hu
    have hFu : Measurable (fun ω => F (u, ω)) := hF.comp (measurable_prodMk_left (x := u))
    have he : (fun ω => F (u, ω)) =ᵐ[A.P] fp81s21_particleQuad A u D.kernel :=
      hFe.mono (fun ω hω => hω u hu)
    have hsix0 := ((hSix N hN A u hu B hB).1 D.kernel hkernel).2
    have hEq : (fun ω => (N : ℝ) *
        (pairEnergy D.kernel (A.X u.toNNReal ω) (r26t3_mu R u) -
        ∫ ω', pairEnergy D.kernel (A.X u.toNNReal ω') (r26t3_mu R u) ∂A.P)) =
        fp81s21_particleQuad A u D.kernel := by
      funext ω
      simp only [fp81s21_particleQuad, fp81s21_center, integral_const_mul]
      ring
    rw [hEq] at hsix0
    have hsix : SixthBound A.P (fun ω => F (u, ω)) (C * B ^ 6) := by
      have he6 : (fun ω => ‖F (u, ω)‖ ^ 6) =ᵐ[A.P]
          (fun ω => ‖fp81s21_particleQuad A u D.kernel ω‖ ^ 6) := he.mono (fun ω hω => by simpa only using congrArg (fun x : ℝ => ‖x‖ ^ 6) hω)
      exact ⟨hsix0.1.congr he6.symm, by rw [integral_congr_ae he6]; exact hsix0.2⟩
    obtain ⟨hmem, hbound⟩ := fp81s21_second_of_sixth A.P _ hFu _
      (mul_nonneg hC (pow_nonneg hB 6)) hsix
    have hnorm : ∀ ω, ‖q u ω‖ = ‖F (u, ω)‖ := by
      intro ω
      simp [q, norm_smul, fp81s21_coeffBasis.orthonormal.norm_eq_one]
    have hqi : Integrable (fun ω => ‖q u ω‖ ^ 2) A.P := by
      simpa only [hnorm] using hmem.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    refine ⟨(memLp_two_iff_integrable_sq_norm
      ((hqm.comp (measurable_prodMk_left (x := u))).aestronglyMeasurable)).2 hqi, ?_⟩
    simpa only [hnorm, M] using hbound
  refine ⟨M, q, hqm, ?_, hsec, ?_⟩
  · filter_upwards [hFe] with ω hω u hu
    simp [q, hω u hu]
  · intro a ha H hH
    let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
    let g : ℝ × A.Ω → r26t6_Coeff := fun z => q (a + z.1) z.2
    have hgm : Measurable g := hqm.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
    have hsecp : ∀ᵐ t ∂dt, MemLp (fun ω => g (t, ω)) 2 A.P ∧
        (∫ ω, ‖g (t, ω)‖ ^ 2 ∂A.P) ≤ M := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hsec (a + t) (add_nonneg ha ht.1)
    obtain ⟨hg, hbnd⟩ := fp81s21_memLp_prod_of_section_bound dt A.P g hgm M hsecp
    have hi : Integrable (fun z => ‖g z‖ ^ 2) (dt.prod A.P) :=
      (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg
    have hs : ∀ᵐ ω ∂A.P, MemLp (fun t => g (t, ω)) 2 dt := by
      filter_upwards [hi.prod_left_ae] with ω hω
      exact (memLp_two_iff_integrable_sq_norm
        (hgm.comp (measurable_prodMk_right (y := ω))).aestronglyMeasurable).2 hω
    obtain ⟨U, hUm, hUL, hUeq, hUin⟩ := fp81s21_time_section_exists A.P H g hgm hg
    refine ⟨U, hUm, hUL, ?_, ?_⟩
    · rw [hUin]
      simpa [dt, Measure.restrict_apply_univ, Real.volume_Icc,
        ENNReal.toReal_ofReal hH] using hbnd
    · filter_upwards [hs, hUeq] with ω hω heq
      exact ⟨hω, heq⟩

#print axioms fp81s21_particle_rankKernel_time_field2
end HRS.Fp81.S21
end
