import HRS.MS.S82UB3

/-!
# S8.2 A01 (S82U): `∫ ρ J ψ = - ∫ ρ <ψ, F_μ>` (abstract)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82U
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2 HRS.MS.S82T HRS.MH.PairingRd

lemma u_force_bdd {d : ℕ} (hd : 2 ≤ d) {rho : Euc d → ℝ} {Λ : ℝ} (hF : UForce d rho Λ) :
    ∃ K1 : ℝ, ∀ x, ‖forceMean rho x‖ ≤ K1 := by
  obtain ⟨hint, K1, hK1⟩ := u_conv_unif hd hF
  refine ⟨K1, fun x => ?_⟩
  exact (norm_integral_le_integral_norm _).trans (hK1 x)

theorem u_jmean {d : ℕ} (hd : 2 ≤ d) {rho : Euc d → ℝ} {Λ : ℝ} (hF : UForce d rho Λ)
    {ψ : Euc d → Euc d} (hψm : Measurable ψ) (hψ1 : Integrable (fun z => rho z * ‖ψ z‖))
    (hD : Integrable (fun p : Euc d × Euc d =>
      rho p.1 * rho p.2 * (‖rieszKernelGrad d (criticalS d) (p.1 - p.2)‖ * ‖ψ p.2 - ψ p.1‖))
      ((volume : Measure (Euc d)).prod volume)) :
    ∫ x, rho x * ∑ j : Fin d,
        (convGradConvW (rieszKernelGrad d (criticalS d)) (fun w => rho w * ψ w j) x) j =
      -∫ x, rho x * inner ℝ (ψ x) (forceMean rho x) := by
  set Gf := rieszKernelGrad d (criticalS d) with hGf
  have hρm := hF.prob.measurable
  have hρ0 := hF.prob.nonneg
  have hG : Measurable Gf := HRS.Whole.movtr_rieszKernelGrad_measurable (d := d) (criticalS d)
  have hsub : Measurable (fun p : Euc d × Euc d => p.1 - p.2) := measurable_fst.sub measurable_snd
  obtain ⟨K1, hK1⟩ := u_force_bdd hd hF
  have hFm : Measurable (forceMean rho) := s82t_forceMean_measurable hρm
  set e : Euc d × Euc d → ℝ := fun p => rho p.1 * rho p.2 *
    inner ℝ (Gf (p.1 - p.2)) (ψ p.2 - ψ p.1) with he
  have hem : Measurable e :=
    ((hρm.comp measurable_fst).mul (hρm.comp measurable_snd)).mul
      (Measurable.inner (hG.comp hsub) ((hψm.comp measurable_snd).sub (hψm.comp measurable_fst)))
  have heint : Integrable e ((volume : Measure (Euc d)).prod volume) := by
    refine Integrable.mono' hD hem.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, he]
    simp only
    rw [abs_mul, abs_of_nonneg (mul_nonneg (hρ0 _) (hρ0 _))]
    exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (mul_nonneg (hρ0 _) (hρ0 _))
  have hdsym := u_dsym hd hF hψm hψ1 hD
  rw [← he] at hdsym
  -- Ẽ
  set Et : Euc d → ℝ := fun x => ∫ z, rho z * inner ℝ (Gf (x - z)) (ψ z - ψ x) with hEt
  have hrE : ∀ x, rho x * Et x = ∫ z, e (x, z) := by
    intro x
    simp only [hEt, he]
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only; ring
  have hint1 : Integrable (fun x => rho x * Et x) := by
    have := heint.integral_prod_left
    refine this.congr (Eventually.of_forall fun x => ?_)
    exact (hrE x).symm
  have hint2 : Integrable (fun x => rho x * inner ℝ (ψ x) (forceMean rho x)) := by
    refine Integrable.mono' (hψ1.const_mul K1)
      (hρm.mul (Measurable.inner hψm hFm)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 _)]
    calc rho x * |inner ℝ (ψ x) (forceMean rho x)| ≤ rho x * (‖ψ x‖ * K1) :=
          mul_le_mul_of_nonneg_left ((abs_real_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_left (hK1 x) (norm_nonneg _))) (hρ0 _)
      _ = K1 * (rho x * ‖ψ x‖) := by ring
  -- a.e. identity
  have hae : ∀ᵐ x ∂(volume : Measure (Euc d)),
      rho x * ∑ j : Fin d, (convGradConvW Gf (fun w => rho w * ψ w j) x) j =
        rho x * Et x + rho x * inner ℝ (ψ x) (forceMean rho x) := by
    filter_upwards [hD.prod_right_ae] with x hx
    by_cases h0 : rho x = 0
    · simp [h0]
    · have hpos : 0 < rho x := lt_of_le_of_ne (hρ0 x) (Ne.symm h0)
      have hx' : Integrable (fun z => rho z * (‖Gf (x - z)‖ * ‖ψ z - ψ x‖)) := by
        have := hx.const_mul (rho x)⁻¹
        refine this.congr (Eventually.of_forall fun z => ?_)
        simp only
        field_simp
      rw [u_JE hd hF hψm hx']
      simp only [hEt]
      ring
  rw [integral_congr_ae hae, integral_add hint1 hint2]
  have h3 : ∫ x, rho x * Et x = ∫ p, e p ∂((volume : Measure (Euc d)).prod volume) := by
    rw [integral_prod _ heint]
    exact integral_congr_ae (Eventually.of_forall hrE)
  rw [h3, hdsym]
  ring

end HRS.MS.S82U
