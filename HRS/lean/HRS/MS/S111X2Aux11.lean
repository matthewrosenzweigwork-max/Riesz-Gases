import HRS.MS.S111X2Aux10
import HRS.MS.S111X1F1
import HRS.MS.TransOpAux23

/-!
# S11.1 X2, packet E02 (part 6): the Dirichlet identity `C_β(f, G h) = -β⁻¹ D(f,h)` and the thermal instance of `TD`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X2

open HRS HRS.Whole
open HRS.MS.S111X1 (EnData KData Nnl)
open HRS.Whole.Q34 (isProbabilityMeasure_nu)
open HRS.MS.TcR (tc2_integrable_nu tc2_integral_nu)

variable {d : ℕ}

section Core

variable {s β : ℝ} {ρ : Euc d → ℝ} {M : ℝ} {C : WholeCoeff d}

theorem s111x2_responseInverse_gen (T : TD d s β ρ M C) {h : Euc d → ℝ} {B1 B2 : ℝ} (H : CbD h B1 B2) :
    HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β (generatorW C 0 h)
      =ᵐ[HRS.Whole.withDensityReal ρ] fun x => -β⁻¹ * s111x2_L ρ h x := by
  have hex : ∃ u, HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β
      (generatorW C 0 h) u := ⟨_, s111x2_isResponse_gen T H⟩
  have hr : HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β
      (generatorW C 0 h) (HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s)
        (HRS.Whole.withDensityReal ρ) β (generatorW C 0 h)) := by
    unfold HRS.Whole.responseInverse
    rw [dif_pos hex]
    exact hex.choose_spec
  exact T.uniq _ _ _ hr (s111x2_isResponse_gen T H)

theorem s111x2_dirichlet_integrable (T : TD d s β ρ M C) {h : Euc d → ℝ} {B1 B2 : ℝ} (H : CbD h B1 B2)
    {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) {Bf : ℝ} (h1 : ∀ x, ‖fderiv ℝ f x‖ ≤ Bf) :
    Integrable (fun x => inner ℝ (gradient f x) (gradient h x)) (HRS.Whole.withDensityReal ρ) := by
  haveI := isProbabilityMeasure_nu T.prob
  have hcf := s111x2_gradient_continuous hf
  have hch := s111x2_gradient_continuous (H.smooth.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2))
  refine (integrable_const (Bf * B1)).mono' (hcf.inner hch).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  have hg1 : ‖gradient f x‖ ≤ Bf := by rw [s111x2_norm_gradient]; exact h1 x
  have hg2 : ‖gradient h x‖ ≤ B1 := by rw [s111x2_norm_gradient]; exact H.d1 x
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul hg1 hg2 (norm_nonneg _) ((norm_nonneg _).trans hg1))

/-- **E02, Dirichlet identity.** -/
theorem s111x2_susc_gen (T : TD d s β ρ M C) {h : Euc d → ℝ} {B1 B2 : ℝ} (H : CbD h B1 B2)
    {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) {B0 Bf : ℝ} (h0 : ∀ x, ‖f x‖ ≤ B0)
    (h1 : ∀ x, ‖fderiv ℝ f x‖ ≤ Bf) :
    HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β f
        (generatorW C 0 h) = -β⁻¹ * s111x2_dirichlet (HRS.Whole.withDensityReal ρ) f h := by
  haveI := isProbabilityMeasure_nu T.prob
  have hβ := T.en.hβ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hLm := s111x2_L_memLp T H
  have hLi : Integrable (s111x2_L ρ h) μ := hLm.integrable (by norm_num)
  have hfm : Measurable f := hf.continuous.measurable
  have hfL : Integrable (fun x => f x * s111x2_L ρ h x) μ := by
    exact hLi.bdd_mul hfm.aestronglyMeasurable (Filter.Eventually.of_forall h0)
  -- the bilinear integration by parts
  have hibp := s111x2_ibp_bilinear (u := f) T.en.smooth T.en.K.int (s111x2_grad_integrable T.en) hf H.smooth
    h0 h1 H.d1 H.d2
  have hfLint : ∫ x, f x * s111x2_L ρ h x ∂μ =
      ∫ x, ρ x * inner ℝ (gradient f x) (gradient h x) := by
    rw [tc2_integral_nu T.prob]
    have : ∀ x, ρ x * (f x * s111x2_L ρ h x) =
        -(f x * (ρ x * Laplacian.laplacian h x + inner ℝ (gradient ρ x) (gradient h x))) := by
      intro x; have := s111x2_rhoL T h x; rw [mul_left_comm, this]; ring
    simp_rw [this, integral_neg, hibp, neg_neg]
  unfold HRS.Whole.susceptibilityCov HRS.Whole.l2Inner
  have hae := s111x2_responseInverse_gen T H
  have : ∫ x, HRS.Whole.projMean μ f x *
      HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) μ β (generatorW C 0 h) x ∂μ =
      ∫ x, (f x - HRS.Whole.pair μ f) * (-β⁻¹ * s111x2_L ρ h x) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]; rfl
  rw [this]
  have e : ∀ x, (f x - HRS.Whole.pair μ f) * (-β⁻¹ * s111x2_L ρ h x) =
      (-β⁻¹) * (f x * s111x2_L ρ h x) + (β⁻¹ * HRS.Whole.pair μ f) * s111x2_L ρ h x := fun x => by ring
  simp_rw [e]
  rw [integral_add (hfL.const_mul _) (hLi.const_mul _), integral_const_mul, integral_const_mul,
    s111x2_L_mean_zero T H, hfLint]
  unfold s111x2_dirichlet
  rw [tc2_integral_nu T.prob]
  ring

end Core

section Thermal

/-- The thermal reference carries the data `TD`. -/
theorem s111x2_td_of_thermal (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) :
    ∃ M : ℝ, TD d s β ρ M ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) := by
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
  obtain ⟨M, hEn, hone⟩ := HRS.MS.S111X1.enData_of_thermal hd hs0 hs ha hβ hρ
  obtain ⟨B, -, hGap, -⟩ := HRS.MS.Mov0.mv0_gapref hd hs0 hsd ha hβ hρ
  obtain ⟨-, hg⟩ := HRS.MS.Mov0.mv0_hgauss hd hs0 hsd ha hβ hρ
  obtain ⟨C0, c, hC0, hc, h0, h1⟩ := movtr_gauss01 hg
  refine ⟨M, ⟨hEn, hGap.pos, ⟨C0, c, hC0, hc, h0, h1⟩, hGap.moment2, hone, ?_⟩⟩
  exact HRS.MS.TransOp.s611_hsus_of_thermal hd hs0 hsd ha hβ hρ hβ.le

end Thermal

end HRS.MS.S111X2
