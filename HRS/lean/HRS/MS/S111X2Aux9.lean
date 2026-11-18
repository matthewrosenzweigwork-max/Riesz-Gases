import HRS.MS.S111X2Aux8

/-!
# S11.1 X2, packet E02 (part 4): the response of the generator, `R_β P G h = -β⁻¹ L h`

`s111x2_response_generator_core`: for the thermal data `TD`, `h ∈ C²` (bounded `Dh, D²h`) and `f ∈ C¹` bounded with
bounded derivative: `L h ∈ L²_0(μ)`, `G h ∈ L²(μ)`, `HRS.Whole.IsResponse β (G h) (-β⁻¹ L h)`, `⟨∇f,∇h⟩ ∈ L¹(μ)` and
`C_β(f, G h) = -β⁻¹ D(f,h)`.
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

/-- The Dirichlet form `D(f,h) = ∫ ⟨∇f,∇h⟩ dμ`. -/
def s111x2_dirichlet (μ : Measure (Euc d)) (f h : Euc d → ℝ) : ℝ :=
  ∫ x, inner ℝ (gradient f x) (gradient h x) ∂μ

section Core

variable {s β : ℝ} {ρ : Euc d → ℝ} {M : ℝ} {C : WholeCoeff d}

theorem TD.prob (T : TD d s β ρ M C) : HRS.Whole.IsProbDensity ρ := ⟨T.en.K.nonneg, T.en.K.meas, T.one⟩

theorem s111x2_L_eq (T : TD d s β ρ M C) (h : Euc d → ℝ) (x : Euc d) :
    s111x2_L ρ h x = -Laplacian.laplacian h x - β * inner ℝ (C.drift 0 x) (gradient h x) := by
  have hβ := T.en.hβ
  have hρ := T.pos x
  unfold s111x2_L
  rw [T.en.grad 0 x, inner_smul_left]
  simp only [conj_trivial]
  field_simp

theorem s111x2_L_continuous (T : TD d s β ρ M C) {h : Euc d → ℝ} (hh : ContDiff ℝ 2 h) :
    Continuous (s111x2_L ρ h) := by
  unfold s111x2_L
  have hρc : ContDiff ℝ 1 ρ := T.en.smooth.of_le (by norm_num)
  have hpc : Continuous ρ := hρc.continuous
  have hg1 := s111x2_gradient_continuous hρc
  have hg2 := s111x2_gradient_continuous (hh.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2))
  refine (s111x2_laplacian_continuous hh).neg.sub ?_
  refine Continuous.mul (hpc.inv₀ fun x => (T.pos x).ne') ?_
  exact hg1.inner hg2

theorem s111x2_L_bound (T : TD d s β ρ M C) {h : Euc d → ℝ} {B1 B2 : ℝ} (H : CbD h B1 B2) :
    ∃ A0 A1 : ℝ, 0 ≤ A0 ∧ 0 ≤ A1 ∧ ∀ x, |s111x2_L ρ h x| ≤ A0 + A1 * ‖x‖ := by
  obtain ⟨c0, hc0⟩ := T.en.dgrow
  have hβ := T.en.hβ
  have hc00 : 0 ≤ c0 := by
    have h1 := hc0 0 0
    have h2 := norm_nonneg (C.drift 0 0)
    simp at h1
    linarith
  have hB1 := H.B1_nonneg
  have hB2 := H.B2_nonneg
  refine ⟨d * B2 + β * (c0 * B1), β * (c0 * B1), by positivity, by positivity, fun x => ?_⟩
  rw [s111x2_L_eq T h x]
  have h1 := s111x2_laplacian_bound H x
  have h2 : |inner ℝ (C.drift 0 x) (gradient h x)| ≤ c0 * (1 + ‖x‖) * B1 := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    have hg : ‖gradient h x‖ ≤ B1 := by rw [s111x2_norm_gradient]; exact H.d1 x
    exact mul_le_mul (hc0 0 x) hg (norm_nonneg _) (mul_nonneg hc00 (by positivity))
  calc |-Laplacian.laplacian h x - β * inner ℝ (C.drift 0 x) (gradient h x)|
      ≤ |Laplacian.laplacian h x| + β * |inner ℝ (C.drift 0 x) (gradient h x)| := by
        refine (abs_sub _ _).trans ?_
        rw [abs_neg, abs_mul, abs_of_pos hβ]
    _ ≤ d * B2 + β * (c0 * (1 + ‖x‖) * B1) := add_le_add h1 (mul_le_mul_of_nonneg_left h2 hβ.le)
    _ = _ := by ring

theorem s111x2_L_memLp (T : TD d s β ρ M C) {h : Euc d → ℝ} {B1 B2 : ℝ} (H : CbD h B1 B2) :
    MemLp (s111x2_L ρ h) 2 (HRS.Whole.withDensityReal ρ) := by
  haveI := isProbabilityMeasure_nu T.prob
  obtain ⟨A0, A1, hA0, hA1, hb⟩ := s111x2_L_bound T H
  have hm : Measurable (s111x2_L ρ h) := (s111x2_L_continuous T H.smooth).measurable
  refine (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 ?_
  rw [tc2_integrable_nu T.prob]
  have hint : Integrable (fun x => 2 * A0 ^ 2 * ρ x + 2 * A1 ^ 2 * (‖x‖ ^ 2 * ρ x)) :=
    (T.en.K.int.const_mul _).add (T.mom2.const_mul _)
  refine hint.mono' ((T.en.K.meas.mul (hm.pow_const 2)).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  have hρ0 := T.en.K.nonneg x
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hρ0 (sq_nonneg _))]
  have h1 : (s111x2_L ρ h x) ^ 2 ≤ 2 * A0 ^ 2 + 2 * A1 ^ 2 * ‖x‖ ^ 2 := by
    have := hb x
    have h2 : (s111x2_L ρ h x) ^ 2 = |s111x2_L ρ h x| ^ 2 := (sq_abs _).symm
    rw [h2]
    have h3 : |s111x2_L ρ h x| ^ 2 ≤ (A0 + A1 * ‖x‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
    nlinarith [sq_nonneg (A0 - A1 * ‖x‖)]
  calc ρ x * s111x2_L ρ h x ^ 2 ≤ ρ x * (2 * A0 ^ 2 + 2 * A1 ^ 2 * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h1 hρ0
    _ = _ := by ring

/-- `ρ L h = -(ρ Δh + ⟨∇ρ,∇h⟩)`. -/
theorem s111x2_rhoL (T : TD d s β ρ M C) (h : Euc d → ℝ) (x : Euc d) :
    ρ x * s111x2_L ρ h x = -(ρ x * Laplacian.laplacian h x + inner ℝ (gradient ρ x) (gradient h x)) := by
  have hρ := T.pos x
  unfold s111x2_L
  field_simp
  ring

/-- Integrability of the weighted quantity `ρ (ρΔh + ⟨∇ρ,∇h⟩)`-type integrand `ρ Δh + ⟨∇ρ,∇h⟩`. -/
theorem s111x2_divform_integrable (T : TD d s β ρ M C) {h : Euc d → ℝ} {B1 B2 : ℝ} (H : CbD h B1 B2) :
    Integrable (fun x => ρ x * Laplacian.laplacian h x + inner ℝ (gradient ρ x) (gradient h x)) := by
  haveI := isProbabilityMeasure_nu T.prob
  have h1 : Integrable (fun x => ρ x * s111x2_L ρ h x) :=
    (tc2_integrable_nu T.prob _).1 ((s111x2_L_memLp T H).integrable (by norm_num))
  have := h1.neg
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.neg_apply]
  rw [s111x2_rhoL T h x, neg_neg]

theorem s111x2_L_mean_zero (T : TD d s β ρ M C) {h : Euc d → ℝ} {B1 B2 : ℝ} (H : CbD h B1 B2) :
    ∫ x, s111x2_L ρ h x ∂(HRS.Whole.withDensityReal ρ) = 0 := by
  haveI := isProbabilityMeasure_nu T.prob
  rw [tc2_integral_nu T.prob]
  have hK := s111x2_ibp_bilinear (u := fun _ => (1 : ℝ)) T.en.smooth T.en.K.int (s111x2_grad_integrable T.en)
    contDiff_const H.smooth (B0 := 1) (B1 := 0) (C1 := B1) (C2 := B2) (fun x => by simp)
    (fun x => by simp) H.d1 H.d2
  simp only [one_mul, gradient_fun_const, inner_zero_left, mul_zero, integral_zero, neg_zero] at hK
  have : ∀ x, ρ x * s111x2_L ρ h x = -(ρ x * Laplacian.laplacian h x + inner ℝ (gradient ρ x) (gradient h x)) :=
    s111x2_rhoL T h
  simp_rw [this, integral_neg, hK]
  simp

theorem s111x2_L_memL2Zero (T : TD d s β ρ M C) {h : Euc d → ℝ} {B1 B2 : ℝ} (H : CbD h B1 B2) :
    MemL2Zero (HRS.Whole.withDensityReal ρ) (s111x2_L ρ h) :=
  ⟨s111x2_L_memLp T H, s111x2_L_mean_zero T H⟩

end Core

end HRS.MS.S111X2
