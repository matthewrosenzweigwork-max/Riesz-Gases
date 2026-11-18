import HRS.MS.Fp81S21InitialUncentered6

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S45
open HRS.Whole
open HRS (Euc)

/-- Weighted integration by parts with the reference potential as test function. The potential
has at most linear growth because its gradient is bounded; the reference Gaussian bound makes
the coordinatewise integration by parts integrable. -/
theorem fp81s21_initial_ibp_potential
    {d : ℕ} {s q C c BU BB : ℝ} {ρ : Euc d → ℝ} {Bd : Euc d → Euc d}
    (hT : S47.TRef d s ρ q C c BU BB Bd)
    {χ : Euc d → ℝ} (hχ : ContDiff ℝ 2 χ)
    {B1 B2 : ℝ} (hB1 : ∀ x, ‖gradient χ x‖ ≤ B1)
    (hB2 : ∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B2) :
    ∫ y : Euc d, HRS.Whole.convMeasure (rieszKernel d s)
      (HRS.Whole.withDensityReal ρ) y * weightedGen ρ χ y
      ∂(HRS.Whole.withDensityReal ρ) =
    ∫ y : Euc d, ⟪gradient χ y,
      gradient (HRS.Whole.convMeasure (rieszKernel d s)
        (HRS.Whole.withDensityReal ρ)) y⟫
      ∂(HRS.Whole.withDensityReal ρ) := by
  let U : Euc d → ℝ := HRS.Whole.convMeasure (rieszKernel d s)
    (HRS.Whole.withDensityReal ρ)
  let v : Euc d → Euc d := gradient χ
  have hUcd : ContDiff ℝ 1 U := by
    exact hT.Usmooth.of_le (by exact_mod_cast le_top)
  have hUdiff : Differentiable ℝ U := hUcd.differentiable (by norm_num)
  have hρcd : ContDiff ℝ 1 ρ := hT.smooth.of_le (by exact_mod_cast le_top)
  have hvcd : ContDiff ℝ 1 v := s45_contDiff_gradient hχ
  have hBU0 : 0 ≤ BU := hT.BU0
  have hB10 : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0)
  have hB20 : 0 ≤ B2 := (norm_nonneg _).trans (hB2 0)
  have hC0 : 0 ≤ C := hT.C0
  have hc : 0 < c := hT.hc
  let L : ℝ≥0 := ⟨BU, hBU0⟩
  have hLB : (L : ℝ) = BU := rfl
  have hL : LipschitzWith L U :=
    lipschitzWith_of_nnnorm_fderiv_le hUdiff (fun y => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, hLB, ← s45_norm_gradient]
      exact hT.gradU_le y)
  have hUgrowth : ∀ y, |U y| ≤ |U 0| + BU * ‖y‖ := by
    intro y
    have hdist := hL.dist_le_mul y 0
    rw [Real.dist_eq, dist_eq_norm, hLB, sub_zero] at hdist
    have habs : |U y - U 0| ≤ BU * ‖y‖ := by
      simpa [Real.norm_eq_abs] using hdist
    calc
      |U y| = |(U y - U 0) + U 0| := by congr 1; ring
      _ ≤ |U y - U 0| + |U 0| := abs_add_le _ _
      _ ≤ BU * ‖y‖ + |U 0| := by
        simpa [add_comm] using add_le_add_left habs (|U 0|)
      _ = |U 0| + BU * ‖y‖ := by ring
  have hUderiv : ∀ y, ‖fderiv ℝ U y‖ ≤ BU := by
    intro y
    rw [← s45_norm_gradient]
    exact hT.gradU_le y
  have hpoly : ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ r : ℝ, 0 ≤ r →
      1 + r ≤ Cp * Real.exp (c / 2 * r ^ 2) := by
    simpa using (s45_poly_le (c := c / 2) (by linarith : 0 < c / 2))
  obtain ⟨Cp, hCp0, hCp⟩ := hpoly
  have hgauss := HRS.MP.SelfSimP4Impl.p4g_integrable_gauss d
    (b := c / 2) (by linarith : 0 < c / 2)
  have hweight : Integrable
      (fun y : Euc d => (1 + ‖y‖) * Real.exp (-c * ‖y‖ ^ 2)) := by
    refine Integrable.mono' (hgauss.const_mul Cp)
      ((continuous_const.add continuous_norm).mul
        (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)]
    calc
      (1 + ‖y‖) * Real.exp (-c * ‖y‖ ^ 2) ≤
          (Cp * Real.exp (c / 2 * ‖y‖ ^ 2)) * Real.exp (-c * ‖y‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (hCp _ (norm_nonneg _)) (Real.exp_pos _).le
      _ = Cp * (Real.exp (c / 2 * ‖y‖ ^ 2) * Real.exp (-c * ‖y‖ ^ 2)) := by ring
      _ = Cp * Real.exp (-(c / 2 * ‖y‖ ^ 2)) := by
        have hexp' : Real.exp (c / 2 * ‖y‖ ^ 2) * Real.exp (-c * ‖y‖ ^ 2) =
            Real.exp (-(c / 2 * ‖y‖ ^ 2)) := by
          rw [← Real.exp_add]
          congr 1
          ring_nf
        rw [hexp']
  have hUrho : ∀ y, |U y * ρ y| ≤
      (C * (|U 0| + BU)) * ((1 + ‖y‖) * Real.exp (-c * ‖y‖ ^ 2)) := by
    intro y
    have h0 := hT.h0 y
    have hg := hUgrowth y
    have hshape : |U y| ≤ (|U 0| + BU) * (1 + ‖y‖) := by
      have hr := norm_nonneg y
      nlinarith [abs_nonneg (U y), abs_nonneg (U 0),
        mul_nonneg hBU0 hr, mul_nonneg (abs_nonneg (U 0)) hr]
    calc
      |U y * ρ y| = |U y| * |ρ y| := abs_mul _ _
      _ ≤ ((|U 0| + BU) * (1 + ‖y‖)) * (C * Real.exp (-c * ‖y‖ ^ 2)) :=
        mul_le_mul (hshape) (h0) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hUrhoDeriv : ∀ y, ‖fderiv ℝ (fun y => U y * ρ y) y‖ ≤
      (C * (|U 0| + 2 * BU)) * ((1 + ‖y‖) * Real.exp (-c * ‖y‖ ^ 2)) := by
    intro y
    have hfd := (hUdiff y).hasFDerivAt.mul (hρcd.differentiable (by norm_num) y).hasFDerivAt
    change ‖fderiv ℝ (U * ρ) y‖ ≤ _
    rw [hfd.fderiv]
    have hU := hUgrowth y
    have hρ0 := hT.h0 y
    have hρ1 := hT.h1 y
    have hshape : |U y| ≤ (|U 0| + BU) * (1 + ‖y‖) := by
      have hr := norm_nonneg y
      nlinarith [abs_nonneg (U y), abs_nonneg (U 0),
        mul_nonneg hBU0 hr, mul_nonneg (abs_nonneg (U 0)) hr]
    have hUρ : |U y| * ‖fderiv ℝ ρ y‖ ≤
        ((|U 0| + BU) * (1 + ‖y‖)) * (C * Real.exp (-c * ‖y‖ ^ 2)) :=
      mul_le_mul hshape hρ1 (norm_nonneg _) (by positivity)
    have hρU : |ρ y| * ‖fderiv ℝ U y‖ ≤
        (C * Real.exp (-c * ‖y‖ ^ 2)) * BU :=
      mul_le_mul hρ0 (hUderiv y) (norm_nonneg _) (by positivity)
    calc
      ‖U y • fderiv ℝ ρ y + ρ y • fderiv ℝ U y‖ ≤
          |U y| * ‖fderiv ℝ ρ y‖ + |ρ y| * ‖fderiv ℝ U y‖ := by
            calc
              _ ≤ ‖U y • fderiv ℝ ρ y‖ + ‖ρ y • fderiv ℝ U y‖ := norm_add_le _ _
              _ = _ := by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ ((|U 0| + BU) * (1 + ‖y‖)) * (C * Real.exp (-c * ‖y‖ ^ 2)) +
          (C * Real.exp (-c * ‖y‖ ^ 2)) * BU := add_le_add hUρ hρU
      _ ≤ (C * (|U 0| + 2 * BU)) *
          ((1 + ‖y‖) * Real.exp (-c * ‖y‖ ^ 2)) := by
            have hR : 0 ≤ 1 + ‖y‖ := by positivity
            have hE : 0 ≤ Real.exp (-c * ‖y‖ ^ 2) := (Real.exp_pos _).le
            have hU0 : 0 ≤ |U 0| := abs_nonneg _
            have h1 : (|U 0| + BU) * (1 + ‖y‖) + BU ≤
                (|U 0| + 2 * BU) * (1 + ‖y‖) := by
              nlinarith [mul_nonneg hBU0 (norm_nonneg y)]
            calc
              ((|U 0| + BU) * (1 + ‖y‖)) * (C * Real.exp (-c * ‖y‖ ^ 2)) +
                  (C * Real.exp (-c * ‖y‖ ^ 2)) * BU =
                C * (((|U 0| + BU) * (1 + ‖y‖) + BU) *
                  Real.exp (-c * ‖y‖ ^ 2)) := by ring
              _ ≤ C * ((|U 0| + 2 * BU) * (1 + ‖y‖) *
                  Real.exp (-c * ‖y‖ ^ 2)) := by
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right h1 hE) hC0
              _ = _ := by ring
  have hUrhoInt : Integrable (fun y => U y * ρ y) := by
    refine Integrable.mono' (hweight.const_mul (C * (|U 0| + BU)))
      (hUcd.continuous.mul hρcd.continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    exact hUrho y
  have hUrhoDerivInt : Integrable (fun y => fderiv ℝ (fun y => U y * ρ y) y) := by
    refine Integrable.mono' (hweight.const_mul (C * (|U 0| + 2 * BU)))
      ((hUcd.mul hρcd).continuous_fderiv one_ne_zero).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => hUrhoDeriv y)
  have hBvCoord : ∀ (b : Fin d) y, |v y b| ≤ B1 := by
    intro b y
    exact (s45_abs_coord_le _ _).trans (hB1 y)
  have hgb : ∀ b : Fin d, ContDiff ℝ 1 (fun y => v y b) := fun b =>
    (EuclideanSpace.proj b : Euc d →L[ℝ] ℝ).contDiff.comp hvcd
  have hgbd : ∀ (b : Fin d) (y : Euc d), HasFDerivAt (fun y => v y b)
      ((EuclideanSpace.proj b : Euc d →L[ℝ] ℝ).comp (fderiv ℝ v y)) y := fun b y =>
    (EuclideanSpace.proj b : Euc d →L[ℝ] ℝ).hasFDerivAt.comp y
      ((hvcd.differentiable (by norm_num)) y).hasFDerivAt
  have hDvCoord : ∀ (b : Fin d) (y : Euc d),
      |fderiv ℝ (fun y => v y b) y (EuclideanSpace.single b 1)| ≤ B2 := by
    intro b y
    rw [(hgbd b y).fderiv]
    simp only [ContinuousLinearMap.comp_apply]
    refine (s45_abs_coord_le _ _).trans ?_
    calc
      ‖fderiv ℝ v y (EuclideanSpace.single b 1)‖ ≤
          ‖fderiv ℝ v y‖ * ‖(EuclideanSpace.single b (1 : ℝ) : Euc d)‖ :=
            ContinuousLinearMap.le_opNorm _ _
      _ ≤ B2 * 1 := mul_le_mul (hB2 y) (by simp) (norm_nonneg _) hB20
      _ = B2 := mul_one _
  have hIntWeightMul {f : Euc d → ℝ} {K : ℝ}
      (hf : AEStronglyMeasurable f volume)
      (hbound : ∀ y, |f y| ≤ K * ((1 + ‖y‖) * Real.exp (-c * ‖y‖ ^ 2))) :
      Integrable f volume := by
    refine Integrable.mono' (hweight.const_mul K) hf
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    exact hbound y
  have key : ∀ b : Fin d,
      Integrable (fun y => U y * ρ y * fderiv ℝ (fun y => v y b) y
        (EuclideanSpace.single b 1)) ∧
      Integrable (fun y => fderiv ℝ (fun y => U y * ρ y) y
        (EuclideanSpace.single b 1) * v y b) ∧
      ∫ y, U y * ρ y * fderiv ℝ (fun y => v y b) y (EuclideanSpace.single b 1) =
        -∫ y, fderiv ℝ (fun y => U y * ρ y) y (EuclideanSpace.single b 1) * v y b := by
    intro b
    have hI1 : Integrable (fun y => U y * ρ y * fderiv ℝ (fun y => v y b) y
        (EuclideanSpace.single b 1)) := by
      refine hIntWeightMul (K := C * (|U 0| + BU) * B2)
        (hf := ((hUcd.continuous.mul hρcd.continuous).mul
          ((hgb b).continuous_fderiv one_ne_zero |>.clm_apply
            (continuous_const : Continuous fun _ : Euc d =>
              (EuclideanSpace.single b (1 : ℝ) : Euc d)))).aestronglyMeasurable)
        (hbound := ?_)
      intro y
      rw [abs_mul]
      calc
        |U y * ρ y| * |fderiv ℝ (fun y => v y b) y (EuclideanSpace.single b 1)| ≤
            (C * (|U 0| + BU)) * ((1 + ‖y‖) * Real.exp (-c * ‖y‖ ^ 2)) * B2 :=
              mul_le_mul (hUrho y) (hDvCoord b y) (abs_nonneg _) (by positivity)
        _ = (C * (|U 0| + BU) * B2) *
            ((1 + ‖y‖) * Real.exp (-c * ‖y‖ ^ 2)) := by ring
        _ = _ := by ring
    have hI2 : Integrable (fun y => fderiv ℝ (fun y => U y * ρ y) y
        (EuclideanSpace.single b 1) * v y b) := by
      have hvbcont : Continuous fun y : Euc d => v y b := by
        exact (EuclideanSpace.proj b : Euc d →L[ℝ] ℝ).continuous.comp hvcd.continuous
      have hfdcont : Continuous fun y : Euc d =>
          fderiv ℝ (fun y => U y * ρ y) y (EuclideanSpace.single b 1) := by
        exact ((hUcd.mul hρcd).continuous_fderiv one_ne_zero).clm_apply
          (continuous_const : Continuous fun _ : Euc d =>
            (EuclideanSpace.single b (1 : ℝ) : Euc d))
      refine hIntWeightMul (K := C * (|U 0| + 2 * BU) * B1)
        (hfdcont.mul hvbcont).aestronglyMeasurable ?_
      intro y
      rw [abs_mul]
      calc
        |fderiv ℝ (fun y => U y * ρ y) y (EuclideanSpace.single b 1)| * |v y b| ≤
            (C * (|U 0| + 2 * BU)) * ((1 + ‖y‖) * Real.exp (-c * ‖y‖ ^ 2)) * B1 :=
              mul_le_mul
                (calc
                  |fderiv ℝ (fun z => U z * ρ z) y (EuclideanSpace.single b 1)| ≤
                      ‖fderiv ℝ (fun z => U z * ρ z) y (EuclideanSpace.single b 1)‖ :=
                        le_of_eq (Real.norm_eq_abs _).symm
                  _ ≤ ‖fderiv ℝ (fun z => U z * ρ z) y‖ *
                      ‖(EuclideanSpace.single b (1 : ℝ) : Euc d)‖ :=
                        ContinuousLinearMap.le_opNorm _ _
                  _ ≤ C * (|U 0| + 2 * BU) *
                      ((1 + ‖y‖) * Real.exp (-c * ‖y‖ ^ 2)) := by
                        simpa using hUrhoDeriv y)
                (hBvCoord b y) (abs_nonneg _) (by positivity)
        _ = (C * (|U 0| + 2 * BU) * B1) *
            ((1 + ‖y‖) * Real.exp (-c * ‖y‖ ^ 2)) := by ring
        _ = _ := by ring
    have hI3 : Integrable (fun y => U y * ρ y * v y b) := by
      refine hIntWeightMul (K := C * (|U 0| + BU) * B1)
        (hf := ((hUcd.continuous.mul hρcd.continuous).mul
          ((EuclideanSpace.proj b : Euc d →L[ℝ] ℝ).continuous.comp hvcd.continuous)).aestronglyMeasurable)
        (hbound := ?_)
      intro y
      rw [abs_mul, abs_mul]
      calc
        |U y| * |ρ y| * |v y b| ≤
            (C * (|U 0| + BU)) * ((1 + ‖y‖) * Real.exp (-c * ‖y‖ ^ 2)) * B1 := by
              rw [← abs_mul]
              exact mul_le_mul (hUrho y) (hBvCoord b y) (abs_nonneg _) (by positivity)
        _ = (C * (|U 0| + BU) * B1) *
            ((1 + ‖y‖) * Real.exp (-c * ‖y‖ ^ 2)) := by ring
        _ = _ := by ring
    have hgbdiff : Differentiable ℝ (fun y => v y b) :=
      (hgb b).differentiable (by norm_num)
    have hUρdiff : Differentiable ℝ (fun y => U y * ρ y) := hUdiff.mul
      (hρcd.differentiable (by norm_num))
    have hfd' : ∀ y, HasFDerivAt (fun y => U y * ρ y)
        (U y • fderiv ℝ ρ y + ρ y • fderiv ℝ U y) y := by
      intro y
      exact (hUdiff y).hasFDerivAt.mul (hρcd.differentiable (by norm_num) y).hasFDerivAt
    have hgb' : ∀ y, HasFDerivAt (fun y => v y b)
        ((EuclideanSpace.proj b : Euc d →L[ℝ] ℝ).comp (fderiv ℝ v y)) y := by
      intro y
      exact (EuclideanSpace.proj b : Euc d →L[ℝ] ℝ).hasFDerivAt.comp y
        ((hvcd.differentiable (by norm_num)) y).hasFDerivAt
    exact ⟨hI1, hI2,
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Euc d)))
        (f := fun y => U y * ρ y) (g := fun y => v y b)
        (v := EuclideanSpace.single b 1) hI2 hI1 hI3
        (fun y _ => hUρdiff y) (fun y _ => hgbdiff y)⟩
  have hsum :
      ∑ b : Fin d, ∫ y, U y * ρ y * fderiv ℝ (fun y => v y b) y
          (EuclideanSpace.single b 1) =
      -∑ b : Fin d, ∫ y, fderiv ℝ (fun y => U y * ρ y) y
          (EuclideanSpace.single b 1) * v y b := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun b _ => (key b).2.2
  have hdivp : ∀ y,
      ∑ b : Fin d, U y * ρ y * fderiv ℝ (fun y => v y b) y
        (EuclideanSpace.single b 1) = U y * ρ y * s45_div v y := by
    intro y
    rw [← Finset.mul_sum]
    congr 1
    unfold s45_div
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [(hgbd b y).fderiv]
    rfl
  have hgrad : ∀ y,
      ∑ b : Fin d, fderiv ℝ (fun y => U y * ρ y) y (EuclideanSpace.single b 1) * v y b =
        U y * ⟪gradient ρ y, v y⟫ + ρ y * ⟪gradient U y, v y⟫ := by
    intro y
    rw [s45_inner_eq_sum, s45_inner_eq_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hfd' : HasFDerivAt (fun y => U y * ρ y)
        (U y • fderiv ℝ ρ y + ρ y • fderiv ℝ U y) y :=
      (hUdiff y).hasFDerivAt.mul (hρcd.differentiable (by norm_num) y).hasFDerivAt
    have hfdEq := hfd'.fderiv
    change fderiv ℝ (U * ρ) y = _ at hfdEq
    change (fderiv ℝ (U * ρ) y) (EuclideanSpace.single b 1) * v y b = _
    rw [hfdEq]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      movtr_gradient_apply]
    ring
  have hdivI : Integrable (fun y => U y * ρ y * s45_div v y) :=
    (integrable_finsetSum _ fun b _ => (key b).1).congr
      (Filter.Eventually.of_forall hdivp)
  have hsum' := hsum
  rw [← integral_finsetSum _ (fun b _ => (key b).1),
    ← integral_finsetSum _ (fun b _ => (key b).2.1), ← integral_neg] at hsum'
  simp_rw [hdivp, hgrad] at hsum'
  have hgen : ∀ y, ρ y * (U y * weightedGen ρ χ y) =
      -(U y * ρ y * s45_div v y) - U y * ⟪gradient ρ y, v y⟫ := by
    intro y
    rw [S47.s47_gen_eq hT, s45_div_gradient hχ y, hT.grad_rho y]
    simp only [real_inner_smul_left, inner_add_left, inner_sub_left]
    ring
  rw [HRS.MS.TcR.tc2_integral_nu hT.prob
      (fun y => U y * weightedGen ρ χ y),
    HRS.MS.TcR.tc2_integral_nu hT.prob
      (fun y => ⟪v y, gradient U y⟫)]
  show ∫ y, ρ y * (U y * weightedGen ρ χ y) =
      ∫ y, ρ y * ⟪v y, gradient U y⟫
  have hgradρcont : Continuous (gradient ρ) := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp
      (hρcd.continuous_fderiv one_ne_zero)
  have hA : Integrable (fun y => U y * ⟪gradient ρ y, v y⟫) := by
    refine hIntWeightMul (K := C * (|U 0| + BU) * B1) ?_ ?_
    · exact (hUcd.continuous.mul
        (hgradρcont.inner hvcd.continuous)).aestronglyMeasurable
    · intro y
      rw [abs_mul]
      have hρ' : ‖gradient ρ y‖ ≤ C * Real.exp (-c * ‖y‖ ^ 2) := by
        rw [s45_norm_gradient]
        exact hT.h1 y
      calc
        |U y| * |⟪gradient ρ y, v y⟫| ≤
            (C * (|U 0| + BU)) * ((1 + ‖y‖) * Real.exp (-c * ‖y‖ ^ 2)) * B1 := by
              have hshape : |U y| ≤ (|U 0| + BU) * (1 + ‖y‖) := by
                have hr := norm_nonneg y
                nlinarith [hUgrowth y, abs_nonneg (U y), abs_nonneg (U 0),
                  mul_nonneg hBU0 hr, mul_nonneg (abs_nonneg (U 0)) hr]
              calc
                |U y| * |⟪gradient ρ y, v y⟫| ≤ |U y| *
                    (‖gradient ρ y‖ * ‖v y‖) :=
                      mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
                _ ≤ ((|U 0| + BU) * (1 + ‖y‖)) *
                    ((C * Real.exp (-c * ‖y‖ ^ 2)) * B1) := by
                      apply mul_le_mul hshape
                      · exact mul_le_mul hρ' (hB1 y)
                          (norm_nonneg (v y)) (by positivity)
                      · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
                      · positivity
                _ = _ := by ring
        _ = (C * (|U 0| + BU) * B1) *
            ((1 + ‖y‖) * Real.exp (-c * ‖y‖ ^ 2)) := by ring
  have hB : Integrable (fun y => ρ y * ⟪gradient U y, v y⟫) := by
    have hgradUcont : Continuous (gradient U) := by
      unfold gradient
      exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp
        (hUcd.continuous_fderiv one_ne_zero)
    refine Integrable.mono' (hgauss.const_mul (C * (BU * B1)))
      (hρcd.continuous.mul (hgradUcont.inner hvcd.continuous)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |ρ y| * |⟪gradient U y, v y⟫| ≤
          (C * Real.exp (-c * ‖y‖ ^ 2)) * (BU * B1) := by
        calc
          |ρ y| * |⟪gradient U y, v y⟫| ≤
              (C * Real.exp (-c * ‖y‖ ^ 2)) *
                (‖gradient U y‖ * ‖v y‖) :=
            mul_le_mul (hT.h0 y) (abs_real_inner_le_norm _ _)
              (abs_nonneg _) (by positivity)
          _ ≤ (C * Real.exp (-c * ‖y‖ ^ 2)) * (BU * B1) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul (hT.gradU_le y) (hB1 y) (norm_nonneg _) hBU0)
              (by positivity)
      _ = (C * (BU * B1)) * Real.exp (-c * ‖y‖ ^ 2) := by ring
      _ ≤ (C * (BU * B1)) * Real.exp (-(c / 2 * ‖y‖ ^ 2)) := by
        apply mul_le_mul_of_nonneg_left
        · apply Real.exp_le_exp.mpr
          nlinarith [sq_nonneg (‖y‖ : ℝ), hT.hc]
        · positivity
      _ = _ := by ring
  have hsumRel :
      (∫ y, U y * ρ y * s45_div v y) +
        (∫ y, U y * ⟪gradient ρ y, v y⟫) +
        (∫ y, ρ y * ⟪gradient U y, v y⟫) = 0 := by
    have hs := hsum'
    rw [integral_neg, integral_add hA hB] at hs
    linarith
  have hfinalScalars :
      -(∫ y, U y * ρ y * s45_div v y) -
          (∫ y, U y * ⟪gradient ρ y, v y⟫) =
        ∫ y, ρ y * ⟪gradient U y, v y⟫ := by
    linarith [hsumRel]
  calc
    ∫ y, ρ y * (U y * weightedGen ρ χ y) =
        ∫ y, ρ y * ⟪gradient U y, v y⟫ := by
      calc
        ∫ y, ρ y * (U y * weightedGen ρ χ y) =
            ∫ y, -(U y * ρ y * s45_div v y) -
              U y * ⟪gradient ρ y, v y⟫ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          exact hgen y
        _ = ∫ y, ρ y * ⟪gradient U y, v y⟫ := by
          have hsub := integral_sub (μ := (volume : Measure (Euc d)))
            hdivI.neg hA
          have hnegInt : (∫ y, -(U y * ρ y * s45_div v y)) =
              -(∫ y, U y * ρ y * s45_div v y) := by
            rw [integral_neg]
          calc
            ∫ y, -(U y * ρ y * s45_div v y) -
                U y * ⟪gradient ρ y, v y⟫ =
                (∫ y, -(U y * ρ y * s45_div v y)) -
                  ∫ y, U y * ⟪gradient ρ y, v y⟫ := hsub
            _ = -(∫ y, U y * ρ y * s45_div v y) -
                ∫ y, U y * ⟪gradient ρ y, v y⟫ := by rw [hnegInt]
            _ = ∫ y, ρ y * ⟪gradient U y, v y⟫ := hfinalScalars
    _ = ∫ y, ρ y * ⟪v y, gradient U y⟫ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      exact congrArg (fun z : ℝ => ρ y * z)
        (real_inner_comm (v y) (gradient U y))

#print axioms fp81s21_initial_ibp_potential

end HRS.Fp81.S21

end
