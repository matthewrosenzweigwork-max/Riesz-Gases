import HRS.MS.QsfCorr2

/-!
# S4.5 packet B1, part 3: integration by parts against `μ` and the covariance identification

`s45_ibp_mu`: `∫ φ (Lχ) dμ = ∫ ⟨∇φ, ∇χ⟩ dμ` for bounded `C¹` `φ` (with `L = thermalGen`).
`s45_cov_identity`: `C_{ij} = β⁻¹ ∫ ⟨∇χ_i, ∇φ_j⟩ dμ` for the susceptibility covariance of the features, where `χ_i` is a
corrector of `φ_i` (S4.4).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s45_thermal_logmoment2 {s : ℝ} {a β C c BU : ℝ}
    (hT : ThermalData d s a β C c BU) : ∃ L, HasLogMoment2 (thermalMeasure d s a β) L := by
  have hμ : thermalMeasure d s a β = withDensityReal (thermalDensity d s a β) := rfl
  have hc := hT.hc
  obtain ⟨Cp, hCp0, hCp⟩ := s45_poly_le (c := c / 4) (by positivity)
  have hint : Integrable (fun x : Euc d => Real.log (2 + ‖x‖) ^ 2) (thermalMeasure d s a β) := by
    rw [hμ, HRS.MS.TcR.tc2_integrable_nu hT.prob]
    have hg := HRS.MP.SelfSimP4Impl.p4g_integrable_gauss d (b := c / 2) (by positivity)
    refine Integrable.mono' (hg.const_mul (C * Cp ^ 2))
      ((hT.prob.measurable.mul (((Real.measurable_log.comp
        (measurable_const.add measurable_norm))).pow_const 2)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => ?_)
    have hn := norm_nonneg y
    have hl0 : 0 ≤ Real.log (2 + ‖y‖) := Real.log_nonneg (by linarith)
    have hl1 : Real.log (2 + ‖y‖) ≤ 1 + ‖y‖ := by
      have := Real.log_le_sub_one_of_pos (x := 2 + ‖y‖) (by positivity); linarith
    have hl2 : Real.log (2 + ‖y‖) ^ 2 ≤ (Cp * Real.exp (c / 4 * ‖y‖ ^ 2)) ^ 2 :=
      pow_le_pow_left₀ hl0 (hl1.trans (hCp ‖y‖ hn)) 2
    have e : (Cp * Real.exp (c / 4 * ‖y‖ ^ 2)) ^ 2 = Cp ^ 2 * Real.exp (c / 2 * ‖y‖ ^ 2) := by
      rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
    have e2 : Real.exp (c / 2 * ‖y‖ ^ 2) * Real.exp (-c * ‖y‖ ^ 2) =
        Real.exp (-(c / 2 * ‖y‖ ^ 2)) := by rw [← Real.exp_add]; congr 1; ring
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hT.prob.nonneg y) (sq_nonneg _))]
    calc thermalDensity d s a β y * Real.log (2 + ‖y‖) ^ 2
        ≤ (C * Real.exp (-c * ‖y‖ ^ 2)) * (Cp ^ 2 * Real.exp (c / 2 * ‖y‖ ^ 2)) := by
          refine mul_le_mul ?_ (hl2.trans e.le) (sq_nonneg _) (by have := hT.C0; positivity)
          exact (le_abs_self _).trans (hT.h0 y)
      _ = (C * Cp ^ 2) * (Real.exp (c / 2 * ‖y‖ ^ 2) * Real.exp (-c * ‖y‖ ^ 2)) := by ring
      _ = _ := by rw [e2]
  exact ⟨_, hint, le_rfl⟩

/-- Integration by parts against the thermal measure: `∫ φ (Lχ) dμ = ∫ ⟨∇φ, ∇χ⟩ dμ`. -/
theorem s45_ibp_mu {s a β C c BU : ℝ} (hT : ThermalData d s a β C c BU) {χ : Euc d → ℝ}
    (hχ : ContDiff ℝ 2 χ) {B1 B2 : ℝ} (hB1 : ∀ x, ‖gradient χ x‖ ≤ B1)
    (hB2 : ∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B2) {φ : Euc d → ℝ} (hφ : ContDiff ℝ 1 φ) {Bφ Dφ : ℝ}
    (hBφ : ∀ x, |φ x| ≤ Bφ) (hDφ : ∀ x, ‖fderiv ℝ φ x‖ ≤ Dφ) :
    ∫ y, φ y * thermalGen d s a β χ y ∂(thermalMeasure d s a β) =
      ∫ y, ⟪gradient φ y, gradient χ y⟫ ∂(thermalMeasure d s a β) := by
  set ρ := thermalDensity d s a β with hρdef
  set U := convMeasure (rieszKernel d s) (thermalMeasure d s a β) with hUdef
  set v := gradient χ with hvdef
  have hc := hT.hc
  have hC := hT.C0
  have hμ : thermalMeasure d s a β = withDensityReal ρ := rfl
  have hρ1 : ContDiff ℝ 1 ρ := hT.smooth.of_le (by exact_mod_cast le_top)
  have hv1 : ContDiff ℝ 1 v := s45_contDiff_gradient hχ
  have hUd : Differentiable ℝ U := hT.Usmooth.differentiable (by simp)
  have hB10 : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0)
  have hB20 : 0 ≤ B2 := (norm_nonneg _).trans (hB2 0)
  have hBφ0 : 0 ≤ Bφ := (abs_nonneg _).trans (hBφ 0)
  have hDφ0 : 0 ≤ Dφ := (norm_nonneg _).trans (hDφ 0)
  have hg := HRS.MP.SelfSimP4Impl.p4g_integrable_gauss d hc
  have hgE : ∀ y : Euc d, Real.exp (-c * ‖y‖ ^ 2) = Real.exp (-(c * ‖y‖ ^ 2)) := fun y => by rw [neg_mul]
  have hρd : Differentiable ℝ ρ := hρ1.differentiable (by norm_num)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hfd : Differentiable ℝ (fun y => φ y * ρ y) := hφd.mul hρd
  -- bounds
  have hfb : ∀ y, |φ y * ρ y| ≤ (Bφ * C) * Real.exp (-(c * ‖y‖ ^ 2)) := by
    intro y; rw [abs_mul, ← hgE]
    calc |φ y| * |ρ y| ≤ Bφ * (C * Real.exp (-c * ‖y‖ ^ 2)) :=
          mul_le_mul (hBφ y) (hT.h0 y) (abs_nonneg _) hBφ0
      _ = _ := by ring
  have hρ' : ∀ y, ‖fderiv ℝ ρ y‖ ≤ C * Real.exp (-(c * ‖y‖ ^ 2)) := fun y => by rw [← hgE]; exact hT.h1 y
  have hρ0 : ∀ y, |ρ y| ≤ C * Real.exp (-(c * ‖y‖ ^ 2)) := fun y => by rw [← hgE]; exact hT.h0 y
  have hfd' : ∀ y, HasFDerivAt (fun y => φ y * ρ y) (φ y • fderiv ℝ ρ y + ρ y • fderiv ℝ φ y) y :=
    fun y => (hφd y).hasFDerivAt.mul (hρd y).hasFDerivAt
  have hdf : ∀ y, ‖fderiv ℝ (fun y => φ y * ρ y) y‖ ≤ (Dφ * C + Bφ * C) * Real.exp (-(c * ‖y‖ ^ 2)) := by
    intro y
    rw [(hfd' y).fderiv]
    calc ‖φ y • fderiv ℝ ρ y + ρ y • fderiv ℝ φ y‖ ≤ ‖φ y • fderiv ℝ ρ y‖ + ‖ρ y • fderiv ℝ φ y‖ :=
          norm_add_le _ _
      _ ≤ (Bφ * (C * Real.exp (-(c * ‖y‖ ^ 2)))) + ((C * Real.exp (-(c * ‖y‖ ^ 2))) * Dφ) := by
          refine add_le_add ?_ ?_
          · rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul (hBφ y) (hρ' y) (norm_nonneg _) hBφ0
          · rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul (hρ0 y) (hDφ y) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hfC : ContDiff ℝ 1 (fun y => φ y * ρ y) := hφ.mul hρ1
  have hnb : ∀ b : Fin d, ‖(EuclideanSpace.single b (1 : ℝ) : Euc d)‖ ≤ 1 := fun b => by simp
  have hgb : ∀ b : Fin d, ContDiff ℝ 1 (fun y => v y b) := fun b =>
    (EuclideanSpace.proj b : Euc d →L[ℝ] ℝ).contDiff.comp hv1
  have hgbd : ∀ (b : Fin d) (y : Euc d), HasFDerivAt (fun y => v y b)
      ((EuclideanSpace.proj b : Euc d →L[ℝ] ℝ).comp (fderiv ℝ v y)) y := fun b y =>
    (EuclideanSpace.proj b : Euc d →L[ℝ] ℝ).hasFDerivAt.comp y
      ((hv1.differentiable (by norm_num)) y).hasFDerivAt
  have hgbB : ∀ (b : Fin d) (y : Euc d), |v y b| ≤ B1 := fun b y => (s45_abs_coord_le _ _).trans (hB1 y)
  have hgbD : ∀ (b : Fin d) (y : Euc d), |fderiv ℝ (fun y => v y b) y (EuclideanSpace.single b 1)| ≤ B2 := by
    intro b y
    rw [(hgbd b y).fderiv]
    simp only [ContinuousLinearMap.comp_apply]
    refine (s45_abs_coord_le _ _).trans ?_
    calc ‖fderiv ℝ v y (EuclideanSpace.single b (1 : ℝ))‖
        ≤ ‖fderiv ℝ v y‖ * ‖(EuclideanSpace.single b (1 : ℝ) : Euc d)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ B2 * 1 := mul_le_mul (hB2 y) (hnb b) (norm_nonneg _) hB20
      _ = B2 := mul_one _
  have key : ∀ b : Fin d,
      Integrable (fun y => φ y * ρ y * fderiv ℝ (fun y => v y b) y (EuclideanSpace.single b 1)) ∧
      Integrable (fun y => fderiv ℝ (fun y => φ y * ρ y) y (EuclideanSpace.single b 1) * v y b) ∧
      ∫ y, φ y * ρ y * fderiv ℝ (fun y => v y b) y (EuclideanSpace.single b 1) =
        -∫ y, fderiv ℝ (fun y => φ y * ρ y) y (EuclideanSpace.single b 1) * v y b := by
    intro b
    have hgd : Differentiable ℝ (fun y => v y b) := (hgb b).differentiable (by norm_num)
    have hI1 : Integrable (fun y => φ y * ρ y * fderiv ℝ (fun y => v y b) y (EuclideanSpace.single b 1)) := by
      refine Integrable.mono' (hg.const_mul ((Bφ * C) * B2))
        ((hfC.continuous.mul ((hgb b).continuous_fderiv one_ne_zero |>.clm_apply continuous_const)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      calc |φ y * ρ y| * |fderiv ℝ (fun y => v y b) y (EuclideanSpace.single b 1)|
          ≤ ((Bφ * C) * Real.exp (-(c * ‖y‖ ^ 2))) * B2 := mul_le_mul (hfb y) (hgbD b y) (abs_nonneg _) (by positivity)
        _ = _ := by ring
    have hI2 : Integrable (fun y => fderiv ℝ (fun y => φ y * ρ y) y (EuclideanSpace.single b 1) * v y b) := by
      refine Integrable.mono' (hg.const_mul ((Dφ * C + Bφ * C) * B1))
        ((((hfC.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul (hgb b).continuous).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |fderiv ℝ (fun y => φ y * ρ y) y (EuclideanSpace.single b 1)| ≤
          (Dφ * C + Bφ * C) * Real.exp (-(c * ‖y‖ ^ 2)) := by
        refine le_trans ?_ (hdf y)
        calc |fderiv ℝ (fun y => φ y * ρ y) y (EuclideanSpace.single b 1)|
            = ‖fderiv ℝ (fun y => φ y * ρ y) y (EuclideanSpace.single b 1)‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖fderiv ℝ (fun y => φ y * ρ y) y‖ * ‖(EuclideanSpace.single b (1 : ℝ) : Euc d)‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ ‖fderiv ℝ (fun y => φ y * ρ y) y‖ * 1 := by gcongr; exact hnb b
          _ = _ := mul_one _
      calc _ ≤ ((Dφ * C + Bφ * C) * Real.exp (-(c * ‖y‖ ^ 2))) * B1 :=
            mul_le_mul h1 (hgbB b y) (abs_nonneg _) (by positivity)
        _ = _ := by ring
    have hI3 : Integrable (fun y => φ y * ρ y * v y b) := by
      refine Integrable.mono' (hg.const_mul ((Bφ * C) * B1))
        ((hfC.continuous.mul (hgb b).continuous).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      calc |φ y * ρ y| * |v y b| ≤ ((Bφ * C) * Real.exp (-(c * ‖y‖ ^ 2))) * B1 :=
            mul_le_mul (hfb y) (hgbB b y) (abs_nonneg _) (by positivity)
        _ = _ := by ring
    exact ⟨hI1, hI2, integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Euc d)))
      (f := fun y => φ y * ρ y) (g := fun y => v y b) (v := EuclideanSpace.single b 1)
      hI2 hI1 hI3 (fun y _ => hfd y) (fun y _ => hgd y)⟩
  -- sum over the coordinates
  have hsum : ∑ b : Fin d, ∫ y, φ y * ρ y * fderiv ℝ (fun y => v y b) y (EuclideanSpace.single b 1) =
      -∑ b : Fin d, ∫ y, fderiv ℝ (fun y => φ y * ρ y) y (EuclideanSpace.single b 1) * v y b := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun b _ => (key b).2.2
  rw [← integral_finsetSum _ (fun b _ => (key b).1), ← integral_finsetSum _ (fun b _ => (key b).2.1),
    ← integral_neg] at hsum
  have hdivp : ∀ y, ∑ b : Fin d, φ y * ρ y * fderiv ℝ (fun y => v y b) y (EuclideanSpace.single b 1) =
      φ y * ρ y * s45_div v y := by
    intro y
    rw [← Finset.mul_sum]
    congr 1
    unfold s45_div
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [(hgbd b y).fderiv]; rfl
  have hgrad : ∀ y, ∑ b : Fin d, fderiv ℝ (fun y => φ y * ρ y) y (EuclideanSpace.single b 1) * v y b =
      φ y * ⟪gradient ρ y, v y⟫ + ρ y * ⟪gradient φ y, v y⟫ := by
    intro y
    rw [s45_inner_eq_sum, s45_inner_eq_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [(hfd' y).fderiv]
    simp only [movtr_gradient_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    ring
  simp_rw [hdivp, hgrad] at hsum
  -- integrability of the two pieces
  have hgρ : Continuous (gradient ρ) := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp (hρ1.continuous_fderiv one_ne_zero)
  have hgφ : Continuous (gradient φ) := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)
  have hA : Integrable (fun y => φ y * ⟪gradient ρ y, v y⟫) := by
    refine Integrable.mono' (hg.const_mul (Bφ * (C * B1)))
      ((hφ.continuous.mul (hgρ.inner hv1.continuous)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |φ y| * |⟪gradient ρ y, v y⟫| ≤ Bφ * ((C * Real.exp (-(c * ‖y‖ ^ 2))) * B1) := by
          refine mul_le_mul (hBφ y) ?_ (abs_nonneg _) hBφ0
          calc |⟪gradient ρ y, v y⟫| ≤ ‖gradient ρ y‖ * ‖v y‖ := abs_real_inner_le_norm _ _
            _ ≤ (C * Real.exp (-(c * ‖y‖ ^ 2))) * B1 := by
                refine mul_le_mul ?_ (hB1 y) (norm_nonneg _) (by positivity)
                rw [s45_norm_gradient]; exact hρ' y
      _ = _ := by ring
  have hB : Integrable (fun y => ρ y * ⟪gradient φ y, v y⟫) := by
    refine Integrable.mono' (hg.const_mul (C * (Dφ * B1)))
      ((hρ1.continuous.mul (hgφ.inner hv1.continuous)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |ρ y| * |⟪gradient φ y, v y⟫| ≤ (C * Real.exp (-(c * ‖y‖ ^ 2))) * (Dφ * B1) := by
          refine mul_le_mul (hρ0 y) ?_ (abs_nonneg _) (by positivity)
          calc |⟪gradient φ y, v y⟫| ≤ ‖gradient φ y‖ * ‖v y‖ := abs_real_inner_le_norm _ _
            _ ≤ Dφ * B1 := by
                refine mul_le_mul ?_ (hB1 y) (norm_nonneg _) hDφ0
                rw [s45_norm_gradient]; exact hDφ y
      _ = _ := by ring
  have hdivI : Integrable (fun y => φ y * ρ y * s45_div v y) :=
    (integrable_finsetSum _ fun b _ => (key b).1).congr (Filter.Eventually.of_forall hdivp)
  rw [integral_neg, integral_add hA hB] at hsum
  have hUd : Differentiable ℝ U := hT.Usmooth.differentiable (by simp)
  have hgenp : ∀ y, ρ y * (φ y * thermalGen d s a β χ y) =
      -(φ y * ρ y * s45_div v y) - φ y * ⟪gradient ρ y, v y⟫ := by
    intro y
    rw [s45_gen_eq hUd y, s45_div_gradient hχ y, hT.grad_rho y]
    simp only [real_inner_smul_left, inner_add_left, real_inner_smul_left]
    ring
  rw [hμ, HRS.MS.TcR.tc2_integral_nu hT.prob (fun y => φ y * thermalGen d s a β χ y),
    HRS.MS.TcR.tc2_integral_nu hT.prob (fun y => ⟪gradient φ y, gradient χ y⟫)]
  show ∫ x, ρ x * (φ x * thermalGen d s a β χ x) = ∫ x, ρ x * ⟪gradient φ x, v x⟫
  simp_rw [hgenp]
  have hdivI' : Integrable (fun y => -(φ y * ρ y * s45_div v y)) := hdivI.neg
  rw [integral_sub hdivI' hA, integral_neg, hsum]
  ring

/-- **The covariance identification** `C_{ij} = β⁻¹ ∫ ⟨∇χ_i, ∇φ_j⟩ dμ` for the susceptibility covariance. -/
theorem s45_cov_identity (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β C c BU : ℝ}
    (hβ : 0 < β) (hT : ThermalData d s a β C c BU) {χ : Euc d → ℝ} (hχ : ContDiff ℝ 2 χ)
    {B1 B2 : ℝ} (hB1 : ∀ x, ‖gradient χ x‖ ≤ B1) (hB2 : ∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B2)
    {φi φj : Euc d → ℝ} (hφi : MemLp φi 2 (thermalMeasure d s a β))
    (hr2 : MemLp (thermalGen d s a β χ) 2 (thermalMeasure d s a β))
    (hcorr : ∀ᵐ x ∂(thermalMeasure d s a β),
      susceptibilityOp (rieszKernel d s) (thermalMeasure d s a β) β (thermalGen d s a β χ) x =
        projMean (thermalMeasure d s a β) φi x)
    (hφj : ContDiff ℝ 1 φj) {Bφ Dφ : ℝ} (hBφ : ∀ x, |φj x| ≤ Bφ)
    (hDφ : ∀ x, ‖fderiv ℝ φj x‖ ≤ Dφ) :
    susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) β φi φj =
      β⁻¹ * ∫ y, ⟪gradient χ y, gradient φj y⟫ ∂(thermalMeasure d s a β) := by
  have hd1 : 1 ≤ d := by omega
  have hμ : thermalMeasure d s a β = withDensityReal (thermalDensity d s a β) := rfl
  haveI hprob : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  obtain ⟨L, hL⟩ := s45_thermal_logmoment2 hT
  have hM : ∀ x, thermalDensity d s a β x ≤ C := fun x => (le_abs_self _).trans
    ((hT.h0 x).trans (by
      have : Real.exp (-c * ‖x‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖, hT.hc])
      nlinarith [hT.C0]))
  obtain ⟨K, hK⟩ : ∃ K : Lp ℝ 2 (thermalMeasure d s a β) →L[ℝ] Lp ℝ 2 (thermalMeasure d s a β),
      IsKData (thermalMeasure d s a β) (rieszKernel d s) K :=
    s45_kdata hd1 hs0 hsd hT.prob hM (L := L) (fun _ => hL)
  -- the mean of `r` is zero (IBP with `φ = 1`)
  have hmean : ∫ y, thermalGen d s a β χ y ∂(thermalMeasure d s a β) = 0 := by
    have h := s45_ibp_mu hT hχ hB1 hB2 (φ := fun _ => (1 : ℝ)) contDiff_const (Bφ := 1) (Dφ := 0)
      (fun _ => by simp) (fun _ => by simp)
    simpa using h
  set Rh : Lp ℝ 2 (thermalMeasure d s a β) := hr2.toLp (thermalGen d s a β χ) with hRh
  have hRhae : (Rh : Euc d → ℝ) =ᵐ[thermalMeasure d s a β] thermalGen d s a β χ :=
    MemLp.coeFn_toLp hr2
  have hP : HRS.Whole.Q34.Pc (thermalMeasure d s a β) Rh = Rh := by
    rw [s45_centered_iff, integral_congr_ae hRhae]; exact hmean
  have hUi := s45_U_ae hφi
  have hkop : Kop (rieszKernel d s) (thermalMeasure d s a β) (thermalGen d s a β χ) =
      Kop (rieszKernel d s) (thermalMeasure d s a β) (Rh : Euc d → ℝ) :=
    (HRS.MS.TcR.tc2_kop_congr_ae hRhae).symm
  have heq : Rh + β • K Rh = β • s45_U φi hφi := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_add Rh (β • K Rh), Lp.coeFn_smul β (K Rh),
      Lp.coeFn_smul β (s45_U φi hφi), hRhae, hK.kop Rh hP, hcorr, hUi] with x e1 e2 e3 e4 e5 e6 e7
    rw [e1, Pi.add_apply, e2, Pi.smul_apply, smul_eq_mul, e3, Pi.smul_apply, smul_eq_mul, e7, ← e5,
      e4, ← hkop]
    unfold susceptibilityOp at e6
    have : thermalGen d s a β χ x + β * Kop (rieszKernel d s) (thermalMeasure d s a β)
        (thermalGen d s a β χ) x = β * projMean (thermalMeasure d s a β) φi x := by
      calc _ = β * (β⁻¹ * thermalGen d s a β χ x + Kop (rieszKernel d s) (thermalMeasure d s a β)
            (thermalGen d s a β χ) x) := by field_simp
        _ = _ := by rw [e6]
    exact this
  have hRh2 : Rh = β • s45_Rr hK hβ.le (s45_U φi hφi) := by
    rw [← map_smul, ← ContinuousLinearEquiv.symm_apply_eq, s45_Rr_symm_apply]
    exact heq
  have hφj2 : MemLp φj 2 (thermalMeasure d s a β) :=
    MemLp.of_bound hφj.continuous.aestronglyMeasurable Bφ
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hBφ x)
  have hRU : s45_Rr hK hβ.le (s45_U φi hφi) = β⁻¹ • Rh := by
    rw [hRh2, smul_smul, inv_mul_cancel₀ hβ.ne', one_smul]
  have hr1 : Integrable (thermalGen d s a β χ) (thermalMeasure d s a β) := hr2.integrable one_le_two
  have hφr : Integrable (fun x => φj x * thermalGen d s a β χ x) (thermalMeasure d s a β) :=
    hφj2.integrable_mul hr2
  have hin : ⟪s45_U φj hφj2, Rh⟫ = ∫ x, φj x * thermalGen d s a β χ x ∂(thermalMeasure d s a β) := by
    rw [← HRS.Whole.Q34.l2Inner_eq (s45_U_ae hφj2).symm hRhae.symm]
    unfold l2Inner projMean pair
    have : (fun x => (φj x - ∫ y, φj y ∂(thermalMeasure d s a β)) * thermalGen d s a β χ x) =
        fun x => φj x * thermalGen d s a β χ x -
          (∫ y, φj y ∂(thermalMeasure d s a β)) * thermalGen d s a β χ x := by
      funext x; ring
    rw [this, integral_sub hφr (hr1.const_mul _), integral_const_mul, hmean, mul_zero, sub_zero]
  rw [s45_susceptibilityCov_eq hK hβ hφi hφj2, s45_inner_Rr_comm hK hβ.le, hRU, real_inner_smul_right,
    hin, s45_ibp_mu hT hχ hB1 hB2 hφj hBφ hDφ]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  exact real_inner_comm _ _

end S45

end
