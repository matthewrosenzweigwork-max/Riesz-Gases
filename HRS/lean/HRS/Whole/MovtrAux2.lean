import HRS.Whole.MovtrAux1

/-!
# MOVTR auxiliary 2: differentiation of the potential `g * ρ`
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d : ℕ}

/-- Gaussian shift: if `‖x'‖ ≤ R` then `e^{-c‖x'-z‖²} ≤ e^{cR²} e^{-(c/2)‖z‖²}`. -/
lemma movtr_gauss_shift {c R : ℝ} (hc : 0 < c) {x' : Euc d} (hx : ‖x'‖ ≤ R) (z : Euc d) :
    Real.exp (-c * ‖x' - z‖ ^ 2) ≤ Real.exp (c * R ^ 2) * Real.exp (-(c / 2) * ‖z‖ ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : ‖z‖ ≤ ‖x'‖ + ‖x' - z‖ := by
    calc ‖z‖ = ‖x' - (x' - z)‖ := by simp
      _ ≤ ‖x'‖ + ‖x' - z‖ := norm_sub_le _ _
  have h2 : ‖z‖ ^ 2 ≤ 2 * ‖x'‖ ^ 2 + 2 * ‖x' - z‖ ^ 2 := by
    nlinarith [sq_nonneg (‖x'‖ - ‖x' - z‖), norm_nonneg z, norm_nonneg x', norm_nonneg (x' - z)]
  have h3 : ‖x'‖ ^ 2 ≤ R ^ 2 := by
    have := norm_nonneg x'
    nlinarith
  nlinarith

lemma movtr_integrable_of_gauss_bound {c : ℝ} (hc : 0 < c) {k : Euc d → ℝ} {B : Euc d → ℝ}
    (hk : AEStronglyMeasurable k volume) (hB : ∀ᵐ z, |k z| ≤ B z)
    (hBint : Integrable (fun z => B z * Real.exp (-(c / 2) * ‖z‖ ^ 2))) {C R : ℝ} (hC : 0 ≤ C)
    {ρ : Euc d → ℝ} (hρc : Continuous ρ) {x' : Euc d} (hx : ‖x'‖ ≤ R)
    (h0 : ∀ y, |ρ y| ≤ C * Real.exp (-c * ‖y‖ ^ 2)) :
    Integrable (fun z => k z * ρ (x' - z)) := by
  have hmeas : AEStronglyMeasurable (fun z => k z * ρ (x' - z)) volume :=
    hk.mul (hρc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  refine Integrable.mono' (hBint.const_mul (C * Real.exp (c * R ^ 2))) hmeas ?_
  filter_upwards [hB] with z hz
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  have h1 := h0 (x' - z)
  have h2 := movtr_gauss_shift hc hx z
  calc |k z| * |ρ (x' - z)| ≤ B z * (C * (Real.exp (c * R ^ 2) * Real.exp (-(c / 2) * ‖z‖ ^ 2))) := by
        apply mul_le_mul hz (h1.trans (mul_le_mul_of_nonneg_left h2 hC)) (abs_nonneg _)
        exact (abs_nonneg _).trans hz
    _ = C * Real.exp (c * R ^ 2) * (B z * Real.exp (-(c / 2) * ‖z‖ ^ 2)) := by ring


/-- Differentiation under the integral sign of `h ↦ ∫ k(z) ρ(x + h e - z) dz`. -/
lemma movtr_hasDerivAt_conv {c : ℝ} (hc : 0 < c) {k : Euc d → ℝ} {B : Euc d → ℝ}
    (hk : AEStronglyMeasurable k volume) (hB : ∀ᵐ z, |k z| ≤ B z)
    (hBint : Integrable (fun z => B z * Real.exp (-(c / 2) * ‖z‖ ^ 2))) {C : ℝ} (hC : 0 ≤ C)
    {ρ : Euc d → ℝ} (hρ1 : ContDiff ℝ 1 ρ)
    (h0 : ∀ y, |ρ y| ≤ C * Real.exp (-c * ‖y‖ ^ 2))
    (h1 : ∀ y, ‖fderiv ℝ ρ y‖ ≤ C * Real.exp (-c * ‖y‖ ^ 2)) (x e : Euc d) (he : ‖e‖ ≤ 1) :
    HasDerivAt (fun h : ℝ => ∫ z, k z * ρ (x + h • e - z))
      (∫ z, k z * fderiv ℝ ρ (x - z) e) 0 := by
  have hρc : Continuous ρ := hρ1.continuous
  have hdiff : Differentiable ℝ ρ := hρ1.differentiable (by norm_num)
  have hfd : Continuous (fderiv ℝ ρ) := hρ1.continuous_fderiv (by norm_num)
  set R : ℝ := ‖x‖ + 1 with hR
  have hRn : ∀ h : ℝ, |h| < 1 → ‖x + h • e‖ ≤ R := by
    intro h hh
    calc ‖x + h • e‖ ≤ ‖x‖ + ‖h • e‖ := norm_add_le _ _
      _ ≤ ‖x‖ + 1 := by
        rw [norm_smul, Real.norm_eq_abs]
        have : |h| * ‖e‖ ≤ 1 := by
          calc |h| * ‖e‖ ≤ 1 * 1 := mul_le_mul hh.le he (norm_nonneg _) zero_le_one
            _ = 1 := by norm_num
        linarith
  have hmeasF : ∀ h : ℝ, AEStronglyMeasurable (fun z => k z * ρ (x + h • e - z)) volume := by
    intro h
    exact hk.mul (hρc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hint0 : Integrable (fun z => k z * ρ (x + (0:ℝ) • e - z)) := by
    have := movtr_integrable_of_gauss_bound hc hk hB hBint hC hρc (x' := x + (0:ℝ) • e) (R := R)
      (hRn 0 (by simp)) h0
    exact this
  have hmeasF' : AEStronglyMeasurable (fun z => k z * fderiv ℝ ρ (x + (0:ℝ) • e - z) e) volume := by
    refine hk.mul ?_
    have : Continuous fun z : Euc d => fderiv ℝ ρ (x + (0:ℝ) • e - z) e :=
      (hfd.comp (continuous_const.sub continuous_id)).clm_apply continuous_const
    exact this.aestronglyMeasurable
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (h : ℝ) (z : Euc d) => k z * ρ (x + h • e - z))
    (F' := fun (h : ℝ) (z : Euc d) => k z * fderiv ℝ ρ (x + h • e - z) e)
    (bound := fun z => C * Real.exp (c * R ^ 2) * (B z * Real.exp (-(c / 2) * ‖z‖ ^ 2)))
    (x₀ := 0) (s := Metric.ball 0 1) (Metric.ball_mem_nhds 0 one_pos)
    (Filter.Eventually.of_forall hmeasF) hint0 hmeasF' ?_ (hBint.const_mul _) ?_
  · simpa using key.2
  · filter_upwards [hB] with z hz h hh
    have hh' : |h| < 1 := by simpa using hh
    rw [norm_mul, Real.norm_eq_abs]
    have h1' := h1 (x + h • e - z)
    have h2 := movtr_gauss_shift hc (hRn h hh') z
    have h3 : ‖fderiv ℝ ρ (x + h • e - z) e‖ ≤ C * (Real.exp (c * R ^ 2) * Real.exp (-(c / 2) * ‖z‖ ^ 2)) := by
      calc ‖fderiv ℝ ρ (x + h • e - z) e‖ ≤ ‖fderiv ℝ ρ (x + h • e - z)‖ * ‖e‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖fderiv ℝ ρ (x + h • e - z)‖ * 1 := by gcongr
        _ = ‖fderiv ℝ ρ (x + h • e - z)‖ := by ring
        _ ≤ C * Real.exp (-c * ‖x + h • e - z‖ ^ 2) := h1'
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 hC
    calc |k z| * ‖fderiv ℝ ρ (x + h • e - z) e‖
        ≤ B z * (C * (Real.exp (c * R ^ 2) * Real.exp (-(c / 2) * ‖z‖ ^ 2))) :=
          mul_le_mul hz h3 (norm_nonneg _) ((abs_nonneg _).trans hz)
      _ = _ := by ring
  · refine Filter.Eventually.of_forall fun z h _ => ?_
    have hline : HasDerivAt (fun h : ℝ => x + h • e - z) e h := by
      have := ((hasDerivAt_id h).smul_const e).const_add x
      simpa [sub_eq_add_neg, add_assoc] using this.sub_const z
    have h1 := (hdiff (x + h • e - z)).hasFDerivAt.comp_hasDerivAt h hline
    exact h1.const_mul (k z)


lemma movtr_gEps_measurable (s ε : ℝ) : Measurable (movtr_gEps d s ε) := by
  unfold movtr_gEps
  by_cases hs : s = 0
  · simp only [hs, ite_true]
    exact (Real.measurable_log.comp ((measurable_norm.pow_const 2).add_const _)).const_mul _
  · simp only [hs, ite_false]
    exact ((measurable_norm.pow_const 2).add_const _).pow_const _

/-- The integrable majorant of the kernel against a Gaussian weight. -/
lemma movtr_majorant_integrable (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {c : ℝ}
    (hc : 0 < c) :
    Integrable (fun z : Euc d => (2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1) * Real.exp (-c * ‖z‖ ^ 2)) := by
  have h1 := movtr_integrable_rpow_gauss (d := d) hd (α := -movtr_sp s)
    (by have := movtr_sp_lt (d := d) hsd hd; linarith) hc
  have h2 := movtr_integrable_rpow_gauss (d := d) hd (α := 1) (by
    have : (0:ℝ) ≤ d := Nat.cast_nonneg d
    linarith) hc
  have h3 := movtr_integrable_rpow_gauss (d := d) hd (α := 0) (by
    have : (0:ℝ) ≤ d := Nat.cast_nonneg d
    have : (1:ℝ) ≤ d := by exact_mod_cast hd
    linarith) hc
  simp only [Real.rpow_one, Real.rpow_zero, one_mul] at h2 h3
  have := ((h1.const_mul 2).add h2).add h3
  refine this.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.add_apply]
  ring

/-- The `e`-derivative of the smoothed kernel. -/
def movtr_dEps (d : ℕ) (s ε : ℝ) (e z : Euc d) : ℝ :=
  -(movtr_sigma s * (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1)) * inner ℝ z e

lemma movtr_dEps_abs_le {s : ℝ} (hs0 : 0 ≤ s) {ε : ℝ} (hε : 0 < ε) (e z : Euc d) (he : ‖e‖ ≤ 1) :
    |movtr_dEps d s ε e z| ≤ movtr_sigma s * ε ^ (-s - 1) := by
  have hσ : 0 ≤ movtr_sigma s := by unfold movtr_sigma; split_ifs <;> linarith
  have hu : 0 < ‖z‖ ^ 2 + ε ^ 2 := by positivity
  unfold movtr_dEps
  set u := ‖z‖ ^ 2 + ε ^ 2 with hu_def
  have hzu : ‖z‖ ≤ u ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ε])
  have hin : |inner ℝ z e| ≤ u ^ (1 / 2 : ℝ) := by
    calc |inner ℝ z e| ≤ ‖z‖ * ‖e‖ := abs_real_inner_le_norm _ _
      _ ≤ u ^ (1 / 2 : ℝ) * 1 := mul_le_mul hzu he (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hup : 0 ≤ u ^ (-s / 2 - 1) := Real.rpow_nonneg hu.le _
  rw [abs_mul, abs_neg, abs_of_nonneg (mul_nonneg hσ hup)]
  have h2 : u ^ (-s / 2 - 1) * u ^ (1 / 2 : ℝ) = u ^ ((-s - 1) / 2) := by
    rw [← Real.rpow_add hu]; congr 1; ring
  have h3 : u ^ ((-s - 1) / 2) ≤ ε ^ (-s - 1) := by
    have : ε ^ (-s - 1) = (ε ^ 2) ^ ((-s - 1) / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]
      congr 1; push_cast; ring
    rw [this]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg ‖z‖]) (by linarith)
  calc movtr_sigma s * u ^ (-s / 2 - 1) * |inner ℝ z e|
      ≤ movtr_sigma s * u ^ (-s / 2 - 1) * u ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hin (mul_nonneg hσ hup)
    _ = movtr_sigma s * (u ^ (-s / 2 - 1) * u ^ (1 / 2 : ℝ)) := by ring
    _ = movtr_sigma s * u ^ ((-s - 1) / 2) := by rw [h2]
    _ ≤ movtr_sigma s * ε ^ (-s - 1) := mul_le_mul_of_nonneg_left h3 hσ


lemma movtr_integrable_of_gauss (hd : 1 ≤ d) {c C : ℝ} (hc : 0 < c) {ρ : Euc d → ℝ}
    (hρc : Continuous ρ) (h0 : ∀ y, |ρ y| ≤ C * Real.exp (-c * ‖y‖ ^ 2)) : Integrable ρ := by
  have h := (movtr_integrable_rpow_gauss (d := d) hd (α := 0) (by
    have : (1:ℝ) ≤ d := by exact_mod_cast hd
    linarith) hc).const_mul C
  refine Integrable.mono' h hρc.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  simpa using h0 y

/-- Derivative of the smoothed potential, computed on the kernel side. -/
lemma movtr_hasDerivAt_smooth (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C) {ρ : Euc d → ℝ} (hρ1 : ContDiff ℝ 1 ρ)
    (h0 : ∀ y, |ρ y| ≤ C * Real.exp (-c * ‖y‖ ^ 2)) (x e : Euc d) (he : ‖e‖ ≤ 1) :
    HasDerivAt (fun h : ℝ => ∫ z, movtr_gEps d s ε z * ρ (x + h • e - z))
      (∫ z, movtr_dEps d s ε e z * ρ (x - z)) 0 := by
  have hρc : Continuous ρ := hρ1.continuous
  have hρint : Integrable ρ := movtr_integrable_of_gauss hd hc hρc h0
  have hgm := movtr_gEps_measurable (d := d) s ε
  -- rewrite both sides by the change of variables
  have hfun : (fun h : ℝ => ∫ z, movtr_gEps d s ε z * ρ (x + h • e - z)) =
      fun h : ℝ => ∫ y, movtr_gEps d s ε (x + h • e - y) * ρ y := by
    funext h
    rw [← integral_sub_left_eq_self (fun y => movtr_gEps d s ε (x + h • e - y) * ρ y) volume
      (x + h • e)]
    simp
  have hval : ∫ z, movtr_dEps d s ε e z * ρ (x - z) = ∫ y, movtr_dEps d s ε e (x - y) * ρ y := by
    rw [← integral_sub_left_eq_self (fun z => movtr_dEps d s ε e z * ρ (x - z)) volume x]
    simp
  rw [hfun, hval]
  have hu : ∀ w : Euc d, 0 < ‖w‖ ^ 2 + ε ^ 2 := fun w => by positivity
  -- integrability at 0
  have hint0 : Integrable (fun y => movtr_gEps d s ε (x + (0:ℝ) • e - y) * ρ y) := by
    have hmaj := movtr_majorant_integrable hd hs0 hsd (c := c / 2) (by positivity)
    have := movtr_integrable_of_gauss_bound (c := c) hc (k := movtr_gEps d s ε)
      (B := fun z => 2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1) hgm.aestronglyMeasurable ?_ ?_ hC hρc
      (x' := x) (R := ‖x‖) le_rfl h0
    · have h2 := this.comp_sub_left x
      refine h2.congr (Filter.Eventually.of_forall fun y => ?_)
      simp
    · have : ({0} : Set (Euc d))ᶜ ∈ ae (volume : Measure (Euc d)) := by
        have hnt : Nontrivial (Euc d) := by
          apply Module.nontrivial_of_finrank_pos (R := ℝ)
          simp [finrank_euclideanSpace_fin]; omega
        exact compl_mem_ae_iff.mpr (measure_singleton 0)
      filter_upwards [this] with z hz
      exact movtr_gEps_abs_le hs0 hε.le hε1 hz
    · exact hmaj
  have hline : ∀ (y : Euc d) (h : ℝ), HasDerivAt (fun h : ℝ => x + h • e - y) e h := by
    intro y h
    have := ((hasDerivAt_id h).smul_const e).const_add x
    simpa [sub_eq_add_neg, add_assoc] using this.sub_const y
  have hdE : Continuous (movtr_dEps d s ε e) := by
    unfold movtr_dEps
    exact ((((continuous_norm.pow 2).add continuous_const).rpow_const
      (fun z => Or.inl (hu z).ne')).const_mul _).neg.mul (continuous_id.inner continuous_const)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (h : ℝ) (y : Euc d) => movtr_gEps d s ε (x + h • e - y) * ρ y)
    (F' := fun (h : ℝ) (y : Euc d) => movtr_dEps d s ε e (x + h • e - y) * ρ y)
    (bound := fun y => movtr_sigma s * ε ^ (-s - 1) * |ρ y|)
    (x₀ := 0) (s := Metric.ball 0 1) (Metric.ball_mem_nhds 0 one_pos)
    (Filter.Eventually.of_forall fun h => ?_) hint0 ?_ ?_ (hρint.abs.const_mul _) ?_
  · simpa using key.2
  · exact (hgm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable.mul
      hρc.aestronglyMeasurable
  · exact (hdE.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul
      hρc.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y h _ => ?_
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (movtr_dEps_abs_le hs0 hε e _ he) (abs_nonneg _)
  · refine Filter.Eventually.of_forall fun y h _ => ?_
    have h1 := (movtr_gEps_hasFDerivAt (d := d) s ε (x + h • e - y) (hu _)).comp_hasDerivAt h
      (hline y h)
    have h2 := h1.mul_const (ρ y)
    refine h2.congr_deriv ?_
    unfold movtr_dEps
    simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]


lemma movtr_u0 {s : ℝ} (z : Euc d) (hz : z ≠ 0) (a : ℝ) :
    (‖z‖ ^ 2 + (0 : ℝ) ^ 2) ^ a = ‖z‖ ^ (2 * a) := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [show (0:ℝ) ^ 2 = 0 by norm_num, add_zero, ← Real.rpow_natCast, ← Real.rpow_mul hzpos.le]
  norm_num

/-- The force `∇g(z)` off the origin. -/
lemma movtr_rieszKernelGrad_eq (s : ℝ) {z : Euc d} (hz : z ≠ 0) :
    rieszKernelGrad d s z = (-(movtr_sigma s * ‖z‖ ^ (-s - 2))) • z := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hu : 0 < ‖z‖ ^ 2 + (0:ℝ) ^ 2 := by positivity
  have h := movtr_gEps_hasFDerivAt (d := d) s 0 z hu
  rw [movtr_gEps_zero] at h
  have h2 : HasGradientAt (rieszKernel d s) ((-(movtr_sigma s * (‖z‖ ^ 2 + (0:ℝ) ^ 2) ^ (-s / 2 - 1))) • z) z := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert h using 1
    ext v
    simp [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]
  unfold rieszKernelGrad
  rw [h2.gradient, movtr_u0 (s := s) z hz]
  congr 3
  ring

lemma movtr_rieszKernelGrad_apply (s : ℝ) {z : Euc d} (hz : z ≠ 0) (i : Fin d) :
    (rieszKernelGrad d s z) i = movtr_dEps d s 0 (EuclideanSpace.single i 1) z := by
  rw [movtr_rieszKernelGrad_eq s hz]
  unfold movtr_dEps
  rw [movtr_u0 (s := s) z hz, EuclideanSpace.inner_single_right]
  have : (2 * (-s / 2 - 1)) = -s - 2 := by ring
  rw [this]
  simp

lemma movtr_rieszKernelGrad_norm (s : ℝ) (hs0 : 0 ≤ s) {z : Euc d} (hz : z ≠ 0) :
    ‖rieszKernelGrad d s z‖ = movtr_sigma s * ‖z‖ ^ (-s - 1) := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hσ : 0 ≤ movtr_sigma s := by unfold movtr_sigma; split_ifs <;> linarith
  rw [movtr_rieszKernelGrad_eq s hz, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (mul_nonneg hσ (Real.rpow_nonneg hzpos.le _))]
  rw [mul_assoc, show ‖z‖ ^ (-s - 1) = ‖z‖ ^ (-s - 2) * ‖z‖ by
    rw [show (-s - 1) = (-s - 2) + 1 by ring, Real.rpow_add hzpos, Real.rpow_one]]


/-- The scalar factor of the cancellation convention (after `y = x - z`). -/
def movtr_R (ρ : Euc d → ℝ) (x z : Euc d) : ℝ :=
  if ‖z‖ ≤ 1 / 4 then ρ (x - z) - ρ x else ρ (x - z)

lemma movtr_dEps_odd (s ε : ℝ) (e z : Euc d) :
    movtr_dEps d s ε e (-z) = -movtr_dEps d s ε e z := by
  unfold movtr_dEps
  simp [inner_neg_left]

lemma movtr_integral_dEps_ball (s ε : ℝ) (e : Euc d) :
    ∫ z, (if ‖z‖ ≤ 1 / 4 then movtr_dEps d s ε e z else 0) = 0 := by
  have h := integral_neg_eq_self (fun z : Euc d => if ‖z‖ ≤ 1 / 4 then movtr_dEps d s ε e z else 0)
    (volume : Measure (Euc d))
  have h2 : (fun z : Euc d => if ‖-z‖ ≤ 1 / 4 then movtr_dEps d s ε e (-z) else 0) =
      fun z => -(if ‖z‖ ≤ 1 / 4 then movtr_dEps d s ε e z else 0) := by
    funext z
    simp only [norm_neg, movtr_dEps_odd]
    split_ifs <;> simp
  rw [h2, integral_neg] at h
  linarith

lemma movtr_eq_eps (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C) {ρ : Euc d → ℝ} (hρ1 : ContDiff ℝ 1 ρ)
    (h0 : ∀ y, |ρ y| ≤ C * Real.exp (-c * ‖y‖ ^ 2))
    (h1 : ∀ y, ‖fderiv ℝ ρ y‖ ≤ C * Real.exp (-c * ‖y‖ ^ 2)) (x e : Euc d) (he : ‖e‖ ≤ 1) :
    ∫ z, movtr_gEps d s ε z * fderiv ℝ ρ (x - z) e = ∫ z, movtr_dEps d s ε e z * movtr_R ρ x z := by
  have hρc : Continuous ρ := hρ1.continuous
  have hgm := movtr_gEps_measurable (d := d) s ε
  have hnt : ({0} : Set (Euc d))ᶜ ∈ ae (volume : Measure (Euc d)) := by
    have : Nontrivial (Euc d) := by
      apply Module.nontrivial_of_finrank_pos (R := ℝ)
      simp; omega
    exact compl_mem_ae_iff.mpr (measure_singleton 0)
  have A := movtr_hasDerivAt_conv (c := c) hc (k := movtr_gEps d s ε)
    (B := fun z => 2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1) hgm.aestronglyMeasurable
    (by
      filter_upwards [hnt] with z hz
      exact movtr_gEps_abs_le hs0 hε.le hε1 hz)
    (movtr_majorant_integrable hd hs0 hsd (c := c / 2) (by positivity)) hC hρ1 h0 h1 x e he
  have S := movtr_hasDerivAt_smooth hd hs0 hsd hε hε1 hc hC hρ1 h0 x e he
  have hU := A.unique S
  rw [hU]
  -- remove the ball part
  have hρx : Integrable (fun z : Euc d => ρ (x - z)) :=
    (movtr_integrable_of_gauss hd hc hρc h0).comp_sub_left x
  have hbd : ∀ z, |movtr_dEps d s ε e z| ≤ movtr_sigma s * ε ^ (-s - 1) :=
    fun z => movtr_dEps_abs_le hs0 hε e z he
  have hdE : Continuous (movtr_dEps d s ε e) := by
    have hu : ∀ w : Euc d, 0 < ‖w‖ ^ 2 + ε ^ 2 := fun w => by positivity
    unfold movtr_dEps
    exact ((((continuous_norm.pow 2).add continuous_const).rpow_const
      (fun z => Or.inl (hu z).ne')).const_mul _).neg.mul (continuous_id.inner continuous_const)
  have hI1 : Integrable (fun z => movtr_dEps d s ε e z * ρ (x - z)) := by
    refine Integrable.mono' (hρx.abs.const_mul (movtr_sigma s * ε ^ (-s - 1)))
      (hdE.aestronglyMeasurable.mul (hρc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hbd z) (abs_nonneg _)
  have hI2 : Integrable (fun z : Euc d => if ‖z‖ ≤ 1 / 4 then movtr_dEps d s ε e z else 0) := by
    have hind : Integrable (Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4))
        (fun _ => movtr_sigma s * ε ^ (-s - 1))) := by
      rw [integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
      exact integrableOn_const (by simp [measure_closedBall_lt_top.ne]) 
    have hfeq : (fun z : Euc d => if ‖z‖ ≤ 1 / 4 then movtr_dEps d s ε e z else 0) =
        Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4)) (movtr_dEps d s ε e) := by
      funext z
      simp [Set.indicator, mem_closedBall_zero_iff]
    rw [hfeq]
    refine Integrable.mono' hind
      (hdE.aestronglyMeasurable.indicator Metric.isClosed_closedBall.measurableSet)
      (Filter.Eventually.of_forall fun z => ?_)
    by_cases hz : ‖z‖ ≤ 1 / 4
    · simp only [Set.indicator, mem_closedBall_zero_iff, hz, ite_true, Real.norm_eq_abs]
      exact hbd z
    · have hz' : z ∉ Metric.closedBall (0 : Euc d) (1 / 4) := by
        simpa [mem_closedBall_zero_iff] using hz
      rw [Set.indicator_of_notMem hz', Set.indicator_of_notMem hz']
      simp
  have hsplit : (fun z => movtr_dEps d s ε e z * movtr_R ρ x z) =
      fun z => movtr_dEps d s ε e z * ρ (x - z) -
        ρ x * (if ‖z‖ ≤ 1 / 4 then movtr_dEps d s ε e z else 0) := by
    funext z
    unfold movtr_R
    split_ifs <;> ring
  rw [hsplit, integral_sub hI1 (hI2.const_mul _), integral_const_mul, movtr_integral_dEps_ball]
  simp

end HRS.Whole
