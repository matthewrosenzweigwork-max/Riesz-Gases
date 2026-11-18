import HRS.MS.LogRegAux1

/-!
# C8 (part 2): the logarithmic potential `x ↦ ∫ -log‖x - y‖ F(y) dy` is `C¹` for rapidly decaying measurable `F`

(`d ≥ 2`.)  Namespace `HRS.MS.LogReg`, helper prefix `lreg_`.  Smooth regularisation
`g_ε(z) = -½ log(ε² + ‖z‖²)`, `∇g_ε(z) = -z/(ε² + ‖z‖²)`: `u_ε = g_ε ⋆ F` is differentiable by dominated
differentiation (`‖∇g_ε‖ ≤ 1/(2ε)`), and `u_ε → u`, `∇u_ε → κ ⋆ F` uniformly (`κ(z) = -z/‖z‖²`), with the
`L¹_loc` bounds `|g - g_ε| ≤ ε‖z‖⁻¹` and `‖κ - ∇g_ε‖ ≤ √ε ‖z‖^{-3/2}` (both exponents are `< d`).
-/

open MeasureTheory Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace HRS.MS.LogReg

open HRS HRS.Whole

variable {d : ℕ}

/-- `κ(z) = ∇(-log ‖z‖) = -z/‖z‖²`. -/
def lreg_kap (z : Euc d) : Euc d := -((‖z‖ ^ 2)⁻¹ • z)

/-- Regularised logarithm. -/
def lreg_gE (ε : ℝ) (z : Euc d) : ℝ := -(1 / 2) * Real.log (ε ^ 2 + ‖z‖ ^ 2)

/-- Gradient of the regularised logarithm. -/
def lreg_kE (ε : ℝ) (z : Euc d) : Euc d := -((ε ^ 2 + ‖z‖ ^ 2)⁻¹ • z)

lemma lreg_kap_norm (z : Euc d) : ‖lreg_kap z‖ = ‖z‖ ^ (-1 : ℝ) := by
  unfold lreg_kap
  rw [norm_neg, norm_smul, Real.rpow_neg_one]
  by_cases hz : z = 0
  · simp [hz]
  · have : 0 < ‖z‖ := norm_pos_iff.2 hz
    rw [norm_inv, norm_pow, norm_norm]
    field_simp

lemma lreg_kap_le (z : Euc d) : ‖lreg_kap z‖ ≤ ‖z‖ ^ (-1 : ℝ) := (lreg_kap_norm z).le

lemma lreg_kap_measurable : Measurable (lreg_kap : Euc d → Euc d) := by
  unfold lreg_kap
  exact (((measurable_norm.pow_const 2).inv).smul measurable_id).neg

lemma lreg_kE_measurable (ε : ℝ) : Measurable (lreg_kE ε : Euc d → Euc d) := by
  unfold lreg_kE
  exact ((((measurable_norm.pow_const 2).const_add (ε ^ 2)).inv).smul measurable_id).neg

lemma lreg_kE_continuous {ε : ℝ} (hε : 0 < ε) : Continuous (lreg_kE ε : Euc d → Euc d) := by
  unfold lreg_kE
  exact (Continuous.smul (Continuous.inv₀ (continuous_const.add (continuous_norm.pow 2)) fun z => (by positivity : (0 : ℝ) < ε ^ 2 + ‖z‖ ^ 2).ne') continuous_id).neg

lemma lreg_kE_le {ε : ℝ} (hε : 0 < ε) (z : Euc d) : ‖lreg_kE ε z‖ ≤ 1 / (2 * ε) := by
  unfold lreg_kE
  rw [norm_neg, norm_smul, norm_inv]
  have h1 : (0 : ℝ) < ε ^ 2 + ‖z‖ ^ 2 := by positivity
  rw [Real.norm_of_nonneg h1.le, inv_mul_le_iff₀ h1, mul_one_div, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (ε - ‖z‖), norm_nonneg z]

lemma lreg_gE_hasFDerivAt {ε : ℝ} (hε : 0 < ε) (y x : Euc d) :
    HasFDerivAt (fun x : Euc d => lreg_gE ε (x - y)) (innerSL ℝ (lreg_kE ε (x - y))) x := by
  have h2 : HasFDerivAt (fun x : Euc d => x - y) (ContinuousLinearMap.id ℝ (Euc d)) x :=
    (hasFDerivAt_id x).sub_const y
  have h3 := (h2.norm_sq).const_add (ε ^ 2)
  have h4 := h3.log (by positivity)
  have h5 := h4.const_mul (-(1 / 2 : ℝ))
  refine h5.congr_fderiv ?_
  ext w
  simp [lreg_kE]
  ring

lemma lreg_g_sub_gE_le {ε : ℝ} (hε : 0 < ε) {z : Euc d} (hz : z ≠ 0) :
    ‖(-Real.log ‖z‖) - lreg_gE ε z‖ ≤ ε * ‖z‖ ^ (-1 : ℝ) := by
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz
  set r := ‖z‖ with hrdef
  have ht : 0 < ε / r := by positivity
  have h1 : (-Real.log r) - lreg_gE ε z = (1 / 2) * Real.log (1 + (ε / r) ^ 2) := by
    unfold lreg_gE
    have : Real.log (ε ^ 2 + r ^ 2) = Real.log (r ^ 2) + Real.log (1 + (ε / r) ^ 2) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      field_simp
      ring
    rw [this, Real.log_pow]
    push_cast
    ring
  have h2 : Real.log (1 + (ε / r) ^ 2) ≤ 2 * (ε / r) := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    calc 1 + (ε / r) ^ 2 ≤ (ε / r + 1) ^ 2 := by nlinarith
      _ ≤ (Real.exp (ε / r)) ^ 2 := by
          gcongr
          exact Real.add_one_le_exp _
      _ = Real.exp (2 * (ε / r)) := by
          rw [← Real.exp_nat_mul]; norm_num
  have h3 : 0 ≤ Real.log (1 + (ε / r) ^ 2) := Real.log_nonneg (by nlinarith)
  rw [h1, Real.norm_of_nonneg (by positivity), Real.rpow_neg_one]
  calc 1 / 2 * Real.log (1 + (ε / r) ^ 2) ≤ 1 / 2 * (2 * (ε / r)) := by gcongr
    _ = ε * r⁻¹ := by ring

lemma lreg_kE_sub_kap_le {ε : ℝ} (hε : 0 < ε) {z : Euc d} (hz : z ≠ 0) :
    ‖lreg_kE ε z - lreg_kap z‖ ≤ Real.sqrt ε * ‖z‖ ^ (-(3 / 2) : ℝ) := by
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz
  set r := ‖z‖ with hrdef
  have hs : 0 < ε / r := by positivity
  have h1 : lreg_kE ε z - lreg_kap z = (ε ^ 2 / (r ^ 2 * (ε ^ 2 + r ^ 2))) • z := by
    unfold lreg_kE lreg_kap
    rw [← hrdef]
    have hc : ε ^ 2 / (r ^ 2 * (ε ^ 2 + r ^ 2)) = (r ^ 2)⁻¹ - (ε ^ 2 + r ^ 2)⁻¹ := by
      field_simp
      ring
    rw [hc]
    module
  have hr32 : r ^ (-(3 / 2) : ℝ) = r⁻¹ * (Real.sqrt r)⁻¹ := by
    rw [Real.rpow_neg hr.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hr,
      Real.rpow_one, ← Real.sqrt_eq_rpow, mul_inv]
  have key : ε ^ 2 / (r ^ 2 * (ε ^ 2 + r ^ 2)) * r = r⁻¹ * ((ε / r) ^ 2 / (1 + (ε / r) ^ 2)) := by
    field_simp
    ring
  have hq : (ε / r) ^ 2 / (1 + (ε / r) ^ 2) ≤ Real.sqrt (ε / r) := by
    set s := ε / r with hsdef
    by_cases h : s ≤ 1
    · calc s ^ 2 / (1 + s ^ 2) ≤ s ^ 2 := by
            rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg s]
        _ ≤ s := by nlinarith
        _ ≤ Real.sqrt s := Real.le_sqrt_of_sq_le (by nlinarith)
    · rw [not_le] at h
      calc s ^ 2 / (1 + s ^ 2) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
        _ ≤ Real.sqrt s := by rw [Real.one_le_sqrt]; exact h.le
  have hc0 : 0 ≤ ε ^ 2 / (r ^ 2 * (ε ^ 2 + r ^ 2)) := by positivity
  rw [h1, norm_smul, Real.norm_of_nonneg hc0, ← hrdef, key, hr32]
  have hq' : (ε / r) ^ 2 / (1 + (ε / r) ^ 2) ≤ Real.sqrt ε / Real.sqrt r := by
    rw [← Real.sqrt_div hε.le r]; exact hq
  calc r⁻¹ * ((ε / r) ^ 2 / (1 + (ε / r) ^ 2)) ≤ r⁻¹ * (Real.sqrt ε / Real.sqrt r) :=
        mul_le_mul_of_nonneg_left hq' (inv_nonneg.2 hr.le)
    _ = Real.sqrt ε * (r⁻¹ * (Real.sqrt r)⁻¹) := by ring

lemma lreg_K_dom_y (hd : 1 ≤ d) {σ : ℝ} (hσ : σ < d) (hσ0 : 0 ≤ σ) {C : ℝ} (hC : 0 ≤ C)
    {h : Euc d → ℝ} (hm : AEStronglyMeasurable h volume)
    (hb : ∀ y, ‖h y‖ ≤ C * lreg_phi d y) (x : Euc d) :
    Integrable (fun y : Euc d => ‖x - y‖ ^ (-σ) * ‖h y‖) ∧
      ∫ y, ‖x - y‖ ^ (-σ) * ‖h y‖ ≤ C * lreg_A d σ := by
  obtain ⟨hI, hJ⟩ := lreg_K_dom hd hσ hσ0 hC hm hb x
  refine ⟨?_, ?_⟩
  · have := hI.comp_sub_left x
    simpa using this
  · have := integral_sub_left_eq_self (fun z : Euc d => ‖z‖ ^ (-σ) * ‖h (x - z)‖) volume x
    simp only [sub_sub_cancel] at this
    rw [this]; exact hJ

lemma lreg_gE_abs_le {ε : ℝ} (hε : 0 < ε) (z : Euc d) :
    |lreg_gE ε z| ≤ |Real.log ε| + (ε ^ 2 + ‖z‖ ^ 2) / 2 := by
  unfold lreg_gE
  have hA : 0 < ε ^ 2 + ‖z‖ ^ 2 := by positivity
  have h1 : 2 * Real.log ε ≤ Real.log (ε ^ 2 + ‖z‖ ^ 2) := by
    rw [← Real.log_rpow hε]
    · apply Real.log_le_log (by positivity)
      have : ε ^ (2 : ℝ) = ε ^ 2 := by norm_cast
      rw [this]; nlinarith [sq_nonneg ‖z‖]
  have h2 : Real.log (ε ^ 2 + ‖z‖ ^ 2) ≤ ε ^ 2 + ‖z‖ ^ 2 := by
    have := Real.log_le_sub_one_of_pos hA
    linarith
  have h3 : 0 ≤ Real.log (ε ^ 2 + ‖z‖ ^ 2) ∨ Real.log (ε ^ 2 + ‖z‖ ^ 2) < 0 := le_or_gt _ _
  rw [abs_le]
  have := neg_abs_le (Real.log ε)
  have := le_abs_self (Real.log ε)
  have := abs_nonneg (Real.log ε)
  constructor <;> nlinarith

lemma lreg_gE_continuous {ε : ℝ} (hε : 0 < ε) : Continuous (lreg_gE ε : Euc d → ℝ) := by
  unfold lreg_gE
  exact continuous_const.mul
    ((continuous_const.add (continuous_norm.pow 2)).log fun z =>
      (by positivity : (0 : ℝ) < ε ^ 2 + ‖z‖ ^ 2).ne')

lemma lreg_norm_integrable {F : Euc d → ℝ} (hm : AEStronglyMeasurable F volume) (hF : lreg_RDec F)
    (j : ℕ) : Integrable (fun y : Euc d => (1 + ‖y‖) ^ j * ‖F y‖) := by
  obtain ⟨C, hC, h⟩ := lreg_bound_of_rdec hF j
  refine lreg_integrable_of_bound (C := C) ?_ (fun y => ?_)
  · exact ((measurable_const.add measurable_norm).pow_const j).aestronglyMeasurable.mul hm.norm
  · rw [Real.norm_of_nonneg (by positivity)]; exact h y

lemma lreg_gE_F_integrable {ε : ℝ} (hε : 0 < ε) {F : Euc d → ℝ} (hm : AEStronglyMeasurable F volume)
    (hF : lreg_RDec F) (x : Euc d) : Integrable (fun y => lreg_gE ε (x - y) * F y) := by
  have hi0 := lreg_norm_integrable hm hF 0
  have hi2 := lreg_norm_integrable hm hF 2
  simp only [pow_zero, one_mul] at hi0
  refine ((hi0.const_mul (|Real.log ε| + ε ^ 2 / 2 + ‖x‖ ^ 2)).add hi2).mono' ?_ (ae_of_all _ fun y => ?_)
  · exact ((lreg_gE_continuous hε).comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul hm
  · rw [norm_mul]
    have h1 := lreg_gE_abs_le hε (x - y)
    have h2 : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
      have := norm_sub_le x y
      nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg (x - y), sq_nonneg (‖x‖ - ‖y‖)]
    have h3 : ‖lreg_gE ε (x - y)‖ ≤ |Real.log ε| + ε ^ 2 / 2 + ‖x‖ ^ 2 + (1 + ‖y‖) ^ 2 := by
      rw [Real.norm_eq_abs]
      nlinarith [norm_nonneg y]
    calc ‖lreg_gE ε (x - y)‖ * ‖F y‖
        ≤ (|Real.log ε| + ε ^ 2 / 2 + ‖x‖ ^ 2 + (1 + ‖y‖) ^ 2) * ‖F y‖ :=
          mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
      _ = _ := by simp only [Pi.add_apply]; ring

lemma lreg_kE_F_integrable {ε : ℝ} (hε : 0 < ε) {F : Euc d → ℝ} (hm : AEStronglyMeasurable F volume)
    (hF : lreg_RDec F) (x : Euc d) : Integrable (fun y => F y • lreg_kE ε (x - y)) := by
  have hi0 := lreg_norm_integrable hm hF 0
  simp only [pow_zero, one_mul] at hi0
  refine (hi0.mul_const (1 / (2 * ε))).mono' ?_ (ae_of_all _ fun y => ?_)
  · exact hm.smul ((lreg_kE_continuous hε).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (lreg_kE_le hε _) (norm_nonneg _)

lemma lreg_UE_hasFDerivAt {ε : ℝ} (hε : 0 < ε) {F : Euc d → ℝ} (hm : AEStronglyMeasurable F volume)
    (hF : lreg_RDec F) (x₀ : Euc d) :
    HasFDerivAt (fun x : Euc d => ∫ y, lreg_gE ε (x - y) * F y)
      (innerSL ℝ (∫ y, F y • lreg_kE ε (x₀ - y))) x₀ := by
  have hi0 := lreg_norm_integrable hm hF 0
  simp only [pow_zero, one_mul] at hi0
  have hint := lreg_kE_F_integrable hε hm hF x₀
  have hcomm : (∫ y, F y • innerSL ℝ (lreg_kE ε (x₀ - y))) =
      innerSL ℝ (∫ y, F y • lreg_kE ε (x₀ - y)) := by
    have := ContinuousLinearMap.integral_comp_comm (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) hint
    simpa [map_smul] using this
  rw [← hcomm]
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := Set.univ)
    (F := fun x y => lreg_gE ε (x - y) * F y)
    (F' := fun x y => F y • innerSL ℝ (lreg_kE ε (x - y)))
    (bound := fun y => ‖F y‖ * (1 / (2 * ε))) Filter.univ_mem ?_ ?_ ?_ ?_ (hi0.mul_const _) ?_
  · exact Eventually.of_forall fun x =>
      ((lreg_gE_continuous hε).comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul hm
  · exact lreg_gE_F_integrable hε hm hF x₀
  · exact hm.smul ((innerSL ℝ).continuous.comp
      ((lreg_kE_continuous hε).comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · refine ae_of_all _ fun y x _ => ?_
    rw [norm_smul, innerSL_apply_norm]
    exact mul_le_mul_of_nonneg_left (lreg_kE_le hε _) (norm_nonneg _)
  · exact ae_of_all _ fun y x _ => (lreg_gE_hasFDerivAt hε y x).mul_const (F y)

lemma lreg_ae_ne (hd : 1 ≤ d) (x : Euc d) : ∀ᵐ y : Euc d, x - y ≠ 0 := by
  have : NeZero d := ⟨by omega⟩
  have h := (Set.countable_singleton x).ae_notMem (volume : Measure (Euc d))
  filter_upwards [h] with y hy
  intro h0
  exact hy (by simp [sub_eq_zero.1 h0])

/-- `∫ -log‖x - y‖ F y dy`. -/
def lreg_U (F : Euc d → ℝ) (x : Euc d) : ℝ := ∫ y, -Real.log ‖x - y‖ * F y

/-- `∫ F y κ(x - y) dy`. -/
def lreg_W (F : Euc d → ℝ) (x : Euc d) : Euc d := ∫ y, F y • lreg_kap (x - y)

lemma lreg_measurable_neglog (x : Euc d) :
    Measurable (fun y : Euc d => -Real.log ‖x - y‖) :=
  (Real.measurable_log.comp (measurable_norm.comp (measurable_const.sub measurable_id))).neg

lemma lreg_U_est (hd2 : 2 ≤ d) {F : Euc d → ℝ} (hm : AEStronglyMeasurable F volume) (hF : lreg_RDec F)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ y, ‖F y‖ ≤ C * lreg_phi d y) {ε : ℝ} (hε : 0 < ε) (x : Euc d) :
    Integrable (fun y => -Real.log ‖x - y‖ * F y) ∧
      ‖lreg_U F x - ∫ y, lreg_gE ε (x - y) * F y‖ ≤ ε * (C * lreg_A d 1) := by
  have hd1 : 1 ≤ d := by omega
  have hσ : (1 : ℝ) < d := by exact_mod_cast hd2
  obtain ⟨hK, hKi⟩ := lreg_K_dom_y hd1 hσ zero_le_one hC hm hb x
  have hbd : ∀ᵐ y : Euc d, ‖(-Real.log ‖x - y‖ - lreg_gE ε (x - y)) * F y‖ ≤
      ε * (‖x - y‖ ^ (-1 : ℝ) * ‖F y‖) := by
    filter_upwards [lreg_ae_ne hd1 x] with y hy
    rw [norm_mul]
    calc _ ≤ (ε * ‖x - y‖ ^ (-1 : ℝ)) * ‖F y‖ :=
          mul_le_mul_of_nonneg_right (lreg_g_sub_gE_le hε hy) (norm_nonneg _)
      _ = _ := by ring
  have hDm : AEStronglyMeasurable (fun y => (-Real.log ‖x - y‖ - lreg_gE ε (x - y)) * F y) volume :=
    ((lreg_measurable_neglog x).sub
      ((lreg_gE_continuous hε).measurable.comp (measurable_const.sub measurable_id))).aestronglyMeasurable.mul hm
  have hD : Integrable (fun y => (-Real.log ‖x - y‖ - lreg_gE ε (x - y)) * F y) :=
    (hK.const_mul ε).mono' hDm hbd
  have hE := lreg_gE_F_integrable hε hm hF x
  have hU : Integrable (fun y => -Real.log ‖x - y‖ * F y) := by
    refine (hE.add hD).congr (ae_of_all _ fun y => ?_)
    simp only [Pi.add_apply]; ring
  refine ⟨hU, ?_⟩
  have : lreg_U F x - ∫ y, lreg_gE ε (x - y) * F y =
      ∫ y, (-Real.log ‖x - y‖ - lreg_gE ε (x - y)) * F y := by
    unfold lreg_U
    rw [← integral_sub hU hE]
    congr 1; ext y; ring
  rw [this]
  calc _ ≤ ∫ y, ε * (‖x - y‖ ^ (-1 : ℝ) * ‖F y‖) :=
        norm_integral_le_of_norm_le (hK.const_mul ε) hbd
    _ = ε * ∫ y, ‖x - y‖ ^ (-1 : ℝ) * ‖F y‖ := integral_const_mul _ _
    _ ≤ ε * (C * lreg_A d 1) := by gcongr

lemma lreg_W_est (hd2 : 2 ≤ d) {F : Euc d → ℝ} (hm : AEStronglyMeasurable F volume)
    (hF : lreg_RDec F) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ y, ‖F y‖ ≤ C * lreg_phi d y) {ε : ℝ}
    (hε : 0 < ε) (x : Euc d) :
    Integrable (fun y => F y • lreg_kap (x - y)) ∧ ‖lreg_W F x‖ ≤ C * lreg_A d 1 ∧
      ‖lreg_W F x - ∫ y, F y • lreg_kE ε (x - y)‖ ≤ Real.sqrt ε * (C * lreg_A d (3 / 2)) := by
  have hd1 : 1 ≤ d := by omega
  have hσ : (1 : ℝ) < d := by exact_mod_cast hd2
  have hσ' : (3 / 2 : ℝ) < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd2
    linarith
  obtain ⟨hK, hKi⟩ := lreg_K_dom_y hd1 hσ zero_le_one hC hm hb x
  obtain ⟨hK', hKi'⟩ := lreg_K_dom_y hd1 hσ' (by norm_num) hC hm hb x
  have hmeas : AEStronglyMeasurable (fun y => F y • lreg_kap (x - y)) volume :=
    hm.smul (lreg_kap_measurable.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  have hbd1 : ∀ y : Euc d, ‖F y • lreg_kap (x - y)‖ ≤ ‖x - y‖ ^ (-1 : ℝ) * ‖F y‖ := fun y => by
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (lreg_kap_le _) (norm_nonneg _)
  have hI : Integrable (fun y => F y • lreg_kap (x - y)) :=
    hK.mono' hmeas (ae_of_all _ hbd1)
  refine ⟨hI, ?_, ?_⟩
  · calc ‖lreg_W F x‖ ≤ ∫ y, ‖x - y‖ ^ (-1 : ℝ) * ‖F y‖ :=
          norm_integral_le_of_norm_le hK (ae_of_all _ hbd1)
      _ ≤ C * lreg_A d 1 := by simpa using hKi
  · have hE := lreg_kE_F_integrable hε hm hF x
    have hbd : ∀ᵐ y : Euc d, ‖F y • lreg_kap (x - y) - F y • lreg_kE ε (x - y)‖ ≤
        Real.sqrt ε * (‖x - y‖ ^ (-(3 / 2) : ℝ) * ‖F y‖) := by
      filter_upwards [lreg_ae_ne hd1 x] with y hy
      rw [← smul_sub, norm_smul, norm_sub_rev]
      calc ‖F y‖ * ‖lreg_kE ε (x - y) - lreg_kap (x - y)‖
          ≤ ‖F y‖ * (Real.sqrt ε * ‖x - y‖ ^ (-(3 / 2) : ℝ)) :=
            mul_le_mul_of_nonneg_left (lreg_kE_sub_kap_le hε hy) (norm_nonneg _)
        _ = _ := by ring
    have : lreg_W F x - ∫ y, F y • lreg_kE ε (x - y) =
        ∫ y, (F y • lreg_kap (x - y) - F y • lreg_kE ε (x - y)) := by
      unfold lreg_W
      rw [integral_sub hI hE]
    rw [this]
    calc _ ≤ ∫ y, Real.sqrt ε * (‖x - y‖ ^ (-(3 / 2) : ℝ) * ‖F y‖) :=
          norm_integral_le_of_norm_le (hK'.const_mul _) hbd
      _ = Real.sqrt ε * ∫ y, ‖x - y‖ ^ (-(3 / 2) : ℝ) * ‖F y‖ := integral_const_mul _ _
      _ ≤ Real.sqrt ε * (C * lreg_A d (3 / 2)) := by gcongr

lemma lreg_tu {X V : Type*} [NormedAddCommGroup V] {a : ℕ → X → V} {b : X → V} {c : ℕ → ℝ}
    (hc : Tendsto c atTop (𝓝 0)) (h : ∀ n x, ‖a n x - b x‖ ≤ c n) :
    TendstoUniformly a b atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro δ hδ
  filter_upwards [hc.eventually (gt_mem_nhds hδ)] with n hn x
  rw [dist_eq_norm, norm_sub_rev]
  exact lt_of_le_of_lt (h n x) hn

/-- **Potential of a rapidly decaying measurable density**: for `d ≥ 2` the logarithmic potential
`U = ∫ -log‖x - y‖ F y dy` is `C¹` with `∇U = ∫ F y κ(x - y) dy` (continuous, and bounded by
`C A` if `‖F‖ ≤ C φ`). -/
theorem lreg_potential (hd2 : 2 ≤ d) {F : Euc d → ℝ} (hm : AEStronglyMeasurable F volume)
    (hF : lreg_RDec F) :
    Continuous (lreg_W F) ∧ (∀ x, HasFDerivAt (lreg_U F) (innerSL ℝ (lreg_W F x)) x) ∧
      ∀ C : ℝ, 0 ≤ C → (∀ y, ‖F y‖ ≤ C * lreg_phi d y) → ∀ x, ‖lreg_W F x‖ ≤ C * lreg_A d 1 := by
  obtain ⟨C0, hC0, h0⟩ := lreg_bound_of_rdec hF 0
  have hb : ∀ y, ‖F y‖ ≤ C0 * lreg_phi d y := fun y => by simpa using h0 y
  have hi0 := lreg_norm_integrable hm hF 0
  simp only [pow_zero, one_mul] at hi0
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hεdef
  have hεpos : ∀ n, 0 < ε n := fun n => by simp only [hεdef]; positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hc1 : Tendsto (fun n => ε n * (C0 * lreg_A d 1)) atTop (𝓝 0) := by
    simpa using hε0.mul_const (C0 * lreg_A d 1)
  have hc2 : Tendsto (fun n => Real.sqrt (ε n) * (C0 * lreg_A d (3 / 2))) atTop (𝓝 0) := by
    have := ((Real.continuous_sqrt.tendsto 0).comp hε0).mul_const (C0 * lreg_A d (3 / 2))
    simpa using this
  have hTUW : TendstoUniformly (fun n x => ∫ y, F y • lreg_kE (ε n) (x - y)) (lreg_W F) atTop :=
    lreg_tu hc2 fun n x => by
      rw [norm_sub_rev]; exact (lreg_W_est hd2 hm hF hC0 hb (hεpos n) x).2.2
  have hcontE : ∀ n, Continuous (fun x => ∫ y, F y • lreg_kE (ε n) (x - y)) := by
    intro n
    refine continuous_of_dominated (bound := fun y => ‖F y‖ * (1 / (2 * ε n))) (fun x => ?_)
      (fun x => ae_of_all _ fun y => ?_) (hi0.mul_const _) (ae_of_all _ fun y => ?_)
    · exact hm.smul ((lreg_kE_continuous (hεpos n)).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    · rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (lreg_kE_le (hεpos n) _) (norm_nonneg _)
    · exact (continuous_const : Continuous fun _ : Euc d => F y).smul ((lreg_kE_continuous (hεpos n)).comp
        ((continuous_id (X := Euc d)).sub continuous_const))
  refine ⟨hTUW.continuous (Eventually.of_forall hcontE).frequently, fun x => ?_, fun C hC hCb x =>
    (lreg_W_est hd2 hm hF hC hCb (hεpos 0) x).2.1⟩
  refine hasFDerivAt_of_tendstoUniformly (l := atTop)
    (f := fun n x => ∫ y, lreg_gE (ε n) (x - y) * F y)
    (f' := fun n x => innerSL ℝ (∫ y, F y • lreg_kE (ε n) (x - y)))
    (g' := fun x => innerSL ℝ (lreg_W F x)) ?_ (fun n x => lreg_UE_hasFDerivAt (hεpos n) hm hF x) ?_ x
  · refine lreg_tu hc2 fun n x => ?_
    rw [← map_sub, innerSL_apply_norm, norm_sub_rev]
    exact (lreg_W_est hd2 hm hF hC0 hb (hεpos n) x).2.2
  · intro x
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hc1)
    rw [norm_sub_rev]
    exact (lreg_U_est hd2 hm hF hC0 hb (hεpos n) x).2

end HRS.MS.LogReg

end
