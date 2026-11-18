import HRS.MH.ScreenedDefs
import HRS.Whole.Q34Aux1

/-!
# Packet S5a, helper file 1: the kernel integral `∫ |h|^{-d-2σ} 4 sin²(π⟨h,ξ⟩) dh = c |ξ|^{2σ}`
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

/-- `4 sin²(π t)` as an extended nonnegative real. -/
def s5aG (t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (4 * Real.sin (Real.pi * t) ^ 2)

/-- The Gagliardo weight `|h|^{-d-2σ}` as an extended nonnegative real. -/
def s5aW (d : ℕ) (σ : ℝ) (h : Euc d) : ℝ≥0∞ := ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ)))

/-- The kernel integral `∫ |h|^{-d-2σ} 4 sin²(π⟨h,ξ⟩) dh`. -/
def s5aK (d : ℕ) (σ : ℝ) (ξ : Euc d) : ℝ≥0∞ :=
  ∫⁻ h : Euc d, s5aW d σ h * s5aG (inner ℝ h ξ)

theorem s5a_lintegral_smul {r : ℝ} (hr : 0 < r) (φ : Euc d → ℝ≥0∞) :
    ∫⁻ h : Euc d, φ (r • h) = ENNReal.ofReal ((r ^ d)⁻¹) * ∫⁻ h, φ h := by
  have h1 : ∫⁻ h : Euc d, φ (r • h) = ∫⁻ h, φ h ∂(Measure.map (r • ·) (volume : Measure (Euc d))) := by
    exact (lintegral_map_equiv (μ := (volume : Measure (Euc d))) φ
      (Homeomorph.smulOfNeZero r hr.ne').toMeasurableEquiv).symm
  rw [h1, Measure.map_addHaar_smul volume hr.ne', lintegral_smul_measure]
  simp [abs_of_pos (inv_pos.2 (pow_pos hr d))]

theorem s5aW_smul {r : ℝ} (hr : 0 < r) (σ : ℝ) (h : Euc d) :
    s5aW d σ (r • h) = ENNReal.ofReal (r ^ (-((d : ℝ) + 2 * σ))) * s5aW d σ h := by
  unfold s5aW
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, Real.mul_rpow hr.le (norm_nonneg _),
    ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)]

theorem s5aW_isometry (T : Euc d ≃ₗᵢ[ℝ] Euc d) (σ : ℝ) (h : Euc d) :
    s5aW d σ (T h) = s5aW d σ h := by
  unfold s5aW; rw [T.norm_map]

theorem s5a_lintegral_isometry (T : Euc d ≃ₗᵢ[ℝ] Euc d) (φ : Euc d → ℝ≥0∞) :
    ∫⁻ h : Euc d, φ (T h) = ∫⁻ h, φ h :=
  T.measurePreserving.lintegral_comp_emb T.toHomeomorph.measurableEmbedding φ

/-- homogeneity and rotation invariance of the kernel integral -/
theorem s5aK_eq (σ : ℝ) (hσ : 0 < σ) (e ξ : Euc d) (he : ‖e‖ = 1) (hξ : ξ ≠ 0) :
    s5aK d σ ξ = ENNReal.ofReal (‖ξ‖ ^ (2 * σ)) * s5aK d σ e := by
  have hr : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  set r := ‖ξ‖ with hrdef
  set v : Euc d := r⁻¹ • ξ with hv
  have hvn : ‖v‖ = ‖e‖ := by
    rw [hv, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr), he, inv_mul_cancel₀ hr.ne']
  -- the reflection `T` with `T e = v`
  set T : Euc d ≃ₗᵢ[ℝ] Euc d := (ℝ ∙ (e - v))ᗮ.reflection with hT
  have hTe : T e = v := by
    have := Submodule.reflection_sub (v := e) (w := v) hvn.symm
    simpa [hT] using this
  have hξv : ξ = r • v := by rw [hv, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hinner : ∀ h' : Euc d, inner ℝ (T h') ξ = r * inner ℝ h' e := by
    intro h'
    rw [hξv, inner_smul_right, ← hTe, LinearIsometryEquiv.inner_map_map]
  unfold s5aK
  rw [← s5a_lintegral_isometry T]
  have h2 : ∀ h' : Euc d, s5aW d σ (T h') * s5aG (inner ℝ (T h') ξ) =
      ENNReal.ofReal (r ^ ((d : ℝ) + 2 * σ)) *
        (s5aW d σ (r • h') * s5aG (inner ℝ (r • h') e)) := by
    intro h'
    rw [s5aW_isometry, hinner, s5aW_smul hr, inner_smul_left]
    simp only [conj_trivial]
    have h3 : ENNReal.ofReal (r ^ ((d : ℝ) + 2 * σ)) * ENNReal.ofReal (r ^ (-((d : ℝ) + 2 * σ))) = 1 := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _), Real.rpow_neg hr.le,
        mul_inv_cancel₀ (Real.rpow_pos_of_pos hr _).ne', ENNReal.ofReal_one]
    rw [← mul_assoc, ← mul_assoc, h3, one_mul]
  simp_rw [h2]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, s5a_lintegral_smul hr (fun k => s5aW d σ k * s5aG (inner ℝ k e))]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)]
  congr 2
  rw [Real.rpow_add hr, Real.rpow_natCast]
  field_simp


/-- The first basis vector. -/
def s5aE (hd : 1 ≤ d) : Euc d := EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ)

theorem s5aE_norm (hd : 1 ≤ d) : ‖s5aE hd‖ = 1 := by simp [s5aE]

theorem s5a_inner_E (hd : 1 ≤ d) (h : Euc d) : inner ℝ h (s5aE hd) = h ⟨0, hd⟩ := by
  simp [s5aE, EuclideanSpace.inner_single_right]

theorem measurable_s5aG : Measurable s5aG := by
  unfold s5aG
  exact ENNReal.measurable_ofReal.comp (by fun_prop)

theorem measurable_s5aW (d : ℕ) (σ : ℝ) : Measurable (s5aW d σ) := by
  unfold s5aW
  exact ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)

theorem s5aK_pos (hd : 1 ≤ d) (σ : ℝ) : 0 < s5aK d σ (s5aE hd) := by
  unfold s5aK
  have hm : Measurable fun h : Euc d => s5aW d σ h * s5aG (inner ℝ h (s5aE hd)) :=
    (measurable_s5aW d σ).mul (measurable_s5aG.comp (by simp_rw [s5a_inner_E]; fun_prop))
  rw [lintegral_pos_iff_support hm]
  set U : Set (Euc d) := {h | 0 < h ⟨0, hd⟩ ∧ h ⟨0, hd⟩ < 1} with hU
  have hUo : IsOpen U := by
    have hc : Continuous fun h : Euc d => h ⟨0, hd⟩ := (EuclideanSpace.proj (⟨0, hd⟩ : Fin d)).continuous
    exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
  have hne : U.Nonempty := ⟨(1 / 2 : ℝ) • s5aE hd, by simp [hU, s5aE]; norm_num⟩
  refine lt_of_lt_of_le (hUo.measure_pos volume hne) (measure_mono fun h hh => ?_)
  obtain ⟨h1, h2⟩ := hh
  have hh0 : h ≠ 0 := by
    intro h0; rw [h0] at h1; simp at h1
  have hn : 0 < ‖h‖ := norm_pos_iff.2 hh0
  have hs : 0 < Real.sin (Real.pi * h ⟨0, hd⟩) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  simp only [Function.mem_support, s5a_inner_E, s5aW, s5aG, ne_eq, mul_eq_zero, ENNReal.ofReal_eq_zero,
    not_or, not_le]
  exact ⟨Real.rpow_pos_of_pos hn _, by positivity⟩


theorem s5aK_lt_top (hd : 1 ≤ d) {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) : s5aK d σ (s5aE hd) < ⊤ := by
  unfold s5aK
  have hA : (d : ℝ) + 2 * σ ≠ 0 := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  rw [← lintegral_add_compl _ (measurableSet_ball : MeasurableSet (ball (0 : Euc d) 1))]
  refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_ball (g := fun h : Euc d =>
      ENNReal.ofReal (4 * Real.pi ^ 2) * ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ - 2)))) ?_) ?_
    · intro h _
      simp only [s5aW, s5aG, s5a_inner_E]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _), ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      by_cases hh : h = 0
      · subst hh
        rw [norm_zero, Real.zero_rpow (neg_ne_zero.2 hA)]
        simp only [zero_mul]
        exact mul_nonneg (by positivity) (Real.rpow_nonneg le_rfl _)
      · have hn : 0 < ‖h‖ := norm_pos_iff.2 hh
        have hsin : Real.sin (Real.pi * h ⟨0, hd⟩) ^ 2 ≤ (Real.pi * ‖h‖) ^ 2 := by
          have h1 : |Real.sin (Real.pi * h ⟨0, hd⟩)| ≤ |Real.pi * h ⟨0, hd⟩| := Real.abs_sin_le_abs
          have h2 : |Real.pi * h ⟨0, hd⟩| ≤ Real.pi * ‖h‖ := by
            rw [abs_mul, abs_of_pos Real.pi_pos]
            exact mul_le_mul_of_nonneg_left (by have := abs_real_inner_le_norm h (s5aE hd); rwa [s5a_inner_E, s5aE_norm, mul_one] at this) Real.pi_pos.le
          calc _ = |Real.sin (Real.pi * h ⟨0, hd⟩)| ^ 2 := (sq_abs _).symm
            _ ≤ (Real.pi * ‖h‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (h1.trans h2) 2
        have : ‖h‖ ^ (-((d : ℝ) + 2 * σ - 2)) = ‖h‖ ^ (-((d : ℝ) + 2 * σ)) * ‖h‖ ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hn]
          norm_num
          ring_nf
        rw [this]
        have := Real.rpow_nonneg hn.le (-((d : ℝ) + 2 * σ))
        nlinarith [mul_le_mul_of_nonneg_left hsin this]
    · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, Q34.lintegral_ball_rpow hd one_pos
        (by linarith)]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  · have hset : (ball (0 : Euc d) 1)ᶜ = {z : Euc d | 1 ≤ ‖z‖} := by
      ext z; simp
    rw [hset]
    refine lt_of_le_of_lt (setLIntegral_mono' ?_ (g := fun h : Euc d =>
      ENNReal.ofReal 4 * ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ)))) ?_) ?_
    · exact measurableSet_le measurable_const measurable_norm
    · intro h _
      simp only [s5aW, s5aG]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _), ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := Real.rpow_nonneg (norm_nonneg h) (-((d : ℝ) + 2 * σ))
      nlinarith [Real.sin_sq_le_one (Real.pi * inner ℝ h (s5aE hd))]
    · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, Q34.lintegral_compl_rpow hd one_pos
        (by have : (0 : ℝ) < σ := h0; linarith)]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

end HRS.MH.Screened
