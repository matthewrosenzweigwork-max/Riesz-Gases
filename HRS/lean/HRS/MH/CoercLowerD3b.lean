import HRS.MH.CoercLowerDefs
import Mathlib

/-!
# CoercLower packet P27 (`phiLog_integral`): integrability and integral of `φ_T` on `ℝ^d`.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace HRS.MH.CoercLower

variable {d N : ℕ}

/-- Auxiliary: the Gaussian `exp(-t‖x‖²)` is integrable on `ℝ^d` for `t > 0`. -/
private lemma cld3b_integrable_gauss (d : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : Euc d => Real.exp (-t * ‖x‖ ^ 2)) (volume : Measure (Euc d)) := by
  have := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Euc d) (b := (t : ℂ))
    (by simpa using ht) 0 0).norm
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  simp
  left
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-- Auxiliary: the integral of the Gaussian. -/
private lemma cld3b_integral_gauss (d : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ x : Euc d, Real.exp (-t * ‖x‖ ^ 2) = (Real.pi / t) ^ ((d : ℝ) / 2) := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm ht, finrank_euclideanSpace_fin]

/-- Auxiliary: the kernel `x ↦ e^{-t‖x‖²}/t` on `(T, ∞)` is integrable for each `x ≠ 0`. -/
private lemma cld3b_integrableOn_kernel {T : ℝ} (hT : 0 < T) (x : Euc d) (hx : x ≠ 0) :
    IntegrableOn (fun t : ℝ => Real.exp (-t * ‖x‖ ^ 2) / t) (Ioi T) := by
  have hr : 0 < ‖x‖ ^ 2 := by positivity
  have hb : IntegrableOn (fun t : ℝ => Real.exp (-(‖x‖ ^ 2) * t)) (Ioi T) :=
    exp_neg_integrableOn_Ioi T hr
  refine Integrable.mono' (g := fun t : ℝ => Real.exp (-(‖x‖ ^ 2) * t) / T) (hb.div_const T) ?_ ?_
  · exact (by fun_prop : Measurable fun t : ℝ => Real.exp (-t * ‖x‖ ^ 2) / t).aestronglyMeasurable
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
    have htT : T < t := ht
    have ht0 : 0 < t := lt_trans hT htT
    have he : 0 < Real.exp (-t * ‖x‖ ^ 2) := Real.exp_pos _
    rw [Real.norm_eq_abs, abs_of_pos (div_pos he ht0)]
    have h1 : -t * ‖x‖ ^ 2 = -(‖x‖ ^ 2) * t := by ring
    rw [h1]
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le hT htT.le

/-- Auxiliary: the integral of `φ_T` is the Tonelli lintegral of the kernel. -/
private lemma cld3b_lintegral_phiLog (hd : 1 ≤ d) {T : ℝ} (hT : 0 < T) :
    ∫⁻ x : Euc d, ENNReal.ofReal (phiLog T x) =
      ENNReal.ofReal (Real.pi ^ ((d : ℝ) / 2) / d * T ^ (-((d : ℝ) / 2))) := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    have : 0 < d := by omega
    exact_mod_cast this
  have hae0 : ∀ᵐ x : Euc d ∂volume, x ≠ 0 := by
    have hnt : Nontrivial (Euc d) := by
      obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
      infer_instance
    have h0 : volume ({0} : Set (Euc d)) = 0 := measure_singleton 0
    rw [ae_iff]
    simpa using h0
  -- pointwise identity off `0`
  have hx_ofReal : ∀ x : Euc d, x ≠ 0 →
      ENNReal.ofReal (phiLog T x) =
        ENNReal.ofReal (1 / 2) * ∫⁻ t in Ioi T, ENNReal.ofReal (Real.exp (-t * ‖x‖ ^ 2) / t) := by
    intro x hx
    have hnn : 0 ≤ᵐ[volume.restrict (Ioi T)] (fun t : ℝ => Real.exp (-t * ‖x‖ ^ 2) / t) :=
      ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
        div_nonneg (Real.exp_pos _).le (lt_trans hT ht).le
    unfold phiLog
    rw [ENNReal.ofReal_mul (by norm_num),
      ← ofReal_integral_eq_lintegral_ofReal (cld3b_integrableOn_kernel hT x hx) hnn]
  have hsw : ∫⁻ x : Euc d, ENNReal.ofReal (phiLog T x) =
      ENNReal.ofReal (1 / 2) * ∫⁻ t in Ioi T, ∫⁻ x : Euc d, ENNReal.ofReal (Real.exp (-t * ‖x‖ ^ 2) / t) := by
    have hmeasF : AEMeasurable
        (Function.uncurry fun (x : Euc d) (t : ℝ) => ENNReal.ofReal (Real.exp (-t * ‖x‖ ^ 2) / t))
        (volume.prod (volume.restrict (Ioi T))) :=
      (by fun_prop : Measurable fun p : Euc d × ℝ => Real.exp (-p.2 * ‖p.1‖ ^ 2) / p.2).ennreal_ofReal.aemeasurable
    rw [lintegral_congr_ae (hae0.mono fun x hx => hx_ofReal x hx),
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_lintegral_swap hmeasF]
  -- inner Gaussian integral for `t > T`
  have hin : ∀ t ∈ Ioi T, ∫⁻ x : Euc d, ENNReal.ofReal (Real.exp (-t * ‖x‖ ^ 2) / t) =
      ENNReal.ofReal (1 / t * (Real.pi / t) ^ ((d : ℝ) / 2)) := by
    intro t ht
    have ht0 : 0 < t := lt_trans hT ht
    have hpt : ∀ x : Euc d, ENNReal.ofReal (Real.exp (-t * ‖x‖ ^ 2) / t) =
        ENNReal.ofReal (1 / t) * ENNReal.ofReal (Real.exp (-t * ‖x‖ ^ 2)) := by
      intro x
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / t)]
      congr 1
      ring
    simp_rw [hpt]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← ofReal_integral_eq_lintegral_ofReal (cld3b_integrable_gauss d ht0)
        (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le),
      cld3b_integral_gauss d ht0,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / t)]
  -- pointwise power identity
  have hpow : ∀ t ∈ Ioi T, ENNReal.ofReal (1 / t * (Real.pi / t) ^ ((d : ℝ) / 2)) =
      ENNReal.ofReal (Real.pi ^ ((d : ℝ) / 2) * t ^ (-((d : ℝ) / 2) - 1)) := by
    intro t ht
    have ht0 : 0 < t := lt_trans hT ht
    congr 1
    rw [Real.rpow_sub_one ht0.ne', Real.rpow_neg ht0.le, Real.div_rpow Real.pi_pos.le ht0.le]
    ring
  have ha : -((d : ℝ) / 2) - 1 < -1 := by linarith
  have hfin : ∫⁻ t in Ioi T, ENNReal.ofReal (Real.pi ^ ((d : ℝ) / 2) * t ^ (-((d : ℝ) / 2) - 1)) =
      ENNReal.ofReal (∫ t in Ioi T, Real.pi ^ ((d : ℝ) / 2) * t ^ (-((d : ℝ) / 2) - 1)) := by
    rw [ofReal_integral_eq_lintegral_ofReal
      (Integrable.const_mul (integrableOn_Ioi_rpow_of_lt ha hT) _)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
        mul_nonneg (Real.rpow_nonneg Real.pi_pos.le _) (Real.rpow_nonneg (lt_trans hT ht).le _))]
  have hexp : -((d : ℝ) / 2) - 1 + 1 = -((d : ℝ) / 2) := by ring
  have hval : ∫ t in Ioi T, Real.pi ^ ((d : ℝ) / 2) * t ^ (-((d : ℝ) / 2) - 1) =
      Real.pi ^ ((d : ℝ) / 2) * (-(T ^ (-((d : ℝ) / 2))) / (-((d : ℝ) / 2))) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt ha hT, hexp]
  rw [hsw, setLIntegral_congr_fun measurableSet_Ioi (fun t ht => hin t ht),
    setLIntegral_congr_fun measurableSet_Ioi (fun t ht => hpow t ht), hfin, hval,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  field_simp

/-- [P27] `φ_T` is integrable on all of `ℝ^d` (`d ≥ 1`), with explicit integral. -/
theorem phiLog_integral (hd : 1 ≤ d) {T : ℝ} (hT : 0 < T) :
    (∀ x : Euc d, 0 ≤ phiLog T x) ∧ Integrable (phiLog T : Euc d → ℝ) ∧
      ∫ x : Euc d, phiLog T x = Real.pi ^ ((d : ℝ) / 2) / d * T ^ (-((d : ℝ) / 2)) := by
  have hnn : ∀ x : Euc d, 0 ≤ phiLog T x := by
    intro x
    unfold phiLog
    refine mul_nonneg (by norm_num) (setIntegral_nonneg measurableSet_Ioi fun t ht => ?_)
    have ht0 : 0 < t := lt_trans hT ht
    exact div_nonneg (Real.exp_pos _).le ht0.le
  have hae : 0 ≤ᵐ[volume] (phiLog T : Euc d → ℝ) := Filter.Eventually.of_forall hnn
  have hmeas : Measurable (phiLog T : Euc d → ℝ) := by
    unfold phiLog
    have hF : StronglyMeasurable fun p : Euc d × ℝ => Real.exp (-p.2 * ‖p.1‖ ^ 2) / p.2 :=
      (by fun_prop : Measurable fun p : Euc d × ℝ => Real.exp (-p.2 * ‖p.1‖ ^ 2) / p.2).stronglyMeasurable
    have hI := hF.integral_prod_right' (ν := volume.restrict (Ioi T))
    exact (hI.const_mul (1 / 2 : ℝ)).measurable
  have hL := cld3b_lintegral_phiLog hd hT
  have hV : 0 ≤ Real.pi ^ ((d : ℝ) / 2) / d * T ^ (-((d : ℝ) / 2)) := by positivity
  refine ⟨hnn, ⟨hmeas.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal hae, hL]
    exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hae hmeas.aestronglyMeasurable, hL,
      ENNReal.toReal_ofReal hV]

end HRS.MH.CoercLower
