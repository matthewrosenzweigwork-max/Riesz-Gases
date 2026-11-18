import HRS.MH.ScreenedDefs
import HRS.Commutator.Whole.LocalAuxKR

/-!
# Packet S3, part 1: real-analysis lemmas for the `s → 0⁺` limit (log kernel)

`(r^{-s} - 1)/s → -log r` with an `s`-uniform domination, the Gamma-function constants
`A(s) = π^{-s/2} Γ(s/2)`, `B(s) = π^{-(d-s)/2} Γ((d-s)/2)` and `B(s)/(s A(s)) → B(0)/2`, and the
abstract statement `s3_zero_case`: from the Riesz identity for `0 < s < d` and `∫ Θ = 0` to the
identity for the logarithmic kernel.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

/-- Uniform bound for the difference quotient `(r^{-s}-1)/s`, `0 < s ≤ 1/4`. -/
lemma s3_pow_bound {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hs4 : s ≤ 1 / 4) :
    |(r ^ (-s) - 1) / s| ≤ 4 * r ^ (-(1 / 2 : ℝ)) + r := by
  have hrw : r ^ (-s) = Real.exp (-s * Real.log r) := by
    rw [Real.rpow_def_of_pos hr]; ring_nf
  have hr12 : 0 < r ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hr _
  rcases le_or_gt r 1 with h1 | h1
  · have hL : Real.log r ≤ 0 := Real.log_nonpos hr.le h1
    set u := -Real.log r with hu
    have hu0 : 0 ≤ u := by linarith
    have hexp : r ^ (-s) = Real.exp (s * u) := by rw [hrw]; congr 1; rw [hu]; ring
    have hp := Real.exp_pos (s * u)
    have h1' : 1 ≤ Real.exp (s * u) := Real.one_le_exp (by positivity)
    have h2 : Real.exp (s * u) - 1 ≤ s * u * Real.exp (s * u) := by
      have h0 := Real.add_one_le_exp (-(s * u))
      rw [Real.exp_neg] at h0
      have h5 : (1 - s * u) * Real.exp (s * u) ≤ 1 := by
        calc (1 - s * u) * Real.exp (s * u) ≤ (Real.exp (s * u))⁻¹ * Real.exp (s * u) := by
              apply mul_le_mul_of_nonneg_right _ hp.le; linarith
          _ = 1 := inv_mul_cancel₀ hp.ne'
      nlinarith
    have h3 : r ^ (-s) ≤ r ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hr h1 (by linarith)
    have hpos : 0 < r ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hr _
    have h4 : u ≤ 4 * r ^ (-(1 / 4 : ℝ)) := by
      have := Real.log_le_sub_one_of_pos hpos
      rw [Real.log_rpow hr] at this
      linarith
    have habs : |(r ^ (-s) - 1) / s| = (r ^ (-s) - 1) / s := by
      rw [abs_of_nonneg]; apply div_nonneg _ hs.le; rw [hexp]; linarith
    rw [habs, div_le_iff₀ hs]
    have hrr : r ^ (-(1 / 4 : ℝ)) * r ^ (-(1 / 4 : ℝ)) = r ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hr]; norm_num
    have h6 : u * r ^ (-s) ≤ (4 * r ^ (-(1 / 4 : ℝ))) * r ^ (-(1 / 4 : ℝ)) :=
      mul_le_mul h4 h3 (by rw [hexp]; exact hp.le) (by positivity)
    have h7 : r ^ (-s) - 1 ≤ s * (u * r ^ (-s)) := by rw [hexp] at h6 ⊢; nlinarith
    nlinarith
  · have hL : 0 < Real.log r := Real.log_pos h1
    have h0 := Real.add_one_le_exp (-(s * Real.log r))
    have hlt : r ^ (-s) ≤ 1 := by
      rw [hrw]; apply Real.exp_le_one_iff.2; nlinarith
    have hnn : 0 ≤ 1 - r ^ (-s) := by linarith
    have habs : |(r ^ (-s) - 1) / s| = (1 - r ^ (-s)) / s := by
      rw [← abs_neg, ← neg_div, neg_sub, abs_of_nonneg (div_nonneg hnn hs.le)]
    rw [habs, div_le_iff₀ hs]
    have h8 : 1 - r ^ (-s) ≤ s * Real.log r := by
      rw [hrw, show -s * Real.log r = -(s * Real.log r) by ring]; linarith
    have h9 : Real.log r ≤ r := by linarith [Real.log_le_sub_one_of_pos hr]
    nlinarith

/-- `(r^{-s}-1)/s → -log r` as `s → 0⁺`. -/
lemma s3_tendsto_slope {r : ℝ} (hr : 0 < r) :
    Tendsto (fun s : ℝ => (r ^ (-s) - 1) / s) (𝓝[>] 0) (𝓝 (-Real.log r)) := by
  have hf : HasDerivAt (fun s : ℝ => Real.exp (Real.log r * (-s)))
      (Real.exp (Real.log r * (-0)) * (Real.log r * (-1))) 0 :=
    (((hasDerivAt_id (0 : ℝ)).neg).const_mul (Real.log r)).exp
  have h1 := (hasDerivAt_iff_tendsto_slope.1 hf)
  have h2 : Tendsto (slope (fun s : ℝ => Real.exp (Real.log r * (-s))) 0) (𝓝[>] 0)
      (𝓝 (Real.exp (Real.log r * (-0)) * (Real.log r * (-1)))) :=
    h1.mono_left (nhdsWithin_mono _ (fun x hx => ne_of_gt hx))
  have h3 : Real.exp (Real.log r * (-0)) * (Real.log r * (-1)) = -Real.log r := by simp
  rw [h3] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [slope_def_field, Real.rpow_def_of_pos hr]
  simp [mul_comm]

/-- Integrability of `‖x‖^a Θ(x)` (complex-valued form) for `-d < a ≤ 0`. -/
lemma s3_integrable_rpow_mul (hd : 1 ≤ d) {a : ℝ} (ha1 : -(d : ℝ) < a) (ha2 : a ≤ 0)
    (f : SchwartzMap (Euc d) ℂ) :
    Integrable (fun x : Euc d => ((‖x‖ ^ a : ℝ) : ℂ) * f x) := by
  refine (HRS.Commutator.Whole.integrable_norm_rpow_mul_schwartz hd ha1 ha2 f).mono' ?_
    (Eventually.of_forall fun x => ?_)
  · exact (Complex.measurable_ofReal.comp (measurable_norm.pow_const a)).aestronglyMeasurable.mul
      f.continuous.aestronglyMeasurable
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) a)]

/-- `‖x‖^a ‖f‖` is integrable for `-d < a ≤ 1`. -/
lemma s3_integrable_rpow_norm (hd : 1 ≤ d) {a : ℝ} (ha1 : -(d : ℝ) < a) (ha2 : a ≤ 1)
    (f : SchwartzMap (Euc d) ℂ) :
    Integrable (fun x : Euc d => ‖x‖ ^ a * ‖f x‖) := by
  rcases le_or_gt a 0 with h | h
  · exact HRS.Commutator.Whole.integrable_norm_rpow_mul_schwartz hd ha1 h f
  · refine ((f.integrable.norm).add (f.integrable_pow_mul volume 1)).mono' ?_
      (Eventually.of_forall fun x => ?_)
    · exact ((measurable_norm.pow_const a).mul f.continuous.norm.measurable).aestronglyMeasurable
    · have h0 : 0 ≤ ‖x‖ ^ a := Real.rpow_nonneg (norm_nonneg x) a
      rw [Real.norm_of_nonneg (mul_nonneg h0 (norm_nonneg _))]
      show ‖x‖ ^ a * ‖f x‖ ≤ ‖f x‖ + ‖x‖ ^ 1 * ‖f x‖
      rcases le_or_gt ‖x‖ 1 with h1 | h1
      · have : ‖x‖ ^ a ≤ 1 := Real.rpow_le_one (norm_nonneg x) h1 h.le
        nlinarith [norm_nonneg (f x), pow_nonneg (norm_nonneg x) 1]
      · have : ‖x‖ ^ a ≤ ‖x‖ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1.le ha2
        rw [Real.rpow_one] at this
        rw [pow_one]
        nlinarith [norm_nonneg (f x), norm_nonneg x]

/-- The `x`-side limit. -/
lemma s3_lim_x (hd : 1 ≤ d) (Θ : SchwartzMap (Euc d) ℂ) :
    Tendsto (fun s : ℝ => ∫ x : Euc d, (((‖x‖ ^ (-s) - 1) / s : ℝ) : ℂ) * Θ x) (𝓝[>] 0)
      (𝓝 (∫ x : Euc d, ((-Real.log ‖x‖ : ℝ) : ℂ) * Θ x)) := by
  have hb1 := HRS.Commutator.Whole.integrable_norm_rpow_mul_schwartz hd (s := -(1 / 2 : ℝ))
    (by have : (1 : ℝ) ≤ d := by exact_mod_cast hd
        linarith) (by norm_num) Θ
  have hb2 := Θ.integrable_pow_mul volume 1
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x : Euc d => 4 * (‖x‖ ^ (-(1 / 2 : ℝ)) * ‖Θ x‖) + ‖x‖ ^ 1 * ‖Θ x‖) ?_ ?_
    ((hb1.const_mul 4).add hb2) ?_
  · refine Eventually.of_forall fun s => ?_
    refine Measurable.aestronglyMeasurable ?_
    refine Measurable.mul ?_ Θ.continuous.measurable
    exact Complex.measurable_ofReal.comp
      (((measurable_norm.pow_const _).sub_const 1).div_const s)
  · filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num)] with s hs
    filter_upwards [HRS.Commutator.Whole.ae_ne_zero_euc hd] with x hx
    have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have := s3_pow_bound hr hs.1 hs.2
    calc |(‖x‖ ^ (-s) - 1) / s| * ‖Θ x‖ ≤ (4 * ‖x‖ ^ (-(1 / 2 : ℝ)) + ‖x‖) * ‖Θ x‖ :=
          mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = _ := by rw [pow_one]; ring
  · filter_upwards [HRS.Commutator.Whole.ae_ne_zero_euc hd] with x hx
    have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
    exact (Complex.continuous_ofReal.tendsto _ |>.comp (s3_tendsto_slope hr)).mul_const _

/-- The Gamma-function constants of the Riesz-potential identity. -/
def s3A (s : ℝ) : ℝ := Real.pi ^ (-s / 2) * Real.Gamma (s / 2)

/-- The Gamma-function constants of the Riesz-potential identity. -/
def s3B (d : ℕ) (s : ℝ) : ℝ := Real.pi ^ (-((d : ℝ) - s) / 2) * Real.Gamma (((d : ℝ) - s) / 2)

lemma s3A_pos {s : ℝ} (hs : 0 < s) : 0 < s3A s :=
  mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by linarith))

lemma s3B_pos {s : ℝ} (hsd : s < d) : 0 < s3B d s :=
  mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by linarith))

lemma s3_tendsto_kappa (hd : 1 ≤ d) :
    Tendsto (fun s : ℝ => s3B d s / (s * s3A s)) (𝓝[>] 0) (𝓝 (s3B d 0 / 2)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set F : ℝ → ℝ := fun s => s3B d s / (Real.pi ^ (-s / 2) * (2 * Real.Gamma (s / 2 + 1))) with hF
  have hGam : ∀ x : ℝ, 0 < x → ContinuousAt Real.Gamma x := fun x hx =>
    (Real.differentiableAt_Gamma (fun m => by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      intro h; linarith)).continuousAt
  have hBc : ContinuousAt (s3B d) 0 := by
    unfold s3B
    refine ContinuousAt.mul ?_ ?_
    · exact (Real.continuous_const_rpow Real.pi_pos.ne' |>.comp (by fun_prop : Continuous
        fun s : ℝ => -((d : ℝ) - s) / 2)).continuousAt
    · refine ContinuousAt.comp (g := Real.Gamma) (f := fun s : ℝ => ((d : ℝ) - s) / 2) ?_ ?_
      · apply hGam; simp; linarith
      · fun_prop
  have hFc : ContinuousAt F 0 := by
    rw [hF]
    refine ContinuousAt.div hBc ?_ ?_
    · refine ContinuousAt.mul ?_ (ContinuousAt.mul continuousAt_const ?_)
      · exact (Real.continuous_const_rpow Real.pi_pos.ne' |>.comp (by fun_prop : Continuous
          fun s : ℝ => -s / 2)).continuousAt
      · refine ContinuousAt.comp (g := Real.Gamma) (f := fun s : ℝ => s / 2 + 1) ?_ ?_
        · apply hGam; simp
        · fun_prop
    · simp [Real.Gamma_one]
  have hF0 : F 0 = s3B d 0 / 2 := by
    simp [hF, Real.Gamma_one]
  have h1 : Tendsto F (𝓝[>] 0) (𝓝 (s3B d 0 / 2)) := by
    rw [← hF0]; exact hFc.tendsto.mono_left nhdsWithin_le_nhds
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : (0 : ℝ) < s := hs
  have hG : Real.Gamma (s / 2 + 1) = s / 2 * Real.Gamma (s / 2) :=
    Real.Gamma_add_one (by positivity)
  simp only [hF, s3A, hG]
  congr 1
  ring

end HRS.MH.Screened
