import HRS.MH.ScreenedS3Aux3

/-!
# Packet S3 (`kg_fourier_h`): Fourier representation of `g * ∂_iφ`, `0 ≤ s < d`

Route: `0 < s`: `riesz_potential_fourier` applied to the Schwartz function `𝓕⁻ Θ`, `Θ = ∂_iφ(y - ·)`.
`s = 0` (kernel `-log|x|`): limit `s → 0⁺` of the identity for `s > 0` applied to `(|x|^{-s} - 1)/s`
(`∫ Θ = 0`), see `ScreenedS3Aux1/2`; this replaces the Frullani integral of the plan.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

lemma s3_fourier_cont (φ : SchwartzMap (Euc d) ℝ) :
    Continuous (𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ))) := by
  have := (𝓕 (s3Cx φ) : SchwartzMap (Euc d) ℂ).continuous
  rw [SchwartzMap.fourier_coe] at this
  exact this

/-- The Schwartz function `2π 𝓕φ`. -/
def s3G (φ : SchwartzMap (Euc d) ℝ) : SchwartzMap (Euc d) ℂ :=
  ((2 * Real.pi : ℝ) : ℂ) • (𝓕 (s3Cx φ) : SchwartzMap (Euc d) ℂ)

lemma norm_s3G (φ : SchwartzMap (Euc d) ℝ) (ξ : Euc d) :
    ‖s3G φ ξ‖ = 2 * Real.pi * ‖𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) ξ‖ := by
  unfold s3G
  rw [smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    SchwartzMap.fourier_coe]
  rfl

/-- The Riesz identity for `Θ = ∂_iφ(y-·)`, `Φ = 𝓕⁻ Θ`. -/
lemma s3_riesz_theta (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d)
    (φ : SchwartzMap (Euc d) ℝ) (i : Fin d) (y : Euc d) :
    (s3A s : ℂ) * ∫ x : Euc d, ((‖x‖ ^ (-s) : ℝ) : ℂ) * s3Theta φ i y x =
      (s3B d s : ℂ) * ∫ ξ : Euc d, ((‖ξ‖ ^ (s - d) : ℝ) : ℂ) * s3Phi φ i y ξ := by
  have h := HRS.Commutator.Whole.riesz_potential_aux hd s hs hsd (s3Phi φ i y)
  rw [fourier_s3Phi] at h
  exact h

/-- The main identity with an explicit constant. -/
lemma s3_main (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (φ : SchwartzMap (Euc d) ℝ) (i : Fin d) (y : Euc d),
      ((HRS.Whole.convFun (rieszKernel d s)
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) y : ℝ) : ℂ) =
      (c : ℂ) * ∫ ξ : Euc d, ((‖ξ‖ ^ (s - d) : ℝ) : ℂ) * s3Phi φ i y ξ := by
  rcases hs0.eq_or_lt with h0 | hpos
  · subst h0
    refine ⟨s3B d 0 / 2, by have := s3B_pos (d := d) (s := 0) (by exact_mod_cast hd); positivity,
      fun φ i y => ?_⟩
    rw [convFun_eq_integral_theta]
    have hk : ∀ x : Euc d, rieszKernel d 0 x = -Real.log ‖x‖ := fun x => by simp [rieszKernel]
    simp_rw [hk]
    refine s3_zero_case hd _ _ (s3Theta φ i y) rfl (s3Phi φ i y).continuous
      (s3G φ) ?_
      (integral_s3Theta φ i y) ?_
    · intro ξ
      rw [norm_s3G]
      exact norm_s3Phi_le φ i y ξ
    · intro s hs hsd'
      exact s3_riesz_theta hd hs hsd' φ i y
  · refine ⟨s3B d s / s3A s, div_pos (s3B_pos hsd) (s3A_pos hpos), fun φ i y => ?_⟩
    rw [convFun_eq_integral_theta]
    have hk : ∀ x : Euc d, rieszKernel d s x = ‖x‖ ^ (-s) := fun x => by
      simp [rieszKernel, hpos.ne']
    simp_rw [hk]
    have hA : (s3A s : ℂ) ≠ 0 := by exact_mod_cast (s3A_pos hpos).ne'
    have := s3_riesz_theta hd hpos hsd φ i y
    push_cast
    rw [div_mul_eq_mul_div, eq_div_iff hA, mul_comm, this]

lemma s3_integrand_eq (c s : ℝ) (φ : SchwartzMap (Euc d) ℝ) (i : Fin d) (y ξ : Euc d) :
    ((c * (2 * Real.pi * ξ i) * ‖ξ‖ ^ (s - d) : ℝ) : ℂ) * Complex.I *
        𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) ξ *
          Complex.exp (2 * Real.pi * Complex.I * (inner ℝ y ξ : ℝ)) =
      (c : ℂ) * (((‖ξ‖ ^ (s - d) : ℝ) : ℂ) * s3Phi φ i y ξ) := by
  rw [s3Phi_apply]
  push_cast
  ring

lemma s3_symbol_integrable' (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {c : ℝ} (hc : 0 < c)
    (φ : SchwartzMap (Euc d) ℝ) (i : Fin d) :
    Integrable (fun ξ : Euc d => ((c * (2 * Real.pi * ξ i) * ‖ξ‖ ^ (s - d) : ℝ) : ℂ) * Complex.I *
        𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) ξ) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hi := (s3_integrable_rpow_norm hd (a := s - d + 1) (by linarith) (by linarith)
    (s3G φ)).const_mul c
  refine hi.mono' ?_ (Eventually.of_forall fun ξ => ?_)
  · refine Measurable.aestronglyMeasurable ?_
    refine Measurable.mul (Measurable.mul ?_ measurable_const) (s3_fourier_cont φ).measurable
    exact Complex.measurable_ofReal.comp
      ((measurable_const.mul (measurable_const.mul (measurable_pi_apply i |>.comp
        (by fun_prop : Measurable fun ξ : Euc d => ξ.ofLp)))).mul
        (measurable_norm.pow_const _))
  · rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, norm_s3G]
    have hi' : |ξ i| ≤ ‖ξ‖ := by simpa using PiLp.norm_apply_le ξ i
    have h2 : ‖ξ‖ ^ (s - d) * ‖ξ‖ ≤ ‖ξ‖ ^ (s - d + 1) := by
      by_cases hξ : ξ = 0
      · subst hξ; simp only [norm_zero, mul_zero]; exact Real.rpow_nonneg le_rfl _
      · rw [Real.rpow_add_one (norm_ne_zero_iff.2 hξ)]
    have h3 : 0 ≤ ‖ξ‖ ^ (s - d) := Real.rpow_nonneg (norm_nonneg ξ) _
    have h4 : ‖c * (2 * Real.pi * ξ i) * ‖ξ‖ ^ (s - d)‖ =
        c * (2 * Real.pi * |ξ i|) * ‖ξ‖ ^ (s - d) := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos hc, abs_of_pos (by positivity :
        0 < 2 * Real.pi), abs_of_nonneg h3]
    rw [h4]
    have hφ := norm_nonneg (𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) ξ)
    calc c * (2 * Real.pi * |ξ i|) * ‖ξ‖ ^ (s - d) * ‖𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) ξ‖
        ≤ c * (2 * Real.pi * ‖ξ‖) * ‖ξ‖ ^ (s - d) * ‖𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) ξ‖ := by
          gcongr
      _ = c * ((‖ξ‖ ^ (s - d) * ‖ξ‖) * (2 * Real.pi * ‖𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) ξ‖)) := by
          ring
      _ ≤ c * (‖ξ‖ ^ (s - d + 1) * (2 * Real.pi * ‖𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) ξ‖)) := by
          gcongr

theorem kg_fourier_h_proof (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (i : Fin d) (φ : SchwartzMap (Euc d) ℝ) (y : Euc d),
      Integrable (fun ξ : Euc d => ((c * (2 * Real.pi * ξ i) * ‖ξ‖ ^ (s - d) : ℝ) : ℂ) * Complex.I *
        𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) ξ) ∧
      ((HRS.Whole.convFun (rieszKernel d s) (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) y : ℝ) : ℂ) =
        ∫ ξ : Euc d, ((c * (2 * Real.pi * ξ i) * ‖ξ‖ ^ (s - d) : ℝ) : ℂ) * Complex.I *
          𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) ξ *
          Complex.exp (2 * Real.pi * Complex.I * (inner ℝ y ξ : ℝ)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨c, hc, hmain⟩ := s3_main hd hs0 hsd
  refine ⟨c, hc, fun i φ y => ⟨?_, ?_⟩⟩
  · exact s3_symbol_integrable' hd hs0 hsd hc φ i
  · rw [hmain φ i y, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun ξ => (s3_integrand_eq c s φ i y ξ).symm)

end HRS.MH.Screened
