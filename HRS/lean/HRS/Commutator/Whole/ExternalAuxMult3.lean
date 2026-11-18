import HRS.Commutator.Whole.ExternalAuxMult2

/-!
# X-MULT auxiliary (3): homogeneous symbols, reality, and `mult_kernel_bounds`

`cmxMY_LP_homog`: for a symbol `(1-χ) h` with `h` smooth off `0` and homogeneous of degree `-γ`
(`0 < γ`), the kernel of `cmxMY_LP`.  `cmxMY_mult_kernel_bounds` is `mult_kernel_bounds`
(the real kernel is the real part of the complex one, the symbol being real and even).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ}

lemma cmxMY_contDiff_of_away {f : Euc d → ℂ} (hf : ∀ η : Euc d, η ≠ 0 → ContDiffAt ℝ ∞ f η)
    (hz : ∀ η : Euc d, ‖η‖ < 1 / 2 → f η = 0) : ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro η
  by_cases h : η = 0
  · subst h
    have : f =ᶠ[𝓝 (0 : Euc d)] fun _ => (0 : ℂ) := by
      filter_upwards [Metric.ball_mem_nhds (0 : Euc d) (by norm_num : (0:ℝ) < 1 / 2)] with y hy
      exact hz y (by simpa using hy)
    exact contDiffAt_const.congr_of_eventuallyEq this
  · exact hf η h

/-- The dyadic pieces of `(1 - χ) h` for a homogeneous `h`. -/
def cmxMY_theta (h : Euc d → ℂ) (j : ℕ) (η : Euc d) : ℂ :=
  (cmxMY_rho η * (1 - chi (((2 : ℝ) ^ j) • η)) : ℝ) • h η

lemma cmxMY_theta_contDiff (h : Euc d → ℂ) (hsm : ∀ η : Euc d, η ≠ 0 → ContDiffAt ℝ ∞ h η) (j : ℕ) :
    ContDiff ℝ ∞ (cmxMY_theta h j) := by
  refine cmxMY_contDiff_of_away (fun η hη => ?_) (fun η hη => ?_)
  · have h1 : ContDiff ℝ ∞ (fun η : Euc d => (cmxMY_rho η * (1 - chi (((2 : ℝ) ^ j) • η)) : ℝ)) :=
      cmxMY_rho_contDiff.mul (contDiff_const.sub (cmxFB_chi_contDiff.comp (contDiff_const_smul _)))
    exact h1.contDiffAt.smul (hsm η hη)
  · unfold cmxMY_theta
    rw [cmxMY_rho_eq_zero_of_le hη.le]; simp

lemma cmxMY_theta_supp (h : Euc d → ℂ) (j : ℕ) (η : Euc d) (hη : 2 < ‖η‖) : cmxMY_theta h j η = 0 := by
  unfold cmxMY_theta
  rw [cmxMY_rho_eq_zero_of_ge hη.le]; simp

lemma cmxMY_theta_ge_two (h : Euc d → ℂ) {j : ℕ} (hj : 2 ≤ j) :
    cmxMY_theta h j = fun η => (cmxMY_rho η : ℝ) • h η := by
  funext η
  unfold cmxMY_theta
  by_cases hη : ‖η‖ ≤ 1 / 2
  · rw [cmxMY_rho_eq_zero_of_le hη]; simp
  · push Not at hη
    have h2 : chi (((2 : ℝ) ^ j) • η) = 0 := by
      apply cmxFB_chi_zero
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      have : (2 : ℝ) ^ 2 ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
      nlinarith
    rw [h2]; simp

lemma cmxMY_theta_bdd (h : Euc d → ℂ) (hsm : ∀ η : Euc d, η ≠ 0 → ContDiffAt ℝ ∞ h η) :
    ∃ j₀ : ℕ, ∀ n : ℕ, ∃ B : ℝ, ∀ j ≥ j₀, ∀ η, ‖iteratedFDeriv ℝ n (cmxMY_theta h j) η‖ ≤ B := by
  refine ⟨2, fun n => ?_⟩
  have hcd : ContDiff ℝ ∞ (cmxMY_theta h 2) := cmxMY_theta_contDiff h hsm 2
  obtain ⟨B, -, hB⟩ := cmxMY_bdd_deriv (cmxMY_theta h 2) hcd (cmxMY_theta_supp h 2) n
  refine ⟨B, fun j hj η => ?_⟩
  rw [cmxMY_theta_ge_two h hj, ← cmxMY_theta_ge_two h (le_refl 2)]
  exact hB η

/-- piece identity. -/
lemma cmxMY_theta_piece (h : Euc d → ℂ) {γ : ℝ}
    (hhom : ∀ (t : ℝ) (η : Euc d), 0 < t → h (t • η) = ((t ^ (-γ) : ℝ)) • h η) (j : ℕ) (ξ : Euc d) :
    (((2 : ℝ) ^ j) ^ (-γ) : ℝ) • cmxMY_theta h j (((2 : ℝ) ^ j)⁻¹ • ξ) =
      (cmxMY_rho (((2 : ℝ) ^ j)⁻¹ • ξ) * (1 - chi ξ) : ℝ) • h ξ := by
  have hs0 : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  unfold cmxMY_theta
  have e1 : ((2 : ℝ) ^ j) • (((2 : ℝ) ^ j)⁻¹ • ξ) = ξ := by
    rw [smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]
  rw [e1, hhom _ _ (inv_pos.2 hs0), smul_smul, smul_smul, Real.inv_rpow hs0.le]
  congr 1
  have : ((2 : ℝ) ^ j) ^ (-γ) * (((2 : ℝ) ^ j) ^ (-γ))⁻¹ = 1 :=
    mul_inv_cancel₀ (Real.rpow_pos_of_pos hs0 _).ne'
  calc ((2 : ℝ) ^ j) ^ (-γ) * (cmxMY_rho (((2 : ℝ) ^ j)⁻¹ • ξ) * (1 - chi ξ)) * (((2 : ℝ) ^ j) ^ (-γ))⁻¹
      = (cmxMY_rho (((2 : ℝ) ^ j)⁻¹ • ξ) * (1 - chi ξ)) *
        (((2 : ℝ) ^ j) ^ (-γ) * (((2 : ℝ) ^ j) ^ (-γ))⁻¹) := by ring
    _ = _ := by rw [this, mul_one]

theorem cmxMY_LP_homog (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (h : Euc d → ℂ)
    (hsm : ∀ η : Euc d, η ≠ 0 → ContDiffAt ℝ ∞ h η)
    (hhom : ∀ (t : ℝ) (η : Euc d), 0 < t → h (t • η) = ((t ^ (-γ) : ℝ)) • h η) :
    ∃ K : Euc d → ℂ, Integrable K ∧ (∀ ξ : Euc d, 𝓕 K ξ = (1 - chi ξ : ℝ) • h ξ) ∧
      (∀ m : ℕ, ∃ C : ℝ, ∀ x : Euc d, 1 ≤ ‖x‖ → ‖K x‖ ≤ C * ‖x‖ ^ (-(m : ℝ))) ∧
      (γ < d → ∃ C : ℝ, ∀ x : Euc d, x ≠ 0 → ‖x‖ ≤ 1 → ‖K x‖ ≤ C * ‖x‖ ^ (γ - d)) := by
  obtain ⟨K, hK, hF, hfar, hnear⟩ := cmxMY_LP hd hγ (cmxMY_theta h)
    (cmxMY_theta_contDiff h hsm) (cmxMY_theta_supp h) (cmxMY_theta_bdd h hsm)
  refine ⟨K, hK, fun ξ => ?_, hfar, hnear⟩
  have hξF := hF ξ
  simp_rw [cmxMY_theta_piece h hhom] at hξF
  by_cases hξ : 1 ≤ ‖ξ‖
  · have h1 := cmxMY_rho_sum_eq_one hξ
    have h2 := (h1.mul_right (1 - chi ξ)).smul_const (h ξ)
    rw [one_mul] at h2
    exact hξF.unique h2
  · have hc : chi ξ = 1 := cmxFB_chi_one (by linarith)
    have h0 : HasSum (fun j : ℕ => (cmxMY_rho (((2 : ℝ) ^ j)⁻¹ • ξ) * (1 - chi ξ) : ℝ) • h ξ)
        ((1 - chi ξ : ℝ) • h ξ) := by
      simp only [hc, sub_self, mul_zero, zero_smul]
      exact hasSum_zero
    exact hξF.unique h0

lemma cmxMY_fourier_conj (K : Euc d → ℂ) (ξ : Euc d) :
    𝓕 (fun x => (starRingEnd ℂ) (K x)) ξ = (starRingEnd ℂ) (𝓕 K (-ξ)) := by
  simp only [Real.fourier_eq]
  rw [← integral_conj]
  congr 1
  ext x
  simp only [inner_neg_right, neg_neg]
  simp only [Circle.smul_def, smul_eq_mul, map_mul, Real.fourierChar_apply]
  rw [← Complex.exp_conj]
  congr 2
  simp [Complex.conj_ofReal]
  left
  exact (map_ofNat (starRingEnd ℂ) 2).symm

lemma cmxMY_real_part (K : Euc d → ℂ) (hK : Integrable K) (q : Euc d → ℝ)
    (hq : ∀ ξ, q (-ξ) = q ξ) (hF : ∀ ξ, 𝓕 K ξ = (q ξ : ℂ)) (ξ : Euc d) :
    𝓕 (fun x => (((K x).re : ℝ) : ℂ)) ξ = (q ξ : ℂ) := by
  have hKc : Integrable (fun x => (starRingEnd ℂ) (K x)) := by
    refine hK.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable hK.1) ?_
    exact Eventually.of_forall fun x => by simp
  have hfun : (fun x => (((K x).re : ℝ) : ℂ)) =
      fun x => (1 / 2 : ℝ) • (K x + (starRingEnd ℂ) (K x)) := by
    funext x
    rw [Complex.re_eq_add_conj]
    simp [Complex.real_smul]
    ring
  have h1 : Integrable (fun x : Euc d => (𝐞 (-inner ℝ x ξ) : Circle) • K x) :=
    (Real.fourierIntegral_convergent_iff ξ).2 hK
  have h2 : Integrable (fun x : Euc d => (𝐞 (-inner ℝ x ξ) : Circle) • (starRingEnd ℂ) (K x)) :=
    (Real.fourierIntegral_convergent_iff ξ).2 hKc
  have e : 𝓕 (fun x => (K x + (starRingEnd ℂ) (K x))) ξ = 𝓕 K ξ + 𝓕 (fun x => (starRingEnd ℂ) (K x)) ξ := by
    simp only [Real.fourier_eq, smul_add]
    exact integral_add h1 h2
  rw [hfun, cmxMY_fourier_real_smul, e, cmxMY_fourier_conj, hF, hF]
  rw [hq, Complex.conj_ofReal, Complex.real_smul]
  push_cast
  ring

/-- `h(η) = (2π‖η‖)^{-γ}` -/
lemma cmxMY_riesz_symbol_smooth (γ : ℝ) (η : Euc d) (hη : η ≠ 0) :
    ContDiffAt ℝ ∞ (fun η : Euc d => (((2 * Real.pi * ‖η‖) ^ (-γ) : ℝ) : ℂ)) η := by
  refine Complex.ofRealCLM.contDiff.contDiffAt.comp η ?_
  have h1 : ContDiffAt ℝ ∞ (fun η : Euc d => 2 * Real.pi * ‖η‖) η :=
    contDiffAt_const.mul (contDiffAt_norm ℝ hη)
  exact h1.rpow_const_of_ne (by positivity)

lemma cmxMY_riesz_symbol_hom (γ : ℝ) (t : ℝ) (η : Euc d) (ht : 0 < t) :
    (((2 * Real.pi * ‖t • η‖) ^ (-γ) : ℝ) : ℂ) =
      ((t ^ (-γ) : ℝ)) • (((2 * Real.pi * ‖η‖) ^ (-γ) : ℝ) : ℂ) := by
  rw [norm_smul, Real.norm_of_nonneg ht.le, Complex.real_smul, ← Complex.ofReal_mul]
  congr 1
  rw [show 2 * Real.pi * (t * ‖η‖) = t * (2 * Real.pi * ‖η‖) by ring,
    Real.mul_rpow ht.le (by positivity)]

theorem cmxMY_mult_kernel_bounds (hd : 1 ≤ d) (γ : ℝ) (hγ : 0 < γ) (hγd : γ < d) :
    ∃ K : Euc d → ℝ, Integrable K ∧
      (∀ ξ : Euc d, 𝓕 (fun x : Euc d => ((K x : ℝ) : ℂ)) ξ =
        (((1 - chi ξ) * (2 * Real.pi * ‖ξ‖) ^ (-γ) : ℝ) : ℂ)) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ x : Euc d, x ≠ 0 → ‖x‖ ≤ 1 → |K x| ≤ C * ‖x‖ ^ (γ - d)) ∧
      (∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : Euc d, 1 ≤ ‖x‖ → |K x| ≤ C * ‖x‖ ^ (-(m : ℝ))) := by
  obtain ⟨K, hK, hF, hfar, hnear⟩ := cmxMY_LP_homog hd hγ
    (fun η : Euc d => (((2 * Real.pi * ‖η‖) ^ (-γ) : ℝ) : ℂ))
    (fun η hη => cmxMY_riesz_symbol_smooth γ η hη)
    (fun t η ht => cmxMY_riesz_symbol_hom γ t η ht)
  have hq : ∀ ξ : Euc d, 𝓕 K ξ = (((1 - chi ξ) * (2 * Real.pi * ‖ξ‖) ^ (-γ) : ℝ) : ℂ) := by
    intro ξ
    rw [hF ξ, Complex.real_smul]
    push_cast
    ring
  have heven : ∀ ξ : Euc d, (1 - chi (-ξ)) * (2 * Real.pi * ‖-ξ‖) ^ (-γ) =
      (1 - chi ξ) * (2 * Real.pi * ‖ξ‖) ^ (-γ) := by
    intro ξ; rw [cmxFB_chi_neg, norm_neg]
  refine ⟨fun x => (K x).re, hK.re, cmxMY_real_part K hK _ heven hq, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := hnear hγd
    refine ⟨|C| + 1, by positivity, fun x hx hx1 => ?_⟩
    have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hp : 0 < ‖x‖ ^ (γ - d) := Real.rpow_pos_of_pos hx0 _
    calc |(K x).re| ≤ ‖K x‖ := Complex.abs_re_le_norm _
      _ ≤ C * ‖x‖ ^ (γ - d) := hC x hx hx1
      _ ≤ (|C| + 1) * ‖x‖ ^ (γ - d) := by
          gcongr
          linarith [le_abs_self C]
  · intro m
    obtain ⟨C, hC⟩ := hfar m
    refine ⟨|C| + 1, by positivity, fun x hx => ?_⟩
    have hx0 : 0 < ‖x‖ := by linarith
    have hp : 0 < ‖x‖ ^ (-(m : ℝ)) := Real.rpow_pos_of_pos hx0 _
    calc |(K x).re| ≤ ‖K x‖ := Complex.abs_re_le_norm _
      _ ≤ C * ‖x‖ ^ (-(m : ℝ)) := hC x hx
      _ ≤ (|C| + 1) * ‖x‖ ^ (-(m : ℝ)) := by
          gcongr
          linarith [le_abs_self C]

end HRS.Commutator.Whole
