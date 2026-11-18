import HRS.MC.D1E

/-!
# Packet D1F: Fourier-side normalisation of the Fefferman-de la Llave constant, `s > 0`
(namespace `HRS.MC.D1F`)
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.MC.D1F

open HRS HRS.MC.D1E

variable {d : ℕ}

theorem d1f_psi_cont {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) : Continuous ψ := hψ.smooth.continuous

theorem d1f_psi_int {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) : Integrable ψ :=
  (d1f_psi_cont hψ).integrable_of_hasCompactSupport (d1e_psi_compact hψ)

theorem d1f_psiC_int {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) :
    Integrable (fun x => (ψ x : ℂ)) := (d1f_psi_int hψ).ofReal

/-- `ψ` as a complex Schwartz function. -/
def d1f_S {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) : SchwartzMap (Euc d) ℂ :=
  HasCompactSupport.toSchwartzMap (f := fun x => (ψ x : ℂ))
    ((d1e_psi_compact hψ).comp_left Complex.ofReal_zero)
    (Complex.ofRealCLM.contDiff.comp hψ.smooth)

/-- The (complex) Fourier transform of `ψ` is the real function `fdlPsiHat ψ`. -/
theorem d1f_fourier_psi {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (ξ : Euc d) :
    𝓕 (fun x => (ψ x : ℂ)) ξ = (fdlPsiHat ψ ξ : ℂ) := by
  have hcont : Continuous ψ := d1f_psi_cont hψ
  have hcs : HasCompactSupport ψ := d1e_psi_compact hψ
  have hI : ∀ g : ℝ → ℝ, Continuous g →
      Integrable (fun v : Euc d => ψ v * g (2 * Real.pi * inner ℝ ξ v)) := by
    intro g hg
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact hcont.mul (hg.comp (continuous_const.mul (continuous_const.inner continuous_id)))
    · exact hcs.mul_right
  have hsin : ∫ v : Euc d, ψ v * Real.sin (2 * Real.pi * inner ℝ ξ v) = 0 := by
    have h := integral_neg_eq_self (fun v : Euc d => ψ v * Real.sin (2 * Real.pi * inner ℝ ξ v))
      (volume : Measure (Euc d))
    have h2 : ∫ v : Euc d, ψ (-v) * Real.sin (2 * Real.pi * inner ℝ ξ (-v)) =
        -∫ v : Euc d, ψ v * Real.sin (2 * Real.pi * inner ℝ ξ v) := by
      rw [← integral_neg]
      congr 1
      funext v
      rw [hψ.radial (-v) v (norm_neg v), inner_neg_right, mul_neg, Real.sin_neg]
      ring
    linarith
  rw [Real.fourier_eq']
  unfold fdlPsiHat
  have hpt : ∀ v : Euc d, Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • (ψ v : ℂ) =
      ((ψ v * Real.cos (2 * Real.pi * inner ℝ ξ v) : ℝ) : ℂ) -
        Complex.I * ((ψ v * Real.sin (2 * Real.pi * inner ℝ ξ v) : ℝ) : ℂ) := by
    intro v
    rw [Complex.exp_mul_I, smul_eq_mul, real_inner_comm]
    have : (-2 * Real.pi * inner ℝ ξ v : ℝ) = -(2 * Real.pi * inner ℝ ξ v) := by ring
    rw [this]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  simp_rw [hpt]
  rw [integral_sub, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal, hsin]
  · simp
  · exact (hI _ Real.continuous_cos).ofReal
  · exact ((hI _ Real.continuous_sin).ofReal).const_mul _


/-- Rotation invariance of `ψ̂`. -/
theorem d1f_hat_invariant {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (L : Euc d ≃ₗᵢ[ℝ] Euc d)
    (ξ : Euc d) : fdlPsiHat ψ (L ξ) = fdlPsiHat ψ ξ := by
  have hmp : MeasurePreserving L := L.measurePreserving
  have hemb : MeasurableEmbedding L := L.toHomeomorph.measurableEmbedding
  unfold fdlPsiHat
  have key := hmp.integral_comp hemb
    (fun y => ψ y * Real.cos (2 * Real.pi * inner ℝ (L ξ) y))
  rw [← key]
  congr 1
  funext x
  rw [hψ.radial (L x) x (LinearIsometryEquiv.norm_map L x), LinearIsometryEquiv.inner_map_map]

/-- Radiality of `ψ̂`. -/
theorem d1f_hat_radial {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {y z : Euc d} (hyz : ‖y‖ = ‖z‖) :
    fdlPsiHat ψ y = fdlPsiHat ψ z := by
  set L : Euc d ≃ₗᵢ[ℝ] Euc d := Submodule.reflection (Submodule.span ℝ {y - z})ᗮ with hL
  have hLy : L y = z := Submodule.reflection_sub hyz
  have := d1f_hat_invariant hψ L y
  rw [hLy] at this
  exact this.symm

/-- `ψ̂` is the evaluation of a complex Schwartz function. -/
theorem d1f_hat_schwartz {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) :
    ∃ T : SchwartzMap (Euc d) ℂ, ∀ ξ, T ξ = (fdlPsiHat ψ ξ : ℂ) := by
  refine ⟨SchwartzMap.fourierTransformCLM ℂ (d1f_S hψ), fun ξ => ?_⟩
  rw [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe]
  exact d1f_fourier_psi hψ ξ

theorem d1f_hat_cont {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) : Continuous (fdlPsiHat ψ) := by
  obtain ⟨T, hT⟩ := d1f_hat_schwartz hψ
  have : Continuous fun ξ => (fdlPsiHat ψ ξ : ℂ) := by
    simpa [funext hT] using T.continuous
  exact (Complex.continuous_re.comp this).congr (fun ξ => by simp)

theorem d1f_hat_decay {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : Euc d, ‖ξ‖ ^ k * |fdlPsiHat ψ ξ| ≤ C := by
  obtain ⟨T, hT⟩ := d1f_hat_schwartz hψ
  obtain ⟨C, hC, h⟩ := T.decay k 0
  refine ⟨C, hC, fun ξ => ?_⟩
  have := h ξ
  rw [norm_iteratedFDeriv_zero, hT, Complex.norm_real, Real.norm_eq_abs] at this
  exact this

/-- `φ = ψ * ψ` has Fourier transform `ψ̂²`. -/
theorem d1f_fourier_phi {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (ξ : Euc d) :
    𝓕 (fun x => (fdlPhi ψ x : ℂ)) ξ = ((fdlPsiHat ψ ξ ^ 2 : ℝ) : ℂ) := by
  have hconv : convolution (fun x => (ψ x : ℂ)) (fun x => (ψ x : ℂ))
      (ContinuousLinearMap.mul ℂ ℂ) volume = fun x => (fdlPhi ψ x : ℂ) := by
    funext x
    unfold fdlPhi
    rw [convolution_def, convolution_def, ← integral_complex_ofReal]
    simp
  rw [← hconv, Real.fourier_mul_convolution_eq (d1f_psiC_int hψ) (d1f_psiC_int hψ),
    d1f_fourier_psi hψ ξ]
  push_cast
  ring


theorem d1f_phi_int {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) : Integrable (fdlPhi ψ) := by
  refine (d1e_phi_cont hψ).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) 1) (fun y hy => ?_)
  refine d1e_phi_zero_of_norm hψ ?_
  exact (not_le.mp (fun h => hy (mem_closedBall_zero_iff.2 h))).le

/-- Gaussian multiplication formula `∫ e^{-c|x|²} ψ̂(x)² dx = (π/c)^{d/2} ∫ e^{-π²|ξ|²/c} φ(ξ) dξ`. -/
theorem d1f_gauss_mult {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {c : ℝ} (hc : 0 < c) :
    ∫ x : Euc d, Real.exp (-c * ‖x‖ ^ 2) * fdlPsiHat ψ x ^ 2 =
      (Real.pi / c) ^ ((d : ℝ) / 2) *
        ∫ ξ : Euc d, Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / c) * fdlPhi ψ ξ := by
  have hcre : 0 < (c : ℂ).re := by simpa using hc
  have J : Integrable (fun v : Euc d => Complex.exp (-(c : ℂ) * (‖v‖ : ℂ) ^ 2)) := by
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Euc d) hcre 0 0
  have hφ : Integrable (fun x : Euc d => (fdlPhi ψ x : ℂ)) := (d1f_phi_int hψ).ofReal
  have key := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ (Euc d))
    (e := Real.fourierChar) Real.continuous_fourierChar continuous_inner J hφ
  have hflip : ∀ x : Euc d, VectorFourier.fourierIntegral Real.fourierChar volume
      (innerₗ (Euc d)).flip (fun x : Euc d => (fdlPhi ψ x : ℂ)) x =
        𝓕 (fun x : Euc d => (fdlPhi ψ x : ℂ)) x := by
    intro x
    rw [Real.fourier_eq]
    unfold VectorFourier.fourierIntegral
    simp only [LinearMap.flip_apply, innerₗ_apply_apply, real_inner_comm]
  simp_rw [hflip, d1f_fourier_phi hψ] at key
  have hG : ∀ ξ : Euc d, VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ (Euc d))
      (fun v : Euc d => Complex.exp (-(c : ℂ) * (‖v‖ : ℂ) ^ 2)) ξ =
        (((Real.pi / c) ^ ((d : ℝ) / 2) * Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / c) : ℝ) : ℂ) := by
    intro ξ
    have h := fourier_gaussian_innerProductSpace (V := Euc d) hcre ξ
    change 𝓕 (fun v : Euc d => Complex.exp (-(c : ℂ) * (‖v‖ : ℂ) ^ 2)) ξ = _
    rw [h, finrank_euclideanSpace_fin]
    push_cast
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl
  simp_rw [hG] at key
  have hl : ∀ ξ : Euc d, (((Real.pi / c) ^ ((d : ℝ) / 2) * Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / c) : ℝ) : ℂ)
      • ((fdlPhi ψ ξ : ℂ)) =
      (((Real.pi / c) ^ ((d : ℝ) / 2) * (Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / c) * fdlPhi ψ ξ) : ℝ) : ℂ) := by
    intro ξ; push_cast; ring
  have hr : ∀ x : Euc d, Complex.exp (-(c : ℂ) * (‖x‖ : ℂ) ^ 2) • (((fdlPsiHat ψ x ^ 2 : ℝ) : ℂ)) =
      ((Real.exp (-c * ‖x‖ ^ 2) * fdlPsiHat ψ x ^ 2 : ℝ) : ℂ) := by
    intro x; push_cast; simp
  simp_rw [hl, hr] at key
  rw [integral_complex_ofReal, integral_complex_ofReal, integral_const_mul] at key
  exact_mod_cast key.symm


/-! ### One-dimensional reductions -/

/-- Integrability on `(0,∞)` of `r^p Q(r)` from boundedness of `Q` and polynomial decay. -/
theorem d1f_oneD_int {Q : ℝ → ℝ} (hQ : Continuous Q) {p : ℝ} (hp : -1 < p) {M : ℝ}
    (hM : ∀ r, |Q r| ≤ M) {n : ℕ} {C : ℝ} (hC : ∀ r : ℝ, 1 ≤ r → |Q r| * r ^ n ≤ C)
    (hpn : p - n < -1) :
    IntegrableOn (fun r : ℝ => r ^ p * Q r) (Ioi 0) := by
  have hI1 : IntegrableOn (fun r : ℝ => r ^ p * Q r) (Ioc 0 1) := by
    have hpow : IntegrableOn (fun u : ℝ => u ^ p) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        (intervalIntegral.intervalIntegrable_rpow' hp)
    refine Integrable.mono' (hpow.const_mul M) ?_ ?_
    · exact (by have := hQ.measurable; fun_prop : Measurable fun u : ℝ => u ^ p * Q u).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioc (fun u hu => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hu.1.le _), mul_comm (u ^ p)]
      exact mul_le_mul_of_nonneg_right (hM u) (Real.rpow_nonneg hu.1.le _)
  have hI2 : IntegrableOn (fun r : ℝ => r ^ p * Q r) (Ioi 1) := by
    have hpow : IntegrableOn (fun u : ℝ => u ^ (p - n)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt hpn zero_lt_one
    refine Integrable.mono' (hpow.const_mul C) ?_ ?_
    · exact (by have := hQ.measurable; fun_prop : Measurable fun u : ℝ => u ^ p * Q u).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu => ?_)
      have hu1 : 1 ≤ u := le_of_lt hu
      have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu1
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hu0.le _)]
      have h1 : u ^ (p - n) = u ^ p / u ^ n := by
        rw [Real.rpow_sub hu0, Real.rpow_natCast]
      have h2 := hC u hu1
      have hun : 0 < u ^ n := pow_pos hu0 n
      rw [h1]
      have : u ^ p * |Q u| = u ^ p / u ^ n * (|Q u| * u ^ n) := by field_simp
      rw [this]
      calc u ^ p / u ^ n * (|Q u| * u ^ n) ≤ u ^ p / u ^ n * C :=
            mul_le_mul_of_nonneg_left h2 (div_nonneg (Real.rpow_nonneg hu0.le _) hun.le)
        _ = C * (u ^ p / u ^ n) := mul_comm _ _
  have := hI1.union hI2
  rwa [Ioc_union_Ioi_eq_Ioi zero_le_one] at this


theorem d1f_nontrivial (hd : 1 ≤ d) : Nontrivial (Euc d) := by
  rw [← Module.finrank_pos_iff (R := ℝ)]
  simpa [finrank_euclideanSpace_fin] using Nat.lt_of_lt_of_le zero_lt_one hd

/-- Surface measure of the unit sphere. -/
def d1f_omega (d : ℕ) : ℝ := (d : ℝ) * (volume (Metric.ball (0 : Euc d) 1)).toReal

theorem d1f_omega_pos (hd : 1 ≤ d) : 0 < d1f_omega d := by
  unfold d1f_omega
  have h1 : (0 : ℝ) < d := by exact_mod_cast hd
  have h2 : 0 < (volume (Metric.ball (0 : Euc d) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  positivity

theorem d1f_polar_integral (hd : 1 ≤ d) (f : ℝ → ℝ) :
    ∫ x : Euc d, f ‖x‖ = d1f_omega d * ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * f y := by
  have := d1f_nontrivial hd
  have := integral_fun_norm_addHaar (volume : Measure (Euc d)) f
  rw [this, finrank_euclideanSpace_fin]
  unfold d1f_omega
  simp only [nsmul_eq_mul, smul_eq_mul, Measure.real]
  ring

theorem d1f_polar_integrable (hd : 1 ≤ d) (f : ℝ → ℝ) :
    Integrable (fun x : Euc d => f ‖x‖) ↔
      IntegrableOn (fun y : ℝ => y ^ (d - 1) * f y) (Ioi 0) := by
  have := d1f_nontrivial hd
  have := integrable_fun_norm_addHaar (volume : Measure (Euc d)) (f := f)
  rw [finrank_euclideanSpace_fin] at this
  simpa using this

theorem d1f_pow_aux (hd : 1 ≤ d) {y : ℝ} (hy : 0 < y) (s A : ℝ) :
    y ^ (d - 1) * (y ^ (-s) * A) = y ^ ((d : ℝ) - s) * A / y := by
  have hd' : y ^ ((d : ℝ) - s) = y ^ d * y ^ (-s) := by
    rw [sub_eq_add_neg, Real.rpow_add hy, Real.rpow_natCast]
  have h2 : y ^ d = y ^ (d - 1) * y := by
    rw [← pow_succ]; congr 1; omega
  rw [hd', h2]
  field_simp

theorem d1f_pow_aux2 (hd : 1 ≤ d) {y : ℝ} (hy : 0 < y) (s A : ℝ) :
    y ^ (d - 1) * (y ^ (s - d) * A) = y ^ (s - 1) * A := by
  have h : y ^ (s - 1) = y ^ (s - d) * y ^ (d - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hy, Nat.cast_sub hd]
    congr 1
    push_cast
    ring
  rw [h]
  ring

/-- Polar coordinates for the Fourier side. -/
theorem d1f_hat_polar (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ)
    {e : Euc d} (he : ‖e‖ = 1) :
    IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - s) * fdlPsiHat ψ (t • e) ^ 2 / t) (Ioi 0) ∧
    Integrable (fun ξ : Euc d => ‖ξ‖ ^ (-s) * fdlPsiHat ψ ξ ^ 2) ∧
    ∫ ξ : Euc d, ‖ξ‖ ^ (-s) * fdlPsiHat ψ ξ ^ 2 =
      d1f_omega d * ∫ t in Ioi (0 : ℝ), t ^ ((d : ℝ) - s) * fdlPsiHat ψ (t • e) ^ 2 / t := by
  set H : ℝ → ℝ := fun r => fdlPsiHat ψ (r • e) with hH
  have hHc : Continuous H :=
    (d1f_hat_cont hψ).comp (continuous_id.smul continuous_const)
  have hrad : ∀ ξ : Euc d, fdlPsiHat ψ ξ = H ‖ξ‖ := by
    intro ξ
    refine d1f_hat_radial hψ ?_
    rw [norm_smul, he, mul_one, Real.norm_of_nonneg (norm_nonneg ξ)]
  obtain ⟨C0, hC0, h0⟩ := d1f_hat_decay hψ 0
  obtain ⟨C1, hC1, h1⟩ := d1f_hat_decay hψ d
  have hQc : Continuous fun r => H r ^ 2 := hHc.pow 2
  have hint : IntegrableOn (fun r : ℝ => r ^ ((d : ℝ) - s - 1) * H r ^ 2) (Ioi 0) := by
    refine d1f_oneD_int hQc (by linarith) (M := C0 ^ 2) (fun r => ?_) (n := 2 * d) (C := C1 ^ 2)
      (fun r hr => ?_) (by
        have : (0 : ℝ) < d := by exact_mod_cast hd
        push_cast; linarith [(by exact_mod_cast hd : (1 : ℝ) ≤ d)])
    · have := h0 (r • e)
      simp only [pow_zero, one_mul] at this
      show |H r ^ 2| ≤ _
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    · have := h1 (r • e)
      rw [norm_smul, he, mul_one, Real.norm_of_nonneg (by linarith)] at this
      show |H r ^ 2| * r ^ (2 * d) ≤ _
      calc |H r ^ 2| * r ^ (2 * d) = (r ^ d * |fdlPsiHat ψ (r • e)|) ^ 2 := by
            rw [abs_pow, pow_mul']
            show |fdlPsiHat ψ (r • e)| ^ 2 * (r ^ d) ^ 2 = _
            ring
        _ ≤ C1 ^ 2 := pow_le_pow_left₀ (by positivity) this 2
  set f : ℝ → ℝ := fun r => r ^ (-s) * H r ^ 2 with hf
  have hfe : ∀ y ∈ Ioi (0 : ℝ), y ^ (d - 1) * f y = y ^ ((d : ℝ) - s) * fdlPsiHat ψ (y • e) ^ 2 / y :=
    fun y hy => d1f_pow_aux hd hy s _
  have hJ : IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - s) * fdlPsiHat ψ (t • e) ^ 2 / t) (Ioi 0) := by
    refine hint.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht' : (0 : ℝ) < t := ht
    show t ^ ((d : ℝ) - s - 1) * H t ^ 2 = _
    rw [Real.rpow_sub_one ht'.ne']
    ring
  have hrw : (fun ξ : Euc d => ‖ξ‖ ^ (-s) * fdlPsiHat ψ ξ ^ 2) = fun ξ => f ‖ξ‖ := by
    funext ξ
    simp only [hf, hrad ξ]
  refine ⟨hJ, ?_, ?_⟩
  · rw [hrw, d1f_polar_integrable hd f]
    exact hJ.congr_fun (fun y hy => (hfe y hy).symm) measurableSet_Ioi
  · rw [hrw, d1f_polar_integral hd f]
    congr 1
    exact setIntegral_congr_fun measurableSet_Ioi hfe


/-- Polar coordinates for `φ`. -/
theorem d1f_phi_polar (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ)
    {e : Euc d} (he : ‖e‖ = 1) :
    IntegrableOn (fun u : ℝ => u ^ (s - 1) * fdlPhi ψ (u • e)) (Ioi 0) ∧
    Integrable (fun x : Euc d => ‖x‖ ^ (s - d) * fdlPhi ψ x) ∧
    ∫ x : Euc d, ‖x‖ ^ (s - d) * fdlPhi ψ x =
      d1f_omega d * ∫ u in Ioi (0 : ℝ), u ^ (s - 1) * fdlPhi ψ (u • e) := by
  set P : ℝ → ℝ := fun u => fdlPhi ψ (u • e) with hP
  have hPc : Continuous P := (d1e_phi_cont hψ).comp (continuous_id.smul continuous_const)
  have hP1 : ∀ u, 1 ≤ u → P u = 0 := fun u hu => by
    refine d1e_phi_zero_of_norm hψ ?_
    rw [norm_smul, he, mul_one, Real.norm_of_nonneg (by linarith)]
    exact hu
  obtain ⟨M, hM⟩ := d1e_phi_bdd hψ
  have hint := d1e_oneD_int_pos hPc hP1 (fun u => hM _) hs
  have hrad : ∀ x : Euc d, fdlPhi ψ x = P ‖x‖ := by
    intro x
    refine d1e_phi_radial hψ ?_
    rw [norm_smul, he, mul_one, Real.norm_of_nonneg (norm_nonneg x)]
  set f : ℝ → ℝ := fun r => r ^ (s - d) * P r with hf
  have hfe : ∀ y ∈ Ioi (0 : ℝ), y ^ (d - 1) * f y = y ^ (s - 1) * P y :=
    fun y hy => d1f_pow_aux2 hd hy s _
  have hrw : (fun x : Euc d => ‖x‖ ^ (s - d) * fdlPhi ψ x) = fun x => f ‖x‖ := by
    funext x
    simp only [hf, hrad x]
  refine ⟨hint, ?_, ?_⟩
  · rw [hrw, d1f_polar_integrable hd f]
    exact hint.congr_fun (fun y hy => (hfe y hy).symm) measurableSet_Ioi
  · rw [hrw, d1f_polar_integral hd f]
    congr 1
    exact setIntegral_congr_fun measurableSet_Ioi hfe

/-- `1/b = ∫_0^∞ u^{s-1} φ(u e) du` from the Euclidean representation. -/
theorem d1f_inv_b (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ)
    {e : Euc d} (he : ‖e‖ = 1) {b : ℝ}
    (hb : ∀ x : Euc d, x ≠ 0 → Whole.rieszKernel d s x =
        b * ∫ t in Set.Ioi (0 : ℝ), t ^ ((d : ℝ) - s) * fdlPhiScale ψ t x / t) :
    b * ∫ u in Ioi (0 : ℝ), u ^ (s - 1) * fdlPhi ψ (u • e) = 1 := by
  set P : ℝ → ℝ := fun u => fdlPhi ψ (u • e) with hP
  have hint := (d1f_phi_polar hd hs hψ he).1
  have hr : (0 : ℝ) < 1 := one_pos
  have hex : e ≠ 0 := by
    intro h; rw [h, norm_zero] at he; exact zero_ne_one he
  have h1 := hb e hex
  have hG : Set.EqOn (fun t : ℝ => t ^ ((d : ℝ) - s) * fdlPhiScale ψ t e / t)
      (fun t : ℝ => t ^ (-s - 1) * P (1 / t)) (Set.Ioi 0) := by
    intro t ht
    beta_reduce
    rw [d1e_integrand_eq hψ e e he ht, he]
  obtain ⟨_, hval⟩ := d1e_subst_pos P hr hint
  rw [setIntegral_congr_fun measurableSet_Ioi hG, hval] at h1
  unfold Whole.rieszKernel at h1
  simp only [hs.ne', ite_false, he, Real.one_rpow] at h1
  have : (∫ u in Ioi (0 : ℝ), u ^ (s - 1) * P u) = ∫ u in Ioi (0 : ℝ), u ^ (s - 1) * fdlPhi ψ (u • e) := rfl
  rw [this] at h1
  linarith


/-! ### The Fubini exchanges -/

theorem d1f_ae_ne (hd : 1 ≤ d) : ∀ᵐ x : Euc d ∂volume, x ≠ 0 := by
  have := d1f_nontrivial hd
  have h := (Set.countable_singleton (0 : Euc d)).ae_notMem (volume : Measure (Euc d))
  filter_upwards [h] with x hx
  simpa using hx

theorem d1f_gamma_int {h r : ℝ} (hh : 0 < h) (hr : 0 < r) :
    IntegrableOn (fun c : ℝ => c ^ (h - 1) * Real.exp (-(r * c))) (Ioi 0) := by
  refine (integrableOn_rpow_mul_exp_neg_mul_rpow (s := h - 1) (p := 1) (b := r)
    (by linarith) one_pos hr).congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp [Real.rpow_one]

theorem d1f_sq_rpow {r : ℝ} (hr : 0 < r) (h : ℝ) : (1 / r ^ 2) ^ h = r ^ (-(2 * h)) := by
  rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hr.le,
    ← Real.rpow_neg hr.le]
  norm_num

theorem d1f_gamma_val {h r : ℝ} (hh : 0 < h) (hr : 0 < r) :
    ∫ c in Ioi (0 : ℝ), c ^ (h - 1) * Real.exp (-(r ^ 2 * c)) = Real.Gamma h * r ^ (-(2 * h)) := by
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hh (by positivity), d1f_sq_rpow hr, mul_comm]

theorem d1f_integrable_prod {F : ℝ × Euc d → ℝ} (hF : Measurable F) {g : Euc d → ℝ}
    (hg : Integrable g)
    (hslice : ∀ᵐ x ∂(volume : Measure (Euc d)), IntegrableOn (fun c => F (c, x)) (Ioi 0) ∧
      ∫ c in Ioi (0 : ℝ), ‖F (c, x)‖ = g x) :
    Integrable F ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure (Euc d))) := by
  rw [integrable_prod_iff' hF.aestronglyMeasurable]
  refine ⟨hslice.mono fun x hx => hx.1, hg.congr ?_⟩
  filter_upwards [hslice] with x hx
  exact hx.2.symm


/-- First exchange: `Γ(s/2) ∫ |ξ|^{-s} ψ̂² = ∫_0^∞ c^{s/2-1} (π/c)^{d/2} ∫ e^{-π²|ξ|²/c} φ`. -/
theorem d1f_step1 (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {e : Euc d} (he : ‖e‖ = 1) :
    Real.Gamma (s / 2) * ∫ ξ : Euc d, ‖ξ‖ ^ (-s) * fdlPsiHat ψ ξ ^ 2 =
      ∫ c in Ioi (0 : ℝ), c ^ (s / 2 - 1) * ((Real.pi / c) ^ ((d : ℝ) / 2) *
        ∫ ξ : Euc d, Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / c) * fdlPhi ψ ξ) := by
  have hh : 0 < s / 2 := by linarith
  have hΨ : Measurable (fun x : Euc d => fdlPsiHat ψ x ^ 2) :=
    ((d1f_hat_cont hψ).measurable).pow_const 2
  set F : ℝ × Euc d → ℝ := fun p => p.1 ^ (s / 2 - 1) *
    (Real.exp (-(‖p.2‖ ^ 2 * p.1)) * fdlPsiHat ψ p.2 ^ 2) with hF
  have hFm : Measurable F := by
    have h1 : Measurable (fun p : ℝ × Euc d => p.1 ^ (s / 2 - 1)) := measurable_fst.pow_const _
    have h2 : Measurable (fun p : ℝ × Euc d => Real.exp (-(‖p.2‖ ^ 2 * p.1))) := by
      refine Real.measurable_exp.comp (Measurable.neg (Measurable.mul ?_ measurable_fst))
      exact (measurable_snd.norm).pow_const 2
    exact h1.mul (h2.mul (hΨ.comp measurable_snd))
  obtain ⟨_, hint, _⟩ := d1f_hat_polar hd hs hsd hψ he
  have hslice : ∀ x : Euc d, x ≠ 0 → IntegrableOn (fun c => F (c, x)) (Ioi 0) ∧
      ∫ c in Ioi (0 : ℝ), ‖F (c, x)‖ = Real.Gamma (s / 2) * (‖x‖ ^ (-s) * fdlPsiHat ψ x ^ 2) := by
    intro x hx
    have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hnn : ∀ c ∈ Ioi (0 : ℝ), 0 ≤ F (c, x) := fun c hc =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt hc) _) (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
    refine ⟨?_, ?_⟩
    · have h0 : IntegrableOn (fun c : ℝ => c ^ (s / 2 - 1) * Real.exp (-(‖x‖ ^ 2 * c)) *
          fdlPsiHat ψ x ^ 2) (Ioi 0) := (d1f_gamma_int hh (pow_pos hr 2)).mul_const _
      exact h0.congr_fun (fun c _ => by simp only [hF]; ring) measurableSet_Ioi
    · rw [setIntegral_congr_fun measurableSet_Ioi (fun c hc => Real.norm_of_nonneg (hnn c hc))]
      have : ∀ c : ℝ, F (c, x) = c ^ (s / 2 - 1) * Real.exp (-(‖x‖ ^ 2 * c)) * fdlPsiHat ψ x ^ 2 :=
        fun c => by simp only [hF]; ring
      simp_rw [this]
      rw [integral_mul_const, d1f_gamma_val hh hr, show -(2 * (s / 2)) = -s by ring]
      ring
  have hFi : Integrable F ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure (Euc d))) := by
    refine d1f_integrable_prod hFm (hint.const_mul (Real.Gamma (s / 2))) ?_
    filter_upwards [d1f_ae_ne hd] with x hx using hslice x hx
  have hswap := integral_integral_swap (f := fun (c : ℝ) (x : Euc d) => F (c, x)) hFi
  have hR : ∫ x : Euc d, ∫ c in Ioi (0 : ℝ), F (c, x) =
      Real.Gamma (s / 2) * ∫ ξ : Euc d, ‖ξ‖ ^ (-s) * fdlPsiHat ψ ξ ^ 2 := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [d1f_ae_ne hd] with x hx
    have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hnn : ∀ c ∈ Ioi (0 : ℝ), 0 ≤ F (c, x) := fun c hc =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt hc) _) (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
    rw [← (hslice x hx).2, setIntegral_congr_fun measurableSet_Ioi
      (fun c hc => (Real.norm_of_nonneg (hnn c hc)).symm)]
  have hL : ∫ c in Ioi (0 : ℝ), ∫ x : Euc d, F (c, x) =
      ∫ c in Ioi (0 : ℝ), c ^ (s / 2 - 1) * ((Real.pi / c) ^ ((d : ℝ) / 2) *
        ∫ ξ : Euc d, Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / c) * fdlPhi ψ ξ) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun c hc => ?_)
    have hc' : (0 : ℝ) < c := hc
    simp only [hF]
    rw [integral_const_mul, ← d1f_gauss_mult hψ hc']
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring_nf
  rw [← hR, ← hL]
  exact hswap.symm


theorem d1f_sq_rpow2 {r : ℝ} (hr : 0 ≤ r) (h : ℝ) : (r ^ 2) ^ h = r ^ (2 * h) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hr]
  norm_num

/-- The `c`-integral appearing in the second exchange. -/
theorem d1f_c_integral {s : ℝ} (hsd : s < d) {ξ : Euc d} (hξ : ξ ≠ 0) :
    IntegrableOn (fun c : ℝ => c ^ (s / 2 - 1 - (d : ℝ) / 2) *
      Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / c)) (Ioi 0) ∧
    ∫ c in Ioi (0 : ℝ), c ^ (s / 2 - 1 - (d : ℝ) / 2) * Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / c) =
      Real.pi ^ (s - d) * ‖ξ‖ ^ (s - d) * Real.Gamma (((d : ℝ) - s) / 2) := by
  have hr : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hκ : 0 < Real.pi ^ 2 * ‖ξ‖ ^ 2 := by positivity
  have ha : 0 < ((d : ℝ) - s) / 2 := by linarith
  set P : ℝ → ℝ := fun u => Real.exp (-u) with hP
  have hint : IntegrableOn (fun u : ℝ => u ^ (((d : ℝ) - s) / 2 - 1) * P u) (Ioi 0) := by
    refine (Real.GammaIntegral_convergent ha).congr_fun (fun u _ => ?_) measurableSet_Ioi
    simp only [hP]; ring
  obtain ⟨h1, h2⟩ := d1e_subst_pos P hκ hint
  have hpt : ∀ c : ℝ, c ^ (s / 2 - 1 - (d : ℝ) / 2) * Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / c) =
      c ^ (-(((d : ℝ) - s) / 2) - 1) * P (Real.pi ^ 2 * ‖ξ‖ ^ 2 / c) := by
    intro c
    simp only [hP]
    congr 2
    · ring
    · ring
  simp_rw [hpt]
  refine ⟨h1, ?_⟩
  rw [h2]
  have hG : ∫ u in Ioi (0 : ℝ), u ^ (((d : ℝ) - s) / 2 - 1) * P u = Real.Gamma (((d : ℝ) - s) / 2) := by
    rw [Real.Gamma_eq_integral ha]
    refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    simp only [hP]; ring
  rw [hG, show Real.pi ^ 2 * ‖ξ‖ ^ 2 = (Real.pi * ‖ξ‖) ^ 2 by ring, d1f_sq_rpow2 (by positivity),
    Real.mul_rpow Real.pi_pos.le hr.le]
  rw [show 2 * (-(((d : ℝ) - s) / 2)) = s - (d : ℝ) by ring]


/-- Second exchange. -/
theorem d1f_step2 (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {e : Euc d} (he : ‖e‖ = 1) :
    ∫ c in Ioi (0 : ℝ), c ^ (s / 2 - 1) * ((Real.pi / c) ^ ((d : ℝ) / 2) *
        ∫ ξ : Euc d, Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / c) * fdlPhi ψ ξ) =
      Real.pi ^ (s - (d : ℝ) / 2) * Real.Gamma (((d : ℝ) - s) / 2) *
        ∫ x : Euc d, ‖x‖ ^ (s - d) * fdlPhi ψ x := by
  have hφm : Measurable (fdlPhi ψ) := (d1e_phi_cont hψ).measurable
  set F : ℝ × Euc d → ℝ := fun p => p.1 ^ (s / 2 - 1) * ((Real.pi / p.1) ^ ((d : ℝ) / 2) *
    (Real.exp (-Real.pi ^ 2 * ‖p.2‖ ^ 2 / p.1) * fdlPhi ψ p.2)) with hF
  have hFm : Measurable F := by
    have h1 : Measurable (fun p : ℝ × Euc d => p.1 ^ (s / 2 - 1)) := measurable_fst.pow_const _
    have h2 : Measurable (fun p : ℝ × Euc d => (Real.pi / p.1) ^ ((d : ℝ) / 2)) :=
      (measurable_const.div measurable_fst).pow_const _
    have h3 : Measurable (fun p : ℝ × Euc d => Real.exp (-Real.pi ^ 2 * ‖p.2‖ ^ 2 / p.1)) := by
      refine Real.measurable_exp.comp (Measurable.div ?_ measurable_fst)
      exact measurable_const.mul ((measurable_snd.norm).pow_const 2)
    exact h1.mul (h2.mul (h3.mul (hφm.comp measurable_snd)))
  obtain ⟨_, hint, _⟩ := d1f_phi_polar hd hs hψ he
  set K : ℝ := Real.pi ^ (s - (d : ℝ) / 2) * Real.Gamma (((d : ℝ) - s) / 2) with hK
  have hFpt : ∀ ξ : Euc d, ∀ c : ℝ, 0 < c → F (c, ξ) = (Real.pi ^ ((d : ℝ) / 2) * fdlPhi ψ ξ) *
      (c ^ (s / 2 - 1 - (d : ℝ) / 2) * Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / c)) := by
    intro ξ c hc
    simp only [hF]
    rw [Real.div_rpow Real.pi_pos.le hc.le, Real.rpow_sub hc (s / 2 - 1) ((d : ℝ) / 2)]
    have : 0 < c ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos hc _
    field_simp
  have hslice : ∀ ξ : Euc d, ξ ≠ 0 → IntegrableOn (fun c => F (c, ξ)) (Ioi 0) ∧
      ∫ c in Ioi (0 : ℝ), ‖F (c, ξ)‖ = K * (‖ξ‖ ^ (s - d) * fdlPhi ψ ξ) := by
    intro ξ hξ
    obtain ⟨h1, h2⟩ := d1f_c_integral hsd hξ
    have hnn : ∀ c ∈ Ioi (0 : ℝ), 0 ≤ F (c, ξ) := fun c hc => by
      simp only [hF]
      have hc' : (0 : ℝ) < c := hc
      exact mul_nonneg (Real.rpow_nonneg hc'.le _) (mul_nonneg (Real.rpow_nonneg
        (div_nonneg Real.pi_pos.le hc'.le) _) (mul_nonneg (Real.exp_pos _).le (d1e_phi_nonneg hψ ξ)))
    refine ⟨?_, ?_⟩
    · have h0 : IntegrableOn (fun c : ℝ => (Real.pi ^ ((d : ℝ) / 2) * fdlPhi ψ ξ) *
          (c ^ (s / 2 - 1 - (d : ℝ) / 2) * Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / c))) (Ioi 0) :=
        h1.const_mul _
      exact h0.congr_fun (fun c hc => (hFpt ξ c hc).symm) measurableSet_Ioi
    · rw [setIntegral_congr_fun measurableSet_Ioi (fun c hc => Real.norm_of_nonneg (hnn c hc)),
        setIntegral_congr_fun measurableSet_Ioi (fun c hc => hFpt ξ c hc), integral_const_mul, h2]
      have hpi : Real.pi ^ ((d : ℝ) / 2) * Real.pi ^ (s - (d : ℝ)) = Real.pi ^ (s - (d : ℝ) / 2) := by
        rw [← Real.rpow_add Real.pi_pos]; congr 1; ring
      rw [hK, ← hpi]
      ring
  have hFi : Integrable F ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure (Euc d))) := by
    refine d1f_integrable_prod hFm (hint.const_mul K) ?_
    filter_upwards [d1f_ae_ne hd] with x hx using hslice x hx
  have hswap := integral_integral_swap (f := fun (c : ℝ) (x : Euc d) => F (c, x)) hFi
  have hR : ∫ x : Euc d, ∫ c in Ioi (0 : ℝ), F (c, x) =
      K * ∫ ξ : Euc d, ‖ξ‖ ^ (s - d) * fdlPhi ψ ξ := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [d1f_ae_ne hd] with x hx
    have hnn : ∀ c ∈ Ioi (0 : ℝ), 0 ≤ F (c, x) := fun c hc => by
      simp only [hF]
      have hc' : (0 : ℝ) < c := hc
      exact mul_nonneg (Real.rpow_nonneg hc'.le _) (mul_nonneg (Real.rpow_nonneg
        (div_nonneg Real.pi_pos.le hc'.le) _) (mul_nonneg (Real.exp_pos _).le (d1e_phi_nonneg hψ x)))
    rw [← (hslice x hx).2, setIntegral_congr_fun measurableSet_Ioi
      (fun c hc => (Real.norm_of_nonneg (hnn c hc)).symm)]
  have hL : ∫ c in Ioi (0 : ℝ), ∫ x : Euc d, F (c, x) =
      ∫ c in Ioi (0 : ℝ), c ^ (s / 2 - 1) * ((Real.pi / c) ^ ((d : ℝ) / 2) *
        ∫ ξ : Euc d, Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / c) * fdlPhi ψ ξ) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun c hc => ?_)
    simp only [hF]
    rw [integral_const_mul, integral_const_mul]
  rw [← hL, hswap, hR]


/-- **Packet D1F (`0 < s < d`).**  For any `b > 0` realising the Euclidean representation, the
Fourier-side integral `b ∫_0^∞ t^{d-s} ψ̂(t e)² dt/t` converges and equals `c_{d,s} (2π)^{s-d}`,
the torus Fourier coefficient normalisation. -/
theorem d1f_pos (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (_hb0 : 0 < b)
    (hb : ∀ x : Euc d, x ≠ 0 → Whole.rieszKernel d s x =
        b * ∫ t in Set.Ioi (0 : ℝ), t ^ ((d : ℝ) - s) * fdlPhiScale ψ t x / t)
    {e : Euc d} (he : ‖e‖ = 1) :
    IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - s) * (fdlPsiHat ψ (t • e)) ^ 2 / t) (Set.Ioi 0) ∧
    b * ∫ t in Set.Ioi (0 : ℝ), t ^ ((d : ℝ) - s) * (fdlPsiHat ψ (t • e)) ^ 2 / t =
      rieszConst d s * (2 * Real.pi) ^ (s - (d : ℝ)) := by
  obtain ⟨hJi, _, hA⟩ := d1f_hat_polar hd hs hsd hψ he
  obtain ⟨_, _, hB⟩ := d1f_phi_polar hd hs hψ he
  have hbI := d1f_inv_b hd hs hψ he hb
  have h1 := d1f_step1 hd hs hsd hψ he
  have h2 := d1f_step2 hd hs hsd hψ he
  rw [h2, hA, hB] at h1
  refine ⟨hJi, ?_⟩
  set J := ∫ t in Set.Ioi (0 : ℝ), t ^ ((d : ℝ) - s) * (fdlPsiHat ψ (t • e)) ^ 2 / t with hJ
  set I := ∫ u in Ioi (0 : ℝ), u ^ (s - 1) * fdlPhi ψ (u • e) with hI
  have hω := d1f_omega_pos hd
  have hΓ : 0 < Real.Gamma (s / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hK : b * J = Real.pi ^ (s - (d : ℝ) / 2) * Real.Gamma (((d : ℝ) - s) / 2) /
      Real.Gamma (s / 2) := by
    rw [eq_div_iff hΓ.ne']
    have : d1f_omega d * (b * J * Real.Gamma (s / 2)) =
        d1f_omega d * (Real.pi ^ (s - (d : ℝ) / 2) * Real.Gamma (((d : ℝ) - s) / 2)) := by
      calc d1f_omega d * (b * J * Real.Gamma (s / 2)) = b * (Real.Gamma (s / 2) * (d1f_omega d * J)) := by
            ring
        _ = b * (Real.pi ^ (s - (d : ℝ) / 2) * Real.Gamma (((d : ℝ) - s) / 2) * (d1f_omega d * I)) := by
            rw [h1]
        _ = d1f_omega d * (Real.pi ^ (s - (d : ℝ) / 2) * Real.Gamma (((d : ℝ) - s) / 2)) * (b * I) := by
            ring
        _ = _ := by rw [hbI, mul_one]
    exact mul_left_cancel₀ hω.ne' this
  rw [hK]
  unfold rieszConst
  simp only [hs.ne', ite_false]
  rw [Real.mul_rpow (by norm_num) Real.pi_pos.le]
  have h2s : (2 : ℝ) ^ ((d : ℝ) - s) * (2 : ℝ) ^ (s - (d : ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num)]
    simp
  have hpi : Real.pi ^ ((d : ℝ) / 2) * Real.pi ^ (s - (d : ℝ)) = Real.pi ^ (s - (d : ℝ) / 2) := by
    rw [← Real.rpow_add Real.pi_pos]; congr 1; ring
  rw [← hpi]
  calc Real.pi ^ ((d : ℝ) / 2) * Real.pi ^ (s - (d : ℝ)) * Real.Gamma (((d : ℝ) - s) / 2) /
        Real.Gamma (s / 2)
      = ((2 : ℝ) ^ ((d : ℝ) - s) * (2 : ℝ) ^ (s - (d : ℝ))) * Real.pi ^ ((d : ℝ) / 2) *
        Real.Gamma (((d : ℝ) - s) / 2) / Real.Gamma (s / 2) * Real.pi ^ (s - (d : ℝ)) := by
        rw [h2s]; ring
    _ = _ := by ring

end HRS.MC.D1F
