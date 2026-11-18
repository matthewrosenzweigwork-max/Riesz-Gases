import HRS.MS.CzMikAux4
import HRS.Commutator.Whole.XBBAux10

/-!
# MIK-2, part 1: the Mikhlin multiplier bound on Schwartz functions

Packet MIK-2 (extension of `mikhlin_localised` to Schwartz data and then to `L^p`, CZ development).

For a symbol `m` with `mik1_IsMikhlin d A m` (smooth off `0`, `‖D^i m ξ‖ ≤ A ‖ξ‖^{-i}` for `i ≤ d+1`) and a
Schwartz function `u`, the multiplier operator is `mik2_T m u = 𝓕⁻ (m · 𝓕 u)`.  This is an honest
(absolutely convergent) Fourier integral: `‖m‖ ≤ A` off `0` and `𝓕 u` is Schwartz, so `m · 𝓕 u` is integrable
(`mik2_integrable`); no junk values are involved.

**Main statement** (`mikhlin_Lp_schwartz`).  For `d ≥ 1`, `1 < p`, there is `C < ∞` (depending only on
`d, p`) such that for all `A ≥ 0`, all Mikhlin symbols `m` with constant `A` and all Schwartz `u`,
`∫ ‖mik2_T m u‖^p ≤ C A^p ∫ ‖u‖^p` (lintegrals in `ℝ≥0∞`, so both sides are meaningful without any
finiteness assumption).

Proof: for `n : ℕ` let `χ_n = cutC(2^{-n} ·) - cutC(2^n ·)`, a smooth compactly supported symbol vanishing for
`‖ξ‖ ≤ 2^{-n}` and `‖ξ‖ ≥ 2^{n+1}`, `χ_n → 1` off `0`.  `u_n = 𝓕⁻(χ_n 𝓕 u)` is Schwartz with Fourier support in
the annulus and `R_n = 𝓕⁻(m χ_n 𝓕 u)` is Schwartz, `𝓕 R_n = m 𝓕 u_n`; `mikhlin_localised` gives
`∫ |R_n|^p ≤ C A^p ∫ |u_n|^p`.  Young's inequality with the uniformly integrable kernels `xbbK n - xbbK (-n)`
gives `∫ |u_n|^p ≤ (2 A₁)^p ∫ |u|^p`; dominated convergence gives `R_n → mik2_T m u` pointwise, and Fatou
closes the argument.

Adjustments relative to the plan sketch: the Mikhlin class is `mik1_IsMikhlin` (smoothness `ContDiffAt ℝ ∞`);
`T_m u` is stated as the explicit Fourier integral `mik2_T m u`, so that the a.e. defined `L^p` extension
(file `CzMikExtAux2.lean`) is anchored to a concrete function.
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section
namespace HRS.CZ.Mik
open HRS.Commutator.Whole HRS.Commutator.Whole.XLI HRS.Commutator.Whole.XNRS HRS.Commutator.Whole.XBB
variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- the multiplier operator on Schwartz functions: `T_m u = 𝓕⁻ (m · 𝓕 u)` -/
def mik2_T (m : 𝔼 → ℂ) (u : 𝓢(𝔼, ℂ)) : 𝔼 → ℂ := 𝓕⁻ (fun ξ => m ξ * 𝓕 (⇑u) ξ)

lemma mik2_norm_le {A : ℝ} {m : 𝔼 → ℂ} (hm : mik1_IsMikhlin d A m) {ξ : 𝔼} (hξ : ξ ≠ 0) :
    ‖m ξ‖ ≤ A := by
  have := hm.2 0 (Nat.zero_le _) ξ hξ
  simpa using this

lemma mik2_nontrivial (hd : 1 ≤ d) : Nontrivial 𝔼 := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact inferInstance

lemma mik2_ae_ne (hd : 1 ≤ d) : ∀ᵐ ξ : 𝔼 ∂(volume : Measure 𝔼), ξ ≠ 0 := by
  have := mik2_nontrivial hd
  exact Measure.ae_ne _ _

lemma mik2_aesm (hd : 1 ≤ d) {A : ℝ} {m : 𝔼 → ℂ} (hm : mik1_IsMikhlin d A m) :
    AEStronglyMeasurable m (volume : Measure 𝔼) := by
  have := mik2_nontrivial hd
  have hc : ContinuousOn m ({0}ᶜ : Set 𝔼) := fun ξ hξ => (hm.1 ξ hξ).continuousAt.continuousWithinAt
  have := hc.aestronglyMeasurable (measurableSet_singleton (0 : 𝔼)).compl (μ := (volume : Measure 𝔼))
  rwa [restrict_compl_singleton] at this

lemma mik2_fourier_integrable (u : 𝓢(𝔼, ℂ)) : Integrable (𝓕 (⇑u)) (volume : Measure 𝔼) := by
  rw [← SchwartzMap.fourier_coe]; exact (𝓕 u).integrable

lemma mik2_integrable (hd : 1 ≤ d) {A : ℝ} {m : 𝔼 → ℂ} (hm : mik1_IsMikhlin d A m) (u : 𝓢(𝔼, ℂ)) :
    Integrable (fun ξ => m ξ * 𝓕 (⇑u) ξ) (volume : Measure 𝔼) :=
  (mik2_fourier_integrable u).bdd_mul (c := A) (mik2_aesm hd hm)
    ((mik2_ae_ne hd).mono fun _ hξ => mik2_norm_le hm hξ)

/-! ### The Fourier cutoffs -/

/-- the band symbol `χ_n = cutC(2^{-n} ·) - cutC(2^n ·)` -/
def mik2_chi (n : ℕ) (ξ : 𝔼) : ℂ :=
  cutC (((2 : ℝ) ^ (n : ℤ))⁻¹ • ξ) - cutC (((2 : ℝ) ^ (-(n : ℤ)))⁻¹ • ξ)

lemma mik2_norm_smul_inv (j : ℤ) (ξ : 𝔼) : ‖((2 : ℝ) ^ j)⁻¹ • ξ‖ = ((2 : ℝ) ^ j)⁻¹ * ‖ξ‖ := by
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (zpow_pos (by norm_num) j).le)]

lemma mik2_chi_contDiff (n : ℕ) : ContDiff ℝ ∞ (mik2_chi n : 𝔼 → ℂ) :=
  (symbol_contDiff cutC_contDiff (n : ℤ)).sub (symbol_contDiff cutC_contDiff (-(n : ℤ)))

lemma mik2_chi_cs (n : ℕ) : HasCompactSupport (mik2_chi n : 𝔼 → ℂ) :=
  (symbol_cs cutC_cs (n : ℤ)).sub (symbol_cs cutC_cs (-(n : ℤ)))

lemma mik2_chi_norm_le (n : ℕ) (ξ : 𝔼) : ‖mik2_chi n ξ‖ ≤ 1 := by
  unfold mik2_chi cutC
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [cut_nonneg (((2 : ℝ) ^ (n : ℤ))⁻¹ • ξ), cut_le_one (((2 : ℝ) ^ (n : ℤ))⁻¹ • ξ),
    cut_nonneg (((2 : ℝ) ^ (-(n : ℤ)))⁻¹ • ξ), cut_le_one (((2 : ℝ) ^ (-(n : ℤ)))⁻¹ • ξ)]

lemma mik2_chi_zero_low (n : ℕ) {ξ : 𝔼} (h : ‖ξ‖ ≤ ((2 : ℝ) ^ n)⁻¹) : mik2_chi n ξ = 0 := by
  have h2n : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hinv : ((2 : ℝ) ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h2n
  have e1 : cutC (((2 : ℝ) ^ (n : ℤ))⁻¹ • ξ) = 1 := by
    refine cutC_eq_one_of_le ?_
    rw [mik2_norm_smul_inv, zpow_natCast]
    calc ((2 : ℝ) ^ n)⁻¹ * ‖ξ‖ ≤ 1 * 1 := by
          gcongr
          exact h.trans hinv
      _ = 1 := one_mul 1
  have e2 : cutC (((2 : ℝ) ^ (-(n : ℤ)))⁻¹ • ξ) = 1 := by
    refine cutC_eq_one_of_le ?_
    rw [mik2_norm_smul_inv, zpow_neg, zpow_natCast, inv_inv]
    calc (2 : ℝ) ^ n * ‖ξ‖ ≤ (2 : ℝ) ^ n * ((2 : ℝ) ^ n)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hpos.ne'
  unfold mik2_chi; rw [e1, e2]; simp

lemma mik2_chi_zero_high (n : ℕ) {ξ : 𝔼} (h : (2 : ℝ) ^ (n + 1) ≤ ‖ξ‖) : mik2_chi n ξ = 0 := by
  have h2n : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hp1 : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by ring
  have e1 : cutC (((2 : ℝ) ^ (n : ℤ))⁻¹ • ξ) = 0 := by
    refine cutC_eq_zero_of_ge ?_
    rw [mik2_norm_smul_inv, zpow_natCast]
    rw [hp1] at h
    calc (2 : ℝ) = ((2 : ℝ) ^ n)⁻¹ * (2 * (2 : ℝ) ^ n) := by field_simp
      _ ≤ ((2 : ℝ) ^ n)⁻¹ * ‖ξ‖ := by gcongr
  have e2 : cutC (((2 : ℝ) ^ (-(n : ℤ)))⁻¹ • ξ) = 0 := by
    refine cutC_eq_zero_of_ge ?_
    rw [mik2_norm_smul_inv, zpow_neg, zpow_natCast, inv_inv]
    rw [hp1] at h
    calc (2 : ℝ) = 1 * 2 := by ring
      _ ≤ (2 : ℝ) ^ n * (2 * (2 : ℝ) ^ n) := by
          gcongr
          nlinarith
      _ ≤ (2 : ℝ) ^ n * ‖ξ‖ := by gcongr
  unfold mik2_chi; rw [e1, e2]; simp

lemma mik2_chi_eventually_one {ξ : 𝔼} (hξ : ξ ≠ 0) : ∀ᶠ n : ℕ in atTop, mik2_chi n ξ = 1 := by
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hev := (tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℝ)) one_lt_two).eventually_ge_atTop
    (max ‖ξ‖ (2 / ‖ξ‖))
  filter_upwards [hev] with n hn2
  have h1 : ‖ξ‖ ≤ (2 : ℝ) ^ n := (le_max_left _ _).trans hn2
  have h2 : 2 / ‖ξ‖ ≤ (2 : ℝ) ^ n := (le_max_right _ _).trans hn2
  have e1 : cutC (((2 : ℝ) ^ (n : ℤ))⁻¹ • ξ) = 1 := by
    refine cutC_eq_one_of_le ?_
    rw [mik2_norm_smul_inv, zpow_natCast]
    calc ((2 : ℝ) ^ n)⁻¹ * ‖ξ‖ ≤ ((2 : ℝ) ^ n)⁻¹ * (2 : ℝ) ^ n := by gcongr
      _ = 1 := inv_mul_cancel₀ (by positivity)
  have e2 : cutC (((2 : ℝ) ^ (-(n : ℤ)))⁻¹ • ξ) = 0 := by
    refine cutC_eq_zero_of_ge ?_
    rw [mik2_norm_smul_inv, zpow_neg, zpow_natCast, inv_inv]
    have : 2 ≤ (2 : ℝ) ^ n * ‖ξ‖ := by
      rw [div_le_iff₀ hn] at h2; exact h2
    exact this
  unfold mik2_chi; rw [e1, e2]; simp

/-! ### The Schwartz approximants `u_n`, `R_n` -/

/-- the Schwartz function with Fourier transform `cutC(2^{-j} ·) 𝓕 u` -/
def mik2_Ln (j : ℤ) (u : 𝓢(𝔼, ℂ)) : 𝓢(𝔼, ℂ) :=
  mulS (fun ξ => cutC (((2 : ℝ) ^ j)⁻¹ • ξ)) (temperate_symbol cutC_contDiff cutC_cs j) u

lemma mik2_Ln_coe (j : ℤ) (u : 𝓢(𝔼, ℂ)) : ⇑(mik2_Ln j u) = cv (⇑(xbbK j)) ⇑u := by
  rw [xbbK_coe, cv_symK_eq_mulS cutC_contDiff cutC_cs u j]; rfl

/-- the band-limited approximant `u_n = 𝓕⁻(χ_n 𝓕 u)` -/
def mik2_un (n : ℕ) (u : 𝓢(𝔼, ℂ)) : 𝓢(𝔼, ℂ) := mik2_Ln (n : ℤ) u - mik2_Ln (-(n : ℤ)) u

lemma mik2_un_fourier (n : ℕ) (u : 𝓢(𝔼, ℂ)) (ξ : 𝔼) :
    𝓕 (⇑(mik2_un n u)) ξ = mik2_chi n ξ * 𝓕 (⇑u) ξ := by
  unfold mik2_un
  rw [xbb_fourier_sub]
  simp only [mik2_Ln, fourier_mulS, mik2_chi]
  ring

lemma mik2_un_fourier_zero (n : ℕ) (u : 𝓢(𝔼, ℂ)) {ξ : 𝔼}
    (h : ‖ξ‖ < ((2 : ℝ) ^ n)⁻¹ ∨ (2 : ℝ) ^ (n + 1) < ‖ξ‖) : 𝓕 (⇑(mik2_un n u)) ξ = 0 := by
  rw [mik2_un_fourier]
  rcases h with h | h
  · rw [mik2_chi_zero_low n h.le, zero_mul]
  · rw [mik2_chi_zero_high n h.le, zero_mul]

lemma mik2_theta_contDiff {A : ℝ} {m : 𝔼 → ℂ} (hm : mik1_IsMikhlin d A m) (n : ℕ) :
    ContDiff ℝ ∞ (fun ξ : 𝔼 => m ξ * mik2_chi n ξ) := by
  have hr : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := by positivity
  refine cmxMY_contDiff_of_away_real hr (fun η hη => ?_) (fun η hη => ?_)
  · exact (hm.1 η hη).mul (mik2_chi_contDiff n).contDiffAt
  · rw [mik2_chi_zero_low n hη.le, mul_zero]

lemma mik2_theta_cs (m : 𝔼 → ℂ) (n : ℕ) : HasCompactSupport (fun ξ : 𝔼 => m ξ * mik2_chi n ξ) :=
  (mik2_chi_cs n).mul_left

/-- the Schwartz function `R_n = 𝓕⁻(m χ_n 𝓕 u)` -/
def mik2_Rn {A : ℝ} {m : 𝔼 → ℂ} (hm : mik1_IsMikhlin d A m) (n : ℕ) (u : 𝓢(𝔼, ℂ)) : 𝓢(𝔼, ℂ) :=
  xbbMul (mik2_theta_contDiff hm n) (mik2_theta_cs m n) u

lemma mik2_Rn_fourier {A : ℝ} {m : 𝔼 → ℂ} (hm : mik1_IsMikhlin d A m) (n : ℕ) (u : 𝓢(𝔼, ℂ)) (ξ : 𝔼) :
    𝓕 (⇑(mik2_Rn hm n u)) ξ = m ξ * 𝓕 (⇑(mik2_un n u)) ξ := by
  unfold mik2_Rn
  rw [fourier_xbbMul, mik2_un_fourier]
  ring

lemma mik2_Rn_apply {A : ℝ} {m : 𝔼 → ℂ} (hm : mik1_IsMikhlin d A m) (n : ℕ) (u : 𝓢(𝔼, ℂ)) (x : 𝔼) :
    mik2_Rn hm n u x = 𝓕⁻ (fun ξ => (m ξ * mik2_chi n ξ) * 𝓕 (⇑u) ξ) x := by
  unfold mik2_Rn xbbMul
  rw [mulS_apply]

/-- pointwise convergence `R_n → T_m u` -/
lemma mik2_Rn_tendsto (hd : 1 ≤ d) {A : ℝ} {m : 𝔼 → ℂ} (hm : mik1_IsMikhlin d A m) (u : 𝓢(𝔼, ℂ))
    (x : 𝔼) : Tendsto (fun n : ℕ => mik2_Rn hm n u x) atTop (𝓝 (mik2_T m u x)) := by
  simp_rw [mik2_Rn_apply]
  unfold mik2_T
  simp_rw [Real.fourierInv_eq']
  refine tendsto_integral_of_dominated_convergence (fun ξ => A * ‖𝓕 (⇑u) ξ‖) ?_ ?_ ?_ ?_
  · intro n
    have hc : Continuous (fun ξ : 𝔼 => (m ξ * mik2_chi n ξ) * 𝓕 (⇑u) ξ) := by
      have h1 := (mik2_theta_contDiff hm n).continuous
      have h2 : Continuous (𝓕 (⇑u)) := by rw [← SchwartzMap.fourier_coe]; exact (𝓕 u).continuous
      exact h1.mul h2
    have hexp : Continuous (fun ξ : 𝔼 =>
        Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I)) := by fun_prop
    exact hexp.aestronglyMeasurable.smul hc.aestronglyMeasurable
  · exact (mik2_fourier_integrable u).norm.const_mul A
  · intro n
    filter_upwards [mik2_ae_ne hd] with ξ hξ
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul, norm_mul]
    have h1 := mik2_norm_le hm hξ
    have h2 := mik2_chi_norm_le n ξ
    have hA : 0 ≤ A := (norm_nonneg _).trans h1
    calc ‖m ξ‖ * ‖mik2_chi n ξ‖ * ‖𝓕 (⇑u) ξ‖ ≤ A * 1 * ‖𝓕 (⇑u) ξ‖ := by gcongr
      _ = A * ‖𝓕 (⇑u) ξ‖ := by rw [mul_one]
  · filter_upwards [mik2_ae_ne hd] with ξ hξ
    refine Tendsto.const_smul ?_ _
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [mik2_chi_eventually_one hξ] with n hn
    rw [hn, mul_one]

/-! ### Young's inequality and the uniform bound for `u_n` -/

/-- Young: `‖K ⋆ u‖_p ≤ ‖K‖₁ ‖u‖_p` in the `lintegral` form -/
lemma mik2_young {K u : 𝔼 → ℂ} (hK : Measurable K) (hu : Measurable u) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ x, ‖cv K u x‖ₑ ^ p ≤ (∫⁻ z, ‖K z‖ₑ) ^ p * ∫⁻ x, ‖u x‖ₑ ^ p := by
  have hp0 : 0 ≤ p := by linarith
  calc ∫⁻ x, ‖cv K u x‖ₑ ^ p ≤ ∫⁻ x, (∫⁻ z, ‖K z‖ₑ * ‖u (x - z)‖ₑ) ^ p :=
        lintegral_mono fun x => ENNReal.rpow_le_rpow (enorm_cv_le K u x) hp0
    _ ≤ (∫⁻ z, ‖K z‖ₑ) ^ p * ∫⁻ x, ‖u x‖ₑ ^ p :=
        young_lintegral (a := fun z => ‖K z‖ₑ) (b := fun x => ‖u x‖ₑ) hK.enorm hu.enorm hp

lemma mik2_schwartz_bdd (u : 𝓢(𝔼, ℂ)) : ∃ L : ℝ, ∀ x, ‖u x‖ ≤ L := by
  obtain ⟨B, -, hB⟩ := u.decay 0 0
  exact ⟨B, fun x => by simpa using hB x⟩

lemma mik2_un_coe (n : ℕ) (u : 𝓢(𝔼, ℂ)) :
    ⇑(mik2_un n u) = cv (fun y => xbbK (n : ℤ) y - xbbK (-(n : ℤ)) y) ⇑u := by
  funext x
  obtain ⟨L, hL⟩ := mik2_schwartz_bdd u
  rw [xbb_cv_sub (xbbK _).integrable (xbbK _).integrable u.continuous.aestronglyMeasurable hL x]
  unfold mik2_un
  rw [SchwartzMap.sub_apply, mik2_Ln_coe, mik2_Ln_coe]

lemma mik2_un_lintegral {A1 : ℝ≥0∞} (hK : ∀ j : ℤ, ∫⁻ y : 𝔼, ‖xbbK j y‖ₑ ≤ A1) {p : ℝ} (hp : 1 ≤ p)
    (n : ℕ) (u : 𝓢(𝔼, ℂ)) :
    ∫⁻ x, ‖mik2_un n u x‖ₑ ^ p ≤ (2 * A1) ^ p * ∫⁻ x, ‖u x‖ₑ ^ p := by
  have hp0 : 0 ≤ p := by linarith
  have hKm : Measurable (fun y : 𝔼 => xbbK (n : ℤ) y - xbbK (-(n : ℤ)) y) :=
    ((xbbK _).continuous.sub (xbbK _).continuous).measurable
  have h1 := mik2_young hKm u.continuous.measurable hp
  rw [mik2_un_coe]
  refine h1.trans ?_
  gcongr
  calc ∫⁻ z, ‖xbbK (n : ℤ) z - xbbK (-(n : ℤ)) z‖ₑ
      ≤ ∫⁻ z, (‖xbbK (n : ℤ) z‖ₑ + ‖xbbK (-(n : ℤ)) z‖ₑ) := lintegral_mono fun z => enorm_sub_le
    _ = (∫⁻ z, ‖xbbK (n : ℤ) z‖ₑ) + ∫⁻ z, ‖xbbK (-(n : ℤ)) z‖ₑ :=
        lintegral_add_left (xbbK _).continuous.measurable.enorm _
    _ ≤ A1 + A1 := add_le_add (hK _) (hK _)
    _ = 2 * A1 := (two_mul A1).symm

/-! ### The main theorem -/

/-- **`mikhlin_Lp_schwartz`** (MIK-2, Schwartz case of the Mikhlin multiplier theorem): for `d ≥ 1`, `1 < p`
there is `C < ∞` such that for every Mikhlin symbol `m` of constant `A` and every Schwartz `u`,
`∫ ‖T_m u‖^p ≤ C A^p ∫ ‖u‖^p`, where `T_m u = 𝓕⁻(m 𝓕 u)` is the (absolutely convergent) Fourier integral
`mik2_T m u`. -/
theorem mikhlin_Lp_schwartz (hd : 1 ≤ d) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (A : ℝ) (m : 𝔼 → ℂ), 0 ≤ A → mik1_IsMikhlin d A m →
      ∀ u : 𝓢(𝔼, ℂ),
        ∫⁻ x, ‖mik2_T m u x‖ₑ ^ p ≤ C * ENNReal.ofReal A ^ p * ∫⁻ x, ‖u x‖ₑ ^ p := by
  obtain ⟨C0, hC0, hloc⟩ := mikhlin_localised hd hp
  obtain ⟨A1, hA1, hK⟩ := xbbK_lintegral_le d
  have hp0 : 0 ≤ p := by linarith
  refine ⟨C0 * (2 * A1) ^ p, ENNReal.mul_ne_top hC0
    (ENNReal.rpow_ne_top_of_nonneg hp0 (ENNReal.mul_ne_top (by simp) hA1)), ?_⟩
  intro A m hA hm u
  have hmeas : ∀ n : ℕ, Measurable (fun x => ‖mik2_Rn hm n u x‖ₑ ^ p) := fun n =>
    ((mik2_Rn hm n u).continuous.measurable.enorm).pow_const p
  calc ∫⁻ x, ‖mik2_T m u x‖ₑ ^ p ≤ ∫⁻ x, liminf (fun n : ℕ => ‖mik2_Rn hm n u x‖ₑ ^ p) atTop := by
        refine lintegral_mono fun x => ?_
        have ht : Tendsto (fun n : ℕ => ‖mik2_Rn hm n u x‖ₑ ^ p) atTop (𝓝 (‖mik2_T m u x‖ₑ ^ p)) :=
          (ENNReal.continuous_rpow_const.tendsto _).comp
            ((continuous_enorm.tendsto _).comp (mik2_Rn_tendsto hd hm u x))
        rw [ht.liminf_eq]
    _ ≤ liminf (fun n : ℕ => ∫⁻ x, ‖mik2_Rn hm n u x‖ₑ ^ p) atTop := lintegral_liminf_le hmeas
    _ ≤ C0 * ENNReal.ofReal A ^ p * ((2 * A1) ^ p * ∫⁻ x, ‖u x‖ₑ ^ p) := by
        refine liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_)
        have h1 := hloc A m hA hm (mik2_un n u) (mik2_Rn hm n u) (((2 : ℝ) ^ n)⁻¹) ((2 : ℝ) ^ (n + 1))
          (by positivity) (fun ξ hξ => mik2_un_fourier_zero n u hξ) (mik2_Rn_fourier hm n u)
        refine h1.trans ?_
        gcongr
        exact mik2_un_lintegral hK hp.le n u
    _ = C0 * (2 * A1) ^ p * ENNReal.ofReal A ^ p * ∫⁻ x, ‖u x‖ₑ ^ p := by ring

end HRS.CZ.Mik
