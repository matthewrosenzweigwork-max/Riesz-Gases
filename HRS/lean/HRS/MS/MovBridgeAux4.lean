import HRS.MS.MovBridgeAux3

/-!
# MOVA3B2, part 1: Fourier rotation and complexification on Schwartz functions

Namespace `HRS.MS.MovOsc`, helpers `mova3b2_`.  Infrastructure for `mo_interp_H_osc` (`MovBridgeAux5`),
the `H → Σ` Stein interpolation: the rotated inputs `⟨D⟩^{2c} f` are Schwartz for every complex `c`.

* `mova3b2_log_tg`, `mova3b2_g_tg`: the multipliers `(1+4π²|ξ|²)^c`, `c ∈ ℂ`, have temperate growth
  (via `Complex.hasTemperateGrowth_exp_mul_I` and the temperate growth of `log (1+|ξ|²)`).
* `mova3b2_rot c`: the Fourier multiplier `W(D)^c` on complex Schwartz functions
  (`SchwartzMap.fourierMultiplierCLM`), with `𝓕 (rot c φ) = W^c 𝓕 φ`.
* `mova3b2_cx`, `mova3b2_re`, `mova3b2_im`: complexification, real and imaginary part of Schwartz maps;
  `mova3b2_sob`: `‖Re φ‖²_{H^r} + ‖Im φ‖²_{H^r} = ∫ W^r |𝓕 φ|²` (and both parts are in `H^r`).
* `mova3b2_Lam Lin`: the complex-linear extension `φ ↦ Lin (Re φ) + i Lin (Im φ)` of a real functional,
  with the bound `mova3b2_Lam_bound`.
-/
noncomputable section

open Filter MeasureTheory
open scoped ContDiff

namespace HRS.MS.MovOsc

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma mova3b2_log_tg : (fun x : H => Real.log (1 + ‖x‖ ^ 2)).HasTemperateGrowth := by
  have hd : ∀ x : H, HasFDerivAt (fun x : H => 1 + ‖x‖ ^ 2) (2 • innerSL ℝ x) x := by
    intro x
    have := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
    simpa using this.const_add 1
  have hpos : ∀ x : H, (1 + ‖x‖ ^ 2) ≠ 0 := fun x => by positivity
  have hlog : ∀ x : H, HasFDerivAt (fun x : H => Real.log (1 + ‖x‖ ^ 2))
      ((1 + ‖x‖ ^ 2)⁻¹ • (2 • innerSL ℝ x)) x := fun x => (hd x).log (hpos x)
  apply Function.HasTemperateGrowth.of_fderiv (C := 1) (k := 2)
  · have : fderiv ℝ (fun x : H => Real.log (1 + ‖x‖ ^ 2)) =
        fun x => (1 + ‖x‖ ^ 2) ^ (-1 : ℝ) • (2 • innerSL ℝ x) := by
      funext x; rw [(hlog x).fderiv, Real.rpow_neg_one]
    rw [this]
    exact (Function.hasTemperateGrowth_one_add_norm_sq_rpow H (-1)).smul
      (by convert (2 • innerSL ℝ (E := H)).hasTemperateGrowth)
  · exact fun x => (hlog x).differentiableAt
  · intro x
    have h0 : 0 ≤ Real.log (1 + ‖x‖ ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg ‖x‖])
    rw [Real.norm_of_nonneg h0]
    have h1 := Real.log_le_sub_one_of_pos (show 0 < 1 + ‖x‖ ^ 2 by positivity)
    nlinarith [norm_nonneg x]
end

open HRS HRS.PDE.ToolboxRd HRS.MS.MovInterp
variable {d : ℕ}

lemma mova3b2_W_eq (ξ : Euc d) : mova3b1_W ξ = 1 + ‖(2 * Real.pi) • ξ‖ ^ 2 := by
  unfold mova3b1_W
  rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
  ring

lemma mova3b2_W_rpow_tg (a : ℝ) : (fun ξ : Euc d => mova3b1_W ξ ^ a).HasTemperateGrowth := by
  have h := (Function.hasTemperateGrowth_one_add_norm_sq_rpow (Euc d) a).comp
    ((2 * Real.pi) • ContinuousLinearMap.id ℝ (Euc d)).hasTemperateGrowth
  convert h using 1
  funext ξ
  simp [mova3b2_W_eq]

lemma mova3b2_L_tg : (fun ξ : Euc d => Real.log (mova3b1_W ξ)).HasTemperateGrowth := by
  have h := (mova3b2_log_tg (H := Euc d)).comp
    ((2 * Real.pi) • ContinuousLinearMap.id ℝ (Euc d)).hasTemperateGrowth
  convert h using 1
  funext ξ
  simp [mova3b2_W_eq]

/-- The multiplier `W^c` (complex power of the Sobolev weight). -/
lemma mova3b2_g_eq (c : ℂ) (ξ : Euc d) :
    ((mova3b1_W ξ : ℝ) : ℂ) ^ c = ((mova3b1_W ξ ^ c.re : ℝ) : ℂ) *
      Complex.exp (((c.im * Real.log (mova3b1_W ξ) : ℝ) : ℂ) * Complex.I) := by
  have hW := mova3b1_W_pos ξ
  have hne : ((mova3b1_W ξ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hW.ne'
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log hW.le, Real.rpow_def_of_pos hW,
    Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

lemma mova3b2_g_tg (c : ℂ) :
    (fun ξ : Euc d => ((mova3b1_W ξ : ℝ) : ℂ) ^ c).HasTemperateGrowth := by
  have h1 : (fun ξ : Euc d => ((mova3b1_W ξ ^ c.re : ℝ) : ℂ)).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_ofReal.comp (mova3b2_W_rpow_tg c.re)
  have h2 : (fun ξ : Euc d => Complex.exp (((c.im * Real.log (mova3b1_W ξ) : ℝ) : ℂ) * Complex.I)).HasTemperateGrowth := by
    have := Complex.hasTemperateGrowth_exp_mul_I.comp
      ((Function.HasTemperateGrowth.const c.im).mul (mova3b2_L_tg (d := d)))
    exact this
  have := h1.mul h2
  convert this using 1
  funext ξ
  exact mova3b2_g_eq c ξ

open scoped FourierTransform ComplexConjugate
local notation "𝓢C" => SchwartzMap (Euc d) ℂ
local notation "𝓢R" => SchwartzMap (Euc d) ℝ

/-- The multiplier `W^c`. -/
def mova3b2_gm (c : ℂ) : Euc d → ℂ := fun ξ => ((mova3b1_W ξ : ℝ) : ℂ) ^ c

/-- The Fourier multiplier `W(D)^c` on complex Schwartz functions. -/
def mova3b2_rot (c : ℂ) : 𝓢C →L[ℂ] 𝓢C :=
  SchwartzMap.fourierMultiplierCLM ℂ (mova3b2_gm (d := d) c)

lemma mova3b2_fourier_rot (c : ℂ) (φ : 𝓢C) (ξ : Euc d) :
    (𝓕 (mova3b2_rot c φ) : 𝓢C) ξ = mova3b2_gm c ξ * (𝓕 φ : 𝓢C) ξ := by
  unfold mova3b2_rot
  rw [SchwartzMap.fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq,
    SchwartzMap.smulLeftCLM_apply_apply (g := mova3b2_gm c) (mova3b2_g_tg c)]
  rfl

lemma mova3b2_rot_zero (φ : 𝓢C) : mova3b2_rot (0 : ℂ) φ = φ := by
  have : mova3b2_gm (d := d) 0 = fun _ => (1 : ℂ) := by
    funext ξ; simp [mova3b2_gm]
  unfold mova3b2_rot
  rw [this, SchwartzMap.fourierMultiplierCLM_const]
  simp

lemma mova3b2_norm_gm (c : ℂ) (ξ : Euc d) : ‖mova3b2_gm c ξ‖ = mova3b1_W ξ ^ c.re := by
  unfold mova3b2_gm
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (mova3b1_W_pos ξ)]

lemma mova3b2_int_W (ψ : 𝓢C) (r : ℝ) :
    Integrable (fun ξ : Euc d => mova3b1_W ξ ^ r * ‖ψ ξ‖ ^ 2) volume := by
  set ψ' : 𝓢C := SchwartzMap.smulLeftCLM ℂ
    (fun ξ : Euc d => ((mova3b1_W ξ ^ (r / 2) : ℝ) : ℂ)) ψ with hψ'
  have hg : (fun ξ : Euc d => ((mova3b1_W ξ ^ (r / 2) : ℝ) : ℂ)).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_ofReal.comp (mova3b2_W_rpow_tg (r / 2))
  have h := (ψ'.memLp 2 volume).norm.integrable_sq
  refine h.congr (Eventually.of_forall fun ξ => ?_)
  simp only [hψ', SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (mova3b1_W_pos ξ).le _)]
  rw [mul_pow, mova3_rpow_half_sq (mova3b1_W_pos ξ)]

open HRS.PDE.ToolboxRd.FourierAux

/-- complexification of a real Schwartz function -/
def mova3b2_cx : 𝓢R →L[ℝ] 𝓢C := SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM
/-- real part -/
def mova3b2_re : 𝓢C →L[ℝ] 𝓢R := SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.reCLM
/-- imaginary part -/
def mova3b2_im : 𝓢C →L[ℝ] 𝓢R := SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.imCLM

@[simp] lemma mova3b2_cx_apply (f : 𝓢R) (x : Euc d) : mova3b2_cx f x = ((f x : ℝ) : ℂ) := rfl
@[simp] lemma mova3b2_re_apply (φ : 𝓢C) (x : Euc d) : mova3b2_re φ x = (φ x).re := rfl
@[simp] lemma mova3b2_im_apply (φ : 𝓢C) (x : Euc d) : mova3b2_im φ x = (φ x).im := rfl

lemma mova3b2_cx_re_eq (φ : 𝓢C) :
    mova3b2_cx (mova3b2_re φ) = (1 / 2 : ℂ) • (φ + conjSchwartz φ) := by
  ext x
  simp only [mova3b2_cx_apply, mova3b2_re_apply, SchwartzMap.smul_apply, SchwartzMap.add_apply,
    conjSchwartz_apply, smul_eq_mul]
  rw [Complex.re_eq_add_conj]; ring

lemma mova3b2_cx_im_eq (φ : 𝓢C) :
    mova3b2_cx (mova3b2_im φ) = (1 / (2 * Complex.I)) • (φ - conjSchwartz φ) := by
  ext x
  simp only [mova3b2_cx_apply, mova3b2_im_apply, SchwartzMap.smul_apply, SchwartzMap.sub_apply,
    conjSchwartz_apply, smul_eq_mul]
  rw [Complex.im_eq_sub_conj]; ring

lemma mova3b2_fourier_re (φ : 𝓢C) (ξ : Euc d) :
    (𝓕 (mova3b2_cx (mova3b2_re φ)) : 𝓢C) ξ =
      ((𝓕 φ : 𝓢C) ξ + conj ((𝓕 φ : 𝓢C) (-ξ))) / 2 := by
  rw [mova3b2_cx_re_eq, FourierTransform.fourier_smul, FourierTransform.fourier_add,
    SchwartzMap.smul_apply, SchwartzMap.add_apply, fourier_conjSchwartz, smul_eq_mul]
  ring

lemma mova3b2_fourier_im (φ : 𝓢C) (ξ : Euc d) :
    (𝓕 (mova3b2_cx (mova3b2_im φ)) : 𝓢C) ξ =
      ((𝓕 φ : 𝓢C) ξ - conj ((𝓕 φ : 𝓢C) (-ξ))) / (2 * Complex.I) := by
  rw [mova3b2_cx_im_eq, FourierTransform.fourier_smul, sub_eq_add_neg,
    FourierTransform.fourier_add, ← neg_one_smul ℂ (conjSchwartz φ), FourierTransform.fourier_smul,
    SchwartzMap.smul_apply, SchwartzMap.add_apply, SchwartzMap.smul_apply, fourier_conjSchwartz,
    smul_eq_mul, smul_eq_mul]
  ring

lemma mova3b2_fourierL2_eq (u : 𝓢R) :
    fourierL2 (⇑u) =ᵐ[volume] fun ξ => (𝓕 (mova3b2_cx u) : 𝓢C) ξ := by
  filter_upwards [fourierL2_schwartz u] with ξ h
  rw [h]; rfl

lemma mova3b2_sob (φ : 𝓢C) (r : ℝ) :
    HRS.PDE.ToolboxRd.MemSobolev r (⇑(mova3b2_re φ)) ∧ HRS.PDE.ToolboxRd.MemSobolev r (⇑(mova3b2_im φ)) ∧
      HRS.PDE.ToolboxRd.sobolevNormSq r (⇑(mova3b2_re φ)) + HRS.PDE.ToolboxRd.sobolevNormSq r (⇑(mova3b2_im φ)) =
        ∫ ξ, mova3b1_W ξ ^ r * ‖(𝓕 φ : 𝓢C) ξ‖ ^ 2 := by
  have hI : ∀ u : 𝓢R, Integrable (fun ξ : Euc d => mova3b1_W ξ ^ r * ‖fourierL2 (⇑u) ξ‖ ^ 2) volume := by
    intro u
    refine (mova3b2_int_W (𝓕 (mova3b2_cx u) : 𝓢C) r).congr ?_
    filter_upwards [mova3b2_fourierL2_eq u] with ξ h
    rw [h]
  have hE : ∀ u : 𝓢R, HRS.PDE.ToolboxRd.sobolevNormSq r (⇑u) =
      ∫ ξ, mova3b1_W ξ ^ r * ‖(𝓕 (mova3b2_cx u) : 𝓢C) ξ‖ ^ 2 := by
    intro u
    rw [mova3b1_sobolevNormSq_eq]
    refine integral_congr_ae ?_
    filter_upwards [mova3b2_fourierL2_eq u] with ξ h
    rw [h]
  refine ⟨⟨(mova3b2_re φ).memLp 2 volume, hI _⟩, ⟨(mova3b2_im φ).memLp 2 volume, hI _⟩, ?_⟩
  rw [hE, hE]
  have hA := mova3b2_int_W (𝓕 φ : 𝓢C) r
  have hA' : Integrable (fun ξ : Euc d => mova3b1_W ξ ^ r * ‖(𝓕 φ : 𝓢C) (-ξ)‖ ^ 2) volume := by
    have := hA.comp_neg (μ := (volume : Measure (Euc d)))
    refine this.congr (Eventually.of_forall fun ξ => ?_)
    simp [mova3b1_W_neg]
  have hre := mova3b2_int_W (𝓕 (mova3b2_cx (mova3b2_re φ)) : 𝓢C) r
  have him := mova3b2_int_W (𝓕 (mova3b2_cx (mova3b2_im φ)) : 𝓢C) r
  rw [← integral_add hre him]
  have hpt : ∀ ξ : Euc d, mova3b1_W ξ ^ r * ‖(𝓕 (mova3b2_cx (mova3b2_re φ)) : 𝓢C) ξ‖ ^ 2 +
      mova3b1_W ξ ^ r * ‖(𝓕 (mova3b2_cx (mova3b2_im φ)) : 𝓢C) ξ‖ ^ 2 =
      (mova3b1_W ξ ^ r * ‖(𝓕 φ : 𝓢C) ξ‖ ^ 2 + mova3b1_W ξ ^ r * ‖(𝓕 φ : 𝓢C) (-ξ)‖ ^ 2) / 2 := by
    intro ξ
    rw [mova3b2_fourier_re, mova3b2_fourier_im]
    have e1 : ‖(((𝓕 φ : 𝓢C) ξ + conj ((𝓕 φ : 𝓢C) (-ξ))) / 2)‖ ^ 2 +
        ‖(((𝓕 φ : 𝓢C) ξ - conj ((𝓕 φ : 𝓢C) (-ξ))) / (2 * Complex.I))‖ ^ 2 =
        (‖(𝓕 φ : 𝓢C) ξ‖ ^ 2 + ‖(𝓕 φ : 𝓢C) (-ξ)‖ ^ 2) / 2 := by
      simp only [norm_div, div_pow, norm_mul, Complex.norm_I, Complex.norm_conj, Complex.sq_norm,
        Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        Complex.conj_re, Complex.conj_im]
      norm_num
      ring
    rw [← mul_add, e1]; ring
  simp_rw [hpt]
  rw [integral_div, integral_add hA hA']
  have : ∫ ξ : Euc d, mova3b1_W ξ ^ r * ‖(𝓕 φ : 𝓢C) (-ξ)‖ ^ 2 =
      ∫ ξ : Euc d, mova3b1_W ξ ^ r * ‖(𝓕 φ : 𝓢C) ξ‖ ^ 2 := by
    have := integral_neg_eq_self (fun ξ : Euc d => mova3b1_W ξ ^ r * ‖(𝓕 φ : 𝓢C) ξ‖ ^ 2)
      (volume : Measure (Euc d))
    simpa [mova3b1_W_neg] using this
  rw [this]; ring

/-- The complexification of a real-linear functional on real Schwartz functions. -/
def mova3b2_Lam (Lin : 𝓢R →ₗ[ℝ] ℝ) : 𝓢C →ₗ[ℂ] ℂ where
  toFun φ := ((Lin (mova3b2_re φ) : ℝ) : ℂ) + Complex.I * ((Lin (mova3b2_im φ) : ℝ) : ℂ)
  map_add' φ ψ := by simp only [map_add, Complex.ofReal_add]; ring
  map_smul' c φ := by
    have h1 : mova3b2_re (c • φ) = c.re • mova3b2_re φ - c.im • mova3b2_im φ := by
      ext x; simp [Complex.mul_re]
    have h2 : mova3b2_im (c • φ) = c.re • mova3b2_im φ + c.im • mova3b2_re φ := by
      ext x; simp [Complex.mul_im]
    simp only [h1, h2, map_sub, map_add, map_smul, smul_eq_mul, RingHom.id_apply,
      Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

lemma mova3b2_Lam_apply (Lin : 𝓢R →ₗ[ℝ] ℝ) (φ : 𝓢C) :
    mova3b2_Lam Lin φ = ((Lin (mova3b2_re φ) : ℝ) : ℂ) + Complex.I * ((Lin (mova3b2_im φ) : ℝ) : ℂ) :=
  rfl

lemma mova3b2_norm_Lam_sq (Lin : 𝓢R →ₗ[ℝ] ℝ) (φ : 𝓢C) :
    ‖mova3b2_Lam Lin φ‖ ^ 2 = Lin (mova3b2_re φ) ^ 2 + Lin (mova3b2_im φ) ^ 2 := by
  rw [mova3b2_Lam_apply, Complex.sq_norm, Complex.normSq_apply]
  simp; ring

lemma mova3b2_sobolevNormSq_nonneg (r : ℝ) (u : Euc d → ℝ) : 0 ≤ HRS.PDE.ToolboxRd.sobolevNormSq r u :=
  integral_nonneg fun ξ => mul_nonneg (Real.rpow_nonneg (mova3b1_W_pos ξ).le _) (sq_nonneg _)

lemma mova3b2_Lam_bound (Lin : 𝓢R →ₗ[ℝ] ℝ) {K r : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ u : 𝓢R, |Lin u| ≤ K * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq r (⇑u))) (φ : 𝓢C) :
    ‖mova3b2_Lam Lin φ‖ ≤ K * Real.sqrt (∫ ξ, mova3b1_W ξ ^ r * ‖(𝓕 φ : 𝓢C) ξ‖ ^ 2) := by
  obtain ⟨_, _, hsum⟩ := mova3b2_sob φ r
  rw [← hsum]
  have h1 := hK (mova3b2_re φ)
  have h2 := hK (mova3b2_im φ)
  have n1 := mova3b2_sobolevNormSq_nonneg r (⇑(mova3b2_re φ))
  have n2 := mova3b2_sobolevNormSq_nonneg r (⇑(mova3b2_im φ))
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [mova3b2_norm_Lam_sq, mul_pow, Real.sq_sqrt (add_nonneg n1 n2)]
  have a1 : Lin (mova3b2_re φ) ^ 2 ≤ K ^ 2 * HRS.PDE.ToolboxRd.sobolevNormSq r (⇑(mova3b2_re φ)) := by
    have := sq_le_sq' (neg_le_of_abs_le (h1.trans le_rfl)) (le_of_abs_le h1)
    rw [mul_pow, Real.sq_sqrt n1] at this; exact this
  have a2 : Lin (mova3b2_im φ) ^ 2 ≤ K ^ 2 * HRS.PDE.ToolboxRd.sobolevNormSq r (⇑(mova3b2_im φ)) := by
    have := sq_le_sq' (neg_le_of_abs_le (h2.trans le_rfl)) (le_of_abs_le h2)
    rw [mul_pow, Real.sq_sqrt n2] at this; exact this
  nlinarith

end HRS.MS.MovOsc
