import HRS.Commutator.Whole.LocalAuxSAMP2Sob
import HRS.Commutator.Whole.ExternalAuxHLS5

/-!
# CMX-SAMP (`potentialSobolev`), part 4: the regularised Schwartz approximants
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole.SAMP2

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

lemma contDiff_of_away_real' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Euc d → E}
    {r : ℝ} (hr : 0 < r) (hf : ∀ η : Euc d, η ≠ 0 → ContDiffAt ℝ ∞ f η)
    (hz : ∀ η : Euc d, ‖η‖ < r → f η = 0) : ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro η
  by_cases h : η = 0
  · subst h
    have : f =ᶠ[𝓝 (0 : Euc d)] fun _ => (0 : E) := by
      filter_upwards [Metric.ball_mem_nhds (0 : Euc d) hr] with y hy
      exact hz y (by simpa using hy)
    exact contDiffAt_const.congr_of_eventuallyEq this
  · exact hf η h

lemma contDiff_sfourier (σ : SMeas d) (h : IsAdmissible σ) : ContDiff ℝ ∞ σ.fourier := by
  obtain ⟨hp, hn⟩ := h.1
  haveI := hp
  haveI := hn
  have := (contDiff_fm σ.pos (fun n => (moments_admissible σ h n).1)).sub
    (contDiff_fm σ.neg (fun n => (moments_admissible σ h n).2))
  exact this

/-- The regularised symbol `(1-χ(ξ/ε)) M_i(ξ) σ̂(ξ)`. -/
def Gfun (d : ℕ) (s : ℝ) (c : ℂ) (σ : SMeas d) (i : Fin d) (ε : ℝ) (ξ : Euc d) : ℂ :=
  (1 - cmxFB_gL d ε ξ) * (Msym d s c i ξ * σ.fourier ξ)

lemma gL_eq_one {ε : ℝ} (hε : 0 < ε) {ξ : Euc d} (h : ‖ξ‖ < ε) : cmxFB_gL d ε ξ = 1 := by
  have : ‖ε⁻¹ • ξ‖ ≤ 1 := by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hε.le, inv_mul_le_iff₀ hε]
    linarith
  simp [cmxFB_gL, cmxFB_chi_one this]

lemma Gfun_contDiff (c : ℂ) (σ : SMeas d) (hσ : ContDiff ℝ ∞ σ.fourier) (i : Fin d) {ε : ℝ}
    (hε : 0 < ε) : ContDiff ℝ ∞ (Gfun d s c σ i ε) := by
  have h1 : ContDiff ℝ ∞ (fun ξ : Euc d => (1 - cmxFB_gL d ε ξ) * cmxMY_hi d s i ξ) := by
    refine contDiff_of_away_real' hε (fun η hη => ?_) (fun η hη => ?_)
    · exact (contDiff_const.sub (cmxFB_gL_contDiff ε)).contDiffAt.mul (cmxMY_hi_smooth s i η hη)
    · rw [gL_eq_one hε hη]; simp
  have h2 : ContDiff ℝ ∞ (fun ξ : Euc d => c * cmxFB_gL d 1 ξ * σ.fourier ξ) :=
    (contDiff_const.mul (cmxFB_gL_contDiff 1)).mul hσ
  have := h1.mul h2
  convert this using 1
  funext ξ
  simp only [Gfun, Msym]
  ring

lemma Gfun_compact (c : ℂ) (σ : SMeas d) (i : Fin d) (ε : ℝ) :
    HasCompactSupport (Gfun d s c σ i ε) := by
  have h := (cmxFB_gL_compact (d := d) (by norm_num : (0 : ℝ) < 1)).mul_left
    (f := fun ξ : Euc d => (1 - cmxFB_gL d ε ξ) * c * cmxMY_hi d s i ξ * σ.fourier ξ)
  convert h using 1
  funext ξ
  simp only [Gfun, Msym, Pi.mul_apply]
  ring

/-- The Schwartz function `ξ ↦ (1-χ(ξ/ε)) M_i(ξ) σ̂(ξ)`. -/
def GS (c : ℂ) (σ : SMeas d) (hσ : ContDiff ℝ ∞ σ.fourier) (i : Fin d) {ε : ℝ} (hε : 0 < ε) :
    SchwartzMap (Euc d) ℂ :=
  (Gfun_compact (s := s) c σ i ε).toSchwartzMap (Gfun_contDiff c σ hσ i hε)

lemma GS_apply (c : ℂ) (σ : SMeas d) (hσ : ContDiff ℝ ∞ σ.fourier) (i : Fin d) {ε : ℝ}
    (hε : 0 < ε) (ξ : Euc d) : GS (s := s) c σ hσ i hε ξ = Gfun d s c σ i ε ξ := rfl

/-- Plancherel for Schwartz functions, in `ℝ≥0∞`. -/
lemma lintegral_sq_fourier (f : SchwartzMap (Euc d) ℂ) :
    ∫⁻ x, ‖𝓕 (⇑f) x‖ₑ ^ (2 : ℝ) = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) := by
  have key : ∀ g : SchwartzMap (Euc d) ℂ, ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal (∫ x, ‖g x‖ ^ 2) := by
    intro g
    have hi : Integrable (fun x => ‖g x‖ ^ 2) volume :=
      (memLp_two_iff_integrable_sq_norm g.continuous.aestronglyMeasurable).1 (g.memLp 2)
    rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => by positivity)]
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
    norm_num
  have hF : ∫⁻ x, ‖𝓕 (⇑f) x‖ₑ ^ (2 : ℝ) = ∫⁻ x, ‖(𝓕 f : SchwartzMap (Euc d) ℂ) x‖ₑ ^ (2 : ℝ) := by
    simp only [SchwartzMap.fourier_coe]
  rw [hF, key, key f, SchwartzMap.integral_norm_sq_fourier f]

/-! ### The Sobolev-weighted symbol -/

/-- `(2π|ξ|)^{σ₀} G_ε(ξ)`. -/
def Hfun (d : ℕ) (s : ℝ) (c : ℂ) (σ : SMeas d) (i : Fin d) (ε σ₀ : ℝ) (ξ : Euc d) : ℂ :=
  (((2 * Real.pi * ‖ξ‖) ^ σ₀ : ℝ) : ℂ) * Gfun d s c σ i ε ξ

lemma Gfun_zero (c : ℂ) (σ : SMeas d) (i : Fin d) {ε : ℝ} (hε : 0 < ε) {ξ : Euc d}
    (h : ‖ξ‖ < ε) : Gfun d s c σ i ε ξ = 0 := by
  simp [Gfun, gL_eq_one hε h]

lemma Hfun_contDiff (c : ℂ) (σ : SMeas d) (hσ : ContDiff ℝ ∞ σ.fourier) (i : Fin d) {ε : ℝ}
    (hε : 0 < ε) (σ₀ : ℝ) : ContDiff ℝ ∞ (Hfun d s c σ i ε σ₀) := by
  refine contDiff_of_away_real' hε (fun η hη => ?_) (fun η hη => ?_)
  · have hn : 2 * Real.pi * ‖η‖ ≠ 0 := by
      have := norm_pos_iff.2 hη
      positivity
    have h1 : ContDiffAt ℝ ∞ (fun ξ : Euc d => (2 * Real.pi * ‖ξ‖) ^ σ₀) η :=
      (contDiffAt_const.mul (contDiffAt_norm ℝ hη)).rpow_const_of_ne hn
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp η h1).mul
      (Gfun_contDiff c σ hσ i hε).contDiffAt
  · simp [Hfun, Gfun_zero c σ i hε hη]

lemma Hfun_compact (c : ℂ) (σ : SMeas d) (i : Fin d) (ε σ₀ : ℝ) :
    HasCompactSupport (Hfun d s c σ i ε σ₀) :=
  (Gfun_compact (s := s) c σ i ε).mul_left (f := fun ξ : Euc d => (((2 * Real.pi * ‖ξ‖) ^ σ₀ : ℝ) : ℂ))

def HS (c : ℂ) (σ : SMeas d) (hσ : ContDiff ℝ ∞ σ.fourier) (i : Fin d) {ε : ℝ} (hε : 0 < ε)
    (σ₀ : ℝ) : SchwartzMap (Euc d) ℂ :=
  (Hfun_compact (s := s) c σ i ε σ₀).toSchwartzMap (Hfun_contDiff c σ hσ i hε σ₀)

lemma HS_apply (c : ℂ) (σ : SMeas d) (hσ : ContDiff ℝ ∞ σ.fourier) (i : Fin d) {ε : ℝ}
    (hε : 0 < ε) (σ₀ : ℝ) (ξ : Euc d) : HS (s := s) c σ hσ i hε σ₀ ξ = Hfun d s c σ i ε σ₀ ξ := rfl

lemma hi_norm_le {ξ : Euc d} (hξ : ξ ≠ 0) (i : Fin d) :
    ‖cmxMY_hi d s i ξ‖ ≤ ‖ξ‖ ^ (1 - ((d : ℝ) - s)) := by
  have hxn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hxi : |ξ i| ≤ ‖ξ‖ := by simpa using PiLp.norm_apply_le ξ i
  unfold cmxMY_hi
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg ξ) _)]
  calc |ξ i| * ‖ξ‖ ^ (-((d : ℝ) - s)) ≤ ‖ξ‖ * ‖ξ‖ ^ (-((d : ℝ) - s)) := by gcongr
    _ = ‖ξ‖ ^ (1 - ((d : ℝ) - s)) := by
        rw [show 1 - ((d : ℝ) - s) = 1 + -((d : ℝ) - s) by ring, Real.rpow_add hxn, Real.rpow_one]

lemma gL_norm_le (ε : ℝ) (ξ : Euc d) : ‖(1 : ℂ) - cmxFB_gL d ε ξ‖ ≤ 1 := by
  unfold cmxFB_gL
  have h0 := cmxFB_chi_nonneg (d := d) (ε⁻¹ • ξ)
  have h1 := cmxFB_chi_le_one (d := d) (ε⁻¹ • ξ)
  have : (1 : ℂ) - ((chi (ε⁻¹ • ξ) : ℝ) : ℂ) = ((1 - chi (ε⁻¹ • ξ) : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  linarith

lemma gL_mul_le (F : Euc d → ℂ) (ξ : Euc d) :
    ‖cmxFB_gL d 1 ξ * F ξ‖ ≤ ‖lowFreq 4 F ξ‖ := by
  unfold lowFreq cmxFB_gL
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  by_cases h : ‖ξ‖ < 2
  · have h4 : chi ((4 : ℝ)⁻¹ • ξ) = 1 := by
      apply cmxFB_chi_one
      rw [norm_smul, norm_inv, Real.norm_of_nonneg (by norm_num)]
      linarith
    rw [h4, abs_one, one_mul]
    have h0 := cmxFB_chi_nonneg (d := d) ((1 : ℝ)⁻¹ • ξ)
    have h1 := cmxFB_chi_le_one (d := d) ((1 : ℝ)⁻¹ • ξ)
    rw [abs_of_nonneg h0]
    exact mul_le_of_le_one_left (norm_nonneg _) h1
  · have h2 : chi ((1 : ℝ)⁻¹ • ξ) = 0 := by
      apply cmxFB_chi_zero
      simpa using not_lt.1 h
    rw [h2, abs_zero, zero_mul]
    positivity

lemma rpow_combine (a : ℝ) (ha : 0 < a) (σ₀ κ α : ℝ) (hα : σ₀ + (1 - κ) = -α) :
    (2 * Real.pi * a) ^ σ₀ * a ^ (1 - κ) =
      (2 * Real.pi) ^ (κ - 1) * (2 * Real.pi * a) ^ (-α) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have h1 : a ^ (1 - κ) = (2 * Real.pi) ^ (κ - 1) * (2 * Real.pi * a) ^ (1 - κ) := by
    rw [Real.mul_rpow hpi.le ha.le, ← mul_assoc, ← Real.rpow_add hpi]
    simp
  rw [h1, ← mul_assoc, mul_comm ((2 * Real.pi * a) ^ σ₀), mul_assoc, ← Real.rpow_add (by positivity),
    hα]

lemma Hfun_pointwise (c : ℂ) (σ : SMeas d) (i : Fin d) (ε : ℝ) (ξ : Euc d) (hξ : ξ ≠ 0) :
    ‖Hfun d s c σ i ε (alphaE d s - 1) ξ‖ ^ 2 ≤
      (‖c‖ * (2 * Real.pi) ^ ((d : ℝ) - s - 1)) ^ 2 *
        ((2 * Real.pi * ‖ξ‖) ^ (2 * (-alphaE d s)) * ‖lowFreq 4 σ.fourier ξ‖ ^ 2) := by
  have ha : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have ht : 0 < 2 * Real.pi * ‖ξ‖ := by positivity
  have hα : (alphaE d s - 1) + (1 - ((d : ℝ) - s)) = -alphaE d s := by
    unfold alphaE; ring
  have h1 : ‖Hfun d s c σ i ε (alphaE d s - 1) ξ‖ ≤
      (2 * Real.pi * ‖ξ‖) ^ (alphaE d s - 1) * (‖c‖ * ‖ξ‖ ^ (1 - ((d : ℝ) - s)) *
        ‖lowFreq 4 σ.fourier ξ‖) := by
    unfold Hfun Gfun Msym
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht.le _)]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg ht.le _)
    have e : c * cmxMY_hi d s i ξ * cmxFB_gL d 1 ξ * σ.fourier ξ =
        c * cmxMY_hi d s i ξ * (cmxFB_gL d 1 ξ * σ.fourier ξ) := by ring
    rw [e, norm_mul, norm_mul (c * _)]
    have := mul_le_mul (gL_norm_le ε ξ)
      (mul_le_mul (mul_le_mul_of_nonneg_left (hi_norm_le (s := s) hξ i) (norm_nonneg c))
        (gL_mul_le σ.fourier ξ) (norm_nonneg _) (by positivity))
      (by positivity) zero_le_one
    simpa [norm_mul, one_mul] using this
  have h2 : ‖Hfun d s c σ i ε (alphaE d s - 1) ξ‖ ≤
      ‖c‖ * (2 * Real.pi) ^ ((d : ℝ) - s - 1) * (2 * Real.pi * ‖ξ‖) ^ (-alphaE d s) *
        ‖lowFreq 4 σ.fourier ξ‖ := by
    refine h1.trans (le_of_eq ?_)
    have := rpow_combine ‖ξ‖ ha (alphaE d s - 1) ((d : ℝ) - s) (alphaE d s) hα
    calc (2 * Real.pi * ‖ξ‖) ^ (alphaE d s - 1) * (‖c‖ * ‖ξ‖ ^ (1 - ((d : ℝ) - s)) *
        ‖lowFreq 4 σ.fourier ξ‖)
        = ‖c‖ * ((2 * Real.pi * ‖ξ‖) ^ (alphaE d s - 1) * ‖ξ‖ ^ (1 - ((d : ℝ) - s))) *
          ‖lowFreq 4 σ.fourier ξ‖ := by ring
      _ = _ := by rw [this]; ring
  have h3 : 0 ≤ ‖Hfun d s c σ i ε (alphaE d s - 1) ξ‖ := norm_nonneg _
  calc ‖Hfun d s c σ i ε (alphaE d s - 1) ξ‖ ^ 2
      ≤ (‖c‖ * (2 * Real.pi) ^ ((d : ℝ) - s - 1) * (2 * Real.pi * ‖ξ‖) ^ (-alphaE d s) *
        ‖lowFreq 4 σ.fourier ξ‖) ^ 2 := pow_le_pow_left₀ h3 h2 2
    _ = (‖c‖ * (2 * Real.pi) ^ ((d : ℝ) - s - 1)) ^ 2 *
        (((2 * Real.pi * ‖ξ‖) ^ (-alphaE d s)) ^ 2 * ‖lowFreq 4 σ.fourier ξ‖ ^ 2) := by ring
    _ = _ := by
        have e : ((2 * Real.pi * ‖ξ‖) ^ (-alphaE d s)) ^ 2 =
            (2 * Real.pi * ‖ξ‖) ^ (2 * (-alphaE d s)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
          norm_num
          ring_nf
        rw [e]

lemma enorm_rpow_two (z : ℂ) : ‖z‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
  norm_num

lemma HS_lintegral_le (hd : 1 ≤ d) (c : ℂ) (σ : SMeas d) (hσ : ContDiff ℝ ∞ σ.fourier) (i : Fin d)
    {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ ξ, ‖HS (s := s) c σ hσ i hε (alphaE d s - 1) ξ‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal ((‖c‖ * (2 * Real.pi) ^ ((d : ℝ) - s - 1)) ^ 2) *
        homSqE (-alphaE d s) (lowFreq 4 σ.fourier) := by
  unfold homSqE
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_ne_zero_euc hd] with ξ hξ
  rw [HS_apply, enorm_rpow_two]
  have h := Hfun_pointwise (s := s) c σ i ε ξ hξ
  have hw : 0 ≤ (2 * Real.pi * ‖ξ‖) ^ (2 * (-alphaE d s)) :=
    Real.rpow_nonneg (by positivity) _
  calc ENNReal.ofReal (‖Hfun d s c σ i ε (alphaE d s - 1) ξ‖ ^ 2)
      ≤ ENNReal.ofReal ((‖c‖ * (2 * Real.pi) ^ ((d : ℝ) - s - 1)) ^ 2 *
        ((2 * Real.pi * ‖ξ‖) ^ (2 * (-alphaE d s)) * ‖lowFreq 4 σ.fourier ξ‖ ^ 2)) :=
        ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal ((‖c‖ * (2 * Real.pi) ^ ((d : ℝ) - s - 1)) ^ 2) *
        (ENNReal.ofReal ((2 * Real.pi * ‖ξ‖) ^ (2 * (-alphaE d s))) *
          ‖lowFreq 4 σ.fourier ξ‖ₑ ^ 2) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hw, ENNReal.ofReal_pow
          (norm_nonneg _), ofReal_norm]

lemma eLpNorm_two_eq (g : SchwartzMap (Euc d) ℂ) :
    eLpNorm (⇑g) 2 volume = (∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) ENNReal.ofNat_ne_top
    g.continuous.aestronglyMeasurable]
  simp

/-- The Schwartz approximant `𝓕⁻[(1-χ(·/ε)) M_i σ̂]`. -/
def fReg (c : ℂ) (σ : SMeas d) (hσ : ContDiff ℝ ∞ σ.fourier) (i : Fin d) {ε : ℝ} (hε : 0 < ε) :
    SchwartzMap (Euc d) ℂ := 𝓕⁻ (GS (s := s) c σ hσ i hε)

lemma fReg_apply (c : ℂ) (σ : SMeas d) (hσ : ContDiff ℝ ∞ σ.fourier) (i : Fin d) {ε : ℝ}
    (hε : 0 < ε) (x : Euc d) :
    fReg (s := s) c σ hσ i hε x = 𝓕⁻ (Gfun d s c σ i ε) x := by
  unfold fReg
  rw [SchwartzMap.fourierInv_coe]
  rfl

lemma reg_norm_bound (hd : 1 ≤ d) {C_H : ℝ} {q : ℝ≥0∞}
    (hC : ∀ φ : SchwartzMap (Euc d) ℂ, eLpNorm (⇑φ) q volume ≤
      ENNReal.ofReal C_H * eLpNorm (cmxHLS_frac (alphaE d s - 1) φ) 2 volume)
    (c : ℂ) (σ : SMeas d) (hσ : ContDiff ℝ ∞ σ.fourier) (i : Fin d) {ε : ℝ} (hε : 0 < ε) :
    eLpNorm (⇑(fReg (s := s) c σ hσ i hε)) q volume ≤ ENNReal.ofReal C_H *
      (ENNReal.ofReal ((‖c‖ * (2 * Real.pi) ^ ((d : ℝ) - s - 1)) ^ 2) *
        homSqE (-alphaE d s) (lowFreq 4 σ.fourier)) ^ (1 / (2 : ℝ)) := by
  refine (hC _).trans ?_
  gcongr
  have hfrac : cmxHLS_frac (alphaE d s - 1) (fReg (s := s) c σ hσ i hε) =
      ⇑(𝓕⁻ (HS (s := s) c σ hσ i hε (alphaE d s - 1))) := by
    funext x
    rw [SchwartzMap.fourierInv_coe]
    unfold cmxHLS_frac
    have h1 : ∀ ξ : Euc d, 𝓕 (⇑(fReg (s := s) c σ hσ i hε)) ξ = GS (s := s) c σ hσ i hε ξ := by
      intro ξ
      rw [← SchwartzMap.fourier_coe]
      unfold fReg
      rw [FourierTransform.fourier_fourierInv_eq]
    simp_rw [h1]
    rfl
  rw [hfrac, eLpNorm_two_eq]
  gcongr
  have hP := lintegral_sq_fourier (𝓕⁻ (HS (s := s) c σ hσ i hε (alphaE d s - 1)))
  have h2 : ∀ x, 𝓕 (⇑(𝓕⁻ (HS (s := s) c σ hσ i hε (alphaE d s - 1)))) x =
      HS (s := s) c σ hσ i hε (alphaE d s - 1) x := by
    intro x
    rw [← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]
  simp_rw [h2] at hP
  rw [← hP]
  exact HS_lintegral_le hd c σ hσ i hε

end HRS.Commutator.Whole.SAMP2
