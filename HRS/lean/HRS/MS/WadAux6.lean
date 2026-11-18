import HRS.MS.WadAux5

/-!
# S8.3, packet D2 (part 4): the Kolmogorov equation for the Mehler semigroup

For `h ∈ C²` with `h`, `Dh`, `D²h` bounded and `τ > 0`:
`d/dτ P_τ h (x) = P_τ (L_0 h) (x)`, `L_0 h = ν Δh - a ⟨y, ∇h⟩` (`s83_P_hasDerivAt`).  Here `Δh = ∑_i ∂_i∂_i h`
(`s83_lap`) and `⟨y,∇h⟩ = Dh(y)(y)`.  The proof differentiates under the Gaussian integral and uses Stein's
identity once: `∫ Dh(cx+σz)(z) dγ = σ ∫ Δh(cx+σz) dγ`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

/-- `Δh = ∑_i ∂_i ∂_i h` (second derivatives in the standard basis). -/
def s83_lap (h : Euc d → ℝ) (y : Euc d) : ℝ :=
  ∑ i : Fin d, fderiv ℝ (fderiv ℝ h) y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)

/-- The Ornstein-Uhlenbeck generator `L_0 h = νΔh - a ⟨y, ∇h⟩`. -/
def s83_L0 (a ν : ℝ) (h : Euc d → ℝ) (y : Euc d) : ℝ :=
  ν * s83_lap h y - a * fderiv ℝ h y y

/-! ### The Mehler parameters as functions of `τ` -/

theorem s83_mc_sq (a τ : ℝ) : s83_mc a τ ^ 2 = Real.exp (-2 * a * τ) := by
  unfold s83_mc; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

theorem s83_hasDerivAt_mc (a τ : ℝ) : HasDerivAt (s83_mc a) (-a * s83_mc a τ) τ := by
  have h := ((hasDerivAt_id τ).const_mul (-a)).exp
  unfold s83_mc
  refine HasDerivAt.congr_deriv h ?_
  show Real.exp (-a * τ) * (-a * 1) = -a * Real.exp (-a * τ)
  ring

theorem s83_u_pos {a ν τ : ℝ} (ha : 0 < a) (hν : 0 < ν) (hτ : 0 < τ) :
    0 < ν * (1 - Real.exp (-2 * a * τ)) / a := by
  have : Real.exp (-2 * a * τ) < 1 := by
    have := Real.exp_lt_exp.2 (show -2 * a * τ < 0 by nlinarith)
    simpa using this
  have : 0 < 1 - Real.exp (-2 * a * τ) := by linarith
  positivity

theorem s83_ms_pos {a ν τ : ℝ} (ha : 0 < a) (hν : 0 < ν) (hτ : 0 < τ) : 0 < s83_ms a ν τ :=
  Real.sqrt_pos.2 (s83_u_pos ha hν hτ)

theorem s83_ms_mono {a ν τ₁ τ₂ : ℝ} (ha : 0 < a) (hν : 0 ≤ ν) (h : τ₁ ≤ τ₂) :
    s83_ms a ν τ₁ ≤ s83_ms a ν τ₂ := by
  unfold s83_ms
  refine Real.sqrt_le_sqrt ?_
  have : Real.exp (-2 * a * τ₂) ≤ Real.exp (-2 * a * τ₁) :=
    Real.exp_le_exp.2 (by nlinarith)
  have : ν * (1 - Real.exp (-2 * a * τ₁)) ≤ ν * (1 - Real.exp (-2 * a * τ₂)) :=
    mul_le_mul_of_nonneg_left (by linarith) hν
  exact div_le_div_of_nonneg_right this ha.le

theorem s83_hasDerivAt_ms {a ν τ : ℝ} (ha : 0 < a) (hν : 0 < ν) (hτ : 0 < τ) :
    HasDerivAt (s83_ms a ν) (ν * s83_mc a τ ^ 2 / s83_ms a ν τ) τ := by
  have hu : HasDerivAt (fun τ => ν * (1 - Real.exp (-2 * a * τ)) / a)
      (ν * (2 * a * Real.exp (-2 * a * τ)) / a) τ := by
    have h1 := ((hasDerivAt_id τ).const_mul (-2 * a)).exp
    have h2 := (h1.const_sub 1).const_mul ν |>.div_const a
    convert h2 using 1
    · simp
    · simp; ring
  have hs := hu.sqrt (s83_u_pos ha hν hτ).ne'
  unfold s83_ms
  convert hs using 1
  rw [s83_mc_sq]
  have : Real.sqrt (ν * (1 - Real.exp (-2 * a * τ)) / a) ≠ 0 := (Real.sqrt_pos.2 (s83_u_pos ha hν hτ)).ne'
  field_simp

/-! ### Stein's identity for bounded data -/

theorem s83_stein_bdd {F : Euc d → ℝ} (hF : ContDiff ℝ 1 F) {B M : ℝ} (hB : ∀ w, |F w| ≤ B)
    (hM : ∀ w, ‖fderiv ℝ F w‖ ≤ M) (i : Fin d) :
    ∫ w, w i * F w ∂(stdGaussian (Euc d)) =
      ∫ w, fderiv ℝ F w (EuclideanSpace.single i 1) ∂(stdGaussian (Euc d)) := by
  refine s83_stein hF i ?_ ?_ ?_
  · exact s83_int_of_poly (C := B) (p := 0) hF.continuous.aestronglyMeasurable
      (fun z => by simpa using hB z)
  · refine s83_int_of_poly (C := B) (p := 1)
      (((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).mul hF.continuous).aestronglyMeasurable
      fun z => ?_
    rw [norm_mul, Real.norm_eq_abs]
    have hz : ‖z i‖ ≤ 1 + ‖z‖ := by
      have := PiLp.norm_apply_le z i
      linarith [norm_nonneg z]
    have h1 : |F z| ≤ B := hB z
    have hB0 : 0 ≤ B := (abs_nonneg _).trans h1
    calc ‖z i‖ * |F z| ≤ (1 + ‖z‖) * B := mul_le_mul hz h1 (abs_nonneg _) (by positivity)
      _ = B * (1 + ‖z‖) ^ 1 := by ring
  · refine s83_int_of_poly (C := M) (p := 0)
      ((continuous_eval_const (EuclideanSpace.single i (1 : ℝ))).comp
        (hF.continuous_fderiv one_ne_zero)).aestronglyMeasurable fun z => ?_
    have := (fderiv ℝ F z).le_opNorm (EuclideanSpace.single i (1 : ℝ))
    simp only [PiLp.norm_single, norm_one, mul_one] at this
    simpa using this.trans (hM z)

/-! ### Derivatives of `z ↦ Dh(cx+σz)(e_i)` -/

theorem s83_hasFDerivAt_Dh {h : Euc d → ℝ} (hh : ContDiff ℝ 2 h) (c σ : ℝ) (x z : Euc d)
    (i : Fin d) :
    HasFDerivAt (fun z : Euc d => fderiv ℝ h (c • x + σ • z) (EuclideanSpace.single i 1))
      (σ • (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))).comp
        (fderiv ℝ (fderiv ℝ h) (c • x + σ • z))) z := by
  have h1 : HasFDerivAt (fun z : Euc d => c • x + σ • z) (σ • ContinuousLinearMap.id ℝ (Euc d)) z :=
    ((hasFDerivAt_id z).const_smul σ).const_add (c • x)
  have hh1 : ContDiff ℝ 1 (fderiv ℝ h) := hh.fderiv_right (m := 1) (by norm_num)
  have h2 := ((hh1.differentiable one_ne_zero) (c • x + σ • z)).hasFDerivAt.comp z h1
  have h3 := (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))).hasFDerivAt.comp z h2
  refine HasFDerivAt.congr_fderiv h3 ?_
  ext v
  simp

theorem s83_Dh_stein {h : Euc d → ℝ} (hh : ContDiff ℝ 2 h) {B1 B2 : ℝ}
    (hB1 : ∀ y, ‖fderiv ℝ h y‖ ≤ B1) (hB2 : ∀ y, ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ B2) (c σ : ℝ)
    (x : Euc d) (i : Fin d) :
    ∫ z, z i * fderiv ℝ h (c • x + σ • z) (EuclideanSpace.single i 1) ∂(stdGaussian (Euc d)) =
      σ * ∫ z, fderiv ℝ (fderiv ℝ h) (c • x + σ • z) (EuclideanSpace.single i 1)
        (EuclideanSpace.single i 1) ∂(stdGaussian (Euc d)) := by
  set F : Euc d → ℝ := fun z => fderiv ℝ h (c • x + σ • z) (EuclideanSpace.single i 1) with hF
  have hd := s83_hasFDerivAt_Dh hh c σ x
  have hFder : ∀ z, fderiv ℝ F z (EuclideanSpace.single i 1) =
      σ * fderiv ℝ (fderiv ℝ h) (c • x + σ • z) (EuclideanSpace.single i 1)
        (EuclideanSpace.single i 1) := fun z => by
    rw [(hd z i).fderiv]; simp
  have hhc : ContDiff ℝ 1 (fderiv ℝ h) := hh.fderiv_right (m := 1) (by norm_num)
  have hFC : ContDiff ℝ 1 F := by
    have : ContDiff ℝ 1 (fun z : Euc d => fderiv ℝ h (c • x + σ • z)) :=
      hhc.comp (contDiff_const.add (contDiff_id.const_smul σ))
    exact (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))).contDiff.comp this
  have hB : ∀ z, |F z| ≤ B1 := fun z => by
    have := (fderiv ℝ h (c • x + σ • z)).le_opNorm (EuclideanSpace.single i (1 : ℝ))
    simp only [PiLp.norm_single, norm_one, mul_one] at this
    rw [← Real.norm_eq_abs]
    exact this.trans (hB1 _)
  have hM : ∀ z, ‖fderiv ℝ F z‖ ≤ |σ| * B2 := fun z => by
    rw [(hd z i).fderiv]
    have hB20 : 0 ≤ B2 := (norm_nonneg (fderiv ℝ (fderiv ℝ h) (c • x + σ • z))).trans (hB2 (c • x + σ • z))
    refine (ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (abs_nonneg _) hB20) fun v => ?_)
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, norm_smul, Real.norm_eq_abs]
    have h5 := (fderiv ℝ (fderiv ℝ h) (c • x + σ • z)).le_opNorm v
    have h6 := (fderiv ℝ (fderiv ℝ h) (c • x + σ • z) v).le_opNorm (EuclideanSpace.single i (1 : ℝ))
    simp only [PiLp.norm_single, norm_one, mul_one] at h6
    have h7 : ‖fderiv ℝ (fderiv ℝ h) (c • x + σ • z) v (EuclideanSpace.single i 1)‖ ≤ B2 * ‖v‖ := by
      refine (h6.trans ?_)
      exact h5.trans (mul_le_mul_of_nonneg_right (hB2 _) (norm_nonneg _))
    calc |σ| * ‖fderiv ℝ (fderiv ℝ h) (c • x + σ • z) v (EuclideanSpace.single i 1)‖
        ≤ |σ| * (B2 * ‖v‖) := mul_le_mul_of_nonneg_left h7 (abs_nonneg σ)
      _ = |σ| * B2 * ‖v‖ := by ring
  have := s83_stein_bdd hFC hB hM i
  simp only [hFder] at this
  rw [integral_const_mul] at this
  exact this

/-! ### The Kolmogorov equation -/

theorem s83_lap_bound {h : Euc d → ℝ} {B2 : ℝ} (hB2 : ∀ y, ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ B2) (y : Euc d) :
    |s83_lap h y| ≤ d * B2 := by
  unfold s83_lap
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ i : Fin d, |fderiv ℝ (fderiv ℝ h) y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)| ≤ B2 := by
    intro i
    rw [← Real.norm_eq_abs]
    have h1 := (fderiv ℝ (fderiv ℝ h) y (EuclideanSpace.single i 1)).le_opNorm (EuclideanSpace.single i (1 : ℝ))
    have h2 := (fderiv ℝ (fderiv ℝ h) y).le_opNorm (EuclideanSpace.single i (1 : ℝ))
    simp only [PiLp.norm_single, norm_one, mul_one] at h1 h2
    exact h1.trans (h2.trans (hB2 y))
  calc ∑ i : Fin d, |fderiv ℝ (fderiv ℝ h) y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)|
      ≤ ∑ i : Fin d, B2 := Finset.sum_le_sum fun i _ => this i
    _ = d * B2 := by simp

theorem s83_lap_continuous {h : Euc d → ℝ} (hh : ContDiff ℝ 2 h) : Continuous (s83_lap h) := by
  unfold s83_lap
  have hc : ContDiff ℝ 1 (fderiv ℝ h) := hh.fderiv_right (m := 1) (by norm_num)
  have h2 : Continuous (fderiv ℝ (fderiv ℝ h)) := hc.continuous_fderiv one_ne_zero
  refine continuous_finset_sum _ fun i _ => ?_
  exact ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))).continuous.comp
    ((ContinuousLinearMap.apply ℝ (Euc d →L[ℝ] ℝ) (EuclideanSpace.single i (1 : ℝ))).continuous.comp h2))

theorem s83_clm_expand (L : Euc d →L[ℝ] ℝ) (z : Euc d) :
    L z = ∑ i : Fin d, z i * L (EuclideanSpace.single i 1) := by
  have hz : z = ∑ i, z i • (EuclideanSpace.single i 1 : Euc d) := by
    have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr' z
    simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left] using this.symm
  conv_lhs => rw [hz]
  simp [map_sum]

theorem s83_cont_Dh {h : Euc d → ℝ} (hh : ContDiff ℝ 2 h) : Continuous (fderiv ℝ h) :=
  hh.continuous_fderiv (by norm_num)

/-- `∫ Dh(cx+σz)(z) dγ = σ ∫ Δh(cx+σz) dγ` (Stein). -/
theorem s83_int_Dh_eval {h : Euc d → ℝ} (hh : ContDiff ℝ 2 h) {B1 B2 : ℝ}
    (hB1 : ∀ y, ‖fderiv ℝ h y‖ ≤ B1) (hB2 : ∀ y, ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ B2) (c σ : ℝ)
    (x : Euc d) :
    ∫ z, fderiv ℝ h (c • x + σ • z) z ∂(stdGaussian (Euc d)) =
      σ * ∫ z, s83_lap h (c • x + σ • z) ∂(stdGaussian (Euc d)) := by
  have hDc := s83_cont_Dh hh
  have hshift : Continuous fun z : Euc d => c • x + σ • z :=
    continuous_const.add (continuous_const_smul σ)
  have hint1 : ∀ i : Fin d, Integrable (fun z : Euc d =>
      z i * fderiv ℝ h (c • x + σ • z) (EuclideanSpace.single i 1)) (stdGaussian (Euc d)) := by
    intro i
    refine s83_int_of_poly (C := B1) (p := 1)
      (((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).mul
        ((continuous_eval_const (EuclideanSpace.single i (1 : ℝ))).comp (hDc.comp hshift))).aestronglyMeasurable
      fun z => ?_
    rw [norm_mul]
    have hz : ‖z i‖ ≤ 1 + ‖z‖ := by
      have := PiLp.norm_apply_le z i
      linarith [norm_nonneg z]
    have h4 : ‖fderiv ℝ h (c • x + σ • z) (EuclideanSpace.single i 1)‖ ≤ B1 := by
      have := (fderiv ℝ h (c • x + σ • z)).le_opNorm (EuclideanSpace.single i (1 : ℝ))
      simp only [PiLp.norm_single, norm_one, mul_one] at this
      exact this.trans (hB1 _)
    have hB10 : 0 ≤ B1 := (norm_nonneg _).trans h4
    calc ‖z i‖ * ‖fderiv ℝ h (c • x + σ • z) (EuclideanSpace.single i 1)‖ ≤ (1 + ‖z‖) * B1 :=
          mul_le_mul hz h4 (norm_nonneg _) (by positivity)
      _ = B1 * (1 + ‖z‖) ^ 1 := by ring
  have hint2 : ∀ i : Fin d, Integrable (fun z : Euc d =>
      fderiv ℝ (fderiv ℝ h) (c • x + σ • z) (EuclideanSpace.single i 1) (EuclideanSpace.single i 1))
      (stdGaussian (Euc d)) := by
    intro i
    have hc : Continuous (fderiv ℝ (fderiv ℝ h)) :=
      (hh.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
    refine s83_int_of_poly (C := B2) (p := 0)
      (((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))).continuous.comp
        ((ContinuousLinearMap.apply ℝ (Euc d →L[ℝ] ℝ) (EuclideanSpace.single i (1 : ℝ))).continuous.comp
          (hc.comp hshift)))).aestronglyMeasurable fun z => ?_
    have h1 := (fderiv ℝ (fderiv ℝ h) (c • x + σ • z) (EuclideanSpace.single i 1)).le_opNorm
      (EuclideanSpace.single i (1 : ℝ))
    have h2 := (fderiv ℝ (fderiv ℝ h) (c • x + σ • z)).le_opNorm (EuclideanSpace.single i (1 : ℝ))
    simp only [PiLp.norm_single, norm_one, mul_one] at h1 h2
    simpa using h1.trans (h2.trans (hB2 _))
  calc ∫ z, fderiv ℝ h (c • x + σ • z) z ∂(stdGaussian (Euc d))
      = ∫ z, ∑ i : Fin d, z i * fderiv ℝ h (c • x + σ • z) (EuclideanSpace.single i 1)
          ∂(stdGaussian (Euc d)) := by
        congr 1; funext z; exact s83_clm_expand _ z
    _ = ∑ i : Fin d, ∫ z, z i * fderiv ℝ h (c • x + σ • z) (EuclideanSpace.single i 1)
          ∂(stdGaussian (Euc d)) := integral_finset_sum _ fun i _ => hint1 i
    _ = ∑ i : Fin d, σ * ∫ z, fderiv ℝ (fderiv ℝ h) (c • x + σ • z) (EuclideanSpace.single i 1)
          (EuclideanSpace.single i 1) ∂(stdGaussian (Euc d)) :=
        Finset.sum_congr rfl fun i _ => s83_Dh_stein hh hB1 hB2 c σ x i
    _ = σ * ∫ z, s83_lap h (c • x + σ • z) ∂(stdGaussian (Euc d)) := by
        rw [← Finset.mul_sum, ← integral_finset_sum _ fun i _ => hint2 i]
        rfl

theorem s83_kolmogorov_id {h : Euc d → ℝ} (hh : ContDiff ℝ 2 h) {B1 B2 : ℝ}
    (hB1 : ∀ y, ‖fderiv ℝ h y‖ ≤ B1) (hB2 : ∀ y, ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ B2) {a ν τ : ℝ}
    (ha : 0 < a) (hν : 0 < ν) (hτ : 0 < τ) (x : Euc d) :
    ∫ z, fderiv ℝ h (s83_mc a τ • x + s83_ms a ν τ • z)
        ((-a * s83_mc a τ) • x + (ν * s83_mc a τ ^ 2 / s83_ms a ν τ) • z)
        ∂(stdGaussian (Euc d)) = s83_P a ν τ (s83_L0 a ν h) x := by
  have hDc := s83_cont_Dh hh
  have hσ0 : 0 < s83_ms a ν τ := s83_ms_pos ha hν hτ
  set c := s83_mc a τ with hc
  set σ := s83_ms a ν τ with hσ
  have hshift : Continuous fun z : Euc d => c • x + σ • z :=
    continuous_const.add (continuous_const_smul _)
  have hB10 : 0 ≤ B1 := (norm_nonneg (fderiv ℝ h 0)).trans (hB1 0)
  have hI1 : Integrable (fun z : Euc d => fderiv ℝ h (c • x + σ • z) x) (stdGaussian (Euc d)) := by
    refine s83_int_of_poly (C := B1 * ‖x‖) (p := 0)
      ((hDc.comp hshift).clm_apply continuous_const).aestronglyMeasurable fun z => ?_
    have := (fderiv ℝ h (c • x + σ • z)).le_opNorm x
    simpa using this.trans (mul_le_mul_of_nonneg_right (hB1 _) (norm_nonneg _))
  have hI3 : Integrable (fun z : Euc d => fderiv ℝ h (c • x + σ • z) z) (stdGaussian (Euc d)) := by
    refine s83_int_of_poly (C := B1) (p := 1)
      ((hDc.comp hshift).clm_apply continuous_id).aestronglyMeasurable fun z => ?_
    have := (fderiv ℝ h (c • x + σ • z)).le_opNorm z
    have h2 := this.trans (mul_le_mul_of_nonneg_right (hB1 _) (norm_nonneg _))
    calc ‖fderiv ℝ h (c • x + σ • z) z‖ ≤ B1 * ‖z‖ := h2
      _ ≤ B1 * (1 + ‖z‖) ^ 1 := by
          rw [pow_one]; exact mul_le_mul_of_nonneg_left (by linarith [norm_nonneg z]) hB10
  have hI2 : Integrable (fun z : Euc d => s83_lap h (c • x + σ • z)) (stdGaussian (Euc d)) := by
    refine s83_int_of_poly (C := d * B2) (p := 0)
      ((s83_lap_continuous hh).comp hshift).aestronglyMeasurable fun z => ?_
    simpa using s83_lap_bound hB2 _
  have hDy : ∀ z : Euc d, fderiv ℝ h (c • x + σ • z) (c • x + σ • z) =
      c * fderiv ℝ h (c • x + σ • z) x + σ * fderiv ℝ h (c • x + σ • z) z := fun z => by
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hI3' := s83_int_Dh_eval hh hB1 hB2 c σ x
  have hL : ∫ z, fderiv ℝ h (c • x + σ • z)
        ((-a * c) • x + (ν * c ^ 2 / σ) • z) ∂(stdGaussian (Euc d)) =
      (-a * c) * ∫ z, fderiv ℝ h (c • x + σ • z) x ∂(stdGaussian (Euc d)) +
        (ν * c ^ 2 / σ) * ∫ z, fderiv ℝ h (c • x + σ • z) z ∂(stdGaussian (Euc d)) := by
    have e : ∀ z : Euc d, fderiv ℝ h (c • x + σ • z) ((-a * c) • x + (ν * c ^ 2 / σ) • z) =
        (-a * c) * fderiv ℝ h (c • x + σ • z) x +
          (ν * c ^ 2 / σ) * fderiv ℝ h (c • x + σ • z) z := fun z => by
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    simp only [e]
    rw [integral_add (hI1.const_mul _) (hI3.const_mul _), integral_const_mul, integral_const_mul]
  have hR : s83_P a ν τ (s83_L0 a ν h) x =
      ν * ∫ z, s83_lap h (c • x + σ • z) ∂(stdGaussian (Euc d)) -
        a * (c * ∫ z, fderiv ℝ h (c • x + σ • z) x ∂(stdGaussian (Euc d)) +
          σ * ∫ z, fderiv ℝ h (c • x + σ • z) z ∂(stdGaussian (Euc d))) := by
    have e : ∀ z : Euc d, s83_L0 a ν h (c • x + σ • z) =
        ν * s83_lap h (c • x + σ • z) - a * (c * fderiv ℝ h (c • x + σ • z) x +
          σ * fderiv ℝ h (c • x + σ • z) z) := fun z => by
      unfold s83_L0; rw [hDy]
    show ∫ z, s83_L0 a ν h (c • x + σ • z) ∂(stdGaussian (Euc d)) = _
    simp only [e]
    have hsum : Integrable (fun z : Euc d => c * fderiv ℝ h (c • x + σ • z) x +
        σ * fderiv ℝ h (c • x + σ • z) z) (stdGaussian (Euc d)) :=
      (hI1.const_mul c).add (hI3.const_mul σ)
    rw [integral_sub (hI2.const_mul ν) (hsum.const_mul a),
      integral_const_mul, integral_const_mul, integral_add (hI1.const_mul c) (hI3.const_mul σ),
      integral_const_mul, integral_const_mul]
  rw [hL, hR, hI3']
  have hσ2 : a * σ ^ 2 = ν * (1 - c ^ 2) := by
    rw [hσ, hc, s83_ms_sq ha hν.le hτ.le, s83_mc_sq]
    field_simp
  have key : ∀ I : ℝ, (ν * c ^ 2 / σ) * (σ * I) = ν * c ^ 2 * I := fun I => by
    field_simp
  rw [key]
  linear_combination (∫ z, s83_lap h (c • x + σ • z) ∂(stdGaussian (Euc d))) * hσ2

/-- **Kolmogorov equation**: `d/dτ P_τ h (x) = P_τ (L_0 h) (x)` for `τ > 0`, `h ∈ C²` with `h, Dh, D²h`
bounded. -/
theorem s83_P_hasDerivAt {h : Euc d → ℝ} (hh : ContDiff ℝ 2 h) {B0 B1 B2 : ℝ}
    (hB0 : ∀ y, |h y| ≤ B0) (hB1 : ∀ y, ‖fderiv ℝ h y‖ ≤ B1)
    (hB2 : ∀ y, ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ B2) {a ν τ : ℝ} (ha : 0 < a) (hν : 0 < ν) (hτ : 0 < τ)
    (x : Euc d) :
    HasDerivAt (fun τ' => s83_P a ν τ' h x) (s83_P a ν τ (s83_L0 a ν h) x) τ := by
  have hDc := s83_cont_Dh hh
  have hhc : Continuous h := hh.continuous
  have hσlow : 0 < s83_ms a ν (τ / 2) := s83_ms_pos ha hν (by linarith)
  have hB10 : 0 ≤ B1 := (norm_nonneg (fderiv ℝ h 0)).trans (hB1 0)
  have hshift : ∀ τ' : ℝ, Continuous fun z : Euc d => s83_mc a τ' • x + s83_ms a ν τ' • z :=
    fun τ' => continuous_const.add (continuous_const_smul _)
  set K := ν / s83_ms a ν (τ / 2) with hK
  have hK0 : 0 ≤ K := by positivity
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := stdGaussian (Euc d))
    (F := fun (τ' : ℝ) (z : Euc d) => h (s83_mc a τ' • x + s83_ms a ν τ' • z))
    (F' := fun (τ' : ℝ) (z : Euc d) => fderiv ℝ h (s83_mc a τ' • x + s83_ms a ν τ' • z)
      ((-a * s83_mc a τ') • x + (ν * s83_mc a τ' ^ 2 / s83_ms a ν τ') • z))
    (x₀ := τ) (s := Metric.ball τ (τ / 2))
    (bound := fun z : Euc d => B1 * (a * ‖x‖ + K * (1 + ‖z‖)))
    (Metric.ball_mem_nhds _ (by linarith)) ?_ ?_ ?_ ?_ ?_ ?_
  · obtain ⟨-, hd⟩ := key
    refine hd.congr_deriv ?_
    exact s83_kolmogorov_id hh hB1 hB2 ha hν hτ x
  · exact Eventually.of_forall fun τ' => (hhc.comp (hshift τ')).aestronglyMeasurable
  · exact s83_int_of_poly (C := B0) (p := 0) (hhc.comp (hshift τ)).aestronglyMeasurable
      (fun z => by simpa using hB0 _)
  · exact ((hDc.comp (hshift τ)).clm_apply
      (continuous_const.add (continuous_const_smul _))).aestronglyMeasurable
  · refine Eventually.of_forall fun z τ' hτ' => ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hτ'
    have hτ'0 : 0 < τ' := by linarith
    have hmono : s83_ms a ν (τ / 2) ≤ s83_ms a ν τ' := s83_ms_mono ha hν.le (by linarith)
    have hσ'pos : 0 < s83_ms a ν τ' := s83_ms_pos ha hν hτ'0
    have hc1 : s83_mc a τ' ≤ 1 := s83_mc_le_one ha.le hτ'0.le
    have hc0 : 0 < s83_mc a τ' := s83_mc_pos a τ'
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    have h1 : ‖(-a * s83_mc a τ') • x + (ν * s83_mc a τ' ^ 2 / s83_ms a ν τ') • z‖ ≤
        a * ‖x‖ + K * (1 + ‖z‖) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      have e1 : |-a * s83_mc a τ'| ≤ a := by
        rw [abs_mul, abs_neg, abs_of_pos ha, abs_of_pos hc0]; nlinarith
      have e2 : |ν * s83_mc a τ' ^ 2 / s83_ms a ν τ'| ≤ K := by
        rw [abs_of_nonneg (by positivity)]
        have hc2 : s83_mc a τ' ^ 2 ≤ 1 := by nlinarith
        calc ν * s83_mc a τ' ^ 2 / s83_ms a ν τ' ≤ ν * 1 / s83_ms a ν τ' :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc2 hν.le) hσ'pos.le
          _ = ν / s83_ms a ν τ' := by rw [mul_one]
          _ ≤ K := div_le_div_of_nonneg_left hν.le hσlow hmono
      have h3 := mul_le_mul e1 le_rfl (norm_nonneg x) ha.le
      have h4 := mul_le_mul e2 (show ‖z‖ ≤ 1 + ‖z‖ by linarith) (norm_nonneg z) hK0
      linarith
    calc ‖fderiv ℝ h (s83_mc a τ' • x + s83_ms a ν τ' • z)‖ *
          ‖(-a * s83_mc a τ') • x + (ν * s83_mc a τ' ^ 2 / s83_ms a ν τ') • z‖
        ≤ B1 * (a * ‖x‖ + K * (1 + ‖z‖)) :=
          mul_le_mul (hB1 _) h1 (norm_nonneg _) hB10
      _ = _ := rfl
  · have : Integrable (fun z : Euc d => B1 * (a * ‖x‖) + (B1 * K) * (1 + ‖z‖) ^ 1)
        (stdGaussian (Euc d)) :=
      (integrable_const _).add ((s83_int_pow 1).const_mul _)
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only [pow_one]
    ring
  · refine Eventually.of_forall fun z τ' hτ' => ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hτ'
    have hτ'0 : 0 < τ' := by linarith
    have hy : HasDerivAt (fun τ'' => s83_mc a τ'' • x + s83_ms a ν τ'' • z)
        ((-a * s83_mc a τ') • x + (ν * s83_mc a τ' ^ 2 / s83_ms a ν τ') • z) τ' :=
      ((s83_hasDerivAt_mc a τ').smul_const x).add ((s83_hasDerivAt_ms ha hν hτ'0).smul_const z)
    exact (hh.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt τ' hy

end HRS.MS.Wad
