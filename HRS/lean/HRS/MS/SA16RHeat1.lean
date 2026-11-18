import HRS.MS.SA16RExt2

/-!
# S.A.16 (SA16R) Heat1: the Gaussian heat kernel on `ℝ^d`

`sa16r_g d a z = (4π a)^{-d/2} exp(-‖z‖²/(4a))`, the kernel of `e^{aΔ}`.  Mass one (`sa16r_g_mass`), smooth, positive,
gradient `∂_i g = -(z_i/(2a)) g` (`sa16r_dg`), with `‖∂_i g_a‖_{L¹} ≤ (4/3)^{d/2} a^{-1/2}` (`sa16r_dg_L1`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA

section Heat1
variable {d : ℕ}

lemma sa16r_gauss_int {b : ℝ} (hb : 0 < b) : Integrable (fun z : Euc d => Real.exp (-b * ‖z‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Euc d)
    (show 0 < (b : ℂ).re from hb) 0 0).norm
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp only [mul_zero, add_zero]
  rw [Complex.norm_exp]
  congr 1
  simp [← Complex.ofReal_pow]

lemma sa16r_gauss_integral {b : ℝ} (hb : 0 < b) :
    ∫ z : Euc d, Real.exp (-b * ‖z‖ ^ 2) = (Real.pi / b) ^ ((d : ℝ) / 2) := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb, finrank_euclideanSpace_fin]

/-- the heat kernel of `e^{aΔ}` -/
def sa16r_g (d : ℕ) (a : ℝ) (z : Euc d) : ℝ :=
  (4 * Real.pi * a) ^ (-((d : ℝ) / 2)) * Real.exp (-(1 / (4 * a)) * ‖z‖ ^ 2)

lemma sa16r_g_pos {a : ℝ} (ha : 0 < a) (z : Euc d) : 0 < sa16r_g d a z := by
  unfold sa16r_g
  have : 0 < 4 * Real.pi * a := by positivity
  exact mul_pos (Real.rpow_pos_of_pos this _) (Real.exp_pos _)

lemma sa16r_g_int {a : ℝ} (ha : 0 < a) : Integrable (sa16r_g d a) := by
  unfold sa16r_g
  exact (sa16r_gauss_int (b := 1 / (4 * a)) (by positivity)).const_mul _

lemma sa16r_g_mass {a : ℝ} (ha : 0 < a) : ∫ z : Euc d, sa16r_g d a z = 1 := by
  unfold sa16r_g
  rw [integral_const_mul, sa16r_gauss_integral (by positivity : 0 < 1 / (4 * a))]
  have hN : 0 < 4 * Real.pi * a := by positivity
  have : Real.pi / (1 / (4 * a)) = 4 * Real.pi * a := by field_simp
  rw [this, ← Real.rpow_add hN]
  simp

lemma sa16r_g_contDiff {a : ℝ} : ContDiff ℝ ∞ (sa16r_g d a) := by
  unfold sa16r_g
  refine contDiff_const.mul (Real.contDiff_exp.comp (contDiff_const.mul ?_))
  exact (contDiff_norm_sq ℝ)

lemma sa16r_g_meas {a : ℝ} : Measurable (sa16r_g d a) := (sa16r_g_contDiff (a := a)).continuous.measurable

/-- the coordinate derivative `∂_i g_a` -/
def sa16r_dg (d : ℕ) (a : ℝ) (i : Fin d) (z : Euc d) : ℝ := -(z i) / (2 * a) * sa16r_g d a z

lemma sa16r_g_fderiv {a : ℝ} (ha : 0 < a) (z : Euc d) (i : Fin d) :
    fderiv ℝ (sa16r_g d a) z (EuclideanSpace.single i 1) = sa16r_dg d a i z := by
  have h1 : HasFDerivAt (fun z : Euc d => ‖z‖ ^ 2) (2 • innerSL ℝ z) z := by
    simpa using (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have h2 := ((h1.const_mul (-(1 / (4 * a)))).exp).const_mul ((4 * Real.pi * a) ^ (-((d : ℝ) / 2)))
  have hfun : sa16r_g d a = fun z => (4 * Real.pi * a) ^ (-((d : ℝ) / 2)) *
      Real.exp (-(1 / (4 * a)) * ‖z‖ ^ 2) := rfl
  rw [hfun, h2.fderiv]
  simp [sa16r_dg, sa16r_g, innerSL_apply_apply, EuclideanSpace.inner_single_right]
  field_simp
  ring

lemma sa16r_norm_le_exp {a : ℝ} (ha : 0 < a) (E : ℝ) (hE : 0 ≤ E) :
    E ≤ 2 * Real.sqrt a * Real.exp (E ^ 2 / (16 * a)) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ a = s ^ 2 := ⟨Real.sqrt a, Real.sqrt_pos.2 ha, (Real.sq_sqrt ha.le).symm⟩
  rw [Real.sqrt_sq hs.le]
  have h1 := Real.add_one_le_exp (E ^ 2 / (16 * s ^ 2))
  have h2 : E ≤ 2 * s * (E ^ 2 / (16 * s ^ 2) + 1) := by
    have : 2 * s * (E ^ 2 / (16 * s ^ 2) + 1) = (E ^ 2 + 16 * s ^ 2) / (8 * s) := by
      field_simp; ring
    rw [this, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (E - 4 * s)]
  calc E ≤ 2 * s * (E ^ 2 / (16 * s ^ 2) + 1) := h2
    _ ≤ 2 * s * Real.exp (E ^ 2 / (16 * s ^ 2)) := by gcongr

lemma sa16r_dg_pointwise {a : ℝ} (ha : 0 < a) (i : Fin d) (z : Euc d) :
    |sa16r_dg d a i z| ≤ a ^ (-(1 / 2 : ℝ)) * (4 / 3 : ℝ) ^ ((d : ℝ) / 2) * sa16r_g d (4 * a / 3) z := by
  have hN : 0 < 4 * Real.pi * a := by positivity
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hss : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  set E : ℝ := ‖z‖ with hE
  have h1 : |z i| ≤ E := by
    have := PiLp.norm_apply_le z i
    simpa [Real.norm_eq_abs] using this
  have h2 := sa16r_norm_le_exp ha E (norm_nonneg z)
  have hg : sa16r_dg d a i z = -(z i) / (2 * a) * sa16r_g d a z := rfl
  have hgpos := sa16r_g_pos ha z
  have hrw : a ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt a := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg ha.le]; simp
  have hsa : (2 * Real.sqrt a) / (2 * a) = 1 / Real.sqrt a := by
    obtain ⟨s, hs0, rfl⟩ : ∃ s : ℝ, 0 < s ∧ a = s ^ 2 := ⟨Real.sqrt a, hs, hss.symm⟩
    rw [Real.sqrt_sq hs0.le]; field_simp
  -- exponential identity
  have hexp : Real.exp (E ^ 2 / (16 * a)) * Real.exp (-(1 / (4 * a)) * E ^ 2) =
      Real.exp (-(1 / (4 * (4 * a / 3))) * E ^ 2) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  -- prefactor identity
  have hpre : (4 * Real.pi * a) ^ (-((d : ℝ) / 2)) =
      (4 / 3 : ℝ) ^ ((d : ℝ) / 2) * (4 * Real.pi * (4 * a / 3)) ^ (-((d : ℝ) / 2)) := by
    have h4 : 4 * Real.pi * (4 * a / 3) = (4 / 3 : ℝ) * (4 * Real.pi * a) := by ring
    rw [h4, Real.mul_rpow (by norm_num) hN.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4 / 3)]
    have : (4 / 3 : ℝ) ^ ((d : ℝ) / 2) * (((4 / 3 : ℝ) ^ ((d : ℝ) / 2))⁻¹ *
        (4 * Real.pi * a) ^ (-((d : ℝ) / 2))) = (4 * Real.pi * a) ^ (-((d : ℝ) / 2)) := by
      rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    exact this.symm
  have hgg : sa16r_g d a z = (4 / 3 : ℝ) ^ ((d : ℝ) / 2) * (4 * Real.pi * (4 * a / 3)) ^ (-((d : ℝ) / 2)) *
      Real.exp (-(1 / (4 * a)) * E ^ 2) := by
    unfold sa16r_g; rw [hpre]
  rw [hg, abs_mul, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * a), abs_of_pos hgpos]
  have hC : 0 ≤ (4 / 3 : ℝ) ^ ((d : ℝ) / 2) * (4 * Real.pi * (4 * a / 3)) ^ (-((d : ℝ) / 2)) := by positivity
  calc |z i| / (2 * a) * sa16r_g d a z
      ≤ (E / (2 * a)) * sa16r_g d a z := by gcongr
    _ ≤ ((2 * Real.sqrt a * Real.exp (E ^ 2 / (16 * a))) / (2 * a)) * sa16r_g d a z := by gcongr
    _ = (1 / Real.sqrt a) * ((4 / 3 : ℝ) ^ ((d : ℝ) / 2) *
          ((4 * Real.pi * (4 * a / 3)) ^ (-((d : ℝ) / 2)) *
            (Real.exp (E ^ 2 / (16 * a)) * Real.exp (-(1 / (4 * a)) * E ^ 2)))) := by
        rw [hgg]
        have : (2 * Real.sqrt a) / (2 * a) = 1 / Real.sqrt a := hsa
        calc (2 * Real.sqrt a * Real.exp (E ^ 2 / (16 * a))) / (2 * a) *
              ((4 / 3 : ℝ) ^ ((d : ℝ) / 2) * (4 * Real.pi * (4 * a / 3)) ^ (-((d : ℝ) / 2)) *
                Real.exp (-(1 / (4 * a)) * E ^ 2))
            = ((2 * Real.sqrt a) / (2 * a)) * Real.exp (E ^ 2 / (16 * a)) *
              ((4 / 3 : ℝ) ^ ((d : ℝ) / 2) * (4 * Real.pi * (4 * a / 3)) ^ (-((d : ℝ) / 2)) *
                Real.exp (-(1 / (4 * a)) * E ^ 2)) := by ring
          _ = _ := by rw [this]; ring
    _ = a ^ (-(1 / 2 : ℝ)) * (4 / 3 : ℝ) ^ ((d : ℝ) / 2) * sa16r_g d (4 * a / 3) z := by
        rw [hexp, hrw]
        unfold sa16r_g
        ring

lemma sa16r_dg_cont (a : ℝ) (i : Fin d) : Continuous (sa16r_dg d a i) := by
  unfold sa16r_dg
  exact (((continuous_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ))).neg.div_const _).mul
    (sa16r_g_contDiff (a := a)).continuous

lemma sa16r_dg_int {a : ℝ} (ha : 0 < a) (i : Fin d) : Integrable (sa16r_dg d a i) := by
  have h43 : 0 < 4 * a / 3 := by positivity
  refine Integrable.mono' ((sa16r_g_int h43).const_mul (a ^ (-(1 / 2 : ℝ)) * (4 / 3 : ℝ) ^ ((d : ℝ) / 2)))
    (sa16r_dg_cont a i).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]
  exact sa16r_dg_pointwise ha i z

lemma sa16r_dg_L1 {a : ℝ} (ha : 0 < a) (i : Fin d) :
    ∫ z, |sa16r_dg d a i z| ≤ a ^ (-(1 / 2 : ℝ)) * (4 / 3 : ℝ) ^ ((d : ℝ) / 2) := by
  have h43 : 0 < 4 * a / 3 := by positivity
  calc ∫ z, |sa16r_dg d a i z|
      ≤ ∫ z, a ^ (-(1 / 2 : ℝ)) * (4 / 3 : ℝ) ^ ((d : ℝ) / 2) * sa16r_g d (4 * a / 3) z :=
        integral_mono (sa16r_dg_int ha i).abs
          ((sa16r_g_int h43).const_mul _) (fun z => sa16r_dg_pointwise ha i z)
    _ = a ^ (-(1 / 2 : ℝ)) * (4 / 3 : ℝ) ^ ((d : ℝ) / 2) := by
        rw [integral_const_mul, sa16r_g_mass h43, mul_one]

end Heat1

end HRS.Whole.AppendixA.Phase2SA16R
