import HRS.MS.ThmCons

/-!
# C-POI, part 1: the Gaussian comparison measure is a centered Gaussian

Namespace `HRS.MS.Poinc`; helper lemmas carry the prefix `cpoi_`.

* `cpoi_gam d a β := withDensityReal (gaussianComparison d a β)`;
* `cpoi_gam_eq_map_std`: `γ = (stdGaussian (Euc d)).map (fun x => (βa)^{-1/2} • x)` (characteristic functions);
* `IsGaussian γ`, `IsProbabilityMeasure γ`, centered, rotation invariance of `γ ⊗ γ`
  (`cpoi_map_rotation`), and the second moment `∫ ⟪v,x⟫² dγ = ‖v‖²/(βa)` (`cpoi_integral_inner_sq`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace HRS.MS.Poinc

open HRS.Whole HRS.MS.Thm

variable {d : ℕ}

/-- The Gaussian comparison measure `γ_{βa} dx`. -/
def cpoi_gam (d : ℕ) (a β : ℝ) : Measure (Euc d) :=
  HRS.Whole.withDensityReal (gaussianComparison d a β)

theorem cpoi_gam_isProb {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    IsProbabilityMeasure (cpoi_gam d a β) := by
  constructor
  have h := gaussianComparison_isProbDensity (d := d) ha hβ
  unfold cpoi_gam HRS.Whole.withDensityReal
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (gaussianComparison_integrable ha hβ)
    (ae_of_all _ h.nonneg), h.integral_one]
  simp

/-- Characteristic function of the Gaussian comparison measure. -/
theorem cpoi_charFun_gam {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (t : Euc d) :
    charFun (cpoi_gam d a β) t = Complex.exp (-(‖t‖ ^ 2 / (2 * (β * a)) : ℝ)) := by
  have hb : 0 < β * a / 2 := by positivity
  have hmeas : Measurable fun x : Euc d => (Real.toNNReal (gaussianComparison d a β x)) :=
    (gaussianComparison_measurable a β).real_toNNReal
  have h1 : cpoi_gam d a β =
      volume.withDensity (fun x => ((Real.toNNReal (gaussianComparison d a β x) : NNReal) : ℝ≥0∞)) := rfl
  rw [charFun_apply, h1, integral_withDensity_eq_integral_smul hmeas]
  have h2 : ∀ x : Euc d, (Real.toNNReal (gaussianComparison d a β x)) • Complex.exp (⟪x, t⟫ * Complex.I)
      = (((β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2) : ℝ) : ℂ) *
        Complex.exp (-((β * a / 2 : ℝ) : ℂ) * (‖x‖ : ℂ) ^ 2 + Complex.I * ((⟪t, x⟫ : ℝ) : ℂ)) := by
    intro x
    rw [NNReal.smul_def, Real.coe_toNNReal _ (gaussianComparison_pos ha hβ x).le,
      gaussianComparison_eq, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_exp, mul_assoc,
      ← Complex.exp_add]
    congr 2
    rw [real_inner_comm]
    push_cast
    ring_nf
  simp_rw [h2]
  rw [integral_const_mul]
  have h3 := GaussianFourier.integral_cexp_neg_mul_sq_norm_add (V := Euc d)
    (b := ((β * a / 2 : ℝ) : ℂ)) (by simpa using hb) Complex.I t
  rw [h3]
  have hfr : (Module.finrank ℝ (Euc d) : ℂ) = (d : ℂ) := by simp
  rw [hfr]
  have h4 : ((β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2) : ℝ) * (Real.pi / (β * a / 2)) ^ ((d : ℝ) / 2) = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    have : β * a / (2 * Real.pi) * (Real.pi / (β * a / 2)) = 1 := by field_simp
    rw [this, Real.one_rpow]
  have h5 : (((β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2) : ℝ) : ℂ) *
      ((Real.pi : ℂ) / ((β * a / 2 : ℝ) : ℂ)) ^ ((d : ℂ) / 2) = 1 := by
    have : ((Real.pi : ℂ) / ((β * a / 2 : ℝ) : ℂ)) ^ ((d : ℂ) / 2) =
        (((Real.pi / (β * a / 2)) ^ ((d : ℝ) / 2) : ℝ) : ℂ) := by
      have := Complex.ofReal_cpow (x := Real.pi / (β * a / 2)) (by positivity) ((d : ℝ) / 2)
      push_cast at this
      push_cast
      exact this.symm
    rw [this, ← Complex.ofReal_mul, h4]; simp
  rw [← mul_assoc, h5, one_mul]
  congr 1
  have hb0 : (β : ℂ) * a ≠ 0 := by
    have : β * a ≠ 0 := by positivity
    exact_mod_cast this
  push_cast
  field_simp
  simp [Complex.I_sq]
  ring

/-- The scaling constant `r = (βa)^{-1/2}`. -/
def cpoi_r (a β : ℝ) : ℝ := (Real.sqrt (β * a))⁻¹

theorem cpoi_r_sq {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) : cpoi_r a β ^ 2 = (β * a)⁻¹ := by
  unfold cpoi_r
  rw [inv_pow, Real.sq_sqrt (by positivity)]

/-- `γ_{βa}` is the image of the standard Gaussian under `x ↦ (βa)^{-1/2} x`. -/
theorem cpoi_gam_eq {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    cpoi_gam d a β = (stdGaussian (Euc d)).map (fun x => cpoi_r a β • x) := by
  have := cpoi_gam_isProb (d := d) ha hβ
  apply Measure.ext_of_charFun
  ext t
  have hr : (‖cpoi_r a β‖ * ‖t‖) ^ 2 = ‖t‖ ^ 2 / (β * a) := by
    rw [mul_pow, Real.norm_eq_abs, sq_abs, cpoi_r_sq ha hβ]; field_simp
  rw [cpoi_charFun_gam ha hβ, charFun_map_smul, charFun_stdGaussian, norm_smul,
    ← Complex.ofReal_pow, hr]
  congr 1
  push_cast
  field_simp

theorem cpoi_gam_map_clm (a β : ℝ) :
    (stdGaussian (Euc d)).map (fun x => cpoi_r a β • x) =
      (stdGaussian (Euc d)).map ((cpoi_r a β • ContinuousLinearMap.id ℝ (Euc d) :
        Euc d →L[ℝ] Euc d)) := rfl

theorem cpoi_gam_isGaussian {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) : IsGaussian (cpoi_gam d a β) := by
  rw [cpoi_gam_eq ha hβ, cpoi_gam_map_clm]
  infer_instance

theorem cpoi_gam_integral_id {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    (cpoi_gam d a β)[id] = 0 := by
  rw [cpoi_gam_eq ha hβ]
  show ∫ x, x ∂(Measure.map _ _) = 0
  rw [integral_map (by fun_prop) (by fun_prop)]
  rw [integral_smul, integral_id_stdGaussian, smul_zero]

/-- Second moment of a linear functional under `γ`. -/
theorem cpoi_integral_inner_sq {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (v : Euc d) :
    ∫ x, ⟪v, x⟫ ^ 2 ∂(cpoi_gam d a β) = ‖v‖ ^ 2 / (β * a) := by
  rw [cpoi_gam_eq ha hβ, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [inner_smul_right, mul_pow]
  rw [integral_const_mul, cpoi_r_sq ha hβ]
  have h1 := variance_dual_stdGaussian (E := Euc d) (innerSL ℝ v)
  rw [variance_of_integral_eq_zero (by fun_prop) (integral_strongDual_stdGaussian _)] at h1
  have h2 : ∫ x, ⟪v, x⟫ ^ 2 ∂(stdGaussian (Euc d)) = ‖v‖ ^ 2 := by
    simpa [innerSL_apply_apply, innerSL_apply_norm] using h1
  rw [h2]; ring

theorem cpoi_map_rotation {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (θ : ℝ) :
    ((cpoi_gam d a β).prod (cpoi_gam d a β)).map (ContinuousLinearMap.rotation θ) =
      (cpoi_gam d a β).prod (cpoi_gam d a β) := by
  haveI := cpoi_gam_isGaussian (d := d) ha hβ
  exact IsGaussian.map_rotation_eq_self (cpoi_gam_integral_id ha hβ) θ

end HRS.MS.Poinc

end
