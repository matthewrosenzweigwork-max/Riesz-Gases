import HRS.MS.PoincAux3
import HRS.MS.ThmCons
import HRS.Whole.Static

/-!
# C-POI: the Gaussian Poincare inequality on `Euc d` and `euc_thermal_gaussian_bounds`

Maurey-Pisier interpolation (`PoincAux1..3`) gives, for `γ = γ_{βa} dx`,
`Var_γ f ≤ (π²/8) (βa)⁻¹ ∫ |∇f|² dγ` for `C¹` functions `f ∈ L²(γ)` with `∇f ∈ L²(γ)`
(`cpoi_gauss_poincare`), i.e. `CbGaussPoincare d a β (π²/8)` of `ThmCons`.
Combined with the merged transfer `cb_euc_thermal_gaussian_bounds_of_poincare` this proves
`HRS.Whole.euc_thermal_gaussian_bounds` (`euc_thermal_gaussian_bounds_proof`).
The constant in the Poincare inequality of the frozen statement is `C (1 + π²/8)/(c β a)`
for the comparison constants of `cb_thermal_two_sided` (the frozen `C` is existential, so enlarging it
is harmless).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace HRS.MS.Poinc

variable {d : ℕ}

/-- **Gaussian Poincare inequality** (Maurey-Pisier constant `π²/8`). -/
theorem cpoi_gauss_poincare {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {f : Euc d → ℝ}
    (hf : ContDiff ℝ 1 f) (hL2 : MemLp f 2 (cpoi_gam d a β))
    (hg : Integrable (fun x => ‖gradient f x‖ ^ 2) (cpoi_gam d a β)) :
    variance f (cpoi_gam d a β) ≤
      (Real.pi ^ 2 / 8) / (β * a) * ∫ x, ‖gradient f x‖ ^ 2 ∂(cpoi_gam d a β) := by
  have hP := cpoi_gam_isProb (d := d) ha hβ
  set γ := cpoi_gam d a β with hγ
  set K := (β * a)⁻¹ * ∫ x, ‖gradient f x‖ ^ 2 ∂γ with hK
  have hK0 : 0 ≤ K := by
    rw [hK]; exact mul_nonneg (by positivity) (integral_nonneg fun x => by positivity)
  have hfm : AEMeasurable f γ := hf.continuous.measurable.aemeasurable
  set m := ∫ x, f x ∂γ with hm
  set g : Euc d → ℝ := fun x => f x - m with hgdef
  have hgL2 : MemLp g 2 γ := hL2.sub (memLp_const m)
  have hg2 : Integrable (fun x => g x ^ 2) γ := hgL2.integrable_sq
  have hg1 : Integrable g γ := hgL2.integrable one_le_two
  have hg0 : ∫ x, g x ∂γ = 0 := by
    simp only [hgdef]
    rw [integral_sub (hL2.integrable one_le_two) (integrable_const m)]
    simp [hm]
  have hvar : variance f γ = ∫ x, g x ^ 2 ∂γ := by
    rw [variance_eq_integral hfm]
  -- the double integral
  have hE : ∫ q, (f q.2 - f q.1) ^ 2 ∂(γ.prod γ) = 2 * ∫ x, g x ^ 2 ∂γ := by
    have e : ∀ q : Euc d × Euc d, (f q.2 - f q.1) ^ 2 =
        1 * g q.2 ^ 2 + (g q.1 ^ 2 * 1 - 2 * (g q.1 * g q.2)) := by
      intro q; simp only [hgdef]; ring
    simp_rw [e]
    have i1 : Integrable (fun q : Euc d × Euc d => 1 * g q.2 ^ 2) (γ.prod γ) :=
      Integrable.mul_prod (integrable_const (1 : ℝ)) hg2
    have i2 : Integrable (fun q : Euc d × Euc d => g q.1 ^ 2 * 1) (γ.prod γ) :=
      Integrable.mul_prod hg2 (integrable_const (1 : ℝ))
    have i3 : Integrable (fun q : Euc d × Euc d => g q.1 * g q.2) (γ.prod γ) :=
      Integrable.mul_prod hg1 hg1
    have i4 : Integrable (fun q : Euc d × Euc d => 2 * (g q.1 * g q.2)) (γ.prod γ) := i3.const_mul 2
    have i23 : Integrable (fun q : Euc d × Euc d => g q.1 ^ 2 * 1 - 2 * (g q.1 * g q.2)) (γ.prod γ) :=
      i2.sub i4
    have j1 : ∫ q : Euc d × Euc d, 1 * g q.2 ^ 2 ∂(γ.prod γ) = ∫ x, g x ^ 2 ∂γ := by
      have := integral_prod_mul (μ := γ) (ν := γ) (fun _ => (1 : ℝ)) (fun x => g x ^ 2)
      simpa using this
    have j2 : ∫ q : Euc d × Euc d, g q.1 ^ 2 * 1 ∂(γ.prod γ) = ∫ x, g x ^ 2 ∂γ := by
      have := integral_prod_mul (μ := γ) (ν := γ) (fun x => g x ^ 2) (fun _ => (1 : ℝ))
      simpa using this
    have j3 : ∫ q : Euc d × Euc d, g q.1 * g q.2 ∂(γ.prod γ) = 0 := by
      have := integral_prod_mul (μ := γ) (ν := γ) g g
      rw [this, hg0]; simp
    rw [integral_add i1 i23, integral_sub i2 i4,
      integral_const_mul (2 : ℝ) (fun q : Euc d × Euc d => g q.1 * g q.2), j1, j2, j3]
    ring
  -- the bound
  have hbd := cpoi_lintegral_diff_le ha hβ hf hg
  have hnn : (0 : ℝ) ≤ (Real.pi / 2) ^ 2 * K := by positivity
  have hmeas : Measurable fun q : Euc d × Euc d => (f q.2 - f q.1) ^ 2 := by
    have : Continuous fun q : Euc d × Euc d => (f q.2 - f q.1) ^ 2 := by
      have := hf.continuous
      fun_prop
    exact this.measurable
  have hle : ∫ q, (f q.2 - f q.1) ^ 2 ∂(γ.prod γ) ≤ (Real.pi / 2) ^ 2 * K := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun q => sq_nonneg _)
      hmeas.aestronglyMeasurable]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbd
    rwa [ENNReal.toReal_ofReal hnn] at this
  rw [hE] at hle
  have hv : variance f γ = ∫ x, g x ^ 2 ∂γ := hvar
  rw [hK] at hle
  rw [hv]
  have : (Real.pi ^ 2 / 8) / (β * a) * ∫ x, ‖gradient f x‖ ^ 2 ∂γ =
      (Real.pi / 2) ^ 2 * K / 2 := by
    rw [hK]; field_simp; ring
  rw [this]
  linarith

/-- The Gaussian Poincare inequality in the form `CbGaussPoincare` of `ThmCons`, with `κ = π²/8`. -/
theorem cpoi_gaussPoincare {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    HRS.MS.Thm.CbGaussPoincare d a β (Real.pi ^ 2 / 8) :=
  fun _ hf hL2 hg => cpoi_gauss_poincare ha hβ hf hL2 hg

/-- **C-POI.** Proof of `HRS.Whole.euc_thermal_gaussian_bounds`. -/
theorem euc_thermal_gaussian_bounds_proof : type_of% @HRS.Whole.euc_thermal_gaussian_bounds := by
  intro d s hd hs0 hsd a β ha hβ
  exact HRS.MS.Thm.cb_euc_thermal_gaussian_bounds_of_poincare hd hs0 hsd a β ha hβ (by positivity)
    (cpoi_gaussPoincare ha hβ)

end HRS.MS.Poinc

end
