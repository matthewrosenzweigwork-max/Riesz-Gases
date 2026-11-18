import HRS.PDE.MovFAux1

/-!
# MOVF Aux2: `L^p` norm of the density between two tilts of the same reference (bridge C)

`movf_lp_tilted`: for `P` a probability measure, `F` measurable and bounded below, `b₀, b ≥ 0`, `p > 1`,
`p b₀ - (p-1) b ≥ 0`: `P.tilted (-b₀F) ≪ P.tilted (-bF)` and
`‖d P_{b₀}/d P_b‖_{L^p(P_b)} = (Z_b^{p-1} Z_{b₀}^{-p} Z_γ)^{1/p}`, `γ = p b₀ - (p-1) b`, `Z_t = ∫ e^{-tF} dP`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movf_eLpNorm_rnDeriv_eq {α : Type*} [MeasurableSpace α] (ν μ : Measure α) [SigmaFinite ν]
    [SigmaFinite μ] {p : ℝ} (hp : 0 < p) :
    eLpNorm (ν.rnDeriv μ) (ENNReal.ofReal p) μ = (∫⁻ x, (ν.rnDeriv μ x) ^ p ∂μ) ^ (1 / p) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top
    (Measure.measurable_rnDeriv ν μ).aestronglyMeasurable, ENNReal.toReal_ofReal hp.le]
  simp

theorem movf_exp_integrable {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]
    {F : α → ℝ} (hF : Measurable F) {c : ℝ} (hc : ∀ x, -c ≤ F x) {b : ℝ} (hb : 0 ≤ b) :
    Integrable (fun x => Real.exp (-b * F x)) P :=
  Integrable.of_bound (C := Real.exp (b * c))
    (Real.measurable_exp.comp (measurable_const.mul hF)).aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_exp.2 ?_
      nlinarith [hc x])

theorem movf_lp_tilted {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]
    {F : α → ℝ} (hF : Measurable F) {c : ℝ} (hc : ∀ x, -c ≤ F x) {b₀ b p : ℝ} (hb₀ : 0 ≤ b₀)
    (hb : 0 ≤ b) (hp : 1 < p)
    (hiγ : Integrable (fun x => Real.exp (-(p * b₀ - (p - 1) * b) * F x)) P) :
    (P.tilted (fun x => -b₀ * F x) ≪ P.tilted (fun x => -b * F x)) ∧
    eLpNorm ((P.tilted (fun x => -b₀ * F x)).rnDeriv (P.tilted (fun x => -b * F x)))
      (ENNReal.ofReal p) (P.tilted (fun x => -b * F x)) =
      ENNReal.ofReal (((∫ x, Real.exp (-b * F x) ∂P) ^ (p - 1) * (∫ x, Real.exp (-b₀ * F x) ∂P) ^ (-p) *
        ∫ x, Real.exp (-(p * b₀ - (p - 1) * b) * F x) ∂P) ^ (1 / p)) := by
  set f₀ : α → ℝ := fun x => -b₀ * F x with hf₀
  set f₁ : α → ℝ := fun x => -b * F x with hf₁
  set fγ : α → ℝ := fun x => -(p * b₀ - (p - 1) * b) * F x with hfγ
  have hi₀ : Integrable (fun x => Real.exp (f₀ x)) P := movf_exp_integrable P hF hc hb₀
  have hi₁ : Integrable (fun x => Real.exp (f₁ x)) P := movf_exp_integrable P hF hc hb
  have hf₀m : Measurable f₀ := measurable_const.mul hF
  have hf₁m : Measurable f₁ := measurable_const.mul hF
  set Z₀ := ∫ x, Real.exp (f₀ x) ∂P with hZ₀
  set Z₁ := ∫ x, Real.exp (f₁ x) ∂P with hZ₁
  set Zγ := ∫ x, Real.exp (fγ x) ∂P with hZγ
  have hZ₀p : 0 < Z₀ := integral_exp_pos hi₀
  have hZ₁p : 0 < Z₁ := integral_exp_pos hi₁
  have hZγp : 0 < Zγ := integral_exp_pos hiγ
  haveI : IsProbabilityMeasure (P.tilted f₀) := isProbabilityMeasure_tilted hi₀
  haveI : IsProbabilityMeasure (P.tilted f₁) := isProbabilityMeasure_tilted hi₁
  have hac : P.tilted f₀ ≪ P.tilted f₁ :=
    (tilted_absolutelyContinuous P f₀).trans (absolutelyContinuous_tilted hi₁)
  refine ⟨hac, ?_⟩
  rw [movf_eLpNorm_rnDeriv_eq _ _ (by linarith)]
  -- the density of Q₀ with respect to Q₁
  have hrn : (P.tilted f₀).rnDeriv (P.tilted f₁) =ᵐ[P]
      fun x => ENNReal.ofReal (Real.exp (f₀ x - f₁ x) * Z₁ / Z₀) := by
    filter_upwards [rnDeriv_tilted_right (P.tilted f₀) P hi₁,
      rnDeriv_tilted_left_self (μ := P) (f := f₀) hf₀m.aemeasurable] with x h1 h2
    rw [← hZ₁] at h1
    rw [← hZ₀] at h2
    rw [h1, h2, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.exp_sub, Real.exp_neg]
    field_simp
  have hmeas : Measurable fun x => ((P.tilted f₀).rnDeriv (P.tilted f₁) x) ^ p :=
    (Measure.measurable_rnDeriv _ _).pow_const p
  have hQ1 : P.tilted f₁ = P.withDensity fun x => ENNReal.ofReal (Real.exp (f₁ x) / Z₁) := rfl
  have hdens : Measurable fun x => ENNReal.ofReal (Real.exp (f₁ x) / Z₁) :=
    ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp hf₁m).div_const _)
  have key : ∫⁻ x, ((P.tilted f₀).rnDeriv (P.tilted f₁) x) ^ p ∂(P.tilted f₁) =
      ENNReal.ofReal (Z₁ ^ (p - 1) * Z₀ ^ (-p) * Zγ) := by
    have hL := lintegral_withDensity_eq_lintegral_mul P hdens hmeas
    rw [← hQ1] at hL
    rw [hL]
    have h2 : ∀ᵐ x ∂P, (ENNReal.ofReal (Real.exp (f₁ x) / Z₁) *
        ((P.tilted f₀).rnDeriv (P.tilted f₁) x) ^ p) =
        ENNReal.ofReal (Z₁ ^ (p - 1) * Z₀ ^ (-p)) * ENNReal.ofReal (Real.exp (fγ x)) := by
      filter_upwards [hrn] with x hx
      rw [hx, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have e1 : Real.exp (f₀ x - f₁ x) ^ p = Real.exp (p * f₀ x - p * f₁ x) := by
        rw [← Real.exp_mul]; congr 1; ring
      have e2 : Real.exp (fγ x) = Real.exp (p * f₀ x - p * f₁ x) * Real.exp (f₁ x) := by
        rw [← Real.exp_add]; congr 1
        simp only [hf₀, hf₁, hfγ]; ring
      rw [Real.div_rpow (by positivity) hZ₀p.le, Real.mul_rpow (by positivity) hZ₁p.le, e1, e2]
      have e3 : Z₁ ^ p = Z₁ ^ (p - 1) * Z₁ := by
        rw [Real.rpow_sub hZ₁p, Real.rpow_one]; field_simp
      have e4 : Z₀ ^ (-p) = (Z₀ ^ p)⁻¹ := Real.rpow_neg hZ₀p.le p
      rw [e3, e4]
      field_simp
    simp only [Pi.mul_apply]
    rw [lintegral_congr_ae h2, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← ofReal_integral_eq_lintegral_ofReal hiγ (Eventually.of_forall fun x => (Real.exp_pos _).le),
      ← ENNReal.ofReal_mul (by positivity)]
  rw [key, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]

end HRS

end
