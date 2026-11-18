import HRS.Whole.Q34Aux10

/-!
# Packet Q34, helper file 11: linearity and symmetry of the integral operator
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric InnerProductSpace
open scoped ENNReal NNReal

namespace HRS.Whole.Q34

variable {d : ℕ} {s : ℝ} {ρ : Euc d → ℝ} {M : ℝ}

theorem tk_congr_ae {ν : Measure (Euc d)} {u u' : Euc d → ℝ} (h : u =ᵐ[ν] u') :
    Tk s ν u = Tk s ν u' := by
  funext x
  unfold Tk
  refine integral_congr_ae ?_
  filter_upwards [h] with y hy
  rw [hy]

theorem tk_smul (ν : Measure (Euc d)) (c : ℝ) (u : Euc d → ℝ) :
    Tk s ν (c • u) = c • Tk s ν u := by
  funext x
  unfold Tk
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  ring

theorem tk_add_ae (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) (hρ : IsProbDensity ρ)
    (hM : ∀ x, ρ x ≤ M) {u v : Euc d → ℝ} (hu : Measurable u) (hv : Measurable v)
    (hu2 : MemLp u 2 (withDensityReal ρ)) (hv2 : MemLp v 2 (withDensityReal ρ)) :
    Tk s (withDensityReal ρ) (u + v) =ᵐ[withDensityReal ρ]
      Tk s (withDensityReal ρ) u + Tk s (withDensityReal ρ) v := by
  filter_upwards [tk_ae_integrable hd hs0 hsd hρ hM hu hu2,
    tk_ae_integrable hd hs0 hsd hρ hM hv hv2] with x h1 h2
  unfold Tk
  simp only [Pi.add_apply, Pi.add_apply, mul_add]
  exact integral_add h1 h2

theorem mul_le_sq_add_sq (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := mul_le_mul' h le_rfl
      _ = b ^ 2 := (sq b).symm
      _ ≤ a ^ 2 + b ^ 2 := le_add_self
  · calc a * b ≤ a * a := mul_le_mul' le_rfl h
      _ = a ^ 2 := (sq a).symm
      _ ≤ a ^ 2 + b ^ 2 := le_self_add

/-- Integrability of the symmetric pair integrand. -/
theorem tk_pair_integrable (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) (hρ : IsProbDensity ρ)
    (hM : ∀ x, ρ x ≤ M) {u v : Euc d → ℝ} (hu : Measurable u) (hv : Measurable v)
    (hu2 : MemLp u 2 (withDensityReal ρ)) (hv2 : MemLp v 2 (withDensityReal ρ)) :
    Integrable (fun p : Euc d × Euc d => ‖p.1 - p.2‖ ^ (-s) * u p.2 * v p.1)
      ((withDensityReal ρ).prod (withDensityReal ρ)) := by
  have := isProbabilityMeasure_nu hρ
  set ν := withDensityReal ρ with hν
  have hmeas : Measurable (fun p : Euc d × Euc d => ‖p.1 - p.2‖ ^ (-s) * u p.2 * v p.1) :=
    (((measurable_norm.comp (measurable_fst.sub measurable_snd)).pow_const _).mul
      (hu.comp measurable_snd)).mul (hv.comp measurable_fst)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hN := lintegral_Nu_sq_le hd hs0 hsd hρ hM hu hu2
  have hv_int : ∫⁻ x, ENNReal.ofReal |v x| ^ 2 ∂ν < ∞ := by
    have : ∫⁻ x, ENNReal.ofReal |v x| ^ 2 ∂ν = ENNReal.ofReal (∫ x, v x ^ 2 ∂ν) := by
      rw [ofReal_integral_eq_lintegral_ofReal (hv2.integrable_sq)
        (Filter.Eventually.of_forall fun x => sq_nonneg _)]
      refine lintegral_congr fun y => ?_
      rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    rw [this]; exact ENNReal.ofReal_lt_top
  have hrw : ∫⁻ p, ‖‖p.1 - p.2‖ ^ (-s) * u p.2 * v p.1‖ₑ ∂(ν.prod ν) =
      ∫⁻ x, ENNReal.ofReal |v x| * Nu s ν u x ∂ν := by
    rw [lintegral_prod _ (hmeas.enorm.aemeasurable)]
    refine lintegral_congr fun x => ?_
    have : ∀ y : Euc d, ‖‖(x, y).1 - (x, y).2‖ ^ (-s) * u (x, y).2 * v (x, y).1‖ₑ =
        ENNReal.ofReal |v x| * (ENNReal.ofReal (‖x - y‖ ^ (-s)) * ENNReal.ofReal |u y|) := by
      intro y
      simp only
      rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
        ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (abs_nonneg _)),
        ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)]
      ring
    simp_rw [this]
    have hm : Measurable (fun y : Euc d =>
        ENNReal.ofReal (‖x - y‖ ^ (-s)) * ENNReal.ofReal |u y|) := by fun_prop
    rw [lintegral_const_mul _ hm]
    rfl
  simp only [HasFiniteIntegral, hrw]
  calc ∫⁻ x, ENNReal.ofReal |v x| * Nu s ν u x ∂ν
      ≤ ∫⁻ x, (ENNReal.ofReal |v x| ^ 2 + Nu s ν u x ^ 2) ∂ν :=
        lintegral_mono fun x => mul_le_sq_add_sq _ _
    _ = ∫⁻ x, ENNReal.ofReal |v x| ^ 2 ∂ν + ∫⁻ x, Nu s ν u x ^ 2 ∂ν :=
        lintegral_add_left (hv.abs.ennreal_ofReal.pow_const 2) _
    _ < ∞ := ENNReal.add_lt_top.2 ⟨hv_int, hN.trans_lt ENNReal.ofReal_lt_top⟩

/-- Symmetry of the integral operator: `⟨T u, v⟩ = ⟨u, T v⟩`. -/
theorem tk_symm (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) (hρ : IsProbDensity ρ)
    (hM : ∀ x, ρ x ≤ M) {u v : Euc d → ℝ} (hu : Measurable u) (hv : Measurable v)
    (hu2 : MemLp u 2 (withDensityReal ρ)) (hv2 : MemLp v 2 (withDensityReal ρ)) :
    ∫ x, Tk s (withDensityReal ρ) u x * v x ∂(withDensityReal ρ) =
      ∫ x, u x * Tk s (withDensityReal ρ) v x ∂(withDensityReal ρ) := by
  have := isProbabilityMeasure_nu hρ
  set ν := withDensityReal ρ with hν
  have hI := tk_pair_integrable hd hs0 hsd hρ hM hu hv hu2 hv2
  have h1 : ∫ x, Tk s ν u x * v x ∂ν =
      ∫ x, ∫ y, ‖x - y‖ ^ (-s) * u y * v x ∂ν ∂ν := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Tk]
    rw [← integral_mul_const]
  have h2 : ∫ x, u x * Tk s ν v x ∂ν =
      ∫ y, ∫ x, ‖x - y‖ ^ (-s) * u y * v x ∂ν ∂ν := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [Tk]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show u y * (‖y - x‖ ^ (-s) * v x) = ‖x - y‖ ^ (-s) * u y * v x
    rw [norm_sub_rev y x]
    ring
  rw [h1, h2]
  exact integral_integral_swap (f := fun x y => ‖x - y‖ ^ (-s) * u y * v x) hI

end HRS.Whole.Q34
