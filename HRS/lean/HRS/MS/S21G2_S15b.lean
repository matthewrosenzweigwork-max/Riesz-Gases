import HRS.MS.S21G2_S15a

/-!
# S21G2 S15b -- finite Gaussian quadratic tilt and determinant factors (R26-T3.S15b)

For `λ_j ≥ 0`, `γ ≥ 0` (the binder `λ` is not allowed: renamed `lam`): under the product of standard Gaussians
`E exp(-(γ/2) ∑ λ_j (x_j² - 1)) = exp(½ ∑ (γλ_j - log (1+γλ_j)))` and the tilt by `(γ/2) ∑ λ_j (x_j² - 1)` is the product of
the centred Gaussians of variances `(1+γλ_j)⁻¹`.  Route: the one-dimensional rectangle identity
`∫ 1_s e^{-(t/2)(x²-1)} dN(0,1) = Z(t) N(0,(1+t)⁻¹)(s)` (density comparison), then `integral_fintype_prod_eq_prod` and
`Measure.pi_eq`.  Helper names carry the prefix `s21g2_s15b_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

/-- The one-dimensional normalising constant. -/
def s21g2_s15b_Z (t : ℝ) : ℝ := Real.exp ((1 / 2) * (t - Real.log (1 + t)))

theorem s21g2_s15b_pdf {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    gaussianPDFReal 0 1 x * Real.exp (-(t / 2) * (x ^ 2 - 1)) =
      s21g2_s15b_Z t * gaussianPDFReal 0 ((1 + t)⁻¹).toNNReal x := by
  have h1 : (0 : ℝ) < 1 + t := by linarith
  have hv : (((1 + t)⁻¹).toNNReal : ℝ) = (1 + t)⁻¹ := Real.coe_toNNReal _ (inv_nonneg.2 h1.le)
  unfold gaussianPDFReal s21g2_s15b_Z
  rw [hv]
  have hs : Real.sqrt (2 * Real.pi * (1 + t)⁻¹) = Real.sqrt (2 * Real.pi) * (Real.sqrt (1 + t))⁻¹ := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_inv]
  have hl : Real.exp ((1 / 2) * (t - Real.log (1 + t))) =
      Real.exp (t / 2) * (Real.sqrt (1 + t))⁻¹ := by
    rw [show (1 / 2) * (t - Real.log (1 + t)) = t / 2 + -((1 / 2) * Real.log (1 + t)) by ring,
      Real.exp_add, Real.exp_neg, Real.sqrt_eq_rpow, Real.rpow_def_of_pos h1]
    ring_nf
  have hq : Real.sqrt (1 + t) ≠ 0 := (Real.sqrt_pos.2 h1).ne'
  have hp : Real.sqrt (2 * Real.pi) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [hs, hl]
  have : Real.exp (-x ^ 2 / 2) * Real.exp (-(t / 2) * (x ^ 2 - 1)) =
      Real.exp (t / 2) * Real.exp (-x ^ 2 / (2 * (1 + t)⁻¹)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; field_simp; ring
  calc (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) * Real.exp (-(t / 2) * (x ^ 2 - 1))
      = (Real.sqrt (2 * Real.pi))⁻¹ * (Real.exp (-x ^ 2 / 2) * Real.exp (-(t / 2) * (x ^ 2 - 1))) := by ring
    _ = _ := by rw [this]; field_simp

theorem s21g2_s15b_rect {t : ℝ} (ht : 0 ≤ t) {s : Set ℝ} (hs : MeasurableSet s) :
    ∫ x, s.indicator (fun x => Real.exp (-(t / 2) * (x ^ 2 - 1))) x ∂(gaussianReal 0 1) =
      s21g2_s15b_Z t * (gaussianReal 0 ((1 + t)⁻¹).toNNReal s).toReal := by
  have h1 : (0 : ℝ) < 1 + t := by linarith
  have hv : ((1 + t)⁻¹).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; exact inv_pos.2 h1
  rw [integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0),
    gaussianReal_apply_eq_integral 0 hv s,
    ENNReal.toReal_ofReal (integral_nonneg fun x => gaussianPDFReal_nonneg _ _ _),
    ← integral_const_mul, ← integral_indicator hs]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  by_cases hx : x ∈ s
  · simp only [Set.indicator_of_mem hx, smul_eq_mul]
    exact s21g2_s15b_pdf ht x
  · simp [Set.indicator_of_notMem hx]

theorem s21g2_s15b_Z_eq {t : ℝ} (ht : 0 ≤ t) :
    ∫ x, Real.exp (-(t / 2) * (x ^ 2 - 1)) ∂(gaussianReal 0 1) = s21g2_s15b_Z t := by
  have := s21g2_s15b_rect ht (MeasurableSet.univ : MeasurableSet (Set.univ : Set ℝ))
  simpa [Set.indicator_univ] using this

theorem r26t3_finite_gaussian_tilt (n : ℕ) (lam : Fin n → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    (γ : ℝ) (hγ : 0 ≤ γ) :
    (∫ x : Fin n → ℝ, Real.exp (-(γ / 2) * ∑ j, lam j * (x j ^ 2 - 1))
      ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) =
      Real.exp ((1 / 2) * ∑ j, (γ * lam j - Real.log (1 + γ * lam j))) ∧
    r26t3_tilt (Measure.pi fun _ : Fin n => gaussianReal 0 1)
      (fun x => (γ / 2) * ∑ j, lam j * (x j ^ 2 - 1)) =
      Measure.pi (fun j => gaussianReal 0 ((1 + γ * lam j)⁻¹).toNNReal) := by
  classical
  set g : Measure ℝ := gaussianReal 0 1 with hg
  have ht : ∀ j, 0 ≤ γ * lam j := fun j => mul_nonneg hγ (hlam j)
  let e : Fin n → ℝ → ℝ := fun j x => Real.exp (-((γ * lam j) / 2) * (x ^ 2 - 1))
  have hexp : ∀ x : Fin n → ℝ, Real.exp (-((γ / 2) * ∑ j, lam j * (x j ^ 2 - 1))) = ∏ j, e j (x j) := by
    intro x
    show _ = ∏ j, Real.exp (-((γ * lam j) / 2) * (x j ^ 2 - 1))
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hZ : ∫ x : Fin n → ℝ, Real.exp (-((γ / 2) * ∑ j, lam j * (x j ^ 2 - 1))) ∂(Measure.pi fun _ : Fin n => g)
      = ∏ j, s21g2_s15b_Z (γ * lam j) := by
    simp_rw [hexp]
    rw [integral_fintype_prod_eq_prod (fun j => e j)]
    exact Finset.prod_congr rfl fun j _ => s21g2_s15b_Z_eq (ht j)
  have hZ' : ∏ j, s21g2_s15b_Z (γ * lam j) = Real.exp ((1 / 2) * ∑ j, (γ * lam j - Real.log (1 + γ * lam j))) := by
    unfold s21g2_s15b_Z
    rw [← Real.exp_sum, Finset.mul_sum]
  refine ⟨?_, ?_⟩
  · have : ∀ x : Fin n → ℝ, -(γ / 2) * ∑ j, lam j * (x j ^ 2 - 1) = -((γ / 2) * ∑ j, lam j * (x j ^ 2 - 1)) :=
      fun x => neg_mul _ _
    simp_rw [this]
    rw [hZ, hZ']
  · refine (Measure.pi_eq fun s hs => ?_).symm
    set S : Set (Fin n → ℝ) := Set.pi Set.univ s with hSdef
    have hS : MeasurableSet S := MeasurableSet.univ_pi hs
    have hem : ∀ j, Measurable (e j) := fun j => by
      show Measurable fun x : ℝ => Real.exp (-((γ * lam j) / 2) * (x ^ 2 - 1))
      fun_prop
    have hF : ∀ j, Integrable ((s j).indicator (e j)) g := fun j => by
      refine (integrable_const (Real.exp ((γ * lam j) / 2))).mono'
        (((hem j).indicator (hs j)).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
      by_cases hx : x ∈ s j
      · rw [Set.indicator_of_mem hx, Real.norm_of_nonneg (Real.exp_pos _).le]
        refine Real.exp_le_exp.2 ?_
        have := ht j
        nlinarith [sq_nonneg x]
      · simp [Set.indicator_of_notMem hx, (Real.exp_pos _).le]
    have hFprod : ∀ x : Fin n → ℝ, S.indicator
        (fun x => Real.exp (-((γ / 2) * ∑ j, lam j * (x j ^ 2 - 1)))) x =
        ∏ j, (s j).indicator (e j) (x j) := by
      intro x
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx, hexp]
        exact Finset.prod_congr rfl fun j _ =>
          (Set.indicator_of_mem (by simpa [S] using hx j) _).symm
      · rw [Set.indicator_of_notMem hx]
        obtain ⟨j, hj⟩ : ∃ j, x j ∉ s j := by simpa [S] using hx
        exact (Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem hj _)).symm
    have hint : Integrable (S.indicator
        (fun x : Fin n → ℝ => Real.exp (-((γ / 2) * ∑ j, lam j * (x j ^ 2 - 1)))))
        (Measure.pi fun _ : Fin n => g) := by
      rw [funext hFprod]
      exact Integrable.fintype_prod (f := fun j => (s j).indicator (e j)) hF
    have hFint : ∫ x, S.indicator
        (fun x : Fin n → ℝ => Real.exp (-((γ / 2) * ∑ j, lam j * (x j ^ 2 - 1)))) x
        ∂(Measure.pi fun _ : Fin n => g) =
        (∏ j, s21g2_s15b_Z (γ * lam j)) *
          ∏ j, (gaussianReal 0 ((1 + γ * lam j)⁻¹).toNNReal (s j)).toReal := by
      simp_rw [hFprod]
      rw [integral_fintype_prod_eq_prod (fun j => (s j).indicator (e j)), ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun j _ => s21g2_s15b_rect (ht j) (hs j)
    have hZpos : 0 < ∏ j, s21g2_s15b_Z (γ * lam j) :=
      Finset.prod_pos fun j _ => Real.exp_pos _
    have hlin : ∫⁻ ω in S, ENNReal.ofReal (Real.exp (-((γ / 2) * ∑ j, lam j * (ω j ^ 2 - 1))))
        ∂(Measure.pi fun _ : Fin n => g) = ENNReal.ofReal (∫ x, S.indicator
        (fun x : Fin n → ℝ => Real.exp (-((γ / 2) * ∑ j, lam j * (x j ^ 2 - 1)))) x
        ∂(Measure.pi fun _ : Fin n => g)) := by
      rw [← lintegral_indicator hS, ofReal_integral_eq_lintegral_ofReal hint
        (ae_of_all _ fun x => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) x)]
      refine lintegral_congr fun x => ?_
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, ENNReal.ofReal_zero]
    unfold r26t3_tilt
    simp only []
    rw [Measure.smul_apply, withDensity_apply _ hS, hlin, hFint, hZ]
    haveI : ∀ j, IsProbabilityMeasure (gaussianReal 0 ((1 + γ * lam j)⁻¹).toNNReal) := fun j => inferInstance
    rw [smul_eq_mul, ENNReal.ofReal_mul hZpos.le, ← mul_assoc,
      ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hZpos).ne' ENNReal.ofReal_ne_top, one_mul,
      ENNReal.ofReal_prod_of_nonneg fun j _ => ENNReal.toReal_nonneg]
    exact Finset.prod_congr rfl fun j _ => ENNReal.ofReal_toReal (measure_ne_top _ _)

end HRS.MS.R26T3
