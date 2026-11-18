import Mathlib

/-!
# S11.3.K1 (breakdown packet K1): forward/adjoint pairing and the `L¹` bound for a substochastic density kernel
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace HRS.MS.S113BD

variable {α : Type*} [MeasurableSpace α]

/-- Integrability of `F(x,y) = k x y * f x` on the product. -/
theorem s113_kf_integrable (lam : Measure α) [SFinite lam]
    (k : α → α → ℝ) (hk : Measurable (Function.uncurry k))
    (hk0 : ∀ x y, 0 ≤ k x y)
    (hki : ∀ x, Integrable (k x) lam)
    (hkm : ∀ x, ∫ y, k x y ∂lam ≤ 1)
    (f : α → ℝ) (hf : Integrable f lam) :
    Integrable (fun p : α × α => k p.1 p.2 * f p.1) (lam.prod lam) := by
  have hmeas : AEStronglyMeasurable (fun p : α × α => k p.1 p.2 * f p.1) (lam.prod lam) :=
    hk.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_fst
  rw [integrable_prod_iff hmeas]
  refine ⟨Filter.Eventually.of_forall fun x => (hki x).mul_const (f x), ?_⟩
  have e : ∀ x, ∫ y, ‖k x y * f x‖ ∂lam = (∫ y, k x y ∂lam) * ‖f x‖ := fun x => by
    rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [norm_mul, Real.norm_of_nonneg (hk0 x y)]
  simp_rw [e]
  have hm2 : AEStronglyMeasurable (fun x => ∫ y, k x y ∂lam) lam :=
    (hk.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
  refine Integrable.mono' hf.norm (hm2.mul hf.norm.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  have h0 : 0 ≤ ∫ y, k x y ∂lam := integral_nonneg (hk0 x)
  rw [Real.norm_of_nonneg (mul_nonneg h0 (norm_nonneg _))]
  calc (∫ y, k x y ∂lam) * ‖f x‖ ≤ 1 * ‖f x‖ := mul_le_mul_of_nonneg_right (hkm x) (norm_nonneg _)
    _ = ‖f x‖ := one_mul _

theorem s113_transition_duality (lam : Measure α) [SFinite lam]
    (k : α → α → ℝ) (hk : Measurable (Function.uncurry k))
    (hk0 : ∀ x y, 0 ≤ k x y)
    (hki : ∀ x, Integrable (k x) lam)
    (hkm : ∀ x, ∫ y, k x y ∂lam ≤ 1)
    (f : α → ℝ) (hf : Integrable f lam) :
    Integrable (fun y => ∫ x, k x y * f x ∂lam) lam ∧
      (∫ y, |∫ x, k x y * f x ∂lam| ∂lam) ≤ ∫ x, |f x| ∂lam ∧
      ∀ (ψ : α → ℝ), Measurable ψ → (∀ y, |ψ y| ≤ 1) →
        (∫ y, ψ y * (∫ x, k x y * f x ∂lam) ∂lam) =
          ∫ x, f x * (∫ y, k x y * ψ y ∂lam) ∂lam := by
  have hF := s113_kf_integrable lam k hk hk0 hki hkm f hf
  have hFn : Integrable (fun p : α × α => ‖k p.1 p.2 * f p.1‖) (lam.prod lam) := hF.norm
  refine ⟨hF.integral_prod_right, ?_, ?_⟩
  · -- the `L¹` bound
    have h1 : ∫ y, |∫ x, k x y * f x ∂lam| ∂lam ≤ ∫ y, ∫ x, ‖k x y * f x‖ ∂lam ∂lam := by
      refine integral_mono hF.integral_prod_right.norm hFn.integral_prod_right (fun y => ?_)
      simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := lam) (fun x => k x y * f x)
    have h2 : ∫ y, ∫ x, ‖k x y * f x‖ ∂lam ∂lam = ∫ x, ∫ y, ‖k x y * f x‖ ∂lam ∂lam :=
      (integral_integral_swap (f := fun x y => ‖k x y * f x‖) hFn).symm
    have h3 : ∫ x, ∫ y, ‖k x y * f x‖ ∂lam ∂lam ≤ ∫ x, |f x| ∂lam := by
      refine integral_mono hFn.integral_prod_left hf.abs (fun x => ?_)
      have : ∫ y, ‖k x y * f x‖ ∂lam = (∫ y, k x y ∂lam) * |f x| := by
        rw [← integral_mul_const]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [norm_mul, Real.norm_of_nonneg (hk0 x y), Real.norm_eq_abs]
      rw [this]
      calc (∫ y, k x y ∂lam) * |f x| ≤ 1 * |f x| := mul_le_mul_of_nonneg_right (hkm x) (abs_nonneg _)
        _ = |f x| := one_mul _
    exact h1.trans (h2.le.trans h3)
  · intro ψ hψ hψ1
    have hG : Integrable (fun p : α × α => ψ p.2 * (k p.1 p.2 * f p.1)) (lam.prod lam) := by
      refine Integrable.mono' hFn ((hψ.comp measurable_snd).aestronglyMeasurable.mul hF.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun p => ?_)
      rw [norm_mul]
      have : ‖ψ p.2‖ ≤ 1 := by simpa [Real.norm_eq_abs] using hψ1 p.2
      calc ‖ψ p.2‖ * ‖k p.1 p.2 * f p.1‖ ≤ 1 * ‖k p.1 p.2 * f p.1‖ :=
            mul_le_mul_of_nonneg_right this (norm_nonneg _)
        _ = _ := one_mul _
    have e1 : ∀ y, ψ y * (∫ x, k x y * f x ∂lam) = ∫ x, ψ y * (k x y * f x) ∂lam := fun y => by
      rw [integral_const_mul]
    simp_rw [e1]
    rw [← integral_integral_swap (f := fun x y => ψ y * (k x y * f x)) hG]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ∫ y, ψ y * (k x y * f x) ∂lam = f x * ∫ y, k x y * ψ y ∂lam
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring

end HRS.MS.S113BD
