import Mathlib

/-!
# S8M: an elementary Young-type bound `L² → L⁴` for convolution with a kernel in `L^{3/2} ∩ L¹` (S8.7, R4)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  For `ℝ≥0∞`-valued measurable `k, G` on a finite-dimensional real
inner product space `V` with Lebesgue measure and `(k * G)(x) = ∫⁻ k(x - y) G(y) dy`:
`∫⁻ (k * G)⁴ ≤ (∫⁻ k^{3/2})² (∫⁻ k) (∫⁻ G²)²` (`s8p_young4`).  Proof: two Cauchy-Schwarz inequalities and Tonelli
(no Mathlib Young inequality is used): `(k*G)² ≤ (∫k^{3/2}) (k^{1/2} * G²)` and
`∫ (k^{1/2} * P)² ≤ (∫ P)² ∫ k`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HRS.MS.Spec

theorem s8p_cs_lint {α : Type*} [MeasurableSpace α] (μ : Measure α) {f g : α → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, f x * g x ∂μ) ^ 2 ≤ (∫⁻ x, f x ^ 2 ∂μ) * ∫⁻ x, g x ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf.aemeasurable
    hg.aemeasurable
  simp only [ENNReal.rpow_two, Pi.mul_apply] at h
  have h2 := pow_le_pow_left' h 2
  refine h2.trans (le_of_eq ?_)
  rw [mul_pow]
  congr 1 <;>
  · rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- Convolution of `ℝ≥0∞`-valued functions. -/
def s8p_cv (k G : V → ℝ≥0∞) (x : V) : ℝ≥0∞ := ∫⁻ y, k (x - y) * G y

theorem s8p_rpow_half_sq (a : ℝ≥0∞) : (a ^ ((1 : ℝ) / 2)) ^ 2 = a := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

theorem s8p_cv_cs {k G : V → ℝ≥0∞} (hk : Measurable k) (hG : Measurable G) (x : V) :
    (s8p_cv k G x) ^ 2 ≤ (∫⁻ z, k z ^ ((3 : ℝ) / 2)) *
      s8p_cv (fun z => k z ^ ((1 : ℝ) / 2)) (fun y => G y ^ 2) x := by
  have hkx : Measurable fun y => k (x - y) := hk.comp (measurable_const.sub measurable_id)
  have e1 : s8p_cv k G x = ∫⁻ y, k (x - y) ^ ((3 : ℝ) / 4) * (k (x - y) ^ ((1 : ℝ) / 4) * G y) := by
    unfold s8p_cv
    refine lintegral_congr fun y => ?_
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  rw [e1]
  have h := s8p_cs_lint volume (f := fun y => k (x - y) ^ ((3 : ℝ) / 4))
    (g := fun y => k (x - y) ^ ((1 : ℝ) / 4) * G y) (hkx.pow_const _) ((hkx.pow_const _).mul hG)
  refine h.trans (le_of_eq ?_)
  congr 1
  · have e2 : ∫⁻ y, (k (x - y) ^ ((3 : ℝ) / 4)) ^ 2 = ∫⁻ y, k (x - y) ^ ((3 : ℝ) / 2) := by
      refine lintegral_congr fun y => ?_
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
    rw [e2]
    exact lintegral_sub_left_eq_self (fun z => k z ^ ((3 : ℝ) / 2)) x
  · unfold s8p_cv
    refine lintegral_congr fun y => ?_
    rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

theorem s8p_cv_sq {h P : V → ℝ≥0∞} (hh : Measurable h) (hP : Measurable P) :
    ∫⁻ x, (s8p_cv h P x) ^ 2 ≤ (∫⁻ y, P y) ^ 2 * ∫⁻ z, h z ^ 2 := by
  have step : ∀ x, (s8p_cv h P x) ^ 2 ≤ (∫⁻ y, h (x - y) ^ 2 * P y) * ∫⁻ y, P y := by
    intro x
    have hhx : Measurable fun y => h (x - y) := hh.comp (measurable_const.sub measurable_id)
    have e1 : s8p_cv h P x = ∫⁻ y, (h (x - y) * P y ^ ((1 : ℝ) / 2)) * P y ^ ((1 : ℝ) / 2) := by
      unfold s8p_cv
      refine lintegral_congr fun y => ?_
      rw [mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num
    rw [e1]
    have := s8p_cs_lint volume (f := fun y => h (x - y) * P y ^ ((1 : ℝ) / 2))
      (g := fun y => P y ^ ((1 : ℝ) / 2)) (hhx.mul (hP.pow_const _)) (hP.pow_const _)
    refine this.trans (le_of_eq ?_)
    congr 1
    · refine lintegral_congr fun y => ?_
      rw [mul_pow, s8p_rpow_half_sq]
    · exact lintegral_congr fun y => s8p_rpow_half_sq _
  have hm : Measurable (fun p : V × V => h (p.1 - p.2) ^ 2 * P p.2) :=
    ((hh.comp (measurable_fst.sub measurable_snd)).pow_const 2).mul (hP.comp measurable_snd)
  calc ∫⁻ x, (s8p_cv h P x) ^ 2
      ≤ ∫⁻ x, (∫⁻ y, h (x - y) ^ 2 * P y) * ∫⁻ y, P y := lintegral_mono step
    _ = (∫⁻ x, ∫⁻ y, h (x - y) ^ 2 * P y) * ∫⁻ y, P y := by
        rw [lintegral_mul_const _ hm.lintegral_prod_right']
    _ = (∫⁻ y, ∫⁻ x, h (x - y) ^ 2 * P y) * ∫⁻ y, P y := by
        rw [lintegral_lintegral_swap hm.aemeasurable]
    _ = (∫⁻ y, (∫⁻ z, h z ^ 2) * P y) * ∫⁻ y, P y := by
        congr 1
        refine lintegral_congr fun y => ?_
        have hmy : Measurable fun x : V => h (x - y) ^ 2 :=
          (hh.comp (measurable_id.sub_const y)).pow_const 2
        rw [lintegral_mul_const _ hmy]
        congr 1
        exact lintegral_sub_right_eq_self (fun z => h z ^ 2) y
    _ = _ := by
        rw [lintegral_const_mul _ hP]; ring

theorem s8p_young4 {k G : V → ℝ≥0∞} (hk : Measurable k) (hG : Measurable G) :
    ∫⁻ x, (s8p_cv k G x) ^ 4 ≤
      (∫⁻ z, k z ^ ((3 : ℝ) / 2)) ^ 2 * (∫⁻ z, k z) * (∫⁻ y, G y ^ 2) ^ 2 := by
  set A := ∫⁻ z, k z ^ ((3 : ℝ) / 2) with hA
  have hh : Measurable fun z => k z ^ ((1 : ℝ) / 2) := hk.pow_const _
  have hP : Measurable fun y => G y ^ 2 := hG.pow_const _
  have h1 : ∀ x, (s8p_cv k G x) ^ 4 ≤ A ^ 2 * (s8p_cv (fun z => k z ^ ((1 : ℝ) / 2)) (fun y => G y ^ 2) x) ^ 2 := by
    intro x
    have := s8p_cv_cs hk hG x
    calc (s8p_cv k G x) ^ 4 = ((s8p_cv k G x) ^ 2) ^ 2 := by ring
      _ ≤ (A * s8p_cv (fun z => k z ^ ((1 : ℝ) / 2)) (fun y => G y ^ 2) x) ^ 2 := pow_le_pow_left' this 2
      _ = _ := by ring
  calc ∫⁻ x, (s8p_cv k G x) ^ 4
      ≤ ∫⁻ x, A ^ 2 * (s8p_cv (fun z => k z ^ ((1 : ℝ) / 2)) (fun y => G y ^ 2) x) ^ 2 := lintegral_mono h1
    _ = A ^ 2 * ∫⁻ x, (s8p_cv (fun z => k z ^ ((1 : ℝ) / 2)) (fun y => G y ^ 2) x) ^ 2 := by
        refine lintegral_const_mul _ ?_
        have hm : Measurable (fun p : V × V => k (p.1 - p.2) ^ ((1 : ℝ) / 2) * G p.2 ^ 2) :=
          ((hh.comp (measurable_fst.sub measurable_snd))).mul (hP.comp measurable_snd)
        exact hm.lintegral_prod_right'.pow_const 2
    _ ≤ A ^ 2 * ((∫⁻ y, G y ^ 2) ^ 2 * ∫⁻ z, (k z ^ ((1 : ℝ) / 2)) ^ 2) := by
        gcongr
        exact s8p_cv_sq hh hP
    _ = _ := by
        simp_rw [s8p_rpow_half_sq]
        ring

end HRS.MS.Spec
