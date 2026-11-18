import HRS.MH.CoercLowerDefs
import Mathlib

/-!
# CoercLower packet P23 (`frullani_core`): the mixture weight of the truncated Frullani kernel.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace HRS.MH.CoercLower

variable {d N : ℕ}

/-- Auxiliary: for `x ≤ 0`-exponents, `|e^x - e^y| ≤ |x - y|`. -/
private lemma cld2_exp_sub_exp_aux {x y : ℝ} (hxy : x ≤ y) (hy : y ≤ 0) :
    0 ≤ Real.exp y - Real.exp x ∧ Real.exp y - Real.exp x ≤ y - x := by
  have hu : 0 ≤ y - x := by linarith
  have hyx : Real.exp y = Real.exp x * Real.exp (y - x) := by
    rw [← Real.exp_add]; ring_nf
  have hE : 0 < Real.exp (y - x) := Real.exp_pos _
  have hF : -(y - x) + 1 ≤ Real.exp (-(y - x)) := by
    linarith [Real.add_one_le_exp (-(y - x))]
  have hEF : Real.exp (y - x) * Real.exp (-(y - x)) = 1 := by
    rw [← Real.exp_add]; simp
  have hE1 : Real.exp (y - x) - 1 ≤ (y - x) * Real.exp (y - x) := by
    have := mul_le_mul_of_nonneg_left hF hE.le
    nlinarith
  have hx0 : 0 < Real.exp x := Real.exp_pos _
  have hyle : Real.exp y ≤ 1 := by
    rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr hy
  have hmono : Real.exp x ≤ Real.exp y := Real.exp_le_exp.mpr hxy
  constructor
  · linarith
  · have h4 : Real.exp y - Real.exp x = Real.exp x * (Real.exp (y - x) - 1) := by
      rw [hyx]; ring
    have h5 : Real.exp x * (Real.exp (y - x) - 1) ≤ Real.exp x * ((y - x) * Real.exp (y - x)) :=
      mul_le_mul_of_nonneg_left hE1 hx0.le
    have h6 : Real.exp x * ((y - x) * Real.exp (y - x)) = (y - x) * Real.exp y := by
      rw [hyx]; ring
    have h7 : (y - x) * Real.exp y ≤ (y - x) * 1 := mul_le_mul_of_nonneg_left hyle hu
    linarith

private lemma cld2_abs_exp_sub_exp_le_nonpos {x y : ℝ} (hx : x ≤ 0) (hy : y ≤ 0) :
    |Real.exp x - Real.exp y| ≤ |x - y| := by
  rcases le_total x y with h | h
  · obtain ⟨h1, h2⟩ := cld2_exp_sub_exp_aux h hy
    have h3 := neg_abs_le (x - y)
    have h4 := abs_nonneg (x - y)
    rw [abs_le]
    constructor <;> linarith
  · obtain ⟨h1, h2⟩ := cld2_exp_sub_exp_aux h hx
    have h3 := neg_abs_le (y - x)
    have h4 := abs_nonneg (y - x)
    rw [abs_sub_comm (Real.exp x), abs_sub_comm x y, abs_le]
    constructor <;> linarith

/-- Auxiliary pointwise bound: for `t > 0`, `|e^{-t r} - e^{-t}| / t ≤ min m t⁻¹` where `m = max r 1`. -/
private lemma cld2_frullani_pointwise {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r) :
    |Real.exp (-t * r) - Real.exp (-t)| / t ≤ min (max r 1) t⁻¹ := by
  have hA : Real.exp (-t * r) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg ht.le hr])
  have hB : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hA0 := Real.exp_pos (-t * r)
  have hB0 := Real.exp_pos (-t)
  have hle1 : |Real.exp (-t * r) - Real.exp (-t)| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  have hk := cld2_abs_exp_sub_exp_le_nonpos (x := -t * r) (y := -t)
    (by nlinarith [mul_nonneg ht.le hr]) (by linarith)
  have heq : |-t * r - -t| = t * |r - 1| := by
    rw [show -t * r - -t = -(t * (r - 1)) by ring, abs_neg, abs_mul, abs_of_pos ht]
  have hr1 : |r - 1| ≤ max r 1 := by
    rw [abs_le]
    constructor <;> linarith [le_max_left r 1, le_max_right r 1]
  apply le_min
  · rw [div_le_iff₀ ht]
    nlinarith [mul_le_mul_of_nonneg_left hr1 ht.le]
  · rw [div_eq_mul_inv]
    exact mul_le_of_le_one_left (inv_nonneg.mpr ht.le) hle1

/-- [P23] Core estimate (`T ≥ 1`): the mixture weight is integrable with logarithmic growth. -/
theorem frullani_core {T : ℝ} (hT : 1 ≤ T) (z : Euc d) :
    IntegrableOn (fun t : ℝ => (Real.exp (-t * ‖z‖ ^ 2) - Real.exp (-t)) / t) (Set.Ioc 0 T) ∧
      ∫ t in Set.Ioc (0 : ℝ) T, ‖(Real.exp (-t * ‖z‖ ^ 2) - Real.exp (-t)) / t‖ ≤
        1 + Real.log T + 2 * Real.log (2 + ‖z‖) := by
  have hr : 0 ≤ ‖z‖ ^ 2 := sq_nonneg _
  set m : ℝ := max (‖z‖ ^ 2) 1 with hm_def
  have hm1 : 1 ≤ m := le_max_right _ _
  have hm0 : 0 < m := by linarith
  have hTpos : 0 < T := by linarith
  have hmT : m⁻¹ ≤ T := le_trans (inv_le_one_of_one_le₀ hm1) hT
  have hs0 : 0 < m⁻¹ := inv_pos.mpr hm0
  set G : ℝ → ℝ := fun t => min m t⁻¹ with hG_def
  have hf_meas : Measurable (fun t : ℝ => (Real.exp (-t * ‖z‖ ^ 2) - Real.exp (-t)) / t) := by
    fun_prop
  have hG_meas : Measurable G := by
    fun_prop
  have hGint : IntegrableOn G (Ioc 0 T) := by
    refine Measure.integrableOn_of_bounded (M := m) measure_Ioc_lt_top.ne hG_meas.aestronglyMeasurable ?_
    refine (ae_restrict_mem measurableSet_Ioc).mono fun t ht => ?_
    have h0 : 0 ≤ G t := le_min hm0.le (inv_nonneg.mpr ht.1.le)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact min_le_left _ _
  have hpt : ∀ t ∈ Ioc (0 : ℝ) T,
      ‖(Real.exp (-t * ‖z‖ ^ 2) - Real.exp (-t)) / t‖ ≤ G t := by
    intro t ht
    rw [Real.norm_eq_abs, abs_div, abs_of_pos ht.1]
    exact cld2_frullani_pointwise ht.1 hr
  have hfint : IntegrableOn (fun t : ℝ => (Real.exp (-t * ‖z‖ ^ 2) - Real.exp (-t)) / t) (Ioc 0 T) :=
    Integrable.mono' hGint hf_meas.aestronglyMeasurable
      ((ae_restrict_mem measurableSet_Ioc).mono fun t ht => hpt t ht)
  refine ⟨hfint, ?_⟩
  have hnorm : ∫ t in Ioc (0 : ℝ) T, ‖(Real.exp (-t * ‖z‖ ^ 2) - Real.exp (-t)) / t‖ ≤
      ∫ t in Ioc (0 : ℝ) T, G t :=
    integral_mono_of_nonneg (ae_of_all _ fun t => norm_nonneg _) hGint
      ((ae_restrict_mem measurableSet_Ioc).mono fun t ht => hpt t ht)
  -- split the integral of `G` at `m⁻¹`
  have hsplit : ∫ t in Ioc (0 : ℝ) T, G t = (∫ t in Ioc (0 : ℝ) m⁻¹, G t) + ∫ t in Ioc m⁻¹ T, G t := by
    rw [← setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (hGint.mono_set (Ioc_subset_Ioc_right hmT)) (hGint.mono_set (Ioc_subset_Ioc_left hs0.le)),
      Set.Ioc_union_Ioc_eq_Ioc hs0.le hmT]
  have h1 : ∫ t in Ioc (0 : ℝ) m⁻¹, G t = ∫ t in Ioc (0 : ℝ) m⁻¹, m := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    show min m t⁻¹ = m
    apply min_eq_left
    exact (le_inv_comm₀ hm0 ht.1).mpr ht.2
  have h2 : ∫ t in Ioc m⁻¹ T, G t = ∫ t in Ioc m⁻¹ T, t⁻¹ := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    have ht0 : 0 < t := lt_of_lt_of_le hs0 ht.1.le
    show min m t⁻¹ = t⁻¹
    apply min_eq_right
    exact (inv_le_comm₀ ht0 hm0).mpr ht.1.le
  have h3 : ∫ t in Ioc m⁻¹ T, t⁻¹ = Real.log T + Real.log m := by
    rw [← intervalIntegral.integral_of_le hmT, integral_inv_of_pos hs0 hTpos, div_inv_eq_mul,
      Real.log_mul hTpos.ne' hm0.ne']
  have h4 : ∫ t in Ioc (0 : ℝ) m⁻¹, m = 1 := by
    rw [setIntegral_const, Real.volume_real_Ioc_of_le hs0.le, smul_eq_mul]
    field_simp
    simp
  have hlogm : Real.log m ≤ 2 * Real.log (2 + ‖z‖) := by
    have hmle : m ≤ (2 + ‖z‖) ^ 2 := max_le (by nlinarith [norm_nonneg z]) (by nlinarith [norm_nonneg z])
    have h2pos : 0 < 2 + ‖z‖ := by positivity
    have := Real.log_le_log hm0 hmle
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hG_total : ∫ t in Ioc (0 : ℝ) T, G t = 1 + Real.log T + Real.log m := by
    rw [hsplit, h1, h4, h2, h3]
    ring
  linarith [hnorm, hG_total, hlogm]

end HRS.MH.CoercLower
