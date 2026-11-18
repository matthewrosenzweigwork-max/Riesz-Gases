import HRS.MH.CoercLowerDefs
import Mathlib

/-!
# CoercLower packets P21 (`integrableOn_frullani`) and P25 (`Etail_bounds`).
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace HRS.MH.CoercLower

variable {d N : ℕ}

/-- Auxiliary: for `x ≤ y ≤ 0`, `0 ≤ e^y - e^x ≤ y - x`. -/
private lemma cld1_exp_sub_exp_aux {x y : ℝ} (hxy : x ≤ y) (hy : y ≤ 0) :
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

/-- Auxiliary: `|e^x - e^y| ≤ |x - y|` for `x, y ≤ 0`. -/
private lemma cld1_abs_exp_sub_exp_le_nonpos {x y : ℝ} (hx : x ≤ 0) (hy : y ≤ 0) :
    |Real.exp x - Real.exp y| ≤ |x - y| := by
  rcases le_total x y with h | h
  · obtain ⟨h1, h2⟩ := cld1_exp_sub_exp_aux h hy
    have h3 := neg_abs_le (x - y)
    have h4 := abs_nonneg (x - y)
    rw [abs_le]
    constructor <;> linarith
  · obtain ⟨h1, h2⟩ := cld1_exp_sub_exp_aux h hx
    have h3 := neg_abs_le (y - x)
    have h4 := abs_nonneg (y - x)
    rw [abs_sub_comm (Real.exp x), abs_sub_comm x y, abs_le]
    constructor <;> linarith

/-- [P21] Integrability of the Frullani integrand on `(0,∞)`. -/
theorem integrableOn_frullani {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => (Real.exp (-t * a) - Real.exp (-t * b)) / t) (Set.Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
  have cld1_meas : Measurable (fun t : ℝ => (Real.exp (-t * a) - Real.exp (-t * b)) / t) :=
    Measurable.div (by fun_prop) measurable_id
  refine integrableOn_union.mpr ⟨?_, ?_⟩
  · -- near zero: the integrand is bounded by |a - b|
    refine Measure.integrableOn_of_bounded (M := |a - b|) measure_Ioc_lt_top.ne ?_ ?_
    · exact cld1_meas.aestronglyMeasurable
    · refine (ae_restrict_mem measurableSet_Ioc).mono fun t ht => ?_
      have ht0 : 0 < t := ht.1
      have hk := cld1_abs_exp_sub_exp_le_nonpos
        (x := -t * a) (y := -t * b)
        (by nlinarith [mul_pos ht0 ha]) (by nlinarith [mul_pos ht0 hb])
      have heq : |-t * a - -t * b| = t * |a - b| := by
        rw [show -t * a - -t * b = -(t * (a - b)) by ring, abs_neg, abs_mul, abs_of_pos ht0]
      rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
      nlinarith [hk, heq, abs_nonneg (a - b)]
  · -- at infinity: the integrand is dominated by `e^{-a t} + e^{-b t}`
    have hA : IntegrableOn (fun t : ℝ => Real.exp (-t * a)) (Ioi 1) := by
      refine (exp_neg_integrableOn_Ioi 1 ha).congr_fun (fun t _ => ?_) measurableSet_Ioi
      congr 1; ring
    have hB : IntegrableOn (fun t : ℝ => Real.exp (-t * b)) (Ioi 1) := by
      refine (exp_neg_integrableOn_Ioi 1 hb).congr_fun (fun t _ => ?_) measurableSet_Ioi
      congr 1; ring
    refine Integrable.mono' (hA.add hB) ?_ ?_
    · exact (Measurable.div (by fun_prop) measurable_id).aestronglyMeasurable
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
      have ht1 : (1:ℝ) ≤ t := le_of_lt ht
      have ht0 : 0 < t := by linarith
      have hA0 := Real.exp_pos (-t * a)
      have hB0 := Real.exp_pos (-t * b)
      rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0]
      have h1 : |Real.exp (-t * a) - Real.exp (-t * b)| / t ≤
          |Real.exp (-t * a) - Real.exp (-t * b)| := div_le_self (abs_nonneg _) ht1
      have h2 : |Real.exp (-t * a) - Real.exp (-t * b)| ≤ Real.exp (-t * a) + Real.exp (-t * b) := by
        rw [abs_le]; constructor <;> linarith
      simp only [Pi.add_apply]
      linarith

/-- [P25] The constant `E_T`. -/
theorem Etail_bounds {T : ℝ} (hT : 1 ≤ T) : 0 ≤ Etail T ∧ Etail T ≤ Real.exp (-T) := by
  have hT0 : (0 : ℝ) < T := by linarith
  constructor
  · unfold Etail
    refine setIntegral_nonneg measurableSet_Ioi (fun t ht => ?_)
    have : (0 : ℝ) < t := lt_trans hT0 ht
    exact div_nonneg (Real.exp_pos _).le this.le
  · unfold Etail
    rw [← integral_exp_neg_Ioi T]
    refine integral_mono_of_nonneg ?_ (integrableOn_exp_neg_Ioi T) ?_
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
      have : (0 : ℝ) < t := lt_trans hT0 ht
      exact div_nonneg (Real.exp_pos _).le this.le
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
      have ht1 : (1 : ℝ) ≤ t := le_trans hT ht.le
      exact div_le_self (Real.exp_pos _).le ht1

end HRS.MH.CoercLower
