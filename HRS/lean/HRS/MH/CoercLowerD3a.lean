import HRS.MH.CoercLowerDefs
import HRS.MH.CoercLowerD1
import HRS.MH.CoercLowerD2
import Mathlib

/-!
# CoercLower packets P22 (`frullani_rep`) and P24 (`gTlog_props`).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace HRS.MH.CoercLower


variable {d N : ℕ}

/-- [P22] Frullani representation of `-log‖x‖`. -/
theorem frullani_rep (d : ℕ) {x : Euc d} (hx : x ≠ 0) :
    HRS.Whole.rieszKernel d 0 x =
      (1 / 2) * ∫ t in Set.Ioi (0 : ℝ), (Real.exp (-t * ‖x‖ ^ 2) - Real.exp (-t)) / t := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have ha : 0 < ‖x‖ ^ 2 := by positivity
  have hb : (0 : ℝ) < 1 := one_pos
  have hcont : Continuous (fun y : ℝ => Real.exp (-y)) := by fun_prop
  have hloc : LocallyIntegrableOn (fun y : ℝ => Real.exp (-y)) (Set.Ioi 0) :=
    hcont.locallyIntegrable.locallyIntegrableOn _
  have hL : Filter.Tendsto (fun y : ℝ => Real.exp (-y)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have h : Filter.Tendsto (fun y : ℝ => Real.exp (-y)) (nhds 0) (nhds 1) := by
      simpa using hcont.tendsto 0
    exact h.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hR : Filter.Tendsto (fun y : ℝ => Real.exp (-y)) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have hexp : ∀ t : ℝ, Real.exp (-t * ‖x‖ ^ 2) = Real.exp (-(‖x‖ ^ 2 * t)) :=
    fun t => congrArg Real.exp (by ring)
  have hpt : ∀ t : ℝ, (Real.exp (-t * ‖x‖ ^ 2) - Real.exp (-t)) / t =
      t⁻¹ • (Real.exp (-(‖x‖ ^ 2 * t)) - Real.exp (-(1 * t))) := by
    intro t
    rw [smul_eq_mul, hexp t, one_mul, div_eq_inv_mul]
  have hpt' : ∀ t : ℝ, (Real.exp (-t * ‖x‖ ^ 2) - Real.exp (-t * 1)) / t =
      t⁻¹ • (Real.exp (-(‖x‖ ^ 2 * t)) - Real.exp (-(1 * t))) := by
    intro t
    rw [mul_one]
    exact hpt t
  have hint0 := integrableOn_frullani ha hb
  have hint : IntegrableOn (fun t : ℝ => t⁻¹ • (Real.exp (-(‖x‖ ^ 2 * t)) - Real.exp (-(1 * t))))
      (Set.Ioi 0) :=
    hint0.congr_fun (fun t _ => hpt' t) measurableSet_Ioi
  have key : ∫ t in Set.Ioi (0 : ℝ), t⁻¹ • (Real.exp (-(‖x‖ ^ 2 * t)) - Real.exp (-(1 * t))) =
      Real.log (1 / ‖x‖ ^ 2) • ((1 : ℝ) - 0) :=
    Frullani.integral_Ioi_eq (f := fun y : ℝ => Real.exp (-y)) (a := ‖x‖ ^ 2) (b := 1)
      (L := 1) (R := 0) hloc ha hb hL hR hint
  have hcongr : (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-t * ‖x‖ ^ 2) - Real.exp (-t)) / t) =
      ∫ t in Set.Ioi (0 : ℝ), t⁻¹ • (Real.exp (-(‖x‖ ^ 2 * t)) - Real.exp (-(1 * t))) :=
    setIntegral_congr_fun measurableSet_Ioi (fun t _ => hpt t)
  have hlog : Real.log (1 / ‖x‖ ^ 2) = -(2 * Real.log ‖x‖) := by
    rw [one_div, Real.log_inv, Real.log_pow]
    push_cast
    ring
  rw [hcongr, key, HRS.Whole.rieszKernel, if_pos rfl, smul_eq_mul, sub_zero, mul_one, hlog]
  ring

/-- [P24] The truncation `gTlog` is NOT bounded; it has logarithmic growth. -/
theorem gTlog_props {T : ℝ} (hT : 1 ≤ T) :
    Measurable (gTlog T : Euc d → ℝ) ∧
      (∀ z : Euc d, |gTlog T z| ≤ 1 + Real.log T + Real.log (2 + ‖z‖)) ∧
      0 ≤ gTlog T (0 : Euc d) ∧ gTlog T (0 : Euc d) ≤ (1 + Real.log T) / 2 := by
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hmeas : Measurable (gTlog T : Euc d → ℝ) := by
    unfold gTlog
    apply Measurable.const_mul
    have hF : Measurable (fun p : Euc d × ℝ =>
        (Real.exp (-p.2 * ‖p.1‖ ^ 2) - Real.exp (-p.2)) / p.2) := by
      fun_prop
    exact (hF.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Ioc 0 T))).measurable
  have hbound : ∀ z : Euc d, |gTlog T z| ≤ 1 + Real.log T + Real.log (2 + ‖z‖) := by
    intro z
    have hL : 0 ≤ Real.log (2 + ‖z‖) := Real.log_nonneg (by linarith [norm_nonneg z])
    have h1 := (frullani_core hT z).2
    have h2 : |∫ t in Set.Ioc (0 : ℝ) T, (Real.exp (-t * ‖z‖ ^ 2) - Real.exp (-t)) / t| ≤
        ∫ t in Set.Ioc (0 : ℝ) T, ‖(Real.exp (-t * ‖z‖ ^ 2) - Real.exp (-t)) / t‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_integral_le_integral_norm _
    unfold gTlog
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  have hzero : ∀ t : ℝ, (Real.exp (-t * ‖(0 : Euc d)‖ ^ 2) - Real.exp (-t)) / t =
      (1 - Real.exp (-t)) / t := by
    intro t
    simp
  have hI0_nonneg : 0 ≤ ∫ t in Set.Ioc (0 : ℝ) T, (1 - Real.exp (-t)) / t := by
    refine setIntegral_nonneg measurableSet_Ioc (fun t ht => ?_)
    exact div_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith [ht.1]))) ht.1.le
  have hI0_upper : ∫ t in Set.Ioc (0 : ℝ) T, (1 - Real.exp (-t)) / t ≤ 1 + Real.log T := by
    have hint : IntegrableOn (fun t : ℝ => (1 - Real.exp (-t)) / t) (Set.Ioc 0 T) :=
      (frullani_core hT (0 : Euc d)).1.congr_fun (fun t _ => hzero t) measurableSet_Ioc
    have hsplit : ∫ t in Set.Ioc (0 : ℝ) T, (1 - Real.exp (-t)) / t =
        (∫ t in Set.Ioc (0 : ℝ) 1, (1 - Real.exp (-t)) / t) +
          ∫ t in Set.Ioc (1 : ℝ) T, (1 - Real.exp (-t)) / t := by
      rw [← setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
        (hint.mono_set (Set.Ioc_subset_Ioc_right hT))
        (hint.mono_set (Set.Ioc_subset_Ioc_left zero_le_one)),
        Set.Ioc_union_Ioc_eq_Ioc zero_le_one hT]
    have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc (0 : ℝ) 1) :=
      integrableOn_const measure_Ioc_lt_top.ne
    have hle1 : ∀ t ∈ Set.Ioc (0 : ℝ) 1, (1 - Real.exp (-t)) / t ≤ 1 := by
      intro t ht
      rw [div_le_iff₀ ht.1]
      linarith [Real.one_sub_le_exp_neg t]
    have h1 : ∫ t in Set.Ioc (0 : ℝ) 1, (1 - Real.exp (-t)) / t ≤ ∫ t in Set.Ioc (0 : ℝ) 1, (1 : ℝ) :=
      setIntegral_mono_on (hint.mono_set (Set.Ioc_subset_Ioc_right hT)) hconst measurableSet_Ioc
        (fun t ht => hle1 t ht)
    have hinv : IntegrableOn (fun t : ℝ => t⁻¹) (Set.Ioc (1 : ℝ) T) := by
      have hc : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc 1 T) := by
        refine ContinuousOn.inv₀ continuousOn_id (fun t ht => ?_)
        exact (show (0 : ℝ) < t by linarith [ht.1]).ne'
      exact hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    have h2 : ∫ t in Set.Ioc (1 : ℝ) T, (1 - Real.exp (-t)) / t ≤ ∫ t : ℝ in Set.Ioc (1 : ℝ) T, t⁻¹ := by
      refine setIntegral_mono_on (hint.mono_set (Set.Ioc_subset_Ioc_left zero_le_one)) hinv
        measurableSet_Ioc (fun t ht => ?_)
      have ht0 : 0 < t := by linarith [ht.1]
      exact (div_le_div_of_nonneg_right (by linarith [Real.exp_pos (-t)]) ht0.le).trans
        (le_of_eq (one_div t))
    have h3 : ∫ t : ℝ in Set.Ioc (1 : ℝ) T, t⁻¹ = Real.log T := by
      rw [← intervalIntegral.integral_of_le hT, integral_inv_of_pos one_pos (by linarith), div_one]
    have h4 : ∫ t in Set.Ioc (0 : ℝ) 1, (1 : ℝ) = 1 := by
      simp
    linarith
  have hgT0 : gTlog T (0 : Euc d) = (1 / 2) * ∫ t in Set.Ioc (0 : ℝ) T, (1 - Real.exp (-t)) / t := by
    unfold gTlog
    congr 1
    exact setIntegral_congr_fun measurableSet_Ioc (fun t _ => hzero t)
  refine ⟨hmeas, hbound, ?_, ?_⟩
  · rw [hgT0]
    exact mul_nonneg (by norm_num) hI0_nonneg
  · rw [hgT0]
    linarith [hI0_upper]

end HRS.MH.CoercLower
