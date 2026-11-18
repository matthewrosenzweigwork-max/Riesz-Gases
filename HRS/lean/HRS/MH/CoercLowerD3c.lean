import HRS.MH.CoercLowerDefs
import HRS.MH.CoercLowerD1
import HRS.MH.CoercLowerD2
import HRS.MH.CoercLowerD3a
import Mathlib

/-!
# CoercLower packet P26 (`fTlog_props`).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace HRS.MH.CoercLower


variable {d N : ℕ}

/-- Auxiliary: the kernel `rieszKernel d 0` is measurable. -/
private lemma cld3c_measurable_rieszKernel_zero (d : ℕ) :
    Measurable (HRS.Whole.rieszKernel d 0) := by
  have h : HRS.Whole.rieszKernel d 0 = fun x => -Real.log ‖x‖ := by
    funext x
    simp [HRS.Whole.rieszKernel]
  rw [h]
  fun_prop

/-- Auxiliary: `t ↦ e^{-tr}/t` is integrable on `(T, ∞)` for `r > 0`, `T ≥ 1`. -/
private lemma cld3c_integrableOn_exp_div {T r : ℝ} (hT : 1 ≤ T) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => Real.exp (-t * r) / t) (Set.Ioi T) := by
  have hg : IntegrableOn (fun t : ℝ => Real.exp (-t * r)) (Set.Ioi T) :=
    (exp_neg_integrableOn_Ioi T hr).congr_fun (fun t _ => by ring_nf) measurableSet_Ioi
  have hmeas : Measurable (fun t : ℝ => Real.exp (-t * r) / t) := by
    fun_prop
  refine Integrable.mono' hg hmeas.aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_))
  have ht1 : 1 ≤ t := by
    have := Set.mem_Ioi.mp ht
    linarith
  have hpos : 0 ≤ Real.exp (-t * r) := (Real.exp_pos _).le
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hpos (by linarith))]
  exact div_le_self hpos ht1

/-- Auxiliary: `φ_T ≥ 0`. -/
private lemma cld3c_phiLog_nonneg {T : ℝ} (hT : 0 < T) (x : Euc d) : 0 ≤ phiLog T x := by
  unfold phiLog
  refine mul_nonneg (by norm_num) (setIntegral_nonneg measurableSet_Ioi (fun t ht => ?_))
  have ht0 : 0 < t := lt_trans hT (Set.mem_Ioi.mp ht)
  exact div_nonneg (Real.exp_pos _).le ht0.le

/-- Auxiliary: off the origin, `fT = φ_T - E_T / 2` (Frullani split at `T`). -/
private lemma cld3c_fTlog_eq {T : ℝ} (hT : 1 ≤ T) {x : Euc d} (hx : x ≠ 0) :
    fTlog d T x = phiLog T x - Etail T / 2 := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hr : 0 < ‖x‖ ^ 2 := by positivity
  have hT0 : (0 : ℝ) < T := by linarith
  have hIoc : IntegrableOn (fun t : ℝ => (Real.exp (-t * ‖x‖ ^ 2) - Real.exp (-t)) / t)
      (Set.Ioc 0 T) := (frullani_core hT x).1
  have hGr : IntegrableOn (fun t : ℝ => Real.exp (-t * ‖x‖ ^ 2) / t) (Set.Ioi T) :=
    cld3c_integrableOn_exp_div hT hr
  have hG1 : IntegrableOn (fun t : ℝ => Real.exp (-t) / t) (Set.Ioi T) := by
    simpa only [mul_one] using cld3c_integrableOn_exp_div (r := 1) hT one_pos
  have hsplit : (fun t : ℝ => (Real.exp (-t * ‖x‖ ^ 2) - Real.exp (-t)) / t) =
      fun t : ℝ => Real.exp (-t * ‖x‖ ^ 2) / t - Real.exp (-t) / t :=
    funext fun t => sub_div _ _ _
  have hIoi : IntegrableOn (fun t : ℝ => (Real.exp (-t * ‖x‖ ^ 2) - Real.exp (-t)) / t)
      (Set.Ioi T) := by
    rw [hsplit]
    exact hGr.sub hG1
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) T) (Set.Ioi T) :=
    Set.disjoint_left.mpr (fun t h1 h2 => by
      have h2' := Set.mem_Ioi.mp h2
      have h1' := h1.2
      linarith)
  have hunion : ∫ t in Set.Ioi (0 : ℝ), (Real.exp (-t * ‖x‖ ^ 2) - Real.exp (-t)) / t =
      (∫ t in Set.Ioc (0 : ℝ) T, (Real.exp (-t * ‖x‖ ^ 2) - Real.exp (-t)) / t) +
        ∫ t in Set.Ioi T, (Real.exp (-t * ‖x‖ ^ 2) - Real.exp (-t)) / t := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hT0.le]
    exact setIntegral_union hdisj measurableSet_Ioi hIoc hIoi
  have hint : ∫ t in Set.Ioi T, (Real.exp (-t * ‖x‖ ^ 2) - Real.exp (-t)) / t =
      (∫ t in Set.Ioi T, Real.exp (-t * ‖x‖ ^ 2) / t) - ∫ t in Set.Ioi T, Real.exp (-t) / t := by
    rw [hsplit, integral_sub hGr hG1]
  have hfrul := frullani_rep d hx
  have hgT : gTlog T x = (1 / 2) *
      ∫ t in Set.Ioc (0 : ℝ) T, (Real.exp (-t * ‖x‖ ^ 2) - Real.exp (-t)) / t := rfl
  unfold fTlog phiLog Etail
  rw [hfrul, hgT, hunion, hint]
  ring

/-- [P26] The tail `fTlog`: measurable, `-E/2 ≤ fT ≤ φ` off `0`. -/
theorem fTlog_props (d : ℕ) {T : ℝ} (hT : 1 ≤ T) :
    Measurable (fTlog d T) ∧
      ∀ x : Euc d, x ≠ 0 → -(Etail T / 2) ≤ fTlog d T x ∧ fTlog d T x ≤ phiLog T x := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hmeas : Measurable (fTlog d T) := by
    unfold fTlog
    exact (cld3c_measurable_rieszKernel_zero d).sub (gTlog_props (d := d) hT).1
  refine ⟨hmeas, fun x hx => ?_⟩
  have key : fTlog d T x = phiLog T x - Etail T / 2 := cld3c_fTlog_eq hT hx
  have hφ : 0 ≤ phiLog T x := cld3c_phiLog_nonneg hT0 x
  have hE : 0 ≤ Etail T := (Etail_bounds hT).1
  constructor <;> linarith

end HRS.MH.CoercLower
