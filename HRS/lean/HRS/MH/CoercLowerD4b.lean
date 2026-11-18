import HRS.MH.CoercLowerDefs
import HRS.MH.CoercLowerB2
import HRS.MH.CoercLowerB3b
import HRS.MH.CoercLowerA3
import HRS.MH.CoercLowerD2
import HRS.MH.CoercLowerD3a
import Mathlib

/-!
# CoercLower packet P28 (`Qform_gTlog_nonneg`).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace HRS.MH.CoercLower

variable {d N : ℕ}

/-- [P28] `Q^{gT} ≥ 0` for `s = 0` (needs the log moment for the Fubini domination). -/
theorem Qform_gTlog_nonneg {T : ℝ} (hT : 1 ≤ T) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    (hlog : Integrable (fun y : Euc d => Real.log (2 + ‖y‖) * ρ y)) (hN : 1 ≤ N)
    (X : HRS.Whole.EucConfig d N) : 0 ≤ Qform (gTlog T) X ρ := by
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  set H : ℝ → Euc d → ℝ := fun t z => (1 / 2) * ((Real.exp (-t * ‖z‖ ^ 2) - Real.exp (-t)) / t)
    with hH_def
  set ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) T) with hν
  have hgT : (gTlog T : Euc d → ℝ) = fun z => ∫ t, H t z ∂ν := by
    funext z
    simp only [gTlog, hH_def, hν]
    rw [integral_const_mul]
  have hmeas : Measurable (fun p : ℝ × Euc d => H p.1 p.2) := by
    simp only [hH_def]
    fun_prop
  have hint : ∀ z, Integrable (fun t => H t z) ν := fun z =>
    ((frullani_core (d := d) hT z).1).const_mul (1 / 2)
  have hdom : ∀ z, ∫ t, ‖H t z‖ ∂ν ≤ (1 + Real.log T) + Real.log (2 + ‖z‖) := by
    intro z
    have h1 := (frullani_core (d := d) hT z).2
    have hn : ∀ t, ‖H t z‖ = (1 / 2) * ‖(Real.exp (-t * ‖z‖ ^ 2) - Real.exp (-t)) / t‖ := by
      intro t
      simp only [hH_def, norm_mul]
      norm_num
    simp only [hn, hν]
    rw [integral_const_mul]
    have : 0 ≤ Real.log (2 + ‖z‖) := Real.log_nonneg (by linarith [norm_nonneg z])
    linarith
  have hK := domK_log (d := d) (c := 1 + Real.log T) (by linarith) hρ hlog
  rw [hgT, Qform_mix (ν := ν) H _ ρ hmeas hint hdom hρ hK X]
  apply integral_nonneg_of_ae
  rw [Filter.EventuallyLE, hν, ae_restrict_iff' measurableSet_Ioc]
  refine Filter.Eventually.of_forall fun t ht => ?_
  have htpos : 0 < t := ht.1
  have hHt : H t = fun z => (1 / (2 * t)) * (gaussK t z - Real.exp (-t)) := by
    funext z
    simp only [hH_def, gaussK]
    field_simp
  have hb : ∀ z : Euc d, |gaussK t z| ≤ 1 := by
    intro z
    have : 0 ≤ gaussK t z := (Real.exp_pos _).le
    rw [abs_of_nonneg this]
    unfold gaussK
    apply Real.exp_le_one_iff.mpr
    nlinarith [sq_nonneg ‖z‖]
  have hdomK : DomK (fun _ : Euc d => (1 : ℝ)) ρ := domK_const 1 hρ
  have hI := integrable_of_domK (h := gaussK t) (K := fun _ => (1 : ℝ)) (ρ := ρ)
    (by unfold gaussK; fun_prop) hρ hb hdomK
  show 0 ≤ Qform (H t) X ρ
  rw [hHt, Qform_smul, Qform_sub_const (gaussK t) (Real.exp (-t)) hρ hN X hI.1 hI.2]
  exact mul_nonneg (by positivity) (Qform_gauss_nonneg htpos hρ hN X)

end HRS.MH.CoercLower
