import HRS.MH.CoercLowerDefs
import HRS.MH.CoercLowerB1
import HRS.MH.CoercLowerB2
import HRS.MH.CoercLowerB3a
import HRS.MH.CoercLowerB3b
import HRS.MH.CoercLowerA3
import HRS.MH.CoercLowerD1
import HRS.MH.CoercLowerD2
import HRS.MH.CoercLowerD3a
import HRS.MH.CoercLowerD3b
import HRS.MH.CoercLowerD3c
import HRS.MH.CoercLowerD4b
import Mathlib

/-!
# CoercLower packet P29 (`two_mul_energy_lower_log`).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace HRS.MH.CoercLower

variable {d N : ℕ}

/-- [P29] Assembly for `s = 0`. -/
theorem two_mul_energy_lower_log (hd : 1 ≤ d) {T Λ : ℝ} (hT : 1 ≤ T) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) (hΛ : ∀ x, ρ x ≤ Λ)
    (hlog : Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) (HRS.Whole.withDensityReal ρ)) (hN : 1 ≤ N)
    (X : HRS.Whole.EucConfig d N) (hX : Function.Injective X) :
    -((1 + Real.log T) / (2 * N) + Real.exp (-T) +
        2 * Λ * (Real.pi ^ ((d : ℝ) / 2) / d * T ^ (-((d : ℝ) / 2)))) ≤
      2 * HRS.Whole.rieszModulatedEnergy d 0 X (HRS.Whole.withDensityReal ρ) := by
  have hlog' := (integrable_log_moment_iff hρ).mp hlog
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hΛ0 : 0 ≤ Λ := (hρ.nonneg 0).trans (hΛ 0)
  obtain ⟨hmeas, hbd, h0, hge⟩ := gTlog_props (d := d) hT
  obtain ⟨hfm, hfb⟩ := fTlog_props d hT
  obtain ⟨hE0, hE1⟩ := Etail_bounds hT
  obtain ⟨hφ0, hφi, hφint⟩ := phiLog_integral hd (T := T) (by linarith)
  have hK := domK_log (c := 1 + Real.log T) (by linarith) hρ hlog'
  have hgi := integrable_of_domK hmeas hρ
    (K := fun z : Euc d => (1 + Real.log T) + Real.log (2 + ‖z‖)) (fun z => hbd z) hK
  obtain ⟨hfi, -, hfe, -⟩ := conv_bounds_of_bounds hd (a := Etail T / 2) (Λ := Λ) hfm
    (by linarith) (fun z hz => (hfb z hz).1) (fun z hz => (hfb z hz).2) hφ0 hφi hρ hΛ
  have hadd := Qform_add (gTlog T) (fTlog d T) X ρ hgi.1 hfi hgi.2 hfe
  have hg : (fun z : Euc d => gTlog T z + fTlog d T z) = HRS.Whole.rieszKernel d 0 := by
    funext z; simp [fTlog]
  rw [hg] at hadd
  have hlow := Qform_lower_of_bounds hd (a := Etail T / 2) (Λ := Λ) hfm (by linarith)
    (fun z hz => (hfb z hz).1) (fun z hz => (hfb z hz).2) hφ0 hφi hρ hΛ hN X hX
  have hnn := Qform_gTlog_nonneg hT hρ hlog' hN X
  have hmod := modulatedEnergy_eq_Qform (HRS.Whole.rieszKernel d 0) hρ hN X
  have hz := rieszKernel_zero d (s := 0) le_rfl
  have hf0 : fTlog d T (0 : Euc d) = -gTlog T (0 : Euc d) := by simp [fTlog, hz]
  have hdiv : -((1 + Real.log T) / (2 * N)) ≤ fTlog d T (0 : Euc d) / N := by
    rw [hf0, show (1 + Real.log T) / (2 * (N : ℝ)) = ((1 + Real.log T) / 2) / N by
      field_simp]
    rw [← neg_div]
    exact div_le_div_of_nonneg_right (by linarith) hNpos.le
  unfold HRS.Whole.rieszModulatedEnergy
  rw [hmod, hz, hφint] at *
  have : 2 * ((Qform (HRS.Whole.rieszKernel d 0) X ρ - 0 / N) / 2) =
      Qform (HRS.Whole.rieszKernel d 0) X ρ := by ring
  rw [this, hadd]
  linarith

end HRS.MH.CoercLower
