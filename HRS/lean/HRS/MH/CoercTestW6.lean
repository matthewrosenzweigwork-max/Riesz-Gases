import Mathlib
import HRS.Whole.AppendixALemmas
import HRS.MH.CoercLowerDefs
import HRS.MH.CoercLowerFinal
import HRS.MH.CoercTestSpecDefs
import HRS.MH.CoercLowerC1
import HRS.MH.CoercLowerC3b
import HRS.MH.CoercLowerD4a
import HRS.MH.CoercLowerD4c

/-!
# W6: upper bounds of `Qform gT` by the modulated energy

Proofs of `qform_gT_le_pos` and `qform_gT_le_log` of `HRS/MH/CoercTestSpec.lean` (statements copied verbatim).
Route: the proofs of `two_mul_energy_lower_pos` (C3b) and `two_mul_energy_lower_log` (D4c), with the inequality
for `Qform gT` obtained from `Qform gT = 2 F - Qform fT` and the lower bound `Qform fT ≥ -A`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform

namespace HRS.MH.CoercTest

open HRS.MH.CoercLower

variable {d N : ℕ}

/-- [W6a] `s > 0`: `Qform gT ≤ 2 F + A` where `-A` is the lower bound of `two_mul_energy_lower_pos`.
Route: copy the proof of `two_mul_energy_lower_pos` (C3b:27), whose `Qform g = Qform gT + Qform fT` and
`Qform fT ≥ -A` (`Qform_lower_of_bounds`) give the reverse inequality. -/
theorem qform_gT_le_pos (hd : 1 ≤ d) {s T Λ : ℝ} (hs : 0 < s) (hsd : s < d) (hT : 0 < T) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) (hΛ : ∀ x, ρ x ≤ Λ) (hN : 1 ≤ N) (X : HRS.Whole.EucConfig d N)
    (hX : Function.Injective X) :
    Qform (gTpos s T) X ρ ≤ 2 * HRS.Whole.rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) +
      (2 / (s * Real.Gamma (s / 2)) * T ^ (s / 2) / N +
        2 * Λ * (Real.pi ^ ((d : ℝ) / 2) / Real.Gamma (s / 2) * (2 / ((d : ℝ) - s)) * T ^ ((s - d) / 2))) := by
  obtain ⟨gm, gb, g0⟩ := gTpos_props (d := d) hs hT
  obtain ⟨fm, fp⟩ := fTpos_props d hs hT
  obtain ⟨fi, fint⟩ := fTpos_integral d hs hsd hT
  have hgsplit : HRS.Whole.rieszKernel d s =
      fun z => gTpos s T z + fTpos d s T z := by
    funext z; simp [fTpos]
  -- integrability for gT
  have hKg := domK_const (gTpos s T (0 : Euc d)) hρ
  obtain ⟨gi1, gi2⟩ := integrable_of_domK (h := gTpos s T) (K := fun _ => gTpos s T (0 : Euc d)) gm hρ
    (fun z => by rw [abs_of_nonneg (gb z).1]; exact (gb z).2) hKg
  -- bounds for fT
  have hflo : ∀ z : Euc d, z ≠ 0 → -(0 : ℝ) ≤ fTpos d s T z := fun z hz => by
    rw [neg_zero]; exact (fp z hz).2.1
  have hfup : ∀ z : Euc d, z ≠ 0 → fTpos d s T z ≤ |fTpos d s T z| := fun z _ => le_abs_self _
  have hφi : Integrable (fun z => |fTpos d s T z|) := fi.abs
  obtain ⟨fi1, -, fi2, -⟩ := conv_bounds_of_bounds hd (f := fTpos d s T) (φ := fun z => |fTpos d s T z|)
    (a := 0) (Λ := Λ) fm le_rfl hflo hfup (fun z => abs_nonneg _) hφi hρ hΛ
  have hlow := Qform_lower_of_bounds hd (f := fTpos d s T) (φ := fun z => |fTpos d s T z|)
    (a := 0) (Λ := Λ) fm le_rfl hflo hfup (fun z => abs_nonneg _) hφi hρ hΛ hN X hX
  have habs : ∫ z, |fTpos d s T z| = ∫ z, fTpos d s T z := by
    refine integral_congr_ae ?_
    filter_upwards [ae_ne_zero hd] with z hz
    exact abs_of_nonneg (fp z hz).2.1
  have hsum : Qform (fun z => gTpos s T z + fTpos d s T z) X ρ =
      Qform (gTpos s T) X ρ + Qform (fTpos d s T) X ρ :=
    Qform_add _ _ X ρ gi1 fi1 gi2 fi2
  have hmod : HRS.Whole.rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) =
      (Qform (HRS.Whole.rieszKernel d s) X ρ - HRS.Whole.rieszKernel d s 0 / N) / 2 :=
    modulatedEnergy_eq_Qform _ hρ hN X
  have hr0 : HRS.Whole.rieszKernel d s (0 : Euc d) = 0 := rieszKernel_zero d hs.le
  have hf0 : fTpos d s T (0 : Euc d) = -gTpos s T (0 : Euc d) := by
    simp [fTpos, hr0]
  rw [hmod, hr0, hgsplit, hsum]
  rw [habs, hf0, g0] at hlow
  rw [fint, neg_div, mul_zero, sub_zero] at hlow
  have hz0 : (0 : ℝ) / (N : ℝ) = 0 := zero_div _
  linarith

/-- [W6b] `s = 0`: `Qform gT ≤ 2 F + A` where `-A` is the lower bound of `two_mul_energy_lower_log`
(copy the proof of D4c:29). -/
theorem qform_gT_le_log (hd : 1 ≤ d) {T Λ : ℝ} (hT : 1 ≤ T) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) (hΛ : ∀ x, ρ x ≤ Λ)
    (hlog : Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) (HRS.Whole.withDensityReal ρ)) (hN : 1 ≤ N)
    (X : HRS.Whole.EucConfig d N) (hX : Function.Injective X) :
    Qform (gTlog T) X ρ ≤ 2 * HRS.Whole.rieszModulatedEnergy d 0 X (HRS.Whole.withDensityReal ρ) +
      ((1 + Real.log T) / (2 * N) + Real.exp (-T) +
        2 * Λ * (Real.pi ^ ((d : ℝ) / 2) / d * T ^ (-((d : ℝ) / 2)))) := by
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
  have hz := rieszKernel_zero d (s := 0) le_rfl
  have hf0 : fTlog d T (0 : Euc d) = -gTlog T (0 : Euc d) := by simp [fTlog, hz]
  have hdiv : -((1 + Real.log T) / (2 * N)) ≤ fTlog d T (0 : Euc d) / N := by
    rw [hf0, show (1 + Real.log T) / (2 * (N : ℝ)) = ((1 + Real.log T) / 2) / N by
      field_simp]
    rw [← neg_div]
    exact div_le_div_of_nonneg_right (by linarith) hNpos.le
  have hF : HRS.Whole.rieszModulatedEnergy d 0 X (HRS.Whole.withDensityReal ρ) =
      (Qform (HRS.Whole.rieszKernel d 0) X ρ - HRS.Whole.rieszKernel d 0 0 / N) / 2 :=
    modulatedEnergy_eq_Qform _ hρ hN X
  rw [hF, hz]
  rw [hφint] at hlow
  have hz0 : (0 : ℝ) / (N : ℝ) = 0 := zero_div _
  linarith

end HRS.MH.CoercTest
