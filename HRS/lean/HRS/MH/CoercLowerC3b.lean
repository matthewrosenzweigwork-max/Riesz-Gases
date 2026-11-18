import Mathlib
import HRS.Whole.Basic
import HRS.MH.CoercLowerDefs
import HRS.MH.CoercLowerB1
import HRS.MH.CoercLowerB2
import HRS.MH.CoercLowerB3a
import HRS.MH.CoercLowerC1
import HRS.MH.CoercLowerC2
import HRS.MH.CoercLowerC3a

/-!
# CoercLower C3b: packet P18 (`two_mul_energy_lower_pos`).

Statement copied verbatim from `HRS/MH/CoercLowerSpec.lean`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace HRS.MH.CoercLower

variable {d N : ℕ}

/-- [P18] Assembly for `s > 0`. -/
theorem two_mul_energy_lower_pos (hd : 1 ≤ d) {s T Λ : ℝ} (hs : 0 < s) (hsd : s < d) (hT : 0 < T)
    {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (hΛ : ∀ x, ρ x ≤ Λ) (hN : 1 ≤ N) (X : HRS.Whole.EucConfig d N)
    (hX : Function.Injective X) :
    -(2 / (s * Real.Gamma (s / 2)) * T ^ (s / 2) / N +
        2 * Λ * (Real.pi ^ ((d : ℝ) / 2) / Real.Gamma (s / 2) * (2 / ((d : ℝ) - s)) *
          T ^ ((s - d) / 2))) ≤
      2 * HRS.Whole.rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) := by
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
  have hgnn := Qform_gTpos_nonneg (N := N) hs hT hρ hN X
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
  have : (2 * ((Qform (gTpos s T) X ρ + Qform (fTpos d s T) X ρ - 0 / (N:ℝ)) / 2)) =
      Qform (gTpos s T) X ρ + Qform (fTpos d s T) X ρ := by ring
  rw [show (2:ℝ) * ((Qform (gTpos s T) X ρ + Qform (fTpos d s T) X ρ - 0 / (N:ℝ)) / 2) = _ from this]
  rw [fint, neg_div, mul_zero, sub_zero] at hlow
  linarith

end HRS.MH.CoercLower
