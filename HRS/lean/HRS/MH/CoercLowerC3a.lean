import Mathlib
import HRS.Whole.Basic
import HRS.MH.CoercLowerDefs
import HRS.MH.CoercLowerA1
import HRS.MH.CoercLowerA2
import HRS.MH.CoercLowerA3
import HRS.MH.CoercLowerB1
import HRS.MH.CoercLowerB2
import HRS.MH.CoercLowerB3b
import HRS.MH.CoercLowerC1

/-!
# CoercLower C3a: packet P17 (`Qform_gTpos_nonneg`).

Statement copied verbatim from `HRS/MH/CoercLowerSpec.lean`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace HRS.MH.CoercLower

variable {d N : ℕ}

/-- Integrability of `t ^ (s/2-1) * exp(-t r)` on `Ioc 0 T` for `r ≥ 0`, `T > 0`. -/
private lemma clc3a_integrableOn_kernel_Ioc {s T r : ℝ} (hs : 0 < s) (hT : 0 < T) (hr : 0 ≤ r) :
    IntegrableOn (fun t : ℝ => t ^ (s / 2 - 1) * Real.exp (-t * r)) (Set.Ioc 0 T) := by
  have h1 : IntegrableOn (fun t : ℝ => t ^ (s / 2 - 1)) (Set.Ioc 0 T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  refine h1.mono' ?_ ?_
  · exact (by fun_prop : Measurable (fun t : ℝ => t ^ (s / 2 - 1) * Real.exp (-t * r))).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun t ht => ?_)
    have ht0 : 0 < t := ht.1
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _) (Real.exp_pos _).le)]
    exact mul_le_of_le_one_right (Real.rpow_nonneg ht0.le _)
      (Real.exp_le_one_iff.mpr (by nlinarith))

/-- [P17] `Q^{gT} ≥ 0`. -/
theorem Qform_gTpos_nonneg {s T : ℝ} (hs : 0 < s) (hT : 0 < T) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) (hN : 1 ≤ N) (X : HRS.Whole.EucConfig d N) : 0 ≤ Qform (gTpos s T) X ρ := by
  have hc : 0 < 1 / Real.Gamma (s / 2) := by
    have := Real.Gamma_pos_of_pos (half_pos hs)
    positivity
  set c : ℝ := 1 / Real.Gamma (s / 2) with hcdef
  let H : ℝ → Euc d → ℝ := fun t z => (c * t ^ (s / 2 - 1)) * gaussK t z
  let ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) T)
  have hgT : ∀ z : Euc d, gTpos s T z = ∫ t, H t z ∂ν := by
    intro z
    unfold gTpos
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [H, gaussK]
    ring
  have hH : Measurable (fun p : ℝ × Euc d => H p.1 p.2) := by
    simp only [H, gaussK]
    fun_prop
  have hint : ∀ z, Integrable (fun t => H t z) ν := by
    intro z
    have h0 : Integrable (fun t : ℝ => t ^ (s / 2 - 1) * Real.exp (-t * ‖z‖ ^ 2)) ν :=
      clc3a_integrableOn_kernel_Ioc hs hT (sq_nonneg ‖z‖)
    refine (Integrable.const_mul h0 c).congr (ae_of_all _ fun t => ?_)
    simp only [H, gaussK]
    ring
  have hnn : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∀ z : Euc d, 0 ≤ H t z := by
    intro t ht z
    exact mul_nonneg (mul_nonneg hc.le (Real.rpow_nonneg ht.1.le _)) (Real.exp_pos _).le
  have hdom : ∀ z, ∫ t, ‖H t z‖ ∂ν ≤ (fun _ : Euc d => gTpos s T (0 : Euc d)) z := by
    intro z
    have h1 : ∫ t, ‖H t z‖ ∂ν = ∫ t, H t z ∂ν := by
      refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
      exact Real.norm_of_nonneg (hnn t ht z)
    rw [h1, ← hgT]
    exact ((gTpos_props hs hT).2.1 z).2
  have hmix := Qform_mix (ν := ν) H (fun _ : Euc d => gTpos s T (0 : Euc d)) ρ hH hint hdom hρ
    (domK_const _ hρ) X
  have hfun : (gTpos s T : Euc d → ℝ) = fun z => ∫ t, H t z ∂ν := funext hgT
  rw [hfun, hmix]
  refine setIntegral_nonneg measurableSet_Ioc (fun t ht => ?_)
  have : Qform (H t) X ρ = (c * t ^ (s / 2 - 1)) * Qform (gaussK t) X ρ :=
    Qform_smul (c * t ^ (s / 2 - 1)) (gaussK t) X ρ
  rw [this]
  exact mul_nonneg (mul_nonneg hc.le (Real.rpow_nonneg ht.1.le _))
    (Qform_gauss_nonneg ht.1 hρ hN X)

end HRS.MH.CoercLower
