import Mathlib
import HRS.Whole.AppendixALemmas
import HRS.MH.CoercLowerDefs
import HRS.MH.CoercLowerFinal
import HRS.MH.CoercTestSpecDefs
import HRS.MH.CoercTestW7b
import HRS.MH.CoercTestW7c

/-!
# CoercTest W7d: `test_bound_core`

Statement copied verbatim from `HRS/MH/CoercTestSpec.lean`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform

namespace HRS.MH.CoercTest

open HRS.MH.CoercLower

variable {d N : ℕ}

/-- [W7d] The test-function clause of `WholeCoercivityPair`, for `C₀ ≥ C₀'`, with `C` independent of `C₀`.
Route: W7b with `T = (NΛ)^{2/d} ≥ 1` (`N ≥ 2`, `Λ ≥ 1`), `T^{-1/2} = smearScale d N Λ` (`Real.rpow_mul`),
W7c, `Real.sqrt_le_sqrt`, `Real.sqrt_mul` (`√(2x) = √2 √x`); take `C = max (C₇b) (√2 C₇b)`. -/
theorem test_bound_core (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C C₀' : ℝ, 0 < C ∧ 0 ≤ C₀' ∧ ∀ C₀ : ℝ, C₀' ≤ C₀ → TestBoundClause d s C₀ C := by
  obtain ⟨C7, hC7, hb⟩ := pair_le_qform_gTs (d := d) hd hs0 hsd
  obtain ⟨C₀', hC₀', hc⟩ := qform_gTs_le_energy (d := d) hd hs0 hsd
  refine ⟨Real.sqrt 2 * C7, C₀', mul_pos (Real.sqrt_pos.2 (by norm_num)) hC7, hC₀', fun C₀ hC₀ => ?_⟩
  unfold TestBoundClause
  intro Λ hΛ N hN ρ hρ hρΛ hint X hX ψ L hL hLip hcomp hψ
  have h2N : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNΛ : (1 : ℝ) ≤ (N : ℝ) * Λ := by nlinarith
  have hd0 : (0 : ℝ) ≤ 2 / (d : ℝ) := by positivity
  have hT1 : (1 : ℝ) ≤ ((N : ℝ) * Λ) ^ (2 / (d : ℝ)) := Real.one_le_rpow hNΛ hd0
  have hbound := hb (((N : ℝ) * Λ) ^ (2 / (d : ℝ))) hT1 ρ hρ hint N (by omega) X ψ L hL hLip hcomp hψ
  have hq := hc C₀ hC₀ Λ hΛ N (by omega) ρ hρ hρΛ hint X hX
  have hsm : (((N : ℝ) * Λ) ^ (2 / (d : ℝ))) ^ (-(1 / 2 : ℝ)) = HRS.smearScale d N Λ := by
    rw [← Real.rpow_mul (le_trans zero_le_one hNΛ)]
    unfold HRS.smearScale
    congr 1
    ring
  rw [hsm] at hbound
  have hhom : 0 ≤ HRS.Whole.AppendixALemmas.homSobolevRd (((d : ℝ) - s) / 2) ψ := by
    unfold HRS.Whole.AppendixALemmas.homSobolevRd
    exact Real.sqrt_nonneg _
  have hsq2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hsqrt : Real.sqrt (Qform (gTs d s (((N : ℝ) * Λ) ^ (2 / (d : ℝ)))) X ρ) ≤
      Real.sqrt 2 * Real.sqrt (HRS.Whole.rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) +
        HRS.oNΛ d s C₀ Λ N) := by
    calc Real.sqrt (Qform (gTs d s (((N : ℝ) * Λ) ^ (2 / (d : ℝ)))) X ρ)
        ≤ Real.sqrt (2 * (HRS.Whole.rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) +
            HRS.oNΛ d s C₀ Λ N)) := Real.sqrt_le_sqrt hq
      _ = Real.sqrt 2 * Real.sqrt (HRS.Whole.rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) +
            HRS.oNΛ d s C₀ Λ N) := Real.sqrt_mul (by norm_num) _
  have hC7hom : 0 ≤ C7 * HRS.Whole.AppendixALemmas.homSobolevRd (((d : ℝ) - s) / 2) ψ :=
    mul_nonneg hC7.le hhom
  have h2 : C7 * HRS.Whole.AppendixALemmas.homSobolevRd (((d : ℝ) - s) / 2) ψ *
      Real.sqrt (Qform (gTs d s (((N : ℝ) * Λ) ^ (2 / (d : ℝ)))) X ρ) ≤
      Real.sqrt 2 * C7 * HRS.Whole.AppendixALemmas.homSobolevRd (((d : ℝ) - s) / 2) ψ *
        Real.sqrt (HRS.Whole.rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) +
          HRS.oNΛ d s C₀ Λ N) := by
    calc C7 * HRS.Whole.AppendixALemmas.homSobolevRd (((d : ℝ) - s) / 2) ψ *
          Real.sqrt (Qform (gTs d s (((N : ℝ) * Λ) ^ (2 / (d : ℝ)))) X ρ)
        ≤ C7 * HRS.Whole.AppendixALemmas.homSobolevRd (((d : ℝ) - s) / 2) ψ *
            (Real.sqrt 2 * Real.sqrt (HRS.Whole.rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) +
              HRS.oNΛ d s C₀ Λ N)) := mul_le_mul_of_nonneg_left hsqrt hC7hom
      _ = Real.sqrt 2 * C7 * HRS.Whole.AppendixALemmas.homSobolevRd (((d : ℝ) - s) / 2) ψ *
            Real.sqrt (HRS.Whole.rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) +
              HRS.oNΛ d s C₀ Λ N) := by ring
  have hsmL : 0 ≤ HRS.smearScale d N Λ * L := by
    apply mul_nonneg _ hL
    unfold HRS.smearScale
    exact Real.rpow_nonneg (le_trans zero_le_one hNΛ) _
  have h3 : C7 * L * HRS.smearScale d N Λ ≤ Real.sqrt 2 * C7 * HRS.smearScale d N Λ * L := by
    have hC7s : 0 ≤ C7 * (HRS.smearScale d N Λ * L) := mul_nonneg hC7.le hsmL
    have key : 0 ≤ C7 * (HRS.smearScale d N Λ * L) * (Real.sqrt 2 - 1) :=
      mul_nonneg hC7s (by linarith)
    nlinarith [key]
  linarith [hbound, h2, h3]

end HRS.MH.CoercTest
