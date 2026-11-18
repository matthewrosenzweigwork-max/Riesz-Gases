import HRS.MH.ScreenedP1
import HRS.MH.ScreenedAsmLocal
import HRS.MH.ScreenedL1Aux1
import HRS.MH.ScreenedK5
import HRS.MH.ScreenedAsmPairingAux1

/-!
# ASM-pairing (S.B.4(iii), `screened_pairing`), `ScreenedSpec.lean` / `AppendixBKernel.lean`

`s < d-1`: `screened_pairing_lt_proof` (P1).  `s = d-1` (`kgOrder = 0`): the argument `aψ` is measurable
(`q1_aesm_of_rep`), `‖aψ‖₂ ≤ Λ‖ψ‖₂` (so `aψ ∈ H^{s+1-d} = L²` and `screened_local_global` applies),
the representative `w'` of `∂_ig * (aψ)` is a.e. equal to `u` (`gk_unique`), then Cauchy-Schwarz.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

theorem screened_pairing_proof : type_of% @HRS.Whole.screened_pairing := by
  intro d hd s hs0 hsd h2
  by_cases hs : s < (d : ℝ) - 1
  · exact screened_pairing_lt_proof hd hs0 hs h2
  · have hsd1 : (d : ℝ) - 1 ≤ s := not_lt.mp hs
    have hseq : s = (d : ℝ) - 1 := le_antisymm hsd hsd1
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hsdd : s < d := by linarith
    have hk0 : kgOrder d s = 0 := by
      unfold kgOrder
      exact max_eq_right (by linarith)
    have hsi : s + 1 - (d : ℝ) = 0 := by linarith
    obtain ⟨C0, hC0⟩ := screened_local_global_proof hd hsdd hsd1
    refine ⟨max C0 0, fun Λ a hA i ψ w u hψ hw hψfin hu hrep => ?_⟩
    have hΛ : 0 ≤ Λ := by
      have h00 : 0 ≤ jbracket (0 : Euc d) ^ ((d : ℝ) + 3) * |a 0| :=
        mul_nonneg (Real.rpow_nonneg (le_trans zero_le_one (p1_one_le_jbracket 0)) _) (abs_nonneg _)
      linarith [hA 0]
    have hab : ∀ x, |a x| ≤ Λ := by
      intro x
      have h1 : 1 ≤ jbracket x ^ ((d : ℝ) + 3) :=
        Real.one_le_rpow (p1_one_le_jbracket x) (by positivity)
      exact (le_mul_of_one_le_left (abs_nonneg _) h1).trans (hA x)
    have hm : AEStronglyMeasurable (fun y => a y * ψ y) volume := q1_aesm_of_rep hs0 i hrep
    have hψa : MemLp (fun y => a y * ψ y) 2 volume := by
      refine MemLp.of_le ((hψ.norm).const_mul Λ) hm (ae_of_all _ fun x => ?_)
      show ‖a x * ψ x‖ ≤ ‖Λ * ‖ψ x‖‖
      rw [Real.norm_of_nonneg (mul_nonneg hΛ (norm_nonneg _)), norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hab x) (norm_nonneg _)
    have hnorm_aψ : eLpNorm (fun y => a y * ψ y) 2 volume ≤ ENNReal.ofReal Λ * eLpNorm ψ 2 volume := by
      have h1 : eLpNorm (fun y => a y * ψ y) 2 volume ≤ eLpNorm (fun y => Λ * ‖ψ y‖) 2 volume :=
        eLpNorm_mono_real hm (fun x => by
          show ‖a x * ψ x‖ ≤ Λ * ‖ψ x‖
          rw [norm_mul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hab x) (norm_nonneg _))
      have h2' : eLpNorm (fun y => Λ * ‖ψ y‖) 2 volume = ‖Λ‖ₑ * eLpNorm (fun y => ‖ψ y‖) 2 volume :=
        eLpNorm_const_smul Λ (fun y => ‖ψ y‖) 2 volume
      rw [eLpNorm_norm ψ hψ.aestronglyMeasurable] at h2'
      rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg hΛ] at h2'
      rw [h2'] at h1
      exact h1
    have hfin : sobolevNormE (s + 1 - d) (fun y => a y * ψ y) < ⊤ := by
      rw [hsi, l1_sobolev_zero_eq hψa]
      exact hψa.eLpNorm_lt_top
    obtain ⟨w', hw'rep, hw'L2, hw'bd⟩ := hC0 i (fun y => a y * ψ y) hfin
    rw [hsi, l1_sobolev_zero_eq hψa] at hw'bd
    have hu_ae : u =ᵐ[volume] w' := gk_unique_proof i hrep hw'rep
    have hbound : eLpNorm w' 2 volume ≤ ENNReal.ofReal (max C0 0) * (ENNReal.ofReal Λ * eLpNorm ψ 2 volume) :=
      hw'bd.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) hnorm_aψ)
    have hEq : ∫ x, u x * w x = ∫ x, w' x * w x := by
      apply integral_congr_ae
      filter_upwards [hu_ae] with x hx
      simp only [hx]
    have hint : ‖∫ x, u x * w x‖ₑ ≤ ∫⁻ x, ‖w' x‖ₑ * ‖w x‖ₑ := by
      rw [hEq]
      exact (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun x => enorm_mul _ _))
    have hCS : (∫⁻ x, ‖w' x‖ₑ * ‖w x‖ₑ) ^ 2 ≤ (∫⁻ x, ‖w' x‖ₑ ^ 2) * ∫⁻ x, ‖w x‖ₑ ^ 2 :=
      p1_cs_aemeas volume (fun x => ‖w' x‖ₑ) (fun x => ‖w x‖ₑ)
        hw'L2.aestronglyMeasurable.enorm hw.aestronglyMeasurable.enorm
    have hW : (∫⁻ x, ‖w' x‖ₑ * ‖w x‖ₑ) ≤ eLpNorm w' 2 volume * eLpNorm w 2 volume := by
      apply p1_le_of_sq_le
      calc (∫⁻ x, ‖w' x‖ₑ * ‖w x‖ₑ) ^ 2 ≤ (∫⁻ x, ‖w' x‖ₑ ^ 2) * ∫⁻ x, ‖w x‖ₑ ^ 2 := hCS
        _ = (eLpNorm w' 2 volume) ^ 2 * (eLpNorm w 2 volume) ^ 2 := by
            rw [← l1_sq_eLpNorm_ae w' hw'L2.aestronglyMeasurable, ← l1_sq_eLpNorm_ae w hw.aestronglyMeasurable]
        _ = (eLpNorm w' 2 volume * eLpNorm w 2 volume) ^ 2 := by ring
    rw [hk0, l1_sobolev_zero_eq hψ, ENNReal.ofReal_mul (le_max_right _ _), ← Real.norm_eq_abs,
      ofReal_norm_eq_enorm]
    calc ‖∫ x, u x * w x‖ₑ ≤ ∫⁻ x, ‖w' x‖ₑ * ‖w x‖ₑ := hint
      _ ≤ eLpNorm w' 2 volume * eLpNorm w 2 volume := hW
      _ ≤ (ENNReal.ofReal (max C0 0) * (ENNReal.ofReal Λ * eLpNorm ψ 2 volume)) * eLpNorm w 2 volume :=
          mul_le_mul_of_nonneg_right hbound zero_le
      _ = ENNReal.ofReal (max C0 0) * ENNReal.ofReal Λ * eLpNorm ψ 2 volume * eLpNorm w 2 volume := by ring

end HRS.MH.Screened
