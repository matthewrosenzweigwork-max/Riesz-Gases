import HRS.MS.SA16ZD2
import HRS.MS.CzElemAux4
import HRS.MS.Asm15Tie

/-!
# S.A.16 (SA16Z) D3: the `L^p` bound of the error `Err_idx`
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section D3
variable {d : ℕ}

lemma sa16z_memCb {N : ℕ} {Λ : ℝ} {μ : Euc d → ℝ} (hμs : ContDiff ℝ ∞ μ) (hCb : sa16z_Cb N Λ μ) :
    HRS.MemCb N μ :=
  ⟨hμs.of_le (by exact_mod_cast le_top), fun j hj => ⟨Λ, by rintro _ ⟨y, rfl⟩; exact hCb j hj y⟩⟩

lemma sa16z_cbNorm_le {N : ℕ} {Λ : ℝ} {μ : Euc d → ℝ} (hCb : sa16z_Cb N Λ μ) :
    HRS.cbNorm N μ ≤ ((N : ℝ) + 1) * Λ := by
  unfold HRS.cbNorm
  calc ∑ j ∈ Finset.range (N + 1), ⨆ z : Euc d, ‖iteratedFDeriv ℝ j μ z‖ ≤ ∑ j ∈ Finset.range (N + 1), Λ :=
        Finset.sum_le_sum fun j hj => ciSup_le fun z => hCb j (by have := Finset.mem_range.1 hj; omega) z
    _ = ((N : ℝ) + 1) * Λ := by simp

lemma sa16z_cbNorm_nonneg {N : ℕ} {μ : Euc d → ℝ} : 0 ≤ HRS.cbNorm N μ :=
  Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun z => norm_nonneg _

lemma sa16z_eLpNorm_pd_le {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) {p : ℝ} {k : ℕ} (κ : Fin k → Fin d) :
    eLpNorm (partialDeriv κ φ) (ENNReal.ofReal p) volume ≤ sa16z_JJ p φ k := by
  unfold sa16z_JJ
  refine eLpNorm_mono (sa16j_pd_smooth hφ κ).continuous.aestronglyMeasurable fun x => ?_
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sa16sz_vn_nonneg _ _ _)]
  exact sa16sz_abs_le_vn φ k κ x

end D3

end HRS.Whole.AppendixA.Phase2SA16R
