import HRS.MS.SA16Y6CLv1
import HRS.MS.SA16ZF1
import HRS.MS.SA16Y6C1
import HRS.MS.SA16Y5Ip1

/-! # SA16Y6 critical-case copy of SA16Y5Ip1 (s = d-1) -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.BreakdownSA16

section Ip1
variable {d : ℕ} {s : ℝ}
theorem sa16y6c_iso_pairing (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hs1 : s = (d : ℝ) - 1)
    (hθ0 : 0 < s + 2 - d) {p : ℝ} (hp : 2 ≤ p) (hfar : (d : ℝ) < p * (s + 1)) {Wd : ℝ} (hWd : 0 ≤ Wd)
    (Λ : ℝ) (hΛ : 0 ≤ Λ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {μ φ : Euc d → ℝ}, HRS.S16Frac.S16FracCb μ → (∀ x, 0 ≤ μ x) → IsCcInfty φ →
      sa16z_Cb 2 Λ μ → sa16y5_Dec (m + 2) Wd μ →
      ∫ x, sa16sz_dens m p φ (sa16z_P s μ φ) x ≤
        C * ∑ k : Fin (m + 1), ∫ x, sa16sz_vn φ k x ^ p := by
  have hlev := fun j : ℕ => sa16y6c_level hd hs0 hsd hs1 hθ0 hp hfar hWd Λ hΛ j
  choose Cj hCj0 hCj using hlev
  refine ⟨∑ j ∈ Finset.range (m + 1), Cj j, Finset.sum_nonneg fun j _ => hCj0 j,
    fun {μ φ} hμ hpos hφ hCb hdec => ?_⟩
  have hV0 : ∀ k, 0 ≤ ∫ x, sa16sz_vn φ k x ^ p := fun k =>
    integral_nonneg fun x => Real.rpow_nonneg (sa16sz_vn_nonneg φ k x) _
  have hμs : ContDiff ℝ ∞ μ := hμ.1
  have e : ∀ x, sa16sz_dens m p φ (sa16z_P s μ φ) x = ∑ j ∈ Finset.range (m + 1),
      sa16sz_vn φ j x ^ (p - 2) * ∑ idx : Fin j → Fin d, partialDeriv idx φ x *
        partialDeriv idx (sa16z_P s μ φ) x := by
    intro x
    unfold sa16sz_dens
    exact Fin.sum_univ_eq_sum_range (fun j => sa16sz_vn φ j x ^ (p - 2) * ∑ idx : Fin j → Fin d,
      partialDeriv idx φ x * partialDeriv idx (sa16z_P s μ φ) x) (m + 1)
  have hint : ∀ j ∈ Finset.range (m + 1), Integrable (fun x => sa16sz_vn φ j x ^ (p - 2) *
      ∑ idx : Fin j → Fin d, partialDeriv idx φ x * partialDeriv idx (sa16z_P s μ φ) x) :=
    fun j _ => sa16z_I_int hs0 hsd hμs hφ hp j
  simp_rw [e]
  rw [integral_finsetSum _ hint]
  have hsumk : ∑ k : Fin (m + 1), ∫ x, sa16sz_vn φ k x ^ p = ∑ k ∈ Finset.range (m + 1), ∫ x, sa16sz_vn φ k x ^ p :=
    Fin.sum_univ_eq_sum_range (fun k => ∫ x, sa16sz_vn φ k x ^ p) (m + 1)
  rw [hsumk]
  calc ∑ j ∈ Finset.range (m + 1), ∫ x, sa16sz_vn φ j x ^ (p - 2) * ∑ idx : Fin j → Fin d,
        partialDeriv idx φ x * partialDeriv idx (sa16z_P s μ φ) x
      ≤ ∑ j ∈ Finset.range (m + 1), Cj j * ∑ k ∈ Finset.range (m + 1), ∫ x, sa16sz_vn φ k x ^ p := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hjm : j ≤ m := by have := Finset.mem_range.1 hj; omega
        refine (hCj j hμ hpos hφ hCb (sa16y5_Dec_mono (by omega) hdec)).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (hCj0 j)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun k _ _ => hV0 k
    _ = _ := by rw [Finset.sum_mul]

end Ip1

end HRS.Whole.AppendixA.Phase2SA16R
