import HRS.MS.SA16ZE4

/-!
# S.A.16 (SA16Z) E5: splitting of the level-`j` pairing integrand and its integrability
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section E5
variable {d : ℕ} {s : ℝ}

theorem sa16z_I_split (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {c cθ : ℝ} {μ φ : Euc d → ℝ}
    (hμ : ContDiff ℝ ∞ μ) (hφ : IsCcInfty φ)
    (hP : ∀ {ψ : Euc d → ℝ}, IsCcInfty ψ → ∀ x : Euc d,
      sa16z_P s μ ψ x = -c * fracLap d (s + 2 - d) (fun y => μ y * ψ y) x +
        HRS.CZ.Hls.hlsg_c s * ∑ i : Fin d, sa16z_pv d (s + 2 - d) i (fun y => sa16z_dm μ i y * ψ y) x)
    (p : ℝ) (j : ℕ) (x : Euc d) :
    sa16sz_vn φ j x ^ (p - 2) * ∑ idx : Fin j → Fin d, partialDeriv idx φ x * partialDeriv idx (sa16z_P s μ φ) x =
      -c * (μ x * sa16sz_vn φ j x ^ (p - 2) * ∑ idx : Fin j → Fin d, partialDeriv idx φ x *
          fracLap d (s + 2 - d) (partialDeriv idx φ) x) +
        ∑ l : Fin d, sa16z_IBd (HRS.CZ.Hls.hlsg_c s - c * cθ) (HRS.CZ.Hls.hlsg_c s) μ φ p (s + 2 - d) l j x +
        sa16sz_vn φ j x ^ (p - 2) * ∑ idx : Fin j → Fin d, partialDeriv idx φ x * sa16z_Err s c cθ μ φ j idx x := by
  have hdec := fun idx => sa16z_decomp hd hs0 hsd (cθ := cθ) hμ hφ hP j idx x
  have key : ∀ (v : ℝ) (W a e : (Fin j → Fin d) → ℝ) (T : (Fin j → Fin d) → Fin d → ℝ),
      v * ∑ idx, W idx * (a idx + ∑ l, T idx l + e idx) =
        v * ∑ idx, W idx * a idx + ∑ l, v * ∑ idx, W idx * T idx l + v * ∑ idx, W idx * e idx := by
    intro v W a e T
    have h1 : ∑ idx, W idx * ∑ l, T idx l = ∑ l, ∑ idx, W idx * T idx l := by
      simp_rw [Finset.mul_sum]; exact Finset.sum_comm
    have h2 : ∑ idx, W idx * (a idx + ∑ l, T idx l + e idx) =
        ∑ idx, W idx * a idx + ∑ idx, W idx * ∑ l, T idx l + ∑ idx, W idx * e idx := by
      simp only [mul_add, Finset.sum_add_distrib]
    rw [h2, h1, mul_add, mul_add, ← Finset.mul_sum]
  simp_rw [hdec]
  rw [key (sa16sz_vn φ j x ^ (p - 2)) (fun idx => partialDeriv idx φ x)
    (fun idx => -c * (μ x * fracLap d (s + 2 - d) (partialDeriv idx φ) x))
    (fun idx => sa16z_Err s c cθ μ φ j idx x)
    (fun idx l => (HRS.CZ.Hls.hlsg_c s - c * cθ) * (sa16z_dm μ l x * sa16z_pv d (s + 2 - d) l (partialDeriv idx φ) x) -
        HRS.CZ.Hls.hlsg_c s * sa16z_Q j idx l (fun a κ => sa16z_dm μ a x * sa16z_pv d (s + 2 - d) l (partialDeriv κ φ) x))]
  unfold sa16z_IBd
  congr 2
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun idx _ => ?_
  ring

end E5

end HRS.Whole.AppendixA.Phase2SA16R
