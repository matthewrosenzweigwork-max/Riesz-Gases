import HRS.MS.SA12DE7L

/-!
# S.A.12(c), packet E7.07 (worker S82Z2), part M: sums over jet indices, `L²` inner products (main theorem in part N)

`SA12Idx d m` is the finite index type `Σ j : Fin (m+1), (Fin j → Fin d)` of ordered jets; `sa12de7_sigma_sum` converts its
sum to the binomial jet sum; `sa12de7_inner_lp`, `sa12de7_norm_sq_lp` are the `L²` inner product and norm in integral form.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.SA12DE7

open HRS HRS.Whole HRS.MH.AdjointRd HRS.Whole.AppendixA HRS.Whole.Q09A

variable {d : ℕ}

abbrev SA12Idx (d m : ℕ) := Σ j : Fin (m + 1), (Fin (j : ℕ) → Fin d)

theorem sa12de7_inner_lp (h : Lp ℝ 2 (volume : Measure (Euc d))) {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) :
    inner ℝ h ((sa12de7_cc_memLp hψ).toLp ψ) = ∫ x, h x * ψ x := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(sa12de7_cc_memLp hψ).coeFn_toLp] with x h2
  rw [h2]
  simp [mul_comm]

theorem sa12de7_norm_sq_lp (h : Lp ℝ 2 (volume : Measure (Euc d))) : ‖h‖ ^ 2 = ∫ x, (h x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [sq]

theorem sa12de7_sigma_sum (m : ℕ) (f : (j : ℕ) → (Fin j → Fin d) → ℝ) :
    ∑ ι : SA12Idx d m, (m.choose (ι.1 : ℕ) : ℝ) * f ι.1 ι.2 =
      ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * ∑ idx : Fin j → Fin d, f j idx := by
  rw [Fintype.sum_sigma]
  have := Fin.sum_univ_eq_sum_range (fun j => (m.choose j : ℝ) * ∑ idx : Fin j → Fin d, f j idx) (m + 1)
  rw [← this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]

end HRS.MS.SA12DE7
