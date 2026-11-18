import HRS.MS.SA16JetSchwartz

/-!
# S.A.16 (SA16Q), E11 part 1: Taylor expansion along a segment

For a smooth `v : ℝ^d → F` (`F` complete) and `x, z`, the function `s ↦ v (x + s • z)` has
`k`-th derivative bounded by `‖D^k v (x + s z)‖ ‖z‖^k`; Taylor's formula with integral remainder
(from `1` back to `0`) gives the pointwise bound
`‖v x‖ ≤ ∑_{k<n} ‖z‖^k/k! ‖D^k v(x+z)‖ + ∫_0^1 t^{n-1}/(n-1)! ‖z‖^n ‖D^n v(x+tz)‖ dt`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Nat

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16

lemma sa16q_mul_le {a b c : ℝ≥0∞} (h : b ≤ c) : a * b ≤ a * c := mul_le_mul' le_rfl h

section Taylor
variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- the derivative of `s ↦ v (x + s • z)` along a line -/
lemma sa16q_line_iter {v : Euc d → F} (hv : ContDiff ℝ ∞ v) (x z : Euc d) (k : ℕ) (t : ℝ) :
    ‖iteratedDeriv k (fun s : ℝ => v (x + s • z)) t‖ ≤ ‖iteratedFDeriv ℝ k v (x + t • z)‖ * ‖z‖ ^ k := by
  have hv' : ContDiff ℝ ∞ (fun w => v (x + w)) := hv.comp (contDiff_const.add contDiff_id)
  have hg : (fun s : ℝ => v (x + s • z)) =
      (fun w => v (x + w)) ∘ (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) z) := by
    funext s; simp
  have hkey := ContinuousLinearMap.iteratedFDeriv_comp_right
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) z) hv' t (i := k) (by exact_mod_cast le_top)
  rw [iteratedDeriv_eq_iteratedFDeriv, hg, hkey]
  have h1 : iteratedFDeriv ℝ k (fun w => v (x + w))
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) z) t) = iteratedFDeriv ℝ k v (x + t • z) := by
    rw [iteratedFDeriv_comp_add_left]
    simp
  rw [h1]
  have h2 := ContinuousMultilinearMap.le_opNorm
    ((iteratedFDeriv ℝ k v (x + t • z)).compContinuousLinearMap
      fun _ : Fin k => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) z) (fun _ : Fin k => (1 : ℝ))
  have h3 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le (iteratedFDeriv ℝ k v (x + t • z))
    (fun _ : Fin k => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) z)
  have h4 : ‖ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) z‖ = ‖z‖ := by
    rw [ContinuousLinearMap.norm_smulRight_apply]; simp
  simp only [h4, Finset.prod_const, Finset.card_univ, Fintype.card_fin, norm_one, one_pow, mul_one] at h2 h3
  exact h2.trans h3

/-- Taylor along the segment from `x + z` back to `x`, in norm. -/
lemma sa16q_taylor_pt [CompleteSpace F] {v : Euc d → F} (hv : ContDiff ℝ ∞ v) (x z : Euc d) (N : ℕ) :
    ‖v x‖ ≤ (∑ k ∈ Finset.range (N + 1), ‖z‖ ^ k / (k ! : ℝ) * ‖iteratedFDeriv ℝ k v (x + z)‖) +
      ∫ t in (0 : ℝ)..1, t ^ N / (N ! : ℝ) *
        (‖z‖ ^ (N + 1) * ‖iteratedFDeriv ℝ (N + 1) v (x + t • z)‖) := by
  set f : ℝ → F := fun s => v (x + s • z) with hf
  have hfd : ContDiff ℝ ∞ f := hv.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hT := taylor_integral_remainder (f := f) (x := 0) (x₀ := 1) (n := N)
    ((hfd.of_le (by exact_mod_cast le_top)).contDiffOn)
  have hU : UniqueDiffOn ℝ (uIcc (1 : ℝ) 0) := uniqueDiffOn_uIcc (by norm_num)
  have hw : ∀ k : ℕ, ∀ t ∈ uIcc (1 : ℝ) 0, iteratedDerivWithin k f (uIcc 1 0) t = iteratedDeriv k f t :=
    fun k t ht => iteratedDerivWithin_eq_iteratedDeriv hU
      ((hfd.of_le (by exact_mod_cast le_top)).contDiffAt) ht
  have h0 : f 0 = v x := by simp [hf]
  have hint_eq : ∫ t in (1 : ℝ)..0, ((0 - t) ^ N / (N ! : ℝ)) • iteratedDerivWithin (N + 1) f (uIcc 1 0) t =
      ∫ t in (1 : ℝ)..0, ((0 - t) ^ N / (N ! : ℝ)) • iteratedDeriv (N + 1) f t :=
    intervalIntegral.integral_congr (fun t ht => by rw [hw (N + 1) t ht])
  rw [hint_eq] at hT
  have hcore : f 0 = taylorWithinEval f N (uIcc 1 0) 1 0 +
      ∫ t in (1 : ℝ)..0, ((0 - t) ^ N / (N ! : ℝ)) • iteratedDeriv (N + 1) f t := by
    rw [add_comm]; exact sub_eq_iff_eq_add.1 hT
  have hcont : Continuous (fun t : ℝ => ‖iteratedFDeriv ℝ (N + 1) v (x + t • z)‖) :=
    ((hv.continuous_iteratedFDeriv (m := N + 1) (by exact_mod_cast le_top)).comp
      (continuous_const.add (continuous_id.smul continuous_const))).norm
  rw [← h0, hcore]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [taylor_within_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_smul, hw k 1 (by simp)]
    have h1 := sa16q_line_iter hv x z k 1
    simp only [one_smul] at h1
    have hk : ‖((k ! : ℝ)⁻¹ * ((0 : ℝ) - 1) ^ k)‖ = 1 / (k ! : ℝ) := by
      rw [norm_mul, norm_inv, norm_pow]
      simp
    rw [hk]
    calc 1 / (k ! : ℝ) * ‖iteratedDeriv k f 1‖
        ≤ 1 / (k ! : ℝ) * (‖iteratedFDeriv ℝ k v (x + z)‖ * ‖z‖ ^ k) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ‖z‖ ^ k / (k ! : ℝ) * ‖iteratedFDeriv ℝ k v (x + z)‖ := by ring
  · rw [intervalIntegral.integral_symm (0 : ℝ) 1, norm_neg]
    refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0 : ℝ) ≤ 1)).trans ?_
    refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ fun t ht => ?_
    · refine Continuous.intervalIntegrable ?_ _ _
      have : Continuous (iteratedDeriv (N + 1) f) := hfd.continuous_iteratedDeriv _ (by exact_mod_cast le_top)
      exact ((((continuous_const.sub continuous_id).pow N).div_const _).smul this).norm
    · exact (((continuous_pow N).div_const _).mul (continuous_const.mul hcont)).intervalIntegrable _ _
    · have h1 := sa16q_line_iter hv x z (N + 1) t
      have hN : ‖((0 - t) ^ N / (N ! : ℝ))‖ = t ^ N / (N ! : ℝ) := by
        rw [Real.norm_eq_abs, abs_div, abs_pow, zero_sub, abs_neg, abs_of_nonneg ht.1, Nat.abs_cast]
      rw [norm_smul, hN]
      calc t ^ N / (N ! : ℝ) * ‖iteratedDeriv (N + 1) f t‖
          ≤ t ^ N / (N ! : ℝ) * (‖iteratedFDeriv ℝ (N + 1) v (x + t • z)‖ * ‖z‖ ^ (N + 1)) :=
            mul_le_mul_of_nonneg_left h1 (by have := ht.1; positivity)
        _ = _ := by ring

end Taylor

end HRS.Whole.AppendixA.Phase2SA16Q
