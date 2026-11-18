import HRS.MS.SA16TGc2
import HRS.MS.SA16SNl4

/-!
# S.A.16 (SA16T) Gc3: the nonlocal operator of a small density is small

`sa16t_G_small`: there is `C` such that every smooth `ν` with `‖D^j ν‖ ≤ A (1+|y|)^{-(d+3)}` (`j ≤ k+3`, `A > 0`) has a
bounded operator `T` on `W^{k,p}` with `SA16SubOp` and `‖T‖ ≤ C A` (scaling `ν/A` and linearity of `eucNonlocal` in the
density).
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16P Phase2SA16Q

section Gc3
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

theorem sa16t_G_small (d k : ℕ) (hd : 1 ≤ d) (s MB : ℝ) (hs0 : 0 ≤ s) (hs2 : s ≤ (d : ℝ) - 2)
    (hfar : (d : ℝ) < p * (s + 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Matrix (Fin d) (Fin d) ℝ, (∀ i j, |M i j| ≤ MB) → ∀ (ν : Euc d → ℝ) (A : ℝ), 0 < A →
      ContDiff ℝ ((k + 3 : ℕ) : WithTop ℕ∞) ν → (∀ j ≤ k + 3, ∀ y, ‖iteratedFDeriv ℝ j ν y‖ ≤ A * sa16p_w d y) →
      ∃ T : WmpSpace d k p →L[ℝ] WmpSpace d k p, SA16SubOp d k p s M ν T ∧ ‖T‖ ≤ C * A := by
  obtain ⟨C, hC, hex⟩ := sa16so_G_exists d k hd s p MB ((((k + 3 : ℕ) : ℝ) + 2) * 1) hs0 hs2 hfar
  have hd2 : 2 ≤ d := by
    have : (2 : ℝ) ≤ d := by linarith
    exact_mod_cast this
  refine ⟨C, hC, fun M hM ν A hA hν hb => ?_⟩
  set ν' : Euc d → ℝ := fun y => A⁻¹ * ν y with hν'
  have hν'd : ContDiff ℝ ((k + 3 : ℕ) : WithTop ℕ∞) ν' := contDiff_const.mul hν
  have hb' : ∀ j ≤ k + 3, ∀ y, ‖iteratedFDeriv ℝ j ν' y‖ ≤ 1 * sa16p_w d y := by
    intro j hj y
    have h1 : iteratedFDeriv ℝ j ν' y = A⁻¹ • iteratedFDeriv ℝ j ν y := by
      have := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (a := A⁻¹) (f := ν) (i := j) (x := y)
        (hν.contDiffAt.of_le (by exact_mod_cast hj))
      have e : ν' = A⁻¹ • ν := by funext y; simp [hν']
      rw [e]; exact this
    rw [h1, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hA.le)]
    calc A⁻¹ * ‖iteratedFDeriv ℝ j ν y‖ ≤ A⁻¹ * (A * sa16p_w d y) :=
          mul_le_mul_of_nonneg_left (hb j hj y) (inv_nonneg.2 hA.le)
      _ = 1 * sa16p_w d y := by field_simp
  have hreg := sa16t_regular_of_decay hν'd hb'
  obtain ⟨T', hT'n, hT'⟩ := hex M hM ν' hreg
  refine ⟨A • T', fun φ => ?_, ?_⟩
  · have hb0 : ∀ y, |ν' y| ≤ 1 := fun y => by
      have := hb' 0 (Nat.zero_le _) y
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
      exact this.trans (by simpa using sa16p_w_le_one y)
    have hb1 : ∀ y, ‖fderiv ℝ ν' y‖ ≤ 1 := fun y => by
      rw [sa16p_norm_fderiv_eq]
      exact (hb' 1 (by omega) y).trans (by simpa using sa16p_w_le_one y)
    have h1 : ContDiff ℝ 1 ν' := hν'd.of_le (by exact_mod_cast (by omega : 1 ≤ k + 3))
    have hνeq : ν = fun y => A * ν' y := by
      funext y; simp only [hν']; field_simp
    have hF : HRS.MH.AdjointRd.eucNonlocal s M ν φ.1 =
        fun x => A * HRS.MH.AdjointRd.eucNonlocal s M ν' φ.1 x := by
      funext x
      have := sa16t_F_smul hd2 hs0 hs2 M h1 hb0 hb1 A (sa16so_schw φ) x
      rw [hνeq]
      exact this
    rw [hF]
    filter_upwards [sa16r_wrep_smul d k p A (T' (sa16r_Jcc d k p φ)), hT' φ] with x h1 h2
    rw [ContinuousLinearMap.smul_apply, h1, h2]
  · calc ‖A • T'‖ ≤ ‖A‖ * ‖T'‖ := ContinuousLinearMap.opNorm_smul_le A T'
      _ ≤ A * C := by
          rw [Real.norm_of_nonneg hA.le]
          exact mul_le_mul_of_nonneg_left hT'n hA.le
      _ = C * A := mul_comm _ _

end Gc3

end HRS.Whole.AppendixA.Phase2SA16R
