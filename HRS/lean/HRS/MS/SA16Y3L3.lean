import HRS.MS.SA16Y3L2
import HRS.MS.SA16SEn11

/-!
# S.A.16 (SA16Y3) L3: bound of the pairing `ℓ_ψ(K_r y)` for `K_r = B_{b_r} - T1_r ι` by the level-`m` norm of `ι² y`

`sa16y3_K_pair_bound`: if `|div(b ψ)| ≤ cN` on `closedBall 0 R0` and `= 0` outside, `T0 ι = ι T1`, `‖T0‖ ≤ CG`, then
`|ℓ_ψ(K y)| ≤ (cN vol(B_{R0})^{1/q} + ‖ℓ_ψ‖ CG) ‖ι² y‖`.
The constant depends on `ψ, R0, cN, CG`, not on the zeroth-order size of `b` away from the support of `ψ`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section L3
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16y3_ell_iota2 {m : ℕ} {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) (y : WmpSpace d (m + 1 + 1) p) :
    sa16r_ell d m p hψ (sa16sz_iota2 d m p y) = sa16r_ell d (m + 1 + 1) p hψ y := by
  unfold sa16sz_iota2
  rw [ContinuousLinearMap.comp_apply, sa16r_ell_iota, sa16r_ell_iota]

set_option maxHeartbeats 1000000 in
theorem sa16y3_K_pair_bound {m : ℕ} {B' CG cN R0 : ℝ} {bc : Fin d → Euc d → ℝ}
    (hbo : SA16BddCoef (m + 1) B' bc) {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ)
    (hNb : ∀ x, |sa16so_divFun bc ψ x| ≤ cN * (closedBall (0 : Euc d) R0).indicator (fun _ => (1 : ℝ)) x)
    (hcN : 0 ≤ cN)
    (T1 : WmpSpace d (m + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (T0 : WmpSpace d m p →L[ℝ] WmpSpace d m p)
    (hcomp : (sa16r_iota d m p).comp T1 = T0.comp (sa16r_iota d m p)) (hT0 : ‖T0‖ ≤ CG)
    (K : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (hK : K = sa16so_B d (m + 1) p bc - T1.comp (sa16r_iota d (m + 1) p)) (y : WmpSpace d (m + 1 + 1) p) :
    |sa16r_ell d (m + 1) p hψ (K y)| ≤
      (cN * (volume (closedBall (0 : Euc d) R0)).toReal ^ (1 / Real.conjExponent p) +
        ‖sa16r_ell d m p hψ‖ * CG) * ‖sa16sz_iota2 d m p y‖ := by
  have hCG : 0 ≤ CG := (norm_nonneg T0).trans hT0
  have hsplit : sa16r_ell d (m + 1) p hψ (K y) =
      -sa16r_ell d (m + 1 + 1) p (sa16so_cc_div hbo hψ) y -
        sa16r_ell d m p hψ (T0 (sa16sz_iota2 d m p y)) := by
    rw [hK, sub_apply, map_sub, sa16so_ell_B hbo hψ y]
    congr 1
    rw [ContinuousLinearMap.comp_apply, ← sa16r_ell_iota hψ m]
    have h1 := congrArg (fun L => L (sa16r_iota d (m + 1) p y)) hcomp
    simp only [ContinuousLinearMap.comp_apply] at h1
    rw [h1]; rfl
  have hA : |sa16r_ell d (m + 1 + 1) p (sa16so_cc_div hbo hψ) y| ≤
      cN * (volume (closedBall (0 : Euc d) R0)).toReal ^ (1 / Real.conjExponent p) *
        ‖sa16sz_iota2 d m p y‖ := by
    rw [← sa16y3_ell_iota2 (sa16so_cc_div hbo hψ), sa16r_ell_apply]
    exact sa16y3_ell_sup_bound _ (sa16so_cc_div hbo hψ).1.continuous.aestronglyMeasurable hcN hNb
  have hBn : |sa16r_ell d m p hψ (T0 (sa16sz_iota2 d m p y))| ≤ ‖sa16r_ell d m p hψ‖ * CG *
      ‖sa16sz_iota2 d m p y‖ := by
    rw [← Real.norm_eq_abs]
    refine ((sa16r_ell d m p hψ).le_opNorm _).trans ?_
    calc ‖sa16r_ell d m p hψ‖ * ‖T0 (sa16sz_iota2 d m p y)‖
        ≤ ‖sa16r_ell d m p hψ‖ * (CG * ‖sa16sz_iota2 d m p y‖) :=
          mul_le_mul_of_nonneg_left ((T0.le_opNorm _).trans (mul_le_mul_of_nonneg_right hT0 (norm_nonneg _)))
            (ContinuousLinearMap.opNorm_nonneg _)
      _ = _ := by ring
  rw [hsplit]
  calc |-sa16r_ell d (m + 1 + 1) p (sa16so_cc_div hbo hψ) y - sa16r_ell d m p hψ (T0 (sa16sz_iota2 d m p y))|
      ≤ |sa16r_ell d (m + 1 + 1) p (sa16so_cc_div hbo hψ) y| +
          |sa16r_ell d m p hψ (T0 (sa16sz_iota2 d m p y))| := by
        rw [sub_eq_add_neg, ← abs_neg (sa16r_ell d (m + 1 + 1) p (sa16so_cc_div hbo hψ) y)]
        simpa [abs_neg] using abs_add_le (-sa16r_ell d (m + 1 + 1) p (sa16so_cc_div hbo hψ) y)
          (-sa16r_ell d m p hψ (T0 (sa16sz_iota2 d m p y)))
    _ ≤ _ := (add_le_add hA hBn).trans (le_of_eq (by ring))

end L3

end HRS.Whole.AppendixA.Phase2SA16R
