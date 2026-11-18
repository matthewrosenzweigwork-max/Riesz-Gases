import HRS.MS.SA16Y3L3

/-!
# S.A.16 (SA16Y3) L4: pointwise bound of `div(b ψ)` from the first-derivative bound and the sup of `b` on `supp ψ` only

`sa16y3_divFun_bound`: if `‖∇ b_i‖ ≤ B` everywhere, `|b_i| ≤ Ab` on `closedBall 0 R0`, `ψ` smooth with `ψ = 0` outside
`closedBall 0 R0`, `|ψ| ≤ Sψ`, `|∂_i ψ| ≤ Sψ'`, then `|div(bψ)| ≤ d (B Sψ + Ab Sψ')` on the ball and `= 0` outside.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section L4
variable {d : ℕ}

lemma sa16y3_divFun_bound {bc : Fin d → Euc d → ℝ} {B Ab R0 Sψ Sψ' : ℝ}
    (hsm : ∀ i, ContDiff ℝ ∞ (bc i)) (hder : ∀ i x, ‖fderiv ℝ (bc i) x‖ ≤ B)
    (hbsup : ∀ i x, ‖x‖ ≤ R0 → |bc i x| ≤ Ab) {ψ : Euc d → ℝ} (hψs : ContDiff ℝ ∞ ψ)
    (hψ0 : ∀ x, R0 < ‖x‖ → ψ x = 0) (hS : ∀ x, |ψ x| ≤ Sψ)
    (hS' : ∀ i x, |fderiv ℝ ψ x (EuclideanSpace.single i 1)| ≤ Sψ') (x : Euc d) :
    |sa16so_divFun bc ψ x| ≤
      ((d : ℝ) * (B * Sψ + Ab * Sψ')) * (closedBall (0 : Euc d) R0).indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : x ∈ closedBall (0 : Euc d) R0
  · rw [Set.indicator_of_mem hx, mul_one]
    have hxn : ‖x‖ ≤ R0 := by simpa using hx
    unfold sa16so_divFun
    have hterm : ∀ i : Fin d, |fderiv ℝ (fun y => bc i y * ψ y) x (EuclideanSpace.single i 1)| ≤
        B * Sψ + Ab * Sψ' := by
      intro i
      have hd1 := ((hsm i).differentiable (by simp)) x
      have hd2 := (hψs.differentiable (by simp)) x
      rw [show (fun y => bc i y * ψ y) = bc i * ψ from rfl, fderiv_mul hd1 hd2]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      have h1 : |fderiv ℝ (bc i) x (EuclideanSpace.single i 1)| ≤ B := by
        have := (fderiv ℝ (bc i) x).le_opNorm (EuclideanSpace.single i 1)
        rw [PiLp.norm_single, norm_one, mul_one] at this
        rw [← Real.norm_eq_abs]
        exact this.trans (hder i x)
      have hA := hbsup i x hxn
      have hA0 : 0 ≤ Ab := (abs_nonneg _).trans hA
      have hSψ0 : 0 ≤ Sψ := (abs_nonneg _).trans (hS x)
      have hB0 : 0 ≤ B := (abs_nonneg _).trans h1
      calc |bc i x * fderiv ℝ ψ x (EuclideanSpace.single i 1) + ψ x * fderiv ℝ (bc i) x (EuclideanSpace.single i 1)|
          ≤ |bc i x * fderiv ℝ ψ x (EuclideanSpace.single i 1)| + |ψ x * fderiv ℝ (bc i) x (EuclideanSpace.single i 1)| :=
            abs_add_le _ _
        _ = |bc i x| * |fderiv ℝ ψ x (EuclideanSpace.single i 1)| + |ψ x| * |fderiv ℝ (bc i) x (EuclideanSpace.single i 1)| := by
            rw [abs_mul, abs_mul]
        _ ≤ Ab * Sψ' + Sψ * B :=
            add_le_add (mul_le_mul hA (hS' i x) (abs_nonneg _) hA0) (mul_le_mul (hS x) h1 (abs_nonneg _) hSψ0)
        _ = B * Sψ + Ab * Sψ' := by ring
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => hterm i).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · rw [Set.indicator_of_notMem hx, mul_zero]
    have hxn : R0 < ‖x‖ := by simpa using hx
    have hz : ∀ i : Fin d, fderiv ℝ (fun y => bc i y * ψ y) x = 0 := by
      intro i
      have hev : (fun y => bc i y * ψ y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        have hn : ∀ᶠ y in 𝓝 x, R0 < ‖y‖ := (isOpen_lt continuous_const continuous_norm).mem_nhds hxn
        filter_upwards [hn] with y hy
        simp [hψ0 y hy]
      rw [hev.fderiv_eq]
      simp
    simp [sa16so_divFun, hz]

end L4

end HRS.Whole.AppendixA.Phase2SA16R
