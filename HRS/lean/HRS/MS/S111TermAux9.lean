import HRS.MS.S111TermAux8

/-!
# S11.1 terminal wave, B07: uniform projected tensor bounds pass to an existing projective tensor
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology

namespace HRS.MS.S111T

open HRS HRS.Sec7 HRS.Whole

/-- **B07.** If `|κ(M∘(P_n,…,P_n))| ≤ A` for all contractive forms `M` and all `n`, then `‖κ‖ ≤ A`
(`κ` already a projective tensor, `P_n → id` strongly, `‖P_n‖ ≤ 1`). -/
theorem s111t_tensor_bound_of_projections {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (j : ℕ) (P : ℕ → B →L[ℝ] B) (hP : ∀ n, ‖P n‖ ≤ 1)
    (hlim : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x))
    (K : projTensor B j) (A : ℝ) (hA : 0 ≤ A)
    (hbd : ∀ n, ∀ M : B [×j]→L[ℝ] ℝ, ‖M‖ ≤ 1 →
      |(K : TensorDual B j) (M.compContinuousLinearMap fun _ => P n)| ≤ A) :
    ‖K‖ ≤ A := by
  have hT := q17_tensorPow_tendsto P hP hlim j (K : TensorDual B j) K.2
  have hunit : ∀ M : B [×j]→L[ℝ] ℝ, ‖M‖ ≤ 1 → |(K : TensorDual B j) M| ≤ A := by
    intro M hM
    have h1 : Tendsto (fun n => (K : TensorDual B j) (M.compContinuousLinearMap fun _ => P n)) atTop
        (𝓝 ((K : TensorDual B j) M)) :=
      ((ContinuousLinearMap.apply ℝ ℝ M).continuous.continuousAt.tendsto.comp hT)
    exact le_of_tendsto (h1.abs) (Eventually.of_forall fun n => hbd n M hM)
  have : ‖(K : TensorDual B j)‖ ≤ A := by
    refine ContinuousLinearMap.opNorm_le_bound _ hA fun M => ?_
    by_cases hM : M = 0
    · simp [hM]
    · have hpos : 0 < ‖M‖ := norm_pos_iff.2 hM
      have hn : ‖‖M‖⁻¹ • M‖ ≤ 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']
      have h := hunit _ hn
      rw [map_smul, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.2 hpos)] at h
      rw [Real.norm_eq_abs]
      have := mul_le_mul_of_nonneg_left h hpos.le
      rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at this
      linarith [mul_comm A ‖M‖]
  exact this

end HRS.MS.S111T
