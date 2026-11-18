import HRS.MS.Fp81S21WickApprox

/-! Squared error for bounded operators on kernel L² classes. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory

namespace HRS.Fp81.S21

/-- A bounded kernel operator transfers an L² kernel-class error to a genuine
squared-error bound for its output representatives. -/
theorem fp81s21_operator_sqerr
    {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (μ : Measure X) (P : Measure Ω)
    (W : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P)
    (x y : Lp ℝ 2 μ) (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hW : ‖W‖ ≤ C) (hxy : ‖x - y‖ ≤ ε) :
    fp81s21_SqErr P (fun ω => W x ω) (fun ω => W y ω) (C * ε) := by
  let z : Lp ℝ 2 P := W x - W y
  have hz : MemLp (fun ω => W x ω - W y ω) 2 P :=
    (Lp.memLp z).ae_eq (Lp.coeFn_sub (W x) (W y))
  have hnorm : ‖z‖ ≤ C * ε := by
    calc
      ‖z‖ = ‖W (x - y)‖ := by simp [z]
      _ ≤ ‖W‖ * ‖x - y‖ := W.le_opNorm _
      _ ≤ C * ε := mul_le_mul hW hxy (norm_nonneg _) hC
  have heq : ‖z‖ ^ 2 = ∫ ω, ‖W x ω - W y ω‖ ^ 2 ∂P := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (W x) (W y)] with ω hω
    change z ω * z ω = _
    rw [show z ω = W x ω - W y ω from hω]
    simp [Real.norm_eq_abs, sq_abs, pow_two]
  refine ⟨hz.norm.integrable_sq, ?_⟩
  rw [← heq]
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

#print axioms fp81s21_operator_sqerr
end HRS.Fp81.S21
end
