import HRS.MC.CepH2Aux23

/-!
# CEPH2, helper 24: comparison of the kernels `Ĝ_v`, `∇Ĝ_v` with `Ĝ_{2v}`

`Ĝ_v ≤ 2^{N/2} Ĝ_{2v}` and `‖∇Ĝ_v‖ ≤ c Ĝ_{2v}` (so that first-order integrals reduce to the Gaussian machinery).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ}

theorem h2_g_two {v : ℝ} (hv : 0 < v) (w : Ch N) :
    h2_g v w = (2 : ℝ) ^ ((N : ℝ) / 2) * Real.exp (-(1 / (4 * v)) * ‖w‖ ^ 2) * h2_g (2 * v) w := by
  unfold h2_g
  have h1 : (2 * Real.pi * (2 * v)) = 2 * (2 * Real.pi * v) := by ring
  have hpos : 0 < 2 * Real.pi * v := by positivity
  rw [h1, Real.mul_rpow (by norm_num) hpos.le]
  have h2 : (2 : ℝ) ^ ((N : ℝ) / 2) * (2 : ℝ) ^ (-(N : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add (by norm_num)]
    have : (N : ℝ) / 2 + -(N : ℝ) / 2 = 0 := by ring
    rw [this]; simp
  have h3 : Real.exp (-(1 / (2 * v)) * ‖w‖ ^ 2) =
      Real.exp (-(1 / (4 * v)) * ‖w‖ ^ 2) * Real.exp (-(1 / (2 * (2 * v))) * ‖w‖ ^ 2) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  rw [h3]
  calc (2 * Real.pi * v) ^ (-(N : ℝ) / 2) * (Real.exp (-(1 / (4 * v)) * ‖w‖ ^ 2) * Real.exp (-(1 / (2 * (2 * v))) * ‖w‖ ^ 2))
      = ((2 : ℝ) ^ ((N : ℝ) / 2) * (2 : ℝ) ^ (-(N : ℝ) / 2)) * ((2 * Real.pi * v) ^ (-(N : ℝ) / 2) *
          (Real.exp (-(1 / (4 * v)) * ‖w‖ ^ 2) * Real.exp (-(1 / (2 * (2 * v))) * ‖w‖ ^ 2))) := by rw [h2, one_mul]
    _ = _ := by ring

theorem h2_g_le_two {v : ℝ} (hv : 0 < v) (w : Ch N) :
    h2_g v w ≤ (2 : ℝ) ^ ((N : ℝ) / 2) * h2_g (2 * v) w := by
  rw [h2_g_two hv w]
  have he : Real.exp (-(1 / (4 * v)) * ‖w‖ ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have : 0 < 1 / (4 * v) := by positivity
    nlinarith [sq_nonneg ‖w‖]
  have hg := h2_g_pos (by positivity : 0 < 2 * v) w
  have ha : 0 ≤ (2 : ℝ) ^ ((N : ℝ) / 2) := by positivity
  calc (2 : ℝ) ^ ((N : ℝ) / 2) * Real.exp (-(1 / (4 * v)) * ‖w‖ ^ 2) * h2_g (2 * v) w
      ≤ (2 : ℝ) ^ ((N : ℝ) / 2) * 1 * h2_g (2 * v) w := by gcongr
    _ = _ := by ring

/-- The constant of the gradient comparison. -/
def h2_c1 (N : ℕ) (v : ℝ) : ℝ := (1 / v) * (2 : ℝ) ^ ((N : ℝ) / 2) * (2 + 2 / (1 / (4 * v)))

theorem h2_c1_nonneg {v : ℝ} (hv : 0 < v) : 0 ≤ h2_c1 N v := by unfold h2_c1; positivity

theorem h2_norm_g1_le_two {v : ℝ} (hv : 0 < v) (w : Ch N) : ‖h2_g1 v w‖ ≤ h2_c1 N v * h2_g (2 * v) w := by
  rw [h2_norm_g1 hv, h2_g_two hv w]
  have hc : 0 < 1 / (4 * v) := by positivity
  have hr := norm_nonneg w
  have h1 := h2_sup_mul_exp hc hr
  have h2 : ‖w‖ * Real.exp (-(1 / (4 * v)) * ‖w‖ ^ 2) ≤ 2 + 2 / (1 / (4 * v)) := by
    refine le_trans ?_ h1
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  have hg := h2_g_pos (by positivity : 0 < 2 * v) w
  have ha : 0 ≤ (2 : ℝ) ^ ((N : ℝ) / 2) := by positivity
  unfold h2_c1
  calc 1 / v * ((2 : ℝ) ^ ((N : ℝ) / 2) * Real.exp (-(1 / (4 * v)) * ‖w‖ ^ 2) * h2_g (2 * v) w) * ‖w‖
      = (1 / v) * (2 : ℝ) ^ ((N : ℝ) / 2) * h2_g (2 * v) w * (‖w‖ * Real.exp (-(1 / (4 * v)) * ‖w‖ ^ 2)) := by ring
    _ ≤ (1 / v) * (2 : ℝ) ^ ((N : ℝ) / 2) * h2_g (2 * v) w * (2 + 2 / (1 / (4 * v))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

section
variable [NeZero N]

theorem h2_per_le_two {v : ℝ} (hv : 0 < v) (w : Ch N) :
    h2_per v w ≤ (2 : ℝ) ^ ((N : ℝ) / 2) * h2_per (2 * v) w := by
  unfold h2_per
  rw [← tsum_mul_left]
  exact (h2_summable_g_trans hv w).tsum_le_tsum (fun m => h2_g_le_two hv _)
    ((h2_summable_g_trans (by positivity : 0 < 2 * v) w).mul_left _)

theorem h2_norm_per1_le_two {v : ℝ} (hv : 0 < v) (w : Ch N) :
    ‖h2_per1 v w‖ ≤ h2_c1 N v * h2_per (2 * v) w := by
  have hs2 := h2_summable_g_trans (by positivity : 0 < 2 * v) w
  have hsn : Summable (fun m : ℤ => ‖h2_g1 v (w + (m : ℝ) • cep_diag N)‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => h2_norm_g1_le_two hv _) (hs2.mul_left _)
  unfold h2_per1 h2_per
  rw [← tsum_mul_left]
  exact (norm_tsum_le_tsum_norm hsn).trans
    (hsn.tsum_le_tsum (fun m => h2_norm_g1_le_two hv _) (hs2.mul_left _))

end

end HRS.MC.CepH2
