import HRS.Whole.Q34Aux15

/-!
# Packet Q34, helper file 16: centering projection on `L²(ν)`
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric InnerProductSpace
open scoped ENNReal NNReal

namespace HRS.Whole.Q34

variable {d : ℕ}

section Proj

variable {ν : Measure (Euc d)} [IsProbabilityMeasure ν]

/-- The constant function `1` in `L²(ν)`. -/
def one2 (ν : Measure (Euc d)) [IsProbabilityMeasure ν] : Lp ℝ 2 ν := Lp.const 2 ν (1 : ℝ)

theorem one2_ae : (one2 ν : Euc d → ℝ) =ᵐ[ν] fun _ => 1 := Lp.coeFn_const 2 ν 1

theorem inner_one2 (U : Lp ℝ 2 ν) : inner ℝ (one2 ν) U = ∫ x, U x ∂ν := by
  rw [lp_inner]
  refine integral_congr_ae ?_
  filter_upwards [one2_ae (ν := ν)] with x hx
  rw [hx, one_mul]

theorem inner_one2_one2 : inner ℝ (one2 ν) (one2 ν) = 1 := by
  rw [inner_one2]
  have : ∫ x, (one2 ν : Euc d → ℝ) x ∂ν = ∫ _x, (1 : ℝ) ∂ν :=
    integral_congr_ae one2_ae
  rw [this]
  simp

/-- The centering projection `P u = u - ⟨1,u⟩ 1`. -/
def Pc (ν : Measure (Euc d)) [IsProbabilityMeasure ν] : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  ContinuousLinearMap.id ℝ _ - (innerSL ℝ (one2 ν)).smulRight (one2 ν)

theorem Pc_apply (U : Lp ℝ 2 ν) : Pc ν U = U - inner ℝ (one2 ν) U • one2 ν := by
  simp [Pc]

theorem Pc_one : Pc ν (one2 ν) = 0 := by
  rw [Pc_apply, inner_one2_one2]; simp

theorem inner_Pc_left (U V : Lp ℝ 2 ν) :
    inner ℝ (Pc ν U) V = inner ℝ U V - inner ℝ (one2 ν) U * inner ℝ (one2 ν) V := by
  rw [Pc_apply, inner_sub_left, real_inner_smul_left]

theorem inner_Pc_right (U V : Lp ℝ 2 ν) :
    inner ℝ U (Pc ν V) = inner ℝ U V - inner ℝ (one2 ν) V * inner ℝ U (one2 ν) := by
  rw [Pc_apply, inner_sub_right, real_inner_smul_right]

theorem Pc_symm (U V : Lp ℝ 2 ν) : inner ℝ (Pc ν U) V = inner ℝ U (Pc ν V) := by
  rw [inner_Pc_left, inner_Pc_right, real_inner_comm (one2 ν) U]
  ring

theorem inner_one2_Pc (U : Lp ℝ 2 ν) : inner ℝ (one2 ν) (Pc ν U) = 0 := by
  rw [← Pc_symm, Pc_one]; simp

theorem Pc_idem (U : Lp ℝ 2 ν) : Pc ν (Pc ν U) = Pc ν U := by
  rw [Pc_apply (Pc ν U), inner_one2_Pc]; simp

theorem Pc_norm_le (U : Lp ℝ 2 ν) : ‖Pc ν U‖ ≤ ‖U‖ := by
  have h1 : ‖Pc ν U‖ ^ 2 = ‖U‖ ^ 2 - inner ℝ (one2 ν) U ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, Pc_symm, Pc_idem,
      inner_Pc_right, real_inner_comm (one2 ν) U]
    ring
  have : ‖Pc ν U‖ ^ 2 ≤ ‖U‖ ^ 2 := by rw [h1]; nlinarith [sq_nonneg (inner ℝ (one2 ν) U)]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this

end Proj

end HRS.Whole.Q34
