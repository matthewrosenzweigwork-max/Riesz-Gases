import HRS.MS.SpecAux17

/-!
# S8P: the operator `Q` on `L²(dx)` (S8.7, packet E1)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_Q : Lp ℝ 2 volume →L[ℝ] Lp ℝ 2 volume` with
`⟨Q v, w⟩ = ∬ g(x-y) √ρ(x) v(x) √ρ(y) w(y)`; symmetric and `⟨Q v, v⟩ ≥ 0`.  In the variables `v = √ρ f` this is
`v ↦ √ρ · g*(√ρ v)`, i.e. `K_μ` before centering.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal RealInnerProductSpace

namespace HRS.MS.Spec

open HRS HRS.Whole

variable {d : ℕ}

/-- The bilinear form as a linear map. -/
def s8p_qlin {ρ : Euc d → ℝ} {s M : ℝ} (h : S8pRho d s ρ M) :
    Lp ℝ 2 (volume : Measure (Euc d)) →ₗ[ℝ] Lp ℝ 2 (volume : Measure (Euc d)) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (s8p_qf s ρ) (s8p_qf_add_left h) (s8p_qf_smul_left h) (s8p_qf_add_right h)
    (s8p_qf_smul_right h)

theorem s8p_qlin_bound {ρ : Euc d → ℝ} {s M : ℝ} (h : S8pRho d s ρ M)
    (v w : Lp ℝ 2 (volume : Measure (Euc d))) :
    ‖s8p_qlin h v w‖ ≤ (2 * s8p_C1 d s M) * ‖v‖ * ‖w‖ := by
  have hC : 0 ≤ s8p_C1 d s M := ENNReal.toReal_nonneg
  by_cases hv : v = 0
  · have : s8p_qlin h v w = 0 := by
      rw [hv]; simp
    rw [this]; simp [hv]
  by_cases hw : w = 0
  · have : s8p_qlin h v w = 0 := by
      rw [hw]; simp
    rw [this]; simp [hw]
  have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw
  set a : ℝ := Real.sqrt (‖w‖ / ‖v‖) with ha
  have ha0 : 0 < a := Real.sqrt_pos.2 (div_pos hwn hvn)
  have ha2 : a ^ 2 = ‖w‖ / ‖v‖ := Real.sq_sqrt (div_pos hwn hvn).le
  have hq : s8p_qlin h v w = s8p_qf s ρ (a • v) (a⁻¹ • w) := by
    show s8p_qf s ρ v w = _
    rw [s8p_qf_smul_left h, s8p_qf_smul_right h, ← mul_assoc, mul_inv_cancel₀ ha0.ne', one_mul]
  rw [hq, Real.norm_eq_abs]
  refine (s8p_qf_abs_le h _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ha0,
    abs_of_pos (inv_pos.2 ha0)]
  have e1 : (a * ‖v‖) ^ 2 = ‖w‖ * ‖v‖ := by
    rw [mul_pow, ha2]; field_simp
  have e2 : (a⁻¹ * ‖w‖) ^ 2 = ‖w‖ * ‖v‖ := by
    rw [mul_pow, inv_pow, ha2]; field_simp
  rw [e1, e2]; nlinarith

/-- The continuous bilinear form. -/
def s8p_qB {ρ : Euc d → ℝ} {s M : ℝ} (h : S8pRho d s ρ M) :
    Lp ℝ 2 (volume : Measure (Euc d)) →L[ℝ] Lp ℝ 2 (volume : Measure (Euc d)) →L[ℝ] ℝ :=
  (s8p_qlin h).mkContinuous₂ (2 * s8p_C1 d s M) (s8p_qlin_bound h)

/-- The operator `Q`. -/
def s8p_Q {ρ : Euc d → ℝ} {s M : ℝ} (h : S8pRho d s ρ M) :
    Lp ℝ 2 (volume : Measure (Euc d)) →L[ℝ] Lp ℝ 2 (volume : Measure (Euc d)) :=
  InnerProductSpace.continuousLinearMapOfBilin (s8p_qB h)

theorem s8p_Q_inner {ρ : Euc d → ℝ} {s M : ℝ} (h : S8pRho d s ρ M)
    (v w : Lp ℝ 2 (volume : Measure (Euc d))) : ⟪s8p_Q h v, w⟫ = s8p_qf s ρ v w :=
  InnerProductSpace.continuousLinearMapOfBilin_apply (s8p_qB h) v w

theorem s8p_Q_symm {ρ : Euc d → ℝ} {s M : ℝ} (h : S8pRho d s ρ M)
    (v w : Lp ℝ 2 (volume : Measure (Euc d))) : ⟪s8p_Q h v, w⟫ = ⟪v, s8p_Q h w⟫ := by
  rw [s8p_Q_inner, real_inner_comm, s8p_Q_inner, s8p_qf_symm h]

theorem s8p_Q_nonneg {ρ : Euc d → ℝ} {s M : ℝ} (h : S8pRho d s ρ M) (hd : 1 ≤ d)
    (v : Lp ℝ 2 (volume : Measure (Euc d))) : 0 ≤ ⟪s8p_Q h v, v⟫ := by
  rw [s8p_Q_inner]; exact s8p_qf_self_nonneg h hd v

end HRS.MS.Spec
