import HRS.MS.SA12K20

/-!
# S.A.12 L8: assembly modulo the nonlocal periodic term

`sa12k_L8_of_nonlocal`: `weak_operator_convergence` follows from (N1) the uniform pointwise decay of the boxed nonlocal
term `1_{centeredBox} nonlocalTestPer` and (N2) its locally uniform convergence to `nonlocalTestRd`.  The drift and
Laplace terms are handled here (`PerApprox` for the drift, differentiability of the limit drift, compact support).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd HRS.MS.ToriCoefA

variable {d : ℕ}

theorem sa12k_movDiv_diff {ψ : Euc d → ℝ} {b₁ b₂ : Euc d → Euc d} {x : Euc d}
    (hψ : DifferentiableAt ℝ ψ x) (h₁ : DifferentiableAt ℝ b₁ x) (h₂ : DifferentiableAt ℝ b₂ x) :
    |movDiv (fun y => ψ y • b₁ y) x - movDiv (fun y => ψ y • b₂ y) x| ≤
      d * (‖fderiv ℝ ψ x‖ * ‖b₁ x - b₂ x‖ + |ψ x| * ‖fderiv ℝ b₁ x - fderiv ℝ b₂ x‖) := by
  have hsub : movDiv (fun y => ψ y • b₁ y) x - movDiv (fun y => ψ y • b₂ y) x =
      movDiv (fun y => ψ y • (b₁ y - b₂ y)) x := by
    unfold movDiv
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (fun y => ψ y • (b₁ y - b₂ y)) =
        (fun y => ψ y • b₁ y - ψ y • b₂ y) := by
      funext y; simp [smul_sub]
    have d1 : DifferentiableAt ℝ (fun y => ψ y • b₁ y) x := hψ.smul h₁
    have d2 : DifferentiableAt ℝ (fun y => ψ y • b₂ y) x := hψ.smul h₂
    have hs : HasFDerivAt (fun y => ψ y • b₁ y - ψ y • b₂ y)
        (fderiv ℝ (fun y => ψ y • b₁ y) x - fderiv ℝ (fun y => ψ y • b₂ y) x) x :=
      d1.hasFDerivAt.sub d2.hasFDerivAt
    rw [e, hs.fderiv]
    simp
  rw [hsub]
  have := sa12k_movDiv_le hψ (h₁.sub h₂)
  rw [fderiv_sub h₁ h₂] at this
  simpa using this

/-- Pointwise decay of `ν Δψ - div(ψ b)` for a drift with linear growth and bounded derivative; the constant
depends only on `ψ`, `Nν`, `Cb`. -/
theorem sa12k_loc_decay {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) (Nν Cb : ℝ) (hN : 0 ≤ Nν)
    (hC : 0 ≤ Cb) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ {ν : ℝ}, |ν| ≤ Nν → ∀ {b : Euc d → Euc d}, ContDiff ℝ 1 b →
      (∀ x, ‖b x‖ ≤ Cb * (1 + ‖x‖)) → (∀ x, ‖fderiv ℝ b x‖ ≤ Cb) → ∀ x,
      |ν * Laplacian.laplacian ψ x - movDiv (fun y => ψ y • b y) x| ≤
        c * jbracket x ^ (-((d : ℝ) + 3)) := by
  obtain ⟨R, A, hR, hA, hjet, hvan⟩ := sa12k_psi_data hψ
  have hψ2 : ContDiff ℝ 2 ψ := hψ.1.of_le (by simp)
  have hψd : ∀ x, DifferentiableAt ℝ ψ x := fun x => (hψ2.differentiable (by norm_num)) x
  set B : ℝ := Nν * d * A + d * (A * (Cb * (1 + R)) + A * Cb) with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  refine ⟨B * (1 + R) ^ ((d : ℝ) + 3), by positivity, fun {ν} hν {b} hb hbg hbd x => ?_⟩
  have hbdiff : ∀ x, DifferentiableAt ℝ b x := fun x => (hb.differentiable (by norm_num)) x
  refine sa12k_cs_decay (g := fun x => ν * Laplacian.laplacian ψ x - movDiv (fun y => ψ y • b y) x)
    (R := R) (B := B) (by linarith) hB0 (fun x hx => ?_) (fun x hx => ?_) x
  · have hl := sa12k_lap_le hψ2 x
    have hm := sa12k_movDiv_le (hψd x) (hbdiff x)
    have e1 : ‖fderiv ℝ ψ x‖ ≤ A := by
      have := hjet 1 (by norm_num) x; rwa [norm_iteratedFDeriv_one] at this
    have e0 : |ψ x| ≤ A := by
      have := hjet 0 (by norm_num) x; rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    have e2 := hjet 2 le_rfl x
    have hbx : ‖b x‖ ≤ Cb * (1 + R) :=
      (hbg x).trans (mul_le_mul_of_nonneg_left (by linarith) hC)
    refine (abs_sub _ _).trans ?_
    have t1 : |ν * Laplacian.laplacian ψ x| ≤ Nν * (d * A) := by
      rw [abs_mul]
      exact mul_le_mul hν (hl.trans (mul_le_mul_of_nonneg_left e2 (Nat.cast_nonneg d))) (abs_nonneg _) hN
    have t2 : |movDiv (fun y => ψ y • b y) x| ≤ d * (A * (Cb * (1 + R)) + A * Cb) := by
      refine hm.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg d))
      exact add_le_add (mul_le_mul e1 hbx (norm_nonneg _) hA)
        (mul_le_mul e0 (hbd x) (norm_nonneg _) hA)
    rw [hBdef]; linarith
  · have hl := sa12k_lap_le hψ2 x
    have hm := sa12k_movDiv_le (hψd x) (hbdiff x)
    have z2 := hvan 2 x hx
    have z1 := hvan 1 x hx
    have z0 := hvan 0 x hx
    have e1 : fderiv ℝ ψ x = 0 := by
      have h := norm_iteratedFDeriv_one (𝕜 := ℝ) (f := ψ) (x := x)
      rw [z1, norm_zero] at h
      exact norm_eq_zero.1 h.symm
    have e0 : ψ x = 0 := by
      have h := norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := ψ) (x := x)
      rw [z0, norm_zero] at h
      exact norm_eq_zero.1 h.symm
    rw [z2, norm_zero, mul_zero] at hl
    rw [e1, e0] at hm
    simp only [norm_zero, zero_mul, abs_zero, mul_zero, add_zero] at hm
    have hl0 : Laplacian.laplacian ψ x = 0 := abs_nonpos_iff.1 hl
    have hm0 : movDiv (fun y => ψ y • b y) x = 0 := abs_nonpos_iff.1 hm
    rw [hl0, hm0]; simp

end HRS.MH.AdjointRd.Phase2SA12Limit
