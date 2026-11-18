import HRS.Uniform.Q54cAux26

/-!
# Q54c, part 27: `PathData.Spec` of the adjoint propagator
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54c

open HRS HRS.PDE

variable {d : ℕ}

namespace PdeSetup

variable {P : PdeSetup d} {D : DynData d} {ν₀ : ℝ} {μ : ℝ → Torus d → ℝ} (h : P.Data D ν₀ μ)

include h

theorem Data.spec_pd : (P.pd D μ).Spec P.T P.Kc where
  hK := P.Kc_nonneg
  hT := h.hA.hT.le
  lin_y := fun t ht σ hσ φ ψ hφ hψ α β => h.lin_y ht hφ hψ α β hσ
  lin_y' := fun t ht σ hσ φ ψ hφ hψ α β => h.lin_y' ht hφ hψ α β hσ
  lin_w := fun t ht φ ψ hφ hψ α β => h.lin_w ht hφ hψ α β
  const_y := fun t ht σ hσ c => h.const_y ht c hσ
  const_y' := fun t ht σ hσ c => h.const_y' ht c hσ
  const_w := fun t ht c => h.const_w ht c
  bd_y := fun t ht σ hσ φ hφ => h.bd_y ht hφ hσ
  bd_y' := fun t ht σ hσ φ hφ => h.bd_y' ht hφ hσ
  bd_w := fun t ht φ hφ => h.bd_w ht hφ
  deriv := fun t ht φ hφ σ hσ => h.deriv_y ht hφ hσ
  cont_y' := fun t ht φ hφ => h.cont_y' ht hφ
  lip_y := by
    intro t ht t' ht' σ hσ φ hφ
    have hS := sobolevNorm_nonneg' ((P.n : ℝ) + 4) φ
    have hk := P.kb1_le
    rcases le_total t' t with htt | htt
    · rw [min_eq_right htt] at hσ
      refine (h.lip_y_one ht htt ht'.1 hφ hσ).trans ?_
      rw [abs_of_nonneg (by linarith)]
      have : 0 ≤ t - t' := by linarith
      nlinarith [mul_nonneg this hS]
    · rw [min_eq_left htt] at hσ
      rw [norm_sub_rev]
      refine (h.lip_y_one ht' htt ht.1 hφ hσ).trans ?_
      rw [abs_of_nonpos (by linarith)]
      have : 0 ≤ t' - t := by linarith
      nlinarith [mul_nonneg this hS]
  lip_y' := by
    intro t ht t' ht' σ hσ φ hφ
    have hS := sobolevNorm_nonneg' ((P.n : ℝ) + 4) φ
    have hk := P.kb2_le
    rcases le_total t' t with htt | htt
    · rw [min_eq_right htt] at hσ
      refine (h.lip_y'_one ht htt ht'.1 hφ hσ).trans ?_
      rw [abs_of_nonneg (by linarith)]
      have : 0 ≤ t - t' := by linarith
      nlinarith [mul_nonneg this hS]
    · rw [min_eq_left htt] at hσ
      rw [norm_sub_rev]
      refine (h.lip_y'_one ht' htt ht.1 hφ hσ).trans ?_
      rw [abs_of_nonpos (by linarith)]
      have : 0 ≤ t' - t := by linarith
      nlinarith [mul_nonneg this hS]
  lip_w := by
    intro t ht t' ht' φ hφ
    have hS := sobolevNorm_nonneg' ((P.n : ℝ) + 4) φ
    have hk := P.kb3_le
    rcases le_total t' t with htt | htt
    · refine (h.lip_w_one ht htt ht'.1 hφ).trans ?_
      rw [abs_of_nonneg (by linarith)]
      have : 0 ≤ t - t' := by linarith
      nlinarith [mul_nonneg this hS]
    · rw [norm_sub_rev]
      refine (h.lip_w_one ht' htt ht.1 hφ).trans ?_
      rw [abs_of_nonpos (by linarith)]
      have : 0 ≤ t' - t := by linarith
      nlinarith [mul_nonneg this hS]
  w_zero := fun φ hφ z => h.w_zero hφ z

end PdeSetup

end HRS.Uniform.Q54c
