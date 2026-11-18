import HRS.MS.R2SeAux8
import HRS.MS.S21F_S00

/-!
# S21F, packet R26-T3.S26a (part T): a smooth bounded scalar cutoff equal to the identity on `[-1,1]`

`θ(t) = ∫_0^t b` for a smooth bump `b` (`b = 1` on `[-1,1]`, compact support): `θ' = b`, `θ = id` on `[-1,1]`, `θ` bounded,
and the derivatives `D^k b`, `k ≤ 2`, are bounded.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T3

theorem s21f_theta :
    ∃ θ b : ℝ → ℝ, ContDiff ℝ ∞ b ∧ (∀ t, HasDerivAt θ (b t) t) ∧ (∀ t ∈ Icc (-1 : ℝ) 1, θ t = t) ∧
      (∃ B : ℝ, ∀ t, |θ t| ≤ B) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, k ≤ 2 → ∀ t, ‖iteratedFDeriv ℝ k b t‖ ≤ C := by
  let bump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hb : ContDiff ℝ ∞ (bump : ℝ → ℝ) := bump.contDiff
  have hcs : HasCompactSupport (bump : ℝ → ℝ) := bump.hasCompactSupport
  have hint : Integrable (bump : ℝ → ℝ) := bump.continuous.integrable_of_hasCompactSupport hcs
  let θ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, bump s
  refine ⟨θ, bump, hb, fun t => (bump.continuous.integral_hasStrictDerivAt 0 t).hasDerivAt, ?_, ?_, ?_⟩
  · intro t ht
    show ∫ s in (0 : ℝ)..t, bump s = t
    have : ∫ s in (0 : ℝ)..t, bump s = ∫ s in (0 : ℝ)..t, (1 : ℝ) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      refine bump.one_of_mem_closedBall ?_
      have : s ∈ uIcc (0 : ℝ) t := hs
      rw [mem_closedBall, Real.dist_eq, sub_zero]
      rcases le_total 0 t with h0 | h0
      · rw [uIcc_of_le h0] at this; rw [abs_of_nonneg this.1]; linarith [this.2, ht.2]
      · rw [uIcc_of_ge h0] at this; rw [abs_of_nonpos this.2]; linarith [this.1, ht.1]
    rw [this]; simp
  · refine ⟨∫ s, bump s, fun t => ?_⟩
    show |∫ s in (0 : ℝ)..t, bump s| ≤ _
    have hnn : ∀ s, 0 ≤ bump s := fun s => bump.nonneg
    rcases le_total 0 t with h0 | h0
    · rw [intervalIntegral.integral_of_le h0, abs_of_nonneg (setIntegral_nonneg measurableSet_Ioc fun s _ => hnn s)]
      exact setIntegral_le_integral hint (Eventually.of_forall hnn)
    · rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le h0, abs_neg,
        abs_of_nonneg (setIntegral_nonneg measurableSet_Ioc fun s _ => hnn s)]
      exact setIntegral_le_integral hint (Eventually.of_forall hnn)
  · obtain ⟨C, hC0, hC⟩ := hcs.exists_bound_iteratedFDeriv hb 2
    exact ⟨C, hC0, fun k hk t => hC k hk t⟩

end HRS.MS.R26T3
