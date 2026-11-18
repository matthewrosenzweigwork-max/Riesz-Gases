import HRS.MH.AdjointRdDefs
import HRS.MS.SA12BuildC12

/-!
# S.A.12 density of `C_c^∞` in `L²` with controlled support, and the `ℓ¹(L²)` cell density (L2)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd

variable {d : ℕ}

/-- Smooth compactly supported approximation in `L²(μ)` of a function vanishing outside `closedBall 0 R`,
with the approximant supported in `closedBall 0 (R+1)`. -/
theorem sa12x_cc_approx {μ : Measure (Euc d)} [IsFiniteMeasureOnCompacts μ] {f : Euc d → ℝ}
    (hf : MemLp f 2 μ) (R : ℝ) (hR : 0 < R) (hf0 : ∀ x, R < ‖x‖ → f x = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Metric.closedBall 0 (R + 1) ∧
      eLpNorm (f - ψ) 2 μ ≤ ENNReal.ofReal ε := by
  obtain ⟨g, hg1, hg2, hg3⟩ := hf.exist_eLpNorm_sub_le (p := 2) (by simp) (by norm_num) hε
  let χ : ContDiffBump (0 : Euc d) := ⟨R, R + 1, hR, by linarith⟩
  refine ⟨fun x => χ x * g x, χ.contDiff.mul hg2, hg1.mul_left, ?_, ?_⟩
  · have h1 : tsupport (fun x => χ x * g x) ⊆ tsupport (χ : Euc d → ℝ) :=
      tsupport_mul_subset_left
    refine h1.trans ?_
    rw [χ.tsupport_eq]
  · refine le_trans (eLpNorm_mono (g := f - g) (hf.aestronglyMeasurable.sub (χ.contDiff.mul hg2).continuous.aestronglyMeasurable) (fun x => ?_)) hg3
    have hfx : f x = χ x * f x := by
      by_cases hx : ‖x‖ ≤ R
      · rw [χ.one_of_mem_closedBall (by simpa [χ] using hx), one_mul]
      · rw [hf0 x (not_le.1 hx)]; simp
    have key : f x - χ x * g x = χ x * (f x - g x) := by
      rw [mul_sub]; nth_rewrite 1 [hfx]; rfl
    simp only [Pi.sub_apply]
    rw [key, norm_mul, Real.norm_of_nonneg χ.nonneg]
    exact mul_le_of_le_one_left (norm_nonneg _) χ.le_one
