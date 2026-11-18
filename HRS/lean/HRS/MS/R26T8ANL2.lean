import HRS.MS.R26T8ANL1
import HRS.MS.R26T8AP10a13

/-!
# S8.2 T8A NL2: the pointwise nonlocal field

`r26t8a_nonlocal_pointwise`: for every `G ∈ Conormal 2 1 M (σ_c - 2) A` (`σ_c = criticalS d`) and every thermal `ρ`,
`|pairJ G x y| ≤ C A pairWeight (M+2) x y (1 + smallRadius x y ^ (-σ_c))`, `x ≠ y`, `C` depending only on `d, a, β, M`.
This is the `nonlocal` pointwise field of `PairCorrector` (for `G = Q0 + Ψ`, via `r26t8a_conormal_add`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_nl_log_bound {s : ℝ} (hs : 0 < s) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    (1 + |Real.log r|) ^ 2 ≤ max 2 (4 / s ^ 2) * r ^ (-s) := by
  set t : ℝ := -Real.log r with ht
  have ht0 : 0 ≤ t := by rw [ht]; have := Real.log_nonpos hr.le hr1; linarith
  have habs : |Real.log r| = t := abs_of_nonpos (Real.log_nonpos hr.le hr1)
  have hrs : r ^ (-s) = Real.exp (s * t) := by
    rw [Real.rpow_def_of_pos hr, ht]; congr 1; ring
  rw [habs, hrs]
  have hq := Real.quadratic_le_exp_of_nonneg (mul_nonneg hs.le ht0)
  have hK1 : (2 : ℝ) ≤ max 2 (4 / s ^ 2) := le_max_left _ _
  have hK2 : 4 / s ^ 2 ≤ max 2 (4 / s ^ 2) := le_max_right _ _
  have hs2 : 0 < s ^ 2 := by positivity
  have hE : 0 ≤ Real.exp (s * t) := (Real.exp_pos _).le
  have h4 : 4 / s ^ 2 * (s ^ 2 * t ^ 2 / 2) = 2 * t ^ 2 := by field_simp; ring
  have h5 : (1 + t) ^ 2 ≤ 2 + 2 * t ^ 2 := by nlinarith [sq_nonneg (1 - t)]
  have h6 : 2 + 2 * t ^ 2 ≤ max 2 (4 / s ^ 2) * (1 + (s * t) + (s * t) ^ 2 / 2) := by
    have h7 : 2 * 1 ≤ max 2 (4 / s ^ 2) * 1 := by linarith
    have h8 : 4 / s ^ 2 * ((s * t) ^ 2 / 2) ≤ max 2 (4 / s ^ 2) * ((s * t) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right hK2 (by positivity)
    have h9 : 0 ≤ max 2 (4 / s ^ 2) * (s * t) := mul_nonneg (by linarith) (mul_nonneg hs.le ht0)
    have : (s * t) ^ 2 / 2 = s ^ 2 * t ^ 2 / 2 := by ring
    rw [this] at h8 ⊢
    nlinarith
  exact h5.trans (h6.trans (mul_le_mul_of_nonneg_left hq (by linarith)))

end HRS.MS.R26T8A

end
