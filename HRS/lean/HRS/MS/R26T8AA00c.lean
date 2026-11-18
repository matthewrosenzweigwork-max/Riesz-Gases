import HRS.MS.R26T8AA00b
import HRS.MS.S82P2Mom
import HRS.MS.WadAux1

/-!
# S8.2 T8A A00 (part c): segment bound for `jb` and the near-field inequality
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_a00_jb_seg {x z w : Euc d} (hw : w ∈ segment ℝ x z) : jbracket w ≤ jbracket x * jbracket z := by
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hw
  have h1 : ‖α • x + β • z‖ ≤ max ‖x‖ ‖z‖ := by
    calc ‖α • x + β • z‖ ≤ ‖α • x‖ + ‖β • z‖ := norm_add_le _ _
      _ = α * ‖x‖ + β * ‖z‖ := by rw [norm_smul, norm_smul, Real.norm_of_nonneg hα, Real.norm_of_nonneg hβ]
      _ ≤ α * max ‖x‖ ‖z‖ + β * max ‖x‖ ‖z‖ :=
          add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hα) (mul_le_mul_of_nonneg_left (le_max_right _ _) hβ)
      _ = max ‖x‖ ‖z‖ := by rw [← add_mul, hαβ, one_mul]
  have h2 : 1 + ‖α • x + β • z‖ ^ 2 ≤ (1 + ‖x‖ ^ 2) * (1 + ‖z‖ ^ 2) := by
    have hm : ‖α • x + β • z‖ ^ 2 ≤ max ‖x‖ ‖z‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rcases le_total ‖x‖ ‖z‖ with h | h
    · rw [max_eq_right h] at hm
      nlinarith [sq_nonneg ‖x‖, sq_nonneg ‖z‖, mul_nonneg (sq_nonneg ‖x‖) (sq_nonneg ‖z‖)]
    · rw [max_eq_left h] at hm
      nlinarith [sq_nonneg ‖x‖, sq_nonneg ‖z‖, mul_nonneg (sq_nonneg ‖x‖) (sq_nonneg ‖z‖)]
  unfold jbracket
  rw [← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt h2

theorem r26t8a_a00_near {s p ℓ : ℝ} (hs : 1 ≤ s) (hp : 0 < p) (hℓ : p / 3 ≤ ℓ) :
    1 + min 1 p ^ (1 - s) ≤ 6 * ℓ * (1 + min 1 p ^ (-s)) := by
  by_cases h1 : 1 ≤ p
  · rw [min_eq_left h1, Real.one_rpow, Real.one_rpow]
    nlinarith
  · push Not at h1
    rw [min_eq_right h1.le]
    have hp1 : 1 ≤ p ^ (1 - s) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hp h1.le (by linarith)
    have e : p ^ (1 - s) = p * p ^ (-s) := by
      rw [show (1 - s) = 1 + (-s) by ring, Real.rpow_add hp, Real.rpow_one]
    have hnn : 0 ≤ p ^ (-s) := Real.rpow_nonneg hp.le _
    nlinarith [mul_le_mul_of_nonneg_right hℓ hnn]

end HRS.MS.R26T8A
