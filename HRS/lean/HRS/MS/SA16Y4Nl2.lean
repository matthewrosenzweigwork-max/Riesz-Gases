import HRS.MS.SA16Y4Nl1
import HRS.MS.SA16QFin4

/-!
# S.A.16 (SA16Y4) Nl2: mollified densities have weighted derivative bounds up to order `m+3`, uniformly in `n`

`sa16y4_mol_data3`: copy of `sa16q_mol_data` with the conclusion extended from `κ ≤ m+1` to `κ ≤ m+3` (the proof only uses the
regularity `m+3` of the density).  With `sa16y4_G_exists_smooth` this gives the nonlocal operators of the mollified
coefficients at levels `m` and `m+1` with constants independent of `n`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Q

section Nl2
variable {d : ℕ}

lemma sa16y4_mol_data3 (hd1 : 1 ≤ d) {m : ℕ} {Λ : ℝ} {μ : Euc d → ℝ} (hμ : IsRegularDensityW (m + 3) Λ μ)
    (N : ℕ) :
    sa16q_SB (sa16q_mol N μ) ∧
      (∀ κ ≤ m + 3, ∀ x, ‖iteratedFDeriv ℝ κ (sa16q_mol N μ) x‖ ≤
        (d : ℝ) ^ (m + 3) * (2 ^ (d + 3) * (2 ^ (d + 3) * max Λ 0)) * (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ))) := by
  obtain ⟨hC, hbd, hw⟩ := sa16q_reg_data hμ
  have hμc : Continuous μ := hC.continuous
  refine ⟨sa16q_mol_SB N hμc (sa16q_reg_abs hμ), fun κ hκ x => ?_⟩
  have hμκ : ContDiff ℝ κ μ := hC.of_le (by exact_mod_cast hκ)
  have hΛ : 0 ≤ max Λ 0 := le_max_right _ _
  have h1 := sa16q_weight_conv (a := sa16q_mol N μ) (κ := κ) (Λ2 := 2 ^ (d + 3) * (2 ^ (d + 3) * max Λ 0))
    (fun r y => sa16q_mol_pd_weight N hμκ (Λ1 := 2 ^ (d + 3) * max Λ 0)
      (fun r' y' => hw κ (by omega) r' y') r y) x
  refine h1.trans ?_
  have hω : 0 ≤ (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ)) := Real.rpow_nonneg (by positivity) _
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hpw : (d : ℝ) ^ κ ≤ (d : ℝ) ^ (m + 3) := pow_le_pow_right₀ hd0 hκ
  have hc : 0 ≤ 2 ^ (d + 3) * (2 ^ (d + 3) * max Λ 0) := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpw hc) hω

end Nl2

end HRS.Whole.AppendixA.Phase2SA16R
