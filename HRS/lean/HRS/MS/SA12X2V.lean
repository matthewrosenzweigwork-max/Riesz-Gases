import HRS.MS.SA12X2U

/-!
# S.A.12 N8 (SA12X2), part V: one term `∫ ω² u T_i(∂^σ[(∂_l a) ∂_j ∂^t F])` of the telescoped remainder

`∂^σ[c K] = c ∂_j Z + L` with `Z = ∂^σ ∂^t F`; the first part is `sa12x2_N4term`, the second `sa12x2_Lterm`.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

theorem sa12x2_first_add {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i : Fin d) {f1 f2 : Euc d → ℝ}
    (h1 : ContDiff ℝ 1 f1) (h1c : HasCompactSupport f1) (h2 : ContDiff ℝ 1 f2)
    (h2c : HasCompactSupport f2) (x : Euc d) :
    firstRiesz d s i (fun y => f1 y + f2 y) x = firstRiesz d s i f1 x + firstRiesz d s i f2 x := by
  have h := sa12z3_firstRiesz_lin hs0 hsd i h1 h1c (v2 := fun _ => 0) contDiff_const
    (HasCompactSupport.zero) h2 h2c x
  have h0 : firstRiesz d s i (fun _ => (0 : ℝ)) x = 0 := by simp [firstRiesz]
  simpa [h0] using h

theorem sa12x2_lip_D1 {a : Euc d → ℝ} (ha : ContDiff ℝ 2 a) {Ka : ℝ} (hKa : 0 ≤ Ka)
    (hb : ∀ x, ‖fderiv ℝ (fderiv ℝ a) x‖ ≤ Ka) (l : Fin d) (x y : Euc d) :
    |D1 l a x - D1 l a y| ≤ Ka * ‖x - y‖ := by
  have hc : ContDiff ℝ 1 (D1 l a) := D1_contDiff ha l
  have hl : LipschitzWith (Real.toNNReal Ka) (D1 l a) :=
    lipschitzWith_of_nnnorm_fderiv_le (hc.differentiable one_ne_zero) (fun z => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hKa]
      exact (sa12z3_fderiv_D1_le ha l z).trans (hb z))
  have := hl.dist_le_mul x y
  rwa [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hKa] at this

end HRS.MH.AdjointRd.Phase2SA12Near
