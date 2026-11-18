import HRS.MS.Fp81S21MovingStd2

/-!
# HRS S2.1(iii): assembled moving standard data

The common radius, physical density fields, moving Gram continuity, and moving orbit summability
are assembled into `Fp81MovingStd` at every shifted positive horizon.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3
open HRS.MS.R2WinOrbNL HRS.MS.R2WinErr

/-- One radius yields all `Fp81MovingStd` fields for every admissible moving trajectory and
every shifted horizon `b + p.T`. -/
theorem fp81s21_moving_std (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ (R : Trajectory p δ) (b : ℝ) (hb : 0 ≤ b),
        ∃ c : MultiIndex p.d → ℝ,
          Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) (b + p.T)
            (2 * p.d + 8) c (by linarith [p.hT, hb]) := by
  obtain ⟨δc, Co, co, hδc, hδcHalf, hco, hcommon⟩ := fp81s21_common_radius p
  obtain ⟨δt, Cot, cot, hδt, hδtHalf, hcot, htrajectory⟩ :=
    fp81s21_moving_trajectory_fields p
  let δ0 := min δc δt
  have hδ0 : 0 < δ0 := lt_min hδc hδt
  have hδ0Half : δ0 ≤ 1 / 2 := (min_le_left _ _).trans hδcHalf
  refine ⟨δ0, hδ0, hδ0Half, fun δ hδ hδle R b hb => ?_⟩
  have hδc' : δ ≤ δc := hδle.trans (min_le_left _ _)
  have hδt' : δ ≤ δt := hδle.trans (min_le_right _ _)
  have hδhalf : δ ≤ 1 / 2 := hδc'.trans hδcHalf
  have hpack := hcommon δ hδ hδc' R.ρβ R.thermal
  obtain ⟨hclaims, -, hterm, -⟩ := hpack
  let H : ℝ := b + p.T
  have hH : 0 < H := by dsimp [H]; linarith [p.hT, hb]
  obtain ⟨hν, hint, hnn, hcls, -, -, -, hgauss, -⟩ :=
    htrajectory δ hδ hδt' R H hH
  obtain ⟨c, hD⟩ := fp81s21_moving_s101data_of_common p R hH hclaims hterm
  have hGram := fp81s21_moving_gram_continuous_of_fields p R hδ hδhalf hH hnn hgauss hcls
  refine ⟨c, ?_⟩
  exact ⟨hD, hν, hint, hnn, hcls, hGram⟩

#print axioms fp81s21_moving_std

end HRS.Fp81.S21

end
