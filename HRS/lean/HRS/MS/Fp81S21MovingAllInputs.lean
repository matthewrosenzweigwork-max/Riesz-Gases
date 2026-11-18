import HRS.MS.Fp81S21MovingStd3
import HRS.MS.Fp81S21MovingInputs2

/-!
# HRS S2.1(iii): one common radius for all moving-reference inputs

The moving standing data `Fp81MovingStd` (from `fp81s21_moving_std`), the trajectory-only
physical fields (from `fp81s21_moving_trajectory_fields`), and the particle-dependent fields
(from `fp81s21_moving_particle_fields`) are assembled under a single radius `δ0`, chosen before
the trajectory `R`, the shift `b`, the particle count `N`, and the particle `A`. The radius is the
minimum of the three producer radii, so every producer applies at every `δ ≤ δ0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Whole.AppendixA
open HRS.MS.R26T3 HRS.MS.CovMeas HRS.MS.R2Interp

/-- One radius yields the standing moving data for every shift `b ≥ 0` and, for every
particle configuration, the full physical-input package at horizon `b + p.T`. -/
theorem fp81s21_moving_inputs_all (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ (R : Trajectory p δ) (b : ℝ) (hb : 0 ≤ b),
        ∃ c : MultiIndex p.d → ℝ,
          Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) (b + p.T)
            (2 * p.d + 8) c (by linarith [p.hT, hb]) ∧
          ∀ (N : ℕ) (hN : 2 ≤ N) (A : Particle R N),
            Fp81MovingPhysicalInputs R hN A (b + p.T) := by
  obtain ⟨δs, hδs, hδsHalf, hstd⟩ := fp81s21_moving_std p
  obtain ⟨δt, Cot, cot, hδt, hδtHalf, hcot, htraj⟩ :=
    fp81s21_moving_trajectory_fields p
  obtain ⟨δp, Cop, cop, pinf, Kp, hδp, hδpHalf, hcop, hpinf, hpart⟩ :=
    fp81s21_moving_particle_fields p
  refine ⟨min δs (min δt δp), lt_min hδs (lt_min hδt hδp),
    (min_le_left _ _).trans hδsHalf, fun δ hδ hδle R b hb => ?_⟩
  have hδs' : δ ≤ δs := le_trans hδle (min_le_left _ _)
  have hδt' : δ ≤ δt :=
    le_trans hδle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδp' : δ ≤ δp :=
    le_trans hδle (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨c, hc⟩ := hstd δ hδ hδs' R b hb
  refine ⟨c, hc, ?_⟩
  intro N hN A
  have hH : 0 < b + p.T := by linarith [p.hT, hb]
  obtain ⟨-, -, -, -, hreg, hdens, hround2, hgauss, href⟩ :=
    htraj δ hδ hδt' R (b + p.T) hH
  obtain ⟨hact, hmom⟩ := hpart δ hδ hδp' R N hN A (b + p.T) hH
  exact ⟨hreg, hdens, hround2, hgauss, ⟨pinf, Kp, hpinf, hact⟩, href, hmom⟩

#print axioms fp81s21_moving_inputs_all

end HRS.Fp81.S21

end
