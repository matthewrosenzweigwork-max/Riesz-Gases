import HRS.MS.Fp81S21PathMom
import HRS.MS.Fp81S21MovingInputs2

/-! Physical moving inputs and adjoint/window features under one radius. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.R26T3 HRS.MS.R2GenInit

/-- A common radius supplies the adjoint and physical inputs for arbitrary
positive horizons, as well as the moving window feature membership. -/
theorem fp81s21_path_moving_inputs (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        (∀ T : ℝ, 0 < T →
          OscAdjointInput (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) T ∧
          ∀ (N : ℕ) (hN : 2 ≤ N) (A : Particle R N),
            Fp81MovingPhysicalInputs R hN A T) ∧
        (∀ H : ℝ, 0 < H → ∀ b : ℝ, 0 ≤ b →
          ∀ (a : Fin p.d) (r : ℝ), r ∈ Icc 0 (b + H) → ∀ x,
            S105WinK (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H b a r x) := by
  obtain ⟨δa, hδa, hδah, hadj⟩ := fp81s21_path_moving_adjoint_window p
  obtain ⟨δt, Cot, cot, hδt, hδth, hcot, htraj⟩ :=
    fp81s21_moving_trajectory_fields p
  obtain ⟨δp, Cop, cop, pinf, Kp, hδp, hδph, hcop, hpinf, hpart⟩ :=
    fp81s21_moving_particle_fields p
  refine ⟨min δa (min δt δp), lt_min hδa (lt_min hδt hδp),
    (min_le_left _ _).trans hδah, ?_⟩
  intro δ hδ hδle R
  have hδa' : δ ≤ δa := hδle.trans (min_le_left _ _)
  have hδt' : δ ≤ δt := hδle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδp' : δ ≤ δp := hδle.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hadjR, hwin⟩ := hadj δ hδ hδa' R
  refine ⟨?_, hwin⟩
  intro T hT
  refine ⟨hadjR T hT, ?_⟩
  intro N hN A
  obtain ⟨-, -, -, -, hreg, hdens, hround2, hgauss, href⟩ :=
    htraj δ hδ hδt' R T hT
  obtain ⟨hact, hmom⟩ := hpart δ hδ hδp' R N hN A T hT
  exact ⟨hreg, hdens, hround2, hgauss, ⟨pinf, Kp, hpinf, hact⟩, href, hmom⟩

#print axioms HRS.Fp81.S21.fp81s21_path_moving_inputs

end HRS.Fp81.S21
