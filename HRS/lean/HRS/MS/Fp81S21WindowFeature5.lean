import HRS.MS.Fp81S21WindowFeature4

/-!
# HRS S2.1 packet 15c: the S101 derivative coordinate

The common-trajectory terminal derivative theorem identifies `s101Dt` with
the propagated generator input on every nondegenerate physical interval.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.CovMeas HRS.MS.R26T3 HRS.MS.R2WinErr
open HRS.MS.R2WinOrbNL

/-- On a nondegenerate physical horizon, the S101 `derivWithin` coordinate is
exactly propagation of the generator terminal input. -/
theorem fp81s21_window_s101Dt_eq_generator
    (p : Parameters) {δ H a v : ℝ} (R : Trajectory p δ)
    (hH : 0 < H) (ha : 0 ≤ a)
    (hv : v ∈ Icc (0 : ℝ) (a + H)) (hvEnd : v < a + H)
    (hterm : S104bTermRegGen p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁) :
    ∀ t ∈ Icc v (a + H), ∀ α : MultiIndex p.d, ∀ x : Euc p.d,
      s101Dt (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) (a + H) v t α x =
        propagatorW (r26t3_coeff R) v t
          (generatorW (r26t3_coeff R) t
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x := by
  intro t ht α x
  have hphys : 0 < a + H := by linarith
  have hder := fp81s21_moving_terminal_derivative_within p R hphys hterm
    α v hv t ht (by linarith : v < a + H) x
  unfold s101Dt
  exact hder.derivWithin (uniqueDiffOn_Icc hvEnd t ht)

#print axioms fp81s21_window_s101Dt_eq_generator

end HRS.Fp81.S21

end
