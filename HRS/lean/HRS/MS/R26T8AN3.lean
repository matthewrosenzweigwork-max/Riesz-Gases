import HRS.MS.R26T8AN2
import HRS.MS.R26T8AP07s
import HRS.MS.R26T8AP07r

/-!
# S8.2 local Newton layer, smooth part (N), step 3: jets of the raw Newton integral of a smooth pair function
`r26t8a_rawNewton_smooth_jets`: if `P` is `C^k` with `‖nest p q (midPair P) X z‖ <= B pw(X +- z/2)` for all `p + q <= k`, then
`‖nest p q (midPair (rawNewton nu chi P)) X z‖ <= C B pw(X +- z/2)` for all `p + q <= k`, `C` independent of `P, B`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_N3_pw_le {M : ℝ} (hM : 0 ≤ M) (X Y w : Euc d) (hY : ‖Y - X‖ < 1) (hw : ‖w‖ ≤ 2) :
    pairWeight M (Y + (1 / 2 : ℝ) • w) (Y - (1 / 2 : ℝ) • w) ≤ 16 ^ M * jbracket X ^ (2 * M) := by
  have hjX := s83_jb_pos X
  have h1 : jbracket (Y + (1 / 2 : ℝ) • w) ≤ 4 * jbracket X := by
    have e : Y + (1 / 2 : ℝ) • w = X + ((Y - X) + (1 / 2 : ℝ) • w) := by abel
    rw [e]
    refine (r26t8a_jb_shift' X _).trans ?_
    have : ‖(Y - X) + (1 / 2 : ℝ) • w‖ ≤ 2 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul]; simp; linarith
    nlinarith
  have h2 : jbracket (Y - (1 / 2 : ℝ) • w) ≤ 4 * jbracket X := by
    have e : Y - (1 / 2 : ℝ) • w = X + ((Y - X) + (-(1 / 2 : ℝ)) • w) := by module
    rw [e]
    refine (r26t8a_jb_shift' X _).trans ?_
    have : ‖(Y - X) + (-(1 / 2 : ℝ)) • w‖ ≤ 2 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul]; simp; linarith
    nlinarith
  unfold pairWeight
  calc jbracket (Y + (1 / 2 : ℝ) • w) ^ M * jbracket (Y - (1 / 2 : ℝ) • w) ^ M
      ≤ (4 * jbracket X) ^ M * (4 * jbracket X) ^ M :=
        mul_le_mul (Real.rpow_le_rpow (s83_jb_pos _).le h1 hM) (Real.rpow_le_rpow (s83_jb_pos _).le h2 hM)
          (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (by positivity) _)
    _ = 16 ^ M * jbracket X ^ (2 * M) := by
        calc (4 * jbracket X) ^ M * (4 * jbracket X) ^ M
            = ((4 : ℝ) ^ M * 4 ^ M) * (jbracket X ^ M * jbracket X ^ M) := by
              rw [Real.mul_rpow (by norm_num) hjX.le]; ring
          _ = 16 ^ M * jbracket X ^ (2 * M) := by
              rw [← Real.mul_rpow (by norm_num) (by norm_num), ← Real.rpow_add hjX,
                show M + M = 2 * M by ring]
              norm_num

end HRS.MS.R26T8A
