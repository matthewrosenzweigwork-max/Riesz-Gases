import HRS.MS.S82P2Cent2

/-!
# S8.2 (S82P2): near-diagonal bound of the difference quotient of the corrector
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

/-- Envelope of `Q` near the diagonal. -/
lemma s82p2_Q_near {d : ℕ} (hd : 2 ≤ d) {a beta M A : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A)
    {rho : Euc d → ℝ} {f : Euc d → ℝ} {Q : Euc d → Euc d → ℝ}
    (hQ : PairCorrector a beta rho M A f Q) (x y z : Euc d) {t : ℝ} (ht1 : t ≤ 1 / 8)
    (hy : ‖y - x‖ ≤ t) (hz : ‖z - x‖ < 2 * t) (hyz : y ≠ z) :
    |Q y z| ≤ 2 * A * ((2 * jbracket x) ^ M * (2 * jbracket x) ^ M) *
      (1 + ‖y - z‖ ^ (1 - criticalS d)) := by
  have hjx := HRS.MS.S82N.s82n_jb_one_le x
  have ht0 : 0 ≤ t := le_trans (norm_nonneg _) hy
  have hjy : jbracket y ≤ 2 * jbracket x := by
    have h1 := s82p2_jb_add_le x (y - x)
    rw [add_sub_cancel] at h1
    linarith
  have hjz : jbracket z ≤ 2 * jbracket x := by
    have h1 := s82p2_jb_add_le x (z - x)
    rw [add_sub_cancel] at h1
    linarith
  have hen := s82p2_Q_env hd hA hQ y z hyz
  have hr : smallRadius y z = ‖y - z‖ := by
    unfold smallRadius
    refine min_eq_right ?_
    have : ‖y - z‖ ≤ ‖y - x‖ + ‖x - z‖ := by simpa using norm_sub_le_norm_sub_add_norm_sub y x z
    rw [norm_sub_rev x z] at this
    linarith
  rw [hr] at hen
  refine hen.trans ?_
  have hpw : jbracket y ^ M * jbracket z ^ M ≤ (2 * jbracket x) ^ M * (2 * jbracket x) ^ M :=
    mul_le_mul (Real.rpow_le_rpow (HRS.MS.S82N.s82n_jb_pos y).le hjy hM)
      (Real.rpow_le_rpow (HRS.MS.S82N.s82n_jb_pos z).le hjz hM)
      (s82p2_jb_rpow_nonneg M z) (Real.rpow_nonneg (by linarith) _)
  have hr0 : 0 ≤ ‖y - z‖ ^ (1 - criticalS d) := Real.rpow_nonneg (norm_nonneg _) _
  calc A * (jbracket y ^ M * jbracket z ^ M) * (2 * (1 + ‖y - z‖ ^ (1 - criticalS d)))
      = 2 * (A * (jbracket y ^ M * jbracket z ^ M)) * (1 + ‖y - z‖ ^ (1 - criticalS d)) := by ring
    _ ≤ 2 * A * ((2 * jbracket x) ^ M * (2 * jbracket x) ^ M) * (1 + ‖y - z‖ ^ (1 - criticalS d)) := by
        have : A * (jbracket y ^ M * jbracket z ^ M) ≤ A * ((2 * jbracket x) ^ M * (2 * jbracket x) ^ M) :=
          mul_le_mul_of_nonneg_left hpw hA
        have h2 : 0 ≤ 1 + ‖y - z‖ ^ (1 - criticalS d) := by linarith
        nlinarith

end HRS.MS.S82P2
