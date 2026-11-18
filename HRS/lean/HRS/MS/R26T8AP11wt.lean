import HRS.MS.R26T8AP11s

/-!
# S8.2 nonlocal layer: centre weight versus pair weight (P11e, part 4)
For `|z| <= 2`: `jb(X)^(2M) <= 3^(2M) * pairWeight M (X + z/2) (X - z/2)`.
-/

set_option autoImplicit false
noncomputable section

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_jb_le_pairWeight {d : ℕ} {M : ℝ} (hM : 0 ≤ M) (X z : Euc d) (hz : ‖z‖ ≤ 2) :
    jbracket X ^ (2 * M) ≤ 3 ^ (2 * M) * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := by
  have hn : ‖(-(1 / 2 : ℝ)) • z‖ ≤ 1 := by
    rw [norm_smul]; simp; linarith
  have hn' : ‖(1 / 2 : ℝ) • z‖ ≤ 1 := by
    rw [norm_smul]; simp; linarith
  have h1 : jbracket X ≤ 3 * jbracket (X + (1 / 2 : ℝ) • z) := by
    have e : X = (X + (1 / 2 : ℝ) • z) + (-(1 / 2 : ℝ)) • z := by module
    have := r26t8a_jb_shift' (X + (1 / 2 : ℝ) • z) ((-(1 / 2 : ℝ)) • z)
    rw [← e] at this
    nlinarith [s83_jb_pos (X + (1 / 2 : ℝ) • z)]
  have h2 : jbracket X ≤ 3 * jbracket (X - (1 / 2 : ℝ) • z) := by
    have e : X = (X - (1 / 2 : ℝ) • z) + (1 / 2 : ℝ) • z := by module
    have := r26t8a_jb_shift' (X - (1 / 2 : ℝ) • z) ((1 / 2 : ℝ) • z)
    rw [← e] at this
    nlinarith [s83_jb_pos (X - (1 / 2 : ℝ) • z)]
  have hp1 : jbracket X ^ M ≤ (3 * jbracket (X + (1 / 2 : ℝ) • z)) ^ M :=
    Real.rpow_le_rpow (s83_jb_pos X).le h1 hM
  have hp2 : jbracket X ^ M ≤ (3 * jbracket (X - (1 / 2 : ℝ) • z)) ^ M :=
    Real.rpow_le_rpow (s83_jb_pos X).le h2 hM
  have e2 : jbracket X ^ (2 * M) = jbracket X ^ M * jbracket X ^ M := by
    rw [two_mul, Real.rpow_add (s83_jb_pos X)]
  have e3 : (3 : ℝ) ^ (2 * M) = 3 ^ M * 3 ^ M := by rw [two_mul, Real.rpow_add (by norm_num)]
  rw [e2, e3]
  unfold pairWeight
  rw [Real.mul_rpow (by norm_num) (s83_jb_pos _).le] at hp1 hp2
  calc jbracket X ^ M * jbracket X ^ M ≤ (3 ^ M * jbracket (X + (1 / 2 : ℝ) • z) ^ M) *
        (3 ^ M * jbracket (X - (1 / 2 : ℝ) • z) ^ M) :=
        mul_le_mul hp1 hp2 (Real.rpow_nonneg (s83_jb_pos X).le _) (by
          have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) M
          have := Real.rpow_nonneg (s83_jb_pos (X + (1 / 2 : ℝ) • z)).le M
          positivity)
    _ = 3 ^ M * 3 ^ M * (jbracket (X + (1 / 2 : ℝ) • z) ^ M * jbracket (X - (1 / 2 : ℝ) • z) ^ M) := by ring

end HRS.MS.R26T8A
