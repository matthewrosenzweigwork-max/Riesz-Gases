import HRS.MS.R26T8AO02e

/-!
# S8.2 T8A O02 (part f): the three envelope functions are nonnegative and each is dominated by the tame bound
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82U HRS.MS.S82W HRS.MS.Wad

variable {d N : ℕ}

theorem r26t8a_o02_nonneg (M M' : ℝ) (X : EucConfig d N) :
    0 ≤ r26t8a_o02_Wb M X ∧ 0 ≤ r26t8a_o02_Pj M' X ∧ 0 ≤ r26t8a_o02_Tr M' X := by
  refine ⟨?_, ?_, ?_⟩
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => wBq_nonneg M zero_le_one i j X
  · refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg ?_ (sq_nonneg _)
    exact mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (s83_jb_pos _).le _)
  · refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => ?_
    refine mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _)
      (Real.rpow_nonneg (s83_jb_pos _).le _)) (Real.rpow_nonneg (s83_jb_pos _).le _)) ?_
    unfold triplePole
    have := r26t8a_o02_pole_nonneg (X i) (X j); have := r26t8a_o02_pole_nonneg (X i) (X k)
    have := r26t8a_o02_pole_nonneg (X j) (X k)
    positivity

theorem r26t8a_o02_each_le {M M' Cg p q : ℝ} {X : EucConfig d N}
    (hG : |r26t8a_o02_Wb M X + r26t8a_o02_Pj M' X + r26t8a_o02_Tr M' X| ≤ Cg * u4Env p q X) :
    r26t8a_o02_Wb M X ≤ Cg * u4Env p q X ∧ r26t8a_o02_Pj M' X ≤ Cg * u4Env p q X ∧
      r26t8a_o02_Tr M' X ≤ Cg * u4Env p q X := by
  obtain ⟨h1, h2, h3⟩ := r26t8a_o02_nonneg (d := d) (N := N) M M' X
  rw [abs_of_nonneg (by linarith)] at hG
  exact ⟨by linarith, by linarith, by linarith⟩

end HRS.MS.R26T8A
