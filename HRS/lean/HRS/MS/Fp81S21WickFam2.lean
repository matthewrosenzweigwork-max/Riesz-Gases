import HRS.MS.Fp81S21WickFam
import HRS.MS.ProClosureS111JointLp

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS.Fp81.S21

open HRS.Whole HRS.MS.R26T3

/-- A continuous nonnegative-time L² family has a jointly measurable
representative whose section represents the given class at every such time. -/
theorem fp81s21_wickFam_joint_of_continuous
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (F : ℝ → Lp ℝ 2 P) (hF : ContinuousOn F (Set.Ici 0)) :
    ∃ W : ℝ × Ω → ℝ, Measurable W ∧
      ∀ u, 0 ≤ u → MemLp (fun ω => W (u, ω)) 2 P ∧
        (fun ω => W (u, ω)) =ᵐ[P] (F u : Ω → ℝ) := by
  have hc : Continuous (fun u : ℝ => F (max u 0)) :=
    hF.comp_continuous (continuous_id.max continuous_const)
      (fun u => Set.mem_Ici.mpr (le_max_right u 0))
  obtain ⟨W, hW, hsec⟩ := HRS.MS.ProClosureS111.joint_Lp_representative
    P 2 (by norm_num) (fun u : ℝ => F (max u 0)) hc.stronglyMeasurable
  refine ⟨W, hW.measurable, ?_⟩
  intro u hu
  simpa [max_eq_left hu] using hsec u

#print axioms fp81s21_wickFam_joint_of_continuous

end HRS.Fp81.S21
end
