import HRS.MS.R26T6CI09Coord
import HRS.MS.CovMeasAux1

/-!
# I09: exact norm identity for the finite coordinate projection into ℓ²
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.Whole HRS.MS.CovMeas
variable {d : ℕ}

theorem r26t6c_finite_ellVec_norm_sq (m : ℝ)
    (s : Finset (MultiIndex d)) (c : MultiIndex d → ℝ) :
    ‖ellVec (d := d) m (fun i => if i ∈ s then c i else 0)‖ ^ 2 =
      ∑ i ∈ s, c i ^ 2 := by
  classical
  have hsumm : Summable (fun i => (if i ∈ s then c i else 0) ^ 2) := by
    apply summable_of_finite_support
    have hsup : Function.support
        (fun i => (if i ∈ s then c i else 0) ^ 2) ⊆ (s : Set (MultiIndex d)) := by
      intro i hi
      by_contra h
      have his : i ∉ s := h
      have hz : (if i ∈ s then c i else 0) ^ 2 = 0 := by simp [his]
      exact hi hz
    exact (Finset.finite_toSet s).subset hsup
  have hm : Memℓp (fun i => if i ∈ s then c i else 0) 2 := by
    rw [memℓp_two_iff]
    exact hsumm
  rw [s101_norm_ellVec_sq hm]
  rw [tsum_eq_sum (s := s) (fun i hi => by simp [hi])]
  apply Finset.sum_congr rfl
  intro i hi
  simp [hi]

end HRS.MS.R26T6C
