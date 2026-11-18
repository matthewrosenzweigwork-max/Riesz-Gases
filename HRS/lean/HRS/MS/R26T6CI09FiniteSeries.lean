import HRS.MS.R26T6CI09FiniteLp

/-! I09: the finite single-coordinate series has exact Euclidean L2 norm. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.Whole HRS.MS.CovMeas
variable {d : ℕ}

theorem r26t6c_finite_single_norm_sq (m : ℝ)
    (s : Finset (MultiIndex d)) (c : MultiIndex d → ℝ) :
    ‖(∑ i ∈ s, (lp.single 2 i (c i) : OscDual d m))‖ ^ 2 =
      ∑ i ∈ s, c i ^ 2 := by
  have h := lp.norm_sum_single (p := (2 : ℝ≥0∞))
    (E := fun _ : MultiIndex d => ℝ)
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal) c s
  calc
    _ = ‖(∑ i ∈ s, (lp.single 2 i (c i) : OscDual d m))‖ ^ (2 : ℝ) :=
      (Real.rpow_natCast _ 2).symm
    _ = ∑ i ∈ s, |c i| ^ (2 : ℝ) := by
      simpa only [ENNReal.toReal_ofNat, Real.norm_eq_abs] using h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        |c i| ^ (2 : ℝ) = |c i| ^ (2 : ℕ) := Real.rpow_natCast _ 2
        _ = c i ^ 2 := sq_abs _

end HRS.MS.R26T6C
