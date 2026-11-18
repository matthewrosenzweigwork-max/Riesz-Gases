import HRS.MS.PROS13VectorError

/-!
# S13: exact Euclidean subtraction of finite families with common first block
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos

theorem pro_s13_euclidean_append_sub
    {n m : ℕ} (f : Fin n → ℝ)
    (g g' : Fin m → ℝ) :
    ((WithLp.toLp 2 (Fin.append f g) :
      EuclideanSpace ℝ (Fin (n + m))) -
      (WithLp.toLp 2 (Fin.append f g') :
      EuclideanSpace ℝ (Fin (n + m)))) =
      (WithLp.toLp 2 (Fin.append
        (fun _ : Fin n => (0 : ℝ))
        (fun k : Fin m => g k - g' k)) :
        EuclideanSpace ℝ (Fin (n + m))) := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · simp
  · simp

end HRS.MS.R26T3
