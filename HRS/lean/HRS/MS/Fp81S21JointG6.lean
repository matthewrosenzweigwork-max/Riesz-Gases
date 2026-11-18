import HRS.MS.Fp81S21JointG5
import HRS.MS.Fp81S21JointW4
import HRS.MS.Fp81S21WickApprox40

/-! The kernel approximation in the joint product space. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory
namespace HRS.Fp81.S21

/-- A bound for the quadratic kernel error lifts to the pair while the linear
coordinate is held fixed. -/
theorem fp81s21_jointG_kernel_pair_sqerr
    {Ω V W : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V] [NormedAddCommGroup W]
    (P : Measure Ω) (f : Ω → V) (u v : Ω → W) (ε : ℝ) (hε : 0 ≤ ε)
    (h : fp81s21_SqErr P u v ε) :
    fp81s21_SqErr P (fun ω => (f ω, v ω)) (fun ω => (f ω, u ω)) ε := by
  have hs : fp81s21_SqErr P v u ε := by
    simpa only [fp81s21_SqErr, norm_sub_rev] using h
  have hz : fp81s21_SqErr P f f 0 := by
    simp [fp81s21_SqErr]
  simpa using fp81s21_jointG_pair_sqerr P f f v u 0 ε le_rfl hε hz hs

#print axioms fp81s21_jointG_kernel_pair_sqerr
end HRS.Fp81.S21
end
