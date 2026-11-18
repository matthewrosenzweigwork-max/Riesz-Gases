import HRS.MS.Fp81S21GaussG4U74

/-! Centered scalar time-integral estimates for the initial G4 bound. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3

/-- Scalar Cauchy--Schwarz on a finite time measure, in the squared-integral
form used after centering Duhamel pointwise. -/
theorem fp81s21_g4_time_cauchy_schwarz
    {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    (f : α → ℝ) (hf : MemLp f 2 ν) :
    (∫ t, f t ∂ν)^2 ≤ ν.real Set.univ * ∫ t, f t ^ 2 ∂ν := by
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) ν := by simpa using hf
  have h1 : MemLp (fun _ : α => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) ν := by
    simpa using (memLp_const (1 : ℝ) : MemLp (fun _ : α => (1 : ℝ)) 2 ν)
  have hcs := integral_mul_norm_le_Lp_mul_Lq (f := f)
    (g := fun _ : α => (1 : ℝ)) (p := 2) (q := 2)
    Real.HolderConjugate.two_two hf' h1
  have habs : |∫ t, f t ∂ν| ≤ ∫ t, |f t| ∂ν := abs_integral_le_integral_abs
  have hcs' : ∫ t, |f t| ∂ν ≤
      Real.sqrt (∫ t, f t ^ 2 ∂ν) * Real.sqrt (ν.real Set.univ) := by
    simpa [Real.sqrt_eq_rpow, Real.norm_eq_abs, Measure.real] using hcs
  have hI : 0 ≤ ∫ t, f t ^ 2 ∂ν := integral_nonneg fun t => sq_nonneg (f t)
  have hν : 0 ≤ ν.real Set.univ := measureReal_nonneg
  have hsqrt : 0 ≤ Real.sqrt (∫ t, f t ^ 2 ∂ν) * Real.sqrt (ν.real Set.univ) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hle := habs.trans hcs'
  have hsq := (sq_le_sq₀ (abs_nonneg _) hsqrt).2 hle
  simpa [sq_abs, mul_pow, Real.sq_sqrt hI, Real.sq_sqrt hν, mul_comm] using hsq

#print axioms fp81s21_g4_time_cauchy_schwarz
end HRS.Fp81.S21
