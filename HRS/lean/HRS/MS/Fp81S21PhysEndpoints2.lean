import HRS.MS.Fp81S21PhysEndpoints
import HRS.MS.Fp81S21InitialWindow

/-! The actual preparation law fixes the centering at time zero. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp

/-- The configuration at time zero has the prescribed preparation law. -/
theorem fp81s21_physical_initial_configuration_law
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (A : Particle R N) : A.P.map (A.X 0) = r26t3_Q R N := by
  have hinit : A.X 0 =ᵐ[A.P] A.X₀ := (A.strong 0).init
  rw [Measure.map_congr hinit]
  exact A.initial

/-- The time-zero fluctuation uses the actual preparation mean, including at
zero coupling. -/
theorem fp81s21_physical_initial_functional
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (A : Particle R N) :
    ∀ᵐ ω ∂A.P, s102_zf A.P A.X ω 0 = initialFunctional R N (A.X₀ ω) := by
  have hlaw := fp81s21_physical_initial_configuration_law p R A
  filter_upwards [(A.strong 0).init] with ω hω
  funext f
  simp only [s102_zf, initialFunctional, Real.toNNReal_zero, hω, hlaw]

/-- The initial propagator in the particle construction is the propagation of
the actual preparation-centered functional. -/
theorem fp81s21_physical_initial_y0
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (A : Particle R N) (H : ℝ) :
    ∀ᵐ ω ∂A.P,
      s102_y0 (r26t3_coeff R) (wholeSpaceIndex p.d) H A.P A.X ω =
        r2InitProp (r26t3_coeff R) (wholeSpaceIndex p.d) H
          (initialFunctional R N (A.X₀ ω)) := by
  filter_upwards [fp81s21_physical_initial_functional p R A] with ω hω
  have he : s102_y0 (r26t3_coeff R) (wholeSpaceIndex p.d) H A.P A.X ω =
      r2InitProp (r26t3_coeff R) (wholeSpaceIndex p.d) H (s102_zf A.P A.X ω 0) := by
    unfold s102_y0 s102_zf
    simp only [Real.toNNReal_zero]
  rw [he, hω]

#print axioms HRS.Fp81.S21.fp81s21_physical_initial_configuration_law
#print axioms HRS.Fp81.S21.fp81s21_physical_initial_functional
#print axioms HRS.Fp81.S21.fp81s21_physical_initial_y0
end HRS.Fp81.S21
end
