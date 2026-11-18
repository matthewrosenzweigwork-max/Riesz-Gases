import HRS.MS.Fp81S21DriftCumulative8
import HRS.MS.Fp81S21DriftCumulative9

/-! Measurable fixed-time sections of the physical drift cumulative. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp

/-- The actual path-valued cumulative has an a.e. measurable section at
every admissible cumulative time. -/
theorem fp81s21_moving_drift_cumulative_section_aemeasurable
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
      (2 * p.d + 8) c hH)
    (hphys : Fp81MovingPhysicalInputs R hN A H)
    (v : ℝ) (hv : v ∈ Icc (0 : ℝ) H) :
    AEMeasurable (fun ω => r2DriftInc (r26t3_coeff R)
      (wholeSpaceIndex p.d : ℝ) H
      (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) 0 v) A.P := by
  apply fp81s21_oscPath_aemeasurable_of_coordinates A.P
  intro t α
  have hi := fp81s21_moving_drift_orbit_integral_aemeasurable
    p R hδ hδh hH A hstd v t hv.1 t.2 α
  apply hi.congr
  filter_upwards [fp81s21_moving_drift_increment_coord p R hH hN A hstd hphys] with ω hω
  rw [← s102_r2PathAt_of_mem _ t.2]
  exact (hω 0 v t le_rfl hv.1 t.2 α).symm

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_moving_drift_cumulative_section_aemeasurable
