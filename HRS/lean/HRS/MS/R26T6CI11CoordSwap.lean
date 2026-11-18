import HRS.MS.R26T6CI11SamplePath
import HRS.MS.R26T6CI09Coord

/-!
# I11: recover oscillator coordinates after Fubini's interchange,
# on one samplewise full-measure set.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.Whole
variable {d : ℕ}

theorem r26t6c_spacetime_coordinates_swapped
    (m : ℝ) {Time Omega : Type*}
    [MeasurableSpace Time] [MeasurableSpace Omega]
    (dt : Measure Time) [SFinite dt]
    (P : Measure Omega) [SFinite P]
    (g : MultiIndex d → Time × Omega → ℝ)
    (hsum : ∀ᵐ z ∂(dt.prod P),
      Summable (fun i => g i z ^ 2)) :
    ∀ᵐ w ∂P, ∀ᵐ t ∂dt, ∀ i,
      OscDual.coord (ellVec (d := d) m (fun j => g j (t,w))) i =
        g i (t,w) := by
  have hcoord := r26t6c_ellVec_coord_ae (P := dt.prod P)
    m g hsum
  have hsw := (Measure.measurePreserving_swap (μ := P) (ν := dt)).quasiMeasurePreserving.ae hcoord
  exact Measure.ae_ae_of_ae_prod hsw

end HRS.MS.R26T6C
