import HRS.MS.R26T6CI09Meas
import HRS.MS.CovMeasAux1

/-! I09: almost-sure coordinates of the genuine ellVec lift. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.Whole HRS.MS.CovMeas

theorem r26t6c_ellVec_coord_ae {d : ℕ} {Omega : Type*}
    [MeasurableSpace Omega] (P : Measure Omega) (m : ℝ)
    (f : MultiIndex d → Omega → ℝ)
    (hsum : ∀ᵐ w ∂P, Summable fun i => f i w ^ 2) :
    ∀ᵐ w ∂P, ∀ i,
      OscDual.coord (ellVec (d := d) m (fun j => f j w)) i = f i w := by
  filter_upwards [hsum] with w hw
  have hm : Memℓp (fun i => f i w) 2 := by
    rw [memℓp_two_iff]
    exact hw
  intro i
  exact s101_ellVec_coord hm i

end HRS.MS.R26T6C
