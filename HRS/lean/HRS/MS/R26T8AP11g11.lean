import HRS.MS.R26T8AP11g10
import HRS.MS.R26T8AP11f12
import HRS.MS.R26T8AP11f9
import HRS.MS.R26T8AP08d

/-!
# S8.2 T8A P11g (part 11): the diagonal is `volume ⊗ volume`-null
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_g11_diag_null (hd : 2 ≤ d) : ∀ᵐ p : Euc d × Euc d ∂(volume.prod volume), p.1 ≠ p.2 := by
  haveI : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  have hms : MeasurableSet {p : Euc d × Euc d | p.1 = p.2} := measurableSet_eq_fun measurable_fst measurable_snd
  rw [ae_iff]
  have : {p : Euc d × Euc d | ¬ p.1 ≠ p.2} = {p : Euc d × Euc d | p.1 = p.2} := by
    ext p; simp
  rw [this, Measure.prod_apply hms]
  have hz : ∀ x : Euc d, (volume : Measure (Euc d)) (Prod.mk x ⁻¹' {p : Euc d × Euc d | p.1 = p.2}) = 0 := by
    intro x
    have : Prod.mk x ⁻¹' {p : Euc d × Euc d | p.1 = p.2} = {x} := by ext y; simp [eq_comm]
    rw [this]
    exact measure_singleton x
  simp only [hz, lintegral_zero]

end HRS.MS.R26T8A
