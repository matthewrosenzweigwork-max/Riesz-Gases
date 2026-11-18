import HRS.MS.R26T8AP08e

/-!
# S8.2 T8A P08 (part f): Fubini for a conormal pair function against `μ ⊗ μ`, `μ = ρ dx` a smooth probability density with polynomial decay
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_f25_diag_null (hd : 2 ≤ d) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) :
    ∀ᵐ p : Euc d × Euc d ∂((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)), p.1 ≠ p.2 := by
  haveI : Nontrivial (Euc d) := ⟨⟨0, EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ), by
    intro h; have := congrArg (fun v : Euc d => v ⟨0, by omega⟩) h; simp at this⟩⟩
  haveI := HRS.MS.Wad.s85_isProb hρ
  have hms : MeasurableSet {p : Euc d × Euc d | p.1 = p.2} := measurableSet_eq_fun measurable_fst measurable_snd
  rw [ae_iff]
  have : {p : Euc d × Euc d | ¬ p.1 ≠ p.2} = {p : Euc d × Euc d | p.1 = p.2} := by
    ext p; simp
  rw [this, Measure.prod_apply hms]
  have hz : ∀ x : Euc d, (HRS.Whole.withDensityReal ρ) (Prod.mk x ⁻¹' {p : Euc d × Euc d | p.1 = p.2}) = 0 := by
    intro x
    have : Prod.mk x ⁻¹' {p : Euc d × Euc d | p.1 = p.2} = {x} := by ext y; simp [eq_comm]
    rw [this]
    exact (withDensity_absolutelyContinuous _ _) (measure_singleton x)
  simp only [hz, lintegral_zero]

end HRS.MS.R26T8A
