import HRS.MC.CepH5MMix
import HRS.MC.CepH5C1
import HRS.MC.CepH5C2
import HRS.MC.CepH5C3

/-!
# Packet M: `h5_selectedLaw_mixture` for the components `h5Comp`
(uses the proved component lemmas of packet C).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH5Pf

open HRS

section Flow

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ} [NeZero N]

theorem h5_selectedLaw_mixture_proof [IsProbabilityMeasure P] {X₀ : Ω → Config 1 N} (hX₀ : Measurable X₀)
    (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet 1 N) {X : ℝ≥0 → Ω → Config 1 N} (t : ℝ)
    (hXt : Measurable (X (Real.toNNReal t))) :
    selectedLaw P X t = ∑ σ : h5Idx N, ENNReal.ofReal ((P (X₀ ⁻¹' h5Comp σ.1)).toReal) •
      selectedLaw (ProbabilityTheory.cond P (X₀ ⁻¹' h5Comp σ.1)) X t :=
  h5M_mixture_general hX₀ hdist t hXt (fun σ : h5Idx N => h5Comp σ.1)
    (fun σ => (h5Comp_isOpen_proof σ.1).measurableSet)
    (fun σ σ' h => h5Comp_disjoint_proof h) h5Comp_iUnion_proof

end Flow

end HRS.MC.CepH5Pf
