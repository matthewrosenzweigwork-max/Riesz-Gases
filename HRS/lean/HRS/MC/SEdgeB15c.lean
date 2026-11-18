import HRS.MC.SEdgeVocab

/-!
# Packet B15c: a.e. congruence of `sed_Qt` and of the triple integral (relocation of `sed_B15c_congr`)

Proof of the statement `HRS.MC.SEdge.sed_B15c_congr` (SEdgeSpec.lean) in its own file.  The spec theorem
stays `sorry`; the `example` at the end ties this proof to it by `type_of%`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B15c

open HRS.Sec7
open HRS.MC.SEdge

variable {d : ℕ}

theorem sed_B15c_congr_proof {ρ : Torus d → ℝ} (s : ℝ) (v : Fin d → Torus d → ℝ)
    {f g f' g' k k' : Torus d → ℝ} (hf : f =ᵐ[withDensityReal ρ] f') (hg : g =ᵐ[withDensityReal ρ] g')
    (hk : k =ᵐ[withDensityReal ρ] k') :
    sed_Qt d s ρ v f g = sed_Qt d s ρ v f' g' ∧
      ∫ x, f x * g x * k x ∂(withDensityReal ρ) = ∫ x, f' x * g' x * k' x ∂(withDensityReal ρ) := by
  constructor
  · unfold sed_Qt
    refine integral_congr_ae ?_
    filter_upwards [hf] with x hx
    try dsimp only
    rw [hx]
    refine integral_congr_ae ?_
    filter_upwards [hg] with y hy
    try dsimp only
    rw [hy]
  · refine integral_congr_ae ?_
    filter_upwards [hf, hg, hk] with x h1 h2 h3
    try dsimp only
    rw [h1, h2, h3]

end HRS.MC.SEdge.B15c

end

