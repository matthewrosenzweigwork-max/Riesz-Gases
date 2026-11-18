import HRS.Appendix.B15Final
import HRS.MC.CepH5FinProof
import HRS.Appendix.CepaFlow

/-!
# Proposition B.15 (`M:B:prop:sde-entropy-law`): both branches

Relocated proof of the frozen `HRS.sde_entropy_law` (`HRS/Appendix/CepaFlow.lean`).  The statement below is a
verbatim copy, tied to the frozen one by `example := (@sde_entropy_law_proof : type_of% @sde_entropy_law)`.

Assembly: `SelectedFlow` is a disjunction.  The collision-free strong branch (cases (a), (b), (d) of Assumption A.1)
is `b15_sde_entropy_law_free_proof`; the Cépa–Lépingle branch (case (c): `d = 1`, `s = 0`) is
`HRS.MC.CepH5Fin.cep_H5_entropy_confined_proof` (Proposition B.14), which has the statement of the frozen
`cepa_entropy_confined` up to the order of four implicit binders.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

theorem sde_entropy_law_proof
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hN : 2 ≤ N) [NeZero N]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ)) (hβ : 0 < D.invβ)
    (hV : Torus.IsCk 2 D.V) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : SelectedFlow P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    (hdens0 : HasSelectedDensity P X 0)
    (hH0 : gibbsEntropy D (selectedLaw P X 0) < ⊤) :
    (∀ t ∈ Set.Icc 0 T, HasSelectedDensity P X t ∧
      gibbsEntropy D (selectedLaw P X t)
        + ((ENNReal.ofReal D.invβ *
            ∫⁻ r in Set.Icc (0 : ℝ) t, fisherInfo D N (selectedLaw P X r) : ℝ≥0∞) : EReal)
        ≤ gibbsEntropy D (selectedLaw P X 0)) ∧
    SolvesSelectedFKE D T (selectedLaw P X) := by
  rcases hX with ⟨hX₀, hdist, hW, hind, hflow⟩
  rcases hflow with ⟨hS, hU⟩ | ⟨hd1, hs0, _, _, hCL⟩
  · exact b15_sde_entropy_law_free_proof hN hM hβ hV hT hX₀ hdist hW hind hS hU hF hdens0 hH0
  · subst hd1
    exact HRS.MC.CepH5Fin.cep_H5_entropy_confined_proof hN hs0 hβ hM hV hT hX₀ hdist hW hind hCL hF hdens0 hH0

example := (@sde_entropy_law_proof : type_of% @sde_entropy_law)

end HRS
