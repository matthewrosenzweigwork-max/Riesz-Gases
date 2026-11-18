import HRS.MC.CepE7
import HRS.MC.CepU2
import HRS.Appendix.CepaFlow

/-!
# Packet CEPB2: assembly of Proposition B.2 (`HRS.cepa_log_flow`) in repaired form

The frozen `HRS.cepa_log_flow` is FALSE as stated: the third conjunct of the existence part asks
`IsFilteredSolution P ℱ W' W X` for every Brownian filtration `ℱ` with `Measurable[ℱ 0] X₀`, but
`IsFilteredSolution.progressive` contains `Measurable[ℱ t] (X 0)` for negative `t` (see `HRS/MC/CepE7.lean`,
ISSUES entry `MC: request CEPA-LOG-FLOW`).

* `cepa_log_flow_repaired_proof`: the frozen statement verbatim except for the single change
  `Measurable[ℱ 0] X₀` ↦ `∀ t : ℝ, Measurable[ℱ t] X₀` in the third conjunct; assembled from
  `HRS.MC.CepE7.cep_E7_existence_repaired_proof` (existence) and `HRS.MC.CepU2.cep_U2_flow_unique_proof`
  (uniqueness), glued by `cep_IsC11 D.V := ⟨hV₁, L, hV₂⟩`.
* `cepa_log_flow_first_two_proof`: the frozen statement with the third conjunct of the existence part dropped
  (what the frozen statement keeps unconditionally).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepB2

open HRS

variable {N : ℕ}

theorem cepa_log_flow_repaired_proof {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {D : DynData 1} (hs : D.s = 0) (hβ : 0 < D.invβ) {a : ℝ} (ha : 0 < a)
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ)))
    (hV₁ : Torus.IsCk 1 D.V) {L : ℝ≥0} (hV₂ : LipschitzWith L (gradient (Torus.lift D.V)))
    {X₀ : Ω → Config 1 N} (hX₀ : Measurable X₀) (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet 1 N)
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)} (hW : IsVectorBrownian P W)
    (hind : IndepFun X₀ (fun ω => fun t => W t ω) P) :
    (∃ X : ℝ≥0 → Ω → Config 1 N,
      (∀ T : ℝ, 0 ≤ T → IsCepaLepingleFlow P D T X₀ W X) ∧
      -- the singular pair forces are locally integrable in time
      (∀ T : ℝ, 0 ≤ T → ∀ᵐ ω ∂P, ∀ i j : Fin N, i ≠ j →
        IntegrableOn (fun r : ℝ => periodicRieszGrad 1 D.s
          (X (Real.toNNReal r) ω i - X (Real.toNNReal r) ω j)) (Set.Icc 0 T)) ∧
      -- strong solution: adapted to every Brownian filtration of `W` for which `X₀` is `ℱ_t`-measurable for all `t`
      (∀ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ),
        IsBrownianFiltration P ℱ W' → (∀ᵐ ω ∂P, ∀ t i j, W' t ω (i, j) = W t ω i j) →
        (∀ t : ℝ, Measurable[ℱ t] X₀) → IsFilteredSolution P ℱ W' W X)) ∧
    ∀ (T : ℝ) (X X' : ℝ≥0 → Ω → Config 1 N),
      IsCepaLepingleFlow P D T X₀ W X → IsCepaLepingleFlow P D T X₀ W X' →
        ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω = X' t ω := by
  refine ⟨?_, fun T X X' h h' =>
    HRS.MC.CepU2.cep_U2_flow_unique_proof hs ha hM ⟨hV₁, L, hV₂⟩ hdist h h'⟩
  exact HRS.MC.CepE7.cep_E7_existence_repaired_proof hs hβ ha hM ⟨hV₁, L, hV₂⟩ hX₀ hdist hW hind

/-- The frozen `HRS.cepa_log_flow` with the (false) third conjunct of the existence part dropped. -/
theorem cepa_log_flow_first_two_proof {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {D : DynData 1} (hs : D.s = 0) (hβ : 0 < D.invβ) {a : ℝ} (ha : 0 < a)
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ)))
    (hV₁ : Torus.IsCk 1 D.V) {L : ℝ≥0} (hV₂ : LipschitzWith L (gradient (Torus.lift D.V)))
    {X₀ : Ω → Config 1 N} (hX₀ : Measurable X₀) (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet 1 N)
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)} (hW : IsVectorBrownian P W)
    (hind : IndepFun X₀ (fun ω => fun t => W t ω) P) :
    (∃ X : ℝ≥0 → Ω → Config 1 N,
      (∀ T : ℝ, 0 ≤ T → IsCepaLepingleFlow P D T X₀ W X) ∧
      -- the singular pair forces are locally integrable in time
      (∀ T : ℝ, 0 ≤ T → ∀ᵐ ω ∂P, ∀ i j : Fin N, i ≠ j →
        IntegrableOn (fun r : ℝ => periodicRieszGrad 1 D.s
          (X (Real.toNNReal r) ω i - X (Real.toNNReal r) ω j)) (Set.Icc 0 T))) ∧
    ∀ (T : ℝ) (X X' : ℝ≥0 → Ω → Config 1 N),
      IsCepaLepingleFlow P D T X₀ W X → IsCepaLepingleFlow P D T X₀ W X' →
        ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω = X' t ω := by
  obtain ⟨⟨X, h1, h2, -⟩, hu⟩ := cepa_log_flow_repaired_proof hs hβ ha hM hV₁ hV₂ hX₀ hdist hW hind
  exact ⟨⟨X, h1, h2⟩, hu⟩

/-- Documentation of the repair: the frozen existence/uniqueness data follow from the repaired statement,
the only difference being the hypothesis `Measurable[ℱ 0] X₀` replaced by the stronger
`∀ t, Measurable[ℱ t] X₀` (so the repaired third conjunct is weaker than the frozen one). -/
example {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ mΩ) {X₀ : Ω → Config 1 N} :
    (∀ t : ℝ, Measurable[ℱ t] X₀) → Measurable[ℱ 0] X₀ := fun h => h 0

end HRS.MC.CepB2
