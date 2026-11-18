import HRS.MC.CepC0
import HRS.MC.CepN6
import HRS.MC.CepS3

/-!
# Packet CEPB13: Remark B.13 (one-dimensional logarithmic threshold), the iff

Proof of `HRS.cepa_noncollision_iff_threshold` (`HRS/Appendix/CepaFlow.lean`, kept as `sorry`).
Necessity (`→`) is `HRS.MC.CepN6.cep_N6_contact_below_threshold_proof` by contraposition; sufficiency (`←`) is
`HRS.MC.CepS3.cep_S3_noncollision_of_threshold_proof`. The frozen hypotheses `Torus.IsCk 1 D.V` and
`LipschitzWith L (gradient (Torus.lift D.V))` give `HRS.MC.CepC0.cep_IsC11 D.V` by definition.
This file imports only proved packet modules.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepB13

open HRS

/-- Remark B.13 (`M:B:rem:d1-threshold-sharp`): the frozen statement `HRS.cepa_noncollision_iff_threshold`. -/
theorem cepa_noncollision_iff_threshold_proof
    {N : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hN : 2 ≤ N) {D : DynData 1} (hs : D.s = 0) (hβ : 0 < D.invβ) {a : ℝ} (ha : 0 < a)
    (hM : D.M = -(a • (1 : Matrix (Fin 1) (Fin 1) ℝ)))
    (hV₁ : Torus.IsCk 1 D.V) {L : ℝ≥0} (hV₂ : LipschitzWith L (gradient (Torus.lift D.V)))
    {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → Config 1 N} (hX₀ : Measurable X₀) (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet 1 N)
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)} (hW : IsVectorBrownian P W)
    (hind : IndepFun X₀ (fun ω => fun t => W t ω) P)
    {X : ℝ≥0 → Ω → Config 1 N} (hX : IsCepaLepingleFlow P D T X₀ W X) :
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω ∉ collisionSet 1 N) ↔
      (N : ℝ) * D.invβ ≤ a := by
  have hV : HRS.MC.CepC0.cep_IsC11 D.V := by
    unfold HRS.MC.CepC0.cep_IsC11
    exact ⟨hV₁, L, hV₂⟩
  constructor
  · intro hall
    by_contra hlt
    exact HRS.MC.CepN6.cep_N6_contact_below_threshold_proof hN hs hβ ha hM hV hT hX₀ hdist hW hind hX
      (not_le.mp hlt) hall
  · intro hthr
    exact HRS.MC.CepS3.cep_S3_noncollision_of_threshold_proof hN hs hβ ha hM hV hT hX₀ hdist hW hind hX hthr

end HRS.MC.CepB13
