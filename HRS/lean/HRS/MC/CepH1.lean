import HRS.Appendix.CepaFlow
import HRS.Stochastic.SelectedLawFKE

/-!
# Packet CEPH1: the FKE conjunct of B.14 from `selected_law_fke`
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.CepH1

open HRS

theorem cep_H1_fke_proof {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}
    [IsProbabilityMeasure P] (hN : 2 ≤ N) [NeZero N]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ}
    {D : DynData 1} (hs : D.s = 0) (hβ : 0 < D.invβ)
    (hM : D.M = -(1 : Matrix (Fin 1) (Fin 1) ℝ)) (hV : Torus.IsCk 2 D.V) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → Config 1 N} (hX₀ : Measurable X₀) (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet 1 N)
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)} (hW : IsVectorBrownian P W)
    (hind : IndepFun X₀ (fun ω => fun t => W t ω) P) {X : ℝ≥0 → Ω → Config 1 N}
    (hX : IsCepaLepingleFlow P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X) :
    SolvesSelectedFKE D T (selectedLaw P X) := by
  have hSF : SelectedFlow P D T X₀ W X :=
    { init_meas := hX₀
      init_distinct := hdist
      brownian := hW
      indep := hind
      flow := Or.inr ⟨rfl, hs, hβ, ⟨1, one_pos, by simpa using hM⟩, hX⟩ }
  exact fun Φ hΦ => (selected_law_fke hN hV hT hSF hF).2 Φ hΦ

end HRS.MC.CepH1
