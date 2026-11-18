import HRS.MS.ProClosureS21IidFamily

set_option autoImplicit false
set_option maxHeartbeats 400000

/-!
# Indexed iid Edgeworth core for the S2.1 shifted observation family

This exports the arbitrary-index form of the iid preparation theorem with one
common norm bound, one common summable coordinate envelope, and a particle
threshold chosen before the index and the test function.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

/-- Indexed iid Edgeworth expansion with a common fourth-moment and projection-tail
package. The particle threshold is uniform over the index and the full `CbUnitBall 5`. -/
theorem fp81s21_iid_indexed_core
    {d : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    {ι : Type*}
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (e : HilbertBasis ℕ ℝ H) (Y : ι → Euc d → H)
    (hYc : ∀ a, Continuous (Y a)) (C : ℝ)
    (hC : ∀ a x, ‖Y a x‖ ≤ C)
    (hcent : ∀ a, ∫ x, Y a x ∂μ = 0)
    (w : ℕ → ℝ) (hw : Summable w)
    (hYw : ∀ a n x, (inner ℝ (e n) (Y a x)) ^ 2 ≤ w n)
    (G : ι → Measure H) [∀ a, IsProbabilityMeasure (G a)]
    (hGg : ∀ a, IsCenteredGaussian (G a))
    (hcov : ∀ a x y,
      covarianceBilin (G a) x y = covarianceBilin (μ.map (Y a)) x y) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N → ∀ a,
      ∀ Φ ∈ CbUnitBall H 5,
      |Real.sqrt N *
        (∫ z, Φ (HRS.StaticLimitAux.Ssum (Y a) N z) ∂(Measure.pi fun _ : Fin N => μ) -
          ∫ F, Φ F ∂(G a)) -
        (1 / 6) * ∫ F, ∫ x,
          iteratedFDeriv ℝ 3 Φ F ![Y a x, Y a x, Y a x] ∂μ ∂(G a)| ≤ ε := by
  exact HRS.MS.ProClosureS21IidFamily.iid_family_Cb5
    μ e Y hYc C hC hcent w hw hYw G hGg hcov

#print axioms fp81s21_iid_indexed_core

end HRS.Fp81.S21
