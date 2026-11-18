import HRS.MS.S21E_Fin
import HRS.MS.S21E_Zeta
import HRS.MS.WsPrepAux11

/-!
# S2.1(iii) packet G8: the measurability conjuncts of the expansion clause are free

`s21e_expansion_of_bound`: `S21eExpansion` follows from its quantitative part `S21eExpBound` alone, because the two `AEMeasurable` conjuncts hold for every
strong solution (`s21e_zeta_window_aemeas`, packet G7: moving first-marginal centering) and every linear Gaussian evolution on the horizon `a₀ + T`
(`s21p_Z_window_aemeas`).  No junk value of `windowPathOf` is used.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Whole

variable {d : ℕ}

/-- The quantitative part of the expansion clause. -/
def S21eExpBound (d : ℕ) (s a β β₀ : ℝ) (ρ : ℝ → Euc d → ℝ) (T : ℝ)
    (κ : ℝ → projTensor (OscPath d (wholeSpaceIndex d) T) 3) (εN : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, 2 ≤ N →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (X : ℝ≥0 → Ω → EucConfig d N),
    IsVectorBrownian P W → IndepFun X₀ (fun ζ t => W t ζ) P →
    law P X₀ = modulatedGibbs (rieszKernel d s) N β₀ (withDensityReal (ρ 0)) →
    (∀ T' : ℝ, IsWholeStrongSolution P (quadraticGradientDyn d s a β) T' X₀ W X) →
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℝ → Ω' → OscDual d (wholeSpaceIndex d)),
    (∀ T' : ℝ, IsLinearGaussianEvolutionW P' ((quadraticGradientDyn d s a β).coeff ρ)
      (wholeSpaceIndex d) β⁻¹ T'
      (susceptibilityCov (rieszKernel d s) (withDensityReal (ρ 0)) β₀) Z) →
  ∀ a₀ : ℝ, 0 ≤ a₀ →
    ∀ Φ : OscPath d (wholeSpaceIndex d) T → ℝ,
      Φ ∈ CbUnitBall (OscPath d (wholeSpaceIndex d) T) 5 →
      |Real.sqrt N * (∫ ζ, Φ (zetaPathW (wholeSpaceIndex d) T a₀ P X ζ) ∂P -
          ∫ ζ', Φ (processWindow (wholeSpaceIndex d) T a₀ Z ζ') ∂P') -
        (1 / 6) * ∫ ζ', (κ a₀ : TensorDual (OscPath d (wholeSpaceIndex d) T) 3)
          (iteratedFDeriv ℝ 3 Φ (processWindow (wholeSpaceIndex d) T a₀ Z ζ')) ∂P'| ≤
        εN N

theorem s21e_expansion_of_bound (hd : 2 ≤ d) {s a β β₀ T : ℝ} (hT : 0 < T) {ρ : ℝ → Euc d → ℝ}
    {κ : ℝ → projTensor (OscPath d (wholeSpaceIndex d) T) 3} {εN : ℕ → ℝ}
    (h : S21eExpBound d s a β β₀ ρ T κ εN) : S21eExpansion d s a β β₀ ρ T κ εN := by
  intro N hN Ω _ P _ X₀ W X hBr hInd hlaw hstrong Ω' _ P' _ Z hZ a₀ ha₀
  have hd1 : 1 ≤ d := by omega
  have hm : (d : ℝ) < ((wholeSpaceIndex d : ℕ) : ℝ) := by
    unfold wholeSpaceIndex
    push_cast
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  refine ⟨?_, s21p_Z_window_aemeas P' ha₀ hT.le (hZ (a₀ + T)), h N hN P X₀ W X hBr hInd hlaw hstrong P' Z hZ a₀ ha₀⟩
  exact s21e_zeta_window_aemeas hd1 (by omega) hm ha₀ hT.le P X (hstrong 0).adapted (hstrong 0).cont

end HRS.Whole
