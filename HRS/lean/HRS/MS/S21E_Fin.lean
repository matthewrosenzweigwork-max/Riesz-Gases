import HRS.MS.S21E_Uniq
import HRS.MS.S21E_Dens

/-!
# S2.1(iii) packet G6: the interface of `whole_space_edgeworth` and its conditional reduction

`S21EdgeBody` is the post-`ρ` body of the frozen conclusion (tensor family, `ε_N`, cross-density clause, expansion), split into
`S21eCrossClause` (existence of densities + universal formula) and `S21eExpansion`.  `whole_space_edgeworth_of_body` (type-checked against
`type_of% @whole_space_edgeworth`) reduces the frozen statement to `S21EdgeBody` for each resulting solution.

`s21e_body_of_parts` builds `S21EdgeBody` from: the bounded symmetric tensor family; the cross-density existence (packet G1, core H1); the formula for
ONE density family (packet H2; every other family is a.e. equal, packet G2); and the expansion.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Whole

variable {d : ℕ}

/-- The pairing clause defining the cross-densities of the frozen conclusion. -/
def S21eChiClause (d : ℕ) (s a β β₀ : ℝ) (ρ : ℝ → Euc d → ℝ) (T a₀ : ℝ) (τ : Fin 3 → Set.Icc (0 : ℝ) T)
    (φ : Fin 3 → Euc d → ℝ) (χ : Fin 3 → ℝ → Euc d → ℝ) : Prop :=
  ∀ i, ∀ r ∈ Set.Icc (0 : ℝ) (a₀ + T),
    MemLp (fun x => χ i r x / ρ r x) 2 (withDensityReal (ρ r)) ∧
    ∀ ψ', IsOscTest (wholeSpaceIndex d) ψ' →
      Integrable (fun x => ψ' x * χ i r x) ∧
      ∫ x, ψ' x * χ i r x = linearGaussianCov
        ((quadraticGradientDyn d s a β).coeff ρ) β⁻¹
        (susceptibilityCov (rieszKernel d s) (withDensityReal (ρ 0)) β₀) r (a₀ + τ i)
        ψ' (φ i)

/-- The formula clause: for the density family `χ`, the tensor `κ` evaluates as `cubicFormula`. -/
def S21eFormulaFor (d : ℕ) (s a β β₀ : ℝ) (ρ : ℝ → Euc d → ℝ) (T a₀ : ℝ)
    (κ : projTensor (OscPath d (wholeSpaceIndex d) T) 3) (τ : Fin 3 → Set.Icc (0 : ℝ) T)
    (φ : Fin 3 → Euc d → ℝ) (χ : Fin 3 → ℝ → Euc d → ℝ) : Prop :=
  ∀ M : (OscPath d (wholeSpaceIndex d) T) [×3]→L[ℝ] ℝ,
    (∀ w : Fin 3 → OscPath d (wholeSpaceIndex d) T,
      M w = ∏ i, OscDual.eval (OscPath.at' (w i) (τ i)) (φ i)) →
    (κ : TensorDual (OscPath d (wholeSpaceIndex d) T) 3) M =
      cubicFormula (quadraticGradientDyn d s a β) ρ β β₀ (withDensityReal (ρ 0))
        (fun i => a₀ + τ i) φ χ ∧
    CubicFormulaIntegrable (quadraticGradientDyn d s a β) ρ β₀ (withDensityReal (ρ 0))
      (fun i => a₀ + τ i) φ χ

/-- The cross-density clause of the frozen conclusion. -/
def S21eCrossClause (d : ℕ) (s a β β₀ : ℝ) (ρ : ℝ → Euc d → ℝ) (T : ℝ)
    (κ : ℝ → projTensor (OscPath d (wholeSpaceIndex d) T) 3) : Prop :=
  ∀ a₀ : ℝ, 0 ≤ a₀ → ∀ (τ : Fin 3 → Set.Icc (0 : ℝ) T) (φ : Fin 3 → Euc d → ℝ),
    (∀ i, IsOscTest (wholeSpaceIndex d) (φ i)) →
    (∃ χ : Fin 3 → ℝ → Euc d → ℝ, S21eChiClause d s a β β₀ ρ T a₀ τ φ χ) ∧
    ∀ χ : Fin 3 → ℝ → Euc d → ℝ, S21eChiClause d s a β β₀ ρ T a₀ τ φ χ →
      S21eFormulaFor d s a β β₀ ρ T a₀ (κ a₀) τ φ χ

/-- The expansion clause of the frozen conclusion. -/
def S21eExpansion (d : ℕ) (s a β β₀ : ℝ) (ρ : ℝ → Euc d → ℝ) (T : ℝ)
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
    AEMeasurable (zetaPathW (wholeSpaceIndex d) T a₀ P X) P ∧
    AEMeasurable (processWindow (wholeSpaceIndex d) T a₀ Z) P' ∧
    ∀ Φ : OscPath d (wholeSpaceIndex d) T → ℝ,
      Φ ∈ CbUnitBall (OscPath d (wholeSpaceIndex d) T) 5 →
      |Real.sqrt N * (∫ ζ, Φ (zetaPathW (wholeSpaceIndex d) T a₀ P X ζ) ∂P -
          ∫ ζ', Φ (processWindow (wholeSpaceIndex d) T a₀ Z ζ') ∂P') -
        (1 / 6) * ∫ ζ', (κ a₀ : TensorDual (OscPath d (wholeSpaceIndex d) T) 3)
          (iteratedFDeriv ℝ 3 Φ (processWindow (wholeSpaceIndex d) T a₀ Z ζ')) ∂P'| ≤
        εN N

/-- The body of the frozen conclusion after the resulting solution `ρ` is fixed. -/
def S21EdgeBody (d : ℕ) (s a β β₀ T : ℝ) (ρ : ℝ → Euc d → ℝ) : Prop :=
  ∃ (κ : ℝ → projTensor (OscPath d (wholeSpaceIndex d) T) 3) (εN : ℕ → ℝ),
    (∃ Kb : ℝ, ∀ a₀ : ℝ, 0 ≤ a₀ → ‖κ a₀‖ ≤ Kb) ∧
    (∀ a₀ : ℝ, 0 ≤ a₀ → ∀ (σ : Equiv.Perm (Fin 3))
      (M : (OscPath d (wholeSpaceIndex d) T) [×3]→L[ℝ] ℝ),
      (κ a₀ : TensorDual (OscPath d (wholeSpaceIndex d) T) 3) (M.domDomCongr σ) =
        (κ a₀ : TensorDual (OscPath d (wholeSpaceIndex d) T) 3) M) ∧
    Tendsto εN atTop (𝓝 0) ∧
    S21eCrossClause d s a β β₀ ρ T κ ∧ S21eExpansion d s a β β₀ ρ T κ εN

/-- **The conditional reduction.**  The frozen `whole_space_edgeworth` follows from `S21EdgeBody` for every resulting solution. -/
theorem whole_space_edgeworth_of_body
    (hbody : ∀ (d : ℕ), 2 ≤ d → ∀ (s : ℝ), 0 ≤ s → s < (d : ℝ) / 2 → ∀ (a β : ℝ), 0 < a → 0 < β →
      ∀ β₀ : ℝ, 0 ≤ β₀ → (0 < s → 0 < β₀) → ∀ T : ℝ, 0 < T → ∀ c₁ C₁ : ℝ,
      ∃ εstar : ℝ, 0 < εstar ∧
        ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ ε : ℝ, ∀ ψ : Euc d → ℝ,
          IsAdmissiblePerturbation ρβ εstar ε ψ → ∀ ρ : ℝ → Euc d → ℝ,
          IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ → S21EdgeBody d s a β β₀ T ρ) :
    HRS.Whole.WholeSpaceEdgeworthStatement := by
  intro d hd s hs0 hs a β ha hβ β₀ hβ₀ hβ₀s T hT c₁ C₁
  obtain ⟨εstar, hε, h⟩ := hbody d hd s hs0 hs a β ha hβ β₀ hβ₀ hβ₀s T hT c₁ C₁
  exact ⟨εstar, hε, h⟩

/-- The universal formula clause from the formula for one density family (all families are a.e. equal, G2). -/
theorem s21e_formula_universal {s a β β₀ T : ℝ} {ρ : ℝ → Euc d → ℝ}
    {κ : projTensor (OscPath d (wholeSpaceIndex d) T) 3} {a₀ : ℝ}
    {τ : Fin 3 → Set.Icc (0 : ℝ) T} {φ : Fin 3 → Euc d → ℝ} {χ₀ : Fin 3 → ℝ → Euc d → ℝ}
    (h₀ : S21eChiClause d s a β β₀ ρ T a₀ τ φ χ₀) (hf : S21eFormulaFor d s a β β₀ ρ T a₀ κ τ φ χ₀)
    {χ : Fin 3 → ℝ → Euc d → ℝ} (h : S21eChiClause d s a β β₀ ρ T a₀ τ φ χ) :
    S21eFormulaFor d s a β β₀ ρ T a₀ κ τ φ χ := by
  have hae : ∀ i, ∀ r ∈ Set.Icc (0 : ℝ) (a₀ + T), χ i r =ᵐ[volume] χ₀ i r := by
    intro i r hr
    refine HRS.MS.S21E.s21e_chi_ae_eq (wholeSpaceIndex d : ℝ)
      (fun ψ hψ => ((h i r hr).2 ψ hψ).1) (fun ψ hψ => ((h₀ i r hr).2 ψ hψ).1) (fun ψ hψ => ?_)
    rw [((h i r hr).2 ψ hψ).2, ((h₀ i r hr).2 ψ hψ).2]
  have htm : ∀ i, a₀ + (τ i : ℝ) ≤ a₀ + T := fun i => by linarith [(τ i).2.2]
  obtain ⟨e1, e2⟩ := HRS.MS.S21E.s21e_cubicFormula_congr (quadraticGradientDyn d s a β) ρ β β₀
    (withDensityReal (ρ 0)) (fun i => a₀ + τ i) φ χ χ₀ (a₀ + T) htm hae
  intro M hM
  obtain ⟨hk1, hk2⟩ := hf M hM
  exact ⟨by rw [hk1, e1], e2.2 hk2⟩

/-- **Assembly of `S21EdgeBody`** from its parts. -/
theorem s21e_body_of_parts {s a β β₀ T : ℝ} {ρ : ℝ → Euc d → ℝ}
    (κ : ℝ → projTensor (OscPath d (wholeSpaceIndex d) T) 3) (εN : ℕ → ℝ)
    (hbd : ∃ Kb : ℝ, ∀ a₀ : ℝ, 0 ≤ a₀ → ‖κ a₀‖ ≤ Kb)
    (hsym : ∀ a₀ : ℝ, 0 ≤ a₀ → ∀ (σ : Equiv.Perm (Fin 3))
      (M : (OscPath d (wholeSpaceIndex d) T) [×3]→L[ℝ] ℝ),
      (κ a₀ : TensorDual (OscPath d (wholeSpaceIndex d) T) 3) (M.domDomCongr σ) =
        (κ a₀ : TensorDual (OscPath d (wholeSpaceIndex d) T) 3) M)
    (hlim : Tendsto εN atTop (𝓝 0))
    (hcross : ∀ a₀ : ℝ, 0 ≤ a₀ → HRS.MS.S21E.S21eCrossExist d s a β β₀ ρ T a₀)
    (hform : ∀ a₀ : ℝ, 0 ≤ a₀ → ∀ (τ : Fin 3 → Set.Icc (0 : ℝ) T) (φ : Fin 3 → Euc d → ℝ),
      (∀ i, IsOscTest (wholeSpaceIndex d) (φ i)) →
      ∃ χ : Fin 3 → ℝ → Euc d → ℝ, S21eChiClause d s a β β₀ ρ T a₀ τ φ χ ∧
        S21eFormulaFor d s a β β₀ ρ T a₀ (κ a₀) τ φ χ)
    (hexp : S21eExpansion d s a β β₀ ρ T κ εN) : S21EdgeBody d s a β β₀ T ρ := by
  refine ⟨κ, εN, hbd, hsym, hlim, ?_, hexp⟩
  intro a₀ ha₀ τ φ hφ
  refine ⟨hcross a₀ ha₀ τ φ hφ, fun χ hχ => ?_⟩
  obtain ⟨χ₀, h₀, hf⟩ := hform a₀ ha₀ τ φ hφ
  exact s21e_formula_universal h₀ hf hχ

end HRS.Whole
