import HRS.MS.R2S11Aux19

/-!
# S11.2 (a): from the conclusion of S11.1 plus a Banach Gaussian comparison and the norm bound of the stationary cubic tensor

`s11_partA_of_h11`: part (a) of `r2_two_parameter_edgeworth` (constants `c, C'` chosen before `ρβ`) follows from
* `h11 : type_of% (r2_tensor_relaxation ..)` (S11.1),
* `hG : S11GaussCompare ..` the Gaussian covariance interpolation `|E F(Z₁) - E F(Z₂)| ≤ ½ sup‖D²F‖ · ‖Cov₁ - Cov₂‖_π` on `C([0,T]; B_m)`
  for two `IsLinearGaussianEvolutionW` windows (a true statement; only the Euclidean/trace-norm version A.31 is in the library; plan packet G),
* `hK : S11KappaBound ..` a uniform bound for `‖κ_β‖_π` (true: `ρ_β` and `κ_β` are unique; plan packet K).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2S11

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

/-- Part (a) of `r2_two_parameter_edgeworth`. -/
def S11PartA (d : ℕ) (s a β γ T lam : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ →
    IsR2Poincare (HRS.Whole.withDensityReal ρβ) lam →
    ∀ (κγ : ℝ → projTensor (R2X d T) 3) (κβ : projTensor (R2X d T) 3),
      (∀ u : ℝ, 0 ≤ u → IsR2PathCubic d s a β γ ρβ T u (κγ u)) → IsR2PathCubic d s a β β ρβ T 0 κβ →
      ∀ {Ω' Ω'' : Type} [MeasurableSpace Ω'] [MeasurableSpace Ω''] (P' : Measure Ω') (P'' : Measure Ω'')
        [IsProbabilityMeasure P'] [IsProbabilityMeasure P''] (Zγ : ℝ → Ω' → OscDual d (wholeSpaceIndex d : ℝ))
        (Zβ : ℝ → Ω'' → OscDual d (wholeSpaceIndex d : ℝ)),
      (∀ T' : ℝ, IsLinearGaussianEvolutionW P' ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ))
        (wholeSpaceIndex d) β⁻¹ T' (HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal ρβ) γ) Zγ) →
      (∀ T' : ℝ, IsLinearGaussianEvolutionW P'' ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ))
        (wholeSpaceIndex d) β⁻¹ T' (HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal ρβ) β) Zβ) →
      (∀ {N : ℕ}, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
        (εN : ℝ),
        IsR2Realization d s a β P X₀ W X →
        law P X₀ = HRS.Whole.modulatedGibbs (rieszKernel d s) N γ (HRS.Whole.withDensityReal ρβ) →
        (∀ u : ℝ, 0 ≤ u → ∀ Φ ∈ CbUnitBall (R2X d T) 5,
          |Real.sqrt N * (∫ ζ, Φ (zetaPathW (wholeSpaceIndex d) T u P X ζ) ∂P -
              ∫ ζ, Φ (processWindow (wholeSpaceIndex d) T u Zγ ζ) ∂P') -
            (1 / 6) * r2CubicExpect P' (processWindow (wholeSpaceIndex d) T u Zγ) (κγ u) Φ| ≤ εN) →
        ∀ u : ℝ, 0 ≤ u → ∀ Φ ∈ CbUnitBall (R2X d T) 5,
          |∫ ζ, Φ (zetaPathW (wholeSpaceIndex d) T u P X ζ) ∂P -
              ∫ ζ, Φ (processWindow (wholeSpaceIndex d) T 0 Zβ ζ) ∂P'' -
            (1 / (6 * Real.sqrt N)) * r2CubicExpect P'' (processWindow (wholeSpaceIndex d) T 0 Zβ) κβ Φ| ≤
            εN / Real.sqrt N + C * Real.exp (-2 * (lam / β) * u) +
              C / Real.sqrt N * Real.exp (-c * u))

/-- Gaussian covariance interpolation on the window space. -/
def S11GaussCompare (d : ℕ) (s a β γ T lam : ℝ) : Prop :=
  ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → IsR2Poincare (HRS.Whole.withDensityReal ρβ) lam →
    ∀ (F : R2X d T → ℝ), ContDiff ℝ 2 F → ∀ Mbd δ : ℝ, (∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ Mbd) →
    ∀ {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] (P₁ : Measure Ω₁) (P₂ : Measure Ω₂)
      [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] (Z₁ : ℝ → Ω₁ → OscDual d (wholeSpaceIndex d : ℝ))
      (Z₂ : ℝ → Ω₂ → OscDual d (wholeSpaceIndex d : ℝ)),
      (∀ T' : ℝ, IsLinearGaussianEvolutionW P₁ ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ))
        (wholeSpaceIndex d) β⁻¹ T' (HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal ρβ) γ) Z₁) →
      (∀ T' : ℝ, IsLinearGaussianEvolutionW P₂ ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ))
        (wholeSpaceIndex d) β⁻¹ T' (HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal ρβ) β) Z₂) →
      ∀ u : ℝ, 0 ≤ u →
      (∀ M : (R2X d T) [×2]→L[ℝ] ℝ, ‖M‖ ≤ 1 →
        |∫ ζ, M ![processWindow (wholeSpaceIndex d) T u Z₁ ζ, processWindow (wholeSpaceIndex d) T u Z₁ ζ] ∂P₁ -
          ∫ ζ, M ![processWindow (wholeSpaceIndex d) T 0 Z₂ ζ, processWindow (wholeSpaceIndex d) T 0 Z₂ ζ] ∂P₂| ≤ δ) →
      |∫ ζ, F (processWindow (wholeSpaceIndex d) T u Z₁ ζ) ∂P₁ -
          ∫ ζ, F (processWindow (wholeSpaceIndex d) T 0 Z₂ ζ) ∂P₂| ≤ 1 / 2 * Mbd * δ

/-- A uniform bound for the projective norm of the stationary cubic tensor. -/
def S11KappaBound (d : ℕ) (s a β γ T lam : ℝ) : Prop :=
  ∃ K : ℝ, ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → IsR2Poincare (HRS.Whole.withDensityReal ρβ) lam →
    ∀ κβ : projTensor (R2X d T) 3, IsR2PathCubic d s a β β ρβ T 0 κβ → ‖κβ‖ ≤ K

theorem s11_alg {s p q r t εN δ C e1 e2 K0 : ℝ} (hs : 1 ≤ s) (hp : |p| ≤ εN) (hq : |q| ≤ δ / 2)
    (hr : |r| ≤ C * e2) (ht : |t| ≤ K0 * δ / 2) (hδ : δ = C * e1) (hC : 0 ≤ C) (hK0 : 0 ≤ K0)
    (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) :
    |p / s + q + r / (6 * s) + t / (6 * s)| ≤ εN / s + C * (1 + K0) * e1 + C * (1 + K0) / s * e2 := by
  have hs0 : 0 < s := by linarith
  have h1 : |p / s| ≤ εN / s := by
    rw [abs_div, abs_of_pos hs0]; exact div_le_div_of_nonneg_right hp hs0.le
  have h2 : |r / (6 * s)| ≤ C * (1 + K0) / s * e2 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 6 * s)]
    rw [div_le_iff₀ (by positivity)]
    have : C * (1 + K0) / s * e2 * (6 * s) = 6 * (C * (1 + K0) * e2) := by field_simp
    rw [this]
    have hce : 0 ≤ C * e2 := mul_nonneg hC he2
    nlinarith [mul_nonneg hce hK0]
  have h3 : |t / (6 * s)| ≤ K0 * δ / 12 := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 6 * s), div_le_iff₀ (by positivity)]
    have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
    have : K0 * δ / 12 * (6 * s) = K0 * δ / 2 * s := by ring
    rw [this]
    nlinarith [mul_nonneg hK0 hδ0]
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  calc |p / s + q + r / (6 * s) + t / (6 * s)|
      ≤ |p / s| + |q| + |r / (6 * s)| + |t / (6 * s)| := by
        have t1 := abs_add_le (p / s + q + r / (6 * s)) (t / (6 * s))
        have t2 := abs_add_le (p / s + q) (r / (6 * s))
        have t3 := abs_add_le (p / s) q
        linarith
    _ ≤ εN / s + δ / 2 + C * (1 + K0) / s * e2 + K0 * δ / 12 := by linarith
    _ ≤ _ := by
        rw [hδ]
        have : 0 ≤ C * e1 * K0 := by positivity
        nlinarith [mul_nonneg hC he1]

end HRS.MS.R2S11
