import HRS.Uniform.Q54cAux57
import HRS.Uniform.Comparison

/-!
# Q54c, part 58: Corollary 3.26 `coefficient_comparison`, the proof
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q54c

open HRS HRS.PDE HRS.Uniform

variable {d : ℕ}

namespace PdeSetup

/-- `core_comparison_all` with the Sobolev levels and the horizon as variables -/
theorem core_comparison_all' (P : PdeSetup d) (cc : P.CmpConst) (hn2 : (d : ℝ) / 2 + 2 < (P.n : ℝ))
    (ν₀ : ℝ) (D₁ D₂ : DynData d) (μ₁ μ₂ : ℝ → Torus d → ℝ)
    (h₁ : P.Data D₁ ν₀ μ₁) (h₂ : P.Data D₂ ν₀ μ₂) (hM : D₁.M = D₂.M) (hV : D₁.V = D₂.V)
    (q₁ q₂ A₁ A₂ δ : ℝ) (hq₁ : 0 ≤ q₁) (hq₁1 : q₁ ≤ 1) (hq₂ : 0 ≤ q₂) (hA₁ : |A₁| ≤ 1)
    (hδ : ∀ r ∈ Set.Icc 0 P.T, Torus.cbNorm (P.n + 4) (μ₁ r - μ₂ r) ≤ δ)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (PΩ : Measure Ω) [IsProbabilityMeasure PΩ]
    (g2 g4 T' : ℝ) (hg2 : g2 = (P.n : ℝ) + 2) (hg4 : g4 = (P.n : ℝ) + 4) (hT' : T' = P.T)
    (η₀ : Ω → NegSobolev d g2) (hη₀ : Measurable η₀)
    (Y₁ Y₂ : ℝ → Ω → NegSobolev d g4)
    (hY₁ : IsLinearFluctuationSolution PΩ D₁ μ₁ g4 q₁ T'
      (fun ω => A₁ • NegSobolev.embed g4 (η₀ ω)) Y₁)
    (hY₂ : IsLinearFluctuationSolution PΩ D₂ μ₂ g4 q₂ T'
      (fun ω => A₂ • NegSobolev.embed g4 (η₀ ω)) Y₂) :
    let Δ : ℝ := |D₁.invβ - D₂.invβ| + |q₁ - q₂| + |A₁ - A₂| + δ
    let B : ℝ≥0∞ := ENNReal.ofReal (P.Ccore cc) * (1 + eLpNorm η₀ 2 PΩ) * ENNReal.ofReal (Δ + Real.sqrt Δ)
    wassersteinE 1 (law PΩ (toPath g4 T' Y₁)) (law PΩ (toPath g4 T' Y₂)) ≤ B ∧
    wassersteinE 2 (law PΩ (toPath g4 T' Y₁)) (law PΩ (toPath g4 T' Y₂)) ≤ B ∧
    ENNReal.ofReal (smoothDist 2 (law PΩ (toPath g4 T' Y₁)) (law PΩ (toPath g4 T' Y₂))) ≤ B := by
  subst hg2 hg4 hT'
  exact core_comparison_all P cc hn2 ν₀ D₁ D₂ μ₁ μ₂ h₁ h₂ hM hV q₁ q₂ A₁ A₂ δ hq₁ hq₁1 hq₂ hA₁ hδ PΩ η₀ hη₀
    Y₁ Y₂ hY₁ hY₂

end PdeSetup

theorem sigmaScale_nonneg' {N : ℕ} {κ invβ : ℝ} (hκ : 0 < κ) : 0 ≤ sigmaScale N κ invβ := by
  unfold sigmaScale
  split_ifs
  · exact hκ.le
  · exact le_min hκ.le (Real.sqrt_nonneg _)

theorem sigmaScale_le_kappa' {N : ℕ} {κ invβ : ℝ} : sigmaScale N κ invβ ≤ κ := by
  unfold sigmaScale
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem qScale_bounds {N : ℕ} (hN : 0 < N) {κ invβ : ℝ} (hκ : 0 < κ) (hβ : 0 ≤ invβ) :
    0 ≤ qScale N κ invβ ∧ qScale N κ invβ ≤ 1 := by
  unfold qScale
  by_cases h0 : invβ = 0
  · simp [h0]
  · simp only [h0, if_false]
    have hinv : 0 < invβ := lt_of_le_of_ne hβ (Ne.symm h0)
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hσ0 := sigmaScale_nonneg' (N := N) (invβ := invβ) hκ
    refine ⟨by positivity, ?_⟩
    have hσle : sigmaScale N κ invβ ≤ Real.sqrt (N / invβ) := by
      unfold sigmaScale
      simp only [h0, if_false]
      exact min_le_right _ _
    have hsq : sigmaScale N κ invβ ^ 2 ≤ N / invβ := by
      calc sigmaScale N κ invβ ^ 2 ≤ (Real.sqrt (N / invβ)) ^ 2 := pow_le_pow_left₀ hσ0 hσle 2
        _ = N / invβ := Real.sq_sqrt (by positivity)
    rw [div_le_one hNr]
    calc sigmaScale N κ invβ ^ 2 * invβ ≤ (N / invβ) * invβ :=
          mul_le_mul_of_nonneg_right hsq hinv.le
      _ = N := by field_simp

theorem Ascale_abs_le {N : ℕ} {κ invβ : ℝ} (hκ : 0 < κ) : |Ascale N κ invβ| ≤ 1 := by
  unfold Ascale
  by_cases h0 : invβ = 0
  · simp [h0]
  · simp only [h0, if_false]
    have hσ0 := sigmaScale_nonneg' (N := N) (invβ := invβ) hκ
    have hσκ := sigmaScale_le_kappa' (N := N) (κ := κ) (invβ := invβ)
    rw [abs_of_nonneg (div_nonneg hσ0 hκ.le), div_le_one hκ]
    exact hσκ

end HRS.Uniform.Q54c
