import HRS.Uniform.Q54cAux50

/-!
# Q54c, part 51: the core comparison theorem, all three metrics
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q54c

open HRS HRS.PDE HRS.Uniform

variable {d : ℕ}

namespace PdeSetup

theorem core_comparison_all (P : PdeSetup d) (cc : P.CmpConst) (hn2 : (d : ℝ) / 2 + 2 < (P.n : ℝ))
    (ν₀ : ℝ) (D₁ D₂ : DynData d) (μ₁ μ₂ : ℝ → Torus d → ℝ)
    (h₁ : P.Data D₁ ν₀ μ₁) (h₂ : P.Data D₂ ν₀ μ₂) (hM : D₁.M = D₂.M) (hV : D₁.V = D₂.V)
    (q₁ q₂ A₁ A₂ δ : ℝ) (hq₁ : 0 ≤ q₁) (hq₁1 : q₁ ≤ 1) (hq₂ : 0 ≤ q₂) (hA₁ : |A₁| ≤ 1)
    (hδ : ∀ r ∈ Set.Icc 0 P.T, Torus.cbNorm (P.n + 4) (μ₁ r - μ₂ r) ≤ δ)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (PΩ : Measure Ω) [IsProbabilityMeasure PΩ]
    (η₀ : Ω → NegSobolev d ((P.n : ℝ) + 2)) (hη₀ : Measurable η₀)
    (Y₁ Y₂ : ℝ → Ω → NegSobolev d ((P.n : ℝ) + 4))
    (hY₁ : IsLinearFluctuationSolution PΩ D₁ μ₁ ((P.n : ℝ) + 4) q₁ P.T
      (fun ω => A₁ • NegSobolev.embed ((P.n : ℝ) + 4) (η₀ ω)) Y₁)
    (hY₂ : IsLinearFluctuationSolution PΩ D₂ μ₂ ((P.n : ℝ) + 4) q₂ P.T
      (fun ω => A₂ • NegSobolev.embed ((P.n : ℝ) + 4) (η₀ ω)) Y₂) :
    let Δ : ℝ := |D₁.invβ - D₂.invβ| + |q₁ - q₂| + |A₁ - A₂| + δ
    let B : ℝ≥0∞ := ENNReal.ofReal (P.Ccore cc) * (1 + eLpNorm η₀ 2 PΩ) * ENNReal.ofReal (Δ + Real.sqrt Δ)
    wassersteinE 1 (law PΩ (toPath ((P.n : ℝ) + 4) P.T Y₁)) (law PΩ (toPath ((P.n : ℝ) + 4) P.T Y₂)) ≤ B ∧
    wassersteinE 2 (law PΩ (toPath ((P.n : ℝ) + 4) P.T Y₁)) (law PΩ (toPath ((P.n : ℝ) + 4) P.T Y₂)) ≤ B ∧
    ENNReal.ofReal (smoothDist 2 (law PΩ (toPath ((P.n : ℝ) + 4) P.T Y₁))
      (law PΩ (toPath ((P.n : ℝ) + 4) P.T Y₂))) ≤ B := by
  intro Δ B
  have hT : 0 < P.T := h₁.hA.hT
  have h2 := core_comparison P cc hn2 ν₀ D₁ D₂ μ₁ μ₂ h₁ h₂ hM hV q₁ q₂ A₁ A₂ δ hq₁ hq₁1 hq₂ hA₁ hδ PΩ η₀ hη₀
    Y₁ Y₂ hY₁ hY₂
  have hm₁ := aemeasurable_toPath hT.le PΩ Y₁ hY₁.meas hY₁.cont
  have hm₂ := aemeasurable_toPath hT.le PΩ Y₂ hY₂.meas hY₂.cont
  haveI : IsProbabilityMeasure (law PΩ (toPath ((P.n : ℝ) + 4) P.T Y₁)) :=
    (Measure.isProbabilityMeasure_map_iff hm₁).2 inferInstance
  haveI : IsProbabilityMeasure (law PΩ (toPath ((P.n : ℝ) + 4) P.T Y₂)) :=
    (Measure.isProbabilityMeasure_map_iff hm₂).2 inferInstance
  have h1 := (wassersteinE_one_le_two (law PΩ (toPath ((P.n : ℝ) + 4) P.T Y₁))
    (law PΩ (toPath ((P.n : ℝ) + 4) P.T Y₂))).trans h2
  refine ⟨h1, h2, ?_⟩
  refine (ENNReal.ofReal_le_ofReal (smoothDist_succ_le 1 _ _)).trans ?_
  exact (smoothDist_one_le_wasserstein _ _).trans h1

end PdeSetup

end HRS.Uniform.Q54c
