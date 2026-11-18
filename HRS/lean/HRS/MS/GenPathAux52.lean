import HRS.MS.GenPathAux51

/-!
# S5.6 packet P7i: stage 1, the initial-data enlargement carrying the coordinate array of the initial path
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole

variable {d : ℕ}

theorem s56_stage1 (b : WholeBounds d) (S : WholeSetup b) {N : ℕ}
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : IsWholeStrongSolution P (S.dyn N) b.T X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsWholeFilteredSolution P ℱ W' W X)
    (Ψc : Ω → (ℕ × MultiIndex d → ℝ)) (hΨ : AEMeasurable Ψc P) :
    ∃ (Ω₁ : Type) (mΩ₁ : MeasurableSpace Ω₁) (P₁ : Measure Ω₁) (_ : IsProbabilityMeasure P₁)
      (π₁ : Ω₁ → Ω) (_ : MeasurePreserving π₁ P₁ P) (ℱ₁ : Filtration ℝ mΩ₁)
      (c' : Ω₁ → (ℕ × MultiIndex d → ℝ)) (Ψt : Ω → (ℕ × MultiIndex d → ℝ)),
      Measurable Ψt ∧ Ψc =ᵐ[P] Ψt ∧
      IsWholeStrongSolution P₁ (S.dyn N) b.T (fun z => X₀ (π₁ z)) (fun t z => W t (π₁ z))
        (fun t z => X t (π₁ z)) ∧
      IsWholeFilteredSolution P₁ ℱ₁ (fun t z k => W' t (π₁ z) k) (fun t z => W t (π₁ z))
        (fun t z => X t (π₁ z)) ∧
      Measurable[ℱ₁ 0] c' ∧
      P₁.map (fun z => (X 0 (π₁ z), c' z)) = P.map (fun ζ => (X 0 ζ, Ψt ζ)) := by
  set Ψt : Ω → (ℕ × MultiIndex d → ℝ) := hΨ.mk Ψc with hΨt
  have hΨtm : Measurable Ψt := hΨ.measurable_mk
  have hX0ℱ : Measurable[ℱ 0] (X 0) := hF.adapted 0
  have hX0m : Measurable (X 0) := hX0ℱ.mono (ℱ.le 0) le_rfl
  haveI : Nonempty (ℕ × MultiIndex d → ℝ) := ⟨fun _ => 0⟩
  set K : Kernel (EucConfig d N) (ℕ × MultiIndex d → ℝ) := condDistrib Ψt (X 0) P with hK
  obtain ⟨Ω₁, mΩ₁, P₁, hP₁, π₁, hπ₁, ℱ₁, c', -, hF₁, hc'0, hlaw⟩ :=
    s56_init_enlargement N P X₀ W X ℱ W' hF hX.init K
  refine ⟨Ω₁, mΩ₁, P₁, hP₁, π₁, hπ₁, ℱ₁, c', Ψt, hΨtm, hΨ.ae_eq_mk, s56_strong_comp hπ₁ hX, hF₁, hc'0, ?_⟩
  have h1 : P₁.map (fun z => (X 0 (π₁ z), c' z)) = P₁.map (fun z => (X₀ (π₁ z), c' z)) := by
    refine Measure.map_congr ?_
    filter_upwards [hπ₁.quasiMeasurePreserving.ae hX.init] with z hz
    rw [hz]
  have h2 : P.map X₀ = P.map (X 0) := by
    refine Measure.map_congr ?_
    filter_upwards [hX.init] with z hz
    rw [hz]
  rw [h1, hlaw, h2]
  exact compProd_map_condDistrib hX0m.aemeasurable hΨtm.aemeasurable

end HRS.MS.GenPath
