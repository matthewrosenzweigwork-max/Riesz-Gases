import HRS.MS.R2GenInitAux35
import HRS.MS.GenPathAux65
import HRS.MS.GenPathAux52

/-!
# S10.5 window comparison, packet E2: measurability of the prescribed initial array; the first enlargement
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2GenInit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.GenPath

variable {d : ℕ}

theorem s105_hη (C : WholeCoeff d) (m q b T : ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (η₀ : Ω → (Euc d → ℝ) → ℝ) (Y : ℝ → Ω → OscDual d m)
    (hY : IsLinearFluctuationSolutionW P C m q (b + T) η₀ Y) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T)
    (hb : 0 ≤ b) (α : MultiIndex d) :
    AEMeasurable (fun ζ => η₀ ζ (propagatorW C 0 (b + u) (oscTestFun m α))) P := by
  have hut : b + u ∈ Set.Icc (0 : ℝ) (b + T) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  obtain ⟨hind, -⟩ := hY.gaussian_part 1 (fun _ => b + u) (fun _ => oscTestFun m α) (fun _ => hut)
    (fun _ => s56_isOscTest m α)
  simp only [OscDual.eval_oscTestFun] at hind
  have hind' := hind.comp (φ := fun v : EuclideanSpace ℝ (Fin 1) => v 0)
    (ψ := fun h : (Euc d → ℝ) → ℝ => h (propagatorW C 0 (b + u) (oscTestFun m α)))
    (by fun_prop) (@measurable_pi_apply (Euc d → ℝ) (fun _ => ℝ) _
      (propagatorW C 0 (b + u) (oscTestFun m α)))
  refine s56_aem_of_indep_sum P _ _ hind' ?_
  have hm : Measurable fun ω => (Y (b + u) ω).coord α :=
    (s56_continuous_coord m α).measurable.comp (hY.meas _)
  convert hm using 2 with ω
  simp

theorem s105_stage1 {D : WholeDyn d} {τ₀ : ℝ} {N : ℕ}
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : IsWholeStrongSolution P D τ₀ X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsWholeFilteredSolution P ℱ W' W X)
    (Ψc : Ω → (ℕ × MultiIndex d → ℝ)) (hΨ : AEMeasurable Ψc P) :
    ∃ (Ω₁ : Type) (mΩ₁ : MeasurableSpace Ω₁) (P₁ : Measure Ω₁) (_ : IsProbabilityMeasure P₁)
      (π₁ : Ω₁ → Ω) (_ : MeasurePreserving π₁ P₁ P) (ℱ₁ : Filtration ℝ mΩ₁)
      (c' : Ω₁ → (ℕ × MultiIndex d → ℝ)) (Ψt : Ω → (ℕ × MultiIndex d → ℝ)),
      Measurable Ψt ∧ Ψc =ᵐ[P] Ψt ∧
      IsWholeStrongSolution P₁ D τ₀ (fun z => X₀ (π₁ z)) (fun t z => W t (π₁ z))
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

end HRS.MS.R2GenInit
