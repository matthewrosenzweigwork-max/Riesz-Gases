import HRS.MC.CepE6aA8
import HRS.MC.CepaSpec

/-! Tie (statement check) for packet CEPE6A: the six conjuncts of `cep_E6_abcd` are literally the first six conjuncts of the
spec theorem `cep_E6_limit_solution`.  Moved here from `CepE6aA8.lean` so that the proof chain does not import the spec. -/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE6A

open HRS HRS.MC.Cepa HRS.MC.CepE4

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

/-- Statement check: the six conjuncts above are literally the first six conjuncts of `cep_E6_limit_solution`. -/
example [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ})
    {a : ℝ} (ha : 0 < a) {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida a N J)
    {F : Ch N → Ch N} {L : ℝ≥0} (hF : LipschitzWith L F) (σ' : ℝ)
    {z₀ : Ω → Ch N} (hz₀ : Measurable[ℱ 0] z₀) (hz₀A : ∀ ω, z₀ ω ∈ cep_Alcove N)
    (hz₀b : ∃ R : ℝ, ∀ ω, ‖z₀ ω‖ ≤ R)
    {Z : ℕ → ℝ → Ω → Ch N}
    (hZ : ∀ n : ℕ, 1 ≤ n → cep_IsChamberSolution P ℱ W' π σ'
      (fun z => -((n : ℝ) • (z - J n z)) + F z) z₀ (Z n)) :
    ∃ Zl : ℝ → Ω → Ch N, (∀ ω, Continuous fun t => Zl t ω) ∧ (∀ t, 0 ≤ t → Measurable[ℱ t] (Zl t)) ∧
      (∀ T : ℝ, ∀ ε : ℝ, 0 < ε → Filter.Tendsto (fun n : ℕ =>
        P {ω | ε < ⨆ t : Set.Icc (0 : ℝ) T, ‖Z n t ω - Zl t ω‖}) Filter.atTop (𝓝 0)) ∧
      (∀ᵐ ω ∂P, ∀ t, 0 ≤ t → Zl t ω ∈ closure (cep_Alcove N)) ∧
      (∀ᵐ ω ∂P, ∀ T : ℝ, volume {s : ℝ | s ∈ Set.Icc 0 T ∧ Zl s ω ∉ cep_Alcove N} = 0) ∧
      (∀ᵐ ω ∂P, ∀ T : ℝ, IntegrableOn (fun s : ℝ => ‖gradient (cep_chamberPot a N) (Zl s ω)‖) (Set.Icc 0 T)) := by
  obtain ⟨Zl, h1, h2, h3, h4, h5, h6, -⟩ := cep_E6_limit_solution hW' hπ ha hJ hF σ' hz₀ hz₀A hz₀b hZ
  exact ⟨Zl, h1, h2, h3, h4, h5, h6⟩

end HRS.MC.CepE6A
