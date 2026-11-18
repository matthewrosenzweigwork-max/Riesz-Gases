import HRS.Main.A8PAux51

/-!
# Packet A8P, part 52: a real semimartingale with nondegenerate noise has a null zero set
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

section ZeroSet

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {ι : Type*} [Fintype ι] {W : ℝ≥0 → Ω → ι → ℝ}

theorem a8p_ito_scalar' (hW : IsBrownianFiltration P ℱ W) {T : ℝ} (hT : 0 ≤ T) {ε : ℝ} (hε : 0 < ε)
    (σ : ι → ℝ) (X : ℝ≥0 → Ω → ℝ) (hX₀ : ∀ t : ℝ, Measurable[ℱ t] (X 0)) (b : ℝ≥0 → Ω → ℝ)
    (hb : IsProgressive ℱ (ofNNRealTime b))
    (hbint : ∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => b (Real.toNNReal s) ω) (Set.Icc 0 T))
    (hX : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      X t ω = X 0 ω + (∫ s in Set.Icc (0 : ℝ) t, b (Real.toNNReal s) ω) +
        ∑ k, (W t ω k - W 0 ω k) • σ k) :
    ∃ M : Ω → ℝ, Measurable M ∧
      ∫⁻ ω, ‖M ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal T * ENNReal.ofReal (∑ k, σ k ^ 2) ∧
      (∀ᵐ ω ∂P, ContinuousOn (fun s : ℝ => X (Real.toNNReal s) ω) (Set.Icc 0 T)) ∧
      ∀ᵐ ω ∂P, ((1 / 2) * ∑ k, σ k ^ 2) * ∫ s in Set.Icc (0 : ℝ) T,
          a8pG1'' ε (X (Real.toNNReal s) ω) ≤
        |X (Real.toNNReal T) ω - X 0 ω| + (∫ s in Set.Icc (0 : ℝ) T, |b (Real.toNNReal s) ω|) + |M ω| := by
  obtain ⟨Zt, M, hXt, hZc, hMm, hMV, hineq⟩ := a8p_ito_scalar hW hT hε σ X hX₀ b hb hbint hX
  refine ⟨M, hMm, hMV, ?_, ?_⟩
  · filter_upwards [hXt, hZc] with ω h1 h2
    exact (h2.continuousOn).congr h1
  · filter_upwards [hXt, hineq] with ω h1 h2
    have hT' : T ∈ Set.Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
    have h0' : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
    have e1 := h1 T hT'
    have e0 := h1 0 h0'
    rw [Real.toNNReal_zero] at e0
    rw [e1, e0]
    rw [setIntegral_congr_fun measurableSet_Icc (fun s hs => by rw [h1 s hs])] 
    exact h2

end ZeroSet

end HRS.Main.A8P
