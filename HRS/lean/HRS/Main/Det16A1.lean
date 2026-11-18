import HRS.Energy.G336C1Final
import HRS.Energy.Commutator.CommonProof

/-!
# Example A.16, lemma L3: the pathwise energy bound for every completion constant above a threshold

At zero temperature the corrected energy along a strong solution is a.s. bounded, uniformly in `t ∈ [0,T]`,
by `exp (C T Λ') · (initial corrected energy)`, for every completion constant `C₀ ≥ C₀min`.
(`gronwall_zero_temperature_proof` is stated at one `C₀`; here the bound is lifted to all larger `C₀` with
`oNΛ_mono_C₀` and the transport bound `K ≥ 0`.)
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Main.Det16

variable {d : ℕ}

theorem det16_pathwise_energy (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀min C : ℝ, 0 ≤ C₀min ∧ 0 < C ∧ ∀ C₀ : ℝ, C₀min ≤ C₀ →
      ∀ (D : DynData d), D.s = s → D.invβ = 0 → Torus.SymNonpos D.M → Torus.IsCk 2 D.V →
      ∀ (N : ℕ), 2 ≤ N → ∀ (T : ℝ), 0 ≤ T →
      ∀ (ρ : ℝ → Torus d → ℝ) (r : ℕ) (Λ : ℝ), 3 ≤ r → 1 ≤ Λ →
        IsMeanFieldSolution D T ρ → IsRegularMF r Λ T ρ →
      ∀ Λ' : ℝ, (∀ t ∈ Set.Icc 0 T, HasTransportBound d s (meanFieldDrift D (ρ t)) Λ') →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsStrongSolution P D T X₀ W X →
        ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc 0 T,
          correctedEnergy D C₀ Λ ρ (X (Real.toNNReal t) ω) t ≤
            Real.exp (C * T * Λ') * correctedEnergy D C₀ Λ ρ (X 0 ω) 0 := by
  obtain ⟨C₀, C, hC₀, hC, hcc⟩ := commutator_coercivity_common_proof hd hs0 hsd
  refine ⟨C₀, C / 2, hC₀, half_pos hC, ?_⟩
  intro C₁ hC₁ D hDs hinv hS hV N hN T hT ρ r Λ hr hΛ hmf hregr Λ' hΛ' Ω _ P X₀ W X hsol
  have hΛ0 : 0 ≤ Λ := by linarith
  refine g336c1_ae_bound hd hC ?_ D hDs hinv hS hV hN hT hr hΛ hmf hregr hΛ' P X₀ W X hsol
  intro Λ hΛ N hN ρ hρ hρΛ X hX
  obtain ⟨h1, h2, -⟩ := hcc Λ hΛ N hN ρ hρ hρΛ X hX
  have hm : oNΛ d s C₀ Λ N ≤ oNΛ d s C₁ Λ N := oNΛ_mono_C₀ hC₁ (by linarith) N
  refine ⟨by linarith, fun v K hK => ?_⟩
  have hK0 := hK.nonneg
  refine (h2 v K hK).trans ?_
  have : 0 ≤ C * K := mul_nonneg hC.le hK0
  nlinarith

end HRS.Main.Det16
