import HRS.Energy.Coercivity
import HRS.Energy.Commutator.Assembly

/-!
# Propositions 3.32 and 3.33 with a common `C₀`, relocated

`HRS.commutator_coercivity_common` (Coercivity.lean) is proved from the frozen `HRS.commutator_estimate`, which keeps a
`sorry` because its proof `HRS.Commutator.commutator_estimate_of_packets` (Energy/Commutator/Assembly.lean, type_of% tie)
cannot be imported into Coercivity.lean (import cycle).  This file repeats the proof verbatim with the proved
`commutator_estimate_of_packets` in place of the frozen statement, as `commutator_coercivity_common_proof`, tied to the
frozen statement by `type_of%`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

theorem commutator_coercivity_common_proof (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (Λ : ℝ), 1 ≤ Λ → ∀ (N : ℕ), 2 ≤ N →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
        0 ≤ rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N ∧
        (∀ (v : Torus d → Euc d) (K : ℝ), HasTransportBound d s v K →
          |commQuantity d s v X (withDensityReal ρ)| ≤
            C * K * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N)) ∧
        (∀ (ψ : Torus d → ℝ) (L : ℝ), 0 ≤ L → KernelGrad.IsLipschitz L ψ →
          HasFiniteHomSobolev (((d : ℝ) - s) / 2) ψ →
          |∫ x, ψ x ∂(empirical X) - ∫ x, ψ x ∂(withDensityReal ρ)| ≤
            C * L * smearScale d N Λ +
              C * homSobolev (((d : ℝ) - s) / 2) ψ *
                Real.sqrt (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N)) := by
  obtain ⟨A₀, A, hA₀, hA, hcomm⟩ := HRS.Commutator.commutator_estimate_of_packets hd hs0 hsd
  obtain ⟨B₀, B, hB₀, hB, hcoer⟩ := periodic_coercivity hd hs0 hsd
  refine ⟨max A₀ B₀, max A B, le_max_of_le_left hA₀, lt_max_of_lt_left hA, ?_⟩
  intro Λ hΛ N hN ρ hρ hρΛ X hX
  have hΛ0 : 0 ≤ Λ := by linarith
  obtain ⟨hlow, htest⟩ := hcoer Λ hΛ N hN ρ hρ hρΛ X hX
  have hoB : oNΛ d s B₀ Λ N ≤ oNΛ d s (max A₀ B₀) Λ N :=
    oNΛ_mono_C₀ (le_max_right _ _) hΛ0 N
  have hoA : oNΛ d s A₀ Λ N ≤ oNΛ d s (max A₀ B₀) Λ N :=
    oNΛ_mono_C₀ (le_max_left _ _) hΛ0 N
  have hlow' : 0 ≤ rieszEnergy d s X (withDensityReal ρ) + oNΛ d s (max A₀ B₀) Λ N := by
    linarith
  refine ⟨hlow', ?_, ?_⟩
  · intro v K hK
    have hK0 := hK.nonneg
    have h1 := (hcomm Λ hΛ N hN ρ hρ hρΛ X hX v K hK).2
    refine h1.trans ?_
    have hAK : 0 ≤ A * K := mul_nonneg hA.le hK0
    calc A * K * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s A₀ Λ N)
        ≤ A * K * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s (max A₀ B₀) Λ N) :=
          mul_le_mul_of_nonneg_left (by linarith) hAK
      _ ≤ max A B * K * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s (max A₀ B₀) Λ N) := by
          apply mul_le_mul_of_nonneg_right _ hlow'
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hK0
  · intro ψ L hL hψ hfin
    refine (htest ψ L hL hψ hfin).trans ?_
    have hsm : 0 ≤ smearScale d N Λ :=
      Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg N) hΛ0) _
    have hhs : 0 ≤ homSobolev (((d : ℝ) - s) / 2) ψ := Real.sqrt_nonneg _
    have hsq : Real.sqrt (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s B₀ Λ N) ≤
        Real.sqrt (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s (max A₀ B₀) Λ N) :=
      Real.sqrt_le_sqrt (by linarith)
    have hAB : B ≤ max A B := le_max_right _ _
    have hsq0 := Real.sqrt_nonneg (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s B₀ Λ N)
    have e1 : B * smearScale d N Λ * L ≤ max A B * L * smearScale d N Λ := by
      nlinarith [mul_nonneg hsm hL]
    have e2 : B * homSobolev (((d : ℝ) - s) / 2) ψ *
        Real.sqrt (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s B₀ Λ N) ≤
        max A B * homSobolev (((d : ℝ) - s) / 2) ψ *
        Real.sqrt (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s (max A₀ B₀) Λ N) := by
      apply mul_le_mul _ hsq hsq0 (mul_nonneg (hA.le.trans (le_max_left _ _)) hhs)
      exact mul_le_mul_of_nonneg_right hAB hhs
    linarith

example := (@commutator_coercivity_common_proof : type_of% @HRS.commutator_coercivity_common)

end HRS
