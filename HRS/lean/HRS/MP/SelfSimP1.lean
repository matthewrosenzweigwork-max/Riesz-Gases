import HRS.MP.SelfSimP1Free
import HRS.MP.SelfSimP1Cepa

/-!
# S.A.28, packet P1: the filtered continuous version of the selected flow

Combination of the three alternatives of `SelectedFlowRd.flow`: the collision-free branch (`ss_P1_free`), the
Cépa-Lépingle branch (`ss_P1_cepa`), and the contact branch, which is void because `D.M = -1 ≠ 0`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.SelfSim
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.SelfSimP1

variable {d : ℕ}

/-- **P1**: the proof of `HRS.MP.SelfSim.ss_P1_filtered_version`. -/
theorem ss_P1_filtered_version_proof (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (N : ℕ)
    (hN : 2 ≤ N) (invβ : ℝ) (hβ : 0 < invβ) (T : ℝ) (hT : 0 < T)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : SelectedFlowRd P (⟨s, -1, fun _ => 0, invβ⟩ : WholeDyn d) T X₀ W X) :
    ∃ (X' : ℝ≥0 → Ω → EucConfig d N) (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
      (∀ t : ℝ≥0, (t : ℝ) ≤ T → X' t =ᵐ[P] X t) ∧ (∀ᵐ ζ ∂P, X' 0 ζ = X₀ ζ) ∧
      SSAddSol P invβ (fun _ Ξ i => particleDriftW (⟨s, -1, fun _ => 0, invβ⟩ : WholeDyn d) Ξ i)
        T ℱ W' W X' ∧
      (SSNoCollision P T X' ∨ (d = 1 ∧ s = 0 ∧ SSOrdered P T X')) := by
  rcases hX.flow with h | ⟨hd1, hs, -, -, hcepa⟩ | ⟨-, -, -, hM, -⟩
  · obtain ⟨X', ℱ, W', h1, h2, h3, h4⟩ := ss_P1_free hd s hs0 hsd N hN invβ hβ T hT P X₀ W X
      hX.init_meas hX.init_distinct hX.brownian hX.indep h
    exact ⟨X', ℱ, W', h1, h2, h3, Or.inl h4⟩
  · obtain ⟨X', ℱ, W', h1, h2, h3, h4⟩ := ss_P1_cepa s N invβ T hT P X₀ W X
      hX.init_meas hX.init_distinct hX.brownian hX.indep hd1 hs hcepa
    exact ⟨X', ℱ, W', h1, h2, h3, Or.inr ⟨hd1, hs, h4⟩⟩
  · exfalso
    have h0 : (-1 : Matrix (Fin d) (Fin d) ℝ) = 0 := hM
    have h1 := congrFun (congrFun h0 ⟨0, hd⟩) ⟨0, hd⟩
    simp at h1

example := (@ss_P1_filtered_version_proof : type_of% @HRS.MP.SelfSim.ss_P1_filtered_version)

end HRS.MP.SelfSimP1
