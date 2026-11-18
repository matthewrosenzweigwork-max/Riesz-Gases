import HRS.Main.Lattice39FinalSpec

/-!
# Example A.39, final form: glue of `EnergySmallness` (G)

`lattice39f_energySmallness_glue_proof`: the lattice part and the off-lattice part of the energy package
assemble into `EnergySmallness` for `𝔈' N = if N ∈ lat then 𝔈L N else 𝔈 N`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory BoundedContinuousFunction

namespace HRS

namespace Main

variable {d : ℕ}

open Classical in
theorem lattice39f_energySmallness_glue_proof (S : MainData d) (R : ∀ N, Realization d N) (C₀ Cc Λ : ℝ)
    (lat : Set ℕ) (𝔈 𝔈L : ℕ → ℝ) (hC : IsCoercivityPair d S.s C₀ Cc)
    (hpos : ∀ N : ℕ, 1 ≤ N → N ∉ lat → 0 < 𝔈 N)
    (hbd : ∀ N : ℕ, 1 ≤ N → N ∉ lat → ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      ∫⁻ ω, ENNReal.ofReal
          (correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) ((R N).X (Real.toNNReal t) ω) t) ∂(R N).P ≤
        ENNReal.ofReal (𝔈 N))
    (hsm : Tendsto (Set.indicator latᶜ (fun N : ℕ => S.sigma N * 𝔈 N)) atTop (𝓝 0))
    (hposL : ∀ N : ℕ, 1 ≤ N → N ∈ lat → 0 < 𝔈L N)
    (hbdL : ∀ N : ℕ, 1 ≤ N → N ∈ lat → ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      ∫⁻ ω, ENNReal.ofReal
          (correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) ((R N).X (Real.toNNReal t) ω) t) ∂(R N).P ≤
        ENNReal.ofReal (𝔈L N))
    (hsmL : Tendsto (Set.indicator lat (fun N : ℕ => S.sigma N * 𝔈L N)) atTop (𝓝 0)) :
    EnergySmallness S R C₀ Cc Λ (fun N => if N ∈ lat then 𝔈L N else 𝔈 N) := by
  refine ⟨hC, ?_, ?_, ?_⟩
  · intro N hN
    by_cases h : N ∈ lat
    · simp only [h, if_true]; exact hposL N hN h
    · simp only [h, if_false]; exact hpos N hN h
  · intro N hN t ht
    by_cases h : N ∈ lat
    · simp only [h, if_true]; exact hbdL N hN h t ht
    · simp only [h, if_false]; exact hbd N hN h t ht
  · have hadd := hsmL.add hsm
    rw [add_zero] at hadd
    refine hadd.congr fun N => ?_
    by_cases h : N ∈ lat
    · simp [Set.indicator, h]
    · simp [Set.indicator, h]

example := (@lattice39f_energySmallness_glue_proof : type_of% @lattice39f_energySmallness_glue)

end Main

end HRS
