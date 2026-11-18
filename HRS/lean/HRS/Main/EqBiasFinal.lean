import HRS.Main.Equilibrium29Spec
import HRS.Main.EqBiasAux2
import HRS.Main.EqBiasAux15

/-!
# EQ-BIAS / EQ-POS: final theorems (relocated proofs; statements verbatim from
`HRS/Main/Equilibrium29Spec.lean`, tied to the originals by `type_of%`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

/-- `supercriticalBias_pos` (verbatim statement of `HRS.Main.supercriticalBias_pos`). -/
theorem supercriticalBias_pos_proof (hd : 2 ≤ d) {s : ℝ} (hs1 : (d : ℝ) / 2 < s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hnc : ∃ x y, ρβ x ≠ ρβ y) :
    0 < supercriticalBias d s β ρβ ρβ := by
  obtain ⟨hs0, hp1, hp2⟩ := eqbias_p_range hs1 hsd hd
  have hρs := eqbias_smoothPos hd hs0.le hsd V hV β hβ ρβ hρβ
  have hint := eqbias_bias_pos hd hs0.le hsd hρs hβ.le hnc
  unfold supercriticalBias
  have hA : 0 < sphereArea d := HRS.StaticLimitsAux.sphereArea_pos hd
  have hG : 0 < Real.Gamma (2 - d / s) := Real.Gamma_pos_of_pos (by linarith)
  have hB : 0 < β ^ ((d : ℝ) / s) := Real.rpow_pos_of_pos hβ _
  have hden : 0 < s * (d / s) * (d / s - 1) := by
    have : 0 < (d : ℝ) / s - 1 := by linarith
    have : 0 < (d : ℝ) / s := by linarith
    positivity
  have hc : 0 < sphereArea d * Real.Gamma (2 - d / s) / (s * (d / s) * (d / s - 1)) :=
    div_pos (mul_pos hA hG) hden
  exact mul_pos (mul_pos hc hB) hint

example := (@supercriticalBias_pos_proof : type_of% @HRS.Main.supercriticalBias_pos)

/-- `equilibrium_bias_expansion` (verbatim statement of `HRS.Main.equilibrium_bias_expansion`). -/
theorem equilibrium_bias_expansion_proof (hd : 2 ≤ d) {s : ℝ} (hs1 : (d : ℝ) / 2 < s)
    (hsd : s < d) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β)
    (ρβ : Torus d → ℝ) (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) :
    (∀ N : ℕ, 2 ≤ N →
      firstMarginal (canonicalGibbs (periodicRiesz d s) V N β) ≪ withDensityReal ρβ) ∧
    Tendsto (fun N : ℕ =>
      eLpNorm (fun y =>
        (((firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)).rnDeriv
            (withDensityReal ρβ) y).toReal - 1) / (N : ℝ) ^ (1 - (d : ℝ) / s) -
          supercriticalBiasDensity d s β ρβ y) 2 (withDensityReal ρβ)) atTop (𝓝 0) := by
  obtain ⟨hs0, hp1, hp2⟩ := eqbias_p_range hs1 hsd hd
  have hρs := eqbias_smoothPos hd hs0.le hsd V hV β hβ ρβ hρβ
  have hcan := fun N => eqbias_canonical hd hs0.le hsd V β ρβ hρs hρβ N
  have hD := eqbias_hD hd hs1 hsd hβ hρs
  obtain ⟨hac, hlim⟩ := eqbias_tendsto_of_D hd hs1 hsd hβ hρs hD
  have hdens : ∀ y, supercriticalBiasDensity d s β ρβ y =
      (eqbias_c0 d s * β ^ ((d : ℝ) / s)) *
        responseInverse (periodicRiesz d s) (withDensityReal ρβ) β ρβ y := by
    intro y
    unfold supercriticalBiasDensity eqbias_c0
    ring
  refine ⟨fun N hN => ?_, ?_⟩
  · rw [hcan N]; exact hac N hN
  · simp only [hcan, hdens]
    exact hlim

example := (@equilibrium_bias_expansion_proof : type_of% @HRS.Main.equilibrium_bias_expansion)

end Main

end HRS

end
