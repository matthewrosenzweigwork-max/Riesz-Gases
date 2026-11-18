import HRS.Sections.AdjKAAux4

/-!
# ADJKA part 5: the quasi-contractive dual evolution along a trajectory (`LevelInput` transported to `ρ`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.AdjK

open HRS.Uniform

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

/-- `LevelInput` (dual evolution, plain, quasi-contractive, decaying) transported from `mfPath ρc` to `ρ`. -/
theorem adjka_levelInput_traj (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (r : ℝ) :
    ∃ Vev : ℝ → ℝ → NegSobolev d r →L[ℝ] NegSobolev d r,
      IsDualEvolution htr.dyn ρ r Vev ∧ (∀ T : ℝ, 0 ≤ T → IsPlainEvolution Vev T) ∧
      (∃ c : ℝ, ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Real.exp (c * (t - u))) ∧
      ∃ Cr cr : ℝ, 0 < Cr ∧ 0 < cr ∧ ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Cr * Real.exp (-cr * (t - u)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨K₀, hK₀⟩ := Q54.exists_levelInput hd1 s htr.hs0 htr.hsd r
  set K : ℕ := max K₀ (⌊(d : ℝ) / 2 + 6⌋₊ + 1) with hK
  have hKgt : (d : ℝ) / 2 + 6 < K := by
    have h1 : (d : ℝ) / 2 + 6 < ((⌊(d : ℝ) / 2 + 6⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast; exact Nat.lt_floor_add_one _
    exact h1.trans_le (by exact_mod_cast le_max_right _ _)
  have H := Q40b.q40b_finiteRegHyp htr hKgt
  obtain ⟨ρc, hρc, hρ⟩ := htr.global K hKgt
  obtain ⟨Vev, hdual, hplain, hq, hdec⟩ := hK₀ K (le_max_left _ _) β htr.hβ V ρ₀ H ρc hρc
  refine ⟨Vev, ?_, hplain, hq, hdec⟩
  intro u t hu hut z φ hφ
  rw [hdual u t hu hut z φ hφ]
  congr 1
  funext x
  have := Q40b.q40b_propagator_congr (D := htr.dyn) (ρ := PDE.mfPath ρc) (ρ' := ρ) (t := t)
    (fun r hr => hρ r hr.1) u φ
  exact congrFun this x

end HRS.AdjK
