import HRS.Main.ThermLinAux7
import HRS.Uniform.Q48bAux1
import HRS.Sections.AdjKGlue
import HRS.Sections.AdjKAFinal

/-!
# THERMLIN, part 8: the stationary trajectory and the stationary evolution package (lemmas A3, A4 of `ThermLinAux6`)
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.ThermLin

variable {d : ℕ}

/-- A3: the constant path `ρ^t ≡ ρβ` is an `IsSmoothPositiveTrajectory` for the potential `S.V` at inverse temperature
`S.β` (it is a global `H^K` solution, `Q48b.q48b_isMFSolutionHK`). -/
theorem thermlin_stationary_traj (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) :
    IsSmoothPositiveTrajectory d S.s S.β S.V ρβ (fun _ => ρβ) := by
  obtain ⟨hsm, hpos⟩ := thermlin_thermal_smooth_pos S h
  have hd1 : 1 ≤ d := by have := S.hd; omega
  refine ⟨S.hs0, S.hsd, S.hβ, S.hV, ⟨h.1, hsm, hpos⟩, fun K hK => ?_⟩
  exact ⟨fun _ => PDE.coeffOf ρβ,
    HRS.Uniform.Q48b.q48b_isMFSolutionHK hd1 S.s S.hs0 S.hsd S.β S.hβ S.V S.hV ρβ h hsm hpos K,
    fun t _ => congrFun (HRS.Uniform.Q48b.q48b_mfPath_const ρβ hsm) t⟩

/-- A4: the stationary dual evolution at every real level `r`, with decay. -/
theorem thermlin_stationary_evolution (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (r : ℝ) :
    ∃ Cr cr : ℝ, 0 < Cr ∧ 0 < cr ∧
      ∃ W : ℝ → ℝ → NegSobolev d r →L[ℝ] NegSobolev d r,
        HRS.Uniform.IsDualEvolution (thermlin_stationary_traj S h).dyn (fun _ => ρβ) r W ∧
        (∀ T : ℝ, 0 ≤ T → HRS.Uniform.IsPlainEvolution W T) ∧
        ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖W t u‖ ≤ Cr * Real.exp (-cr * (t - u)) := by
  obtain ⟨Cr, cr, hCr, hcr, W, hW, hp, hdec, -⟩ :=
    HRS.AdjK.adjk_evolution_along_trajectory S.hd (thermlin_stationary_traj S h) r
  exact ⟨Cr, cr, hCr, hcr, W, hW, hp, hdec⟩

end HRS.ThermLin
