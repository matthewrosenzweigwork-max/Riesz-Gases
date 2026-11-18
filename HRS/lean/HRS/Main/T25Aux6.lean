import HRS.Main.T25Aux1
import HRS.Main.GFSpec1

/-!
# T25-IN, part 6 (BRIDGES): `MovHyp`, window paths

* `t25_movHyp`: `SelectedFlow` of `S.dyn` on `[0,T]` + filtered solution ⇒ `MovHyp P S.dyn N T S.ρ X₀ W X` (bridges A, D of the MOV
  glue: `movlog_traj`, `movT_hyp_of_parts`).
* `t25_windowPath_eq`: the window `Main.windowPath m T a Y` of a linear process is `Uniform.windowPath a T Y`, the object of
  Proposition 3.28 (`comparison_smooth`, `comparison_wasserstein`).
* `t25_windowFluc_eq`: the window `Main.windowFluc m T a σ X ρ` of the fluctuation path is `Uniform.windowPath a T` of the process
  `flucProc m σ X ρ`, for `a ≥ 0` (`toNNReal (a + t) = toNNReal a + t`).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace T25

open HRS.Main

variable {d : ℕ}

/-- Bridge: `SelectedFlow` + filtered solution ⇒ `MovHyp` on the horizon. -/
theorem t25_movHyp (S : PreparedData d) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : ℝ}
    {N : ℕ} {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hF : SelectedFlow P S.dyn T X₀ W X)
    (hfilt : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
      (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) :
    MovHyp P S.dyn N T S.ρ X₀ W X :=
  movT_hyp_of_parts (MovLog.movlog_traj (t25_traj S) T) hF.brownian hF.indep
    (t25_isParticleSystem S hF).sol hfilt

/-- The window of a linear process is the `Uniform.windowPath` of Proposition 3.28. -/
theorem t25_windowPath_eq {Ω : Type*} (m T a : ℝ) (Y : ℝ → Ω → NegSobolev d m) (ω : Ω) :
    windowPath m T a Y ω = (Uniform.windowPath a T Y ω : PathSpace d m T) := by
  unfold windowPath Uniform.windowPath
  rw [GF.toPath_eq_windowPath]
  unfold Uniform.windowPath
  exact GF.dite_continuousMap_congr _ _ (funext fun t => by simp)

/-- The window of the fluctuation path is the `Uniform.windowPath` of the process `flucProc`. -/
theorem t25_windowFluc_eq {Ω : Type*} {N : ℕ} (m T a σ : ℝ) (ha : 0 ≤ a) (X : ℝ≥0 → Ω → Config d N)
    (ρ : ℝ → Torus d → ℝ) (ω : Ω) :
    windowFluc m T a σ X ρ ω = (Uniform.windowPath a T (GF.flucProc m σ X ρ) ω : PathSpace d m T) := by
  unfold windowFluc flucPath Uniform.windowPath
  refine GF.dite_continuousMap_congr _ _ (funext fun t => ?_)
  have ht : 0 ≤ (t : ℝ) := t.2.1
  simp only [GF.flucProc]
  rw [Real.toNNReal_add ha ht]

end T25

end HRS

end
