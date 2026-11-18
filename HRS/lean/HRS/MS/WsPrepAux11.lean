import HRS.MS.WsPrepAux1
import HRS.MS.WsStatAux12

/-!
# S21R packet 11: measurability of the windows of the Gaussian comparator `Z`

`s21p_wpo_shift`: `windowPathOf m T a f = windowPathOf m T 0 (fun u => f (a + u))`.
`s21p_Z_window_aemeas`: if `Z` is a linear Gaussian evolution on the horizon `a₀ + T` (`a₀ ≥ 0`, `T ≥ 0`) then the window `processWindow m T a₀ Z`
is a.e. measurable (conjunct 2 of `S21PrepMain`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.Whole

variable {d : ℕ}

theorem s21p_wpo_shift (m T a : ℝ) (f : ℝ → OscDual d m) :
    windowPathOf m T a f = windowPathOf m T 0 (fun u => f (a + u)) := by
  unfold windowPathOf
  have h : (fun t : Set.Icc (0 : ℝ) T => f (a + (t : ℝ))) =
      (fun t : Set.Icc (0 : ℝ) T => f (a + (0 + (t : ℝ)))) := by
    funext t; rw [zero_add]
  exact HRS.GF.dite_continuousMap_congr _ _ h

theorem s21p_Z_window_aemeas {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') {C : WholeCoeff d}
    {m q : ℝ} {C₀ : (Euc d → ℝ) → (Euc d → ℝ) → ℝ} {Z : ℝ → Ω' → OscDual d m} {a₀ T : ℝ}
    (ha₀ : 0 ≤ a₀) (hT : 0 ≤ T) (hZ : IsLinearGaussianEvolutionW P' C m q (a₀ + T) C₀ Z) :
    AEMeasurable (processWindow m T a₀ Z) P' := by
  have hcont : ∀ᵐ ζ ∂P', ContinuousOn (fun u => Z (a₀ + u) ζ) (Icc 0 T) := by
    filter_upwards [hZ.cont] with ζ hζ
    refine hζ.comp (continuous_const.add continuous_id).continuousOn fun u hu => ?_
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have h := HRS.GF.gfb4_aemeasurable_windowPath P' hT (fun u ζ => Z (a₀ + u) ζ)
    (fun u _ => hZ.meas (a₀ + u)) hcont
  rw [← HRS.MS.GenPath.s56_wpo_eq_windowPath] at h
  have e : processWindow m T a₀ Z = fun ζ => windowPathOf m T 0 (fun u => Z (a₀ + u) ζ) := by
    funext ζ
    exact s21p_wpo_shift m T a₀ (fun t => Z t ζ)
  rw [e]
  exact h

end HRS.Whole
