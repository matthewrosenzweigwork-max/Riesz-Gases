import HRS.MS.WsPrepAux14
import HRS.MS.WsStatAux37

/-!
# S21R packet 15: the law of a window of the Gaussian comparator is a convolution

`s21p_Zwin_law`: let `Z` be a linear Gaussian evolution on the horizon `a₀ + T` (`IsLinearGaussianEvolutionW`, noise level `q`, initial form `C₀`)
and let `γ0`, `Γ` be probability measures on the path space `C([0,T];B_m)` whose finite-dimensional coordinate laws are the centered Gaussians
with the covariances of the transported initial form `C₀(U^{0,a₀+t}φ_α, U^{0,a₀+t'}φ_{α'})` and of the noise `noiseCovW C q (a₀+t) (a₀+t')`
respectively (both positive semidefinite).  Then `law (processWindow m T a₀ Z) = γ0 * Γ` (convolution).  This is `s21_Zlaw` (WsStatAux31, the
window `a = 0`) applied to the shifted process `u ↦ Z (a₀ + u)`; it identifies the comparator side of every window estimate of S2.1 (ii).
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.Whole

variable {d : ℕ}

theorem s21p_Zwin_law {m q T a₀ : ℝ} (hT : 0 ≤ T) (ha₀ : 0 ≤ a₀) {Ω' : Type} [MeasurableSpace Ω']
    (P' : Measure Ω') [IsProbabilityMeasure P'] {C : WholeCoeff d}
    {C₀ : (Euc d → ℝ) → (Euc d → ℝ) → ℝ} {Z : ℝ → Ω' → OscDual d m}
    (hZ : IsLinearGaussianEvolutionW P' C m q (a₀ + T) C₀ Z)
    (γ0 Γ : Measure (OscPath d m T)) [IsProbabilityMeasure γ0] [IsProbabilityMeasure Γ]
    (hγ : ∀ (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T) (αs : Fin p → MultiIndex d),
      (Matrix.of fun a c => C₀ (propagatorW C 0 (a₀ + ts a) (oscTestFun m (αs a)))
          (propagatorW C 0 (a₀ + ts c) (oscTestFun m (αs c)))).PosSemidef ∧
      γ0.map (fun w : OscPath d m T => (WithLp.toLp 2 fun a => OscDual.coord (OscPath.at' w ⟨ts a, hts a⟩)
          (αs a) : EuclideanSpace ℝ (Fin p))) =
        multivariateGaussian 0 (Matrix.of fun a c => C₀ (propagatorW C 0 (a₀ + ts a) (oscTestFun m (αs a)))
          (propagatorW C 0 (a₀ + ts c) (oscTestFun m (αs c)))))
    (hΓ : ∀ (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T) (αs : Fin p → MultiIndex d),
      (Matrix.of fun a c => noiseCovW C q (a₀ + ts a) (a₀ + ts c) (oscTestFun m (αs a))
          (oscTestFun m (αs c))).PosSemidef ∧
      Γ.map (fun w : OscPath d m T => (WithLp.toLp 2 fun a => OscDual.coord (OscPath.at' w ⟨ts a, hts a⟩)
          (αs a) : EuclideanSpace ℝ (Fin p))) =
        multivariateGaussian 0 (Matrix.of fun a c => noiseCovW C q (a₀ + ts a) (a₀ + ts c)
          (oscTestFun m (αs a)) (oscTestFun m (αs c)))) :
    law P' (processWindow m T a₀ Z) = (γ0.prod Γ).map (fun z : OscPath d m T × OscPath d m T => z.1 + z.2) := by
  have hcont : ∀ᵐ ζ ∂P', ContinuousOn (fun u => Z (a₀ + u) ζ) (Icc 0 T) := by
    filter_upwards [hZ.cont] with ζ hζ
    refine hζ.comp (continuous_const.add continuous_id).continuousOn fun u hu => ?_
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hshift : processWindow m T a₀ Z = processWindow m T 0 (fun u ζ => Z (a₀ + u) ζ) := by
    funext ζ
    exact s21p_wpo_shift m T a₀ (fun t => Z t ζ)
  rw [hshift]
  refine HRS.MS.S21.s21_Zlaw m T hT P' (fun u ζ => Z (a₀ + u) ζ) (fun u => hZ.meas _) hcont
    (fun t t' α α' => C₀ (propagatorW C 0 (a₀ + t) (oscTestFun m α)) (propagatorW C 0 (a₀ + t') (oscTestFun m α')))
    (fun t t' α α' => noiseCovW C q (a₀ + t) (a₀ + t') (oscTestFun m α) (oscTestFun m α'))
    γ0 Γ ?_ hγ hΓ
  intro p ts hts αs
  have hts' : ∀ a, a₀ + ts a ∈ Set.Icc (0 : ℝ) (a₀ + T) := fun a =>
    ⟨by linarith [(hts a).1], by linarith [(hts a).2]⟩
  have h := hZ.gaussian p (fun a => a₀ + ts a) (fun a => oscTestFun m (αs a)) hts'
    (fun a => HRS.MS.GenPath.s56_isOscTest m (αs a))
  simp only [OscDual.eval_oscTestFun] at h
  exact h

end HRS.Whole
