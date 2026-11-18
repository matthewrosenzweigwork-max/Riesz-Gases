import HRS.MS.R2InterpAux5
import HRS.MC.S7PIF6A

/-!
# S10.2 (worker S102), part 6: the heat function of a cylindrical functional (whole-space port of `s7_PIF_heat_obs`)

For `G ∈ C_b^2(ℝ^q)` and the observation map `obs = s102_obs τ α`: `u_{G∘obs}(u,y) = gaussHeat (obsCov) G u (obs y)` for `u ∈ [0,T]`,
`gaussHeat obsCov G T = G`, and the first two derivatives of `u_{G∘obs}(u,·)` are those of `gaussHeat` composed with `obs`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIF6

variable {d : ℕ} {m T : ℝ}

theorem s102_obsCov_T (C : WholeCoeff d) {q : ℕ} (τ : Fin q → Set.Icc (0 : ℝ) T) (α : Fin q → MultiIndex d) :
    s102_obsCov C m τ α T = 0 := by
  ext i j
  simp only [s102_obsCov, Matrix.of_apply, Matrix.zero_apply]
  have hm : min (τ i : ℝ) (τ j : ℝ) ≤ T := (min_le_left _ _).trans (τ i).2.2
  have h0 : volume (Set.Icc T (min (τ i : ℝ) (τ j : ℝ))) = 0 := by
    refine measure_mono_null (t := {T}) (fun v hv => ?_) (measure_singleton T)
    exact le_antisymm (hv.2.trans hm) hv.1
  rw [setIntegral_measure_zero _ h0, mul_zero]

theorem s102_gaussHeat_T (C : WholeCoeff d) {q : ℕ} (τ : Fin q → Set.Icc (0 : ℝ) T)
    (α : Fin q → MultiIndex d) (G : EuclideanSpace ℝ (Fin q) → ℝ) (c : EuclideanSpace ℝ (Fin q)) :
    gaussHeat (s102_obsCov C m τ α) G T c = G c := by
  unfold gaussHeat
  rw [s102_obsCov_T C τ α, S7PIF6_mvG_zero, integral_dirac]
  simp

/-- The heat function of a cylindrical functional. -/
theorem s102_heat_obs (C : WholeCoeff d) (γ : ℝ → Measure (OscPath d m T))
    (hγ : ∀ u ∈ Set.Icc (0 : ℝ) T, IsR2FutureGaussian C m T u (γ u)) {q : ℕ}
    (τ : Fin q → Set.Icc (0 : ℝ) T) (α : Fin q → MultiIndex d) (G : EuclideanSpace ℝ (Fin q) → ℝ)
    (hG : MemCb 2 G) (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) T) (y : OscPath d m T) :
    r2HeatFn γ (fun w => G (s102_obs τ α w)) u y =
      gaussHeat (s102_obsCov C m τ α) G u (s102_obs τ α y) := by
  have hl := (s102_obs_law C (hγ u hu) τ α).2
  haveI : IsGaussian (γ u) := (hγ u hu).1.1
  unfold r2HeatFn gaussHeat
  rw [← hl]
  have hmeas : AEMeasurable (s102_obs τ α) (γ u) := (s102_obs τ α).continuous.aemeasurable
  rw [integral_map hmeas]
  · simp [map_add]
  · exact (hG.1.continuous.comp (by fun_prop : Continuous fun x => s102_obs τ α y + x)).aestronglyMeasurable

/-- The heat function as a composition with the observation map. -/
theorem s102_heat_obs_fun (C : WholeCoeff d) (γ : ℝ → Measure (OscPath d m T))
    (hγ : ∀ u ∈ Set.Icc (0 : ℝ) T, IsR2FutureGaussian C m T u (γ u)) {q : ℕ}
    (τ : Fin q → Set.Icc (0 : ℝ) T) (α : Fin q → MultiIndex d) (G : EuclideanSpace ℝ (Fin q) → ℝ)
    (hG : MemCb 2 G) (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) T) :
    r2HeatFn γ (fun w => G (s102_obs τ α w)) u =
      fun y => gaussHeat (s102_obsCov C m τ α) G u (s102_obs τ α y) :=
  funext fun y => s102_heat_obs C γ hγ τ α G hG u hu y

/-- First and second derivatives of the cylindrical heat function. -/
theorem s102_heat_obs_deriv (C : WholeCoeff d) (γ : ℝ → Measure (OscPath d m T))
    (hγ : ∀ u ∈ Set.Icc (0 : ℝ) T, IsR2FutureGaussian C m T u (γ u)) {q : ℕ}
    (τ : Fin q → Set.Icc (0 : ℝ) T) (α : Fin q → MultiIndex d) (G : EuclideanSpace ℝ (Fin q) → ℝ)
    (hG : MemCb 2 G) (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) T) (y : OscPath d m T) :
    fderiv ℝ (r2HeatFn γ (fun w => G (s102_obs τ α w)) u) y =
        (fderiv ℝ (gaussHeat (s102_obsCov C m τ α) G u) (s102_obs τ α y)).comp (s102_obs τ α) ∧
      iteratedFDeriv ℝ 2 (r2HeatFn γ (fun w => G (s102_obs τ α w)) u) y =
        (iteratedFDeriv ℝ 2 (gaussHeat (s102_obsCov C m τ α) G u) (s102_obs τ α y)).compContinuousLinearMap
          (fun _ => s102_obs τ α) := by
  have hl := (s102_obs_law C (hγ u hu) τ α)
  haveI : IsProbabilityMeasure (multivariateGaussian (0 : EuclideanSpace ℝ (Fin q))
    (s102_obsCov C m τ α u)) := inferInstance
  have hcd : ContDiff ℝ 2 (gaussHeat (s102_obsCov C m τ α) G u) :=
    HRS.MC.Sec7.S7PIH.S7PIH_heat_contDiff _ (by norm_num) hG
  rw [s102_heat_obs_fun C γ hγ τ α G hG u hu]
  constructor
  · exact (HasFDerivAt.comp y (hcd.differentiable (by norm_num) _).hasFDerivAt
      (s102_obs τ α).hasFDerivAt).fderiv
  · exact (s102_obs τ α).iteratedFDeriv_comp_right (n := 2) (f := gaussHeat (s102_obsCov C m τ α) G u)
      hcd y le_rfl

end HRS.MS.R2Interp

end
