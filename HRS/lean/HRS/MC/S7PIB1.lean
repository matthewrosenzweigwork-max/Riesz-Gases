import HRS.MC.S7PIDefs
import HRS.MC.S7PIS2Obs
import HRS.MC.S7PIS3Law
import HRS.MC.S7PIS3Heat

/-!
# Packet piB, part 1: `s7_PIF_heat_obs` (the heat function of a cylindrical functional is the finite-dimensional one)

Route: `obsVec` is a continuous linear map `O`; the law of `obsVec` under `γ_u` is `N(0, obsCov u)` (`s7_PIS_obs_law_proof`),
so `heatFn γ (G ∘ obsVec) u = gaussHeat obsCov G u ∘ obsVec`; the chain rule for the continuous linear map `O` gives the
derivative clauses, `gaussHeat` being `C²` by differentiation under the integral sign.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace HRS.MC.Sec7.S7PIB

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

/-- `C²` smoothness of a Gaussian (or any probability) average of a `C_b²` function on `ℝ^q`. -/
theorem S7PIB_heat_contDiff2 {q : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin q))) [IsProbabilityMeasure ν]
    {G : EuclideanSpace ℝ (Fin q) → ℝ} (hG : MemCb 2 G) :
    ContDiff ℝ 2 (fun y => ∫ x, G (y + x) ∂ν) := by
  have hGc : ∀ m : ℕ, m ≤ 2 → Continuous (iteratedFDeriv ℝ m G) := fun m hm =>
    hG.1.continuous_iteratedFDeriv (by exact_mod_cast hm)
  have hcd : ∀ z : EuclideanSpace ℝ (Fin q), ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (fun y => G (y + z)) :=
    fun z => by
      have := hG.1.comp (contDiff_id.add (contDiff_const (c := z)))
      simpa [Function.comp_def] using this
  have key := contDiff_integral_dominated (B := EuclideanSpace ℝ (Fin q)) ν
    (fun z y => G (y + z)) 2 (by norm_num) hcd
    (fun x => by
      have hGcont : Continuous G := by simpa using hG.1.continuous
      refine Integrable.of_bound (C := ⨆ z, ‖iteratedFDeriv ℝ 0 G z‖) ?_ ?_
      · exact (hGcont.comp (by fun_prop : Continuous fun z => x + z)).aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun z => ?_
        have := HRS.MC.Sec7.S7PIS3.S7PIS3_cb_bound hG (j := 0) (Nat.zero_le _) (x + z)
        simpa using this)
    (fun m hm x => by
      have h : (fun z => iteratedFDeriv ℝ m (fun y => G (y + z)) x) =
          fun z => iteratedFDeriv ℝ m G (x + z) := by
        funext z; exact iteratedFDeriv_comp_add_right m z x
      rw [h]
      exact ((hGc m hm).comp (by fun_prop : Continuous fun z => x + z)).aestronglyMeasurable)
    (fun m _ => ⨆ z, ‖iteratedFDeriv ℝ m G z‖) (fun m _ _ => integrable_const _)
    (fun m _ hmj z x => by
      rw [iteratedFDeriv_comp_add_right]
      exact HRS.MC.Sec7.S7PIS3.S7PIS3_cb_bound hG hmj _)
  simpa using key.1

/-- The centred Gaussian with covariance `0` is the Dirac mass at `0`. -/
theorem S7PIB_mvG_zero {q : ℕ} :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin q)) (0 : Matrix (Fin q) (Fin q) ℝ) = Measure.dirac 0 := by
  unfold multivariateGaussian
  have : (fun x : EuclideanSpace ℝ (Fin q) =>
      (0 : EuclideanSpace ℝ (Fin q)) + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (0 : Matrix (Fin q) (Fin q) ℝ)) x) =
      fun _ => 0 := by
    funext x
    simp
  rw [this, Measure.map_const]
  simp

theorem s7_PIF_heat_obs_proof (R : Regime d) (m : ℝ) (T : ℝ) (hT : 0 < T)
    (γ : ℝ → Measure (PathSpace d m T)) (hγ : ∀ u ∈ Set.Icc (0 : ℝ) T, IsFutureGaussian R.D R.ρ m T u (γ u))
    {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ) (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T)
    (hφ : ∀ i, Torus.IsSmooth (φ i)) (G : EuclideanSpace ℝ (Fin q) → ℝ) (hG : MemCb 2 G) :
    (∀ u ∈ Set.Icc (0 : ℝ) T, ∀ y, heatFn γ (fun w => G (obsVec m T t φ w)) u y =
        gaussHeat (obsCov R.D R.ρ t φ) G u (obsVec m T t φ y)) ∧
    (∀ c, gaussHeat (obsCov R.D R.ρ t φ) G T c = G c) ∧
    ∀ (O : PathSpace d m T →L[ℝ] EuclideanSpace ℝ (Fin q)), (∀ w, O w = obsVec m T t φ w) →
      ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ y,
        fderiv ℝ (heatFn γ (fun w => G (obsVec m T t φ w)) u) y =
          (fderiv ℝ (gaussHeat (obsCov R.D R.ρ t φ) G u) (obsVec m T t φ y)).comp O ∧
        iteratedFDeriv ℝ 2 (heatFn γ (fun w => G (obsVec m T t φ w)) u) y =
          (iteratedFDeriv ℝ 2 (gaussHeat (obsCov R.D R.ρ t φ) G u) (obsVec m T t φ y)).compContinuousLinearMap
            (fun _ => O) := by
  obtain ⟨O0, hO0⟩ := HRS.MC.Sec7.S7PIS2.s7_PIS_obs_clm_proof m T t φ ht hφ
  have law := HRS.MC.Sec7.S7PIS3.s7_PIS_obs_law_proof R m T hT γ hγ t φ ht hφ
  have hmeas : Measurable (obsVec m T t φ) := by
    have : obsVec m T t φ = fun w => O0 w := funext fun w => (hO0 w).symm
    rw [this]; exact O0.continuous.measurable
  have hadd : ∀ y z, obsVec m T t φ (y + z) = obsVec m T t φ y + obsVec m T t φ z := by
    intro y z; rw [← hO0, ← hO0, ← hO0, map_add]
  have hGc : Continuous G := by simpa using hG.1.continuous
  have hA : ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ y, heatFn γ (fun w => G (obsVec m T t φ w)) u y =
      gaussHeat (obsCov R.D R.ρ t φ) G u (obsVec m T t φ y) := by
    intro u hu y
    unfold heatFn gaussHeat
    rw [← (law u hu).2]
    have hm' : AEStronglyMeasurable (fun x : EuclideanSpace ℝ (Fin q) => G (obsVec m T t φ y + x))
        (Measure.map (obsVec m T t φ) (γ u)) :=
      (hGc.comp (by fun_prop : Continuous fun x : EuclideanSpace ℝ (Fin q) => obsVec m T t φ y + x)).aestronglyMeasurable
    rw [integral_map hmeas.aemeasurable hm']
    simp_rw [hadd]
  refine ⟨hA, ?_, ?_⟩
  · intro c
    have hcov0 : obsCov R.D R.ρ t φ T = 0 := by
      ext i j
      simp only [obsCov, Matrix.of_apply, Matrix.zero_apply]
      have hz : volume (Set.Icc T (min (t i) (t j))) = 0 := by
        refine measure_mono_null (t := {T}) (fun x hx => ?_) Real.volume_singleton
        have h1 : x ≤ T := hx.2.trans ((min_le_left _ _).trans (ht i).2)
        exact le_antisymm h1 hx.1
      rw [Measure.restrict_eq_zero.2 hz, integral_zero_measure, mul_zero]
    unfold gaussHeat
    rw [hcov0, S7PIB_mvG_zero, integral_dirac]
    simp
  · intro O hO u hu y
    have hOe : ∀ w, O w = O0 w := fun w => (hO w).trans (hO0 w).symm
    have hcd : ContDiff ℝ 2 (gaussHeat (obsCov R.D R.ρ t φ) G u) :=
      S7PIB_heat_contDiff2 (multivariateGaussian 0 (obsCov R.D R.ρ t φ u)) hG
    have hfun : heatFn γ (fun w => G (obsVec m T t φ w)) u =
        (gaussHeat (obsCov R.D R.ρ t φ) G u) ∘ O := by
      funext w
      rw [hA u hu w, Function.comp_apply, hO]
    rw [hfun]
    refine ⟨?_, ?_⟩
    · have hd : DifferentiableAt ℝ (gaussHeat (obsCov R.D R.ρ t φ) G u) (O y) :=
        (hcd.differentiable (by norm_num)) _
      rw [fderiv_comp y hd O.differentiableAt, O.fderiv, hO]
    · rw [ContinuousLinearMap.iteratedFDeriv_comp_right O hcd y (by norm_num), hO]

end HRS.MC.Sec7.S7PIB

end
