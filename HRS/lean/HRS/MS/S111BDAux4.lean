import HRS.MS.S111BDAux1
import HRS.MS.S111BDAux2
import HRS.MS.S111BDAux3
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
# S11.1 packet G2: the shifted-window Gaussian law and finite second moment
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S111BD

open HRS HRS.Whole

theorem s111_isCenteredGaussian_mvg (p : ℕ) (S : Matrix (Fin p) (Fin p) ℝ) :
    HRS.IsCenteredGaussian (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S) := by
  refine ⟨inferInstance, fun L => ?_⟩
  rw [show ∫ z, L z ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S) =
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S)[L] from rfl,
    IsGaussian.integral_dual, integral_id_multivariateGaussian]
  simp

theorem s111_shifted_window_gaussian (d : ℕ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (C : WholeCoeff d) (m q T u H : ℝ)
    (C₀ : (Euc d → ℝ) → (Euc d → ℝ) → ℝ)
    (Z : ℝ → Ω → OscDual d m)
    (hZ : IsLinearGaussianEvolutionW P C m q H C₀ Z)
    (hT : 0 < T) (hu : 0 ≤ u) (hH : u + T ≤ H) :
    AEMeasurable (processWindow m T u Z) P ∧
      HRS.IsCenteredGaussian (P.map (processWindow m T u Z)) ∧
      MemLp (processWindow m T u Z) 2 P := by
  obtain ⟨hWm, hae⟩ := s111_shifted_window_aemeas d P C m q T u H C₀ Z hZ hT.le hu hH
  set W := processWindow m T u Z with hW
  have hprob : IsProbabilityMeasure (P.map W) :=
    ⟨by simp [Measure.map_apply_of_aemeasurable hWm MeasurableSet.univ]⟩
  have hobs : ∀ (p : ℕ) (τ : Fin p → Set.Icc (0 : ℝ) T) (α : Fin p → MultiIndex d),
      HRS.IsCenteredGaussian ((P.map W).map (HRS.MS.R2Interp.s102_obs (m := m) τ α)) := by
    intro p τ α
    rw [AEMeasurable.map_map_of_aemeasurable
      (HRS.MS.R2Interp.s102_obs (m := m) τ α).continuous.measurable.aemeasurable hWm]
    have hG := hZ.gaussian p (fun a => u + (τ a : ℝ)) (fun a => oscTestFun m (α a))
      (fun a => ⟨by linarith [(τ a).2.1], by linarith [(τ a).2.2]⟩)
      (fun a => HRS.MS.GenPath.s56_isOscTest m (α a))
    have hcongr : (HRS.MS.R2Interp.s102_obs (m := m) τ α) ∘ W =ᵐ[P]
        fun ζ => (WithLp.toLp 2 fun a => OscDual.eval (Z (u + (τ a : ℝ)) ζ) (oscTestFun m (α a)) :
          EuclideanSpace ℝ (Fin p)) := by
      filter_upwards [hae] with ζ hζ
      ext a
      simp only [Function.comp, HRS.MS.R2Interp.s102_obs_apply, hζ (τ a),
        OscDual.eval_oscTestFun]
    rw [Measure.map_congr hcongr]
    unfold HRS.law at hG
    rw [hG]
    exact s111_isCenteredGaussian_mvg p _
  have hproj := fun L => s111_projection_gaussian d m T hT (P.map W) hobs L
  have hX : ∀ L : ℕ, HRS.IsCenteredGaussian
      (P.map (fun ζ => HRS.MS.R2Interp.s102_Pj (d := d) (m := m) T hT L (W ζ))) := by
    intro L
    have := hproj L
    rwa [AEMeasurable.map_map_of_aemeasurable
      (HRS.MS.R2Interp.s102_Pj (d := d) (m := m) T hT L).continuous.measurable.aemeasurable hWm]
      at this
  have hG := s111_centered_gaussian_ae_limit P
    (fun L ζ => HRS.MS.R2Interp.s102_Pj (d := d) (m := m) T hT L (W ζ)) W
    (fun L => (HRS.MS.R2Interp.s102_Pj (d := d) (m := m) T hT L).continuous.measurable.comp_aemeasurable hWm)
    hWm hX
    (Filter.Eventually.of_forall fun ζ =>
      (HRS.MS.R2Interp.s102_projection_strong m T hT).2.1 (W ζ))
  exact ⟨hWm, hG, (HasGaussianLaw.mk hWm hG.1).memLp_two⟩

end HRS.MS.S111BD
