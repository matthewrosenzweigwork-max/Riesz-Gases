import HRS.MS.R2S11Aux18

/-!
# S11.2 (a): window measurability and the cubic-expectation difference bound
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2S11

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s11_window_aemeas {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') {C : WholeCoeff d} {m q T u T' : ℝ}
    {C₀ : (Euc d → ℝ) → (Euc d → ℝ) → ℝ} {Z : ℝ → Ω' → OscDual d m}
    (hZ : IsLinearGaussianEvolutionW P' C m q T' C₀ Z) (hT : 0 ≤ T) (hu : 0 ≤ u) (hT' : u + T ≤ T') :
    AEMeasurable (processWindow m T u Z) P' := by
  have hc : ∀ᵐ ζ ∂P', ContinuousOn (fun t => Z (u + t) ζ) (Set.Icc 0 T) := by
    filter_upwards [hZ.cont] with ζ hζ
    exact hζ.comp (continuous_const.add continuous_id).continuousOn
      (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have h := HRS.GF.gfb4_aemeasurable_windowPath P' hT (fun t ζ => Z (u + t) ζ) (fun t _ => hZ.meas _) hc
  rw [← HRS.MS.GenPath.s56_wpo_eq_windowPath] at h
  have e : processWindow m T u Z = fun ζ => windowPathOf m T 0 (fun t => Z (u + t) ζ) := by
    funext ζ
    unfold processWindow windowPathOf
    have hfun : (fun t : Set.Icc (0 : ℝ) T => Z (u + (t : ℝ)) ζ) =
        (fun t : Set.Icc (0 : ℝ) T => Z (u + (0 + (t : ℝ))) ζ) := by
      funext t; simp
    exact HRS.GF.dite_continuousMap_congr _ _ hfun
  rw [e]
  exact h

/-- The expectation `E[κ(D³Φ(w))]` is a bounded, integrable quantity, and differences are bounded by `‖κ₁-κ₂‖`. -/
theorem s11_cubic_diff_bound {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] {T : ℝ}
    (w : Ω' → R2X d T) (hw : AEMeasurable w P') (κ₁ κ₂ : projTensor (R2X d T) 3)
    {Φ : R2X d T → ℝ} (hΦ : Φ ∈ HRS.CbUnitBall (R2X d T) 5) :
    |r2CubicExpect P' w κ₁ Φ - r2CubicExpect P' w κ₂ Φ| ≤ ‖κ₁ - κ₂‖ := by
  have hΦ5 : ContDiff ℝ 5 Φ := hΦ.1
  have hint : ∀ κ : projTensor (R2X d T) 3, Integrable (fun ζ => (κ : TensorDual (R2X d T) 3)
      (iteratedFDeriv ℝ 3 Φ (w ζ))) P' := by
    intro κ
    have hcont : Continuous fun x => (κ : TensorDual (R2X d T) 3) (iteratedFDeriv ℝ 3 Φ x) :=
      (s11_cubic_F hΦ5 (κ : TensorDual (R2X d T) 3)).1.continuous
    refine Integrable.of_bound (C := ‖κ‖) (hcont.measurable.comp_aemeasurable hw).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ζ => ?_)
    have h1 : ‖iteratedFDeriv ℝ 3 Φ (w ζ)‖ ≤ 1 := s11_cbUnit_bound hΦ (by norm_num) _
    calc ‖(κ : TensorDual (R2X d T) 3) (iteratedFDeriv ℝ 3 Φ (w ζ))‖
        ≤ ‖(κ : TensorDual (R2X d T) 3)‖ * ‖iteratedFDeriv ℝ 3 Φ (w ζ)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖κ‖ * 1 := by
          exact mul_le_mul_of_nonneg_left h1 (norm_nonneg (κ : TensorDual (R2X d T) 3))
      _ = ‖κ‖ := mul_one _
  unfold r2CubicExpect
  rw [← integral_sub (hint κ₁) (hint κ₂)]
  have hb : ∀ ζ, ‖(κ₁ : TensorDual (R2X d T) 3) (iteratedFDeriv ℝ 3 Φ (w ζ)) -
      (κ₂ : TensorDual (R2X d T) 3) (iteratedFDeriv ℝ 3 Φ (w ζ))‖ ≤ ‖κ₁ - κ₂‖ := fun ζ => by
    have h1 : ‖iteratedFDeriv ℝ 3 Φ (w ζ)‖ ≤ 1 := s11_cbUnit_bound hΦ (by norm_num) _
    have e : (κ₁ : TensorDual (R2X d T) 3) (iteratedFDeriv ℝ 3 Φ (w ζ)) -
        (κ₂ : TensorDual (R2X d T) 3) (iteratedFDeriv ℝ 3 Φ (w ζ)) =
        ((κ₁ - κ₂ : projTensor (R2X d T) 3) : TensorDual (R2X d T) 3) (iteratedFDeriv ℝ 3 Φ (w ζ)) := by
      simp
    rw [e]
    calc _ ≤ ‖((κ₁ - κ₂ : projTensor (R2X d T) 3) : TensorDual (R2X d T) 3)‖ * ‖iteratedFDeriv ℝ 3 Φ (w ζ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖κ₁ - κ₂‖ * 1 := by
          exact mul_le_mul_of_nonneg_left h1 (norm_nonneg ((κ₁ - κ₂ : projTensor (R2X d T) 3) : TensorDual (R2X d T) 3))
      _ = _ := mul_one _
  have := norm_integral_le_of_norm_le_const (μ := P') (C := ‖κ₁ - κ₂‖) (Filter.Eventually.of_forall hb)
  simpa [Real.norm_eq_abs] using this

end HRS.MS.R2S11
