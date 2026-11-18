import HRS.MS.R26T8AP29d

/-!
# S8.2 T8A P29 (part e): small structural lemmas for assembling the `PairCorrector` fields
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_p29_canonical_add {mu : Measure (Euc d)} {F G : Euc d → Euc d → ℝ} (hF : CanonicalPair mu F)
    (hG : CanonicalPair mu G) : CanonicalPair mu (fun x y => F x y + G x y) := by
  obtain ⟨f1, f2, f3, f4⟩ := hF
  obtain ⟨g1, g2, g3, g4⟩ := hG
  refine ⟨fun y => (f1 y).add (g1 y), fun x => (f2 x).add (g2 x), fun y => ?_, fun x => ?_⟩
  · show ∫ x, (F x y + G x y) ∂mu = 0
    rw [integral_add (f1 y) (g1 y), f3 y, g3 y]; ring
  · show ∫ y, (F x y + G x y) ∂mu = 0
    rw [integral_add (f2 x) (g2 x), f4 x, g4 x]; ring

theorem r26t8a_p29_measurable_of_diag {Q : Euc d → Euc d → ℝ}
    (hQ : ContDiffOn ℝ 8 (Function.uncurry Q) {p : Euc d × Euc d | p.1 ≠ p.2}) (hdiag : ∀ x, Q x x = 0) :
    Measurable (Function.uncurry Q) := by
  have hU : IsOpen {p : Euc d × Euc d | p.1 ≠ p.2} := isOpen_ne_fun continuous_fst continuous_snd
  have hpw : Measurable ({p : Euc d × Euc d | p.1 ≠ p.2}.piecewise (Function.uncurry Q) (fun _ => 0)) :=
    ContinuousOn.measurable_piecewise (hQ.continuousOn.mono (le_refl _)) continuousOn_const hU.measurableSet
  have : Function.uncurry Q = {p : Euc d × Euc d | p.1 ≠ p.2}.piecewise (Function.uncurry Q) (fun _ => 0) := by
    funext ⟨x, y⟩
    by_cases h : x = y
    · subst h
      simp [Set.piecewise, Function.uncurry, hdiag]
    · simp [Set.piecewise, h]
  rw [this]; exact hpw

theorem r26t8a_p29_pairGrad_norm_le {F : Euc d → Euc d → ℝ} {x y : Euc d}
    (hF : DifferentiableAt ℝ (Function.uncurry F) (x, y)) :
    ‖pairGradX F x y‖ + ‖pairGradY F x y‖ ≤ 2 * ‖iteratedFDeriv ℝ 1 (Function.uncurry F) (x, y)‖ := by
  rw [norm_iteratedFDeriv_one]
  have e1 : fderiv ℝ (fun x' => F x' y) x =
      (fderiv ℝ (Function.uncurry F) (x, y)).comp (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) := by
    have h := HasFDerivAt.comp x hF.hasFDerivAt (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y)
    exact h.fderiv
  have e2 : fderiv ℝ (F x) y =
      (fderiv ℝ (Function.uncurry F) (x, y)).comp (ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) := by
    have h := HasFDerivAt.comp y hF.hasFDerivAt (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y)
    exact h.fderiv
  have n1 : ‖pairGradX F x y‖ ≤ ‖fderiv ℝ (Function.uncurry F) (x, y)‖ := by
    unfold pairGradX gradient
    rw [LinearIsometryEquiv.norm_map, e1]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have : ‖ContinuousLinearMap.inl ℝ (Euc d) (Euc d)‖ ≤ 1 := ContinuousLinearMap.norm_inl_le_one ℝ (Euc d) (Euc d)
    nlinarith [norm_nonneg (fderiv ℝ (Function.uncurry F) (x, y)), norm_nonneg (ContinuousLinearMap.inl ℝ (Euc d) (Euc d))]
  have n2 : ‖pairGradY F x y‖ ≤ ‖fderiv ℝ (Function.uncurry F) (x, y)‖ := by
    unfold pairGradY gradient
    rw [LinearIsometryEquiv.norm_map, e2]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have : ‖ContinuousLinearMap.inr ℝ (Euc d) (Euc d)‖ ≤ 1 := ContinuousLinearMap.norm_inr_le_one ℝ (Euc d) (Euc d)
    nlinarith [norm_nonneg (fderiv ℝ (Function.uncurry F) (x, y)), norm_nonneg (ContinuousLinearMap.inr ℝ (Euc d) (Euc d))]
  linarith

end HRS.MS.R26T8A

end
