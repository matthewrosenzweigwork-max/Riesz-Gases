import HRS.Uniform.Comp28Aux7

/-!
# COMP-28, part 8: the degenerate point window `a = T = 0`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators Matrix

namespace HRS.Uniform.Comp28

open HRS HRS.Uniform HRS.Uniform.Q45 HRS.LindebergAux

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]

theorem smooth_zero_w {K c : ℝ} (hK : 0 ≤ K) (hc : 0 ≤ c) (ℱ : Filtration ℝ mΩ) (V : ℝ → ℝ → H →L[ℝ] H)
    (hV00 : V 0 0 = 1) (hVb : ‖V 0 0‖ ≤ K)
    (X₀ X₀' : Ω → H) (hX₀ : Measurable[ℱ 0] X₀) (hX₀' : Measurable[ℱ 0] X₀')
    (M : ℝ → Ω → H) (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ))
    (G : ℝ → Ω → H) (Cb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ))
    (Z Zb R : ℝ → Ω → H)
    (hZ : IsStochConv P V (ContinuousLinearMap.id ℝ H) M 0 0 (Z 0))
    (hZb : IsStochConv P V (ContinuousLinearMap.id ℝ H) G 0 0 (Zb 0))
    (hZm : ∀ t, Measurable (Z t)) (hZbm : ∀ t, Measurable (Zb t)) (hRm : ∀ t, Measurable (R t))
    (X Xb : ℝ → Ω → H)
    (hXd : ∀ ω, X 0 ω = V 0 0 (X₀ ω) + Z 0 ω + R 0 ω)
    (hXbd : ∀ ω, Xb 0 ω = V 0 0 (X₀' ω) + Zb 0 ω) :
    ENNReal.ofReal (smoothDist 2 (law P (windowPath 0 0 X)) (law P (windowPath 0 0 Xb))) ≤
      ENNReal.ofReal K * ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P + ∫⁻ ω, ‖windowPath 0 0 R ω‖ₑ ∂P := by
  set RHS := ENNReal.ofReal K * ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P + ∫⁻ ω, ‖windowPath 0 0 R ω‖ₑ ∂P with hRHS
  by_cases htop : RHS = ⊤
  · rw [htop]; exact le_top
  have hsplit := ENNReal.add_ne_top.1 htop
  have hfin1 := hsplit.1
  have hfin2 := hsplit.2
  have hX₀m : Measurable X₀ := hX₀.mono (ℱ.le 0) le_rfl
  have hX₀'m : Measurable X₀' := hX₀'.mono (ℱ.le 0) le_rfl
  have hX0m : Measurable (X 0) := by
    have : X 0 = fun ω => V 0 0 (X₀ ω) + Z 0 ω + R 0 ω := funext hXd
    rw [this]
    exact (((V 0 0).continuous.measurable.comp hX₀m).add (hZm 0)).add (hRm 0)
  have hXb0m : Measurable (Xb 0) := by
    have : Xb 0 = fun ω => V 0 0 (X₀' ω) + Zb 0 ω := funext hXbd
    rw [this]
    exact ((V 0 0).continuous.measurable.comp hX₀'m).add (hZbm 0)
  have hwX := aemeasurable_windowPath_zero P X hX0m
  have hwXb := aemeasurable_windowPath_zero P Xb hXb0m
  have hZ0 := stochConv_zero_ae P (plainData V) M (Z 0) (hZm 0) hZ
  have hZb0 := stochConv_zero_ae P (plainData V) G (Zb 0) (hZbm 0) hZb
  have hjb : ∀ x : H, ‖x‖ ≤ K * ‖x‖ := fun x => by
    have := ((V 0 0).le_opNorm x).trans (mul_le_mul_of_nonneg_right hVb (norm_nonneg x))
    rwa [hV00, ContinuousLinearMap.one_apply] at this
  have hdiff : ∀ᵐ ω ∂P, ‖windowPath 0 0 X ω - windowPath 0 0 Xb ω‖ₑ ≤
      ENNReal.ofReal K * ‖X₀ ω - X₀' ω‖ₑ + ‖windowPath 0 0 R ω‖ₑ := by
    filter_upwards [hZ0, hZb0] with ω h1 h2
    rw [windowPath_zero, windowPath_zero, windowPath_zero]
    have e : constPath (X 0 ω) - constPath (Xb 0 ω) = constPath (X 0 ω - Xb 0 ω) :=
      pcm_ext fun t => by rw [pcm_sub, pcm_constPath, pcm_constPath, pcm_constPath]
    rw [e, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm, norm_constPath, norm_constPath]
    have hx : X 0 ω - Xb 0 ω = (X₀ ω - X₀' ω) + R 0 ω := by
      rw [hXd ω, hXbd ω, h1, h2, hV00]
      simp only [ContinuousLinearMap.one_apply, add_zero]
      abel
    rw [hx, ← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_add (by positivity) (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ((norm_add_le _ _).trans ?_)
    exact add_le_add (hjb _) le_rfl
  have hbd : ∫⁻ ω, ‖windowPath 0 0 X ω - windowPath 0 0 Xb ω‖ₑ ∂P ≤ RHS := by
    calc _ ≤ ∫⁻ ω, (ENNReal.ofReal K * ‖X₀ ω - X₀' ω‖ₑ + ‖windowPath 0 0 R ω‖ₑ) ∂P :=
          lintegral_mono_ae hdiff
      _ = RHS := by
          rw [hRHS, lintegral_add_left' ?_, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact (hX₀m.sub hX₀'m).enorm.const_mul _ |>.aemeasurable
  have hfinD : ∫⁻ ω, ‖windowPath 0 0 X ω - windowPath 0 0 Xb ω‖ₑ ∂P ≠ ⊤ :=
    ne_top_of_le_ne_top htop hbd
  have hper : ∀ Φ ∈ CbUnitBall (PathSp 0 H) 2,
      ENNReal.ofReal |∫ z, Φ z ∂(law P (windowPath 0 0 X)) - ∫ z, Φ z ∂(law P (windowPath 0 0 Xb))| ≤
        RHS := by
    intro Φ hΦ
    have hΦc := (cbUnit_bounds hΦ).1.continuous
    have e1 : ∫ z, Φ z ∂(law P (windowPath 0 0 X)) = ∫ ω, Φ (windowPath 0 0 X ω) ∂P :=
      integral_map hwX hΦc.aestronglyMeasurable
    have e2 : ∫ z, Φ z ∂(law P (windowPath 0 0 Xb)) = ∫ ω, Φ (windowPath 0 0 Xb ω) ∂P :=
      integral_map hwXb hΦc.aestronglyMeasurable
    rw [e1, e2]
    have key := cb_integral_diff_le P hΦ hwX hwXb hfinD
    calc ENNReal.ofReal |∫ ω, Φ (windowPath 0 0 X ω) ∂P - ∫ ω, Φ (windowPath 0 0 Xb ω) ∂P|
        ≤ ENNReal.ofReal (∫⁻ ω, ‖windowPath 0 0 X ω - windowPath 0 0 Xb ω‖ₑ ∂P).toReal :=
          ENNReal.ofReal_le_ofReal key
      _ = ∫⁻ ω, ‖windowPath 0 0 X ω - windowPath 0 0 Xb ω‖ₑ ∂P := ENNReal.ofReal_toReal hfinD
      _ ≤ RHS := hbd
  have hr0 : 0 ≤ RHS.toReal := ENNReal.toReal_nonneg
  have hsd : smoothDist 2 (law P (windowPath 0 0 X)) (law P (windowPath 0 0 Xb)) ≤ RHS.toReal := by
    refine Real.iSup_le (fun Φ => ?_) hr0
    exact (ENNReal.ofReal_le_iff_le_toReal htop).1 (hper Φ.1 Φ.2)
  calc ENNReal.ofReal (smoothDist 2 (law P (windowPath 0 0 X)) (law P (windowPath 0 0 Xb)))
      ≤ ENNReal.ofReal RHS.toReal := ENNReal.ofReal_le_ofReal hsd
    _ = RHS := ENNReal.ofReal_toReal htop

end HRS.Uniform.Comp28
