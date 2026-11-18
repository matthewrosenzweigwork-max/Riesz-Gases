import HRS.Uniform.Q45Fnl5

/-!
# Q45: Proposition 3.21 for `T = 0`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

theorem smooth_zero_final {K : ℝ} {Ω : Type} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ)
    {H E : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (S : EvolData H E) (hS : S.MaxHyp 0 K)
    (X₀ X₀' : Ω → H) (hX₀ : Measurable[ℱ 0] X₀) (hX₀' : Measurable[ℱ 0] X₀')
    (M : ℝ → Ω → H) (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ))
    (G : ℝ → Ω → H) (Cb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ))
    (Z Zb R : ℝ → Ω → E)
    (hZ : ∀ t ∈ Set.Icc (0 : ℝ) 0, IsStochConv P S.VE S.j M 0 t (Z t))
    (hZb : ∀ t ∈ Set.Icc (0 : ℝ) 0, IsStochConv P S.VE S.j G 0 t (Zb t))
    (hZm : ∀ t, Measurable (Z t)) (hZbm : ∀ t, Measurable (Zb t)) (hRm : ∀ t, Measurable (R t))
    (X Xb : ℝ → Ω → E)
    (hXd : ∀ t ∈ Set.Icc (0 : ℝ) 0, ∀ ω, X t ω = S.VE t 0 (S.j (X₀ ω)) + Z t ω + R t ω)
    (hXbd : ∀ t ∈ Set.Icc (0 : ℝ) 0, ∀ ω, Xb t ω = S.VE t 0 (S.j (X₀' ω)) + Zb t ω) :
    ENNReal.ofReal (smoothDist 2 (law P (windowPath 0 0 X)) (law P (windowPath 0 0 Xb))) ≤
      ENNReal.ofReal (detConst 0 K ^ 2) * ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P +
        ∫⁻ ω, ‖windowPath 0 0 R ω‖ₑ ∂P +
        ENNReal.ofReal (detConst 0 K ^ 2) *
          ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) 0, ENNReal.ofReal (traceNormForm (Sg r ω - Cb r))) ∂P := by
  set Cv := detConst 0 K with hCv
  have hCv1 : 1 ≤ Cv := detConst_ge_one 0 K
  have hCvpos : 0 < Cv := by linarith
  set RHS := ENNReal.ofReal (Cv ^ 2) * ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P +
        ∫⁻ ω, ‖windowPath 0 0 R ω‖ₑ ∂P +
        ENNReal.ofReal (Cv ^ 2) *
          ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) 0, ENNReal.ofReal (traceNormForm (Sg r ω - Cb r))) ∂P
    with hRHS
  by_cases htop : RHS = ⊤
  · rw [htop]; exact le_top
  have hsplit := ENNReal.add_ne_top.1 htop
  have hsplit' := ENNReal.add_ne_top.1 hsplit.1
  have hC2 : ENNReal.ofReal (Cv ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hfin1 : ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P ≠ ⊤ := by
    intro h
    apply hsplit'.1
    rw [h, ENNReal.mul_top hC2]
  have hfin2 : ∫⁻ ω, ‖windowPath 0 0 R ω‖ₑ ∂P ≠ ⊤ := hsplit'.2
  have hev := hS.1
  have h00 : S.VE 0 0 = 1 := hev.self_E 0 ⟨le_rfl, le_rfl⟩
  have hX₀m : Measurable X₀ := hX₀.mono (ℱ.le 0) le_rfl
  have hX₀'m : Measurable X₀' := hX₀'.mono (ℱ.le 0) le_rfl
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 0 := ⟨le_rfl, le_rfl⟩
  have hvm : ∀ (x : Ω → H), Measurable x → Measurable fun ω => S.VE 0 0 (S.j (x ω)) :=
    fun x hx => ((S.VE 0 0).continuous.comp S.j.continuous).measurable.comp hx
  have hX0m : Measurable (X 0) := by
    have : X 0 = fun ω => S.VE 0 0 (S.j (X₀ ω)) + Z 0 ω + R 0 ω := funext fun ω => hXd 0 hmem0 ω
    rw [this]; exact ((hvm X₀ hX₀m).add (hZm 0)).add (hRm 0)
  have hXb0m : Measurable (Xb 0) := by
    have : Xb 0 = fun ω => S.VE 0 0 (S.j (X₀' ω)) + Zb 0 ω := funext fun ω => hXbd 0 hmem0 ω
    rw [this]; exact (hvm X₀' hX₀'m).add (hZbm 0)
  have hwX := aemeasurable_windowPath_zero P X hX0m
  have hwXb := aemeasurable_windowPath_zero P Xb hXb0m
  have hZ0 := stochConv_zero_ae P S M (Z 0) (hZm 0) (hZ 0 hmem0)
  have hZb0 := stochConv_zero_ae P S G (Zb 0) (hZbm 0) (hZb 0 hmem0)
  have hjb : ∀ x : H, ‖S.j x‖ ≤ Cv * ‖x‖ := fun x => by
    have := hS.norm_le le_rfl (le_refl (0 : ℝ)) le_rfl le_rfl x
    rwa [h00, ContinuousLinearMap.one_apply] at this
  have hdiff : ∀ᵐ ω ∂P, ‖windowPath 0 0 X ω - windowPath 0 0 Xb ω‖ₑ ≤
      ENNReal.ofReal Cv * ‖X₀ ω - X₀' ω‖ₑ + ‖windowPath 0 0 R ω‖ₑ := by
    filter_upwards [hZ0, hZb0] with ω h1 h2
    rw [windowPath_zero, windowPath_zero, windowPath_zero]
    have e : constPath (X 0 ω) - constPath (Xb 0 ω) = constPath (X 0 ω - Xb 0 ω) :=
      pcm_ext fun t => by rw [pcm_sub, pcm_constPath, pcm_constPath, pcm_constPath]
    rw [e, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm, norm_constPath, norm_constPath]
    have hx : X 0 ω - Xb 0 ω = S.j (X₀ ω - X₀' ω) + R 0 ω := by
      rw [hXd 0 hmem0 ω, hXbd 0 hmem0 ω, h1, h2, h00, map_sub]
      simp only [ContinuousLinearMap.one_apply, add_zero]
      abel
    rw [hx, ← ENNReal.ofReal_mul hCvpos.le, ← ENNReal.ofReal_add (by positivity) (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ((norm_add_le _ _).trans ?_)
    exact add_le_add (hjb _) le_rfl
  have hbd : ∫⁻ ω, ‖windowPath 0 0 X ω - windowPath 0 0 Xb ω‖ₑ ∂P ≤
      ENNReal.ofReal Cv * ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P + ∫⁻ ω, ‖windowPath 0 0 R ω‖ₑ ∂P := by
    calc _ ≤ ∫⁻ ω, (ENNReal.ofReal Cv * ‖X₀ ω - X₀' ω‖ₑ + ‖windowPath 0 0 R ω‖ₑ) ∂P :=
          lintegral_mono_ae hdiff
      _ = ENNReal.ofReal Cv * ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P + ∫⁻ ω, ‖windowPath 0 0 R ω‖ₑ ∂P := by
          rw [lintegral_add_left' ?_, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact (hX₀m.sub hX₀'m).enorm.const_mul _ |>.aemeasurable
  have hfinD : ∫⁻ ω, ‖windowPath 0 0 X ω - windowPath 0 0 Xb ω‖ₑ ∂P ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin1, hfin2⟩)
      hbd
  have hper : ∀ Φ ∈ CbUnitBall (PathSp 0 E) 2,
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
      _ ≤ ENNReal.ofReal Cv * ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P + ∫⁻ ω, ‖windowPath 0 0 R ω‖ₑ ∂P := hbd
      _ ≤ ENNReal.ofReal (Cv ^ 2) * ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P + ∫⁻ ω, ‖windowPath 0 0 R ω‖ₑ ∂P :=
          add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal (by nlinarith)) le_rfl) le_rfl
      _ ≤ RHS := le_self_add
  have hr0 : 0 ≤ RHS.toReal := ENNReal.toReal_nonneg
  have hsd : smoothDist 2 (law P (windowPath 0 0 X)) (law P (windowPath 0 0 Xb)) ≤ RHS.toReal := by
    refine Real.iSup_le (fun Φ => ?_) hr0
    exact (ENNReal.ofReal_le_iff_le_toReal htop).1 (hper Φ.1 Φ.2)
  calc ENNReal.ofReal (smoothDist 2 (law P (windowPath 0 0 X)) (law P (windowPath 0 0 Xb)))
      ≤ ENNReal.ofReal RHS.toReal := ENNReal.ofReal_le_ofReal hsd
    _ = RHS := ENNReal.ofReal_toReal htop

end HRS.Uniform.Q45
