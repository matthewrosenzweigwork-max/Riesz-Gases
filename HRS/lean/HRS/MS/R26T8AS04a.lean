import Mathlib

/-!
# S8.2 T8A.S04a: Bochner integral in `Lp E 2 ν` versus the pointwise integral of a joint representative (generic)

If `V : α → Lp E 2 ν` is Bochner integrable and `G` is a jointly a.e. strongly measurable function with
`G t` representing `V t` for a.e. `t`, then the `Lp`-valued integral `∫ V` is represented by `q ↦ ∫ G t q dμ`.
Route: test against `indicatorConstLp` (`L2.inner_indicatorConstLp_eq_inner_setIntegral`), Fubini, and
`ae_eq_of_forall_setIntegral_eq_of_sigmaFinite`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace HRS.MS.R26T8A

theorem r26t8a_s04a_integral_ae {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) [SFinite μ] (ν : Measure β) [IsFiniteMeasure ν]
    (V : α → Lp E 2 ν) (hV : Integrable V μ) (G : α → β → E)
    (hG : AEStronglyMeasurable (Function.uncurry G) (μ.prod ν))
    (hVG : ∀ᵐ t ∂μ, ⇑(V t) =ᵐ[ν] G t) :
    ⇑(∫ t, V t ∂μ) =ᵐ[ν] fun q => ∫ t, G t q ∂μ := by
  classical
  have hsec : ∀ᵐ t ∂μ, Integrable (G t) ν := by
    filter_upwards [hVG] with t ht
    exact ((Lp.memLp (V t)).integrable one_le_two).congr ht
  have hGint : Integrable (Function.uncurry G) (μ.prod ν) := by
    rw [integrable_prod_iff hG]
    refine ⟨hsec, ?_⟩
    refine Integrable.mono' (g := fun t => ((ν univ).toReal ^ (1 / 2 : ℝ)) * ‖V t‖)
      (hV.norm.const_mul _) hG.norm.integral_prod_right' ?_
    filter_upwards [hVG] with t ht
    have h1 : ∫ q, ‖G t q‖ ∂ν = ∫ q, ‖V t q‖ ∂ν :=
      integral_congr_ae (ht.mono fun q hq => by simp [hq])
    have h2 : ∫ q, ‖V t q‖ ∂ν = (eLpNorm (V t) 1 ν).toReal := by
      rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable _),
        eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable _)]
    have h3 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := ν) (f := V t) (p := 1) (q := 2)
      (by norm_num) (Lp.aestronglyMeasurable _)
    have h4 : eLpNorm (V t) 2 ν * ν univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) ≠ ∞ := by
      refine ENNReal.mul_ne_top (Lp.eLpNorm_ne_top _) ?_
      refine ENNReal.rpow_ne_top_of_nonneg ?_ (measure_ne_top ν _)
      norm_num
    have h5 := ENNReal.toReal_mono h4 h3
    rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at h5
    have h6 : (eLpNorm (V t) 2 ν).toReal = ‖V t‖ := by rw [Lp.norm_def]
    rw [h6] at h5
    have h7 : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by norm_num
    rw [h7] at h5
    show ‖∫ q, ‖G t q‖ ∂ν‖ ≤ ((ν univ).toReal ^ (1 / 2 : ℝ)) * ‖V t‖
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), h1, h2]
    linarith [mul_comm ‖V t‖ ((ν univ).toReal ^ (1 / 2 : ℝ))]
  have hRint : Integrable (fun q => ∫ t, G t q ∂μ) ν := hGint.integral_prod_right
  set Xs : Lp E 2 ν := ∫ t, V t ∂μ with hXs
  have hXint : Integrable (⇑Xs) ν := (Lp.memLp Xs).integrable one_le_two
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun s _ _ => hXint.integrableOn)
    (fun s _ _ => hRint.integrableOn) ?_
  intro B hB _
  refine ext_inner_left ℝ fun c => ?_
  have hBν : ν B ≠ ∞ := measure_ne_top ν B
  have h1 : inner ℝ c (∫ q in B, Xs q ∂ν) = inner ℝ (indicatorConstLp 2 hB hBν c) Xs :=
    (L2.inner_indicatorConstLp_eq_inner_setIntegral ℝ hB hBν c Xs).symm
  have h2 : inner ℝ (indicatorConstLp 2 hB hBν c) Xs =
      ∫ t, inner ℝ (indicatorConstLp 2 hB hBν c) (V t) ∂μ :=
    (integral_inner hV (indicatorConstLp 2 hB hBν c)).symm
  have h4 : ∀ᵐ t ∂μ, inner ℝ (indicatorConstLp 2 hB hBν c) (V t) =
      ∫ q in B, inner ℝ c (G t q) ∂ν := by
    filter_upwards [hVG] with t ht
    rw [L2.inner_indicatorConstLp_eq_setIntegral_inner]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae ht] with q hq
    rw [hq]
  have hGB : Integrable (Function.uncurry G) (μ.prod (ν.restrict B)) :=
    hGint.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  have hGB' : Integrable (Function.uncurry fun t q => inner ℝ c (G t q)) (μ.prod (ν.restrict B)) := by
    refine ((innerSL ℝ c).integrable_comp hGB).congr (Eventually.of_forall fun a => ?_)
    simp [Function.uncurry]
  have h5 : ∫ t, ∫ q in B, inner ℝ c (G t q) ∂ν ∂μ = ∫ q in B, ∫ t, inner ℝ c (G t q) ∂μ ∂ν :=
    integral_integral_swap (μ := μ) (ν := ν.restrict B) hGB'
  have h6 : ∀ᵐ q ∂ν, ∫ t, inner ℝ c (G t q) ∂μ = inner ℝ c (∫ t, G t q ∂μ) := by
    filter_upwards [hGint.prod_left_ae] with q hq
    exact integral_inner hq c
  have h7 : ∫ q in B, ∫ t, inner ℝ c (G t q) ∂μ ∂ν = ∫ q in B, inner ℝ c (∫ t, G t q ∂μ) ∂ν :=
    integral_congr_ae (ae_restrict_of_ae h6)
  have h8 : ∫ q in B, inner ℝ c (∫ t, G t q ∂μ) ∂ν = inner ℝ c (∫ q in B, ∫ t, G t q ∂μ ∂ν) :=
    integral_inner hRint.integrableOn c
  rw [h1, h2, integral_congr_ae h4, h5, h7, h8]

end HRS.MS.R26T8A

end
