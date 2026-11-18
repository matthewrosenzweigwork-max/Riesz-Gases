import HRS.MC.CepP4Aux3

/-!
# Packet P4, Aux4: the density integrated against a good test function equals the cube integral
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MC.CepP4

open HRS HRS.MC.CepP3

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d N : ℕ}

theorem ghat_nonneg {f : ℝ → Config d N → ℝ} {T : ℝ}
    (hf0 : ∀ r ∈ Set.Ioo 0 T, ∀ x ∉ collisionSet d N, 0 ≤ f r x) (p : ℝ × (Fin N → Euc d)) :
    0 ≤ ghat f T p := by
  by_cases hp : p ∈ Ioo 0 T ×ˢ liftedFree d N
  · rw [ghat_of_mem hp]; exact hf0 _ hp.1 _ hp.2
  · unfold ghat; rw [Set.indicator_of_notMem hp]

theorem lintegral_eq_ofReal_Bfun {f : ℝ → Config d N → ℝ} {T : ℝ}
    (hgc : ContinuousOn (fun p : ℝ × (Fin N → Euc d) => f p.1 (mkC p.2)) (Ioo 0 T ×ˢ liftedFree d N))
    (hfs : Measurable (ghat f T))
    (hf0 : ∀ r ∈ Set.Ioo 0 T, ∀ x ∉ collisionSet d N, 0 ≤ f r x)
    {ψ : Config d N → ℝ} {δ : ℝ} (hψ : Good ψ δ) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    ∫⁻ x in (collisionSet d N)ᶜ, ENNReal.ofReal (fhat f T (t, x)) * ENNReal.ofReal (ψ x)
      = ENNReal.ofReal (Bfun f T ψ t) := by
  set H : Config d N → ℝ≥0∞ := fun x => ENNReal.ofReal (fhat f T (t, x)) * ENNReal.ofReal (ψ x) with hH
  have hfhm : Measurable (fun x : Config d N => fhat f T (t, x)) :=
    hfs.comp (measurable_const.prodMk measurable_repC)
  have hψm : Measurable ψ := hψ.1.measurable
  have hHm : Measurable H := (ENNReal.measurable_ofReal.comp hfhm).mul (ENNReal.measurable_ofReal.comp hψm)
  -- step 1: the integrand vanishes on the collisions
  have h1 : ∫⁻ x in (collisionSet d N)ᶜ, H x = ∫⁻ x, H x := by
    refine setLIntegral_eq_of_support_subset (fun x hx => ?_)
    have hψx : ψ x ≠ 0 := by
      intro h0; apply hx; simp [hH, h0]
    exact hψ.notMem hψx
  -- step 2: transfer to the cube
  have h2 : ∫⁻ x, H x = ∫⁻ Y in cubeQ d N, H (mkC Y) :=
    ((mkC_measurePreserving_cube (d := d) (N := N)).lintegral_comp hHm).symm
  -- step 3: on the cube
  have h3 : ∫⁻ Y in cubeQ d N, H (mkC Y) =
      ∫⁻ Y in cubeQ d N, ENNReal.ofReal (ψ (mkC Y) * ghat f T (t, Y)) := by
    refine setLIntegral_congr_fun measurableSet_cubeQ (fun Y hY => ?_)
    have hr : fhat f T (t, mkC Y) = ghat f T (t, Y) := by
      unfold fhat; simp only; rw [repC_mkC_of_mem hY]
    simp only [hH, hr]
    rw [ENNReal.ofReal_mul (hψ.2.1 _), mul_comm]
  -- step 4: integral
  have h4 : ENNReal.ofReal (Bfun f T ψ t) =
      ∫⁻ Y in cubeQ d N, ENNReal.ofReal (ψ (mkC Y) * ghat f T (t, Y)) := by
    unfold Bfun
    exact ofReal_integral_eq_lintegral_ofReal (integrableOn_cube hgc hfs hψ ht)
      (Eventually.of_forall fun Y => mul_nonneg (hψ.2.1 _) (ghat_nonneg hf0 _))
  rw [h1, h2, h3, h4]

end HRS.MC.CepP4
