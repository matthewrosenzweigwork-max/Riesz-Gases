import HRS.MC.E213U10B
import HRS.MC.E213U7
import HRS.MC.E213U5b
import HRS.MC.E213U1b

/-!
# Packet e213u10, part C: general comparison lemmas

* `u10_rs_cmp`: comparison of two Riemann--Stieltjes integrals when the summands differ by at most `∫_{(u,u']} g` (`isRS_sub_le`
  with the finite measure `g dv`).
* `u10_L1_le_L2`: `∫_{[0,L]} ‖β‖ ≤ √L ‖β‖_{L²}` for an element of `L²([0,L];E)`.
* bounds on `fderiv`/`iteratedFDeriv 2` of the heat function and their Lipschitz constants (from `Ucan_regular`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213U10

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ}

theorem u10_rs_cmp {T : ℝ} (hT : 0 < T) {S₁ S₂ : ℝ → ℝ → ℝ → ℝ} {I₁ I₂ : ℝ} (hS₁ : IsRS T S₁ I₁)
    (hS₂ : IsRS T S₂ I₂) (g : ℝ → ℝ) (hg0 : ∀ v, 0 ≤ g v) (hgi : IntegrableOn g (Set.Ioc 0 T))
    (h : ∀ τ u u' : ℝ, 0 ≤ u → u ≤ τ → τ ≤ u' → u' ≤ T →
      |S₁ τ u u' - S₂ τ u u'| ≤ ∫ v in Set.Ioc u u', g v) :
    |I₁ - I₂| ≤ ∫ v in Set.Ioc 0 T, g v := by
  set ν : Measure ℝ := (volume.restrict (Set.Ioc 0 T)).withDensity (fun v => ENNReal.ofReal (g v)) with hν
  haveI : IsFiniteMeasure ν := ⟨by
    rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_restrict MeasurableSet.univ, Set.univ_inter]
    exact hgi.lintegral_lt_top⟩
  have hν_ioc : ∀ u u' : ℝ, 0 ≤ u → u' ≤ T → (ν (Set.Ioc u u')).toReal = ∫ v in Set.Ioc u u', g v := by
    intro u u' hu hu'
    have hsub : Set.Ioc u u' ⊆ Set.Ioc 0 T := Set.Ioc_subset_Ioc hu hu'
    rw [hν, withDensity_apply _ measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
      Set.inter_eq_left.2 hsub,
      ← ofReal_integral_eq_lintegral_ofReal (hgi.mono_set hsub) (Filter.Eventually.of_forall hg0)]
    exact ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioc fun v _ => hg0 v)
  have key := HRS.MC.E213U1.isRS_sub_le_proof hT hS₁ hS₂ ν 1 (fun τ u u' hu huτ hτu' hu'T => by
    rw [one_mul, hν_ioc u u' hu hu'T]
    exact h τ u u' hu huτ hτu' hu'T)
  rw [one_mul, hν_ioc 0 T le_rfl le_rfl] at key
  exact key

/-- Cauchy--Schwarz on `[0,L]`: `∫ ‖β‖ ≤ √L ‖β‖_{L²}`. -/
theorem u10_L1_le_L2 {E : Type*} [NormedAddCommGroup E] (L : ℝ) (hL : 0 ≤ L)
    (β : Lp E 2 (volume.restrict (Set.Icc (0 : ℝ) L))) :
    ∫ t in Set.Icc (0 : ℝ) L, ‖β t‖ ≤ Real.sqrt L * ‖β‖ := by
  have hfin : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) L)) :=
    ⟨by rw [Measure.restrict_apply_univ]; simp⟩
  have hmem : MemLp β 2 (volume.restrict (Set.Icc (0 : ℝ) L)) := Lp.memLp β
  have hmem1 : MemLp β 1 (volume.restrict (Set.Icc (0 : ℝ) L)) := hmem.mono_exponent (by norm_num)
  have hineq := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict (Set.Icc (0 : ℝ) L)) (f := β)
    (p := 1) (q := 2) (by norm_num) (Lp.aestronglyMeasurable β)
  have h1 : eLpNorm β 1 (volume.restrict (Set.Icc (0 : ℝ) L)) =
      ENNReal.ofReal (∫ t in Set.Icc (0 : ℝ) L, ‖β t‖) := by
    rw [eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable β),
      ofReal_integral_norm_eq_lintegral_enorm (memLp_one_iff_integrable.1 hmem1)]
  have h2 : eLpNorm β 2 (volume.restrict (Set.Icc (0 : ℝ) L)) = ENNReal.ofReal ‖β‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top β)]
  have hmu : (volume.restrict (Set.Icc (0 : ℝ) L)) Set.univ = ENNReal.ofReal L := by
    rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
  have hexp : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = 1 / 2 := by norm_num
  rw [h1, h2, hmu, hexp, ENNReal.ofReal_rpow_of_nonneg hL (by norm_num)] at hineq
  rw [← ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_le_ofReal_iff (by positivity)] at hineq
  calc ∫ t in Set.Icc (0 : ℝ) L, ‖β t‖ ≤ ‖β‖ * L ^ (1 / 2 : ℝ) := hineq
    _ = Real.sqrt L * ‖β‖ := by rw [Real.sqrt_eq_rpow, mul_comm]

/-! ### Bounds on the heat function -/

section HeatBounds

variable (hE : EdgeworthHyp S β₀ m) (T : ℝ) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ)

theorem u10_fderiv_norm_le (hreg : HRS.MC.E213U7.e213u7_Reg hE T a ha Φ) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) (a + T))
    (y : PathSpace d m T) : ‖fderiv ℝ (Ucan hE T a ha Φ τ) y‖ ≤ cbNorm 5 Φ := by
  have h := hreg.2.1 τ hτ 1 (by norm_num) y
  rw [← HRS.MC.E213U7.e213u7_curry_iter, LinearIsometryEquiv.norm_map]
  exact h

theorem u10_fderiv_lip (hreg : HRS.MC.E213U7.e213u7_Reg hE T a ha Φ) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) (a + T))
    (y y' : PathSpace d m T) :
    ‖fderiv ℝ (Ucan hE T a ha Φ τ) y - fderiv ℝ (Ucan hE T a ha Φ τ) y'‖ ≤ cbNorm 5 Φ * ‖y - y'‖ := by
  have h := HRS.MC.E213U7.e213u7_lip_iFD (hreg.1 τ hτ).1 1 (by norm_num) (cbNorm 5 Φ)
    (fun y => hreg.2.1 τ hτ 2 (by norm_num) y) y y'
  rw [← HRS.MC.E213U7.e213u7_curry_iter, ← HRS.MC.E213U7.e213u7_curry_iter, ← map_sub,
    LinearIsometryEquiv.norm_map]
  exact h

theorem u10_iFD2_norm_le (hreg : HRS.MC.E213U7.e213u7_Reg hE T a ha Φ) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) (a + T))
    (y : PathSpace d m T) : ‖iteratedFDeriv ℝ 2 (Ucan hE T a ha Φ τ) y‖ ≤ cbNorm 5 Φ :=
  hreg.2.1 τ hτ 2 (by norm_num) y

theorem u10_iFD2_lip (hreg : HRS.MC.E213U7.e213u7_Reg hE T a ha Φ) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) (a + T))
    (y y' : PathSpace d m T) :
    ‖iteratedFDeriv ℝ 2 (Ucan hE T a ha Φ τ) y - iteratedFDeriv ℝ 2 (Ucan hE T a ha Φ τ) y'‖ ≤
      cbNorm 5 Φ * ‖y - y'‖ :=
  HRS.MC.E213U7.e213u7_lip_iFD (hreg.1 τ hτ).1 2 (by norm_num) (cbNorm 5 Φ)
    (fun y => hreg.2.1 τ hτ 3 (by norm_num) y) y y'

end HeatBounds

end HRS.MC.E213U10

end
