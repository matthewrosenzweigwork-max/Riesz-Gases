import HRS.Commutator.Torus.LEIBTAux1

/-!
# LEIB-T helpers, part 2: `L^p` norms of lifts of torus functions over the boxes `(-N,N]^d`
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

lemma leibt_eLpNorm_box_eq {E : Type*} [NormedAddCommGroup E] {η : ℝ} (hη : 0 < η) (M : ℕ) {N : ℝ}
    (hN : N = ((M : ℝ) + 1 / 2) / η) {G : Torus d → E} (hG : Continuous G) {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hpt : p ≠ ⊤) :
    eLpNorm ((leibt_boxN d N).indicator (fun y : Euc d => G (Torus.mk (η • y)))) p volume =
      ENNReal.ofReal ((2 * N) ^ d) ^ (1 / p.toReal) * eLpNorm G p volume := by
  subst hN
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hGm : AEStronglyMeasurable G (volume : Measure (Torus d)) := hG.aestronglyMeasurable
  have hLm : AEStronglyMeasurable ((leibt_boxN d (((M : ℝ) + 1 / 2) / η)).indicator
      (fun y : Euc d => G (Torus.mk (η • y)))) (volume : Measure (Euc d)) :=
    ((hG.comp (HRS.Torus.continuous_mk.comp (continuous_const_smul η))).aestronglyMeasurable).indicator
      (leibt_measurableSet_boxN _)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hLm, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hGm,
    ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  congr 1
  have hΨ : Measurable (fun x : Torus d => ‖G x‖ₑ ^ p.toReal) :=
    hG.enorm.measurable.pow_const _
  have hbox := leibt_lintegral_boxN hη M (fun x : Torus d => ‖G x‖ₑ ^ p.toReal) hΨ
  rw [← hbox, ← lintegral_indicator (leibt_measurableSet_boxN _)]
  congr 1
  funext y
  by_cases hy : y ∈ leibt_boxN d (((M : ℝ) + 1 / 2) / η)
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, enorm_zero, ENNReal.zero_rpow_of_pos hpr]

lemma leibt_eLpNorm_box_top_le {E : Type*} [NormedAddCommGroup E] {η : ℝ} (hη : 0 < η) (M : ℕ) {N : ℝ}
    (hN : N = ((M : ℝ) + 1 / 2) / η) {G : Torus d → E} (hG : Continuous G) :
    eLpNorm ((leibt_boxN d N).indicator (fun y : Euc d => G (Torus.mk (η • y)))) ⊤ volume ≤
      eLpNorm G ⊤ volume := by
  subst hN
  have hGm : AEStronglyMeasurable G (volume : Measure (Torus d)) := hG.aestronglyMeasurable
  have hLm : AEStronglyMeasurable ((leibt_boxN d (((M : ℝ) + 1 / 2) / η)).indicator
      (fun y : Euc d => G (Torus.mk (η • y)))) (volume : Measure (Euc d)) :=
    ((hG.comp (HRS.Torus.continuous_mk.comp (continuous_const_smul η))).aestronglyMeasurable).indicator
      (leibt_measurableSet_boxN _)
  rw [eLpNorm_exponent_top hLm, eLpNorm_exponent_top hGm]
  set c := eLpNormEssSup G volume with hc
  have hA : MeasurableSet {x : Torus d | c < ‖G x‖ₑ} :=
    measurableSet_lt measurable_const hG.enorm.measurable
  have hA0 : volume {x : Torus d | c < ‖G x‖ₑ} = 0 := by
    have := enorm_ae_le_eLpNormEssSup G (volume : Measure (Torus d))
    rw [ae_iff] at this
    simpa using this
  have h1 := leibt_lintegral_boxN hη M ({x : Torus d | c < ‖G x‖ₑ}.indicator (fun _ => (1 : ℝ≥0∞)))
    (measurable_const.indicator hA)
  rw [lintegral_indicator hA, setLIntegral_const, hA0, mul_zero, mul_zero] at h1
  refine eLpNormEssSup_le_of_ae_enorm_bound ?_
  have h2 : ∀ᵐ y ∂(volume.restrict (leibt_boxN d (((M : ℝ) + 1 / 2) / η))),
      ({x : Torus d | c < ‖G x‖ₑ}.indicator (fun _ => (1 : ℝ≥0∞))) (Torus.mk (η • y)) = 0 := by
    refine (lintegral_eq_zero_iff ?_).1 h1
    exact (measurable_const.indicator hA).comp (HRS.Torus.continuous_mk.measurable.comp (measurable_const_smul η))
  rw [ae_restrict_iff' (leibt_measurableSet_boxN _)] at h2
  filter_upwards [h2] with y hy
  by_cases hyb : y ∈ leibt_boxN d (((M : ℝ) + 1 / 2) / η)
  · rw [Set.indicator_of_mem hyb]
    have := hy hyb
    by_contra hcon
    push Not at hcon
    rw [Set.indicator_of_mem (show Torus.mk (η • y) ∈ {x : Torus d | c < ‖G x‖ₑ} from hcon)] at this
    exact one_ne_zero this
  · rw [Set.indicator_of_notMem hyb, enorm_zero]; exact zero_le

end HRS.Commutator.TorusNote
