import HRS.MS.S111K4J02A

/-!
# S11.1 / J02, piece B (S111K4): `timeCoeffOf` is strongly measurable (Pro J02, clause 1)
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4J01

open HRS HRS.Whole HRS.MS.S111K2

section tcm
variable {Ω : Type*} [MeasurableSpace Ω]

theorem k4j_timeCoeffOf_dist (H : ℝ) (q : ℝ × Ω → Coeff) (hqm : Measurable q) (g : TimeCoeff H) (w : Ω)
    (hw : ∫⁻ v in Set.Icc (0 : ℝ) H, ‖q (v, w)‖ₑ < ⊤) :
    dist (timeCoeffOf H q w) g =
      (∫⁻ v in Set.Icc (0 : ℝ) H, ‖q (v, w) - (g : ℝ → Coeff) v‖ₑ).toReal := by
  have hm : AEStronglyMeasurable (fun v => q (v, w)) (volume.restrict (Set.Icc (0 : ℝ) H)) :=
    (hqm.comp measurable_prodMk_right).aestronglyMeasurable
  have hmem : MemLp (fun v => q (v, w)) 1 (volume.restrict (Set.Icc (0 : ℝ) H)) :=
    memLp_one_iff_integrable.2 ⟨hm, hw⟩
  have htc : timeCoeffOf H q w = hmem.toLp (fun v => q (v, w)) := by
    unfold timeCoeffOf; rw [dif_pos hmem]
  rw [htc, dist_eq_norm, Lp.norm_def]
  congr 1
  rw [eLpNorm_congr_ae ((Lp.coeFn_sub _ _).trans ((hmem.coeFn_toLp).sub (Eventually.of_forall fun _ => rfl))),
    eLpNorm_one_eq_lintegral_enorm]
  · rfl
  · exact hm.sub (Lp.aestronglyMeasurable g)

theorem k4j_timeCoeffOf_dist_bad (H : ℝ) (q : ℝ × Ω → Coeff) (g : TimeCoeff H) (w : Ω)
    (hw : ¬ ∫⁻ v in Set.Icc (0 : ℝ) H, ‖q (v, w)‖ₑ < ⊤) :
    dist (timeCoeffOf H q w) g = ‖g‖ := by
  have hmem : ¬ MemLp (fun v => q (v, w)) 1 (volume.restrict (Set.Icc (0 : ℝ) H)) := fun h =>
    hw (memLp_one_iff_integrable.1 h).2
  have htc : timeCoeffOf H q w = 0 := by
    unfold timeCoeffOf; rw [dif_neg hmem]
  rw [htc, dist_zero_left]

theorem k4j_timeCoeffOf_stronglyMeasurable (H : ℝ) (q : ℝ × Ω → Coeff) (hqm : Measurable q) :
    StronglyMeasurable (timeCoeffOf H q) := by
  haveI : Fact ((1 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.one_ne_top⟩
  letI : MeasurableSpace (TimeCoeff H) := borel _
  haveI : BorelSpace (TimeCoeff H) := ⟨rfl⟩
  refine Measurable.stronglyMeasurable (k4j_measurable_of_dist fun g => ?_)
  have hA : MeasurableSet {w : Ω | ∫⁻ v in Set.Icc (0 : ℝ) H, ‖q (v, w)‖ₑ < ⊤} :=
    measurableSet_lt (Measurable.lintegral_prod_left' (hqm.enorm)) measurable_const
  have hF : Measurable fun p : ℝ × Ω => ‖q p - (g : ℝ → Coeff) p.1‖ₑ :=
    (hqm.sub ((Lp.stronglyMeasurable g).measurable.comp measurable_fst)).enorm
  have hmeas : Measurable fun w : Ω => (∫⁻ v in Set.Icc (0 : ℝ) H, ‖q (v, w) - (g : ℝ → Coeff) v‖ₑ).toReal :=
    ENNReal.measurable_toReal.comp (Measurable.lintegral_prod_left' hF)
  have hfun : (fun w => dist (timeCoeffOf H q w) g) =
      fun w => if w ∈ {w : Ω | ∫⁻ v in Set.Icc (0 : ℝ) H, ‖q (v, w)‖ₑ < ⊤} then
        (∫⁻ v in Set.Icc (0 : ℝ) H, ‖q (v, w) - (g : ℝ → Coeff) v‖ₑ).toReal else ‖g‖ := by
    funext w
    by_cases hw : w ∈ {w : Ω | ∫⁻ v in Set.Icc (0 : ℝ) H, ‖q (v, w)‖ₑ < ⊤}
    · rw [if_pos hw]; exact k4j_timeCoeffOf_dist H q hqm g w hw
    · rw [if_neg hw]; exact k4j_timeCoeffOf_dist_bad H q g w hw
  rw [hfun]
  exact Measurable.ite hA hmeas measurable_const

end tcm

end HRS.MS.S111K4J01
