import HRS.MS.S111K4J02C
import HRS.MS.S111K4J02D
import HRS.MS.S111K4J02B

/-!
# S11.1 / J02, piece E (S111K4): `L²(P)` bound of a bounded functional of the random time coefficient

`k4j_L2_bound`: `‖L (timeCoeffOf H q ·)‖_{L²(P)} ≤ β ∫_{[a,b]} wt · R` from the slice bound (D) and Minkowski (C).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4J01

open HRS HRS.Whole HRS.MS.S111K2

theorem k4j_eLpNorm_two {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [NormedAddCommGroup E] (P : Measure Ω)
    (f : Ω → E) (hf : AEStronglyMeasurable f P) : eLpNorm f 2 P = (∫⁻ y, ‖f y‖ₑ ^ 2 ∂P) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  simp

theorem k4j_L2_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : ℝ) (q : ℝ × Ω → Coeff) (hqm : Measurable q)
    (R : ℝ → ℝ) (hRi : IntegrableOn R (Set.Icc 0 H)) (hRn : ∀ v ∈ Set.Icc (0 : ℝ) H, 0 ≤ R v)
    (hRs : ∀ᵐ v ∂(volume.restrict (Set.Icc (0 : ℝ) H)), eLpNorm (fun y => q (v, y)) 2 P ≤ ENNReal.ofReal (R v))
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (L : TimeCoeff H →L[ℝ] X)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ H) (wt : ℝ → ℝ) (hwt0 : ∀ v, 0 ≤ wt v)
    (hwt1 : ∀ v, wt v ≤ 1) (hwtm : Measurable wt) (β : ℝ) (hβ : 0 ≤ β)
    (hL : ∀ q' : TimeCoeff H, ‖L q'‖ ≤ β * ∫ z in Set.Ioc a b, wt z * ‖(q' : ℝ → Coeff) z‖) :
    eLpNorm (fun y => L (timeCoeffOf H q y)) 2 P ≤
      ENNReal.ofReal (β * ∫ z in Set.Icc a b, wt z * R z) := by
  have hsub : Set.Ioc a b ⊆ Set.Icc (0 : ℝ) H := fun v hv => ⟨ha.trans hv.1.le, hv.2.trans hb⟩
  set F : ℝ × Ω → ℝ≥0∞ := fun p => ENNReal.ofReal (wt p.1) * ‖q p‖ₑ with hFdef
  have hF : Measurable F :=
    (ENNReal.measurable_ofReal.comp (hwtm.comp measurable_fst)).mul hqm.enorm
  set μ : Measure ℝ := volume.restrict (Set.Ioc a b) with hμ
  have hmink := k4j_minkowski_L2 P μ F hF
  -- the right-hand side of Minkowski
  have hsq : ∀ z, (∫⁻ y, F (z, y) ^ 2 ∂P) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (wt z) * eLpNorm (fun y => q (z, y)) 2 P := by
    intro z
    have h1 : ∀ y, F (z, y) ^ 2 = ENNReal.ofReal (wt z) ^ 2 * ‖q (z, y)‖ₑ ^ 2 := fun y => by
      simp only [hFdef]; rw [mul_pow]
    simp_rw [h1]
    have hqz : AEStronglyMeasurable (fun y => q (z, y)) P :=
      (hqm.comp measurable_prodMk_left).aestronglyMeasurable
    have hmq : Measurable fun y => ‖q (z, y)‖ₑ ^ 2 :=
      ((hqm.comp measurable_prodMk_left).enorm).pow_const 2
    rw [lintegral_const_mul _ hmq,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), k4j_eLpNorm_two P (fun y => q (z, y)) hqz]
    congr 1
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hMk : ∫⁻ z, (∫⁻ y, F (z, y) ^ 2 ∂P) ^ (1 / 2 : ℝ) ∂μ ≤
      ENNReal.ofReal (∫ z in Set.Icc a b, wt z * R z) := by
    have hae : ∀ᵐ z ∂μ, eLpNorm (fun y => q (z, y)) 2 P ≤ ENNReal.ofReal (R z) :=
      ae_restrict_of_ae_restrict_of_subset hsub hRs
    have hRI : IntegrableOn (fun z => wt z * R z) (Set.Ioc a b) volume := by
      have hR1 : IntegrableOn R (Set.Ioc a b) volume := hRi.mono_set hsub
      refine Integrable.mono' hR1 ((hwtm.aemeasurable.mul hR1.aemeasurable).aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub
        ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hRn))] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hwt0 z) hz)]
      calc wt z * R z ≤ 1 * R z := mul_le_mul_of_nonneg_right (hwt1 z) hz
        _ = R z := one_mul _
    have hnn : ∀ᵐ z ∂μ, 0 ≤ wt z * R z := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub
        ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hRn))] with z hz
      exact mul_nonneg (hwt0 z) hz
    rw [integral_Icc_eq_integral_Ioc, ofReal_integral_eq_lintegral_ofReal hRI hnn]
    refine lintegral_mono_ae ?_
    filter_upwards [hae, ae_restrict_of_ae_restrict_of_subset hsub
        ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hRn))] with z hz hzR
    rw [hsq z, ENNReal.ofReal_mul (hwt0 z)]
    exact mul_le_mul' le_rfl hz
  -- assemble
  have hpt : ∀ y, ‖L (timeCoeffOf H q y)‖ₑ ≤ ENNReal.ofReal β * ∫⁻ z, F (z, y) ∂μ := fun y =>
    k4j_slice_bound H q hqm L ha hb wt hwt0 β hβ hL y
  have hQ := k4j_timeCoeffOf_stronglyMeasurable H q hqm
  rw [k4j_eLpNorm_two P _ (L.continuous.comp_stronglyMeasurable hQ).aestronglyMeasurable]
  set Mk := ∫⁻ z, (∫⁻ y, F (z, y) ^ 2 ∂P) ^ (1 / 2 : ℝ) ∂μ with hMkdef
  calc (∫⁻ y, ‖L (timeCoeffOf H q y)‖ₑ ^ 2 ∂P) ^ (1 / 2 : ℝ)
      ≤ (∫⁻ y, (ENNReal.ofReal β * ∫⁻ z, F (z, y) ∂μ) ^ 2 ∂P) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (lintegral_mono fun y => pow_le_pow_left' (hpt y) 2) (by norm_num)
    _ = (ENNReal.ofReal β ^ 2 * ∫⁻ y, (∫⁻ z, F (z, y) ∂μ) ^ 2 ∂P) ^ (1 / 2 : ℝ) := by
        congr 1
        simp_rw [mul_pow]
        exact lintegral_const_mul _ ((Measurable.lintegral_prod_left' hF).pow_const 2)
    _ ≤ (ENNReal.ofReal β ^ 2 * Mk ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (mul_le_mul' le_rfl hmink) (by norm_num)
    _ = ENNReal.ofReal β * Mk := by
        rw [← mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
    _ ≤ ENNReal.ofReal β * ENNReal.ofReal (∫ z in Set.Icc a b, wt z * R z) := mul_le_mul' le_rfl hMk
    _ = _ := by rw [← ENNReal.ofReal_mul hβ]

end HRS.MS.S111K4J01
