import HRS.MC.E213U10C

/-!
# Packet e213u10, part D: the near coefficient of an `L²([0,L];E_r)` element

`u10_bq b L β v = β (v - b)` (the coefficient on `[b, b+L]`), its measurability and integrability, the translation of
integrals, and the `L¹ ≤ √L · L²` bound on `[b, b+L]`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213U10

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ}

theorem u10_translate_hmp (b L : ℝ) :
    MeasurePreserving (fun v : ℝ => v - b) (volume.restrict (Set.Icc b (b + L)))
      (volume.restrict (Set.Icc 0 L)) := by
  have h := (measurePreserving_sub_right (volume : Measure ℝ) b).restrict_preimage
    (measurableSet_Icc (a := (0 : ℝ)) (b := L))
  have hpre : (fun v : ℝ => v - b) ⁻¹' Set.Icc 0 L = Set.Icc b (b + L) := by
    ext v
    simp only [Set.mem_preimage, Set.mem_Icc, sub_nonneg, sub_le_iff_le_add]
    rw [add_comm L b]
  rwa [hpre] at h

theorem u10_translate_integral (b L : ℝ) (F : ℝ → ℝ) :
    ∫ v in Set.Icc b (b + L), F (v - b) = ∫ t in Set.Icc 0 L, F t :=
  (u10_translate_hmp b L).integral_comp (Homeomorph.subRight b).measurableEmbedding F

/-- The coefficient on `[b, b+L]` of an `L²` element (the Lp representative, translated). -/
def u10_bq (b L : ℝ) (β : L2Path d (rLvl d) L) : ℝ → NegSobolev d (rLvl d) :=
  fun v => (β : ℝ → NegSobolev d (rLvl d)) (v - b)

theorem u10_bq_memLp (b L : ℝ) (β : L2Path d (rLvl d) L) :
    MemLp (u10_bq b L β) 2 (volume.restrict (Set.Icc b (b + L))) :=
  (Lp.memLp β).comp_measurePreserving (u10_translate_hmp b L)

theorem u10_bq_meas (b L : ℝ) (β : L2Path d (rLvl d) L) : Measurable (u10_bq b L β) :=
  (Lp.stronglyMeasurable β).measurable.comp (measurable_sub_const b)

theorem u10_bq_int (b L : ℝ) (hL : 0 ≤ L) (β : L2Path d (rLvl d) L) :
    IntegrableOn (fun v => ‖u10_bq b L β v‖) (Set.Icc b (b + L)) := by
  have hfin : IsFiniteMeasure (volume.restrict (Set.Icc b (b + L))) :=
    ⟨by rw [Measure.restrict_apply_univ]; simp⟩
  have h1 : MemLp (u10_bq b L β) 1 (volume.restrict (Set.Icc b (b + L))) :=
    (u10_bq_memLp b L β).mono_exponent (by norm_num)
  exact (memLp_one_iff_integrable.1 h1).norm

theorem u10_bq_int_le (b L : ℝ) (hL : 0 ≤ L) (β : L2Path d (rLvl d) L) :
    ∫ v in Set.Icc b (b + L), ‖u10_bq b L β v‖ ≤ Real.sqrt L * ‖β‖ := by
  have := u10_translate_integral b L (fun t => ‖(β : ℝ → NegSobolev d (rLvl d)) t‖)
  unfold u10_bq
  rw [this]
  exact u10_L1_le_L2 L hL β

/-- The pointwise difference of two coefficients. -/
def u10_bqd (b L : ℝ) (β β' : L2Path d (rLvl d)  L) : ℝ → NegSobolev d (rLvl d) :=
  fun v => u10_bq b L β v - u10_bq b L β' v

theorem u10_bqd_meas (b L : ℝ) (β β' : L2Path d (rLvl d) L) : Measurable (u10_bqd b L β β') :=
  (u10_bq_meas b L β).sub (u10_bq_meas b L β')

theorem u10_bqd_int (b L : ℝ) (hL : 0 ≤ L) (β β' : L2Path d (rLvl d) L) :
    IntegrableOn (fun v => ‖u10_bqd b L β β' v‖) (Set.Icc b (b + L)) := by
  refine Integrable.mono' ((u10_bq_int b L hL β).add (u10_bq_int b L hL β'))
    (u10_bqd_meas b L β β').norm.aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)
  simpa [u10_bqd] using norm_sub_le (u10_bq b L β v) (u10_bq b L β' v)

theorem u10_bqd_int_le (b L : ℝ) (hL : 0 ≤ L) (β β' : L2Path d (rLvl d) L) :
    ∫ v in Set.Icc b (b + L), ‖u10_bqd b L β β' v‖ ≤ Real.sqrt L * ‖β - β'‖ := by
  have h1 := u10_translate_integral b L
    (fun t => ‖(β : ℝ → NegSobolev d (rLvl d)) t - (β' : ℝ → NegSobolev d (rLvl d)) t‖)
  have h2 : ∫ t in Set.Icc (0 : ℝ) L, ‖(β : ℝ → NegSobolev d (rLvl d)) t - (β' : ℝ → NegSobolev d (rLvl d)) t‖ =
      ∫ t in Set.Icc (0 : ℝ) L, ‖((β - β' : L2Path d (rLvl d) L) : ℝ → NegSobolev d (rLvl d)) t‖ := by
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub β β'] with t ht
    rw [ht]
    rfl
  unfold u10_bqd u10_bq
  rw [h1, h2]
  exact u10_L1_le_L2 L hL (β - β')

/-- The near part of a measurable coefficient is measurable after cutting at `0`. -/
theorem u10_nearCoef0_meas {E : Type*} [Zero E] [MeasurableSpace E] (b : ℝ) {f : ℝ → E} (hf : Measurable f) :
    Measurable (nearCoef 0 (nearCoef b f)) := by
  unfold nearCoef
  exact Measurable.ite measurableSet_Ici (Measurable.ite measurableSet_Ici hf measurable_const) measurable_const

theorem u10_nearCoef_meas {E : Type*} [Zero E] [MeasurableSpace E] (b : ℝ) {f : ℝ → E} (hf : Measurable f) :
    Measurable (nearCoef b f) := by
  unfold nearCoef
  exact Measurable.ite measurableSet_Ici hf measurable_const

theorem u10_nearCoef_norm_int {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] {b L H : ℝ}
    (hH : H ≤ b + L) {f : ℝ → E} (hfm : Measurable f)
    (hf : IntegrableOn (fun v => ‖f v‖) (Set.Icc b (b + L))) :
    IntegrableOn (fun v => ‖nearCoef b f v‖) (Set.Icc 0 H) := by
  have hg : Integrable (Set.indicator (Set.Icc b (b + L)) (fun v => ‖f v‖)) volume :=
    (integrable_indicator_iff measurableSet_Icc).2 hf
  refine Integrable.mono' hg.integrableOn ((u10_nearCoef_meas b hfm).norm.aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun v hv => ?_))
  by_cases hbv : b ≤ v
  · have hvm : v ∈ Set.Icc b (b + L) := ⟨hbv, hv.2.trans hH⟩
    rw [Set.indicator_of_mem hvm]
    simp [nearCoef, hbv]
  · simp [nearCoef, hbv]

end HRS.MC.E213U10

end
