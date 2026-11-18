import HRS.MC.E213U10E

/-!
# Packet e213u10, part F: Lipschitz bound and domination of the drift functional

`u10_FD_lip_core`: `|FD(w,β) - FD(w',β')| ≤ c√L (‖β-β'‖ + ‖w-w'‖‖β‖)` (with `c = CD(1+CY)`);
`u10_FD_abs_le`: `|FD(w,β)| ≤ CD √L ‖β‖`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213U10

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ}

/-- The conclusion of `winDrift_near` for fixed `a, b` and constant `CD`. -/
def U10_DriftNear (hE : EdgeworthHyp S β₀ m) (T a : ℝ) (ha : 0 ≤ a) (b CD : ℝ) : Prop :=
  ∀ (bq : ℝ → NegSobolev d (rLvl d)), Measurable (nearCoef 0 bq) →
    IntegrableOn (fun v => ‖bq v‖) (Set.Icc b (a + T)) →
    ∀ u u' : ℝ, 0 ≤ u → u ≤ u' → u' ≤ a + T →
      ‖winDrift (regime S β₀ hE) m T a ha (nearCoef b (fun v => NegSobolev.embed m (bq v))) u u'‖ ≤
        CD * ∫ v in Set.Ioc u u' ∩ Set.Ici b, ‖bq v‖

/-- The bound `‖winPred w τ‖ ≤ CY ‖w‖`. -/
def U10_PredBound (hE : EdgeworthHyp S β₀ m) (T a : ℝ) (ha : 0 ≤ a) (CY : ℝ) : Prop :=
  ∀ (w : PathSpace d m (a + T)) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) (a + T) →
    ‖winPred (regime S β₀ hE) m T a ha w τ‖ ≤ CY * ‖w‖

theorem u10_cb_nonneg {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] (Φ : B → ℝ) : 0 ≤ cbNorm 5 Φ := by
  unfold cbNorm
  exact Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _

theorem u10_integral_set_nonneg (s : Set ℝ) (f : ℝ → ℝ) (hf : ∀ v, 0 ≤ f v) : 0 ≤ ∫ v in s, f v :=
  setIntegral_nonneg_of_ae_restrict (Filter.Eventually.of_forall hf) |>.trans_eq rfl

theorem u10_SD_abs_le (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) (hcb : cbNorm 5 Φ ≤ 1) (b L : ℝ) (hL : 0 ≤ L)
    (hH : a + T ≤ b + L) (CD : ℝ) (hCD0 : 0 ≤ CD) (hCD : U10_DriftNear hE T a ha b CD)
    (x : PathSpace d (rLvl d) L × L2Path d (rLvl d) L) {τ u u' : ℝ} (hu : 0 ≤ u) (huτ : u ≤ τ) (hτu' : τ ≤ u')
    (hu' : u' ≤ a + T) :
    |u10_SD hE T a ha Φ b L hL hH x τ u u'| ≤ CD * ∫ v in Set.Ioc u u' ∩ Set.Ici b, ‖u10_bq b L x.2 v‖ := by
  have hτ : τ ∈ Set.Icc (0 : ℝ) (a + T) := ⟨hu.trans huτ, hτu'.trans hu'⟩
  have hreg := HRS.MC.E213U5.Ucan_regular_proof hE T hT a ha Φ hΦ
  have huu' : u ≤ u' := huτ.trans hτu'
  have hD : ‖winDrift (regime S β₀ hE) m T a ha (u10_cD b L m x.2) u u'‖ ≤
      CD * ∫ v in Set.Ioc u u' ∩ Set.Ici b, ‖u10_bq b L x.2 v‖ :=
    hCD (u10_bq b L x.2) (u10_nearCoef_meas 0 (u10_bq_meas b L x.2))
      ((u10_bq_int b L hL x.2).mono_set (Set.Icc_subset_Icc_right hH)) u u' hu huu' hu'
  have hA := u10_fderiv_norm_le hE T a ha Φ hreg hτ (u10_Y hE T a ha b L hL hH x.1 τ)
  have hI : 0 ≤ ∫ v in Set.Ioc u u' ∩ Set.Ici b, ‖u10_bq b L x.2 v‖ := integral_nonneg fun _ => norm_nonneg _
  unfold u10_SD rsSumD
  rw [← Real.norm_eq_abs]
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  calc ‖fderiv ℝ (Ucan hE T a ha Φ τ) (u10_Y hE T a ha b L hL hH x.1 τ)‖ *
        ‖winDrift (regime S β₀ hE) m T a ha (u10_cD b L m x.2) u u'‖
      ≤ 1 * (CD * ∫ v in Set.Ioc u u' ∩ Set.Ici b, ‖u10_bq b L x.2 v‖) := by
        refine mul_le_mul (hA.trans hcb) hD (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem u10_SD_diff_le (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) (hcb : cbNorm 5 Φ ≤ 1) (b L : ℝ) (hL : 0 ≤ L)
    (hH : a + T ≤ b + L) (CD CY : ℝ) (hCD0 : 0 ≤ CD) (hCY0 : 0 ≤ CY) (hCD : U10_DriftNear hE T a ha b CD)
    (hCY : U10_PredBound hE T a ha CY)
    (x x' : PathSpace d (rLvl d) L × L2Path d (rLvl d) L) {τ u u' : ℝ} (hu : 0 ≤ u) (huτ : u ≤ τ) (hτu' : τ ≤ u')
    (hu' : u' ≤ a + T) :
    |u10_SD hE T a ha Φ b L hL hH x τ u u' - u10_SD hE T a ha Φ b L hL hH x' τ u u'| ≤
      CD * CY * ‖x.1 - x'.1‖ * (∫ v in Set.Ioc u u' ∩ Set.Ici b, ‖u10_bq b L x.2 v‖) +
        CD * ∫ v in Set.Ioc u u' ∩ Set.Ici b, ‖u10_bqd b L x.2 x'.2 v‖ := by
  have hτ : τ ∈ Set.Icc (0 : ℝ) (a + T) := ⟨hu.trans huτ, hτu'.trans hu'⟩
  have hreg := HRS.MC.E213U5.Ucan_regular_proof hE T hT a ha Φ hΦ
  have huu' : u ≤ u' := huτ.trans hτu'
  have hsplit := u10_cD_split hE T hT a ha b L hL hH x.2 x'.2 hu huu' hu'
  set D := winDrift (regime S β₀ hE) m T a ha (u10_cD b L m x.2) u u' with hDdef
  set D' := winDrift (regime S β₀ hE) m T a ha (u10_cD b L m x'.2) u u' with hD'def
  set Dδ := winDrift (regime S β₀ hE) m T a ha
    (nearCoef b (fun v => NegSobolev.embed m (u10_bqd b L x.2 x'.2 v))) u u' with hDδdef
  have hDn : ‖D‖ ≤ CD * ∫ v in Set.Ioc u u' ∩ Set.Ici b, ‖u10_bq b L x.2 v‖ :=
    hCD (u10_bq b L x.2) (u10_nearCoef_meas 0 (u10_bq_meas b L x.2))
      ((u10_bq_int b L hL x.2).mono_set (Set.Icc_subset_Icc_right hH)) u u' hu huu' hu'
  have hDδn : ‖Dδ‖ ≤ CD * ∫ v in Set.Ioc u u' ∩ Set.Ici b, ‖u10_bqd b L x.2 x'.2 v‖ :=
    hCD (u10_bqd b L x.2 x'.2) (u10_nearCoef_meas 0 (u10_bqd_meas b L x.2 x'.2))
      ((u10_bqd_int b L hL x.2 x'.2).mono_set (Set.Icc_subset_Icc_right hH)) u u' hu huu' hu'
  set A := fderiv ℝ (Ucan hE T a ha Φ τ) (u10_Y hE T a ha b L hL hH x.1 τ) with hAdef
  set A' := fderiv ℝ (Ucan hE T a ha Φ τ) (u10_Y hE T a ha b L hL hH x'.1 τ) with hA'def
  have hA' : ‖A'‖ ≤ 1 := (u10_fderiv_norm_le hE T a ha Φ hreg hτ _).trans hcb
  have hAA' : ‖A - A'‖ ≤ CY * ‖x.1 - x'.1‖ := by
    refine (u10_fderiv_lip hE T a ha Φ hreg hτ _ _).trans ?_
    have h := u10_Y_sub_norm_le hE T hT a ha b L hL hH CY hCY0 hCY x.1 x'.1 hτ
    calc cbNorm 5 Φ * ‖u10_Y hE T a ha b L hL hH x.1 τ - u10_Y hE T a ha b L hL hH x'.1 τ‖
        ≤ 1 * (CY * ‖x.1 - x'.1‖) := mul_le_mul hcb h (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hI₁ : 0 ≤ ∫ v in Set.Ioc u u' ∩ Set.Ici b, ‖u10_bq b L x.2 v‖ := integral_nonneg fun _ => norm_nonneg _
  have hdiff : D - D' = Dδ := by rw [hsplit]; abel
  unfold u10_SD rsSumD
  have e : A D - A' D' = (A - A') D + A' Dδ := by
    rw [← hdiff, ContinuousLinearMap.sub_apply, map_sub]; ring
  rw [e]
  calc |(A - A') D + A' Dδ| ≤ |(A - A') D| + |A' Dδ| := abs_add_le _ _
    _ ≤ ‖A - A'‖ * ‖D‖ + ‖A'‖ * ‖Dδ‖ := by
        rw [← Real.norm_eq_abs, ← Real.norm_eq_abs]
        exact add_le_add ((A - A').le_opNorm D) (A'.le_opNorm Dδ)
    _ ≤ (CY * ‖x.1 - x'.1‖) * (CD * (∫ v in Set.Ioc u u' ∩ Set.Ici b, ‖u10_bq b L x.2 v‖)) +
          1 * (CD * ∫ v in Set.Ioc u u' ∩ Set.Ici b, ‖u10_bqd b L x.2 x'.2 v‖) := by
        refine add_le_add (mul_le_mul hAA' hDn (norm_nonneg _) (by positivity)) ?_
        exact mul_le_mul hA' hDδn (norm_nonneg _) zero_le_one
    _ = _ := by ring

theorem u10_isRS_zero (T : ℝ) : IsRS T (fun _ _ _ => (0 : ℝ)) 0 := by
  intro ε hε
  exact ⟨1, one_pos, fun n u τ _ _ _ _ _ => by simpa using hε⟩

theorem u10_FD_lip_core (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) (hcb : cbNorm 5 Φ ≤ 1) (b L : ℝ) (hL : 0 ≤ L)
    (hH : a + T ≤ b + L) (CD CY : ℝ) (hCD0 : 0 ≤ CD) (hCY0 : 0 ≤ CY) (hCD : U10_DriftNear hE T a ha b CD)
    (hCY : U10_PredBound hE T a ha CY)
    (x x' : PathSpace d (rLvl d) L × L2Path d (rLvl d) L) :
    |u10_FD hE T a ha Φ b L hL hH x - u10_FD hE T a ha Φ b L hL hH x'| ≤
      CD * CY * Real.sqrt L * ‖x.1 - x'.1‖ * ‖x.2‖ + CD * Real.sqrt L * ‖x.2 - x'.2‖ := by
  have hH0 : 0 < a + T := by linarith
  set Dw := ‖x.1 - x'.1‖ with hDw
  have hDw0 : 0 ≤ Dw := norm_nonneg _
  set F : ℝ → ℝ := fun v => CD * CY * Dw * ‖u10_bq b L x.2 v‖ + CD * ‖u10_bqd b L x.2 x'.2 v‖ with hF
  have hFnn : ∀ v, 0 ≤ F v := fun v => by positivity
  have hI1 := u10_bq_int b L hL x.2
  have hI2 := u10_bqd_int b L hL x.2 x'.2
  have hFint : IntegrableOn F (Set.Icc b (b + L)) := (hI1.const_mul (CD * CY * Dw)).add (hI2.const_mul CD)
  set g : ℝ → ℝ := Set.indicator (Set.Ici b) F with hg
  have hg0 : ∀ v, 0 ≤ g v := fun v => Set.indicator_nonneg (fun v _ => hFnn v) v
  have hsubset : ∀ u u' : ℝ, u' ≤ a + T → Set.Ioc u u' ∩ Set.Ici b ⊆ Set.Icc b (b + L) := fun u u' hu' v hv =>
    ⟨hv.2, (hv.1.2.trans hu').trans hH⟩
  have hgi : IntegrableOn g (Set.Ioc 0 (a + T)) := by
    have h1 : Integrable (Set.indicator (Set.Icc b (b + L)) F) volume :=
      (integrable_indicator_iff measurableSet_Icc).2 hFint
    refine h1.integrableOn.congr_fun (fun v hv => ?_) measurableSet_Ioc
    by_cases hbv : b ≤ v
    · have : v ∈ Set.Icc b (b + L) := ⟨hbv, hv.2.trans hH⟩
      simp [hg, Set.indicator_of_mem, hbv, this]
    · simp [hg, hbv, Set.indicator_of_notMem (show v ∉ Set.Icc b (b + L) from fun h => hbv h.1)]
  have hbound : ∀ τ u u' : ℝ, 0 ≤ u → u ≤ τ → τ ≤ u' → u' ≤ a + T →
      |u10_SD hE T a ha Φ b L hL hH x τ u u' - u10_SD hE T a ha Φ b L hL hH x' τ u u'| ≤
        ∫ v in Set.Ioc u u', g v := by
    intro τ u u' hu huτ hτu' hu'
    refine (u10_SD_diff_le hE T hT a ha Φ hΦ hcb b L hL hH CD CY hCD0 hCY0 hCD hCY x x' hu huτ hτu' hu').trans ?_
    rw [hg, setIntegral_indicator measurableSet_Ici]
    have i1 : IntegrableOn (fun v => ‖u10_bq b L x.2 v‖) (Set.Ioc u u' ∩ Set.Ici b) :=
      hI1.mono_set (hsubset u u' hu')
    have i2 : IntegrableOn (fun v => ‖u10_bqd b L x.2 x'.2 v‖) (Set.Ioc u u' ∩ Set.Ici b) :=
      hI2.mono_set (hsubset u u' hu')
    rw [hF]
    simp only []
    rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul]
  have key := u10_rs_cmp hH0 (u10_SD_isRS hE T hT a ha Φ hΦ b L hL hH x)
    (u10_SD_isRS hE T hT a ha Φ hΦ b L hL hH x') g hg0 hgi hbound
  refine key.trans ?_
  have hsub0 : Set.Ioc 0 (a + T) ∩ Set.Ici b ⊆ Set.Icc b (b + L) := hsubset 0 (a + T) le_rfl
  calc ∫ v in Set.Ioc 0 (a + T), g v = ∫ v in Set.Ioc 0 (a + T) ∩ Set.Ici b, F v := by
        rw [hg, setIntegral_indicator measurableSet_Ici]
    _ ≤ ∫ v in Set.Icc b (b + L), F v :=
        setIntegral_mono_set hFint (Filter.Eventually.of_forall hFnn) (Filter.Eventually.of_forall hsub0)
    _ = CD * CY * Dw * (∫ v in Set.Icc b (b + L), ‖u10_bq b L x.2 v‖) +
          CD * (∫ v in Set.Icc b (b + L), ‖u10_bqd b L x.2 x'.2 v‖) := by
        rw [hF]
        simp only []
        rw [integral_add (hI1.const_mul _) (hI2.const_mul _), integral_const_mul, integral_const_mul]
    _ ≤ CD * CY * Dw * (Real.sqrt L * ‖x.2‖) + CD * (Real.sqrt L * ‖x.2 - x'.2‖) := by
        have := u10_bq_int_le b L hL x.2
        have := u10_bqd_int_le b L hL x.2 x'.2
        gcongr
    _ = _ := by ring

theorem u10_FD_abs_le (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) (hcb : cbNorm 5 Φ ≤ 1) (b L : ℝ) (hL : 0 ≤ L)
    (hH : a + T ≤ b + L) (CD : ℝ) (hCD0 : 0 ≤ CD) (hCD : U10_DriftNear hE T a ha b CD)
    (x : PathSpace d (rLvl d) L × L2Path d (rLvl d) L) :
    |u10_FD hE T a ha Φ b L hL hH x| ≤ CD * Real.sqrt L * ‖x.2‖ := by
  have hH0 : 0 < a + T := by linarith
  set F : ℝ → ℝ := fun v => CD * ‖u10_bq b L x.2 v‖ with hF
  have hFnn : ∀ v, 0 ≤ F v := fun v => by positivity
  have hI1 := u10_bq_int b L hL x.2
  have hFint : IntegrableOn F (Set.Icc b (b + L)) := hI1.const_mul CD
  set g : ℝ → ℝ := Set.indicator (Set.Ici b) F with hg
  have hg0 : ∀ v, 0 ≤ g v := fun v => Set.indicator_nonneg (fun v _ => hFnn v) v
  have hsubset : ∀ u u' : ℝ, u' ≤ a + T → Set.Ioc u u' ∩ Set.Ici b ⊆ Set.Icc b (b + L) := fun u u' hu' v hv =>
    ⟨hv.2, (hv.1.2.trans hu').trans hH⟩
  have hgi : IntegrableOn g (Set.Ioc 0 (a + T)) := by
    have h1 : Integrable (Set.indicator (Set.Icc b (b + L)) F) volume :=
      (integrable_indicator_iff measurableSet_Icc).2 hFint
    refine h1.integrableOn.congr_fun (fun v hv => ?_) measurableSet_Ioc
    by_cases hbv : b ≤ v
    · have : v ∈ Set.Icc b (b + L) := ⟨hbv, hv.2.trans hH⟩
      simp [hg, Set.indicator_of_mem, hbv, this]
    · simp [hg, hbv, Set.indicator_of_notMem (show v ∉ Set.Icc b (b + L) from fun h => hbv h.1)]
  have hbound : ∀ τ u u' : ℝ, 0 ≤ u → u ≤ τ → τ ≤ u' → u' ≤ a + T →
      |u10_SD hE T a ha Φ b L hL hH x τ u u' - (fun _ _ _ => (0 : ℝ)) τ u u'| ≤ ∫ v in Set.Ioc u u', g v := by
    intro τ u u' hu huτ hτu' hu'
    simp only [sub_zero]
    refine (u10_SD_abs_le hE T hT a ha Φ hΦ hcb b L hL hH CD hCD0 hCD x hu huτ hτu' hu').trans ?_
    rw [hg, setIntegral_indicator measurableSet_Ici, hF]
    simp only []
    rw [integral_const_mul]
  have key := u10_rs_cmp hH0 (u10_SD_isRS hE T hT a ha Φ hΦ b L hL hH x) (u10_isRS_zero (a + T)) g hg0 hgi hbound
  rw [sub_zero] at key
  refine key.trans ?_
  have hsub0 : Set.Ioc 0 (a + T) ∩ Set.Ici b ⊆ Set.Icc b (b + L) := hsubset 0 (a + T) le_rfl
  calc ∫ v in Set.Ioc 0 (a + T), g v = ∫ v in Set.Ioc 0 (a + T) ∩ Set.Ici b, F v := by
        rw [hg, setIntegral_indicator measurableSet_Ici]
    _ ≤ ∫ v in Set.Icc b (b + L), F v :=
        setIntegral_mono_set hFint (Filter.Eventually.of_forall hFnn) (Filter.Eventually.of_forall hsub0)
    _ = CD * (∫ v in Set.Icc b (b + L), ‖u10_bq b L x.2 v‖) := by
        rw [hF]
        simp only []
        rw [integral_const_mul]
    _ ≤ CD * (Real.sqrt L * ‖x.2‖) := by
        have := u10_bq_int_le b L hL x.2
        gcongr
    _ = _ := by ring

end HRS.MC.E213U10

end
