import HRS.MC.E213U11a
import HRS.MC.E213U1b

/-!
# Packet e213u11, file b: pointwise weighted bound for the window drift `D_a`

For `bq : ℝ → E_r` (locally integrable, measurable on `[0,∞)`): `‖𝒟_{a,bq}((0,a+T])‖ ≤ K ∫_{(0,a+T]} e^{-c(a-v)}‖bq v‖ dv`,
with `K, c` independent of `a` and `bq` (near/far split at `b = max (a-1) 0`, `winDrift_near/far/add`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U11

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}

theorem u11_embed_zero (m : ℝ) (hrm : rLvl d ≤ m) : (NegSobolev.embed m (0 : NegSobolev d (rLvl d)) : NegSobolev d m) = 0 := by
  have := NegSobolev.norm_embed_le (d := d) (m := rLvl d) m hrm (0 : NegSobolev d (rLvl d))
  rw [norm_zero] at this
  exact norm_le_zero_iff.1 this

theorem u11_nearCoef_embed {m : ℝ} (hrm : rLvl d ≤ m) (b : ℝ) (bq : ℝ → NegSobolev d (rLvl d)) :
    nearCoef b (fun v => NegSobolev.embed m (bq v)) = fun v => NegSobolev.embed m (nearCoef b bq v) := by
  funext v
  unfold nearCoef
  split_ifs
  · rfl
  · exact (u11_embed_zero m hrm).symm

theorem u11_farCoef_embed {m : ℝ} (hrm : rLvl d ≤ m) (b : ℝ) (bq : ℝ → NegSobolev d (rLvl d)) :
    farCoef b (fun v => NegSobolev.embed m (bq v)) = fun v => NegSobolev.embed m (farCoef b bq v) := by
  funext v
  unfold farCoef
  split_ifs
  · rfl
  · exact (u11_embed_zero m hrm).symm

theorem u11_measurable_nearCoef_near {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {bq : ℝ → E} (hbm : Measurable (nearCoef 0 bq)) {b : ℝ} (hb : 0 ≤ b) :
    Measurable (nearCoef 0 (nearCoef b bq)) := by
  have : nearCoef 0 (nearCoef b bq) = fun v => if b ≤ v then nearCoef 0 bq v else 0 := by
    funext v
    unfold nearCoef
    by_cases h : b ≤ v
    · simp [h, hb.trans h]
    · simp [h]
  rw [this]
  exact Measurable.ite measurableSet_Ici hbm measurable_const

theorem u11_measurable_nearCoef_far {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {bq : ℝ → E} (hbm : Measurable (nearCoef 0 bq)) (b : ℝ) :
    Measurable (nearCoef 0 (farCoef b bq)) := by
  have : nearCoef 0 (farCoef b bq) = fun v => if v < b then nearCoef 0 bq v else 0 := by
    funext v
    unfold nearCoef farCoef
    by_cases h : v < b <;> by_cases h0 : 0 ≤ v <;> simp [h, h0]
  rw [this]
  exact Measurable.ite measurableSet_Iio hbm measurable_const

section Drift

variable {S : PreparedData d} {β₀ m : ℝ}

theorem u11_winDrift_bound (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∀ (a : ℝ) (ha : 0 ≤ a) (bq : ℝ → NegSobolev d (rLvl d)),
      Measurable (nearCoef 0 bq) → IntegrableOn (fun v => ‖bq v‖) (Set.Icc 0 (a + T)) →
      ‖winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (bq v)) 0 (a + T)‖ ≤
        K * ∫ v in Set.Ioc 0 (a + T), Real.exp (-c * (a - v)) * ‖bq v‖ := by
  obtain ⟨Cn, hCn, hnear⟩ := HRS.MC.E213U1.winDrift_near_proof hE T hT
  obtain ⟨Cf, c, hCf, hc, hfar⟩ := HRS.MC.E213U1.winDrift_far_proof hE T hT
  have hrm : rLvl d ≤ m := rLvl_le hE
  refine ⟨max (Cn * Real.exp c) Cf, c, lt_max_of_lt_left (by positivity), hc, fun a ha bq hbm hbi => ?_⟩
  set b : ℝ := max (a - 1) 0 with hb
  have hb0 : 0 ≤ b := le_max_right _ _
  have hba : a - 1 ≤ b := le_max_left _ _
  have hH : (0 : ℝ) ≤ a + T := by linarith
  -- the splitting
  have hsplit : (fun v => NegSobolev.embed m (bq v)) =
      fun v => NegSobolev.embed m (nearCoef b bq v + farCoef b bq v) := by
    funext v
    have := congrFun (nearCoef_add_farCoef b bq) v
    rw [this]
  have hm1 : Measurable (nearCoef 0 (nearCoef b bq)) := u11_measurable_nearCoef_near hbm hb0
  have hm2 : Measurable (nearCoef 0 (farCoef b bq)) := u11_measurable_nearCoef_far hbm b
  have hmeasS : MeasurableSet (Set.Icc (0 : ℝ) (a + T)) := measurableSet_Icc
  have hnn : ∀ s : Set ℝ, s ⊆ Set.Icc (0 : ℝ) (a + T) → MeasurableSet s →
      IntegrableOn (fun v => ‖bq v‖) s := fun s hs _ => hbi.mono_set hs
  have hae : AEStronglyMeasurable bq (volume.restrict (Set.Icc (0 : ℝ) (a + T))) :=
    HRS.MC.E213U1.u1_aesm_of_nearCoef hbm hmeasS (fun v hv => Set.mem_Ici.2 hv.1)
  have hi1 : IntegrableOn (fun v => ‖nearCoef b bq v‖) (Set.Icc 0 (a + T)) := by
    have e1 := HRS.MC.E213U1.u1_aesm_of_nearCoef hm1 hmeasS (fun v hv => Set.mem_Ici.2 hv.1)
    refine hbi.mono' e1.norm (Eventually.of_forall fun v => ?_)
    rw [norm_norm]
    unfold nearCoef
    split_ifs
    · exact le_rfl
    · rw [norm_zero]; exact norm_nonneg _
  have hi2 : IntegrableOn (fun v => ‖farCoef b bq v‖) (Set.Icc 0 (a + T)) := by
    have e2 := HRS.MC.E213U1.u1_aesm_of_nearCoef hm2 hmeasS (fun v hv => Set.mem_Ici.2 hv.1)
    refine hbi.mono' e2.norm (Eventually.of_forall fun v => ?_)
    rw [norm_norm]
    unfold farCoef
    split_ifs
    · exact le_rfl
    · rw [norm_zero]; exact norm_nonneg _
  have hadd := HRS.MC.E213U1.winDrift_add_proof hE T hT a ha (nearCoef b bq) (farCoef b bq) hm1 hm2 hi1 hi2
    0 (a + T) le_rfl hH le_rfl
  rw [hsplit, hadd, ← u11_nearCoef_embed hrm, ← u11_farCoef_embed hrm]
  -- the two bounds
  have hbnear := hnear a ha b hb0 bq hbm (hbi.mono_set (Set.Icc_subset_Icc hb0 le_rfl)) 0 (a + T) le_rfl hH le_rfl
  set w : ℝ → ℝ := fun v => Real.exp (-c * (a - v)) with hw
  have hwpos : ∀ v, 0 < w v := fun v => Real.exp_pos _
  have hwint : IntegrableOn (fun v => w v * ‖bq v‖) (Set.Icc 0 (a + T)) := by
    refine (hbi.const_mul (Real.exp (c * T))).mono' ?_ ?_
    · exact ((Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).aestronglyMeasurable).mul
        hae.norm
    · refine (ae_restrict_iff' hmeasS).2 (Eventually.of_forall fun v hv => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hwpos v).le (norm_nonneg _))]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [hw]; simp only
      exact Real.exp_le_exp.2 (by nlinarith [hv.2, hc])
  have hbfar := hfar a ha b hb0 bq hbm (hwint.mono_set (by
    intro v hv; exact ⟨hv.1.le, hv.2.trans (min_le_right _ _)⟩)) 0 (a + T) le_rfl hH le_rfl
  have hA : (Set.Ioc (0 : ℝ) (a + T)) ⊆ Set.Icc 0 (a + T) := Set.Ioc_subset_Icc_self
  have hwA : IntegrableOn (fun v => w v * ‖bq v‖) (Set.Ioc 0 (a + T)) := hwint.mono_set hA
  have hsum := integral_inter_add_sdiff (μ := volume) (measurableSet_Ici (a := b)) hwA
  have hdiff : Set.Ioc (0 : ℝ) (a + T) \ Set.Ici b = Set.Ioc 0 (a + T) ∩ Set.Iio b := by
    ext v; simp [Set.mem_diff, Set.mem_inter_iff]
  rw [hdiff] at hsum
  have hnear' : ∫ v in Set.Ioc 0 (a + T) ∩ Set.Ici b, ‖bq v‖ ≤
      Real.exp c * ∫ v in Set.Ioc 0 (a + T) ∩ Set.Ici b, w v * ‖bq v‖ := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on ((hbi.mono_set (fun v hv => hA hv.1)).mono_set (Set.Subset.refl _) |>.mono_set
        (fun v hv => hv) |> fun h => h) ?_ (measurableSet_Ioc.inter measurableSet_Ici) fun v hv => ?_
    · exact ((hwA.mono_set Set.inter_subset_left).const_mul _)
    · have hv1 : a - 1 ≤ v := hba.trans hv.2
      have : 1 ≤ Real.exp c * w v := by
        rw [hw]; simp only
        rw [← Real.exp_add, ← Real.exp_zero]
        exact Real.exp_le_exp.2 (by nlinarith)
      calc ‖bq v‖ = 1 * ‖bq v‖ := (one_mul _).symm
        _ ≤ (Real.exp c * w v) * ‖bq v‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
        _ = Real.exp c * (w v * ‖bq v‖) := by ring
  have hI0 : 0 ≤ ∫ v in Set.Ioc 0 (a + T) ∩ Set.Ici b, w v * ‖bq v‖ :=
    setIntegral_nonneg (measurableSet_Ioc.inter measurableSet_Ici) fun v _ => mul_nonneg (hwpos v).le (norm_nonneg _)
  have hI1 : 0 ≤ ∫ v in Set.Ioc 0 (a + T) ∩ Set.Iio b, w v * ‖bq v‖ :=
    setIntegral_nonneg (measurableSet_Ioc.inter measurableSet_Iio) fun v _ => mul_nonneg (hwpos v).le (norm_nonneg _)
  have hK1 : Cn * Real.exp c ≤ max (Cn * Real.exp c) Cf := le_max_left _ _
  have hK2 : Cf ≤ max (Cn * Real.exp c) Cf := le_max_right _ _
  calc _ ≤ ‖winDrift (regime S β₀ hE) m T a ha (nearCoef b fun v => NegSobolev.embed m (bq v)) 0 (a + T)‖ +
        ‖winDrift (regime S β₀ hE) m T a ha (farCoef b fun v => NegSobolev.embed m (bq v)) 0 (a + T)‖ :=
        norm_add_le _ _
    _ ≤ Cn * (Real.exp c * ∫ v in Set.Ioc 0 (a + T) ∩ Set.Ici b, w v * ‖bq v‖) +
        Cf * ∫ v in Set.Ioc 0 (a + T) ∩ Set.Iio b, w v * ‖bq v‖ :=
        add_le_add (hbnear.trans (mul_le_mul_of_nonneg_left hnear' hCn.le)) hbfar
    _ = (Cn * Real.exp c) * (∫ v in Set.Ioc 0 (a + T) ∩ Set.Ici b, w v * ‖bq v‖) +
        Cf * ∫ v in Set.Ioc 0 (a + T) ∩ Set.Iio b, w v * ‖bq v‖ := by ring
    _ ≤ max (Cn * Real.exp c) Cf * (∫ v in Set.Ioc 0 (a + T) ∩ Set.Ici b, w v * ‖bq v‖) +
        max (Cn * Real.exp c) Cf * ∫ v in Set.Ioc 0 (a + T) ∩ Set.Iio b, w v * ‖bq v‖ :=
        add_le_add (mul_le_mul_of_nonneg_right hK1 hI0) (mul_le_mul_of_nonneg_right hK2 hI1)
    _ = max (Cn * Real.exp c) Cf * ((∫ v in Set.Ioc 0 (a + T) ∩ Set.Ici b, w v * ‖bq v‖) +
        ∫ v in Set.Ioc 0 (a + T) ∩ Set.Iio b, w v * ‖bq v‖) := by ring
    _ = _ := by rw [hsum]

end Drift

end HRS.MC.E213U11

end
