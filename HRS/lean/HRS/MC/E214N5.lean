import HRS.MC.E214N4

/-!
# E214N5: the window drift at `a + h` against the shifted window drift at `a`

`‖𝒟_{a+h,B}((0,a+h+T]) - 𝒟_{a,B(h+·)}((0,a+T])‖ ≤ C ∫_{(0,a+h+T] ∩ (-∞,h)} e^{-c(a+h-v)} ‖B_v‖ dv`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214N

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final

variable {d : ℕ}

section Shifts

theorem nearCoef_shift_measurable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {bq : ℝ → E} (hbm : Measurable (nearCoef 0 bq)) {h : ℝ} (hh : 0 ≤ h) :
    Measurable (nearCoef 0 (fun v => bq (h + v))) := by
  have : nearCoef 0 (fun v => bq (h + v)) = fun v => if 0 ≤ v then nearCoef 0 bq (h + v) else 0 := by
    funext v
    unfold nearCoef
    by_cases hv : 0 ≤ v
    · have hhv : 0 ≤ h + v := add_nonneg hh hv
      simp [hv, hhv]
    · simp [hv]
  rw [this]
  exact Measurable.ite measurableSet_Ici (hbm.comp (measurable_const_add h)) measurable_const

theorem integrableOn_norm_shift {E : Type*} [NormedAddCommGroup E] {bq : ℝ → E} {a h T : ℝ} (hh : 0 ≤ h)
    (hbi : IntegrableOn (fun v => ‖bq v‖) (Set.Icc 0 (a + h + T))) :
    IntegrableOn (fun v => ‖bq (h + v)‖) (Set.Icc 0 (a + T)) := by
  have hmp := measurePreserving_add_left (volume : Measure ℝ) h
  have hemb : MeasurableEmbedding (fun x : ℝ => h + x) := measurableEmbedding_addLeft h
  have hpre : (fun x : ℝ => h + x) ⁻¹' Set.Icc h (a + h + T) = Set.Icc 0 (a + T) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have h1 : IntegrableOn (fun v => ‖bq v‖) (Set.Icc h (a + h + T)) :=
    hbi.mono_set (Set.Icc_subset_Icc hh le_rfl)
  have := (hmp.integrableOn_comp_preimage hemb).2 h1
  rwa [hpre] at this

end Shifts

section Drift

variable {S : PreparedData d} {β₀ m : ℝ} (hE : EdgeworthHyp S β₀ m)

/-- Near-part identity of the drift (time-homogeneity). -/
theorem winDrift_near_shift (hρ : ∀ t t', (regime S β₀ hE).ρ t = (regime S β₀ hE).ρ t') (T : ℝ) (hT : 0 < T)
    {a h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) (bq : ℝ → NegSobolev d (rLvl d)) (hbm : Measurable (nearCoef 0 bq))
    (hbi : IntegrableOn (fun v => ‖bq v‖) (Set.Icc 0 (a + h + T))) :
    winDrift (regime S β₀ hE) m T (a + h) (add_nonneg ha hh)
        (nearCoef h (fun v => NegSobolev.embed m (bq v))) 0 (a + h + T) =
      winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (bq (h + v))) 0 (a + T) := by
  have hrm := rLvl_le hE
  have hnb : Measurable (nearCoef 0 (nearCoef h bq)) := HRS.MC.E213U11.u11_measurable_nearCoef_near hbm hh
  have hnbi : IntegrableOn (fun v => ‖nearCoef h bq v‖) (Set.Icc 0 (a + h + T)) := by
    have hmeasS : MeasurableSet (Set.Icc (0 : ℝ) (a + h + T)) := measurableSet_Icc
    have e1 := HRS.MC.E213U1.u1_aesm_of_nearCoef hnb hmeasS (fun v hv => Set.mem_Ici.2 hv.1)
    refine hbi.mono' e1.norm (Eventually.of_forall fun v => ?_)
    rw [norm_norm]
    unfold nearCoef
    split_ifs
    · exact le_rfl
    · rw [norm_zero]; exact norm_nonneg _
  have hbm' := nearCoef_shift_measurable hbm hh
  have hbi' := integrableOn_norm_shift (a := a) (T := T) hh hbi
  have c1 := HRS.MC.E213U1.winDrift_cont_proof hE T hT (a + h) (add_nonneg ha hh) (nearCoef h bq) hnb hnbi
    0 (a + h + T) le_rfl (by linarith) le_rfl
  have c2 := HRS.MC.E213U1.winDrift_cont_proof hE T hT a ha (fun v => bq (h + v)) hbm' hbi'
    0 (a + T) le_rfl (by linarith) le_rfl
  rw [HRS.MC.E213U11.u11_nearCoef_embed hrm]
  unfold winDrift driftInc
  refine e213o_ext (fun t => ?_)
  rw [winRestr_at', winRestr_at', e213o_pathOf_at' _ c1, e213o_pathOf_at' _ c2]
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have htT : (t : ℝ) ≤ T := t.2.2
  simp only [e213o_shift]
  rw [show min (a + h + T) (a + h + (t : ℝ)) = a + h + t by rw [min_eq_right (by linarith)],
    show min (a + T) (a + (t : ℝ)) = a + t by rw [min_eq_right (by linarith)]]
  have := drift_integral_shift hE hρ ha hh bq ht0
  rw [HRS.MC.E213U11.u11_nearCoef_embed hrm] at this
  exact this

theorem winDrift_shift_bound (hρ : ∀ t t', (regime S β₀ hE).ρ t = (regime S β₀ hE).ρ t') (T : ℝ) (hT : 0 < T) :
    ∃ Cf c : ℝ, 0 < Cf ∧ 0 < c ∧ ∀ {a h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) (bq : ℝ → NegSobolev d (rLvl d)),
      Measurable (nearCoef 0 bq) → IntegrableOn (fun v => ‖bq v‖) (Set.Icc 0 (a + h + T)) →
      ‖winDrift (regime S β₀ hE) m T (a + h) (add_nonneg ha hh) (fun v => NegSobolev.embed m (bq v)) 0 (a + h + T) -
          winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (bq (h + v))) 0 (a + T)‖ ≤
        Cf * ∫ v in Set.Ioc 0 (a + h + T) ∩ Set.Iio h, Real.exp (-c * (a + h - v)) * ‖bq v‖ := by
  obtain ⟨Cf, c, hCf, hc, hfar⟩ := HRS.MC.E213U1.winDrift_far_proof hE T hT
  refine ⟨Cf, c, hCf, hc, fun {a h} ha hh bq hbm hbi => ?_⟩
  have hrm := rLvl_le hE
  have ha' : 0 ≤ a + h := add_nonneg ha hh
  have hH : (0 : ℝ) ≤ a + h + T := by linarith
  have hmeasS : MeasurableSet (Set.Icc (0 : ℝ) (a + h + T)) := measurableSet_Icc
  have hm1 : Measurable (nearCoef 0 (nearCoef h bq)) := HRS.MC.E213U11.u11_measurable_nearCoef_near hbm hh
  have hm2 : Measurable (nearCoef 0 (farCoef h bq)) := HRS.MC.E213U11.u11_measurable_nearCoef_far hbm h
  have hi1 : IntegrableOn (fun v => ‖nearCoef h bq v‖) (Set.Icc 0 (a + h + T)) := by
    have e1 := HRS.MC.E213U1.u1_aesm_of_nearCoef hm1 hmeasS (fun v hv => Set.mem_Ici.2 hv.1)
    refine hbi.mono' e1.norm (Eventually.of_forall fun v => ?_)
    rw [norm_norm]
    unfold nearCoef
    split_ifs
    · exact le_rfl
    · rw [norm_zero]; exact norm_nonneg _
  have hi2 : IntegrableOn (fun v => ‖farCoef h bq v‖) (Set.Icc 0 (a + h + T)) := by
    have e2 := HRS.MC.E213U1.u1_aesm_of_nearCoef hm2 hmeasS (fun v hv => Set.mem_Ici.2 hv.1)
    refine hbi.mono' e2.norm (Eventually.of_forall fun v => ?_)
    rw [norm_norm]
    unfold farCoef
    split_ifs
    · exact le_rfl
    · rw [norm_zero]; exact norm_nonneg _
  have hsplit : (fun v => NegSobolev.embed m (bq v)) =
      fun v => NegSobolev.embed m (nearCoef h bq v + farCoef h bq v) := by
    funext v
    have := congrFun (nearCoef_add_farCoef h bq) v
    rw [this]
  have hadd := HRS.MC.E213U1.winDrift_add_proof hE T hT (a + h) ha' (nearCoef h bq) (farCoef h bq) hm1 hm2 hi1 hi2
    0 (a + h + T) le_rfl hH le_rfl
  have hnear := winDrift_near_shift hE hρ T hT ha hh bq hbm hbi
  rw [HRS.MC.E213U11.u11_nearCoef_embed hrm] at hnear
  rw [hsplit, hadd, hnear, add_sub_cancel_left, ← HRS.MC.E213U11.u11_farCoef_embed hrm]
  -- the far bound
  have hae : AEStronglyMeasurable bq (volume.restrict (Set.Icc (0 : ℝ) (a + h + T))) :=
    HRS.MC.E213U1.u1_aesm_of_nearCoef hbm hmeasS (fun v hv => Set.mem_Ici.2 hv.1)
  have hwint : IntegrableOn (fun v => Real.exp (-c * (a + h - v)) * ‖bq v‖) (Set.Icc 0 (a + h + T)) := by
    refine (hbi.const_mul (Real.exp (c * T))).mono' ?_ ?_
    · exact ((Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).aestronglyMeasurable).mul
        hae.norm
    · refine (ae_restrict_iff' hmeasS).2 (Eventually.of_forall fun v hv => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact Real.exp_le_exp.2 (by nlinarith [hv.2, hc])
  exact hfar (a + h) ha' h hh bq hbm (hwint.mono_set (by
    intro v hv; exact ⟨hv.1.le, hv.2.trans (min_le_right _ _)⟩)) 0 (a + h + T) le_rfl hH le_rfl

end Drift

end HRS.MC.E214N

end
