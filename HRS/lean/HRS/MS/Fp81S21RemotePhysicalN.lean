import HRS.MS.Fp81S21WeightedDrift2
import HRS.MS.Fp81S21CovClose
import HRS.MS.Fp81S21WindowCovClose
import HRS.MS.Fp81S21CenterPhysical
import HRS.MS.Fp81S21RemoteMean
import HRS.MS.Fp81S21PredictionPhysical
import HRS.MS.Fp81S21RecentHeatKernelPhysical2
import HRS.MS.Fp81S21RSValue5

/-! Source-time norm and RS estimates for the particle remote correction.
These lemmas retain supplied coefficient/time representatives and RS values.
They do not yet assert the radius-uniform physical remote correction theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp

/-- The measurable coefficient norm has the remote first-moment bound with
exact constant `sqrt M / c`, including the empty interval. -/
theorem fp81s21_remotePhysicalN_momentRep_tail
    {d r : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (E : r26t6_WeightedChart d r Pw) (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : ℝ → Ω → (Euc d → ℝ) → ℝ)
    (q : ℝ → Ω → r26t6_Coeff) (M : ℝ)
    (hrep : fp81s21_MomentRep E P Q q M)
    (c a L : ℝ) (hc : 0 < c) (ha : 0 ≤ a) (hL : 0 < L) :
    Integrable (fun ω => ∫ v in Ioc (0 : ℝ) (max (a - L) 0),
      Real.exp (-c * (a - v)) * ‖q v ω‖) P ∧
    (∫ ω, (∫ v in Ioc (0 : ℝ) (max (a - L) 0),
      Real.exp (-c * (a - v)) * ‖q v ω‖) ∂P) ≤
      Real.sqrt M * c⁻¹ * Real.exp (-c * L) := by
  apply fp81s21_expected_remote_exp_bound P (fun v ω => ‖q v ω‖)
    (Real.sqrt M) c hrep.1.norm (fun _ _ => norm_nonneg _)
    (Real.sqrt_nonneg M) hc
  · intro v hv
    have hi := ((hrep.2 v hv).1.integrable one_le_two).norm
    refine ⟨hi, ?_⟩
    have heq : (fun ω => dualNormE r Pw (Q v ω)) =ᵐ[P]
        (fun ω => ENNReal.ofReal ‖q v ω‖) := by
      filter_upwards [(hrep.2 v hv).2.2] with ω hω
      exact hω.2
    have hb := (fp81s21_MomentRep_firstMoment E P Q q M hrep v hv).2
    rw [lintegral_congr_ae heq,
      ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all P (fun ω => norm_nonneg _))] at hb
    exact (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg M)).mp hb
  · exact ha
  · exact hL

/-- A supplied physical time representative identifies the actual dual norm
on one almost-sure event, almost everywhere in source time. This avoids
interchanging the two a.e. quantifiers without a measurable equality event. -/
theorem fp81s21_remotePhysicalN_time_norm
    {d r : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (hP : (d : ℝ) < 2 * Pw) (E : r26t6_WeightedChart d r Pw)
    (P : Measure Ω) (Q : ℝ → Ω → (Euc d → ℝ) → ℝ)
    (q : ℝ → Ω → r26t6_Coeff) (M H : ℝ)
    (U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H)))
    (hU : fp81s21_TimeRep E P Q q M 0 H U) :
    ∀ᵐ ω ∂P, ∀ᵐ v ∂(volume.restrict (Icc (0 : ℝ) H)),
      dualNormE r Pw (Q v ω) = ENNReal.ofReal ‖q v ω‖ := by
  filter_upwards [hU.2.2.2] with ω hω
  filter_upwards [hω.2] with v hv
  have ha : ∀ f, IsR2Test f →
      Q v ω f = fp81s21_chartAction E (q v ω) f := by
    intro f hf
    have hw := HRS.MS.ProClosureS111.weightedTestSubmodule_iff.1
      (HRS.MS.ProClosureS111.weighted_test_of_compact_smooth
        (r := r) (Pw := Pw) hP hf)
    simpa only [zero_add, hv.1] using (hv.2 f hw).symm
  calc
    dualNormE r Pw (Q v ω) = dualNormE r Pw (fp81s21_chartAction E (q v ω)) := by
      unfold dualNormE
      congr 1
      funext f
      congr 1
      funext hf
      rw [ha f ⟨hf.1, hf.2.1⟩]
    _ = ENNReal.ofReal ‖q v ω‖ := fp81s21_chartAction_dualNorm hP E _

/-- Any supplied RS value is bounded by actual variation, independently of
its stored majorant. The zero-length case is included. -/
theorem fp81s21_remotePhysicalN_value_bound
    {Ω V : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {P : Measure Ω} {H : ℝ}
    {A : Ω → ℝ → V →L[ℝ] ℝ} {F : Ω → ℝ → V}
    (W : fp81s21_RSBVWindow P H A F)
    {b : ℝ} (hb : 0 ≤ b) (hbH : b ≤ H)
    (hgood : ∀ᵐ ω ∂P, ContinuousOn (A ω) (Icc 0 b) ∧
      BoundedVariationOn (F ω) (Icc 0 b))
    (hA : ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) b, ‖A ω t‖ ≤ 1) :
    ∀ᵐ ω ∂P, |W.value 0 b ω| ≤
      (eVariationOn (F ω) (Icc (0 : ℝ) b)).toReal := by
  letI : Nonempty (Icc (0 : ℝ) b) := ⟨⟨0, le_rfl, hb⟩⟩
  rcases eq_or_lt_of_le hb with heq | hpos
  · subst b
    filter_upwards [W.value_zero 0 le_rfl hbH] with ω hω
    simp [hω]
  · filter_upwards [hgood, hA, W.value_isRS 0 b le_rfl hb hbH] with ω hg hAω hrs
    refine (fp81s21_rsOn_bv_bound hpos (F ω) (A ω) hg.2 hg.1 hrs).trans ?_
    have hs : (⨆ t : Icc (0 : ℝ) b, ‖A ω t‖) ≤ 1 := by
      apply ciSup_le
      intro t
      exact hAω t t.property
    simpa using mul_le_mul_of_nonneg_right hs ENNReal.toReal_nonneg

/-- Integrate bounds on the actual drift and covariance RS values. -/
theorem fp81s21_remotePhysicalN_corr_bound
    {Ω VD VJ : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup VD] [NormedSpace ℝ VD] [CompleteSpace VD]
    [NormedAddCommGroup VJ] [NormedSpace ℝ VJ] [CompleteSpace VJ]
    {P : Measure Ω} {H : ℝ}
    {Ad : Ω → ℝ → VD →L[ℝ] ℝ} {Fd : Ω → ℝ → VD}
    {Aj : Ω → ℝ → VJ →L[ℝ] ℝ} {Fj : Ω → ℝ → VJ}
    (W : fp81s21_WindowRS P H Ad Fd Aj Fj)
    {b : ℝ} (hb : 0 ≤ b) (hbH : b ≤ H)
    (md mj : Ω → ℝ) (hd : Integrable md P) (hj : Integrable mj P)
    (hdb : ∀ᵐ ω ∂P, |W.drift.value 0 b ω| ≤ md ω)
    (hjb : ∀ᵐ ω ∂P, |W.covariance.value 0 b ω| ≤ mj ω) :
    |fp81s21_WindowRS_corr W 0 b| ≤
      (∫ ω, md ω ∂P) + (1 / 2 : ℝ) * (∫ ω, mj ω ∂P) := by
  have hdi := W.drift.value_integrable 0 b le_rfl hb hbH
  have hji := W.covariance.value_integrable 0 b le_rfl hb hbH
  have hD : |∫ ω, W.drift.value 0 b ω ∂P| ≤ ∫ ω, md ω ∂P :=
    (abs_integral_le_integral_abs).trans (integral_mono_ae hdi.abs hd hdb)
  have hJ : |∫ ω, W.covariance.value 0 b ω ∂P| ≤ ∫ ω, mj ω ∂P :=
    (abs_integral_le_integral_abs).trans (integral_mono_ae hji.abs hj hjb)
  calc
    |fp81s21_WindowRS_corr W 0 b| ≤
        |∫ ω, W.drift.value 0 b ω ∂P| +
          (1 / 2 : ℝ) * |∫ ω, W.covariance.value 0 b ω ∂P| := by
      simpa [fp81s21_WindowRS_corr, abs_mul] using
        (abs_add_le (-(∫ ω, W.drift.value 0 b ω ∂P))
          ((1 / 2 : ℝ) * (∫ ω, W.covariance.value 0 b ω ∂P)))
    _ ≤ _ := add_le_add hD (mul_le_mul_of_nonneg_left hJ (by norm_num))

/-- Transfer the source-time identity supplied by `TimeRep` before taking the
expectation. The exact exponential weight and the empty interval are retained. -/
theorem fp81s21_remotePhysicalN_source_tail
    {d r : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (hP : (d : ℝ) < 2 * Pw) (E : r26t6_WeightedChart d r Pw)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : ℝ → Ω → (Euc d → ℝ) → ℝ)
    (q : ℝ → Ω → r26t6_Coeff) (M H : ℝ)
    (hrep : fp81s21_MomentRep E P Q q M)
    (U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H)))
    (hU : fp81s21_TimeRep E P Q q M 0 H U)
    (c a L : ℝ) (hc : 0 < c) (ha : 0 ≤ a) (haH : a ≤ H) (hL : 0 < L) :
    let J := fun ω => ∫⁻ v in Ioc (0 : ℝ) (max (a - L) 0),
      ENNReal.ofReal (Real.exp (-c * max (a - v) 0)) * dualNormE r Pw (Q v ω)
    (∀ᵐ ω ∂P, J ω < ∞) ∧ Integrable (fun ω => (J ω).toReal) P ∧
      (∫ ω, (J ω).toReal ∂P) ≤ Real.sqrt M * c⁻¹ * Real.exp (-c * L) := by
  let b := max (a - L) 0
  let I := Ioc (0 : ℝ) b
  let J := fun ω => ∫⁻ v in I,
    ENNReal.ofReal (Real.exp (-c * max (a - v) 0)) * dualNormE r Pw (Q v ω)
  let B := fun ω => ∫ v in I, Real.exp (-c * (a - v)) * ‖q v ω‖
  have hba : b ≤ a := max_le (by linarith) ha
  have hsub : I ⊆ Icc (0 : ℝ) H := fun v hv => ⟨hv.1.le, hv.2.trans (hba.trans haH)⟩
  have hnorm := fp81s21_remotePhysicalN_time_norm hP E P Q q M H U hU
  have heq : ∀ᵐ ω ∂P, J ω = ENNReal.ofReal (B ω) := by
    filter_upwards [hnorm, hU.2.2.2] with ω hω htime
    have hn := ae_restrict_of_ae_restrict_of_subset hsub hω
    have hqi : IntegrableOn (fun v => ‖q v ω‖) I volume := by
      have hi := (htime.1.integrable one_le_two).norm
      simp only [zero_add] at hi
      exact hi.mono_measure (Measure.restrict_mono hsub le_rfl)
    have hm : Measurable (fun v => Real.exp (-c * (a - v)) * ‖q v ω‖) :=
      (Real.measurable_exp.comp (measurable_const.mul (measurable_const.sub measurable_id))).mul
        ((hrep.1.comp (measurable_id.prodMk measurable_const)).norm)
    have hi : IntegrableOn (fun v => Real.exp (-c * (a - v)) * ‖q v ω‖) I volume := by
      refine hqi.mono' hm.aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      have hv' : v ≤ a := hv.2.trans hba
      have hw : Real.exp (-c * (a - v)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sub_nonneg.mpr hv'))
      rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
      exact (mul_le_mul_of_nonneg_right hw (norm_nonneg _)).trans_eq (one_mul _)
    calc
      J ω = ∫⁻ v in I, ENNReal.ofReal (Real.exp (-c * (a - v)) * ‖q v ω‖) := by
        apply lintegral_congr_ae
        filter_upwards [hn, ae_restrict_mem measurableSet_Ioc] with v hv hvI
        have hva : 0 ≤ a - v := sub_nonneg.mpr (hvI.2.trans hba)
        rw [hv, max_eq_left hva, ENNReal.ofReal_mul (Real.exp_pos _).le]
      _ = ENNReal.ofReal (B ω) :=
        (ofReal_integral_eq_lintegral_ofReal hi
          (ae_of_all _ (fun v => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)))).symm
  have hB0 (ω) : 0 ≤ B ω := integral_nonneg fun v =>
    mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  have hreal : (fun ω => (J ω).toReal) =ᵐ[P] B := by
    filter_upwards [heq] with ω hω
    rw [hω, ENNReal.toReal_ofReal (hB0 ω)]
  have hbnd := fp81s21_remotePhysicalN_momentRep_tail E P Q q M hrep c a L hc ha hL
  refine ⟨?_, hbnd.1.congr hreal.symm, ?_⟩
  · filter_upwards [heq] with ω hω
    change J ω < ∞
    rw [hω]
    exact ENNReal.ofReal_lt_top
  · exact (integral_congr_ae hreal).trans_le hbnd.2

#print axioms fp81s21_remotePhysicalN_source_tail
#print axioms fp81s21_remotePhysicalN_momentRep_tail
#print axioms fp81s21_remotePhysicalN_time_norm
#print axioms fp81s21_remotePhysicalN_value_bound
#print axioms fp81s21_remotePhysicalN_corr_bound
end HRS.Fp81.S21
end
