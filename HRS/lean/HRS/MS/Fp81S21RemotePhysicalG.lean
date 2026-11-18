import HRS.MS.Fp81S21GaussianPhysicalPackage2
import HRS.MS.Fp81S21GaussianO1Moments
import HRS.MS.Fp81S21CenterPhysical
import HRS.MS.Fp81S21RemoteMean
import HRS.MS.Fp81S21RSValue5
import HRS.MS.Fp81S21CovRS3

/-! Packet 38G: direct bounds for supplied RS values. The arbitrary majorant
in an RS certificate is never used. History representatives are transferred
under the time integral, before taking expectations. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.R2Interp HRS.MS.S111K2

private theorem fp81s21_remote_rs_control
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {b K I : ℝ} (hb : 0 < b) (A : ℝ → E →L[ℝ] ℝ) (F : ℝ → E)
    (w : ℝ → ℝ) (hw : IntegrableOn w (Icc 0 b))
    (hA : ∀ t ∈ Icc 0 b, ‖A t‖ ≤ 1)
    (hinc : ∀ u v, 0 ≤ u → u ≤ v → v ≤ b →
      ‖F v - F u‖ ≤ K * ∫ s in Ioc u v, w s)
    (hI : fp81s21_IsRSOn 0 b (fun t u v => A t (F v - F u)) I) :
    |I| ≤ K * ∫ s in Ioc 0 b, w s := by
  have hint (u v : ℝ) (hu : u ∈ Icc 0 b) (hv : v ∈ Icc 0 b) :
      IntervalIntegrable w volume u v := by
    apply (intervalIntegrable_iff).2
    exact hw.mono_set (uIcc_subset_Icc hu hv) |>.mono_set Ioc_subset_Icc_self
  have h := s102_rs_bound_mono hb (fun t => ∫ s in (0 : ℝ)..t, w s)
    (show HRS.Sec7.IsRS b (fun t u v => A t (F v - F u)) I by
      simpa only [fp81s21_IsRSOn, IsR2RS, HRS.Sec7.IsRS, zero_add, sub_zero] using hI) (C := K) ?_
  · simpa only [intervalIntegral.integral_same, sub_zero,
      intervalIntegral.integral_of_le hb.le] using h
  intro t u v hu hut htv hv
  have huv := hut.trans htv
  have hu' : u ∈ Icc 0 b := ⟨hu, huv.trans hv⟩
  have hv' : v ∈ Icc 0 b := ⟨hu.trans huv, hv⟩
  have he := intervalIntegral.integral_add_adjacent_intervals
    (hint 0 u ⟨le_rfl, hb.le⟩ hu') (hint u v hu' hv')
  rw [intervalIntegral.integral_of_le huv] at he
  calc
    |A t (F v - F u)| ≤ ‖A t‖ * ‖F v - F u‖ := (A t).le_opNorm _
    _ ≤ 1 * ‖F v - F u‖ := mul_le_mul_of_nonneg_right
      (hA t ⟨hu.trans hut, htv.trans hv⟩) (norm_nonneg _)
    _ ≤ K * ∫ s in Ioc u v, w s := by simpa using hinc u v hu huv hv
    _ = K * ((∫ s in (0 : ℝ)..v, w s) - ∫ s in (0 : ℝ)..u, w s) := by
      rw [← he]; ring

/-- A supplied scalar RS family with the literal weighted-history increment
bound has the sharp exponential tail associated to its supplied first moment. -/
theorem fp81s21_remote_history_rs_bound
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (q : ℝ → Ω → r26t6_Coeff) (M m H a c K : ℝ)
    (hH : 0 ≤ H) (haH : a ≤ H) (hc : 0 < c) (hK : 0 ≤ K)
    (hq : Measurable (Function.uncurry q)) (hm : 0 ≤ m)
    (hsec : ∀ s, 0 ≤ s → Integrable (fun ω => ‖q s ω‖) P ∧
      (∫ ω, ‖q s ω‖ ∂P) ≤ m)
    (U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H)))
    (hU : fp81s21_TimeL2Rep P q M 0 H U)
    (A : Ω → ℝ → E →L[ℝ] ℝ) (F : Ω → ℝ → E)
    (W : fp81s21_RSBVWindow P H A F)
    (hA : ∀ ω t, 0 ≤ t → t ≤ H → ‖A ω t‖ ≤ 1)
    (hinc : ∀ ω u v, 0 ≤ u → u ≤ v → v ≤ H →
      ‖F ω v - F ω u‖ ≤ K * ∫ s in Ioc u v,
        s111k2_age c a s * ‖fp81s21_timeL2L1 H hH (U ω) s‖)
    (a_nonneg : 0 ≤ a) (L : ℝ) (hL : 0 < L) :
    |∫ ω, W.value 0 (max (a - L) 0) ω ∂P| ≤
      K * (m * c⁻¹ * Real.exp (-c * L)) := by
  let b := max (a - L) 0
  have hb : 0 ≤ b := le_max_right _ _
  have hba : b ≤ a := max_le (by linarith) a_nonneg
  have hbH : b ≤ H := hba.trans haH
  let Z : Ω → ℝ := fun ω => ∫ s in Ioc (0 : ℝ) b,
    Real.exp (-c * (a - s)) * ‖q s ω‖
  obtain ⟨hZi, hZb⟩ := fp81s21_expected_remote_exp_bound P
    (fun s ω => ‖q s ω‖) m c hq.norm (fun _ _ => norm_nonneg _) hm hc hsec
    a L a_nonneg hL
  have hZi' : Integrable Z P := hZi
  by_cases hb0 : b = 0
  · have he : (∫ ω, W.value 0 b ω ∂P) = 0 := by
      rw [hb0]
      exact (integral_congr_ae (W.value_zero 0 le_rfl hH)).trans (by simp)
    change |∫ ω, W.value 0 b ω ∂P| ≤ _
    rw [he, abs_zero]
    positivity
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hbound : ∀ᵐ ω ∂P, |W.value 0 b ω| ≤ K * Z ω := by
    filter_upwards [W.value_isRS 0 b le_rfl hb hbH, hU.2.2.2] with ω hRS hrep
    let V := fp81s21_timeL2L1 H hH (U ω)
    let w := fun s => s111k2_age c a s * ‖V s‖
    have hw : IntegrableOn w (Icc (0 : ℝ) H) := by
      have hm' : Measurable (fun s => s111k2_age c a s) := by
        unfold s111k2_age; fun_prop
      have hbd : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) H),
          ‖s111k2_age c a s‖ ≤ 1 := by
        filter_upwards with s
        rw [Real.norm_of_nonneg (fp81s21_age_bounds (u := a) hc.le s).1]
        exact (fp81s21_age_bounds (u := a) hc.le s).2
      change Integrable w (volume.restrict (Icc (0 : ℝ) H))
      simpa only [w, mul_comm] using
        ((Lp.memLp V).integrable le_rfl).norm.bdd_mul hm'.aestronglyMeasurable hbd
    have hcontrol := fp81s21_remote_rs_control hbpos (A ω) (F ω) w
      (hw.mono_set (Icc_subset_Icc le_rfl hbH))
      (fun t ht => hA ω t ht.1 (ht.2.trans hbH))
      (fun u v hu huv hv => hinc ω u v hu huv (hv.trans hbH)) hRS
    have hrep' : V =ᵐ[volume.restrict (Icc (0 : ℝ) H)] fun s => q s ω := by
      simpa only [zero_add] using (fp81s21_timeL2L1_ae H hH (U ω)).trans hrep.2
    have he : (∫ s in Ioc 0 b, w s) = Z ω := by
      apply integral_congr_ae
      have hs := ae_mono (Measure.restrict_mono
        (show Ioc (0 : ℝ) b ⊆ Icc 0 H from fun s hs => ⟨hs.1.le, hs.2.trans hbH⟩)
        le_rfl) hrep'
      filter_upwards [hs, ae_restrict_mem measurableSet_Ioc] with s hs hsb
      dsimp [w, s111k2_age]
      rw [hs, max_eq_left (sub_nonneg.mpr (hsb.2.trans hba))]
    exact hcontrol.trans_eq (congrArg (K * ·) he)
  calc
    |∫ ω, W.value 0 b ω ∂P| ≤ ∫ ω, |W.value 0 b ω| ∂P :=
      abs_integral_le_integral_abs
    _ ≤ ∫ ω, K * Z ω ∂P := integral_mono_ae
      (W.value_integrable 0 b le_rfl hb hbH).abs (hZi'.const_mul K) hbound
    _ = K * ∫ ω, Z ω ∂P := integral_const_mul _ _
    _ ≤ K * (m * c⁻¹ * Real.exp (-c * L)) :=
      mul_le_mul_of_nonneg_left hZb hK

#print axioms fp81s21_remote_history_rs_bound
end HRS.Fp81.S21
end
