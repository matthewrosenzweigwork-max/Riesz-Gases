import HRS.MS.Fp81S21GaussianIncrementAdapted2
import HRS.MS.Fp81S21TimeHistoryPast2

/-! Packet 36: locality of the supplied interval operators and past adaptation
of the literal cumulative increments. All histories and operators are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.S111K2

private theorem fp81s21_timeL2_local_residual
    (H : ℝ) (hH : 0 ≤ H) (u v : ℝ) (hu : 0 ≤ u) (hv : v ≤ H)
    (z : Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H))) :
    ⇑(fp81s21_timeL2L1 H hH z - fp81s21_timeL2L1 H hH
      (fp81s21_timeL2_indicator (volume.restrict (Icc (0 : ℝ) H))
        (Ioc u v) measurableSet_Ioc z)) =ᵐ[volume.restrict (Ioc u v)] 0 := by
  let μ := volume.restrict (Icc (0 : ℝ) H)
  let T := fp81s21_timeL2L1 H hH
  let M := fp81s21_timeL2_indicator μ (Ioc u v) measurableSet_Ioc
  have hsub : Ioc u v ⊆ Icc (0 : ℝ) H := fun s hs =>
    ⟨hu.trans hs.1.le, hs.2.trans hv⟩
  have he : ∀ᵐ s ∂μ, s ∈ Ioc u v → (T z - T (M z)) s = 0 := by
    filter_upwards [Lp.coeFn_sub (T z) (T (M z)),
      fp81s21_timeL2L1_ae H hH z, fp81s21_timeL2L1_ae H hH (M z),
      fp81s21_timeL2_indicator_ae μ (Ioc u v) measurableSet_Ioc z]
      with s hs hz hm hi
    intro hmem
    rw [hs]
    change T z s - T (M z) s = 0
    rw [hz, hm, hi, Set.indicator_of_mem hmem, sub_self]
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub he,
    ae_restrict_mem measurableSet_Ioc] with s hs hi
  exact hs hi

/-- Drift depends only on the history inside the exact integration interval. -/
theorem fp81s21_interval_drift_local
    {d r : ℕ} {Pw : ℝ} {E : r26t6_WeightedChart d r Pw} {C : WholeCoeff d}
    {T a c K : ℝ} (O : r26t6_IntervalOperators E C T a c K)
    (hH : 0 ≤ a + T) (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ a + T)
    (z : Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) (a + T)))) :
    O.drift u v (fp81s21_timeL2L1 (a + T) hH z) =
      O.drift u v (fp81s21_timeL2L1 (a + T) hH
        (fp81s21_timeL2_indicator (volume.restrict (Icc (0 : ℝ) (a + T)))
          (Ioc u v) measurableSet_Ioc z)) := by
  let L := fp81s21_timeL2L1 (a + T) hH
  let M := fp81s21_timeL2_indicator (volume.restrict (Icc (0 : ℝ) (a + T)))
    (Ioc u v) measurableSet_Ioc
  have he := fp81s21_timeL2_local_residual (a + T) hH u v hu hv z
  have hi : (∫ s in Ioc u v, s111k2_age c a s * ‖(L z - L (M z)) s‖) = 0 := by
    calc
      _ = ∫ _s in Ioc u v, (0 : ℝ) := integral_congr_ae (he.mono fun s hs => by
        change (L z - L (M z)) s = 0 at hs
        rw [hs, norm_zero, mul_zero])
      _ = 0 := by simp
  have hn := O.drift_norm u v hu huv hv (L z - L (M z))
  rw [hi, mul_zero] at hn
  have hz := norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

/-- Covariance has the same locality, in the projective tensor subspace. -/
theorem fp81s21_interval_covariance_local
    {d r : ℕ} {Pw : ℝ} {E : r26t6_WeightedChart d r Pw} {C : WholeCoeff d}
    {T a c K : ℝ} (O : r26t6_IntervalOperators E C T a c K)
    (hH : 0 ≤ a + T) (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ a + T)
    (z : Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) (a + T)))) :
    O.covariance u v (fp81s21_timeL2L1 (a + T) hH z) =
      O.covariance u v (fp81s21_timeL2L1 (a + T) hH
        (fp81s21_timeL2_indicator (volume.restrict (Icc (0 : ℝ) (a + T)))
          (Ioc u v) measurableSet_Ioc z)) := by
  let L := fp81s21_timeL2L1 (a + T) hH
  let M := fp81s21_timeL2_indicator (volume.restrict (Icc (0 : ℝ) (a + T)))
    (Ioc u v) measurableSet_Ioc
  have he := fp81s21_timeL2_local_residual (a + T) hH u v hu hv z
  have hi : (∫ s in Ioc u v, s111k2_age c a s ^ 2 * ‖(L z - L (M z)) s‖) = 0 := by
    calc
      _ = ∫ _s in Ioc u v, (0 : ℝ) := integral_congr_ae (he.mono fun s hs => by
        change (L z - L (M z)) s = 0 at hs
        rw [hs, norm_zero, mul_zero])
      _ = 0 := by simp
  have hn := O.covariance_norm u v hu huv hv (L z - L (M z))
  rw [hi, mul_zero] at hn
  have hz := norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

variable {p : Parameters} {δ : ℝ} {R : Trajectory p δ}

/-- Both actual cumulative increments are measurable in the retained past at
cutoff `v`. No adaptedness of the untruncated horizon history is assumed. -/
theorem fp81s21_gaussian_increments_past_adapted
    (Q : fp81s21_Physical35 p R) (a : ℝ) (ha : 0 ≤ a)
    (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ a + p.T) :
    AEStronglyMeasurable[MeasurableSpace.comap
      (fp81s21_predictionPast Q.tofp81s21_Gaussian35Selection v) inferInstance]
      (fun ω =>
        fp81s21_gaussian_Dcum (Q.OD a ha) (add_nonneg ha p.hT.le) (Q.UB a ha) v ω -
        fp81s21_gaussian_Dcum (Q.OD a ha) (add_nonneg ha p.hT.le) (Q.UB a ha) u ω)
      Q.src.G0.P ∧
    AEStronglyMeasurable[MeasurableSpace.comap
      (fp81s21_predictionPast Q.tofp81s21_Gaussian35Selection v) inferInstance]
      (fun ω =>
        fp81s21_gaussian_Jcum (Q.OJ a ha) (add_nonneg ha p.hT.le) (Q.UG a ha) v ω -
        fp81s21_gaussian_Jcum (Q.OJ a ha) (add_nonneg ha p.hT.le) (Q.UG a ha) u ω)
      Q.src.G0.P := by
  letI : MeasurableSpace Q.src.G0.Ω := Q.src.G0.mΩ
  letI : IsProbabilityMeasure Q.src.G0.P := Q.src.G0.prob
  let μ := volume.restrict (Icc (0 : ℝ) (a + p.T))
  let m := MeasurableSpace.comap
    (fp81s21_predictionPast Q.tofp81s21_Gaussian35Selection v) inferInstance
  letI : MeasurableSpace Q.src.G0.Ω := Q.src.G0.mΩ
  have hp : Measurable (fp81s21_predictionPast Q.tofp81s21_Gaussian35Selection v) :=
    measurable_pi_iff.2 fun i => Q.src.rawBundle.2.2.2.1 _
  have hm : m ≤ Q.src.G0.mΩ := hp.comap_le
  let L := fp81s21_timeL2L1 (a + p.T) (add_nonneg ha p.hT.le)
  let M := fp81s21_timeL2_indicator μ (Ioc u v) measurableSet_Ioc
  have hB : AEStronglyMeasurable[m] (fun ω => M (Q.UB a ha ω)) Q.src.G0.P := by
    refine fp81s21_timeL2_indicator_past μ Q.src.G0.P (Ioc u v) measurableSet_Ioc
      (Q.S.qe Q.src.G0) (Q.UB a ha)
      ((Q.S.payload Q.src.G0).2.2.2.2.1).1 (Q.hUB a ha).2.1 ?_ m hm ?_
    · filter_upwards [(Q.hUB a ha).2.2.2] with ω hω
      simpa only [zero_add] using hω.2
    · exact Filter.Eventually.of_forall fun s hs =>
        fp81s21_gaussian_quadratic_past_adapted Q s v (hu.trans hs.1.le) hs.2
  have hG : AEStronglyMeasurable[m] (fun ω => M (Q.UG a ha ω)) Q.src.G0.P := by
    refine fp81s21_timeL2_indicator_past μ Q.src.G0.P (Ioc u v) measurableSet_Ioc
      (fp81s21_gaussian35_qG Q.tofp81s21_Gaussian35Selection) (Q.UG a ha)
      (Q.canon.payload Q.src.G0).coefficients.weak_momentRep.1
      (Q.hUG a ha).2.1 ?_ m hm ?_
    · filter_upwards [(Q.hUG a ha).2.2.2] with ω hω
      simpa only [zero_add] using hω.2
    · apply Filter.Eventually.of_forall
      intro s hs
      obtain ⟨q, _, hq, he⟩ := fp81s21_gaussian_prediction_coefficient_adapted
        Q.tofp81s21_Gaussian35Selection s v (hu.trans hs.1.le) hs.2
      exact hq.stronglyMeasurable.aestronglyMeasurable.congr he.symm
  constructor
  · have hd := ((Q.OD a ha).drift u v |>.comp L).continuous.comp_aestronglyMeasurable hB
    apply hd.congr
    apply Filter.Eventually.of_forall
    intro ω
    exact ((Q.DRegularity a ha).2.2.1 u v hu huv hv ω |>.trans
      (fp81s21_interval_drift_local (Q.OD a ha) (add_nonneg ha p.hT.le)
        u v hu huv hv (Q.UB a ha ω))).symm
  · have hj := ((Q.OJ a ha).covariance u v |>.comp L).continuous.comp_aestronglyMeasurable hG
    apply hj.congr
    apply Filter.Eventually.of_forall
    intro ω
    exact ((Q.JRegularity a ha).2.2.1 u v hu huv hv ω |>.trans
      (fp81s21_interval_covariance_local (Q.OJ a ha) (add_nonneg ha p.hT.le)
        u v hu huv hv (Q.UG a ha ω))).symm

#print axioms fp81s21_interval_drift_local
#print axioms fp81s21_interval_covariance_local
#print axioms fp81s21_gaussian_increments_past_adapted
end HRS.Fp81.S21
end
