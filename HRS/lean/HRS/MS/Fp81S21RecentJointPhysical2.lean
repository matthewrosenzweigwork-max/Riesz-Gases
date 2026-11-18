import HRS.MS.Fp81S21RecentJointPhysical

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp HRS.MS.CovMeas

local instance fp81s21_recentJoint2_CH_meas (H : ℝ) : MeasurableSpace (CH H) := borel _
local instance fp81s21_recentJoint2_CH_borel (H : ℝ) : BorelSpace (CH H) := ⟨rfl⟩
local instance fp81s21_recentJoint2_UH_meas (H : ℝ) : MeasurableSpace (UH H) := borel _
local instance fp81s21_recentJoint2_UH_borel (H : ℝ) : BorelSpace (UH H) := ⟨rfl⟩
local instance fp81s21_recentJoint2_YH_meas (p : Parameters) (H : ℝ) :
    MeasurableSpace (YH p H) := borel _
local instance fp81s21_recentJoint2_YH_borel (p : Parameters) (H : ℝ) :
    BorelSpace (YH p H) := ⟨rfl⟩
local instance fp81s21_recentJoint2_CH_countable (H : ℝ) : SecondCountableTopology (CH H) := by
  letI : TopologicalSpace.SeparableSpace r26t6_Coeff := HRS.StaticLimitAux.separable_lp (ι := ℕ)
  infer_instance
local instance fp81s21_recentJoint2_UH_countable (H : ℝ) : SecondCountableTopology (UH H) := by
  letI := fp81s21_L2History_separable H
  infer_instance
local instance fp81s21_recentJoint2_YH_countable (p : Parameters) (H : ℝ) :
    SecondCountableTopology (YH p H) := by
  change SecondCountableTopology C(I H, C(I p.T, OscDual p.d (wholeSpaceIndex p.d)))
  infer_instance
local instance fp81s21_recentJoint2_YH_complete (p : Parameters) (H : ℝ) :
    CompleteSpace (YH p H) := by
  change CompleteSpace C(I H, C(I p.T, OscDual p.d (wholeSpaceIndex p.d)))
  infer_instance

private theorem fp81s21_recentJoint_moment_sum
    {Ω V W : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V] [NormedAddCommGroup W]
    (μ : Measure Ω) (D : Ω → V) (J : Ω → W)
    (H d j mB mη MB Mη : ℝ) (hH : 0 ≤ H)
    (hD : MemLp D 2 μ) (hJ : MemLp J 2 μ)
    (hd : (∫ ω, ‖D ω‖ ^ 2 ∂μ) ≤ d ^ 2 * (H * mB))
    (hj : (∫ ω, ‖J ω‖ ^ 2 ∂μ) ≤ j ^ 2 * (H * mη))
    (hB : mB ≤ MB) (hη : mη ≤ Mη) :
    (∫ ω, (‖D ω‖ ^ 2 + ‖J ω‖ ^ 2) ∂μ) ≤ H * (d ^ 2 * MB + j ^ 2 * Mη) := by
  rw [integral_add (hD.integrable_norm_pow (by norm_num))
    (hJ.integrable_norm_pow (by norm_num))]
  calc
    _ ≤ d ^ 2 * (H * mB) + j ^ 2 * (H * mη) := add_le_add hd hj
    _ ≤ d ^ 2 * (H * MB) + j ^ 2 * (H * Mη) := add_le_add
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB hH) (sq_nonneg d))
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hη hH) (sq_nonneg j))
    _ = H * (d ^ 2 * MB + j ^ 2 * Mη) := by ring

/-- Whole-packet recent prediction, drift and covariance comparison, using
exactly the retained particle/Gaussian paths and quadratic histories. -/
theorem fp81s21_recent_joint_physical (p : Parameters) : fp81s21_RecentJointPhysicalSpec p := by
  obtain ⟨Es, E, εAvg, hε, hεlim, δp, hδp, hδph, hp⟩ :=
    fp81s21_physical_recent_prediction_comparison_centered p
  obtain ⟨δb, hδb, _, hb⟩ := fp81s21_recent_bv_interval_of_selected p Es E
  refine ⟨Es, E, εAvg, hε, hεlim, min δp δb, lt_min hδp hδb,
    (min_le_left _ _).trans hδph, ?_⟩
  intro δ hδ hδle R
  obtain ⟨MUG, hMUG, canon, εN, εG, εB, hn, hnl, hg, hgl, hbε, hbl,
    S31, Kpred, hKpred, hpred⟩ := hp δ hδ (hδle.trans (min_le_left _ _)) R
  obtain ⟨c, K, hc, hK, O, hBV⟩ := hb δ hδ (hδle.trans (min_le_right _ _)) R
  refine ⟨MUG, hMUG, canon, εN, εG, εB, hn, hnl, hg, hgl, hbε, hbl,
    S31, c, hc, K, hK, Kpred, hKpred, O, ?_⟩
  intro L hL
  let H := L + p.T
  have hH : 0 < H := add_pos hL p.hT
  let T := fp81s21_smoothPathToL2 H hH
  let dL := K * Real.sqrt H
  let jL := K * |2 * (r26t3_coeff R).ν| * Real.sqrt H
  let CL := max Kpred (max dL (jL * ‖T‖))
  let MBG := S31.gaussian.quadratic.Kstar ^ 4 * S31.gaussian.quadratic.B / 2
  let M33 := H * (dL ^ 2 * max S31.MN MBG + jL ^ 2 * max S31.MN MUG)
  have hCL : 0 ≤ CL := hKpred.trans (le_max_left _ _)
  have hmaxB : 0 ≤ max S31.MN MBG := S31.MN_nonneg.trans (le_max_left _ _)
  have hmaxη : 0 ≤ max S31.MN MUG := S31.MN_nonneg.trans (le_max_left _ _)
  have hM33 : 0 ≤ M33 := mul_nonneg hH.le
    (add_nonneg (mul_nonneg (sq_nonneg _) hmaxB) (mul_nonneg (sq_nonneg _) hmaxη))
  obtain ⟨e, eL, he, helim, heL, _, _, P, hP, hall⟩ := hpred L hL
  let e33 := fun N => 2 * CL * e N
  have he33 : ∀ N, 0 ≤ e33 N := fun N =>
    mul_nonneg (mul_nonneg (by norm_num) hCL) (he N)
  have he33lim : Tendsto e33 atTop (𝓝 0) := by
    simpa [e33] using (tendsto_const_nhds.mul helim :
      Tendsto (fun N => (2 * CL) * e N) atTop (𝓝 ((2 * CL) * 0)))
  refine ⟨e, e33, M33, hM33, he, helim, rfl, he33, he33lim, P, hP, ?_⟩
  intro N hN A G a ha
  obtain ⟨XN, XG, UBN, UBG, YN, YG, hNcd, hGcd, hBN, hBG, hmean, hGA,
    hYN, hYG, hYNm, hYN2, hYGm, hYG2, hNid, hGid, hraw, hcenter, hpair⟩ :=
    hall N hN A G a ha
  obtain ⟨UN0, BN0, UG0, BG0, hIN, hIG⟩ :=
    hBV εAvg MUG canon εN εG εB S31 N hN A G L hL a ha XN XG UBN UBG
      hNcd hGcd hBN hBG
  have hBVN := fp81s21_recent_bv_physical p R A.P E _ _ _ _ _
    S31.MN S31.MN a L c K ha hL (O a ha) hK hc UN0 BN0 _ UBN XN hIN
  have hBVG := fp81s21_recent_bv_physical p R G.P E _ _ _ _ _
    MUG MBG a L c K ha hL (O a ha) hK hc UG0 BG0 _ UBG XG hIG
  letI : MeasurableSpace (fp81s21_VD p a ha L hL c K (O a ha) hK hc.le) := borel _
  letI : BorelSpace (fp81s21_VD p a ha L hL c K (O a ha) hK hc.le) := ⟨rfl⟩
  letI : MeasurableSpace (fp81s21_VJ p a ha L hL c K (O a ha) hK hc.le) := borel _
  letI : BorelSpace (fp81s21_VJ p a ha L hL c K (O a ha) hK hc.le) := ⟨rfl⟩
  letI := fp81s21_VD_complete p a ha L hL c K (O a ha) hK hc.le
  letI := fp81s21_VJ_complete p a ha L hL c K (O a ha) hK hc.le
  letI := fp81s21_VD_separable p a ha L hL c K (O a ha) hK hc.le
  letI := fp81s21_VJ_separable p a ha L hL c K (O a ha) hK hc.le
  let D := fp81s21_VDtransport p a ha L hL c K (O a ha) hK hc.le
  let J := fp81s21_VJtransport p a ha L hL c K (O a ha) hK hc.le
  have hdL : 0 ≤ dL := mul_nonneg hK (Real.sqrt_nonneg _)
  have hjL : 0 ≤ jL := mul_nonneg (mul_nonneg hK (abs_nonneg _)) (Real.sqrt_nonneg _)
  have hD : ‖D‖ ≤ dL := by
    apply ContinuousLinearMap.opNorm_le_bound _ hdL
    intro u
    simpa only [map_zero, sub_zero] using
      fp81s21_VDtransport_difference p a ha L hL c K (O a ha) hK hc.le u 0
  have hJ : ‖J‖ ≤ jL := by
    apply ContinuousLinearMap.opNorm_le_bound _ hjL
    intro u
    simpa only [map_zero, sub_zero] using
      fp81s21_VJtransport_difference p a ha L hL c K (O a ha) hK hc.le u 0
  have hMN : (∫ ω, (‖D (UBN ω)‖ ^ 2 + ‖J (T (XN ω))‖ ^ 2) ∂A.P) ≤ M33 :=
    fp81s21_recentJoint_moment_sum A.P _ _ H dL jL S31.MN S31.MN _ _ hH.le
      hBVN.2.1 hBVN.2.2.2.1 hBVN.2.2.2.2.1 hBVN.2.2.2.2.2.1
      (le_max_left _ _) (le_max_left _ _)
  have hMG : (∫ ω, (‖D (UBG ω)‖ ^ 2 + ‖J (T (XG ω))‖ ^ 2) ∂G.P) ≤ M33 :=
    fp81s21_recentJoint_moment_sum G.P _ _ H dL jL MBG MUG _ _ hH.le
      hBVG.2.1 hBVG.2.2.2.1 hBVG.2.2.2.2.1 hBVG.2.2.2.2.2.1
      (le_max_right _ _) (le_max_right _ _)
  have htr := fp81s21_recent_joint_transport A.P G.P XN UBN XG UBG
    hNcd.1 hBN.1 hGcd.1 hBG.1 hNcd.2.1 hBN.2.1 hGcd.2.1 hBG.2.1
    (P a ha) D J T Kpred dL jL (e N) (hP a ha).1 hD hJ (he N) hraw
  rw [heL] at hpair
  exact ⟨XN, XG, UBN, UBG, YN, YG, hNcd, hGcd, hBN, hBG, hmean, hGA,
    hYN, hYG, hYNm, hYN2, hYGm, hYG2, hNid, hGid, hraw, hcenter, hpair,
    hBVN, hBVG, hMN, hMG, htr⟩

#print axioms fp81s21_recent_joint_physical
end HRS.Fp81.S21
