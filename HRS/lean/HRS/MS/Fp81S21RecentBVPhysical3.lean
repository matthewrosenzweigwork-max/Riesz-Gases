import HRS.MS.Fp81S21RecentBVPhysical2

/-! Moment estimates for the recent BV transports. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp

/-- A bounded linear image preserves measurability and carries a second moment
bound with the square of the operator bound. -/
theorem fp81s21_recentBV_linear_moment
    {Ω U V : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [MeasurableSpace U] [BorelSpace U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V]
    (P : Measure Ω) (T : U →L[ℝ] V) (u : Ω → U) (k m : ℝ)
    (hk : 0 ≤ k) (hT : ‖T‖ ≤ k) (hu : Measurable u) (hu2 : MemLp u 2 P)
    (hm : (∫ ω, ‖u ω‖ ^ 2 ∂P) ≤ m) :
    Measurable (fun ω => T (u ω)) ∧ MemLp (fun ω => T (u ω)) 2 P ∧
      (∫ ω, ‖T (u ω)‖ ^ 2 ∂P) ≤ k ^ 2 * m := by
  have ht : MemLp (fun ω => T (u ω)) 2 P := hu2.continuousLinearMap_comp T
  refine ⟨T.continuous.measurable.comp hu, ht, ?_⟩
  calc
    _ ≤ ∫ ω, k ^ 2 * ‖u ω‖ ^ 2 ∂P := by
      apply integral_mono (ht.integrable_norm_pow (by norm_num))
        ((hu2.integrable_norm_pow (by norm_num)).const_mul (k ^ 2))
      intro ω
      calc
        ‖T (u ω)‖ ^ 2 ≤ (k * ‖u ω‖) ^ 2 := by
          apply pow_le_pow_left₀ (norm_nonneg _)
          exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
        _ = k ^ 2 * ‖u ω‖ ^ 2 := by ring
    _ = k ^ 2 * (∫ ω, ‖u ω‖ ^ 2 ∂P) := by rw [integral_const_mul]
    _ ≤ k ^ 2 * m := mul_le_mul_of_nonneg_left hm (sq_nonneg k)


local instance fp81s21_recentBV3_history_measurable (H : ℝ) :
    MeasurableSpace (fp81s21_L2History H) := borel _
local instance fp81s21_recentBV3_history_borel (H : ℝ) :
    BorelSpace (fp81s21_L2History H) := ⟨rfl⟩

/-- The supplied physical interval witnesses induce measurable BV carriers,
with the exact numerical moments and simultaneous clipped increments. -/
theorem fp81s21_recent_bv_physical
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (qη qB : ℝ → Ω → r26t6_Coeff)
    (z B zTest : ℝ → Ω → (Euc p.d → ℝ) → ℝ)
    (Mη MB a L c K : ℝ) (ha : 0 ≤ a) (hL : 0 < L)
    (O : r26t6_IntervalOperators E (r26t3_coeff R) p.T a c K)
    (hK : 0 ≤ K) (hc : 0 < c)
    (Uη0 UB0 : Ω → fp81s21_L2History (a + p.T))
    (Uη UB : Ω → fp81s21_L2History (L + p.T))
    (X : Ω → fp81s21_SmoothCH (L + p.T))
    (hI : fp81s21_IW p R P E qη qB z B zTest Mη MB a L c K ha hL O
      Uη0 UB0 Uη UB X) :
    fp81s21_BVLaw p R P E z B Mη MB a L c K ha hL O hK hc.le
      (fun ω => fp81s21_VDtransport p a ha L hL c K O hK hc.le (UB ω))
      (fun ω => fp81s21_VJtransport p a ha L hL c K O hK hc.le (Uη ω)) := by
  letI : MeasurableSpace (fp81s21_VD p a ha L hL c K O hK hc.le) := borel _
  letI : BorelSpace (fp81s21_VD p a ha L hL c K O hK hc.le) := ⟨rfl⟩
  letI : MeasurableSpace (fp81s21_VJ p a ha L hL c K O hK hc.le) := borel _
  letI : BorelSpace (fp81s21_VJ p a ha L hL c K O hK hc.le) := ⟨rfl⟩
  letI := fp81s21_VD_separable p a ha L hL c K O hK hc.le
  letI := fp81s21_VJ_separable p a ha L hL c K O hK hc.le
  let D := fp81s21_VDtransport p a ha L hL c K O hK hc.le
  let J := fp81s21_VJtransport p a ha L hL c K O hK hc.le
  have hdL : 0 ≤ K * Real.sqrt (L + p.T) := mul_nonneg hK (Real.sqrt_nonneg _)
  have hjL : 0 ≤ K * |2 * (r26t3_coeff R).ν| * Real.sqrt (L + p.T) :=
    mul_nonneg (mul_nonneg hK (abs_nonneg _)) (Real.sqrt_nonneg _)
  have hD : ‖D‖ ≤ K * Real.sqrt (L + p.T) := by
    apply ContinuousLinearMap.opNorm_le_bound _ hdL
    intro u
    simpa only [map_zero, sub_zero] using
      fp81s21_VDtransport_difference p a ha L hL c K O hK hc.le u 0
  have hJ : ‖J‖ ≤ K * |2 * (r26t3_coeff R).ν| * Real.sqrt (L + p.T) := by
    apply ContinuousLinearMap.opNorm_le_bound _ hjL
    intro u
    simpa only [map_zero, sub_zero] using
      fp81s21_VJtransport_difference p a ha L hL c K O hK hc.le u 0
  rcases hI with ⟨hη0, hB0, hη, hB, hXm, hX, heq, hTest, hphys⟩
  obtain ⟨hDm, hD2, hDb⟩ := fp81s21_recentBV_linear_moment P D UB _ _
    hdL hD hB.1 hB.2.1 hB.2.2.1
  obtain ⟨hJm, hJ2, hJb⟩ := fp81s21_recentBV_linear_moment P J Uη _ _
    hjL hJ hη.1 hη.2.1 hη.2.2.1
  refine ⟨hDm, hD2, hJm, hJ2, hDb, hJb, ?_⟩
  filter_upwards [hphys] with ω hω
  dsimp only
  simp only [fp81s21_VDtransport_coe, fp81s21_VJtransport_coe,
    fp81s21_D2_apply, fp81s21_J2_apply]
  let b := max (a - L) 0
  let h := a - b + p.T
  have hb : 0 ≤ b := le_max_right _ _
  have hh : 0 ≤ h := (fp81s21_recentBV_geometry p a ha L hL).duration_nonneg
  have ht (s : Icc (0 : ℝ) (L + p.T)) :
      b ≤ b + min (s : ℝ) h ∧ b + min (s : ℝ) h ≤ a + p.T := by
    constructor
    · exact le_add_of_nonneg_right (le_min s.property.1 hh)
    · have := min_le_right (s : ℝ) h
      dsimp [h, b] at *
      linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · change O.drift b (b + min 0 h) _ = 0
    simp only [min_eq_left hh, add_zero, O.drift_zero, ContinuousLinearMap.zero_apply]
  · change O.covariance b (b + min 0 h) _ = 0
    simp only [min_eq_left hh, add_zero, O.covariance_zero, ContinuousLinearMap.zero_apply]
  · intro s t hs ht
    simp only [min_eq_right hs, min_eq_right ht, and_self]
  · intro s t hst
    have hst' : b + min (s : ℝ) h ≤ b + min (t : ℝ) h :=
      add_le_add_right (min_le_min_right h hst) b
    have hp := hω (b + min (s : ℝ) h) (b + min (t : ℝ) h)
      (ht s).1 hst' (ht t).2
    have hd := O.drift_add b (b + min (s : ℝ) h) (b + min (t : ℝ) h)
      hb (ht s).1 hst' (ht t).2
    have hj := O.covariance_add b (b + min (s : ℝ) h) (b + min (t : ℝ) h)
      hb (ht s).1 hst' (ht t).2
    constructor
    · rw [hd, ContinuousLinearMap.add_apply, add_sub_cancel_left]
      exact hp.1.trans hp.2.1
    · rw [hj, ContinuousLinearMap.add_apply, add_sub_cancel_left, hp.2.2.1]
      exact hp.2.2.2


/-- A chart-first radius works for every supplied canonical/packet-31 family,
continuous linear path and quadratic recent history. Only origin histories
are selected; the recent linear histories are literally the supplied paths. -/
theorem fp81s21_recent_bv_interval_of_selected
    (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
    ∃ c K : ℝ, 0 < c ∧ 0 ≤ K ∧
    ∃ O : (a : ℝ) → (ha : 0 ≤ a) →
      r26t6_IntervalOperators E (r26t3_coeff R) p.T a c K,
    ∀ (ε : ℕ → ℝ) (MUG : ℝ)
      (canon : fp81s21_gaussian_V2_G_canonicalFamily p Es E R MUG ε)
      (εN εG εB : ℕ → ℝ) (S : fp81s21_Physical31 p R Es E εN εG εB)
      (N : ℕ) (hN : 2 ≤ N) (A : Particle R N) (G : GaussianRealization R)
      (L : ℝ) (hL : 0 < L) (a : ℝ) (ha : 0 ≤ a)
      (XN : A.Ω → fp81s21_SmoothCH (L + p.T))
      (XG : G.Ω → fp81s21_SmoothCH (L + p.T))
      (UBN : A.Ω → fp81s21_L2History (L + p.T))
      (UBG : G.Ω → fp81s21_L2History (L + p.T)),
    let qN := fun s ω => fp81s21_particle_embedField p Es E (S.qsηN N hN A s ω)
    let qBN := fun s ω => fp81s21_particle_embedField p Es E (S.qsBN N hN A s ω)
    let qG := fp81s21_gaussian_embedFamily p Es E (canon.q G)
    let qBG := S.gaussian.quadratic.qe G
    let MBG := S.gaussian.quadratic.Kstar ^ 4 * S.gaussian.quadratic.B / 2
    let b := max (a - L) 0
    let T := fp81s21_smoothPathToL2 (L + p.T) (add_pos hL p.hT)
    CD E A.P (fp81s21_particleEmpField R N A) b (L + p.T) XN →
    CD E G.P (fun s ω f => OscDual.eval (G.Z s ω) f) b (L + p.T) XG →
    fp81s21_TimeL2Rep A.P qBN S.MN b (L + p.T) UBN →
    fp81s21_TimeL2Rep G.P qBG MBG b (L + p.T) UBG →
    ∃ UN0 BN0 : A.Ω → fp81s21_L2History (a + p.T),
    ∃ UG0 BG0 : G.Ω → fp81s21_L2History (a + p.T),
      fp81s21_IW p R A.P E qN qBN
        (fp81s21_particleEmpField R N A) (fp81s21_particleQuadField R N A)
        (fp81s21_particleEmpField R N A) S.MN S.MN a L c K ha hL (O a ha)
        UN0 BN0 (fun ω => T (XN ω)) UBN XN ∧
      fp81s21_IW p R G.P E qG qBG
        (fun s ω f => fp81s21_chartAction E (qG s ω) f)
        (fun s ω f => fp81s21_chartAction E (qBG s ω) f)
        (fun s ω f => OscDual.eval (G.Z s ω) f) MUG MBG a L c K ha hL (O a ha)
        UG0 BG0 (fun ω => T (XG ω)) UBG XG := by
  obtain ⟨δO, hδO, hδOh, hOps⟩ := fp81s21_moving_interval_operators p
  obtain ⟨δI, hδI, hδIh, hInputs⟩ := fp81s21_moving_inputs_all p
  refine ⟨min δO δI, lt_min hδO hδI, (min_le_left _ _).trans hδOh, ?_⟩
  intro δ hδ hδle R
  obtain ⟨c, K, hc, hK, hO⟩ := hOps δ hδ (hδle.trans (min_le_left _ _)) R E
  let O := fun a ha => Classical.choice (hO a ha)
  refine ⟨c, K, hc, hK, O, ?_⟩
  intro ε MUG canon εN εG εB S N hN A G L hL a ha XN XG UBN UBG
  dsimp only
  intro hXN hXG hBN hBG
  have hH := add_pos hL p.hT
  have hQ := add_pos_of_nonneg_of_pos ha p.hT
  have hb : 0 ≤ max (a - L) 0 := le_max_right _ _
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    linarith [Nat.cast_nonneg p.d (α := ℝ)]
  obtain ⟨coef, hstd, hphys⟩ := hInputs δ hδ (hδle.trans (min_le_right _ _)) R a ha
  obtain ⟨UN0, BN0, hUN0, hBN0, htailN⟩ :=
    (S.particle N hN A).2.2.2.2.2.2 0 le_rfl (a + p.T) hQ
  have hUN := fp81s21_recentBV_CD_timeL2 p A.P E _ _ S.MN
    (max (a - L) 0) (L + p.T) hb hH (S.particle N hN A).2.2.2.2.1 XN hXN
  obtain ⟨Mb, hMb, hMbint⟩ := fp81s21_moving_M1 p R hQ hN A hstd
    (by push_cast; linarith [Nat.cast_nonneg p.d (α := ℝ)]) (hphys N hN A)
  have hNzero : ∀ᵐ ω ∂A.P, ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) (a + p.T)),
      fp81s21_particleQuadField R N A s ω (fun _ => 1) = 0 := by
    filter_upwards with ω
    filter_upwards with s
    simp [fp81s21_particleQuadField, r2QuadField, gradient, commutatorKernel, pairEnergy]
  have hNP := fp81s21_recentBV_origin_physical p R A.P E ha (O a ha) hstd
    _ _ _ _ UN0 BN0 hUN0 hBN0 Mb hMb hNzero
  have hrepG := (canon.payload G).coefficients.weak_momentRep
  obtain ⟨UG0, hUG0⟩ := fp81s21_MomentRep_time_section E G.P _ _ MUG
    0 (a + p.T) hrepG le_rfl hQ.le
  obtain ⟨BG0, hBG0, hBGweighted0, htailG⟩ :=
    (S.gaussian.quadratic.payload G).2.2.2.2.2.2.2 0 le_rfl (a + p.T) hQ
  have hUG := fp81s21_recentBV_CD_timeL2 p G.P E _ _ MUG
    (max (a - L) 0) (L + p.T) hb hH hrepG XG hXG
  have hchart := fp81s21_moving_charted_orbits p R hQ hstd hP E
  have hGdrift := fp81s21_recentBV_chart_drift_data E (r26t3_coeff R) G.P
    (S.gaussian.quadratic.qe G) BG0 hBG0 hchart
  have hGzero := fp81s21_quadraticPhysical31_zero_mass p R Es E
    S.gaussian.quadratic G (a + p.T) hQ.le
  have hGP := fp81s21_recentBV_origin_physical p R G.P E ha (O a ha) hstd
    _ _ _ _ UG0 BG0 (fp81s21_recentBV_TimeRep_chart E hUG0)
    hBGweighted0 _ hGdrift hGzero
  refine ⟨UN0, BN0, UG0, BG0, ?_, ?_⟩
  · exact fp81s21_recentBV_IW_assemble p R A.P E _ _ _ _ _ S.MN S.MN a L c K
      ha hL (O a ha) UN0 BN0 _ UBN XN (fp81s21_recentBV_TimeRep_core hUN0)
      (fp81s21_recentBV_TimeRep_core hBN0) hUN hBN hXN.1 hXN.2.1
      (Filter.EventuallyEq.rfl) hXN.2.2 hNP
  · exact fp81s21_recentBV_IW_assemble p R G.P E _ _ _ _ _ MUG _ a L c K
      ha hL (O a ha) UG0 BG0 _ UBG XG hUG0 hBG0 hUG hBG hXG.1 hXG.2.1
      (Filter.EventuallyEq.rfl) hXG.2.2 hGP

end HRS.Fp81.S21
end

#print axioms HRS.Fp81.S21.fp81s21_recentBV_linear_moment

#print axioms HRS.Fp81.S21.fp81s21_recent_bv_physical

#print axioms HRS.Fp81.S21.fp81s21_recent_bv_interval_of_selected
