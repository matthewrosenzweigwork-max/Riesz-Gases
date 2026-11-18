import HRS.MS.Fp81S21RecentHeatKernelPhysical

/-! Literal derivative kernels on the recent BV carriers. Both time and point
are clipped at the physical endpoint; constants precede the window and test. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp

/-- The recent prediction index, including its constant terminal tail. -/
def fp81s21_recentHeatClip (p : Parameters) (L : ℝ) (hL : 0 < L)
    (a : ℝ) (ha : 0 ≤ a) (s : Icc (0 : ℝ) (L + p.T)) : Icc (0 : ℝ) (L + p.T) :=
  ⟨min (s : ℝ) (a - max (a - L) 0 + p.T),
    le_min s.property.1 (fp81s21_recentBV_geometry p a ha L hL).duration_nonneg,
    (min_le_left _ _).trans s.property.2⟩

/-- The literal heat derivative at the clipped absolute time and prediction. -/
def fp81s21_recentHeatEval (p : Parameters)
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (L : ℝ) (hL : 0 < L) (a : ℝ) (ha : 0 ≤ a) (Φ : Window p → ℝ)
    (j : ℕ) (y : YH p (L + p.T)) (s : Icc (0 : ℝ) (L + p.T)) :=
  iteratedFDeriv ℝ j
    (initialHeat future a ha Φ (max (a - L) 0 + fp81s21_recentHeatClip p L hL a ha s))
    (y (fp81s21_recentHeatClip p L hL a ha s))

private theorem fp81s21_recentHeatEval_continuous
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hf : fp81s21_moving_heat_full_clause p R future)
    (L : ℝ) (hL : 0 < L) (a : ℝ) (ha : 0 ≤ a) (Φ : Window p → ℝ)
    (hΦ : MemCb 5 Φ) (j : ℕ) (hj : j ≤ 2) (y : YH p (L + p.T)) :
    Continuous (fp81s21_recentHeatEval p future L hL a ha Φ j y) := by
  let g := fp81s21_recentBV_geometry p a ha L hL
  let b := max (a - L) 0
  let q := fp81s21_recentHeatClip p L hL a ha
  have hq : Continuous q := by
    exact (continuous_subtype_val.min continuous_const).subtype_mk _
  let Y : ℝ → Window p := fun t => y (projIcc 0 (L + p.T) g.horizon_nonneg (t - b))
  have hY : Continuous Y := y.continuous.comp
    (continuous_projIcc.comp (continuous_id.sub continuous_const))
  have hc := fp81s21_recent_heat_derivative_continuous p R future hf a ha Φ hΦ
    Y hY.continuousOn j hj
  have ht : Continuous (fun s => b + (q s : ℝ)) :=
    continuous_const.add (continuous_subtype_val.comp hq)
  have hm (s : Icc (0 : ℝ) (L + p.T)) : b + (q s : ℝ) ∈ Icc 0 (a + p.T) := by
    refine ⟨add_nonneg g.start_nonneg (q s).property.1, ?_⟩
    have hh : (q s : ℝ) ≤ a - b + p.T := min_le_right _ _
    dsimp [b] at *
    linarith
  have hc' := hc.comp_continuous ht hm
  have he (s : Icc (0 : ℝ) (L + p.T)) : Y (b + (q s : ℝ)) = y (q s) := by
    dsimp [Y]
    rw [add_sub_cancel_left, projIcc_val]
  change Continuous (fun s => iteratedFDeriv ℝ j
    (initialHeat future a ha Φ (b + (q s : ℝ))) (y (q s)))
  simpa only [Function.comp_def, he] using hc'

/-- A contractive image of either derivative yields the RS kernel on any BV
submodule. This is used below with the two actual physical carriers. -/
private theorem fp81s21_recent_heat_component
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hf : fp81s21_moving_heat_full_clause p R future)
    (L : ℝ) (hL : 0 < L) (a : ℝ) (ha : 0 ≤ a) (Φ : Window p → ℝ)
    (hΦ : Φ ∈ CbUnitBall (Window p) 5) (j : ℕ) (hj : j ≤ 2)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : (Window p [×j]→L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ))
    (hT : ∀ Q, ‖T Q‖ ≤ ‖Q‖)
    (V : Submodule ℝ (fp81s21_BV0 (E := E)
      (fp81s21_recentBV_geometry p a ha L hL).horizon_nonneg)) :
    ∃ F : fp81s21_RecentRSKernel (YH p (L + p.T)) V 2,
      ∀ y v, fp81s21_IsRSOn 0 (L + p.T)
        (fun τ u w => T (fp81s21_recentHeatEval p future L hL a ha Φ j y
          (projIcc 0 (L + p.T) (fp81s21_recentBV_geometry p a ha L hL).horizon_nonneg τ))
          (fp81s21_bvExt (fp81s21_recentBV_geometry p a ha L hL).horizon_nonneg v.val w -
           fp81s21_bvExt (fp81s21_recentBV_geometry p a ha L hL).horizon_nonneg v.val u))
        (F.kernel y v) := by
  let g := fp81s21_recentBV_geometry p a ha L hL
  have hH : 0 < L + p.T := add_pos hL p.hT
  let A : YH p (L + p.T) → C(Icc (0 : ℝ) (L + p.T), E →L[ℝ] ℝ) := fun y =>
    ⟨fun s => T (fp81s21_recentHeatEval p future L hL a ha Φ j y s),
      T.continuous.comp (fp81s21_recentHeatEval_continuous p R future hf L hL a ha Φ
        ⟨hΦ.1, hΦ.2.1⟩ j hj y)⟩
  have hb (y) : ‖A y‖ ≤ 1 := by
    apply (ContinuousMap.norm_le _ zero_le_one).2
    intro s
    exact (hT _).trans (fp81s21_recent_heat_derivative_bound future hf.1 a ha Φ hΦ
      _ j (by omega) _)
  have hl (y z) : ‖A y - A z‖ ≤ 1 * ‖y - z‖ := by
    apply (ContinuousMap.norm_le _ (by positivity)).2
    intro s
    change ‖T _ - T _‖ ≤ _
    rw [← map_sub]
    refine (hT _).trans ?_
    refine (fp81s21_recent_heat_derivative_lipschitz future hf.1 a ha Φ hΦ
      _ j (by omega) _ _).trans ?_
    simpa only [one_mul, ContinuousMap.sub_apply] using ContinuousMap.norm_coe_le_norm (y - z)
      (fp81s21_recentHeatClip p L hL a ha s)
  obtain ⟨F, hF⟩ := fp81s21_recentRSKernel_of_continuous_operators
    (L + p.T) 1 hH zero_le_one A hb hl
  let G : fp81s21_RecentRSKernel (YH p (L + p.T)) V 2 :=
    { kernel := fun y => (F.kernel y).comp V.subtypeL
      bound := by
        intro y
        apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
        intro v
        exact ((F.kernel y).le_opNorm v.val).trans
          (mul_le_mul_of_nonneg_right (show ‖F.kernel y‖ ≤ 2 from (F.bound y).trans (by norm_num)) (norm_nonneg v))
      lipschitz := by
        intro y z
        apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
        intro v
        exact ((F.kernel y - F.kernel z).le_opNorm v.val).trans
          (mul_le_mul_of_nonneg_right (show ‖F.kernel y - F.kernel z‖ ≤ 2 * ‖y - z‖ from
            (F.lipschitz y z).trans (by norm_num)) (norm_nonneg v)) }
  exact ⟨G, fun y v => hF y v.val⟩

/-- Both literal RS certificates; the carrier paths use their BV extensions. -/
def fp81s21_recentHeatKernelRS (p : Parameters)
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (L : ℝ) (hL : 0 < L) (a : ℝ) (ha : 0 ≤ a) (Φ : Window p → ℝ)
    {VD : Submodule ℝ (fp81s21_BV0 (E := Window p)
      (fp81s21_recentBV_geometry p a ha L hL).horizon_nonneg)}
    {VJ : Submodule ℝ (fp81s21_BV0 (E := projTensor (Window p) 2)
      (fp81s21_recentBV_geometry p a ha L hL).horizon_nonneg)}
    {KD KJ : ℝ} (FD : fp81s21_RecentRSKernel (YH p (L + p.T)) VD KD)
    (FJ : fp81s21_RecentRSKernel (YH p (L + p.T)) VJ KJ) : Prop :=
      (∀ y v, fp81s21_IsRSOn 0 (L + p.T)
        (fun τ u w =>
          let s := fp81s21_recentHeatClip p L hL a ha
            (projIcc 0 (L + p.T) (fp81s21_recentBV_geometry p a ha L hL).horizon_nonneg τ)
          fderiv ℝ (initialHeat future a ha Φ (max (a - L) 0 + s)) (y s)
            (fp81s21_bvExt (fp81s21_recentBV_geometry p a ha L hL).horizon_nonneg v.val w -
             fp81s21_bvExt (fp81s21_recentBV_geometry p a ha L hL).horizon_nonneg v.val u))
        (FD.kernel y v)) ∧
      (∀ y v, fp81s21_IsRSOn 0 (L + p.T)
        (fun τ u w => fp81s21_covariance_pairingCLM
          (fp81s21_recentHeatEval p future L hL a ha Φ 2 y
            (projIcc 0 (L + p.T) (fp81s21_recentBV_geometry p a ha L hL).horizon_nonneg τ))
          (fp81s21_bvExt (fp81s21_recentBV_geometry p a ha L hL).horizon_nonneg v.val w -
           fp81s21_bvExt (fp81s21_recentBV_geometry p a ha L hL).horizon_nonneg v.val u))
        (FJ.kernel y v))

/-- Literal first- and second-derivative RS characterizations on the physical
carriers, with both constants chosen before the window start and unit test.
The same supplied future is retained throughout. -/
theorem fp81s21_recent_heat_kernel
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {n : ℕ} {Pw0 : ℝ} (E : r26t6_WeightedChart p.d n Pw0)
    (c K : ℝ) (hc : 0 ≤ c) (hK : 0 ≤ K)
    (O : ∀ a, 0 ≤ a → r26t6_IntervalOperators E (r26t3_coeff R) p.T a c K)
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hfuture : fp81s21_moving_heat_full_clause p R future)
    (L : ℝ) (hL : 0 < L) :
    ∃ KD KJ : ℝ, 0 < KD ∧ 0 < KJ ∧
      ∀ (a : ℝ) (ha : 0 ≤ a) (Φ : Window p → ℝ), Φ ∈ CbUnitBall (Window p) 5 →
      ∃ FD : fp81s21_RecentRSKernel (YH p (L + p.T))
        (fp81s21_VD p a ha L hL c K (O a ha) hK hc) KD,
      ∃ FJ : fp81s21_RecentRSKernel (YH p (L + p.T))
        (fp81s21_VJ p a ha L hL c K (O a ha) hK hc) KJ,
      fp81s21_recentHeatKernelRS p future L hL a ha Φ FD FJ := by
  refine ⟨2, 2, by norm_num, by norm_num, ?_⟩
  intro a ha Φ hΦ
  let TD := (continuousMultilinearCurryFin1 ℝ (Window p) ℝ).toLinearIsometry.toContinuousLinearMap
  obtain ⟨FD, hD⟩ := fp81s21_recent_heat_component p R future hfuture L hL a ha Φ hΦ
    1 (by norm_num) TD (fun Q => (continuousMultilinearCurryFin1 ℝ (Window p) ℝ).norm_map Q |>.le)
    (fp81s21_VD p a ha L hL c K (O a ha) hK hc)
  let TJ : (Window p [×2]→L[ℝ] ℝ) →L[ℝ] (projTensor (Window p) 2 →L[ℝ] ℝ) :=
    { toLinearMap :=
        { toFun := fp81s21_covariance_pairingCLM
          map_add' := by
            intro Q Q'
            apply ContinuousLinearMap.ext
            intro v
            change v.val (Q + Q') = v.val Q + v.val Q'
            exact v.val.map_add Q Q'
          map_smul' := by
            intro r Q
            apply ContinuousLinearMap.ext
            intro v
            change v.val (r • Q) = r • v.val Q
            exact v.val.map_smul r Q }
      cont := fp81s21_covariance_pairingCLM_continuous }
  letI : CompleteSpace (projTensor (Window p) 2) :=
    (HRS.MC.E213U3.u3_isClosed_proj (Window p) 2).completeSpace_coe
  obtain ⟨FJ, hJ⟩ := fp81s21_recent_heat_component p R future hfuture L hL a ha Φ hΦ
    2 (by norm_num) TJ fp81s21_covariance_pairingCLM_norm_le
    (fp81s21_VJ p a ha L hL c K (O a ha) hK hc)
  refine ⟨FD, FJ, ?_, hJ⟩
  intro y v
  simpa only [TD, LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry, fp81s21_recentHeatEval,
    s102_curry_iter] using hD y v

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_recent_heat_kernel
end
