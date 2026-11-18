import HRS.MS.Fp81S21RecentBVPhysical

/-! Physical certificates for the recent BV carriers. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp

/-- Measurable BV corrections, their second moments, and simultaneous physical
clipped-interval identities. The carrier coercions provide continuous BV paths. -/
def fp81s21_BVLaw
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (z B : ℝ → Ω → (Euc p.d → ℝ) → ℝ)
    (Mη MB a L c K : ℝ) (ha : 0 ≤ a) (hL : 0 < L)
    (O : r26t6_IntervalOperators E (r26t3_coeff R) p.T a c K)
    (hK : 0 ≤ K) (hc : 0 ≤ c)
    (D : Ω → fp81s21_VD p a ha L hL c K O hK hc)
    (J : Ω → fp81s21_VJ p a ha L hL c K O hK hc) : Prop :=
  letI : MeasurableSpace (fp81s21_VD p a ha L hL c K O hK hc) := borel _
  letI : MeasurableSpace (fp81s21_VJ p a ha L hL c K O hK hc) := borel _
  let H := L + p.T
  let b := max (a - L) 0
  let h := a - b + p.T
  let hH := (fp81s21_recentBV_geometry p a ha L hL).horizon_nonneg
  let dL := K * Real.sqrt H
  let jL := K * |2 * (r26t3_coeff R).ν| * Real.sqrt H
  Measurable D ∧ MemLp D 2 P ∧ Measurable J ∧ MemLp J 2 P ∧
  (∫ ω, ‖D ω‖ ^ 2 ∂P) ≤ dL ^ 2 * (H * MB) ∧
  (∫ ω, ‖J ω‖ ^ 2 ∂P) ≤ jL ^ 2 * (H * Mη) ∧
  ∀ᵐ ω ∂P,
    let d := fp81s21_bvPath hH ((D ω) : fp81s21_BV0 (E := R2X p.d p.T) hH)
    let j := fp81s21_bvPath hH ((J ω) : fp81s21_BV0 (E := projTensor (R2X p.d p.T) 2) hH)
    d ⟨0, ⟨le_rfl, hH⟩⟩ = 0 ∧ j ⟨0, ⟨le_rfl, hH⟩⟩ = 0 ∧
    (∀ s t : Icc (0 : ℝ) H, h ≤ (s : ℝ) → h ≤ (t : ℝ) →
      d s = d t ∧ j s = j t) ∧
    ∀ s t : Icc (0 : ℝ) H, (s : ℝ) ≤ t →
      d t - d s = fp81s21_weightedDrift_windowInc ha le_rfl
        (r26t3_coeff R) (fun u f => B u ω f)
        (b + min (s : ℝ) h) (b + min (t : ℝ) h) ∧
      fp81s21_IsWindowJValue (r26t3_coeff R) (wholeSpaceIndex p.d) p.T a
        (fun u f => z u ω f) (Ioc (b + min (s : ℝ) h) (b + min (t : ℝ) h))
        (((j t - j s : projTensor (R2X p.d p.T) 2)) : TensorDual (R2X p.d p.T) 2)

theorem fp81s21_recentBV_combo_memCb
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {coef : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
      (2 * p.d + 8) coef hH)
    {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) H) (hs : s ∈ Icc (0 : ℝ) t)
    {φ : Euc p.d → ℝ} (hφ : IsR2DualCombo (wholeSpaceIndex p.d) φ) :
    MemCb (2 * p.d + 9) (propagatorW (r26t3_coeff R) s t φ) := by
  obtain ⟨S, coeff, rfl⟩ := hφ
  rw [s102_prop_sum (fp81s21_S102Lin p R H) hs.1 hs.2 ht.2 S coeff]
  have hb : ∀ α : MultiIndex p.d, MemCb (2 * p.d + 9)
      (propagatorW (r26t3_coeff R) s t (oscTestFun (wholeSpaceIndex p.d) α)) := by
    intro α
    have hsH : s ∈ Icc (0 : ℝ) H := ⟨hs.1, hs.2.trans ht.2⟩
    have hst : t ∈ Icc s H := ⟨hs.2, ht.2⟩
    refine ⟨?_, ?_⟩
    · have heq : 2 * p.d + 9 = (2 * p.d + 8) + 1 := by omega
      rw [heq]
      exact hstd.hD.smoothU α s hsH t hst
    · intro j hj
      refine ⟨coef α, ?_⟩
      rintro _ ⟨x, rfl⟩
      exact hstd.hD.bddU α s hsH t hst j (by omega) x
  induction S using Finset.induction_on with
  | empty =>
      change MemCb (2 * p.d + 9) (0 : Euc p.d → ℝ)
      simpa using HRS.MS.ProClosureS111.chart_memCb_smul (0 : ℝ) (hb 0)
  | @insert α S hα ih =>
      have hh := HRS.MS.ProClosureS111.chart_memCb_sub
        (HRS.MS.ProClosureS111.chart_memCb_smul (coeff α) (hb α))
        (HRS.MS.ProClosureS111.chart_memCb_smul (-1 : ℝ) ih)
      convert hh using 1
      funext x
      simp [Finset.sum_insert, hα, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]

theorem fp81s21_recentBV_origin_physical
    (p : Parameters) {δ a c K Mη MB : ℝ} (R : Trajectory p δ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (ha : 0 ≤ a)
    (O : r26t6_IntervalOperators E (r26t3_coeff R) p.T a c K)
    {coef : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
      (a + p.T) (2 * p.d + 8) coef (add_pos_of_nonneg_of_pos ha p.hT))
    (qη qB : ℝ → Ω → r26t6_Coeff)
    (z B : ℝ → Ω → (Euc p.d → ℝ) → ℝ)
    (Uη UB : Ω → fp81s21_L2History (a + p.T))
    (hη : fp81s21_TimeRep E P z qη Mη 0 (a + p.T) Uη)
    (hB : fp81s21_TimeRep E P B qB MB 0 (a + p.T) UB)
    (Mb : Ω → ℝ → ℝ)
    (hDrift : ∀ᵐ ω ∂P, S102Drift (r26t3_coeff R) (wholeSpaceIndex p.d)
      (a + p.T) (2 * p.d + 8) ((p.d : ℝ) + 2) (fun s f => B s ω f) (Mb ω))
    (hzero : ∀ᵐ ω ∂P, ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) (a + p.T)),
      B s ω (fun _ => 1) = 0) :
    ∀ᵐ ω ∂P, ∀ v w : ℝ, 0 ≤ v → v ≤ w → w ≤ a + p.T →
      O.drift v w (fp81s21_timeL2L1 (a + p.T) (add_nonneg ha p.hT.le) (UB ω)) =
        fp81s21_weightedDrift_windowInc ha le_rfl (r26t3_coeff R)
          (fun s f => B s ω f) v w ∧
      fp81s21_IsWindowJValue (r26t3_coeff R) (wholeSpaceIndex p.d) p.T a
        (fun s f => z s ω f) (Ioc v w)
        ((O.covariance v w
          (fp81s21_timeL2L1 (a + p.T) (add_nonneg ha p.hT.le) (Uη ω)) :
            projTensor (R2X p.d p.T) 2) : TensorDual (R2X p.d p.T) 2) := by
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    linarith [Nat.cast_nonneg p.d (α := ℝ)]
  filter_upwards [hη.2.2.2, hB.2.2.2, hDrift, hzero] with ω hηω hBω hd hz
  let Vη := fp81s21_timeL2L1 (a + p.T) (add_nonneg ha p.hT.le) (Uη ω)
  let VB := fp81s21_timeL2L1 (a + p.T) (add_nonneg ha p.hT.le) (UB ω)
  have hb : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) (a + p.T)),
      ∀ f, IsR2WeightedTest (2 * p.d + 8) ((p.d : ℝ) + 2) f →
        r26t6_coefficientField E VB s f = B s ω f := by
    filter_upwards [fp81s21_timeL2L1_ae _ _ (UB ω), hBω.2] with s he hs
    intro f hf
    change inner ℝ (VB s) (E.encode f) = B s ω f
    change VB s = (UB ω) s at he
    rw [he]
    simpa only [fp81s21_chartAction, zero_add] using hs.2 f hf
  have hη' : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) (a + p.T)),
      ∀ f, IsR2WeightedTest (2 * p.d + 8) ((p.d : ℝ) + 2) f →
        r26t6_coefficientField E Vη s f = z s ω f := by
    filter_upwards [fp81s21_timeL2L1_ae _ _ (Uη ω), hηω.2] with s he hs
    intro f hf
    change inner ℝ (Vη s) (E.encode f) = z s ω f
    change Vη s = (Uη ω) s at he
    rw [he]
    simpa only [fp81s21_chartAction, zero_add] using hs.2 f hf
  have hq0 : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) (a + p.T)),
      inner ℝ (VB s) (E.encode (fun _ => 1)) = 0 := by
    filter_upwards [hb, hz] with s hs hs0
    exact (hs _ (HRS.MS.ProClosureS111.constant_isWeightedTest hP 1)).trans hs0
  intro v w hv hvw hw
  constructor
  · apply fp81s21_interval_drift_eq_physical O VB ha p.hT.le hP hstd.hD
      (fp81s21_S102Lin p R (a + p.T)) hd hq0 hv hvw hw
    intro τ α
    have hsub : Ioc v (min w (a + ↑τ)) ⊆ Icc (0 : ℝ) (a + p.T) := by
      intro s hs
      exact ⟨hv.trans hs.1.le, (hs.2.trans (min_le_left _ _)).trans hw⟩
    filter_upwards [hb.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)),
      ae_restrict_mem measurableSet_Ioc] with s hs hm
    apply hs
    exact (s102_orbit_test hP hstd.hD (hsub hm)
      ⟨hm.2.trans (min_le_right _ _), by linarith [τ.property.2]⟩ α).1
  · have hvalue := fp81s21_interval_covariance_window_value O Vη hv hvw hw
    refine ⟨hvalue.1, ?_⟩
    intro ta tb φ ψ l₁ l₂ hφ hψ hta htb hl₁ hl₂
    rw [hvalue.2 ta tb φ ψ l₁ l₂ hφ hψ hta htb hl₁ hl₂]
    congr 1
    apply integral_congr_ae
    have hsub : Ioc v w ∩ Icc (0 : ℝ) (min (a + ta) (a + tb)) ⊆
        Icc (0 : ℝ) (a + p.T) := fun s hs => ⟨hv.trans hs.1.1.le, hs.1.2.trans hw⟩
    filter_upwards [hη'.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)),
      ae_restrict_mem (measurableSet_Ioc.inter measurableSet_Icc)] with s hs hm
    apply hs
    apply HRS.MS.ProClosureS111.chart_weighted_of_memCb hP
    apply HRS.MS.ProClosureS111.chart_memCb_gradient_inner
    · exact fp81s21_recentBV_combo_memCb p R (add_pos_of_nonneg_of_pos ha p.hT) hstd
        ⟨add_nonneg ha hta.1, by linarith [hta.2]⟩
        ⟨hm.2.1, hm.2.2.trans (min_le_left _ _)⟩ hφ
    · exact fp81s21_recentBV_combo_memCb p R (add_pos_of_nonneg_of_pos ha p.hT) hstd
        ⟨add_nonneg ha htb.1, by linarith [htb.2]⟩
        ⟨hm.2.1, hm.2.2.trans (min_le_right _ _)⟩ hψ

theorem fp81s21_recentBV_chart_drift_data
    {d r : ℕ} {Pw H : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (E : r26t6_WeightedChart d r Pw) (C : WholeCoeff d)
    (P : Measure Ω) (q : ℝ → Ω → r26t6_Coeff)
    {M : ℝ} (U : Ω → fp81s21_L2History H)
    (hU : fp81s21_TimeL2Rep P q M 0 H U)
    (hchart : r26t6_ChartedOrbits E C (wholeSpaceIndex d) H) :
    ∀ᵐ ω ∂P, S102Drift C (wholeSpaceIndex d) H r Pw
      (fun s f => fp81s21_chartAction E (q s ω) f) (fun s => ‖q s ω‖) := by
  filter_upwards [hU.2.2.2] with ω hω
  refine {
    hZ := fun u _ => fp81s21_chartAction_S102Z E (q u ω)
    hM := fun u _ f hf => fp81s21_chartAction_weighted_bound E (q u ω) f hf
    Mb_nonneg := fun _ => norm_nonneg _
    Mb_int := ?_
    meas := ?_ }
  · change Integrable (fun s => ‖q s ω‖) (volume.restrict (Icc (0 : ℝ) H))
    simpa only [zero_add] using (hω.1.integrable one_le_two).norm
  · intro t ht α
    have hsm : AEStronglyMeasurable (fun s => q s ω)
        (volume.restrict (Icc (0 : ℝ) H)) := by
      simpa only [zero_add] using hω.1.aestronglyMeasurable
    have hsm' := hsm.mono_ac (Measure.absolutelyContinuous_of_le
      (Measure.restrict_mono (Icc_subset_Icc_right ht.2) le_rfl))
    exact hsm'.inner (hchart.2 t ht _ (s102_isDualCombo α))

end HRS.Fp81.S21
end

#print axioms HRS.Fp81.S21.fp81s21_BVLaw

#print axioms HRS.Fp81.S21.fp81s21_recentBV_combo_memCb

#print axioms HRS.Fp81.S21.fp81s21_recentBV_origin_physical

#print axioms HRS.Fp81.S21.fp81s21_recentBV_chart_drift_data
