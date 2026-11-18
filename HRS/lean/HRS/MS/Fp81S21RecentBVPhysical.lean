import HRS.MS.Fp81S21RecentIntervalPhysical
import HRS.MS.Fp81S21PredictionPhysicalDefs

/-! Supplied witnesses for the recent physical interval law. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp

local instance fp81s21_recentBV_history_measurable (H : ℝ) :
    MeasurableSpace (fp81s21_L2History H) := borel _
local instance fp81s21_recentBV_history_borel (H : ℝ) :
    BorelSpace (fp81s21_L2History H) := ⟨rfl⟩

/-- The five selected witnesses and precisely the conjunction in the interval law. -/
def fp81s21_IW
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (qη qB : ℝ → Ω → r26t6_Coeff)
    (z B zTest : ℝ → Ω → (Euc p.d → ℝ) → ℝ)
    (Mη MB a L c K : ℝ) (ha : 0 ≤ a) (hL : 0 < L)
    (O : r26t6_IntervalOperators E (r26t3_coeff R) p.T a c K)
    (Uη0 UB0 : Ω → fp81s21_L2History (a + p.T))
    (Uη UB : Ω → fp81s21_L2History (L + p.T))
    (X : Ω → fp81s21_SmoothCH (L + p.T)) : Prop :=
  let b := max (a - L) 0
  let H := L + p.T
  let hH : 0 < H := add_pos hL p.hT
  let hQ : 0 ≤ a + p.T := add_nonneg ha p.hT.le
  fp81s21_TimeL2Rep P qη Mη 0 (a + p.T) Uη0 ∧
  fp81s21_TimeL2Rep P qB MB 0 (a + p.T) UB0 ∧
  fp81s21_TimeL2Rep P qη Mη b H Uη ∧
  fp81s21_TimeL2Rep P qB MB b H UB ∧
  Measurable X ∧ MemLp X 2 P ∧
  Uη =ᵐ[P] (fun ω => fp81s21_smoothPathToL2 H hH (X ω)) ∧
  (∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) H, ∀ f : Euc p.d → ℝ,
    IsR2Test f → fp81s21_chartAction E (X ω t) f = zTest (b + t) ω f) ∧
  (∀ᵐ ω ∂P, ∀ v w : ℝ, b ≤ v → v ≤ w → w ≤ a + p.T →
    let Vη0 := fp81s21_timeL2L1 (a + p.T) hQ (Uη0 ω)
    let VB0 := fp81s21_timeL2L1 (a + p.T) hQ (UB0 ω)
    let Vη := fp81s21_recentShift p a ha L hL
      (fp81s21_timeL2L1 H hH.le (Uη ω))
    let VB := fp81s21_recentShift p a ha L hL
      (fp81s21_timeL2L1 H hH.le (UB ω))
    O.drift v w VB = O.drift v w VB0 ∧
    O.drift v w VB0 = fp81s21_weightedDrift_windowInc ha le_rfl
      (r26t3_coeff R) (fun s f => B s ω f) v w ∧
    O.covariance v w Vη = O.covariance v w Vη0 ∧
    fp81s21_IsWindowJValue (r26t3_coeff R) (wholeSpaceIndex p.d) p.T a
      (fun s f => z s ω f) (Ioc v w)
      ((O.covariance v w Vη0 : projTensor (R2X p.d p.T) 2) :
        TensorDual (R2X p.d p.T) 2))

/-- Existentially closing the supplied witnesses recovers the interval law. -/
theorem fp81s21_IW_iff_recentIntervalLaw
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (qη qB : ℝ → Ω → r26t6_Coeff)
    (z B zTest : ℝ → Ω → (Euc p.d → ℝ) → ℝ)
    (Mη MB a L c K : ℝ) (ha : 0 ≤ a) (hL : 0 < L)
    (O : r26t6_IntervalOperators E (r26t3_coeff R) p.T a c K) :
    (∃ Uη0 UB0 Uη UB X, fp81s21_IW p R P E qη qB z B zTest
      Mη MB a L c K ha hL O Uη0 UB0 Uη UB X) ↔
    fp81s21_RecentIntervalLaw p R P E qη qB z B zTest Mη MB a L c K ha hL O := by
  rfl

theorem fp81s21_recentBV_TimeRep_core
    {d r : ℕ} {Pw M a H : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {E : r26t6_WeightedChart d r Pw} {P : Measure Ω}
    {Q : ℝ → Ω → (Euc d → ℝ) → ℝ} {q : ℝ → Ω → r26t6_Coeff}
    {U : Ω → fp81s21_L2History H} (h : fp81s21_TimeRep E P Q q M a H U) :
    fp81s21_TimeL2Rep P q M a H U := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  filter_upwards [h.2.2.2] with ω hω
  exact ⟨hω.1, hω.2.mono (fun _ hs => hs.1)⟩

theorem fp81s21_recentBV_TimeRep_chart
    {d r : ℕ} {Pw M a H : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (E : r26t6_WeightedChart d r Pw) {P : Measure Ω}
    {q : ℝ → Ω → r26t6_Coeff} {U : Ω → fp81s21_L2History H}
    (h : fp81s21_TimeL2Rep P q M a H U) :
    fp81s21_TimeRep E P (fun s ω f => fp81s21_chartAction E (q s ω) f)
      q M a H U := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  filter_upwards [h.2.2.2] with ω hω
  refine ⟨hω.1, ?_⟩
  filter_upwards [hω.2] with s hs
  exact ⟨hs, fun f _ => congrArg (fun z => fp81s21_chartAction E z f) hs⟩


/-- Compact-test identification, followed by Fubini, certifies the supplied
continuous path itself as the linear time history, with the field's moment bound. -/
theorem fp81s21_recentBV_CD_timeL2
    (p : Parameters) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (Q : ℝ → Ω → (Euc p.d → ℝ) → ℝ) (q : ℝ → Ω → r26t6_Coeff)
    (M b H : ℝ) (hb : 0 ≤ b) (hH : 0 < H)
    (hrep : fp81s21_MomentRep E P Q q M)
    (X : Ω → fp81s21_SmoothCH H) (hCD : CD E P Q b H X) :
    fp81s21_TimeL2Rep P q M b H
      (fun ω => fp81s21_smoothPathToL2 H hH (X ω)) := by
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    linarith [Nat.cast_nonneg p.d (α := ℝ)]
  have hsec (t : Icc (0 : ℝ) H) :
      (fun ω => X ω t) =ᵐ[P] q (b + t) := by
    filter_upwards [hCD.2.2, (hrep.2 (b + t) (add_nonneg hb t.property.1)).2.2]
      with ω hx hq
    have hcpt : ∀ f, IsR2Test f →
        fp81s21_chartAction E (X ω t - q (b + t) ω) f = 0 := by
      intro f hf
      simp only [fp81s21_chartAction, inner_sub_left]
      exact sub_eq_zero.mpr ((hx t f hf).trans (hq.1 f hf).symm)
    have hn : ENNReal.ofReal ‖X ω t - q (b + t) ω‖ = 0 := by
      rw [← fp81s21_chartAction_dualNorm hP E]
      unfold dualNormE
      apply le_antisymm _ bot_le
      refine iSup_le fun f => iSup_le fun hf => ?_
      rw [hcpt f ⟨hf.1, hf.2.1⟩]
      simp
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm
      (ENNReal.ofReal_eq_zero.mp hn) (norm_nonneg _)))
  let dt := volume.restrict (Icc (0 : ℝ) H)
  let f : ℝ × Ω → r26t6_Coeff := fun z => q (b + z.1) z.2
  let g : ℝ × Ω → r26t6_Coeff := fun z => X z.2 (fp81s21_smoothClamp H hH z.1)
  have hf : Measurable f :=
    hrep.1.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hg : Measurable g := continuous_eval.measurable.comp
    ((hCD.1.comp measurable_snd).prodMk
      ((fp81s21_smoothClamp H hH).continuous.measurable.comp measurable_fst))
  have hsections : ∀ᵐ t ∂dt, (fun ω => g (t, ω)) =ᵐ[P] fun ω => f (t, ω) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have he : fp81s21_smoothClamp H hH t = ⟨t, ht⟩ :=
      fp81s21_smoothClamp_apply_of_mem H hH ⟨t, ht⟩
    simpa only [f, g, he] using hsec ⟨t, ht⟩
  have hp : g =ᵐ[dt.prod P] f :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hg hf)).2 hsections
  have hs := Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := P) (ν := dt)).quasiMeasurePreserving.ae hp)
  let U := fun ω => fp81s21_smoothPathToL2 H hH (X ω)
  have hu : Measurable U := (fp81s21_smoothPathToL2 H hH).continuous.measurable.comp hCD.1
  have heq : ∀ᵐ ω ∂P, ∀ᵐ t ∂dt, U ω t = f (t, ω) := by
    filter_upwards [hs] with ω hω
    exact (fp81s21_smoothPathToL2_coe H hH (X ω)).trans hω
  obtain ⟨hf2, hbound, hmem⟩ := fp81s21_MomentRep_time_product E P Q q M b H hrep hb hH.le
  obtain ⟨hu2, hmoment⟩ := fp81s21_time_section_moment P H f U
    hu.aestronglyMeasurable hf2 heq
  refine ⟨hu, hu2, hmoment.trans_le hbound, ?_⟩
  filter_upwards [hmem, heq] with ω hm he
  exact ⟨hm, he⟩

theorem fp81s21_recentBV_IW_assemble
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (qη qB : ℝ → Ω → r26t6_Coeff)
    (z B zTest : ℝ → Ω → (Euc p.d → ℝ) → ℝ)
    (Mη MB a L c K : ℝ) (ha : 0 ≤ a) (hL : 0 < L)
    (O : r26t6_IntervalOperators E (r26t3_coeff R) p.T a c K)
    (Uη0 UB0 : Ω → fp81s21_L2History (a + p.T))
    (Uη UB : Ω → fp81s21_L2History (L + p.T))
    (X : Ω → fp81s21_SmoothCH (L + p.T))
    (hη0 : fp81s21_TimeL2Rep P qη Mη 0 (a + p.T) Uη0)
    (hB0 : fp81s21_TimeL2Rep P qB MB 0 (a + p.T) UB0)
    (hη : fp81s21_TimeL2Rep P qη Mη (max (a - L) 0) (L + p.T) Uη)
    (hB : fp81s21_TimeL2Rep P qB MB (max (a - L) 0) (L + p.T) UB)
    (hXm : Measurable X) (hX : MemLp X 2 P)
    (heq : Uη =ᵐ[P] fun ω => fp81s21_smoothPathToL2 (L + p.T) (add_pos hL p.hT) (X ω))
    (hTest : ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) (L + p.T), ∀ f : Euc p.d → ℝ,
      IsR2Test f → fp81s21_chartAction E (X ω t) f = zTest (max (a - L) 0 + t) ω f)
    (hphys : ∀ᵐ ω ∂P, ∀ v w : ℝ, 0 ≤ v → v ≤ w → w ≤ a + p.T →
      O.drift v w (fp81s21_timeL2L1 (a + p.T) (add_nonneg ha p.hT.le) (UB0 ω)) =
        fp81s21_weightedDrift_windowInc ha le_rfl (r26t3_coeff R) (fun s f => B s ω f) v w ∧
      fp81s21_IsWindowJValue (r26t3_coeff R) (wholeSpaceIndex p.d) p.T a
        (fun s f => z s ω f) (Ioc v w)
        ((O.covariance v w (fp81s21_timeL2L1 (a + p.T) (add_nonneg ha p.hT.le) (Uη0 ω)) :
          projTensor (R2X p.d p.T) 2) : TensorDual (R2X p.d p.T) 2)) :
    fp81s21_IW p R P E qη qB z B zTest Mη MB a L c K ha hL O
      Uη0 UB0 Uη UB X := by
  refine ⟨hη0, hB0, hη, hB, hXm, hX, heq, hTest, ?_⟩
  filter_upwards [hphys, fp81s21_recent_history_agreement p P qη Mη a L ha hL Uη0 Uη hη0 hη,
    fp81s21_recent_history_agreement p P qB MB a L ha hL UB0 UB hB0 hB] with ω hp hηω hBω
  intro v w hv hvw hw
  have hv0 : 0 ≤ v := (le_max_right _ _).trans hv
  have hsub : Ioc v w ⊆ Icc (max (a - L) 0) (a + p.T) :=
    fun s hs => ⟨hv.trans hs.1.le, hs.2.trans hw⟩
  have heη := fp81s21_interval_operators_congr O _ _ hv0 hvw hw
    (hηω.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)))
  have heB := fp81s21_interval_operators_congr O _ _ hv0 hvw hw
    (hBω.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)))
  exact ⟨heB.1, (hp v w hv0 hvw hw).1, heη.2, (hp v w hv0 hvw hw).2⟩

end HRS.Fp81.S21
end

#print axioms HRS.Fp81.S21.fp81s21_IW
#print axioms HRS.Fp81.S21.fp81s21_IW_iff_recentIntervalLaw

#print axioms HRS.Fp81.S21.fp81s21_recentBV_TimeRep_core

#print axioms HRS.Fp81.S21.fp81s21_recentBV_TimeRep_chart

#print axioms HRS.Fp81.S21.fp81s21_recentBV_CD_timeL2

#print axioms HRS.Fp81.S21.fp81s21_recentBV_IW_assemble
