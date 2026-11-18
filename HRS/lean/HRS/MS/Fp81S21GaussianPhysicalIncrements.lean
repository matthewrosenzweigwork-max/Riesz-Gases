import HRS.MS.Fp81S21GaussianCovPhysical
import HRS.MS.Fp81S21GaussianDriftPhysical

/-! Simultaneous physical increments for the supplied coefficient histories.
The probability-good events are chosen before either real endpoint. No field,
history, chart, or interval operator is reselected. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.S111K2 HRS.MS.R2Interp
open HRS.MS.CovMeas HRS.MS.S111K4J01

local instance fp81s21_GaussianPhysicalIncrements_inst1 (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H))) := borel _
local instance fp81s21_GaussianPhysicalIncrements_inst2 (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H))) := ⟨rfl⟩
local instance fp81s21_GaussianPhysicalIncrements_inst3 (H : ℝ) : MeasurableSpace (r26t6_TimeCoeff H) := borel _
local instance fp81s21_GaussianPhysicalIncrements_inst4 (H : ℝ) : BorelSpace (r26t6_TimeCoeff H) := ⟨rfl⟩

/-- Every covariance increment has its physical window-value certificate on
one common probability-one event, for the supplied history and operator. -/
theorem fp81s21_gaussian_Jcum_physical_simultaneous
    {d r : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (E : r26t6_WeightedChart d r Pw) (C : WholeCoeff d)
    (P : Measure Ω) (qG : ℝ → Ω → r26t6_Coeff) (MG a T c K : ℝ)
    (ha : 0 ≤ a) (hT : 0 < T) (hc : 0 ≤ c) (hK : 0 ≤ K)
    (O : r26t6_IntervalOperators E C T a c K)
    (UG : Ω → Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) (a + T))))
    (hUG : fp81s21_TimeL2Rep P qG MG 0 (a + T) UG) :
    ∀ᵐ ω ∂P, ∀ v r, 0 ≤ v → v ≤ r → r ≤ a + T →
      fp81s21_IsWindowJValue C (wholeSpaceIndex d) T a
        (fun s f => fp81s21_chartAction E (qG s ω) f) (Ioc v r)
        ((fp81s21_gaussian_Jcum O (add_nonneg ha hT.le) UG r ω -
          fp81s21_gaussian_Jcum O (add_nonneg ha hT.le) UG v ω :
            projTensor (R2X d T) 2) : TensorDual (R2X d T) 2) := by
  let H : ℝ := a + T
  let hH : 0 ≤ H := add_nonneg ha hT.le
  let VG : Ω → r26t6_TimeCoeff H :=
    fun ω => fp81s21_timeL2L1 H hH (UG ω)
  let Jcum : ℝ → Ω → projTensor (R2X d T) 2 :=
    fp81s21_gaussian_Jcum O hH UG
  have hbridge := fp81s21_TimeL2Rep_toL1_chart E P qG MG 0 H hH UG hUG
  filter_upwards [hbridge.2] with ω hω
  intro v r hv hvr hr
  have hω' : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) H), ∀ f,
      r26t6_coefficientField E (VG ω) s f = fp81s21_chartAction E (qG s ω) f := by
    simpa [VG, zero_add] using hω
  have hO := fp81s21_interval_covariance_window_value O (VG ω) hv hvr hr
  have hphys : fp81s21_IsWindowJValue C (wholeSpaceIndex d) T a
      (fun s f => fp81s21_chartAction E (qG s ω) f) (Ioc v r)
      (((O.covariance v r (VG ω) : projTensor (R2X d T) 2) :
        TensorDual (R2X d T) 2)) := by
    refine ⟨hO.1, ?_⟩
    intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
    have hcoord := hO.2 ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
    rw [hcoord]
    congr 1
    apply integral_congr_ae
    let S : Set ℝ := Ioc v r ∩ Icc (0 : ℝ) (min (a + ta) (a + tb))
    have hSmeas : MeasurableSet S := measurableSet_Ioc.inter measurableSet_Icc
    have hSsub : S ⊆ Icc (0 : ℝ) H := by
      intro s hs
      constructor
      · exact hv.trans hs.1.1.le
      · exact hs.2.2.trans ((min_le_left _ _).trans (add_le_add_right hta.2 a))
    have hbase : ∀ᵐ s ∂volume,
        s ∈ Icc (0 : ℝ) H → ∀ f,
          r26t6_coefficientField E (VG ω) s f =
            fp81s21_chartAction E (qG s ω) f :=
      (ae_restrict_iff' measurableSet_Icc).1 hω'
    have hS : ∀ᵐ s ∂volume.restrict S, ∀ f,
        r26t6_coefficientField E (VG ω) s f =
          fp81s21_chartAction E (qG s ω) f := by
      apply (ae_restrict_iff' hSmeas).2
      filter_upwards [hbase] with s hs
      intro hsS
      exact hs (hSsub hsS)
    filter_upwards [hS] with s hs
    exact hs (fun x => inner ℝ
      (gradient (propagatorW C s (a + ta) φa) x)
      (gradient (propagatorW C s (a + tb) φb) x))
  have hadd := congrArg (fun F => F (VG ω))
    (O.covariance_add 0 v r (le_rfl) hv hvr hr)
  have hdiff : Jcum r ω - Jcum v ω = O.covariance v r (VG ω) := by
    change Jcum r ω = Jcum v ω + O.covariance v r (VG ω) at hadd
    rw [hadd]
    abel
  rw [← hdiff] at hphys
  simpa [Jcum, fp81s21_gaussian_Jcum, H, hH, VG] using hphys

/-- Every drift increment equals the physical weighted-drift increment on
one common probability-one event, for the supplied history and operator. -/
theorem fp81s21_gaussian_Dcum_physical_simultaneous
    {d k : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (E : r26t6_WeightedChart d k Pw) (C : WholeCoeff d)
    (P : Measure Ω) (qB : ℝ → Ω → r26t6_Coeff) (MB a T c K : ℝ)
    (ha : 0 ≤ a) (hT : 0 < T) (hc : 0 ≤ c) (hK : 0 ≤ K)
    (O : r26t6_IntervalOperators E C T a c K)
    (coef : MultiIndex d → ℝ)
    (hD : S101Data C (wholeSpaceIndex d) (a + T) k coef)
    (hlin : S102Lin C (wholeSpaceIndex d) (a + T))
    (hchart : r26t6_ChartedOrbits E C (wholeSpaceIndex d) (a + T))
    (hP : (d : ℝ) < 2 * Pw)
    (UB : Ω → Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) (a + T))))
    (hUB : fp81s21_TimeL2Rep P qB MB 0 (a + T) UB)
    (hB0 : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) (a + T))),
      fp81s21_chartAction E (qB s ω) (fun _ => 1) = 0) :
    ∀ᵐ ω ∂P, ∀ v r, 0 ≤ v → v ≤ r → r ≤ a + T →
      fp81s21_gaussian_Dcum O (add_nonneg ha hT.le) UB r ω -
        fp81s21_gaussian_Dcum O (add_nonneg ha hT.le) UB v ω =
      fp81s21_weightedDrift_windowInc ha le_rfl C
        (fun s f => fp81s21_chartAction E (qB s ω) f) v r := by
  let H : ℝ := a + T
  let hH : 0 ≤ H := add_nonneg ha hT.le
  let VB : Ω → r26t6_TimeCoeff H :=
    fun ω => fp81s21_timeL2L1 H hH (UB ω)
  let Dcum : ℝ → Ω → R2X d T := fp81s21_gaussian_Dcum O hH UB
  have hbridge := fp81s21_TimeL2Rep_toL1_chart E P qB MB 0 H hH UB hUB
  filter_upwards [hbridge.2, hB0, hUB.2.2.2] with ω hω hz hsection
  intro v r hv hvr hr
  have hω' : ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) H)), ∀ f,
      r26t6_coefficientField E (VB ω) s f =
        fp81s21_chartAction E (qB s ω) f := by
    simpa [VB, zero_add] using hω
  have hq0 : ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) H)),
      inner ℝ (VB ω s) (E.encode (fun _ => (1 : ℝ))) = 0 := by
    filter_upwards [hω', hz] with s hs hs0
    have hconst := hs (fun _ => (1 : ℝ))
    change inner ℝ (VB ω s) (E.encode (fun _ => (1 : ℝ))) =
      fp81s21_chartAction E (qB s ω) (fun _ => (1 : ℝ)) at hconst
    rw [hconst]
    exact hs0
  let b : ℝ → (Euc d → ℝ) → ℝ :=
    fun s f => fp81s21_chartAction E (qB s ω) f
  let Mb : ℝ → ℝ := fun s => ‖qB s ω‖
  have hbdata : S102Drift C (wholeSpaceIndex d) H k Pw b Mb := by
    refine {
      hZ := ?_
      hM := ?_
      Mb_nonneg := ?_
      Mb_int := ?_
      meas := ?_ }
    · intro u hu
      change S102Z k Pw (fp81s21_chartAction E (qB u ω))
      exact fp81s21_chartAction_S102Z E (qB u ω)
    · intro u hu f hf
      change |fp81s21_chartAction E (qB u ω) f| ≤
        ‖qB u ω‖ * (weightedSobolevE k Pw f).toReal
      exact fp81s21_chartAction_weighted_bound E (qB u ω) f hf
    · intro u
      exact norm_nonneg _
    · change Integrable (fun s => ‖qB s ω‖)
        (volume.restrict (Icc (0 : ℝ) H))
      simpa [H, zero_add] using (hsection.1.integrable one_le_two).norm
    · intro t ht α
      have hqsm : AEStronglyMeasurable (fun s => qB s ω)
          (volume.restrict (Icc (0 : ℝ) t)) := by
        have hsub : volume.restrict (Icc (0 : ℝ) t) ≤
            volume.restrict (Icc (0 : ℝ) H) :=
          Measure.restrict_mono (Icc_subset_Icc_right ht.2) le_rfl
        have hqsm0 : AEStronglyMeasurable (fun s => qB s ω)
            (volume.restrict (Icc (0 : ℝ) H)) := by
          simpa only [zero_add] using hsection.1.aestronglyMeasurable
        exact hqsm0.mono_ac (Measure.absolutelyContinuous_of_le hsub)
      have horbit : AEStronglyMeasurable
          (fun s => E.encode (propagatorW C s t (oscTestFun (wholeSpaceIndex d) α)))
          (volume.restrict (Icc (0 : ℝ) t)) :=
        hchart.2 t ht (oscTestFun (wholeSpaceIndex d) α) (s102_isDualCombo α)
      change AEStronglyMeasurable
        (fun s => fp81s21_chartAction E (qB s ω)
          (propagatorW C s t (oscTestFun (wholeSpaceIndex d) α)))
        (volume.restrict (Icc (0 : ℝ) t))
      change AEStronglyMeasurable
        (fun s => inner ℝ (qB s ω)
          (E.encode (propagatorW C s t (oscTestFun (wholeSpaceIndex d) α))))
        (volume.restrict (Icc (0 : ℝ) t))
      exact hqsm.inner horbit
  have hrep : ∀ (τ : Icc (0 : ℝ) T) (α : MultiIndex d),
      ∀ᵐ s ∂volume.restrict (Ioc v (min r (a + (τ : ℝ)))),
        r26t6_coefficientField E (VB ω) s
            (propagatorW C s (a + (τ : ℝ)) (oscTestFun (wholeSpaceIndex d) α)) =
          b s (propagatorW C s (a + (τ : ℝ)) (oscTestFun (wholeSpaceIndex d) α)) := by
    have hbase : ∀ᵐ s ∂volume,
        s ∈ Icc (0 : ℝ) H → ∀ f,
          r26t6_coefficientField E (VB ω) s f =
            fp81s21_chartAction E (qB s ω) f :=
      (ae_restrict_iff' measurableSet_Icc).1 hω'
    intro τ α
    let S : Set ℝ := Ioc v (min r (a + (τ : ℝ)))
    have hSmeas : MeasurableSet S := measurableSet_Ioc
    have hSsub : S ⊆ Icc (0 : ℝ) H := by
      intro s hs
      refine ⟨hv.trans hs.1.le, ?_⟩
      exact (hs.2.trans (min_le_left _ _)).trans hr
    have hS : ∀ᵐ s ∂volume.restrict S, ∀ f,
        r26t6_coefficientField E (VB ω) s f =
          fp81s21_chartAction E (qB s ω) f := by
      apply (ae_restrict_iff' hSmeas).2
      filter_upwards [hbase] with s hs
      intro hsS
      exact hs (hSsub hsS)
    filter_upwards [hS] with s hs
    exact hs (propagatorW C s (a + (τ : ℝ)) (oscTestFun (wholeSpaceIndex d) α))
  have hphys : O.drift v r (VB ω) =
      fp81s21_weightedDrift_windowInc ha le_rfl C b v r := by
    exact fp81s21_interval_drift_eq_physical (O := O) (q := VB ω)
      (b := b) (Mb := Mb) (ha := ha) (hT := hT.le) (hP := hP)
      (hD := hD) (hlin := hlin) (hb := hbdata) (hq0 := hq0)
      (hv := hv) (hvw := hvr) (hw := hr) hrep
  have hadd := congrArg (fun F => F (VB ω))
    (O.drift_add 0 v r le_rfl hv hvr hr)
  have hdiff : Dcum r ω - Dcum v ω = O.drift v r (VB ω) := by
    change Dcum r ω = Dcum v ω + O.drift v r (VB ω) at hadd
    rw [hadd]
    abel
  rw [← hdiff] at hphys
  simpa [Dcum, fp81s21_gaussian_Dcum, H, hH, VB, b] using hphys

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_gaussian_Jcum_physical_simultaneous
#print axioms HRS.Fp81.S21.fp81s21_gaussian_Dcum_physical_simultaneous
