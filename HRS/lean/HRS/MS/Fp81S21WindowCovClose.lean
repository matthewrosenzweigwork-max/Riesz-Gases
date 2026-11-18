import HRS.MS.Fp81S21SharedRS
import HRS.MS.Fp81S21CovRSSelected
import HRS.MS.Fp81S21SharedRS2
import HRS.MS.Fp81S21SharedRSData
import HRS.MS.Fp81S21WindowCovId6
import HRS.MS.Fp81S21WindowCovId7
import HRS.MS.Fp81S21WindowCovBV
import HRS.MS.Fp81S21WindowCovBV2
import HRS.MS.Fp81S21WindowCovRSId
import HRS.MS.Fp81S21WindowCovRSId2
import HRS.MS.Fp81S21WindowCovId4
import HRS.MS.Fp81S21WindowCovId5
import HRS.MS.Fp81S21DualMeas2

/-! Packet 20 window covariance closure, retaining the shared future,
prediction, and covariance cumulative selected by the finite RS package. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MC.E213O
open HRS.MC.Sec7.S7PIL

/-- Physical interval covariance identification for a supplied shared
covariance cumulative. The four local inputs are selected simultaneously over
all admissible intervals. -/
def fp81s21_shared_physical_window_covariance_identification
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (a : ℝ) (ha : 0 ≤ a) {N : ℕ} (A : Particle R N)
    (Cmix cdec : ℝ) (K : ℝ → ℝ)
    (Fj : A.Ω → ℝ → projTensor
      (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2) : Prop :=
  let z := fun ω => fp81s21_horizonFieldExtension (a + p.T)
    (fun v => fp81s21_movingRawEtaField p R A ω v)
  let P : ℝ := (p.d : ℝ) + 2
  ∀ᵐ ω ∂A.P,
    ∃ (D : fp81s21_WindowLocalInput (r26t3_coeff R)
          (wholeSpaceIndex p.d : ℝ) p.T a (2 * p.d + 8) P (z ω) Cmix cdec)
      (D' : fp81s21_WindowLocalInput (r26t3_coeff R)
          (wholeSpaceIndex p.d : ℝ) p.T a (2 * p.d + 8) P (z ω) Cmix cdec)
      (Dsum : fp81s21_WindowLocalInput (r26t3_coeff R)
          (wholeSpaceIndex p.d : ℝ) p.T a (2 * p.d + 8) P ((z + z) ω) Cmix cdec)
      (Dsmul : fp81s21_WindowLocalInput (r26t3_coeff R)
          (wholeSpaceIndex p.d : ℝ) p.T a (2 * p.d + 8) P (((1 : ℝ) • z) ω) Cmix cdec),
      ∀ q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
        tensorPow' 2
          (HRS.MS.ProClosureS111.physicalWindowRestriction
            (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
            (T := p.T) (H := a + p.T) ha le_rfl)
          (((Fj ω r - Fj ω q : projTensor
            (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2) :
              TensorDual (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2)) =
          ((fp81s21_window_covariance_measure D q r : projTensor (Window p) 2) :
            TensorDual (Window p) 2) ∧
        fp81s21_covariance_interval_contract D D' Dsum Dsmul
          (K P) q r

/-- Build the unprojected full-history covariance RS record from supplied
prediction and cumulative witnesses. -/
theorem fp81s21_full_covariance_rsbv_of_shared
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (a : ℝ) (ha : 0 ≤ a) (hH : 0 < a + p.T)
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hfuture : fp81s21_moving_heat_full_clause p R future)
    (Φ : Window p → ℝ) (hΦ : MemCb 5 Φ)
    (Yh : Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T))
    (Fj : Ω → ℝ → projTensor (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2)
    (V : Ω → ℝ)
    (hYm : ∀ t, Measurable (fun ω => Yh ω t))
    (hJm : ∀ t, Measurable (fun ω => Fj ω t))
    (hYc : ∀ᵐ ω ∂μ, ContinuousOn (Yh ω) (Icc 0 (a + p.T)))
    (hJc : ∀ᵐ ω ∂μ, ContinuousOn (Fj ω) (Icc 0 (a + p.T)))
    (hVi : Integrable V μ)
    (hJV : ∀ᵐ ω ∂μ, BoundedVariationOn (Fj ω) (Icc 0 (a + p.T)) ∧
      (eVariationOn (Fj ω) (Icc 0 (a + p.T))).toReal ≤ V ω) :
    let W := HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
      (T := p.T) (H := a + p.T) ha le_rfl
    let Ψ := fun w => Φ (W w)
    let AjH := fun ω τ => fp81s21_covariance_pairingCLM
      (iteratedFDeriv ℝ 2
        (r2HeatFn (future (a + p.T)) Ψ τ) (Yh ω τ))
    Nonempty (fp81s21_RSBVWindow μ (a + p.T) AjH Fj) := by
  classical
  let H := a + p.T
  let B := OscPath p.d (wholeSpaceIndex p.d : ℝ) H
  let W : B →L[ℝ] Window p :=
    HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
      (T := p.T) (H := H) ha le_rfl
  let Ψ : B → ℝ := fun w => Φ (W w)
  let AjH : Ω → ℝ → projTensor B 2 →L[ℝ] ℝ := fun ω τ =>
    fp81s21_covariance_pairingCLM
      (iteratedFDeriv ℝ 2 (r2HeatFn (future H) Ψ τ) (Yh ω τ))
  letI : SecondCountableTopology B := by infer_instance
  letI : SecondCountableTopology (projTensor B 2) :=
    HRS.MS.R26T3.s21g2_k06_sc (B := B) 2
  letI : MeasurableAdd₂ (projTensor B 2) := ⟨continuous_add.measurable⟩
  letI : CompleteSpace (projTensor B 2) :=
    HRS.Fp81.V01.fp81v01_projTensorComplete B 2
  have hΨ : MemCb 5 Ψ :=
    (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof W hΦ).1
  have hprob : ∀ τ, IsProbabilityMeasure (future H τ) :=
    fun τ => hfuture.1 H τ
  have hdiff : ∀ τ, ContDiff ℝ 2 (r2HeatFn (future H) Ψ τ) := by
    intro τ
    exact ((hfuture.2.2.2 H hH).2.2.2.2 Ψ hΨ τ).1.of_le (by norm_num)
  have hAc : ∀ᵐ ω ∂μ, ContinuousOn (AjH ω) (Icc 0 H) := by
    filter_upwards [hYc] with ω hc
    have hreg := (hfuture.2.2.2 H hH).2.2.2.1 Ψ hΨ (Yh ω) hc 2 (by norm_num)
    exact fp81s21_covariance_pairingCLM_continuous.comp_continuousOn hreg.1
  have hsection : ∀ τ, Measurable (fun ω => ‖AjH ω τ‖) := by
    intro τ
    have hD : Continuous (iteratedFDeriv ℝ 2 (r2HeatFn (future H) Ψ τ)) :=
      (hdiff τ).continuous_iteratedFDeriv (by norm_num)
    have hA : Continuous (fun y : B => fp81s21_covariance_pairingCLM
        (iteratedFDeriv ℝ 2 (r2HeatFn (future H) Ψ τ) y)) :=
      fp81s21_covariance_pairingCLM_continuous.comp hD
    exact (hA.comp_stronglyMeasurable (hYm τ).stronglyMeasurable).norm.measurable
  have hnorm : ∀ ω τ, ‖AjH ω τ‖ ≤ cbNorm 5 Ψ := by
    intro ω τ
    calc
      ‖AjH ω τ‖ ≤
          ‖iteratedFDeriv ℝ 2 (r2HeatFn (future H) Ψ τ) (Yh ω τ)‖ :=
        fp81s21_covariance_pairingCLM_norm_le _
      _ ≤ cbNorm 5 Ψ :=
        s102_deriv_norm_le (future H) hprob (ContinuousLinearMap.id ℝ B)
          ContinuousLinearMap.norm_id_le hΨ τ (Yh ω τ)
  have hmajor : ∀ q r, 0 ≤ q → q ≤ r → r ≤ H →
      Integrable (fp81s21_rs_bv_variation_majorant AjH Fj q r) μ ∧
      (∀ᵐ ω ∂μ,
        fp81s21_rs_bv_variation_majorant AjH Fj q r ω ≤ cbNorm 5 Ψ * |V ω|) := by
    intro q r hq hqr hr
    letI : Nonempty (Icc q r) := ⟨⟨q, le_rfl, hqr⟩⟩
    have hm := fp81s21_rs_bv_variation_majorant_aemeasurable μ AjH Fj q r hqr
      hsection hJm (by
        filter_upwards [hAc, hJc] with ω hA hF
        exact ⟨hA.norm.mono (Icc_subset_Icc hq hr),
          hF.mono (Icc_subset_Icc hq hr)⟩)
    have hb : ∀ᵐ ω ∂μ,
        fp81s21_rs_bv_variation_majorant AjH Fj q r ω ≤ cbNorm 5 Ψ * |V ω| := by
      filter_upwards [hJV] with ω hv
      have hvar : (eVariationOn (Fj ω) (Icc q r)).toReal ≤ V ω :=
        (ENNReal.toReal_mono hv.1
          (eVariationOn.mono (Fj ω) (Icc_subset_Icc hq hr))).trans hv.2
      have hsup : (⨆ τ : Icc q r, ‖AjH ω τ‖) ≤ cbNorm 5 Ψ := by
        apply ciSup_le
        intro τ
        exact hnorm ω τ
      calc
        fp81s21_rs_bv_variation_majorant AjH Fj q r ω ≤
            cbNorm 5 Ψ * (eVariationOn (Fj ω) (Icc q r)).toReal :=
          mul_le_mul_of_nonneg_right hsup ENNReal.toReal_nonneg
        _ ≤ cbNorm 5 Ψ * V ω :=
          mul_le_mul_of_nonneg_left hvar (S7PIL_cbNorm_nonneg hΨ 0)
        _ ≤ cbNorm 5 Ψ * |V ω| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (S7PIL_cbNorm_nonneg hΨ 0)
    refine ⟨(hVi.abs.const_mul (cbNorm 5 Ψ)).mono' hm.aestronglyMeasurable ?_, hb⟩
    filter_upwards [hb] with ω hbω
    have hsup : 0 ≤ ⨆ τ : Icc q r, ‖AjH ω τ‖ := by
      have hbd : BddAbove (Set.range (fun τ : Icc q r => ‖AjH ω τ‖)) := by
        refine ⟨cbNorm 5 Ψ, ?_⟩
        rintro _ ⟨τ, rfl⟩
        exact hnorm ω τ
      exact (norm_nonneg _).trans (le_ciSup hbd ⟨q, le_rfl, hqr⟩)
    have hnonneg : 0 ≤ fp81s21_rs_bv_variation_majorant AjH Fj q r ω := by
      unfold fp81s21_rs_bv_variation_majorant
      exact mul_nonneg hsup ENNReal.toReal_nonneg
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hbω
  have hS : ∀ q r, 0 ≤ q → q < r → r ≤ H →
      ∀ τ u v, Measurable (fun ω => AjH ω τ (Fj ω v - Fj ω u)) := by
    intro q r hq hqr hr τ u v
    exact fp81s21_covariance_derivative_increment_measurable
      (fun τ => r2HeatFn (future H) Ψ τ) Yh Fj hdiff
      (fun τ => (hYm τ).stronglyMeasurable)
      (fun t => (hJm t).stronglyMeasurable) τ u v
  have hgood : ∀ q r, 0 ≤ q → q < r → r ≤ H →
      ∀ᵐ ω ∂μ, ContinuousOn (AjH ω) (Icc q r) ∧
        BoundedVariationOn (Fj ω) (Icc q r) := by
    intro q r hq hqr hr
    filter_upwards [hAc, hJc, hJV] with ω hA hF hv
    exact ⟨hA.mono (Icc_subset_Icc hq hr),
      hv.1.mono (Icc_subset_Icc hq hr)⟩
  let WSH := fp81s21_rsbv_window_of_bv μ H AjH Fj hS hgood
    (fun q r hq hqr hr => (hmajor q r hq hqr.le hr).1)
  exact ⟨WSH⟩

/-- The physical-window covariance RS records and their interval identities
are built from the same data and level family as the shared finite-projection
RS theorem. -/
theorem fp81s21_moving_window_covariance_close (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ future : (H : ℝ) → ℝ →
            Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H),
          fp81s21_moving_heat_full_clause p R future ∧
          ∃ Cmix cdec : ℝ, ∃ K : ℝ → ℝ,
            ∀ (a : ℝ) (ha : 0 ≤ a) (hH : 0 < a + p.T)
              (N : ℕ) (hN : 2 ≤ N) (A : Particle R N)
              (F : FilteredParticle A),
              ∃ D : fp81s21_finproj_shared_data p R a A F,
                fp81s21_shared_physical_window_covariance_identification
                  p R a ha A Cmix cdec K D.Fj ∧
                ∀ Φ : Window p → ℝ, MemCb 5 Φ →
                  let W := HRS.MS.ProClosureS111.physicalWindowRestriction
                    (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
                    (T := p.T) (H := a + p.T) ha le_rfl
                  let Fw := fun ω t =>
                    fp81s21_windowCovarianceMap p a ha (D.Fj ω t)
                  let Ψ := fun w => Φ (W w)
                  let AjH := fun ω τ => fp81s21_covariance_pairingCLM
                    (iteratedFDeriv ℝ 2
                      (r2HeatFn (future (a + p.T)) Ψ τ) (D.Yh ω τ))
                  let AjW := fun ω τ => fp81s21_covariance_pairingCLM
                    (iteratedFDeriv ℝ 2
                      (initialHeat future a ha Φ τ) (W (D.Yh ω τ)))
                  ∃ WS : fp81s21_finproj_shared_RS_family
                      p R a ha hH A future F Φ D,
                    (∀ L q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
                      ∀ᵐ ω ∂A.P,
                        IntegrableOn
                          (fp81s21_moving_drift_cyl_sum
                            p R A F a ha hH L Φ ω) (Ioc q r)) ∧
                    (∀ L q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
                      ∀ᵐ ω ∂A.P,
                        IntegrableOn
                          (fp81s21_moving_covariance_cyl_sum
                            p R A F a ha hH L Φ ω) (Ioc q r)) ∧
                    (∀ L q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
                      ∀ᵐ ω ∂A.P,
                        (WS L).drift.value q r ω =
                          ∫ u in Ioc q r,
                            fp81s21_moving_drift_cyl_sum
                              p R A F a ha hH L Φ ω u) ∧
                    (∀ L q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
                      ∀ᵐ ω ∂A.P,
                        (WS L).covariance.value q r ω =
                          ∫ u in Ioc q r,
                            fp81s21_moving_covariance_cyl_sum
                              p R A F a ha hH L Φ ω u) ∧
                    (∀ L q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
                      Real.sqrt N *
                        ((∫ ω, fp81s21_moving_heat_ito_endpoint
                            p R A a ha hH future L Φ r ω ∂A.P) -
                          (∫ ω, fp81s21_moving_heat_ito_endpoint
                            p R A a ha hH future L Φ q ω ∂A.P)) =
                        fp81s21_WindowRS_corr (WS L) q r) ∧
                    ∃ WSH : fp81s21_RSBVWindow A.P (a + p.T) AjH D.Fj,
                    ∃ WSW : fp81s21_RSBVWindow A.P (a + p.T) AjW Fw,
                      (∀ q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
                        Integrable
                          (fp81s21_rs_bv_variation_majorant AjW Fw q r) A.P ∧
                        (∀ᵐ ω ∂A.P,
                          fp81s21_rs_bv_variation_majorant AjW Fw q r ω ≤
                            cbNorm 5 Φ * |D.Vj ω|) ∧
                        (∀ᵐ ω ∂A.P,
                          |WSW.value q r ω| ≤ cbNorm 5 Φ * |D.Vj ω|)) ∧
                      (∀ q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
                        WSH.value q r =ᵐ[A.P] WSW.value q r) ∧
                      (∀ q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
                        ∀ (jval : A.Ω → ℝ),
                          (∀ᵐ ω ∂A.P,
                            fp81s21_IsRSOn q r
                              (fun τ u v =>
                                r2JPair (r26t3_coeff R)
                                  (wholeSpaceIndex p.d : ℝ) (a + p.T)
                                  (fp81s21_movingRawEtaField p R A ω)
                                  (Ioc u v)
                                  (iteratedFDeriv ℝ 2
                                    (r2HeatFn (future (a + p.T))
                                      (fun w => Φ (W w)) τ)
                                    (D.Yh ω τ)))
                              (jval ω)) →
                          jval =ᵐ[A.P] WSW.value q r)
                
                := by
  obtain ⟨δs, hδs, hsHalf, hshared⟩ := fp81s21_moving_shared_rs_data p
  obtain ⟨δi, hδi, hiHalf, hinputs⟩ := fp81s21_moving_inputs_all p
  obtain ⟨δc, hδc, hcHalf, hphysical⟩ :=
    fp81s21_physical_window_covariance_selected p
  let δ0 := min δs (min δi δc)
  refine ⟨δ0, lt_min hδs (lt_min hδi hδc), ?_, ?_⟩
  · exact (min_le_left _ _).trans hsHalf
  · intro δ hδ hδle R
    have hδs' : δ ≤ δs := hδle.trans (min_le_left _ _)
    have hδi' : δ ≤ δi :=
      hδle.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hδc' : δ ≤ δc :=
      hδle.trans ((min_le_right _ _).trans (min_le_right _ _))
    obtain ⟨future, hfuture, hmain⟩ := hshared δ hδ hδs' R
    obtain ⟨Cmix, cdec, K, hselect⟩ :=
      hphysical δ hδ hδc' R
    refine ⟨future, hfuture, Cmix, cdec, K, ?_⟩
    intro a ha hH N hN A F
    obtain ⟨c, hstd, hphysAll⟩ := hinputs δ hδ hδi' R a ha
    have hphys : Fp81MovingPhysicalInputs R hN A (a + p.T) :=
      hphysAll N hN A
    have hlin : S102Lin (r26t3_coeff R)
        (wholeSpaceIndex p.d : ℝ) (a + p.T) :=
      fp81s21_S102Lin p R (a + p.T)
    obtain ⟨D, hlevels⟩ := hmain a ha hH N hN A F
    have hJraw : ∀ᵐ ω ∂A.P,
        ∀ q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
          IsR2JValue (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
            (a + p.T) (fp81s21_movingRawEtaField p R A ω) (Ioc q r)
            (((D.Fj ω r - D.Fj ω q : projTensor
              (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2) :
                TensorDual (OscPath p.d (wholeSpaceIndex p.d : ℝ)
                  (a + p.T)) 2)) := by
      filter_upwards [D.Fj_good] with ω hg
      exact hg.1
    have hL1 : ∀ᵐ ω ∂A.P,
        IsR2L1F (2 * p.d + 8) ((p.d : ℝ) + 2) (a + p.T)
          (fp81s21_horizonFieldExtension (a + p.T)
            (fp81s21_movingRawEtaField p R A ω)) :=
      fp81s21_moving_raw_eta_horizonL1F_ae p R hH hN A hphys
    have hd : 0 < p.d := by linarith [p.hd]
    have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
      push_cast
      nlinarith [p.hd]
    have hdual :
        (let z : A.Ω → ℝ → (Euc p.d → ℝ) → ℝ := fun ω =>
          fp81s21_horizonFieldExtension (a + p.T)
            (fun v => fp81s21_movingRawEtaField p R A ω v)
         let P : ℝ := (p.d : ℝ) + 2
         ∀ᵐ ω ∂A.P,
           AEMeasurable (fun v => dualNormE (2 * p.d + 8) P (z ω v))
             (volume.restrict (Icc (0 : ℝ) (a + p.T))) ∧
           AEMeasurable (fun v => dualNormE (2 * p.d + 8) P ((z + z) ω v))
             (volume.restrict (Icc (0 : ℝ) (a + p.T))) ∧
           AEMeasurable (fun v => dualNormE (2 * p.d + 8) P
             (((1 : ℝ) • z) ω v))
             (volume.restrict (Icc (0 : ℝ) (a + p.T)))) := by
      dsimp
      filter_upwards [hL1] with ω hω
      have hdual0 := fp81s21_dualNormE_aemeasurable_of_IsR2L1F
        (d := p.d) (r := 2 * p.d + 8) (Pw := (p.d : ℝ) + 2)
        (T := a + p.T) hd hP hω
      have hsum := fp81s21_IsR2L1F_add_of_aemeasurable_dualNorm
        hω hω hdual0
      have hdualSum := fp81s21_dualNormE_aemeasurable_add_of_IsR2L1F
        (d := p.d) (r := 2 * p.d + 8) (Pw := (p.d : ℝ) + 2)
        (T := a + p.T) hd hP hω hω
      have hsmul := fp81s21_IsR2L1F_smul (c := (1 : ℝ)) hω
      have hdualSmul := fp81s21_dualNormE_aemeasurable_smul_of_IsR2L1F
        (d := p.d) (r := 2 * p.d + 8) (Pw := (p.d : ℝ) + 2)
        (T := a + p.T) (c := (1 : ℝ)) hd hP hω
      exact ⟨hdual0, hdualSum, hdualSmul⟩
    have hident := hselect a ha N hN A hphys D.Fj hJraw hdual
    have hphysicalIdent :
        fp81s21_shared_physical_window_covariance_identification
          p R a ha A Cmix cdec K D.Fj := by
      dsimp [fp81s21_shared_physical_window_covariance_identification]
      exact hident
    refine ⟨D, hphysicalIdent, ?_⟩
    intro Φ hΦ
    obtain ⟨WS, hpayload⟩ := hlevels Φ hΦ
    let W := HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
      (T := p.T) (H := a + p.T) ha le_rfl
    let Fw : A.Ω → ℝ → projTensor (Window p) 2 :=
      fun ω t => fp81s21_windowCovarianceMap p a ha (D.Fj ω t)
    let AjW : A.Ω → ℝ → projTensor (Window p) 2 →L[ℝ] ℝ :=
      fun ω τ => fp81s21_covariance_pairingCLM
        (iteratedFDeriv ℝ 2 (initialHeat future a ha Φ τ) (W (D.Yh ω τ)))
    have hJc : ∀ᵐ ω ∂A.P, ContinuousOn (D.Fj ω) (Icc 0 (a + p.T)) := by
      filter_upwards [D.Fj_good] with ω hg
      exact hg.2.1
    have hJV : ∀ᵐ ω ∂A.P,
        BoundedVariationOn (D.Fj ω) (Icc 0 (a + p.T)) ∧
        (eVariationOn (D.Fj ω) (Icc 0 (a + p.T))).toReal ≤ D.Vj ω := by
      filter_upwards [D.Fj_good] with ω hg
      exact ⟨hg.2.2.1, hg.2.2.2⟩
    obtain ⟨WSW, hB⟩ := fp81s21_window_covariance_rsbv_of_selected
      A.P p R a ha hH future hfuture Φ hΦ D.Yh D.Fj D.Vj
      D.Yh_measurable D.Fj_measurable D.Yh_continuous hJc
      D.Vj_integrable hJV
    rcases hpayload with ⟨hDOn, hJOn, hDval, hJval, hidentity⟩
    have hDOn' : ∀ L q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
        ∀ᵐ ω ∂A.P,
          IntegrableOn
            (fp81s21_moving_drift_cyl_sum p R A F a ha hH L Φ ω)
            (Ioc q r) := by
      simpa [fp81s21_finproj_shared_RS_family] using hDOn
    have hJOn' : ∀ L q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
        ∀ᵐ ω ∂A.P,
          IntegrableOn
            (fp81s21_moving_covariance_cyl_sum p R A F a ha hH L Φ ω)
            (Ioc q r) := by
      simpa [fp81s21_finproj_shared_RS_family] using hJOn
    have hDval' : ∀ L q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
        ∀ᵐ ω ∂A.P,
          (WS L).drift.value q r ω =
            ∫ u in Ioc q r,
              fp81s21_moving_drift_cyl_sum p R A F a ha hH L Φ ω u := by
      simpa [fp81s21_finproj_shared_RS_family] using hDval
    have hJval' : ∀ L q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
        ∀ᵐ ω ∂A.P,
          (WS L).covariance.value q r ω =
            ∫ u in Ioc q r,
              fp81s21_moving_covariance_cyl_sum p R A F a ha hH L Φ ω u := by
      simpa [fp81s21_finproj_shared_RS_family] using hJval
    obtain ⟨WSH⟩ := fp81s21_full_covariance_rsbv_of_shared
      A.P p R a ha hH future hfuture Φ hΦ D.Yh D.Fj D.Vj
      D.Yh_measurable D.Fj_measurable D.Yh_continuous hJc
      D.Vj_integrable hJV
    have hC : ∀ q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
        WSH.value q r =ᵐ[A.P] WSW.value q r := by
      intro q r hq hqr hr
      exact fp81s21_unprojected_window_covariance_rs_values p A.P a ha
        future hfuture.1 Φ hΦ D.Yh D.Fj WSH WSW q r hq hqr hr
    have hJvalue : ∀ q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
        ∀ (jval : A.Ω → ℝ),
          (∀ᵐ ω ∂A.P,
            fp81s21_IsRSOn q r
              (fun τ u v =>
                r2JPair (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
                  (a + p.T) (fp81s21_movingRawEtaField p R A ω)
                  (Ioc u v)
                  (iteratedFDeriv ℝ 2
                    (r2HeatFn (future (a + p.T)) (fun w => Φ (W w)) τ)
                    (D.Yh ω τ))) (jval ω)) →
          jval =ᵐ[A.P] WSW.value q r := by
      intro q r hq hqr hr jval hjval
      exact fp81s21_unprojected_isRSOn_window_covariance_value
        p A.P a ha future hfuture.1 Φ hΦ (r26t3_coeff R)
        (fp81s21_movingRawEtaField p R A) D.Yh D.Fj hJraw WSW
        q r hq hqr hr jval hjval
    refine ⟨WS, hDOn', hJOn', hDval', hJval', ?_, WSH, WSW, hB, hC, hJvalue⟩
    simpa [fp81s21_finproj_shared_RS_family] using hidentity

#print axioms HRS.Fp81.S21.fp81s21_shared_physical_window_covariance_identification
#print axioms HRS.Fp81.S21.fp81s21_full_covariance_rsbv_of_shared
#print axioms HRS.Fp81.S21.fp81s21_moving_window_covariance_close
end HRS.Fp81.S21
end
