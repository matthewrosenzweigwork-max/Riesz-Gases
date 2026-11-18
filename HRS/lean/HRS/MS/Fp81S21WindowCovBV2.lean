import HRS.MS.Fp81S21WindowCovBV

/-! Riemann--Stieltjes covariance on the physical observation window. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MC.Sec7.S7PIL

/-- A supplied covariance cumulative yields window RS values with the same
integrable variation bound. -/
theorem fp81s21_window_covariance_rsbv_of_selected
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
      (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T) (H := a + p.T) ha le_rfl
    let Fw := fun ω t => fp81s21_windowCovarianceMap p a ha (Fj ω t)
    let AjW := fun ω τ => fp81s21_covariance_pairingCLM
      (iteratedFDeriv ℝ 2 (initialHeat future a ha Φ τ) (W (Yh ω τ)))
    ∃ WSW : fp81s21_RSBVWindow μ (a + p.T) AjW Fw,
      ∀ q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
        Integrable (fp81s21_rs_bv_variation_majorant AjW Fw q r) μ ∧
        (∀ᵐ ω ∂μ, fp81s21_rs_bv_variation_majorant AjW Fw q r ω ≤ cbNorm 5 Φ * |V ω|) ∧
        (∀ᵐ ω ∂μ, |WSW.value q r ω| ≤ cbNorm 5 Φ * |V ω|) := by
  classical
  let H := a + p.T
  let B := Window p
  haveI : SecondCountableTopology B := by infer_instance
  haveI : SecondCountableTopology (projTensor B 2) :=
    HRS.MS.R26T3.s21g2_k06_sc (B := B) 2
  let W := HRS.MS.ProClosureS111.physicalWindowRestriction
    (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T) (H := H) ha le_rfl
  let Fw := fun ω t => fp81s21_windowCovarianceMap p a ha (Fj ω t)
  let AjW := fun ω τ => fp81s21_covariance_pairingCLM
    (iteratedFDeriv ℝ 2 (initialHeat future a ha Φ τ) (W (Yh ω τ)))
  have hprob : ∀ τ, IsProbabilityMeasure (windowFuture future a ha τ) :=
    fun τ => fp81s21_windowFuture_isProbability future hfuture.1 a ha τ
  have hC : 0 ≤ cbNorm 5 Φ := S7PIL_cbNorm_nonneg hΦ 0
  have hFm : ∀ t, Measurable (fun ω => Fw ω t) := by
    intro t
    exact (fp81s21_windowCovarianceMap p a ha).continuous.measurable.comp (hJm t)
  have hFc : ∀ᵐ ω ∂μ, ContinuousOn (Fw ω) (Icc 0 H) ∧
      BoundedVariationOn (Fw ω) (Icc 0 H) ∧
      eVariationOn (Fw ω) (Icc 0 H) ≤ eVariationOn (Fj ω) (Icc 0 H) := by
    filter_upwards [hJc, hJV] with ω hc hv
    exact fp81s21_windowCovarianceMap_bv p a ha (Fj ω) _ hc hv.1
  have hAc : ∀ᵐ ω ∂μ, ContinuousOn (AjW ω) (Icc 0 H) := by
    filter_upwards [hYc] with ω hc
    exact fp81s21_window_covariance_pairing_continuousOn p R a ha hH future hfuture Φ hΦ (Yh ω) hc
  have hdiff : ∀ τ, ContDiff ℝ 2 (initialHeat future a ha Φ τ) := by
    intro τ
    exact ((fp81s21_windowFuture_heat_derivs future hfuture.1 a ha Φ hΦ τ).1).of_le (by norm_num)
  have hsection : ∀ τ, Measurable (fun ω => ‖AjW ω τ‖) := by
    intro τ
    have hD : Continuous (iteratedFDeriv ℝ 2 (initialHeat future a ha Φ τ)) :=
      (hdiff τ).continuous_iteratedFDeriv (by norm_num)
    have hA : Continuous (fun y : B => fp81s21_covariance_pairingCLM
        (iteratedFDeriv ℝ 2 (initialHeat future a ha Φ τ) y)) :=
      fp81s21_covariance_pairingCLM_continuous.comp hD
    exact (hA.comp_stronglyMeasurable
      (W.continuous.measurable.comp (hYm τ)).stronglyMeasurable).norm.measurable
  have hnorm : ∀ ω τ, ‖AjW ω τ‖ ≤ cbNorm 5 Φ := by
    intro ω τ
    have hb := fp81s21_projected_heat_covariance_pairing_norm_le
      (windowFuture future a ha) hprob (ContinuousLinearMap.id ℝ B)
      ContinuousLinearMap.norm_id_le Φ hΦ τ (W (Yh ω τ))
    change ‖fp81s21_covariance_pairingCLM (iteratedFDeriv ℝ 2
      (r2HeatFn (windowFuture future a ha) Φ τ) (W (Yh ω τ)))‖ ≤ cbNorm 5 Φ at hb
    exact hb
  have hmajor : ∀ q r, 0 ≤ q → q ≤ r → r ≤ H →
      Integrable (fp81s21_rs_bv_variation_majorant AjW Fw q r) μ ∧
      (∀ᵐ ω ∂μ, fp81s21_rs_bv_variation_majorant AjW Fw q r ω ≤ cbNorm 5 Φ * |V ω|) := by
    intro q r hq hqr hr
    letI : Nonempty (Icc q r) := ⟨⟨q, le_rfl, hqr⟩⟩
    have hm := fp81s21_rs_bv_variation_majorant_aemeasurable μ AjW Fw q r hqr
      hsection hFm (by
        filter_upwards [hAc, hFc] with ω hA hF
        exact ⟨hA.norm.mono (Icc_subset_Icc hq hr), hF.1.mono (Icc_subset_Icc hq hr)⟩)
    have hb : ∀ᵐ ω ∂μ, fp81s21_rs_bv_variation_majorant AjW Fw q r ω ≤ cbNorm 5 Φ * |V ω| := by
      filter_upwards [hFc, hJV] with ω hf hj
      have hv : (eVariationOn (Fw ω) (Icc q r)).toReal ≤ V ω :=
        (ENNReal.toReal_mono hj.1 ((eVariationOn.mono (Fw ω) (Icc_subset_Icc hq hr)).trans hf.2.2)).trans hj.2
      have hs : (⨆ τ : Icc q r, ‖AjW ω τ‖) ≤ cbNorm 5 Φ := by
        apply ciSup_le
        intro τ
        exact hnorm ω τ
      calc
        fp81s21_rs_bv_variation_majorant AjW Fw q r ω
            ≤ cbNorm 5 Φ * (eVariationOn (Fw ω) (Icc q r)).toReal :=
              mul_le_mul_of_nonneg_right hs ENNReal.toReal_nonneg
        _ ≤ cbNorm 5 Φ * V ω := mul_le_mul_of_nonneg_left hv hC
        _ ≤ cbNorm 5 Φ * |V ω| := mul_le_mul_of_nonneg_left (le_abs_self _) hC
    refine ⟨(hVi.abs.const_mul (cbNorm 5 Φ)).mono' hm.aestronglyMeasurable ?_, hb⟩
    filter_upwards [hb] with ω hbω
    have hs : 0 ≤ ⨆ τ : Icc q r, ‖AjW ω τ‖ := by
      have hbd : BddAbove (Set.range (fun τ : Icc q r => ‖AjW ω τ‖)) := by
        refine ⟨cbNorm 5 Φ, ?_⟩
        rintro _ ⟨τ, rfl⟩
        exact hnorm ω τ
      exact (norm_nonneg _).trans (le_ciSup hbd ⟨q, le_rfl, hqr⟩)
    have hn : 0 ≤ fp81s21_rs_bv_variation_majorant AjW Fw q r ω :=
      mul_nonneg hs ENNReal.toReal_nonneg
    simpa [Real.norm_eq_abs, abs_of_nonneg hn] using hbω
  have hS : ∀ q r, 0 ≤ q → q < r → r ≤ H → ∀ τ u v,
      Measurable (fun ω => AjW ω τ (Fw ω v - Fw ω u)) := by
    intro q r hq hqr hr τ u v
    exact fp81s21_covariance_derivative_increment_measurable
      (fun τ => initialHeat future a ha Φ τ) (fun ω τ => W (Yh ω τ)) Fw hdiff
      (fun τ => (W.continuous.measurable.comp (hYm τ)).stronglyMeasurable)
      (fun t => (hFm t).stronglyMeasurable) τ u v
  have hgood : ∀ q r, 0 ≤ q → q < r → r ≤ H →
      ∀ᵐ ω ∂μ, ContinuousOn (AjW ω) (Icc q r) ∧ BoundedVariationOn (Fw ω) (Icc q r) := by
    intro q r hq hqr hr
    filter_upwards [hAc, hFc] with ω ha' hf
    exact ⟨ha'.mono (Icc_subset_Icc hq hr), hf.2.1.mono (Icc_subset_Icc hq hr)⟩
  let WS := fp81s21_rsbv_window_of_bv μ H AjW Fw hS hgood
    (fun q r hq hqr hr => (hmajor q r hq hqr.le hr).1)
  refine ⟨WS, ?_⟩
  intro q r hq hqr hr
  refine ⟨(hmajor q r hq hqr hr).1, (hmajor q r hq hqr hr).2, ?_⟩
  by_cases hlt : q < r
  · filter_upwards [WS.value_isRS q r hq hqr hr, hgood q r hq hlt hr,
      (hmajor q r hq hqr hr).2] with ω hrs hg hb
    exact (fp81s21_rsOn_bv_bound hlt (Fw ω) (AjW ω) hg.2 hg.1 hrs).trans hb
  · have heq : q = r := le_antisymm hqr (le_of_not_gt hlt)
    subst r
    filter_upwards [WS.value_zero q hq hr] with ω hz
    rw [hz]
    simpa using mul_nonneg hC (abs_nonneg (V ω))

end HRS.Fp81.S21
end
#print axioms HRS.Fp81.S21.fp81s21_window_covariance_rsbv_of_selected
