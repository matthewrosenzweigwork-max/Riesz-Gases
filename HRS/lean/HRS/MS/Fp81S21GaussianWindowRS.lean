import HRS.MS.Fp81S21RemotePhysicalG4
import HRS.MS.Fp81S21GaussianPredictionAdapted3
import HRS.MS.Fp81S21WindowRSShared

/-! Packet 36RS: supplied-data BV selection and heat continuity on windows.
The dominating random variable is a norm of the supplied history, not an
endpoint moment. No conditioning identity or raw-path equality is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp

/-- Select literal RS values using a supplied BV transport of an integrable
history. In particular the exact supremum-times-variation majorant is integrable. -/
theorem fp81s21_gaussian_rs_of_transport
    {Ω E U : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    (P : Measure Ω) (H : ℝ) (hH : 0 ≤ H)
    (X : Ω → U) (hX : Integrable X P)
    (L : U →L[ℝ] fp81s21_BV0 (E := E) hH)
    (A : Ω → ℝ → E →L[ℝ] ℝ) (F : Ω → ℝ → E)
    (hF : ∀ t, Measurable (fun ω => F ω t))
    (hFL : ∀ ω t, t ∈ Icc 0 H → F ω t = fp81s21_bvExt hH (L (X ω)) t)
    (hAm : ∀ t, Measurable (fun ω => ‖A ω t‖))
    (hAc : ∀ ω, ContinuousOn (A ω) (Icc 0 H))
    (hAb : ∀ ω t, ‖A ω t‖ ≤ 1)
    (hS : ∀ t u v, Measurable (fun ω => A ω t (F ω v - F ω u))) :
    Nonempty (fp81s21_RSBVWindow P H A F) := by
  have hFc (ω : Ω) : ContinuousOn (F ω) (Icc 0 H) :=
    (fp81s21_bvExt_continuous hH (L (X ω))).continuousOn.congr (hFL ω)
  have hvar (ω : Ω) : eVariationOn (F ω) (Icc 0 H) =
      eVariationOn (fp81s21_bvExt hH (L (X ω))) (Icc 0 H) :=
    eVariationOn.congr (hFL ω)
  have hBV (ω : Ω) : BoundedVariationOn (F ω) (Icc 0 H) := by
    change eVariationOn (F ω) (Icc 0 H) ≠ ⊤
    rw [hvar]
    exact fp81s21_bvExt_bv hH (L (X ω))
  have hmaj : ∀ q r, 0 ≤ q → q < r → r ≤ H →
      Integrable (fp81s21_rs_bv_variation_majorant A F q r) P := by
    intro q r hq hqr hr
    letI : Nonempty (Icc q r) := ⟨⟨q, le_rfl, hqr.le⟩⟩
    have hm := fp81s21_rs_bv_variation_majorant_aemeasurable P A F q r hqr.le
      hAm hF (ae_of_all P fun ω =>
        ⟨(hAc ω).norm.mono (Icc_subset_Icc hq hr),
          (hFc ω).mono (Icc_subset_Icc hq hr)⟩)
    apply (hX.norm.const_mul ‖L‖).mono' hm.aestronglyMeasurable
    filter_upwards with ω
    have hb : BddAbove (Set.range (fun t : Icc q r => ‖A ω t‖)) :=
      ⟨1, by rintro _ ⟨t, rfl⟩; exact hAb ω t⟩
    have hs0 : 0 ≤ ⨆ t : Icc q r, ‖A ω t‖ :=
      (norm_nonneg _).trans (le_ciSup hb ⟨q, le_rfl, hqr.le⟩)
    have hs1 : (⨆ t : Icc q r, ‖A ω t‖) ≤ 1 := ciSup_le (fun t => hAb ω t)
    have hv : (eVariationOn (F ω) (Icc q r)).toReal ≤ ‖L‖ * ‖X ω‖ := by
      calc
        _ ≤ (eVariationOn (F ω) (Icc 0 H)).toReal :=
          ENNReal.toReal_mono (hBV ω) (eVariationOn.mono _ (Icc_subset_Icc hq hr))
        _ = ‖L (X ω)‖ := by rw [hvar]; rfl
        _ ≤ ‖L‖ * ‖X ω‖ := L.le_opNorm _
    rw [fp81s21_rs_bv_variation_majorant, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hs0 ENNReal.toReal_nonneg)]
    exact (mul_le_mul_of_nonneg_right hs1 ENNReal.toReal_nonneg).trans (by simpa using hv)
  exact ⟨fp81s21_rsbv_window_of_bv P H A F
    (fun _ _ _ _ _ => hS)
    (fun q r hq _ hr => ae_of_all P fun ω =>
      ⟨(hAc ω).mono (Icc_subset_Icc hq hr), (hBV ω).mono (Icc_subset_Icc hq hr)⟩)
    hmaj⟩

/-- Heat derivatives on the window are continuous along every supplied
continuous window curve. The extension is a right inverse of restriction. -/
theorem fp81s21_gaussian_window_heat_continuous
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hf : fp81s21_moving_heat_full_clause p R future)
    (a : ℝ) (ha : 0 ≤ a) (Φ : Window p → ℝ) (hΦ : MemCb 5 Φ)
    (Y : ℝ → Window p) (hY : ContinuousOn Y (Icc 0 (a + p.T)))
    (j : ℕ) (hj : j ≤ 2) :
    ContinuousOn (fun t => iteratedFDeriv ℝ j (initialHeat future a ha Φ t) (Y t))
      (Icc 0 (a + p.T)) := by
  let W := HRS.MS.ProClosureS111.physicalWindowRestriction
    (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T) ha le_rfl
  let E := fp81s21_physicalWindowExtension (d := p.d)
    (m := (wholeSpaceIndex p.d : ℝ)) ha p.hT.le
  let Ψ := fun w => Φ (W w)
  have hΨ : MemCb 5 Ψ := (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof W hΦ).1
  have hWE : W.comp E = ContinuousLinearMap.id ℝ (Window p) :=
    fp81s21_physicalWindowRestriction_comp_extension ha p.hT.le
  have he (x : Window p) : W (E x) = x := congrArg (fun L => L x) hWE
  have hreg := ((hf.2.2.2 (a + p.T) (add_pos_of_nonneg_of_pos ha p.hT)).2.2.2.1
    Ψ hΨ (fun t => E (Y t)) (E.continuous.comp_continuousOn hY) j hj).1
  have hc := (ContinuousMultilinearMap.compContinuousLinearMapL
    (F := ℝ) (fun _ : Fin j => E)).continuous.comp_continuousOn hreg
  apply hc.congr
  intro t _
  have hpull := fp81s21_initialHeat_pullback_iteratedFDeriv future hf.1 a ha Φ hΦ t j
    (hj.trans (by norm_num)) (E (Y t))
  change iteratedFDeriv ℝ j (r2HeatFn (future (a + p.T)) Ψ t) (E (Y t)) =
    (iteratedFDeriv ℝ j (initialHeat future a ha Φ t) (W (E (Y t)))).compContinuousLinearMap
      (fun _ => W) at hpull
  change iteratedFDeriv ℝ j (initialHeat future a ha Φ t) (Y t) =
    (iteratedFDeriv ℝ j (r2HeatFn (future (a + p.T)) Ψ t) (E (Y t))).compContinuousLinearMap
      (fun _ => E)
  rw [hpull]
  ext v
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, he]

#print axioms fp81s21_gaussian_rs_of_transport
#print axioms fp81s21_gaussian_window_heat_continuous
end HRS.Fp81.S21
end
