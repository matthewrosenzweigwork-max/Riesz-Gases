import HRS.MS.Fp81S21WinRSBV
import HRS.MS.Fp81S21MovingHeat5
import HRS.MS.Fp81S21WeightedDrift2
import HRS.MS.Fp81S21DriftProjRemoval2

/-! Unprojected physical-window BV Riemann--Stieltjes families. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp
open HRS.MC.Sec7.S7PIL

/-- The physical unprojected drift integrand has a window BV Riemann--Stieltjes
family, with the exact variation majorant integrable on every subinterval. -/
theorem fp81s21_moving_window_rsbv (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∃ future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H),
        fp81s21_moving_heat_full_clause p R future ∧
        ∀ (a : ℝ) (ha : 0 ≤ a) (hH : 0 < a + p.T)
          (N : ℕ) (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A),
        ∃ (Yh Fd : A.Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T))
          (V : A.Ω → ℝ),
          (∀ t, Measurable (fun ω => Yh ω t)) ∧
          (∀ t, Measurable (fun ω => Fd ω t)) ∧
          Integrable V A.P ∧
          (∀ᵐ ω ∂A.P,
            (∀ t ∈ Icc (0 : ℝ) (a + p.T),
              Yh ω t = s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
                (a + p.T) A.P A.X ω t) ∧
            ContinuousOn (Yh ω) (Icc 0 (a + p.T)) ∧
            Fd ω 0 = 0 ∧ ContinuousOn (Fd ω) (Icc 0 (a + p.T)) ∧
            BoundedVariationOn (Fd ω) (Icc 0 (a + p.T)) ∧
            (eVariationOn (Fd ω) (Icc 0 (a + p.T))).toReal ≤ V ω ∧
            ∀ q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
              Fd ω r - Fd ω q = r2DriftInc (r26t3_coeff R)
                (wholeSpaceIndex p.d : ℝ) (a + p.T)
                (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) q r) ∧
          ∀ (Φ : Window p → ℝ), MemCb 5 Φ →
            ∃ WSW : fp81s21_RSBVWindow A.P (a + p.T)
              (fun ω τ => fderiv ℝ (initialHeat future a ha Φ τ)
                (HRS.MS.ProClosureS111.physicalWindowRestriction
                  (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
                  (T := p.T) (H := a + p.T) ha le_rfl (Yh ω τ)))
              (fun ω t => fp81s21_weightedDrift_windowCum
                (m := (wholeSpaceIndex p.d : ℝ)) ha le_rfl (r26t3_coeff R)
                (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) t),
            ∀ q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
              Integrable (fp81s21_rs_bv_variation_majorant
                (fun ω τ => fderiv ℝ (initialHeat future a ha Φ τ)
                  (HRS.MS.ProClosureS111.physicalWindowRestriction
                    (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
                    (T := p.T) (H := a + p.T) ha le_rfl (Yh ω τ)))
                (fun ω t => fp81s21_weightedDrift_windowCum
                  (m := (wholeSpaceIndex p.d : ℝ)) ha le_rfl (r26t3_coeff R)
                  (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) t) q r) A.P := by
  obtain ⟨δ0, hδ0, hδhalf, hmain⟩ := fp81s21_moving_drift_projection_removal p
  refine ⟨δ0, hδ0, hδhalf, ?_⟩
  intro δ hδ hδle R
  obtain ⟨future, hfuture, hrest⟩ := hmain δ hδ hδle R
  refine ⟨future, hfuture, ?_⟩
  intro a ha hH N hN A F
  obtain ⟨Yh, Fd, V, hYm, hFm, hVi, hgood, _⟩ := hrest a ha hH N hN A F
  refine ⟨Yh, Fd, V, hYm, hFm, hVi, hgood, ?_⟩
  intro Φ hΦ
  let H : ℝ := a + p.T
  let W := HRS.MS.ProClosureS111.physicalWindowRestriction
    (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
    (T := p.T) (H := H) ha le_rfl
  let Ψ : OscPath p.d (wholeSpaceIndex p.d : ℝ) H → ℝ := fun w => Φ (W w)
  have hΨ : MemCb 5 Ψ :=
    (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof W hΦ).1
  let Cfull : ℝ := cbNorm 5 Ψ
  let Cwin : ℝ := cbNorm 5 Φ
  let b : A.Ω → ℝ → (Euc p.d → ℝ) → ℝ := fun ω u f =>
    r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f
  let AH : A.Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) H →L[ℝ] ℝ :=
    fun ω τ => fderiv ℝ (r2HeatFn (future H) Ψ τ) (Yh ω τ)
  let AW : A.Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) p.T →L[ℝ] ℝ :=
    fun ω τ => fderiv ℝ (initialHeat future a ha Φ τ) (W (Yh ω τ))
  let Fw : A.Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) p.T :=
    fun ω t => fp81s21_weightedDrift_windowCum
      (m := (wholeSpaceIndex p.d : ℝ)) ha le_rfl (r26t3_coeff R) (b ω) t
  let Fsur : A.Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) p.T :=
    fun ω t => W (Fd ω t)
  have hprob : ∀ τ, IsProbabilityMeasure (future H τ) := hfuture.1 H
  have hprobW : ∀ τ, IsProbabilityMeasure (windowFuture future a ha τ) :=
    fun τ => fp81s21_windowFuture_isProbability future hfuture.1 a ha τ
  have hp := hfuture.2.2.2 H hH
  have hCfull : 0 ≤ Cfull := by
    exact S7PIL_cbNorm_nonneg hΨ 0
  have hCwin : 0 ≤ Cwin := by
    exact S7PIL_cbNorm_nonneg hΦ 0
  have hWnorm : ‖W‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [one_mul] using
      HRS.MS.ProClosureS111.physicalWindowRestriction_norm_le ha le_rfl x
  have hWlip : LipschitzWith 1 W :=
    ContinuousLinearMap.lipschitzWith_of_opNorm_le hWnorm
  have hpull : ∀ ω τ z, AH ω τ z = AW ω τ (W z) := by
    intro ω τ z
    dsimp [AH, AW, Ψ]
    have hder := fp81s21_initialHeat_pullback_iteratedFDeriv
      future hfuture.1 a ha Φ hΦ τ 1 (by norm_num) (Yh ω τ)
    have heval := congrArg (fun D => D ![z]) hder
    simpa [iteratedFDeriv_one_apply] using heval
  have hWL : W.comp
      (fp81s21_physicalWindowExtension (d := p.d)
        (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T) ha p.hT.le) =
      ContinuousLinearMap.id ℝ (OscPath p.d (wholeSpaceIndex p.d : ℝ) p.T) :=
    fp81s21_physicalWindowRestriction_comp_extension ha p.hT.le
  let L := fp81s21_physicalWindowExtension (d := p.d)
    (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T) ha p.hT.le
  have hAWpull : ∀ ω τ,
      AW ω τ = (AH ω τ).comp L := by
    intro ω τ
    ext z
    have hz := congrArg (fun G => G z) hWL
    change W (L z) = z at hz
    calc
      AW ω τ z = AW ω τ (W (L z)) := (congrArg (AW ω τ) hz).symm
      _ = AH ω τ (L z) := (hpull ω τ (L z)).symm
  have hAHe : ∀ᵐ ω ∂A.P, ContinuousOn (AH ω) (Icc (0 : ℝ) H) := by
    filter_upwards [hgood] with ω hg
    have hYc : ContinuousOn (Yh ω) (Icc (0 : ℝ) H) := hg.2.1
    have hreg := (hp.2.2.2.1 Ψ hΨ (Yh ω) hYc 1 (by norm_num)).1
    have hc := (continuousMultilinearCurryFin1 ℝ
      (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) ℝ).continuous.comp_continuousOn hreg
    change ContinuousOn (fun τ => continuousMultilinearCurryFin1 ℝ
      (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) ℝ
        (iteratedFDeriv ℝ 1 (r2HeatFn (future H) Ψ τ) (Yh ω τ)))
      (Icc (0 : ℝ) H) at hc
    simpa only [s102_curry_iter] using hc
  have hAWe : ∀ᵐ ω ∂A.P, ContinuousOn (AW ω) (Icc (0 : ℝ) H) := by
    filter_upwards [hAHe] with ω hω
    have hc := hω.clm_comp (continuousOn_const :
      ContinuousOn (fun _ : ℝ => L)
        (Icc (0 : ℝ) H))
    exact ContinuousOn.congr hc (fun τ _ => hAWpull ω τ)
  have hFwEq : ∀ᵐ ω ∂A.P, ∀ t ∈ Icc (0 : ℝ) H, Fw ω t = W (Fd ω t) := by
    filter_upwards [hgood] with ω hg
    rcases hg with ⟨_, _, hzero, _, _, _, hinc⟩
    intro t ht
    have hstart := hinc 0 t (by norm_num) ht.1 ht.2
    have hFd : Fd ω t = r2DriftInc (r26t3_coeff R)
        (wholeSpaceIndex p.d : ℝ) H (b ω) 0 t := by
      calc
        Fd ω t = Fd ω t - Fd ω 0 := by rw [hzero]; simp
        _ = r2DriftInc (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
            (b ω) 0 t := hstart
    change W (r2DriftInc (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
      H (b ω) 0 t) = W (Fd ω t)
    rw [← hFd]
  have hFwBV : ∀ᵐ ω ∂A.P, BoundedVariationOn (Fw ω) (Icc (0 : ℝ) H) := by
    filter_upwards [hgood, hFwEq] with ω hg heq
    rcases hg with ⟨_, _, _, _, hBV, _, _⟩
    have hsur : BoundedVariationOn (Fsur ω) (Icc (0 : ℝ) H) :=
      hWlip.comp_boundedVariationOn hBV
    have hvar : eVariationOn (Fw ω) (Icc (0 : ℝ) H) =
        eVariationOn (Fsur ω) (Icc (0 : ℝ) H) :=
      eVariationOn.congr (fun t ht => heq t ht)
    change eVariationOn (Fw ω) (Icc (0 : ℝ) H) ≠ ⊤
    rw [hvar]
    exact hsur
  have hFwCont : ∀ᵐ ω ∂A.P, ContinuousOn (Fw ω) (Icc (0 : ℝ) H) := by
    filter_upwards [hgood, hFwEq] with ω hg heq
    have hFdCont : ContinuousOn (Fd ω) (Icc (0 : ℝ) H) := hg.2.2.2.1
    have hc := W.continuous.comp_continuousOn hFdCont
    exact ContinuousOn.congr hc (fun t ht => heq t ht)
  have hAfullSection : ∀ τ, Measurable (fun ω => ‖AH ω τ‖) := by
    intro τ
    letI : IsProbabilityMeasure (future H τ) := hprob τ
    have hΨdiff : ContDiff ℝ 1 (r2HeatFn (future H) Ψ τ) :=
      ((s102_r2HeatFn_derivs (future H) τ hΨ).1).of_le (by norm_num)
    have hc := hΨdiff.continuous_fderiv (by norm_num)
    exact (hc.comp_stronglyMeasurable (hYm τ).stronglyMeasurable).norm.measurable
  let Mfull : A.Ω → ℝ := fun ω => Cfull * |V ω|
  have hMfull : Integrable Mfull A.P := by
    simpa [Mfull] using hVi.abs.const_mul Cfull
  have hfullMajorant : ∀ q r, 0 ≤ q → q < r → r ≤ H →
      Integrable (fp81s21_rs_bv_variation_majorant AH Fd q r) A.P := by
    intro q r hq hqr hr
    letI : Nonempty (Icc q r) := ⟨⟨q, le_rfl, hqr.le⟩⟩
    have hmeas := fp81s21_rs_bv_variation_majorant_aemeasurable
      A.P AH Fd q r hqr.le hAfullSection hFm (by
        filter_upwards [hAHe, hgood] with ω hA hg
        exact ⟨hA.norm.mono (Icc_subset_Icc hq hr),
          (show ContinuousOn (Fd ω) (Icc (0 : ℝ) H) from hg.2.2.2.1).mono
            (Icc_subset_Icc hq hr)⟩)
    have hbound : ∀ᵐ ω ∂A.P,
        fp81s21_rs_bv_variation_majorant AH Fd q r ω ≤ Cfull * V ω := by
      filter_upwards [hgood] with ω hg
      rcases hg with ⟨_, _, _, _, hBV, hvar, _⟩
      have hle := fp81s21_projected_heat_variation_majorant_le
        (future H) hprob (ContinuousLinearMap.id ℝ
          (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
        ContinuousLinearMap.norm_id_le
        Ψ hΨ Yh Fd ω (V ω) hBV hvar hq hqr.le hr
      simpa [AH, Cfull] using hle
    refine hMfull.mono' hmeas.aestronglyMeasurable ?_
    · filter_upwards [hbound] with ω hb
      have hsup : 0 ≤ ⨆ τ : Icc q r, ‖AH ω τ‖ := by
          have hbd : BddAbove (Set.range (fun τ : Icc q r => ‖AH ω τ‖)) := by
            refine ⟨Cfull, ?_⟩
            rintro _ ⟨τ, rfl⟩
            have hh := fp81s21_projected_heat_gradient_norm_le
              (future H) hprob (ContinuousLinearMap.id ℝ
                (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
                ContinuousLinearMap.norm_id_le
              Ψ hΨ τ (Yh ω τ)
            simpa [AH] using hh
          exact (norm_nonneg _).trans
            (le_ciSup hbd ⟨q, le_rfl, hqr.le⟩)
      have hnonneg : 0 ≤ fp81s21_rs_bv_variation_majorant AH Fd q r ω :=
        mul_nonneg hsup ENNReal.toReal_nonneg
      have hCabs : Cfull * V ω ≤ Cfull * |V ω| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hCfull
      have hb' : fp81s21_rs_bv_variation_majorant AH Fd q r ω ≤ Mfull ω := by
        simpa [Mfull] using hb.trans hCabs
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hb'
  let WSFull := fp81s21_rsbv_window_of_bv A.P H AH Fd
    (by
      intro q r hq hqr hr τ u v
      apply fp81s21_derivative_increment_measurable
        (fun τ => r2HeatFn (future H) Ψ τ) Yh Fd
        (fun τ => by
          letI : IsProbabilityMeasure (future H τ) := hprob τ
          exact ((s102_r2HeatFn_derivs (future H) τ hΨ).1).of_le (by norm_num))
        (fun τ => (hYm τ).stronglyMeasurable)
        (fun t => (hFm t).stronglyMeasurable) τ u v)
    (by
      intro q r hq hqr hr
      filter_upwards [hAHe, hgood] with ω hA hg
      exact ⟨hA.mono (Icc_subset_Icc hq hr),
        (show BoundedVariationOn (Fd ω) (Icc (0 : ℝ) H) from hg.2.2.2.2.1).mono
          (Icc_subset_Icc hq hr)⟩)
    (by intro q r hq hqr hr; exact hfullMajorant q r hq hqr hr)
  have hAwSection : ∀ τ, Measurable (fun ω => ‖AW ω τ‖) := by
    intro τ
    letI : IsProbabilityMeasure (windowFuture future a ha τ) := hprobW τ
    have hΦdiff : ContDiff ℝ 1 (initialHeat future a ha Φ τ) :=
      ((s102_r2HeatFn_derivs (windowFuture future a ha) τ hΦ).1).of_le (by norm_num)
    have hc := hΦdiff.continuous_fderiv (by norm_num)
    have hYmW : Measurable (fun ω => W (Yh ω τ)) :=
      W.continuous.measurable.comp (hYm τ)
    change Measurable (fun ω => ‖fderiv ℝ
      (r2HeatFn (windowFuture future a ha) Φ τ) (W (Yh ω τ))‖)
    exact (hc.comp_stronglyMeasurable hYmW.stronglyMeasurable).norm.measurable
  have hAwNorm : ∀ ω τ, ‖AW ω τ‖ ≤ Cwin := by
    intro ω τ
    have hh := fp81s21_projected_heat_gradient_norm_le
      (windowFuture future a ha) hprobW
      (ContinuousLinearMap.id ℝ (OscPath p.d (wholeSpaceIndex p.d : ℝ) p.T))
      ContinuousLinearMap.norm_id_le Φ hΦ τ (W (Yh ω τ))
    change ‖fderiv ℝ (r2HeatFn (windowFuture future a ha) Φ τ)
      (W (Yh ω τ))‖ ≤ cbNorm 5 Φ
    exact hh
  let Mwin : A.Ω → ℝ := fun ω => Cwin * |V ω|
  have hMwin : Integrable Mwin A.P := by
    simpa [Mwin] using hVi.abs.const_mul Cwin
  have hwinMajorant : ∀ q r, 0 ≤ q → q ≤ r → r ≤ H →
      Integrable (fp81s21_rs_bv_variation_majorant AW Fw q r) A.P := by
    intro q r hq hqr hr
    letI : Nonempty (Icc q r) := ⟨⟨q, le_rfl, hqr⟩⟩
    have hFsurSection : ∀ t, Measurable (fun ω => Fsur ω t) := by
      intro t
      exact W.continuous.measurable.comp (hFm t)
    have hmeasSur := fp81s21_rs_bv_variation_majorant_aemeasurable
      A.P AW Fsur q r hqr hAwSection hFsurSection (by
        filter_upwards [hAWe, hgood] with ω hA hg
        exact ⟨hA.norm.mono (Icc_subset_Icc hq hr),
          (W.continuous.comp_continuousOn
            (show ContinuousOn (Fd ω) (Icc (0 : ℝ) H) from hg.2.2.2.1)).mono
              (Icc_subset_Icc hq hr)⟩)
    have hmajCong : fp81s21_rs_bv_variation_majorant AW Fw q r =ᵐ[A.P]
        fp81s21_rs_bv_variation_majorant AW Fsur q r := by
      filter_upwards [hFwEq] with ω heq
      have hvar : eVariationOn (Fw ω) (Icc q r) =
          eVariationOn (Fsur ω) (Icc q r) :=
        eVariationOn.congr (fun t ht => heq t (Icc_subset_Icc hq hr ht))
      change (⨆ τ : Icc q r, ‖AW ω τ‖) *
          (eVariationOn (Fw ω) (Icc q r)).toReal =
        (⨆ τ : Icc q r, ‖AW ω τ‖) *
          (eVariationOn (Fsur ω) (Icc q r)).toReal
      rw [hvar]
    have hmeas := hmeasSur.congr hmajCong.symm
    have hbound : ∀ᵐ ω ∂A.P,
        fp81s21_rs_bv_variation_majorant AW Fw q r ω ≤ Cwin * V ω := by
      filter_upwards [hgood, hFwEq] with ω hg heq
      rcases hg with ⟨_, _, _, _, hBV, hvar, _⟩
      have hvarW : eVariationOn (Fsur ω) (Icc q r) ≤
          eVariationOn (Fd ω) (Icc q r) := by
        have hcomp := hWlip.lipschitzOnWith.comp_eVariationOn_le
          (mapsTo_univ (Fd ω) (Icc q r))
        have hEq : Fsur ω = W ∘ Fd ω := by
          funext t
          rfl
        rw [hEq]
        simpa using hcomp
      have hvarQ : eVariationOn (Fd ω) (Icc q r) ≤
          eVariationOn (Fd ω) (Icc (0 : ℝ) H) :=
        eVariationOn.mono (Fd ω) (Icc_subset_Icc hq hr)
      have hvarToReal :
          (eVariationOn (Fw ω) (Icc q r)).toReal ≤ V ω := by
        have hEqVar : eVariationOn (Fw ω) (Icc q r) =
            eVariationOn (Fsur ω) (Icc q r) :=
          eVariationOn.congr (fun t ht => heq t (Icc_subset_Icc hq hr ht))
        rw [hEqVar]
        exact (ENNReal.toReal_mono hBV (hvarW.trans hvarQ)).trans hvar
      have hsup : (⨆ τ : Icc q r, ‖AW ω τ‖) ≤ Cwin := by
        apply ciSup_le
        intro τ
        exact hAwNorm ω τ
      unfold fp81s21_rs_bv_variation_majorant
      calc
        _ ≤ Cwin * (eVariationOn (Fw ω) (Icc q r)).toReal :=
          mul_le_mul_of_nonneg_right hsup ENNReal.toReal_nonneg
        _ ≤ Cwin * V ω := mul_le_mul_of_nonneg_left hvarToReal hCwin
    refine hMwin.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [hbound] with ω hb
    have hsup : 0 ≤ ⨆ τ : Icc q r, ‖AW ω τ‖ := by
      have hbd : BddAbove (Set.range (fun τ : Icc q r => ‖AW ω τ‖)) := by
        refine ⟨Cwin, ?_⟩
        rintro _ ⟨τ, rfl⟩
        exact hAwNorm ω τ
      exact (norm_nonneg _).trans (le_ciSup hbd ⟨q, le_rfl, hqr⟩)
    have hnonneg : 0 ≤ fp81s21_rs_bv_variation_majorant AW Fw q r ω :=
      mul_nonneg hsup ENNReal.toReal_nonneg
    have hCabs : Cwin * V ω ≤ Cwin * |V ω| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hCwin
    have hb' : fp81s21_rs_bv_variation_majorant AW Fw q r ω ≤ Mwin ω := by
      simpa [Mwin] using hb.trans hCabs
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hb'
  have hwindowRS : ∀ q r, 0 ≤ q → q ≤ r → r ≤ H →
      ∀ᵐ ω ∂A.P, fp81s21_IsRSOn q r
        (fun τ u v => AW ω τ (Fw ω v - Fw ω u)) (WSFull.value q r ω) := by
    intro q r hq hqr hr
    by_cases hlt : q < r
    · filter_upwards [WSFull.value_isRS q r hq hqr hr, hgood] with ω hRS hg
      rcases hg with ⟨_, _, hzero, _, _, _, hinc⟩
      have hFwAt : ∀ t, t ∈ Icc (0 : ℝ) H → Fw ω t = W (Fd ω t) := by
        intro t ht
        have hstart := hinc 0 t (by norm_num) ht.1 ht.2
        have hFdT : Fd ω t = r2DriftInc (r26t3_coeff R)
            (wholeSpaceIndex p.d : ℝ) H (b ω) 0 t := by
          calc
            Fd ω t = Fd ω t - Fd ω 0 := by rw [hzero]; simp
            _ = r2DriftInc (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
                (b ω) 0 t := hstart
        change W (r2DriftInc (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
          H (b ω) 0 t) = W (Fd ω t)
        rw [← hFdT]
      have hsource : IsR2RS (r - q)
          (fun t u v => AH ω (q + t) (Fd ω (q + v) - Fd ω (q + u)))
          (WSFull.value q r ω) := by
        simpa only [fp81s21_IsRSOn] using hRS
      have htarget : IsR2RS (r - q)
          (fun t u v => AW ω (q + t) (Fw ω (q + v) - Fw ω (q + u)))
          (WSFull.value q r ω) := by
        refine (s102_isR2RS_iff _ _ _).2
          (HRS.MC.Sec7.S7PIG6.S7PIG6_IsRS_congr
            ((s102_isR2RS_iff _ _ _).1 hsource) ?_)
        intro t u v ht hu huv hv
        have huH : q + u ∈ Icc (0 : ℝ) H := by
          constructor <;> linarith [hq, hu, huv, hv, hr]
        have hvH : q + v ∈ Icc (0 : ℝ) H := by
          constructor <;> linarith [hq, hu, huv, hv, hr]
        have hincW : Fw ω (q + v) - Fw ω (q + u) =
            W (Fd ω (q + v) - Fd ω (q + u)) := by
          rw [hFwAt (q + v) hvH, hFwAt (q + u) huH]
          simp
        rw [hincW]
        exact hpull ω (q + t) _
      simpa only [fp81s21_IsRSOn] using htarget
    · have heq : q = r := le_antisymm hqr (le_of_not_gt hlt)
      subst r
      filter_upwards [WSFull.value_zero q hq hr] with ω hzero
      rw [hzero]
      exact fp81s21_isRSOn_zero q (fun τ u v => AW ω τ (Fw ω v - Fw ω u))
  have WSW : fp81s21_RSBVWindow A.P H AW Fw := by
    refine {
      value := WSFull.value
      majorant := fun q r => fp81s21_rs_bv_variation_majorant AW Fw q r
      value_isRS := ?_
      value_aemeasurable := WSFull.value_aemeasurable
      value_integrable := WSFull.value_integrable
      majorant_integrable := ?_
      value_bound := ?_
      value_zero := WSFull.value_zero
      value_add := WSFull.value_add
    }
    · exact hwindowRS
    · intro q r hq hqr hr
      exact hwinMajorant q r hq hqr hr
    · intro q r hq hqr hr
      by_cases hlt : q < r
      · have hgoodWindow : ∀ᵐ ω ∂A.P,
            ContinuousOn (AW ω) (Icc q r) ∧
              BoundedVariationOn (Fw ω) (Icc q r) := by
          filter_upwards [hAWe, hFwBV] with ω hA hF
          exact ⟨hA.mono (Icc_subset_Icc hq hr),
            hF.mono (Icc_subset_Icc hq hr)⟩
        filter_upwards [hgoodWindow, hwindowRS q r hq hqr hr] with ω hg hRS
        exact fp81s21_rsOn_bv_bound hlt (Fw ω) (AW ω) hg.2 hg.1 hRS
      · have heq : q = r := le_antisymm hqr (le_of_not_gt hlt)
        subst r
        filter_upwards [WSFull.value_zero q hq hr] with ω hz
        rw [hz]
        have hnonneg : 0 ≤ fp81s21_rs_bv_variation_majorant AW Fw q q ω := by
          letI : Nonempty (Icc q q) := ⟨⟨q, le_rfl, le_rfl⟩⟩
          unfold fp81s21_rs_bv_variation_majorant
          apply mul_nonneg _ ENNReal.toReal_nonneg
          have hbd : BddAbove (Set.range (fun τ : Icc q q => ‖AW ω τ‖)) := by
            refine ⟨Cwin, ?_⟩
            rintro _ ⟨τ, rfl⟩
            exact hAwNorm ω τ
          exact (norm_nonneg _).trans (le_ciSup hbd ⟨q, le_rfl, le_rfl⟩)
        simpa using hnonneg
  exact ⟨WSW, hwinMajorant⟩

#print axioms HRS.Fp81.S21.fp81s21_moving_window_rsbv

end HRS.Fp81.S21

end
