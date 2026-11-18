import HRS.MS.Fp81S21SharedRS2
import HRS.MS.Fp81S21SharedRSData
import HRS.MS.Fp81S21WindowCovClose

/-! Assemble the selected shared drift witness and physical-window covariance
witnesses on the same finite-projection data. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MC.E213O
open HRS.MC.Sec7.S7PIL

theorem fp81s21_moving_window_rs_close (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ future : (H : ℝ) → ℝ →
            Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H),
          fp81s21_moving_heat_full_clause p R future ∧
          ∃ Cmix cdec : ℝ, ∃ K : ℝ → ℝ,
            ∀ (a : ℝ) (ha : 0 ≤ a) (N : ℕ) (hN : 2 ≤ N)
              (A : Particle R N) (F : FilteredParticle A),
              ∃ D : fp81s21_finproj_shared_data p R a A F,
                fp81s21_shared_physical_window_covariance_identification
                  p R a ha A Cmix cdec K D.Fj ∧
                ∀ (Φ : Window p → ℝ) (hΦ : MemCb 5 Φ),
                  let H := a + p.T
                  let W := HRS.MS.ProClosureS111.physicalWindowRestriction
                    (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
                    (T := p.T) (H := H) ha le_rfl
                  let Ad := fun ω τ => fderiv ℝ
                    (initialHeat future a ha Φ τ) (W (D.Yh ω τ))
                  let Fdw := fun ω t => fp81s21_weightedDrift_windowCum
                    (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T) (H := H)
                    (a := a) ha le_rfl (r26t3_coeff R)
                    (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) t
                  let Aj := fun ω τ => fp81s21_covariance_pairingCLM
                    (iteratedFDeriv ℝ 2
                      (initialHeat future a ha Φ τ) (W (D.Yh ω τ)))
                  let Fjw := fun ω t => fp81s21_windowCovarianceMap p a ha
                    (D.Fj ω t)
                  letI : CompleteSpace (projTensor (Window p) 2) :=
                    HRS.Fp81.V01.fp81v01_projTensorComplete (Window p) 2
                  ∃ WS : fp81s21_finproj_shared_RS_family
                      p R a ha (by linarith [p.hT]) A future F Φ D,
                    Nonempty (fp81s21_WindowRS A.P H Ad Fdw Aj Fjw) := by
  classical
  obtain ⟨δs, hδs, hsHalf, hshared⟩ := fp81s21_moving_shared_rs p
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
    obtain ⟨Cmix, cdec, K, hselect⟩ := hphysical δ hδ hδc' R
    refine ⟨future, hfuture, Cmix, cdec, K, ?_⟩
    intro a ha N hN A F
    have hH : 0 < a + p.T := by linarith [ha, p.hT]
    obtain ⟨c, hstd, hphysAll⟩ := hinputs δ hδ hδi' R a ha
    have hphys : Fp81MovingPhysicalInputs R hN A (a + p.T) :=
      hphysAll N hN A
    have hlin : S102Lin (r26t3_coeff R)
        (wholeSpaceIndex p.d : ℝ) (a + p.T) :=
      fp81s21_S102Lin p R (a + p.T)
    have hδh : δ ≤ 1 / 2 := hδs'.trans hsHalf
    obtain ⟨Yh, Fd, Fj, V, hcore, hlevels⟩ :=
      hmain a ha N hN A F
    rcases hcore with ⟨hYm, hDm, hJm, hVi, hJzero, hgood⟩
    have hDgood : ∀ᵐ ω ∂A.P,
        Fd ω 0 = 0 ∧ ContinuousOn (Fd ω) (Icc 0 (a + p.T)) ∧
        BoundedVariationOn (Fd ω) (Icc 0 (a + p.T)) ∧
        (eVariationOn (Fd ω) (Icc 0 (a + p.T))).toReal ≤ V ω ∧
        ∀ q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
          Fd ω r - Fd ω q = r2DriftInc (r26t3_coeff R)
            (wholeSpaceIndex p.d : ℝ) (a + p.T)
            (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) q r := by
      filter_upwards [hgood] with ω hg
      rcases hg with ⟨_, _, hDzero, hDc, hDBV, hDvar, hDinc, _, _, _, _⟩
      exact ⟨hDzero, hDc, hDBV, hDvar, hDinc⟩
    have hJgood : ∀ᵐ ω ∂A.P,
        (∀ q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
          IsR2JValue (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) (a + p.T)
            (fp81s21_movingRawEtaField p R A ω) (Ioc q r)
            (((Fj ω r - Fj ω q : projTensor
                (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2) :
              TensorDual (OscPath p.d (wholeSpaceIndex p.d : ℝ)
                (a + p.T)) 2))) ∧
        ContinuousOn (Fj ω) (Icc 0 (a + p.T)) ∧
        BoundedVariationOn (Fj ω) (Icc 0 (a + p.T)) ∧
        (eVariationOn (Fj ω) (Icc 0 (a + p.T))).toReal ≤ V ω := by
      filter_upwards [hgood] with ω hg
      rcases hg with ⟨_, _, _, _, _, _, _, hJinc, hJc, hJBV, hJvar⟩
      exact ⟨hJinc, hJc, hJBV, hJvar⟩
    let D : fp81s21_finproj_shared_data p R a A F := {
      Yh := Yh
      Yh_measurable := hYm
      Yh_ae := by
        filter_upwards [hgood] with ω hg
        exact hg.1
      Yh_continuous := by
        filter_upwards [hgood] with ω hg
        exact hg.2.1
      Fd := Fd
      Fd_measurable := hDm
      Vd := V
      Vd_integrable := hVi
      Fd_good := hDgood
      Fj := Fj
      Fj_measurable := hJm
      Vj := V
      Vj_integrable := hVi
      Fj_zero := hJzero
      Fj_good := hJgood }
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
           AEMeasurable (fun v => dualNormE (2 * p.d + 8) P
             ((z + z) ω v)) (volume.restrict (Icc (0 : ℝ) (a + p.T))) ∧
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
    obtain ⟨WS0, hpayload⟩ := hlevels Φ hΦ
    let WS : fp81s21_finproj_shared_RS_family
        p R a ha hH A future F Φ D := WS0
    dsimp [fp81s21_moving_shared_rs_level_payload] at hpayload
    obtain ⟨dval, MD, MJ, WSDW, hdInt, hMDInt, hMJInt,
      hDmajInt, hDOn0, hDval0, hDmajBound, hJmajInt, hJOn0,
      hJval0, hJmajBound, hDlimit, hDexpect, hWSDWmajor, hDident⟩ := hpayload
    let W := HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
      (T := p.T) (H := a + p.T) ha le_rfl
    let Fw : A.Ω → ℝ → projTensor (Window p) 2 :=
      fun ω t => fp81s21_windowCovarianceMap p a ha (D.Fj ω t)
    let AjW : A.Ω → ℝ → projTensor (Window p) 2 →L[ℝ] ℝ :=
      fun ω τ => fp81s21_covariance_pairingCLM
        (iteratedFDeriv ℝ 2 (initialHeat future a ha Φ τ) (W (D.Yh ω τ)))
    have hJc : ∀ᵐ ω ∂A.P,
        ContinuousOn (D.Fj ω) (Icc 0 (a + p.T)) := by
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
                    (r2HeatFn (future (a + p.T))
                      (fun w => Φ (W w)) τ) (D.Yh ω τ))) (jval ω)) →
          jval =ᵐ[A.P] WSW.value q r := by
      intro q r hq hqr hr jval hjval
      exact fp81s21_unprojected_isRSOn_window_covariance_value
        p A.P a ha future hfuture.1 Φ hΦ (r26t3_coeff R)
        (fp81s21_movingRawEtaField p R A) D.Yh D.Fj hJraw WSW
        q r hq hqr hr jval hjval
    let WP : fp81s21_WindowRS A.P (a + p.T)
        (fun ω τ => fderiv ℝ (initialHeat future a ha Φ τ)
          (W (D.Yh ω τ)))
        (fun ω t => fp81s21_weightedDrift_windowCum
          (m := (wholeSpaceIndex p.d : ℝ)) ha le_rfl (r26t3_coeff R)
          (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) t)
        AjW Fw := ⟨hH.le, WSDW, WSW⟩
    refine ⟨WS, ?_⟩
    exact ⟨WP⟩

#print axioms HRS.Fp81.S21.fp81s21_moving_window_rs_close
end HRS.Fp81.S21
end
