import HRS.MS.Fp81S21WindowRSShared
import HRS.MS.Fp81S21HeatTerminal
import HRS.MS.Fp81S21MovingG6c
import HRS.MS.Fp81S21WindowDriftId4
import HRS.MS.Fp81S21WindowCovRSId2
import HRS.MS.Fp81S21PhysEndpoints
import HRS.MS.Fp81S21PhysEndpoints7
import HRS.MS.Fp81S21MovingHeat4

/-! Assemble the full-horizon heat identity, the physical endpoints, and the
same-data window Riemann--Stieltjes correction. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp

theorem fp81s21_moving_path_interpolation (p : Parameters) :
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
                  ∃ WP : fp81s21_WindowRS A.P H Ad Fdw Aj Fjw,
                    let corrN : ℝ → ℝ → ℝ := fp81s21_WindowRS_corr WP
                    Real.sqrt N *
                      ((∫ ω, Φ (r26t3_zetapath A a ω) ∂A.P) -
                        ∫ X, initialHeat future a ha Φ 0 (initialWindow R N a X)
                          ∂(r26t3_Q R N)) = corrN 0 H := by
  classical
  obtain ⟨δA, hδA, hδAh, hA⟩ := fp81s21_moving_window_rs_close p
  obtain ⟨δI, hδI, hδIh, hInputs⟩ := fp81s21_moving_inputs_all p
  obtain ⟨δE, hδE, hδEh, hEndpoint⟩ :=
    fp81s21_physical_initial_prediction_endpoint_both p
      ((lt_or_eq_of_le p.hγ).imp id Eq.symm)
  let δ0 := min δA (min δI δE)
  refine ⟨δ0, lt_min hδA (lt_min hδI hδE),
    (min_le_left _ _).trans hδAh, ?_⟩
  intro δ hδ hδle R
  have hδA' : δ ≤ δA := hδle.trans (min_le_left _ _)
  have hδI' : δ ≤ δI :=
    hδle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδE' : δ ≤ δE :=
    hδle.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨future, hfuture, hconstants⟩ := hA δ hδ hδA' R
  obtain ⟨Cmix, cdec, K, hmain⟩ := hconstants
  refine ⟨future, hfuture, Cmix, cdec, K, ?_⟩
  intro a ha N hN A F
  have hδh : δ ≤ 1 / 2 := hδA'.trans hδAh
  have hH : 0 < a + p.T := by linarith [ha, p.hT]
  obtain ⟨c, hstd, hphysAll⟩ := hInputs δ hδ hδI' R a ha
  have hphys : Fp81MovingPhysicalInputs R hN A (a + p.T) := hphysAll N hN A
  have hlin : S102Lin (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
      (a + p.T) := fp81s21_S102Lin p R (a + p.T)
  obtain ⟨D, hcov, hphi⟩ := hmain a ha N hN A F
  refine ⟨D, hcov, ?_⟩
  intro Φ hΦ
  let H : ℝ := a + p.T
  let W : OscPath p.d (wholeSpaceIndex p.d : ℝ) H →L[ℝ] Window p :=
    HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
      (T := p.T) (H := H) ha le_rfl
  let Ad : A.Ω → ℝ → Window p →L[ℝ] ℝ := fun ω τ =>
    fderiv ℝ (initialHeat future a ha Φ τ) (W (D.Yh ω τ))
  let Fdw : A.Ω → ℝ → Window p := fun ω t =>
    fp81s21_weightedDrift_windowCum
      (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T) (H := H)
      (a := a) ha le_rfl (r26t3_coeff R)
      (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) t
  let Aj : A.Ω → ℝ → projTensor (Window p) 2 →L[ℝ] ℝ := fun ω τ =>
    fp81s21_covariance_pairingCLM
      (iteratedFDeriv ℝ 2 (initialHeat future a ha Φ τ) (W (D.Yh ω τ)))
  let Fjw : A.Ω → ℝ → projTensor (Window p) 2 := fun ω t =>
    fp81s21_windowCovarianceMap p a ha (D.Fj ω t)
  let Ψ : OscPath p.d (wholeSpaceIndex p.d : ℝ) H → ℝ := fun w => Φ (W w)
  letI : CompleteSpace (projTensor (Window p) 2) :=
    HRS.Fp81.V01.fp81v01_projTensorComplete (Window p) 2
  obtain ⟨WS, hWP⟩ := hphi Φ hΦ
  rcases hWP with ⟨WP⟩
  have hfull := fp81s21_moving_heat_ito_full_horizon_expectation_identity_of_data
    p R hδ hδh a ha hH hN A F hstd hlin hphys future hfuture D Φ hΦ WS
  obtain ⟨dval, jval, hdInt, hjInt, hdSpec, hjSpec, hdExpect, hjExpect,
    hidentity⟩ := hfull
  have hdRS := hdSpec.mono (fun _ hω => hω.1)
  have hdPointLimit := hdSpec.mono (fun _ hω => hω.2)
  have hjRS := hjSpec.mono (fun _ hω => hω.1)
  have hjPointLimit := hjSpec.mono (fun _ hω => hω.2)
  have hFd : ∀ᵐ ω ∂A.P, D.Fd ω 0 = 0 ∧
      ∀ q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
        D.Fd ω r - D.Fd ω q = r2DriftInc (r26t3_coeff R)
          (wholeSpaceIndex p.d : ℝ) (a + p.T)
          (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) q r := by
    filter_upwards [D.Fd_good] with ω hω
    exact ⟨hω.1, fun q r hq hqr hr => hω.2.2.2.2 q r hq hqr hr⟩
  have hdValue := fp81s21_unprojected_isR2RS_window_drift_value
    p A.P a ha hH future hfuture.1 Φ hΦ (r26t3_coeff R)
    (fun ω u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f)
    D.Yh D.Fd hFd WP.drift dval hdRS
  have hJ : ∀ᵐ ω ∂A.P, ∀ q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
      IsR2JValue (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) (a + p.T)
        (fp81s21_movingRawEtaField p R A ω) (Ioc q r)
        (((D.Fj ω r - D.Fj ω q :
          projTensor (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2) :
          TensorDual (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2)) := by
    filter_upwards [D.Fj_good] with ω hω
    exact hω.1
  have hjRawRS : ∀ᵐ ω ∂A.P,
      IsR2RS (a + p.T)
        (fun τ u v => r2JPair (r26t3_coeff R)
          (wholeSpaceIndex p.d : ℝ) (a + p.T)
          (fp81s21_movingRawEtaField p R A ω) (Ioc u v)
          (iteratedFDeriv ℝ 2 (r2HeatFn (future (a + p.T)) Ψ τ)
            (D.Yh ω τ))) (jval ω) := by
    filter_upwards [hjRS, hJ] with ω hω hJω
    refine (HRS.MS.R2Interp.s102_isR2RS_iff _ _ _).2
      (HRS.MC.Sec7.S7PIG6.S7PIG6_IsRS_congr
        ((HRS.MS.R2Interp.s102_isR2RS_iff _ _ _).1 hω) ?_)
    intro τ u v hτ hu huv hv
    let Jc : ℝ → TensorDual
        (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2 :=
      fun t => D.Fj ω t
    have hJc : ∀ u v, 0 ≤ u → u ≤ v → v ≤ a + p.T →
        IsR2JValue (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
          (a + p.T) (fp81s21_movingRawEtaField p R A ω) (Ioc u v)
          (Jc v - Jc u) := by
      intro u v hu huv hv
      simpa [Jc] using hJω u v hu huv hv
    rw [HRS.MS.R2Interp.s102_jPair_eq (r26t3_coeff R) hH
      (fp81s21_movingRawEtaField p R A ω) Jc hJc u v hu huv hv _]
    simp only [fp81s21_covariance_pairingCLM, Jc, Ψ, W]
    all_goals first | rfl | simp
  have hjValue := fp81s21_unprojected_isR2RS_window_covariance_value
    p A.P a ha future hfuture.1 Φ hΦ (r26t3_coeff R)
    (fp81s21_movingRawEtaField p R A) D.Yh D.Fj hJ WP.covariance jval hjRawRS
  have hcorr : -(∫ ω, dval ω ∂A.P) + (1 / 2 : ℝ) *
      (∫ ω, jval ω ∂A.P) = fp81s21_WindowRS_corr WP 0 (a + p.T) := by
    unfold fp81s21_WindowRS_corr
    rw [integral_congr_ae hdValue, integral_congr_ae hjValue]
  have hΨ : MemCb 5 Ψ :=
    (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof W hΦ).1
  have hterminal :
      (∫ ω, r2HeatFn (future (a + p.T)) Ψ (a + p.T)
        (s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) (a + p.T)
          A.P A.X ω (a + p.T)) ∂A.P) =
      ∫ ω, Φ (r26t3_zetapath A a ω) ∂A.P := by
    calc
      _ = ∫ ω, Φ (W (s102_Y (r26t3_coeff R)
          (wholeSpaceIndex p.d : ℝ) (a + p.T) A.P A.X ω (a + p.T))) ∂A.P := by
        apply integral_congr_ae
        filter_upwards [] with ω
        exact fp81s21_heat_terminal_of_future (r26t3_coeff R) hH
          (future (a + p.T))
          (hfuture.2.1 (a + p.T) hH) Ψ hΨ
          (s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
            (a + p.T) A.P A.X ω (a + p.T))
      _ = ∫ ω, Φ (r26t3_zetapath A a ω) ∂A.P :=
        fp81s21_physical_terminal_expectation p R hN A a ha Φ
  have hinitialPath :
      (∫ ω, r2HeatFn (future (a + p.T)) Ψ 0
        (s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) (a + p.T)
          A.P A.X ω 0) ∂A.P) =
      ∫ X, initialHeat future a ha Φ 0
        (initialWindow R N a X) ∂(r26t3_Q R N) := by
    calc
      _ = ∫ ω, initialHeat future a ha Φ 0
          (W (s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
            (a + p.T) A.P A.X ω 0)) ∂A.P := by
        apply integral_congr_ae
        filter_upwards [] with ω
        simpa [W, Ψ] using
          (fp81s21_initialHeat_pullback future a ha Φ hΦ 0
            (s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
              (a + p.T) A.P A.X ω 0)).symm
      _ = ∫ X, initialHeat future a ha Φ 0
          (initialWindow R N a X) ∂(r26t3_Q R N) := by
        have hphysical := hEndpoint δ hδ hδE' R future hfuture.1
          a ha N hN A Φ hΦ
        simpa [W, H] using hphysical
  have hLHS :
      Real.sqrt N *
        ((∫ ω, Φ (r26t3_zetapath A a ω) ∂A.P) -
          ∫ X, initialHeat future a ha Φ 0 (initialWindow R N a X)
            ∂(r26t3_Q R N)) =
      Real.sqrt N *
        ((∫ ω, r2HeatFn (future (a + p.T)) Ψ (a + p.T)
            (s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
              (a + p.T) A.P A.X ω (a + p.T)) ∂A.P) -
          ∫ ω, r2HeatFn (future (a + p.T)) Ψ 0
            (s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
              (a + p.T) A.P A.X ω 0) ∂A.P) := by
    rw [← hterminal, ← hinitialPath]
  refine ⟨WP, ?_⟩
  change Real.sqrt N *
      ((∫ ω, Φ (r26t3_zetapath A a ω) ∂A.P) -
        ∫ X, initialHeat future a ha Φ 0 (initialWindow R N a X)
          ∂(r26t3_Q R N)) = fp81s21_WindowRS_corr WP 0 H
  calc
    _ = Real.sqrt N *
        ((∫ ω, r2HeatFn (future (a + p.T)) Ψ (a + p.T)
            (s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
              (a + p.T) A.P A.X ω (a + p.T)) ∂A.P) -
          ∫ ω, r2HeatFn (future (a + p.T)) Ψ 0
            (s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
              (a + p.T) A.P A.X ω 0) ∂A.P) := hLHS
    _ = -(∫ ω, dval ω ∂A.P) + (1 / 2 : ℝ) *
        (∫ ω, jval ω ∂A.P) := by
      simpa [H, Ψ] using hidentity
    _ = fp81s21_WindowRS_corr WP 0 H := by
      simpa [H] using hcorr

#print axioms HRS.Fp81.S21.fp81s21_moving_path_interpolation
end HRS.Fp81.S21
end
