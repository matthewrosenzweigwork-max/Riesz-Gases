import HRS.MS.Fp81S21SharedRS2
import HRS.MS.Fp81S21FinProj3

/-! Adapt the selected shared finite-projection witnesses to the consumer data
record, retaining the same future, cumulatives, and level families. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp

theorem fp81s21_moving_shared_rs_data (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ future : (H : ℝ) → ℝ →
            Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H),
          fp81s21_moving_heat_full_clause p R future ∧
          ∀ (a : ℝ) (ha : 0 ≤ a) (hH : 0 < a + p.T)
            (N : ℕ) (hN : 2 ≤ N) (A : Particle R N)
            (F : FilteredParticle A),
            ∃ D : fp81s21_finproj_shared_data p R a A F,
              ∀ Φ : Window p → ℝ, MemCb 5 Φ →
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
                  ∀ L q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
                    Real.sqrt N *
                        ((∫ ω, fp81s21_moving_heat_ito_endpoint
                            p R A a ha hH future L Φ r ω ∂A.P) -
                          (∫ ω, fp81s21_moving_heat_ito_endpoint
                            p R A a ha hH future L Φ q ω ∂A.P)) =
                      fp81s21_WindowRS_corr (WS L) q r := by
  classical
  obtain ⟨δs, hδs, hsHalf, hshared⟩ := fp81s21_moving_shared_rs p
  obtain ⟨δi, hδi, hiHalf, hinputs⟩ := fp81s21_moving_inputs_all p
  let δ0 := min δs δi
  refine ⟨δ0, lt_min hδs hδi, (min_le_left _ _).trans hsHalf, ?_⟩
  intro δ hδ hδle R
  have hδs' : δ ≤ δs := hδle.trans (min_le_left _ _)
  have hδi' : δ ≤ δi := hδle.trans (min_le_right _ _)
  obtain ⟨future, hfuture, hmain⟩ := hshared δ hδ hδs' R
  refine ⟨future, hfuture, ?_⟩
  intro a ha hH N hN A F
  obtain ⟨c, hstd, hphysAll⟩ := hinputs δ hδ hδi' R a ha
  have hphys : Fp81MovingPhysicalInputs R hN A (a + p.T) := by
    exact hphysAll N hN A
  have hlin : S102Lin (r26t3_coeff R)
      (wholeSpaceIndex p.d : ℝ) (a + p.T) :=
    fp81s21_S102Lin p R (a + p.T)
  have hr0 : (p.d : ℝ) / 2 + 2 < (2 * p.d + 8 : ℕ) := by
    have hd0 : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
    norm_num [Nat.cast_add, Nat.cast_mul]
    linarith
  have hδh : δ ≤ 1 / 2 := hδs'.trans hsHalf
  obtain ⟨Yh, Fd, Fj, V, hcore, hlevels⟩ := hmain a ha N hN A F
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
            (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2) : TensorDual
            (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2))) ∧
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
  refine ⟨D, ?_⟩
  intro Φ hΦ
  obtain ⟨WS0, hpayload⟩ := hlevels Φ hΦ
  let WS : fp81s21_finproj_shared_RS_family
      p R a ha hH A future F Φ D := WS0
  dsimp [fp81s21_moving_shared_rs_level_payload] at hpayload
  obtain ⟨dval, MD, MJ, WSDW, hdInt, hMDInt, hMJInt,
    hDmajInt, hDOn0, hDval0, hDmajBound, hJmajInt, hJOn0, hJval0,
    hJmajBound, hDlimit, hDexpect, hWSDWmajor, hDident⟩ := hpayload
  have hDOn : ∀ L q r, 0 ≤ q → q ≤ r → r ≤ a + p.T → ∀ᵐ ω ∂A.P,
      IntegrableOn (fp81s21_moving_drift_cyl_sum p R A F a ha hH L Φ ω)
        (Ioc q r) := by
    simpa [WS, D, fp81s21_finproj_shared_RS_family] using hDOn0
  have hJOn : ∀ L q r, 0 ≤ q → q ≤ r → r ≤ a + p.T → ∀ᵐ ω ∂A.P,
      IntegrableOn (fp81s21_moving_covariance_cyl_sum p R A F a ha hH L Φ ω)
        (Ioc q r) := by
    simpa [WS, D, fp81s21_finproj_shared_RS_family] using hJOn0
  have hDval : ∀ L q r, 0 ≤ q → q ≤ r → r ≤ a + p.T → ∀ᵐ ω ∂A.P,
      (WS L).drift.value q r ω =
        ∫ u in Ioc q r, fp81s21_moving_drift_cyl_sum p R A F a ha hH L Φ ω u := by
    simpa [WS, D, fp81s21_finproj_shared_RS_family] using hDval0
  have hJval : ∀ L q r, 0 ≤ q → q ≤ r → r ≤ a + p.T → ∀ᵐ ω ∂A.P,
      (WS L).covariance.value q r ω =
        ∫ u in Ioc q r, fp81s21_moving_covariance_cyl_sum p R A F a ha hH L Φ ω u := by
    simpa [WS, D, fp81s21_finproj_shared_RS_family] using hJval0
  have hidentity := fp81s21_moving_heat_ito_finite_projection_expectation_identity
    p R hδ hδh a ha hH hN A F hstd hlin hr0 hphys future hfuture Φ hΦ
    D.Yh D.Fd D.Fj D.Yh_measurable D.Yh_ae WS hDOn hJOn hDval hJval
  exact ⟨WS, hDOn, hJOn, hDval, hJval, hidentity⟩

#print axioms HRS.Fp81.S21.fp81s21_moving_shared_rs_data
end HRS.Fp81.S21
end
