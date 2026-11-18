import HRS.MS.Fp81S21MovingG6b
import HRS.MS.Fp81S21DriftProjRemoval
import HRS.MS.Fp81S21CovProjRemoval

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.CovMeas

/-- Full-horizon expected Itô identity after removal of the heat projection,
with limits associated to the supplied shared cumulative paths and RS windows. -/
theorem fp81s21_moving_heat_ito_full_horizon_expectation_identity_of_data
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (a : ℝ) (ha : 0 ≤ a) (hH : 0 < a + p.T)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
    {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
      (a + p.T) (2 * p.d + 8) c hH)
    (hlin : S102Lin (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) (a + p.T))
    (hphys : Fp81MovingPhysicalInputs R hN A (a + p.T))
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hfuture : fp81s21_moving_heat_full_clause p R future)
    (D : fp81s21_finproj_shared_data p R a A F)
    (Φ : Window p → ℝ) (hΦ : MemCb 5 Φ)
    (WS : fp81s21_finproj_shared_RS_family p R a ha hH A future F Φ D) :
    let H := a + p.T
    let W := HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T) (H := H) ha le_rfl
    let Ψ := fun w => Φ (W w)
    ∃ dval jval : A.Ω → ℝ,
      Integrable dval A.P ∧ Integrable jval A.P ∧
      (∀ᵐ ω ∂A.P, IsR2RS H (fun t q r =>
        fderiv ℝ (r2HeatFn (future H) Ψ t) (D.Yh ω t)
          (r2DriftInc (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
            (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) q r)) (dval ω) ∧
        Tendsto (fun L => (WS L).drift.value 0 H ω) atTop (𝓝 (dval ω))) ∧
      (∀ᵐ ω ∂A.P, IsR2RS H (fun t q r => fp81s21_covariance_pairingCLM
        (iteratedFDeriv ℝ 2 (r2HeatFn (future H) Ψ t) (D.Yh ω t))
        (D.Fj ω r - D.Fj ω q)) (jval ω) ∧
        Tendsto (fun L => (WS L).covariance.value 0 H ω) atTop (𝓝 (jval ω))) ∧
      Tendsto (fun L => ∫ ω, (WS L).drift.value 0 H ω ∂A.P) atTop (𝓝 (∫ ω, dval ω ∂A.P)) ∧
      Tendsto (fun L => ∫ ω, (WS L).covariance.value 0 H ω ∂A.P) atTop (𝓝 (∫ ω, jval ω ∂A.P)) ∧
      Real.sqrt N * ((∫ ω, r2HeatFn (future H) Ψ H
        (s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H A.P A.X ω H) ∂A.P) -
        (∫ ω, r2HeatFn (future H) Ψ 0
        (s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H A.P A.X ω 0) ∂A.P)) =
          -(∫ ω, dval ω ∂A.P) + (1 / 2 : ℝ) * (∫ ω, jval ω ∂A.P) := by
  classical
  let H : ℝ := a + p.T
  let B := OscPath p.d (wholeSpaceIndex p.d : ℝ) H
  letI : CompleteSpace (projTensor B 2) := HRS.Fp81.V01.fp81v01_projTensorComplete B 2
  let W : B →L[ℝ] Window p := HRS.MS.ProClosureS111.physicalWindowRestriction
    (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T) (H := H) ha le_rfl
  let Ψ : B → ℝ := fun w => Φ (W w)
  have hΨ : MemCb 5 Ψ := (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof W hΦ).1
  have hr0 : (p.d : ℝ) / 2 + 2 < (2 * p.d + 8 : ℕ) := by
    have hd0 : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
    norm_num [Nat.cast_add, Nat.cast_mul]
    linarith
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    have hd0 : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
    linarith
  obtain ⟨Mb, hMb, -⟩ := fp81s21_moving_M1 p R hH hN A hstd hr0 hphys
  have hg : ∀ᵐ ω ∂A.P, S102Drift (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
      H (2 * p.d + 8) ((p.d : ℝ) + 2)
      (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) (Mb ω) ∧
      ContinuousOn (D.Yh ω) (Icc 0 H) ∧ BoundedVariationOn (D.Fd ω) (Icc 0 H) ∧
      (eVariationOn (D.Fd ω) (Icc 0 H)).toReal ≤ D.Vd ω ∧
      ∀ q r, 0 ≤ q → q ≤ r → r ≤ H → D.Fd ω r - D.Fd ω q =
        r2DriftInc (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
          (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) q r := by
    filter_upwards [hMb, D.Yh_continuous, D.Fd_good] with ω hb hy hd
    exact ⟨hb, hy, hd.2.2.1, hd.2.2.2⟩
  have hjg : ∀ᵐ ω ∂A.P, ContinuousOn (D.Yh ω) (Icc 0 H) ∧
      (∀ q r, 0 ≤ q → q ≤ r → r ≤ H →
        IsR2JValue (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
          (fp81s21_movingRawEtaField p R A ω) (Ioc q r)
          (((D.Fj ω r - D.Fj ω q : projTensor B 2) : TensorDual B 2))) ∧
      ContinuousOn (D.Fj ω) (Icc 0 H) ∧ BoundedVariationOn (D.Fj ω) (Icc 0 H) ∧
      (eVariationOn (D.Fj ω) (Icc 0 H)).toReal ≤ D.Vj ω := by
    filter_upwards [D.Yh_continuous, D.Fj_good] with ω hy hj
    exact ⟨hy, hj⟩
  have hp := hfuture.2.2.2 H hH
  obtain ⟨dval, hdi, hd, hdiLim⟩ := fp81s21_drift_projection_removal hP hstd.hD hlin hH
    A.P (future H) (hfuture.1 H) (fun L => s102_Pj H hH L) hp.1 hp.2.1
    (hfuture.2.2.1 H hH) Ψ hΨ D.Yh D.Fd
    (fun ω u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) Mb D.Vd
    D.Vd_integrable hg (fun L => (WS L).drift)
  obtain ⟨jval, hji, hj, hjiLim⟩ := fp81s21_covariance_projection_removal
    (r26t3_coeff R) hH A.P (HRS.Fp81.V01.fp81v01_projTensorComplete B 2)
    (future H) (hfuture.1 H) (fun L => s102_Pj H hH L) hp.1 hp.2.1
    (fun j v hv => hp.2.2.1 j v hv) (hfuture.2.2.1 H hH) hΨ D.Yh D.Fj
    (fun ω => fp81s21_movingRawEtaField p R A ω) D.Vj D.Vj_integrable D.Fj_zero hjg
    (fun L => (WS L).covariance)
  refine ⟨dval, jval, hdi, hji, hd.mono (fun _ h => ⟨h.1, h.2.1⟩),
    hj.mono (fun _ h => ⟨h.1, h.2.1⟩), hdiLim, hjiLim, ?_⟩
  have hlast := fp81s21_moving_heat_endpoint_expectation_projection_limit
    p R A F a ha hH future hfuture D Φ hΦ H hH.le le_rfl
  have hfirst := fp81s21_moving_heat_endpoint_expectation_projection_limit
    p R A F a ha hH future hfuture D Φ hΦ 0 le_rfl hH.le
  have hl := (hlast.sub hfirst).const_mul (Real.sqrt N)
  have hr := hdiLim.neg.add (hjiLim.const_mul (1 / 2 : ℝ))
  apply tendsto_nhds_unique hl
  apply hr.congr'
  filter_upwards [] with L
  simpa [fp81s21_WindowRS_corr] using
    (fp81s21_moving_heat_ito_finite_projection_expectation_identity_of_data
      p R hδ hδh a ha hH hN A F hstd hlin hphys future hfuture D Φ hΦ WS
      L 0 H le_rfl hH.le le_rfl).symm

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_moving_heat_ito_full_horizon_expectation_identity_of_data
