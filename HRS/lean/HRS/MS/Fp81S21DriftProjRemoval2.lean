import HRS.MS.Fp81S21DriftProjRemoval
import HRS.MS.Fp81S21DriftRS15

/-! Physical drift projection removal with the selected cylindrical values. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.CovMeas

/-- The physical finite-level drift values converge to the specified
unprojected drift RS value, with one integrable variation bound. -/
theorem fp81s21_moving_drift_projection_removal (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∃ future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H),
        fp81s21_moving_heat_full_clause p R future ∧
        ∀ (a : ℝ) (ha : 0 ≤ a) (hH : 0 < a + p.T)
          (N : ℕ) (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A),
        ∃ (Yh Fd : A.Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T))
          (V : A.Ω → ℝ),
          (∀ t, Measurable (fun ω => Yh ω t)) ∧
          (∀ t, Measurable (fun ω => Fd ω t)) ∧ Integrable V A.P ∧
          (∀ᵐ ω ∂A.P, (∀ t ∈ Icc (0 : ℝ) (a + p.T),
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
            let W := HRS.MS.ProClosureS111.physicalWindowRestriction
              (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T)
              (H := a + p.T) ha le_rfl
            let Ψ := fun w => Φ (W w)
            let Ad := fun L ω t => fderiv ℝ
              (r2HeatFn (future (a + p.T)) (fun w => Ψ (s102_Pj (a + p.T) hH L w)) t)
              (Yh ω t)
            ∃ (WS : ∀ L, fp81s21_RSBVWindow A.P (a + p.T) (Ad L) Fd)
              (dval : A.Ω → ℝ) (M : A.Ω → ℝ),
              Integrable dval A.P ∧ Integrable M A.P ∧
              (∀ L q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
                Integrable (fp81s21_rs_bv_variation_majorant (Ad L) Fd q r) A.P ∧
                (∀ᵐ ω ∂A.P,
                  IntegrableOn (fp81s21_moving_drift_cyl_sum p R A F a ha hH L Φ ω) (Ioc q r) ∧
                  (WS L).value q r ω =
                    ∫ u in Ioc q r, fp81s21_moving_drift_cyl_sum p R A F a ha hH L Φ ω u) ∧
                (∀ᵐ ω ∂A.P, fp81s21_rs_bv_variation_majorant (Ad L) Fd q r ω ≤ M ω)) ∧
              (∀ᵐ ω ∂A.P, IsR2RS (a + p.T) (fun t q r =>
                fderiv ℝ (r2HeatFn (future (a + p.T)) Ψ t) (Yh ω t)
                  (r2DriftInc (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) (a + p.T)
                    (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) q r)) (dval ω) ∧
                Tendsto (fun L => (WS L).value 0 (a + p.T) ω) atTop (𝓝 (dval ω)) ∧
                ∀ L, |(WS L).value 0 (a + p.T) ω| ≤ cbNorm 5 Ψ * V ω) ∧
              Tendsto (fun L => ∫ ω, (WS L).value 0 (a + p.T) ω ∂A.P) atTop
                (𝓝 (∫ ω, dval ω ∂A.P)) := by
  classical
  obtain ⟨δr, hδr, hrhalf, hrs⟩ := fp81s21_moving_drift_rs p
  obtain ⟨δi, hδi, -, hinputs⟩ := fp81s21_moving_inputs_all p
  refine ⟨min δr δi, lt_min hδr hδi, (min_le_left _ _).trans hrhalf, ?_⟩
  intro δ hδ hδle R
  obtain ⟨future, hfuture, hfamilies⟩ := hrs δ hδ (hδle.trans (min_le_left _ _)) R
  refine ⟨future, hfuture, ?_⟩
  intro a ha hH N hN A F
  obtain ⟨Yh, Fd, V, hYm, hFm, hVi, hgood, hfamily⟩ := hfamilies a ha hH N hN A F
  obtain ⟨c, hstd, hphys⟩ := hinputs δ hδ (hδle.trans (min_le_right _ _)) R a ha
  have hr0 : (p.d : ℝ) / 2 + 2 < (2 * p.d + 8 : ℕ) := by
    have hd0 : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
    norm_num [Nat.cast_add, Nat.cast_mul]
    linarith
  obtain ⟨Mb, hMb, -⟩ := fp81s21_moving_M1 p R hH hN A hstd hr0 (hphys N hN A)
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    have : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
    linarith
  refine ⟨Yh, Fd, V, hYm, hFm, hVi, hgood, ?_⟩
  intro Φ hΦ
  let W := HRS.MS.ProClosureS111.physicalWindowRestriction
    (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T) (H := a + p.T) ha le_rfl
  let Ψ := fun w => Φ (W w)
  have hΨ : MemCb 5 Ψ := (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof W hΦ).1
  obtain ⟨M, hMi, hlevels⟩ := hfamily Φ hΦ
  choose WS hWS using hlevels
  have hp := hfuture.2.2.2 (a + p.T) hH
  have hg : ∀ᵐ ω ∂A.P, S102Drift (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
      (a + p.T) (2 * p.d + 8) ((p.d : ℝ) + 2)
      (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) (Mb ω) ∧
      ContinuousOn (Yh ω) (Icc 0 (a + p.T)) ∧
      BoundedVariationOn (Fd ω) (Icc 0 (a + p.T)) ∧
      (eVariationOn (Fd ω) (Icc 0 (a + p.T))).toReal ≤ V ω ∧
      ∀ q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
        Fd ω r - Fd ω q = r2DriftInc (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
          (a + p.T) (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) q r := by
    filter_upwards [hMb, hgood] with ω hb hd
    exact ⟨hb, hd.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2⟩
  obtain ⟨dval, hdi, hd, hdiLim⟩ := fp81s21_drift_projection_removal hP hstd.hD
    (fp81s21_S102Lin p R (a + p.T)) hH A.P (future (a + p.T))
    (hfuture.1 (a + p.T)) (fun L => s102_Pj (a + p.T) hH L)
    hp.1 hp.2.1 (hfuture.2.2.1 (a + p.T) hH) Ψ hΨ Yh Fd
    (fun ω u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) Mb V hVi hg WS
  exact ⟨WS, dval, M, hdi, hMi, hWS, hd, hdiLim⟩

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_moving_drift_projection_removal
