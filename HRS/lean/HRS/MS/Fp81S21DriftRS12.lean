import HRS.MS.Fp81S21MovingPrediction3
import HRS.MS.Fp81S21DriftCumulative11
import HRS.MS.Fp81S21MovingHeat3
import HRS.MS.Fp81S21DriftRS10

/-! Physical moving drift: selected measurable BV RS families. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp

/-- At a fixed physical start, the actual measurable prediction and drift
cumulative produce projected RS families with one integrable bound independent
of the projection level. -/
theorem fp81s21_moving_drift_rsbv_window_fixed
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (a : ℝ) (ha : 0 ≤ a)
    (hH : 0 < a + p.T) {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
    (F : FilteredParticle A) {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) (a + p.T)
      (2 * p.d + 8) c hH)
    (hlin : S102Lin (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) (a + p.T))
    (hphys : Fp81MovingPhysicalInputs R hN A (a + p.T))
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hfuture : fp81s21_moving_heat_full_clause p R future) :
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
        let Ad := fun L ω t => fderiv ℝ
          (r2HeatFn (future (a + p.T)) (fun w => Φ (W (s102_Pj (a + p.T) hH L w))) t)
          (Yh ω t)
        ∃ M : A.Ω → ℝ, Integrable M A.P ∧ ∀ L,
          Nonempty (fp81s21_RSBVWindow A.P (a + p.T) (Ad L) Fd) ∧
          ∀ q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
            Integrable (fp81s21_rs_bv_variation_majorant (Ad L) Fd q r) A.P ∧
            ∀ᵐ ω ∂A.P, fp81s21_rs_bv_variation_majorant (Ad L) Fd q r ω ≤ M ω := by
  obtain ⟨Yh, hYm, hYe, hYc⟩ := fp81s21_moving_prediction p R hδ hδh hH hN A F hstd hlin hphys
  obtain ⟨Fd, V, hFm, hVi, hFg⟩ := fp81s21_moving_drift_cumulative_fixed p R hδ hδh hH hN A hstd hphys
  refine ⟨Yh, Fd, V, hYm, hFm, hVi, ?_, ?_⟩
  · filter_upwards [hYe, hYc, hFg] with ω he hc hf
    exact ⟨he, hc, hf⟩
  · intro Φ hΦ
    let W := HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T)
      (H := a + p.T) ha le_rfl
    let Ψ := fun w => Φ (W w)
    have hΨ : MemCb 5 Ψ := (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof W hΦ).1
    have hp := hfuture.2.2.2 (a + p.T) hH
    exact fp81s21_projected_heat_rsbv_window A.P (future (a + p.T))
      (hfuture.1 (a + p.T)) (fun L => s102_Pj (a + p.T) hH L)
      hp.1 hp.2.1 (hfuture.2.2.1 (a + p.T) hH) Ψ hΨ Yh Fd V hYm hFm hYc
      (hFg.mono fun _ h => h.2.1) hVi (hFg.mono fun _ h => ⟨h.2.2.1, h.2.2.2.1⟩)

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_moving_drift_rsbv_window_fixed
