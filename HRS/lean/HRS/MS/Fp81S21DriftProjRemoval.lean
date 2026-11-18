import HRS.MS.Fp81S21DriftRS7
import HRS.MC.S7PIG6A

/-! Removal of the full-horizon drift projection for specified RS values. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R2Interp HRS.MS.CovMeas

/-- The deterministic drift theorem identifies its projected values with any
specified BV window values. The common bound is the full-path variation. -/
theorem fp81s21_drift_projection_removal
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {C : WholeCoeff d}
    {m H : ℝ} {k : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m H k c)
    (hlin : S102Lin C m H) (hH : 0 < H)
    (μ : Measure Ω) (γ : ℝ → Measure (OscPath d m H))
    (hγ : ∀ t, IsProbabilityMeasure (γ t))
    (Pj : ℕ → (OscPath d m H →L[ℝ] OscPath d m H))
    (hPj : ∀ L, ‖Pj L‖ ≤ 1)
    (hconv : ∀ w, Tendsto (fun L => Pj L w) atTop (𝓝 w))
    (hLP : S102LipProj γ Pj) (Ψ : OscPath d m H → ℝ) (hΨ : MemCb 5 Ψ)
    (Y F : Ω → ℝ → OscPath d m H) (b : Ω → ℝ → (Euc d → ℝ) → ℝ)
    (Mb : Ω → ℝ → ℝ) (V : Ω → ℝ) (hVi : Integrable V μ)
    (hgood : ∀ᵐ ω ∂μ, S102Drift C m H k Pw (b ω) (Mb ω) ∧
      ContinuousOn (Y ω) (Icc 0 H) ∧
      BoundedVariationOn (F ω) (Icc 0 H) ∧
      (eVariationOn (F ω) (Icc 0 H)).toReal ≤ V ω ∧
      ∀ q r, 0 ≤ q → q ≤ r → r ≤ H →
        F ω r - F ω q = r2DriftInc C m H (b ω) q r)
    (WS : ∀ L, fp81s21_RSBVWindow μ H
      (fun ω t => fderiv ℝ (r2HeatFn γ (fun w => Ψ (Pj L w)) t) (Y ω t)) F) :
    ∃ dval : Ω → ℝ, Integrable dval μ ∧
      (∀ᵐ ω ∂μ, IsR2RS H (fun t q r =>
        fderiv ℝ (r2HeatFn γ Ψ t) (Y ω t) (r2DriftInc C m H (b ω) q r)) (dval ω) ∧
        Tendsto (fun L => (WS L).value 0 H ω) atTop (𝓝 (dval ω)) ∧
        ∀ L, |(WS L).value 0 H ω| ≤ cbNorm 5 Ψ * V ω) ∧
      Tendsto (fun L => ∫ ω, (WS L).value 0 H ω ∂μ) atTop (𝓝 (∫ ω, dval ω ∂μ)) := by
  classical
  let vals : ℕ → Ω → ℝ := fun L => (WS L).value 0 H
  have hrs : ∀ᵐ ω ∂μ, ∀ L, fp81s21_IsRSOn 0 H
      (fun t q r => fderiv ℝ (r2HeatFn γ (fun w => Ψ (Pj L w)) t)
        (Y ω t) (F ω r - F ω q)) (vals L ω) :=
    ae_all_iff.2 (fun L => (WS L).value_isRS 0 H le_rfl hH.le le_rfl)
  have hex : ∀ᵐ ω ∂μ, ∃ I, IsR2RS H (fun t q r =>
      fderiv ℝ (r2HeatFn γ Ψ t) (Y ω t) (r2DriftInc C m H (b ω) q r)) I ∧
      Tendsto (fun L => vals L ω) atTop (𝓝 I) ∧
      ∀ L, |vals L ω| ≤ cbNorm 5 Ψ * V ω := by
    filter_upwards [hgood, hrs] with ω hg hr
    obtain ⟨hb, hY, hBV, hV, hinc⟩ := hg
    obtain ⟨I, hI, -, IL, hIL, -, hlim⟩ :=
      s102_RS_drift hP hD hlin hb hH γ hγ Pj hPj hconv hLP hΨ (Y ω) hY
    have heq : ∀ L, vals L ω = IL L := by
      intro L
      have hR : IsR2RS H (fun t q r =>
          fderiv ℝ (r2HeatFn γ (fun w => Ψ (Pj L w)) t) (Y ω t)
            (F ω r - F ω q)) (vals L ω) := by
        simpa [fp81s21_IsRSOn] using hr L
      have hR' : IsR2RS H (fun t q r =>
          fderiv ℝ (r2HeatFn γ (fun w => Ψ (Pj L w)) t) (Y ω t)
            (r2DriftInc C m H (b ω) q r)) (vals L ω) := by
        refine (s102_isR2RS_iff _ _ _).2 (HRS.MC.Sec7.S7PIG4.S7PIG4_RS_congr
          ((s102_isR2RS_iff _ _ _).1 hR) ?_)
        intro t q r hq hqt htr hrH
        rw [hinc q r hq (hqt.trans htr) hrH]
      exact s102_RS_unique hH hR' (hIL L)
    refine ⟨I, hI, ?_, ?_⟩
    · simpa only [heq] using hlim
    · intro L
      have hc := fp81s21_projected_heat_gradient_continuousOn γ hγ Pj hPj hconv hLP Ψ hΨ L (Y ω) hY
      have hbnd := fp81s21_rsOn_bv_bound hH (F ω) _ hBV hc (hr L)
      exact hbnd.trans (fp81s21_projected_heat_variation_majorant_le γ hγ (Pj L)
        (hPj L) Ψ hΨ Y F ω (V ω) hBV hV le_rfl hH.le le_rfl)
  have hlim := HRS.MC.Sec7.S7PIG6.S7PIG6_lim vals
    (fun L => ((WS L).value_aemeasurable 0 H le_rfl hH.le le_rfl).aestronglyMeasurable)
    (fun ω => cbNorm 5 Ψ * V ω) (hVi.const_mul _) (hex.mono fun ω h => ⟨⟨h.choose, h.choose_spec.2.1⟩, h.choose_spec.2.2⟩)
  refine ⟨fun ω => limUnder atTop (fun L => vals L ω), hlim.1, ?_, hlim.2.2⟩
  filter_upwards [hex, hlim.2.1] with ω h ht
  obtain ⟨I, hI, hIlim, hb⟩ := h
  have heq := tendsto_nhds_unique hIlim ht
  exact ⟨heq ▸ hI, ht, hb⟩

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_drift_projection_removal
