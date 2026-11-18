import HRS.MS.Fp81S21CovRS
import HRS.MS.R2InterpAux65
import HRS.MC.S7PIG6A

/-! Covariance projection removal for one specified raw-eta cumulative. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.Sec7 HRS.MS.R2Interp HRS.MS.CovMeas

/-- Remove the heat projection from scalar covariance RS values while keeping
one specified projective raw-eta cumulative throughout. -/
theorem fp81s21_covariance_projection_removal
    {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {m H : ℝ} (C : WholeCoeff d) (hH : 0 < H)
    (μ : Measure Ω)
    (hComplete : CompleteSpace (projTensor (OscPath d m H) 2))
    (γ : ℝ → Measure (OscPath d m H))
    (hγ : ∀ t, IsProbabilityMeasure (γ t))
    (Pj : ℕ → (OscPath d m H →L[ℝ] OscPath d m H))
    (hPj : ∀ L, ‖Pj L‖ ≤ 1)
    (hconv : ∀ w, Tendsto (fun L => Pj L w) atTop (𝓝 w))
    (hTconv : ∀ (j : ℕ) (v : TensorDual (OscPath d m H) j),
      v ∈ projTensor (OscPath d m H) j →
        Tendsto (fun L => tensorPow j (Pj L) v) atTop (𝓝 v))
    (hLP : S102LipProj γ Pj)
    {Ψ : OscPath d m H → ℝ} (hΨ : MemCb 5 Ψ)
    (Y : Ω → ℝ → OscPath d m H)
    (Fj : Ω → ℝ → projTensor (OscPath d m H) 2)
    (z : Ω → ℝ → (Euc d → ℝ) → ℝ)
    (V : Ω → ℝ) (hVi : Integrable V μ)
    (hF0 : ∀ ω, Fj ω 0 = 0)
    (hgood : ∀ᵐ ω ∂μ,
      ContinuousOn (Y ω) (Icc 0 H) ∧
      (∀ q r, 0 ≤ q → q ≤ r → r ≤ H →
        IsR2JValue C m H (z ω) (Ioc q r)
          (((Fj ω r - Fj ω q : projTensor (OscPath d m H) 2) :
            TensorDual (OscPath d m H) 2))) ∧
      ContinuousOn (Fj ω) (Icc 0 H) ∧
      BoundedVariationOn (Fj ω) (Icc 0 H) ∧
      (eVariationOn (Fj ω) (Icc 0 H)).toReal ≤ V ω)
    (WS : ∀ L, fp81s21_RSBVWindow μ H
      (fun ω τ => fp81s21_covariance_pairingCLM
        (iteratedFDeriv ℝ 2
          (r2HeatFn γ (fun w => Ψ (Pj L w)) τ) (Y ω τ)))
      Fj) :
    ∃ jval : Ω → ℝ, Integrable jval μ ∧
      (∀ᵐ ω ∂μ,
        IsR2RS H (fun τ q r => fp81s21_covariance_pairingCLM
          (iteratedFDeriv ℝ 2 (r2HeatFn γ Ψ τ) (Y ω τ))
          (Fj ω r - Fj ω q)) (jval ω) ∧
        Tendsto (fun L => (WS L).value 0 H ω) atTop (𝓝 (jval ω)) ∧
        ∀ L, |(WS L).value 0 H ω| ≤ cbNorm 5 Ψ * V ω) ∧
      Tendsto (fun L => ∫ ω, (WS L).value 0 H ω ∂μ) atTop
        (𝓝 (∫ ω, jval ω ∂μ)) := by
  classical
  letI : CompleteSpace (projTensor (OscPath d m H) 2) := hComplete
  let vals : ℕ → Ω → ℝ := fun L => (WS L).value 0 H
  let Jc : Ω → ℝ → TensorDual (OscPath d m H) 2 :=
    fun ω t => (Fj ω t : TensorDual (OscPath d m H) 2)
  have hRS : ∀ᵐ ω ∂μ, ∀ L, fp81s21_IsRSOn 0 H
      (fun τ q r => fp81s21_covariance_pairingCLM
        (iteratedFDeriv ℝ 2
          (r2HeatFn γ (fun w => Ψ (Pj L w)) τ) (Y ω τ))
        (Fj ω r - Fj ω q)) (vals L ω) :=
    ae_all_iff.2 (fun L => by
      simpa only [vals] using (WS L).value_isRS 0 H le_rfl hH.le le_rfl)
  have hex : ∀ᵐ ω ∂μ,
      ∃ I, IsR2RS H (fun τ q r => fp81s21_covariance_pairingCLM
        (iteratedFDeriv ℝ 2 (r2HeatFn γ Ψ τ) (Y ω τ))
        (Fj ω r - Fj ω q)) I ∧
        Tendsto (fun L => vals L ω) atTop (𝓝 I) ∧
        ∀ L, |vals L ω| ≤ cbNorm 5 Ψ * V ω := by
    filter_upwards [hgood, hRS] with ω hg hωRS
    obtain ⟨hY, hJ, hFc, hBV, hV⟩ := hg
    have hJc0 : Jc ω 0 = 0 := by simpa [Jc] using hF0 ω
    have hJc : ∀ q r, 0 ≤ q → q ≤ r → r ≤ H →
        IsR2JValue C m H (z ω) (Ioc q r) (Jc ω r - Jc ω q) := by
      intro q r hq hqr hr
      have hmap : ((Fj ω r - Fj ω q : projTensor (OscPath d m H) 2) :
          TensorDual (OscPath d m H) 2) = Jc ω r - Jc ω q := by
        exact map_sub (projTensor (OscPath d m H) 2).subtypeL _ _
      have hraw := hJ q r hq hqr hr
      rw [hmap] at hraw
      exact hraw
    obtain ⟨I, hI, _, IL, hIL, hILbound, hlim⟩ :=
      s102_RS_J_bv C hH γ hγ Pj hPj hconv hTconv hLP hΨ (Y ω) hY
        (z ω) (Jc ω) hJc0 hJc hBV
    have heq : ∀ L, vals L ω = IL L := by
      intro L
      have hR : IsR2RS H (fun τ q r => fp81s21_covariance_pairingCLM
          (iteratedFDeriv ℝ 2
            (r2HeatFn γ (fun w => Ψ (Pj L w)) τ) (Y ω τ))
          (Fj ω r - Fj ω q)) (vals L ω) := by
        simpa [fp81s21_IsRSOn, vals] using hωRS L
      have hR' : IsR2RS H (fun τ q r =>
          r2JPair C m H (z ω) (Ioc q r)
            (iteratedFDeriv ℝ 2
              (r2HeatFn γ (fun w => Ψ (Pj L w)) τ) (Y ω τ)))
          (vals L ω) := by
        refine (s102_isR2RS_iff _ _ _).2
          (HRS.MC.Sec7.S7PIG6.S7PIG6_IsRS_congr
            ((s102_isR2RS_iff _ _ _).1 hR) ?_)
        intro τ q r hτ hq hqr hr
        rw [s102_jPair_eq C hH (z ω) (Jc ω) hJc q r hq
          hqr hr _]
        simp [fp81s21_covariance_pairingCLM, Jc]
      exact s102_RS_unique hH hR' (hIL L)
    have hI' : IsR2RS H (fun τ q r => fp81s21_covariance_pairingCLM
        (iteratedFDeriv ℝ 2 (r2HeatFn γ Ψ τ) (Y ω τ))
        (Fj ω r - Fj ω q)) I := by
      refine (s102_isR2RS_iff _ _ _).2
        (HRS.MC.Sec7.S7PIG6.S7PIG6_IsRS_congr
          ((s102_isR2RS_iff _ _ _).1 hI) ?_)
      intro τ q r hτ hq hqr hr
      rw [s102_jPair_eq C hH (z ω) (Jc ω) hJc q r hq
        hqr hr _]
      simp [fp81s21_covariance_pairingCLM, Jc]
    refine ⟨I, hI', ?_, ?_⟩
    · simpa only [heq] using hlim
    · intro L
      rw [heq L]
      calc
        |IL L| ≤ cbNorm 5 Ψ * (eVariationOn (Fj ω) (Icc 0 H)).toReal :=
          hILbound L
        _ ≤ cbNorm 5 Ψ * V ω :=
          mul_le_mul_of_nonneg_left hV
            (HRS.MC.Sec7.S7PIL.S7PIL_cbNorm_nonneg hΨ 0)
  have hlimit := HRS.MC.Sec7.S7PIG6.S7PIG6_lim vals
    (fun L => ((WS L).value_aemeasurable 0 H le_rfl hH.le le_rfl).aestronglyMeasurable)
    (fun ω => cbNorm 5 Ψ * V ω) (hVi.const_mul _)
    (hex.mono fun ω hω => ⟨⟨hω.choose, hω.choose_spec.2.1⟩, hω.choose_spec.2.2⟩)
  refine ⟨fun ω => limUnder atTop (fun L => vals L ω), hlimit.1, ?_, hlimit.2.2⟩
  filter_upwards [hex, hlimit.2.1] with ω hω hlim
  obtain ⟨I, hI, hIlim, hbound⟩ := hω
  have heq := tendsto_nhds_unique hIlim hlim
  exact ⟨heq ▸ hI, hlim, hbound⟩

#print axioms HRS.Fp81.S21.fp81s21_covariance_projection_removal

end HRS.Fp81.S21
end
