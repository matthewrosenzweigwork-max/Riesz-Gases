import HRS.MS.Fp81S21LiftTwoLaw2

/-! Cutoff lifting for almost-everywhere measurable random variables. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace HRS.Fp81.S21

/-- The cutoff bound is invariant under replacing both raw windows and both
outputs by measurable versions. In particular, no pointwise measurability of
the original windows is needed. -/
theorem fp81s21_jointClose_ae_cutoff
    {Ω₁ Ω₂ X B : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]
    [SecondCountableTopology B] [CompleteSpace B]
    (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (U₁ : Ω₁ → X) (U₂ : Ω₂ → X) (V₁ : Ω₁ → B) (V₂ : Ω₂ → B)
    (F : X → B) (Q : B →L[ℝ] B)
    (hU₁ : AEMeasurable U₁ P₁) (hU₂ : AEMeasurable U₂ P₂)
    (hV₁ : AEMeasurable V₁ P₁) (hV₂ : AEMeasurable V₂ P₂) (hF : Measurable F)
    (hQ : ‖Q‖ ≤ 1)
    (K M δ R τ₁ τ₂ : ℝ) (hK : 0 ≤ K)
    (hR : 1 ≤ R) (hτ₁ : 0 ≤ τ₁) (hτ₂ : 0 ≤ τ₂)
    (hgrowth : ∀ x, ‖F x‖ ≤ K * (1 + ‖x‖ ^ 2))
    (hlip : ∀ x y, ‖F x - F y‖ ≤ K * (1 + ‖x‖ + ‖y‖) * ‖x - y‖)
    (hF₁ : Integrable (fun ω => F (U₁ ω)) P₁)
    (hF₂ : Integrable (fun ω => F (U₂ ω)) P₂)
    (π : Measure (X × X)) [IsProbabilityMeasure π]
    (hπ₁ : π.map Prod.fst = law P₁ U₁)
    (hπ₂ : π.map Prod.snd = law P₂ U₂)
    (hfst6 : Integrable (fun z : X × X => ‖z.1‖ ^ 6) π)
    (hsnd6 : Integrable (fun z : X × X => ‖z.2‖ ^ 6) π)
    (hfstM : ∫ z, ‖z.1‖ ^ 6 ∂π ≤ M)
    (hsndM : ∫ z, ‖z.2‖ ^ 6 ∂π ≤ M)
    (hinput : ∫ z, ‖z.1 - z.2‖ ∂π ≤ δ)
    (hErr₁int : Integrable (fun ω => ‖V₁ ω -
      (F (U₁ ω) - Q (∫ ω', F (U₁ ω') ∂P₁))‖ ^ 2) P₁)
    (hErr₁ : ∫ ω, ‖V₁ ω -
      (F (U₁ ω) - Q (∫ ω', F (U₁ ω') ∂P₁))‖ ^ 2 ∂P₁ ≤ τ₁ ^ 2)
    (hErr₂int : Integrable (fun ω => ‖V₂ ω -
      (F (U₂ ω) - Q (∫ ω', F (U₂ ω') ∂P₂))‖ ^ 2) P₂)
    (hErr₂ : ∫ ω, ‖V₂ ω -
      (F (U₂ ω) - Q (∫ ω', F (U₂ ω') ∂P₂))‖ ^ 2 ∂P₂ ≤ τ₂ ^ 2) :
    wassersteinE 2 (law P₁ V₁) (law P₂ V₂) ≤
      ENNReal.ofReal (τ₁ + τ₂ + 2 * Real.sqrt
        (K ^ 2 * ((1 + 2 * R) ^ 2 * (2 * R) * δ + 64 * (1 + M) / R ^ 2))) := by
  let U₁' := hU₁.mk U₁
  let U₂' := hU₂.mk U₂
  let V₁' := hV₁.mk V₁
  let V₂' := hV₂.mk V₂
  have hfu₁ : (fun ω => F (U₁ ω)) =ᵐ[P₁] (fun ω => F (U₁' ω)) := by
    filter_upwards [hU₁.ae_eq_mk] with ω hω
    rw [hω]
  have hfu₂ : (fun ω => F (U₂ ω)) =ᵐ[P₂] (fun ω => F (U₂' ω)) := by
    filter_upwards [hU₂.ae_eq_mk] with ω hω
    rw [hω]
  have hi₁ : (∫ ω, F (U₁ ω) ∂P₁) = ∫ ω, F (U₁' ω) ∂P₁ := integral_congr_ae hfu₁
  have hi₂ : (∫ ω, F (U₂ ω) ∂P₂) = ∫ ω, F (U₂' ω) ∂P₂ := integral_congr_ae hfu₂
  have he₁ : (fun ω => ‖V₁ ω - (F (U₁ ω) - Q (∫ ω', F (U₁ ω') ∂P₁))‖ ^ 2) =ᵐ[P₁]
      (fun ω => ‖V₁' ω - (F (U₁' ω) - Q (∫ ω', F (U₁' ω') ∂P₁))‖ ^ 2) := by
    filter_upwards [hV₁.ae_eq_mk, hfu₁] with ω hv hu
    rw [hv, hu, hi₁]
  have he₂ : (fun ω => ‖V₂ ω - (F (U₂ ω) - Q (∫ ω', F (U₂ ω') ∂P₂))‖ ^ 2) =ᵐ[P₂]
      (fun ω => ‖V₂' ω - (F (U₂' ω) - Q (∫ ω', F (U₂' ω') ∂P₂))‖ ^ 2) := by
    filter_upwards [hV₂.ae_eq_mk, hfu₂] with ω hv hu
    rw [hv, hu, hi₂]
  have hc := fp81s21_liftTwoLaw_cutoff P₁ P₂ U₁' U₂' V₁' V₂' F Q
    hU₁.measurable_mk hU₂.measurable_mk hV₁.measurable_mk hV₂.measurable_mk hF
    hQ K M δ R τ₁ τ₂ hK hR hτ₁ hτ₂ hgrowth hlip
    (hF₁.congr hfu₁) (hF₂.congr hfu₂) π
    (hπ₁.trans (Measure.map_congr hU₁.ae_eq_mk))
    (hπ₂.trans (Measure.map_congr hU₂.ae_eq_mk))
    hfst6 hsnd6 hfstM hsndM hinput (hErr₁int.congr he₁)
    (by rw [← integral_congr_ae he₁]; exact hErr₁) (hErr₂int.congr he₂)
    (by rw [← integral_congr_ae he₂]; exact hErr₂)
  change wassersteinE 2 (P₁.map V₁') (P₂.map V₂') ≤ _ at hc
  rw [← Measure.map_congr hV₁.ae_eq_mk, ← Measure.map_congr hV₂.ae_eq_mk] at hc
  exact hc

#print axioms fp81s21_jointClose_ae_cutoff
end HRS.Fp81.S21
end
