import HRS.MS.Fp81S21LiftTwoLaw

/-!
# S2.1(iii), two-law cutoff lift

This wrapper feeds the compiled packet 7 sixth-moment cutoff estimate into the
two-law separately centered adapter.  `π` is a coupling of the input laws;
the coordinate moment assumptions and mean input-distance assumption are
written on `π`, where the packet 7 theorem consumes them.  By the marginal
identities these are precisely the corresponding law moments and coupling
costs in the packet 31b design.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HRS.Fp81.S21

/-- Two-law, separately centered lifting estimate from a coupling of the
input laws.  The cutoff contribution is the packet 7 value
`sqrt (K² ((1+2R)² (2R) δ + 64(1+M)/R²))`; centering only the selected output
component doubles this contribution. -/
theorem fp81s21_liftTwoLaw_cutoff
    {Ω₁ Ω₂ X B : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]
    [SecondCountableTopology B] [CompleteSpace B]
    (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (U₁ : Ω₁ → X) (U₂ : Ω₂ → X) (V₁ : Ω₁ → B) (V₂ : Ω₂ → B)
    (F : X → B) (Q : B →L[ℝ] B)
    (hU₁ : Measurable U₁) (hU₂ : Measurable U₂)
    (hV₁ : Measurable V₁) (hV₂ : Measurable V₂) (hF : Measurable F)
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
        (K ^ 2 * ((1 + 2 * R) ^ 2 * (2 * R) * δ +
          64 * (1 + M) / R ^ 2))) := by
  have hfst : Measurable (fun z : X × X => z.1) := measurable_fst
  have hsnd : Measurable (fun z : X × X => z.2) := measurable_snd
  have hcost := HRS.Fp81.V01.fp81_s21_lift_L2_expectation_form π F
    (fun z : X × X => z.1) (fun z => z.2) K M δ R hK hR
    hF hfst hsnd hgrowth hlip hfst6 hsnd6 hfstM hsndM hinput
  have hM0 : 0 ≤ M := (integral_nonneg fun z => by positivity).trans hfstM
  have hδ0 : 0 ≤ δ := (integral_nonneg fun z => by positivity).trans hinput
  let Bcut : ℝ := K ^ 2 * ((1 + 2 * R) ^ 2 * (2 * R) * δ +
    64 * (1 + M) / R ^ 2)
  have hBcut0 : 0 ≤ Bcut := by
    dsimp [Bcut]
    positivity
  have hcost' : ∫⁻ z, ENNReal.ofReal (‖F z.1 - F z.2‖ ^ 2) ∂π ≤
      ENNReal.ofReal ((Real.sqrt Bcut) ^ 2) := by
    simpa [Real.sq_sqrt hBcut0] using hcost
  exact fp81s21_liftTwoLaw_adapter_of_rawCost P₁ P₂ U₁ U₂ V₁ V₂ F Q
    hU₁ hU₂ hV₁ hV₂ hF hQ hF₁ hF₂ π hπ₁ hπ₂
    (Real.sqrt Bcut) τ₁ τ₂
    (Real.sqrt_nonneg _) hτ₁ hτ₂ hcost' hErr₁int hErr₁ hErr₂int hErr₂

#print axioms fp81s21_liftTwoLaw_cutoff

end HRS.Fp81.S21

end
