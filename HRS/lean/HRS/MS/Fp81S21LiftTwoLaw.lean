import HRS.MS.Fp81S21LiftingClean
import HRS.MS.Fp81S21CenteredAdapter2

/-!
# S2.1(iii), two-law separately centered lifting

This file abstracts the output of the path lift as a map `F : X → B`.  A
contractive continuous linear map `Q : B → B` selects the component to be
centered (for a joint output, `Q` is the projection onto the final quadratic
component).  The generic result compares actual outputs on two probability
spaces with their separately centered lifts, using a coupling of the input
laws.  The coupling cost hypothesis is intended to be discharged by the
cutoff estimate in `Fp81S21LiftTwoLaw2`.

The actual outputs correspond to the two finite-rank approximations in packet
31b; `hErr₁` and `hErr₂` are their squared-mean errors.  The map `F` is the
common polynomial lift.  The constants `c₁` and `c₂` below are the separate
law barycenters after applying `Q`.  Their difference is bounded by the raw
W₂ cost, which accounts for the factor two in the centered comparison.

The exported estimate has the schema
`W₂(law V₁, law V₂) ≤ τ₁ + τ₂ + 2σ`, where `σ²` bounds the coupled raw
square cost of `F`; its input approximation hypotheses are
`E_i ‖V_i - (F(U_i) - Q(E_i F(U_i)))‖² ≤ τ_i²` separately under `P_i`.
For the physical packet, take `X` to be the oscillator
path space `OscPath p.d (wholeSpaceIndex p.d) H`, take `B` to be the joint
output `Joint H = X × (Y H × Z H)`, take `F = liftMap m k`, and let `Q` be
the coordinate projection onto the last (quadratic) component, embedded back
into `Joint H`.  Then `U₁,U₂` are the particle and Gaussian raw path inputs,
`V₁,V₂` are their actual joint outputs, and `hErr₁,hErr₂` are the two
separately centered `SqErr` bounds.  In that instance `σ` is the cutoff
profile supplied by `fp81s21_liftTwoLaw_cutoff`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HRS.Fp81.S21

private theorem fp81s21_liftTwoLaw_wass_of_sq_cost
    {Ω B : Type*} [MeasurableSpace Ω] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [MeasurableSpace B] [BorelSpace B]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (A D : Ω → B) (hA : AEMeasurable A P) (hD : AEMeasurable D P)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hcost : ∫⁻ ω, ENNReal.ofReal (‖A ω - D ω‖ ^ 2) ∂P ≤ ENNReal.ofReal (τ ^ 2)) :
    wassersteinE 2 (law P A) (law P D) ≤ ENNReal.ofReal τ := by
  have hcouple := wassersteinE_le_of_coupling P 2 (by norm_num) A D hA hD
  have hcost' : ∫⁻ ω, ENNReal.ofReal (‖A ω - D ω‖ ^ ((2 : ℕ) : ℝ)) ∂P =
      ∫⁻ ω, ENNReal.ofReal (‖A ω - D ω‖ ^ 2) ∂P := by
    apply lintegral_congr
    intro ω
    congr 1
    rw [Real.rpow_natCast]
  calc
    wassersteinE 2 (law P A) (law P D) ≤
        (∫⁻ ω, ENNReal.ofReal (‖A ω - D ω‖ ^ ((2 : ℕ) : ℝ)) ∂P) ^ (1 / (2 : ℝ)) := hcouple
    _ = (∫⁻ ω, ENNReal.ofReal (‖A ω - D ω‖ ^ 2) ∂P) ^ (1 / (2 : ℝ)) := by
      rw [hcost']
    _ ≤ (ENNReal.ofReal (τ ^ 2)) ^ (1 / (2 : ℝ)) :=
      ENNReal.rpow_le_rpow hcost (by norm_num)
    _ = ENNReal.ofReal τ := by
      rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg τ) (by norm_num : 0 ≤ (1 / (2 : ℝ)))]
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_nonneg hτ]

/-- Two-law lifting adapter with separate centering of one contractive output
component.  The input coupling has the two input laws as marginals, and
`hrawCost` bounds the squared raw lift discrepancy under that coupling.

The approximation hypotheses are stated as real `L²` errors.  The result is
the Wasserstein-2 bound `τ₁ + τ₂ + 2σ`; no common probability space for the
actual outputs is required. -/
theorem fp81s21_liftTwoLaw_adapter_of_rawCost
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
    (hF₁ : Integrable (fun ω => F (U₁ ω)) P₁)
    (hF₂ : Integrable (fun ω => F (U₂ ω)) P₂)
    (π : Measure (X × X)) [IsProbabilityMeasure π]
    (hπ₁ : π.map Prod.fst = law P₁ U₁)
    (hπ₂ : π.map Prod.snd = law P₂ U₂)
    (σ τ₁ τ₂ : ℝ) (hσ : 0 ≤ σ) (hτ₁ : 0 ≤ τ₁) (hτ₂ : 0 ≤ τ₂)
    (hrawCost : ∫⁻ z, ENNReal.ofReal (‖F z.1 - F z.2‖ ^ 2) ∂π ≤
      ENNReal.ofReal (σ ^ 2))
    (hErr₁int : Integrable (fun ω => ‖V₁ ω -
      (F (U₁ ω) - Q (∫ ω', F (U₁ ω') ∂P₁))‖ ^ 2) P₁)
    (hErr₁ : ∫ ω, ‖V₁ ω -
      (F (U₁ ω) - Q (∫ ω', F (U₁ ω') ∂P₁))‖ ^ 2 ∂P₁ ≤ τ₁ ^ 2)
    (hErr₂int : Integrable (fun ω => ‖V₂ ω -
      (F (U₂ ω) - Q (∫ ω', F (U₂ ω') ∂P₂))‖ ^ 2) P₂)
    (hErr₂ : ∫ ω, ‖V₂ ω -
      (F (U₂ ω) - Q (∫ ω', F (U₂ ω') ∂P₂))‖ ^ 2 ∂P₂ ≤ τ₂ ^ 2) :
    wassersteinE 2 (law P₁ V₁) (law P₂ V₂) ≤
      ENNReal.ofReal (τ₁ + τ₂ + 2 * σ) := by
  let m₁ : B := ∫ ω, F (U₁ ω) ∂P₁
  let m₂ : B := ∫ ω, F (U₂ ω) ∂P₂
  let c₁ : B := Q m₁
  let c₂ : B := Q m₂
  let C₁ : Ω₁ → B := fun ω => F (U₁ ω) - c₁
  let C₂ : Ω₂ → B := fun ω => F (U₂ ω) - c₂
  let C₂' : Ω₂ → B := fun ω => F (U₂ ω) - c₁
  have hFC₁ : Measurable C₁ := by
    exact (hF.comp hU₁).sub_const c₁
  have hFC₂ : Measurable C₂ := by
    exact (hF.comp hU₂).sub_const c₂
  have hFC₂' : Measurable C₂' := by
    exact (hF.comp hU₂).sub_const c₁
  have hF1m : Measurable (fun x : X => F x - c₁) := hF.sub_const c₁
  have hF2m : Measurable (fun x : X => F x - c₂) := hF.sub_const c₂
  have hRaw₁ : Measurable (fun z : X × X => F z.1 - c₁) := hF1m.comp measurable_fst
  have hRaw₂ : Measurable (fun z : X × X => F z.2 - c₁) := hF1m.comp measurable_snd
  have hRaw₂' : Measurable (fun z : X × X => F z.2 - c₂) := hF2m.comp measurable_snd
  have hLaw₁ : law π (fun z : X × X => F z.1 - c₁) = law P₁ C₁ := by
    dsimp [law, C₁]
    calc
      π.map ((fun x : X => F x - c₁) ∘ Prod.fst) = (π.map Prod.fst).map (fun x : X => F x - c₁) :=
        (Measure.map_map hF1m measurable_fst).symm
      _ = (law P₁ U₁).map (fun x : X => F x - c₁) := by rw [hπ₁]
      _ = P₁.map ((fun x : X => F x - c₁) ∘ U₁) := Measure.map_map hF1m hU₁
  have hLaw₂ : law π (fun z : X × X => F z.2 - c₁) = law P₂ C₂' := by
    dsimp [law, C₂']
    calc
      π.map ((fun x : X => F x - c₁) ∘ Prod.snd) = (π.map Prod.snd).map (fun x : X => F x - c₁) :=
        (Measure.map_map hF1m measurable_snd).symm
      _ = (law P₂ U₂).map (fun x : X => F x - c₁) := by rw [hπ₂]
      _ = P₂.map ((fun x : X => F x - c₁) ∘ U₂) := Measure.map_map hF1m hU₂
  have hLaw₂' : law π (fun z : X × X => F z.2 - c₂) = law P₂ C₂ := by
    dsimp [law, C₂]
    calc
      π.map ((fun x : X => F x - c₂) ∘ Prod.snd) = (π.map Prod.snd).map (fun x : X => F x - c₂) :=
        (Measure.map_map hF2m measurable_snd).symm
      _ = (law P₂ U₂).map (fun x : X => F x - c₂) := by rw [hπ₂]
      _ = P₂.map ((fun x : X => F x - c₂) ∘ U₂) := Measure.map_map hF2m hU₂
  have hRawCost' : ∫⁻ z, ENNReal.ofReal
      (‖(F z.1 - c₁) - (F z.2 - c₁)‖ ^ 2) ∂π ≤ ENNReal.ofReal (σ ^ 2) := by
    calc
      _ = ∫⁻ z, ENNReal.ofReal (‖F z.1 - F z.2‖ ^ 2) ∂π := by
        apply lintegral_congr
        intro z
        congr 3
        abel
      _ ≤ ENNReal.ofReal (σ ^ 2) := hrawCost
  have hMidCouple := wassersteinE_le_of_coupling π 2 (by norm_num)
    (fun z : X × X => F z.1 - c₁) (fun z => F z.2 - c₁)
    hRaw₁.aemeasurable hRaw₂.aemeasurable
  have hMid : wassersteinE 2 (law P₁ C₁) (law P₂ C₂') ≤ ENNReal.ofReal σ := by
    rw [← hLaw₁, ← hLaw₂]
    calc
      wassersteinE 2 (law π (fun z : X × X => F z.1 - c₁))
          (law π (fun z : X × X => F z.2 - c₁)) ≤
          (∫⁻ z, ENNReal.ofReal
            (‖(F z.1 - c₁) - (F z.2 - c₁)‖ ^ ((2 : ℕ) : ℝ)) ∂π) ^ (1 / (2 : ℝ)) :=
              hMidCouple
      _ = (∫⁻ z, ENNReal.ofReal
          (‖(F z.1 - c₁) - (F z.2 - c₁)‖ ^ 2) ∂π) ^ (1 / (2 : ℝ)) := by
            congr 1
            apply lintegral_congr
            intro z
            congr 1
            rw [Real.rpow_natCast]
      _ ≤ (ENNReal.ofReal (σ ^ 2)) ^ (1 / (2 : ℝ)) :=
            ENNReal.rpow_le_rpow hRawCost' (by norm_num)
      _ = ENNReal.ofReal σ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg σ)
          (by norm_num : 0 ≤ (1 / (2 : ℝ)))]
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_nonneg hσ]
  have hRawW : wassersteinE 2 (law P₁ (fun ω => F (U₁ ω)))
      (law P₂ (fun ω => F (U₂ ω))) ≤ ENNReal.ofReal σ := by
    have hRawCouple := wassersteinE_le_of_coupling π 2 (by norm_num)
      (fun z : X × X => F z.1) (fun z => F z.2)
      ((hF.comp measurable_fst).aemeasurable) ((hF.comp measurable_snd).aemeasurable)
    have hLawRaw₁ : law π (fun z : X × X => F z.1) = law P₁ (fun ω => F (U₁ ω)) := by
      dsimp [law]
      calc
        π.map (F ∘ Prod.fst) = (π.map Prod.fst).map F := (Measure.map_map hF measurable_fst).symm
        _ = (law P₁ U₁).map F := by rw [hπ₁]
        _ = P₁.map (F ∘ U₁) := Measure.map_map hF hU₁
    have hLawRaw₂ : law π (fun z : X × X => F z.2) = law P₂ (fun ω => F (U₂ ω)) := by
      dsimp [law]
      calc
        π.map (F ∘ Prod.snd) = (π.map Prod.snd).map F := (Measure.map_map hF measurable_snd).symm
        _ = (law P₂ U₂).map F := by rw [hπ₂]
        _ = P₂.map (F ∘ U₂) := Measure.map_map hF hU₂
    rw [← hLawRaw₁, ← hLawRaw₂]
    calc
      wassersteinE 2 (law π (fun z : X × X => F z.1))
          (law π (fun z : X × X => F z.2)) ≤
          (∫⁻ z, ENNReal.ofReal (‖F z.1 - F z.2‖ ^ ((2 : ℕ) : ℝ)) ∂π) ^ (1 / (2 : ℝ)) :=
            hRawCouple
      _ = (∫⁻ z, ENNReal.ofReal (‖F z.1 - F z.2‖ ^ 2) ∂π) ^ (1 / (2 : ℝ)) := by
            congr 1
            apply lintegral_congr
            intro z
            congr 1
            rw [Real.rpow_natCast]
      _ ≤ (ENNReal.ofReal (σ ^ 2)) ^ (1 / (2 : ℝ)) :=
            ENNReal.rpow_le_rpow hrawCost (by norm_num)
      _ = ENNReal.ofReal σ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg σ)
          (by norm_num : 0 ≤ (1 / (2 : ℝ)))]
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_nonneg hσ]
  haveI : IsProbabilityMeasure (law P₁ (fun ω => F (U₁ ω))) :=
    (Measure.isProbabilityMeasure_map_iff hF₁.aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure (law P₂ (fun ω => F (U₂ ω))) :=
    (Measure.isProbabilityMeasure_map_iff hF₂.aemeasurable).2 inferInstance
  have hBar := fp81s21_barycenter_wasserstein (fun ω => F (U₁ ω))
    (fun ω => F (U₂ ω)) hF₁ hF₂
  have hW₁₂ := wassersteinE_one_le_two
    (law P₁ (fun ω => F (U₁ ω))) (law P₂ (fun ω => F (U₂ ω)))
  have hmean : ‖m₁ - m₂‖ ≤ σ := by
    have hmeanE : ENNReal.ofReal ‖m₁ - m₂‖ ≤ ENNReal.ofReal σ := by
      simpa [m₁, m₂] using hBar.trans (hW₁₂.trans hRawW)
    exact (ENNReal.ofReal_le_ofReal_iff hσ).1 hmeanE
  have hcenter : ‖c₁ - c₂‖ ≤ σ := by
    have hlin : c₁ - c₂ = Q (m₁ - m₂) := by
      dsimp [c₁, c₂, m₁, m₂]
      rw [map_sub]
    rw [hlin]
    calc
      ‖Q (m₁ - m₂)‖ ≤ ‖Q‖ * ‖m₁ - m₂‖ := Q.le_opNorm _
      _ ≤ 1 * ‖m₁ - m₂‖ := by gcongr
      _ = ‖m₁ - m₂‖ := by ring
      _ ≤ σ := hmean
  have hshift := wassersteinE_translate π 2 (by norm_num)
    (fun z : X × X => F z.2) ((hF.comp measurable_snd).aemeasurable) (-c₁) (-c₂)
  have hShiftLaw : wassersteinE 2 (law P₂ C₂') (law P₂ C₂) ≤ ENNReal.ofReal σ := by
    have hshift' : wassersteinE 2
        (law π (fun z : X × X => F z.2 - c₁))
        (law π (fun z => F z.2 - c₂)) ≤ ENNReal.ofReal ‖c₁ - c₂‖ := by
      have hn : ‖(-c₁) + c₂‖ = ‖c₁ + (-c₂)‖ := by
        rw [show (-c₁) + c₂ = -(c₁ + (-c₂)) by abel, norm_neg]
      simpa [law, sub_eq_add_neg, hn] using hshift
    rw [← hLaw₂, ← hLaw₂']
    exact hshift'.trans (ENNReal.ofReal_le_ofReal hcenter)
  haveI : IsProbabilityMeasure (law P₁ C₁) :=
    (Measure.isProbabilityMeasure_map_iff hFC₁.aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure (law P₂ C₂') :=
    (Measure.isProbabilityMeasure_map_iff hFC₂'.aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure (law P₂ C₂) :=
    (Measure.isProbabilityMeasure_map_iff hFC₂.aemeasurable).2 inferInstance
  have hCenterW : wassersteinE 2 (law P₁ C₁) (law P₂ C₂) ≤
      ENNReal.ofReal (2 * σ) := by
    calc
      wassersteinE 2 (law P₁ C₁) (law P₂ C₂) ≤
          wassersteinE 2 (law P₁ C₁) (law P₂ C₂') +
            wassersteinE 2 (law P₂ C₂') (law P₂ C₂) :=
              wassersteinE_triangle 2 (by norm_num) _ _ _
      _ ≤ ENNReal.ofReal σ + ENNReal.ofReal σ := add_le_add hMid hShiftLaw
      _ = ENNReal.ofReal (2 * σ) := by
        rw [← ENNReal.ofReal_add hσ hσ]
        congr 1
        ring
  have hErr₁cost : ∫⁻ ω, ENNReal.ofReal (‖V₁ ω - C₁ ω‖ ^ 2) ∂P₁ ≤
      ENNReal.ofReal (τ₁ ^ 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hErr₁int
      (ae_of_all P₁ fun ω => by positivity)]
    exact ENNReal.ofReal_le_ofReal hErr₁
  have hErr₂cost : ∫⁻ ω, ENNReal.ofReal (‖V₂ ω - C₂ ω‖ ^ 2) ∂P₂ ≤
      ENNReal.ofReal (τ₂ ^ 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hErr₂int
      (ae_of_all P₂ fun ω => by positivity)]
    exact ENNReal.ofReal_le_ofReal hErr₂
  have hErr₁W := fp81s21_liftTwoLaw_wass_of_sq_cost V₁ C₁
    hV₁.aemeasurable hFC₁.aemeasurable τ₁ hτ₁ hErr₁cost
  have hErr₂costRev : ∫⁻ ω, ENNReal.ofReal (‖C₂ ω - V₂ ω‖ ^ 2) ∂P₂ ≤
      ENNReal.ofReal (τ₂ ^ 2) := by
    calc
      ∫⁻ ω, ENNReal.ofReal (‖C₂ ω - V₂ ω‖ ^ 2) ∂P₂ =
          ∫⁻ ω, ENNReal.ofReal (‖V₂ ω - C₂ ω‖ ^ 2) ∂P₂ := by
            apply lintegral_congr
            intro ω
            rw [norm_sub_rev]
      _ ≤ ENNReal.ofReal (τ₂ ^ 2) := hErr₂cost
  have hErr₂Wrev := fp81s21_liftTwoLaw_wass_of_sq_cost C₂ V₂
    hFC₂.aemeasurable hV₂.aemeasurable τ₂ hτ₂ hErr₂costRev
  haveI : IsProbabilityMeasure (law P₁ V₁) :=
    (Measure.isProbabilityMeasure_map_iff hV₁.aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure (law P₂ V₂) :=
    (Measure.isProbabilityMeasure_map_iff hV₂.aemeasurable).2 inferInstance
  calc
    wassersteinE 2 (law P₁ V₁) (law P₂ V₂) ≤
        wassersteinE 2 (law P₁ V₁) (law P₁ C₁) +
          wassersteinE 2 (law P₁ C₁) (law P₂ V₂) :=
            wassersteinE_triangle 2 (by norm_num) _ _ _
    _ ≤ ENNReal.ofReal τ₁ +
        (wassersteinE 2 (law P₁ C₁) (law P₂ C₂) +
          wassersteinE 2 (law P₂ C₂) (law P₂ V₂)) := by
      exact add_le_add hErr₁W (wassersteinE_triangle 2 (by norm_num) _ _ _)
    _ ≤ ENNReal.ofReal τ₁ + (ENNReal.ofReal (2 * σ) + ENNReal.ofReal τ₂) := by
      gcongr
    _ = ENNReal.ofReal (τ₁ + τ₂ + 2 * σ) := by
      calc
        _ = (ENNReal.ofReal τ₁ + ENNReal.ofReal τ₂) + ENNReal.ofReal (2 * σ) := by ac_rfl
        _ = ENNReal.ofReal (τ₁ + τ₂) + ENNReal.ofReal (2 * σ) := by
          rw [← ENNReal.ofReal_add hτ₁ hτ₂]
        _ = ENNReal.ofReal ((τ₁ + τ₂) + 2 * σ) := by
          rw [← ENNReal.ofReal_add (add_nonneg hτ₁ hτ₂)
            (mul_nonneg (by norm_num) hσ)]
        _ = ENNReal.ofReal (τ₁ + τ₂ + 2 * σ) := by congr 1 <;> ring

#print axioms fp81s21_liftTwoLaw_adapter_of_rawCost

end HRS.Fp81.S21

end
