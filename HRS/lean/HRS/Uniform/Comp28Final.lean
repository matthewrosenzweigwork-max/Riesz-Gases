import HRS.Uniform.Comparison
import HRS.Uniform.Comp28Aux8
import HRS.Uniform.Comp28W11

/-!
# COMP-28 final: Proposition 3.28 (`comparison_smooth`, relocated proof)

`HRS/Uniform/Comparison.lean` cannot import this file; the statements are repeated verbatim as `*_proof` and tied to the
frozen statements by `example := (@..._proof : type_of% @HRS.Uniform....)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Uniform

universe u

theorem comparison_smooth_proof (K c : ℝ) (hK : 0 ≤ K) (hc : 0 ≤ c) (a T : ℝ) (ha : 0 ≤ a) (hT : 0 ≤ T)
    (Ω : Type*) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ)
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (V : ℝ → ℝ → H →L[ℝ] H) (hEv : IsPlainEvolution V (a + T))
    (hVb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ a + T → ‖V t r‖ ≤ K * Real.exp (-c * (t - r)))
    (X₀ X₀' : Ω → H) (hX₀ : Measurable[ℱ 0] X₀) (hX₀' : Measurable[ℱ 0] X₀')
    (M : ℝ → Ω → H) (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ))
    (hM : IsHilbertMartingaleWithCovariation P ℱ (a + T) M Sg)
    (G : ℝ → Ω → H) (Cb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)) (hCb : IsDetCovDensity (a + T) Cb)
    (hG : IsHilbertMartingaleWithCovariation P ℱ (a + T) G (fun r _ => Cb r))
    (Z Zb R : ℝ → Ω → H)
    (hZ : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), IsStochConv P V (ContinuousLinearMap.id ℝ H) M 0 t (Z t))
    (hZb : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), IsStochConv P V (ContinuousLinearMap.id ℝ H) G 0 t (Zb t))
    (hZc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 (a + T)))
    (hZbc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Zb t ω) (Set.Icc 0 (a + T)))
    (hRc : ∀ᵐ ω ∂P, ContinuousOn (fun t => R t ω) (Set.Icc 0 (a + T)))
    (hZm : ∀ t, Measurable (Z t)) (hZbm : ∀ t, Measurable (Zb t)) (hRm : ∀ t, Measurable (R t))
    (X Xb : ℝ → Ω → H)
    (hXd : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), ∀ ω, X t ω = V t 0 (X₀ ω) + Z t ω + R t ω)
    (hXbd : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), ∀ ω, Xb t ω = V t 0 (X₀' ω) + Zb t ω) :
    ENNReal.ofReal (smoothDist 2 (law P (windowPath a T X)) (law P (windowPath a T Xb))) ≤
      ENNReal.ofReal (K * Real.exp (-c * a)) * ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P +
        ∫⁻ ω, ‖windowPath a T R ω‖ₑ ∂P +
        ENNReal.ofReal (K ^ 2 / 2) *
          ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T),
            ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 * traceNormForm (Sg r ω - Cb r))) ∂P := by
  rcases (add_nonneg ha hT).eq_or_lt with h0 | hpos
  · have ha0 : a = 0 := by linarith
    have hT0 : T = 0 := by linarith
    subst ha0 hT0
    have hmem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (0 + 0) := ⟨le_rfl, by norm_num⟩
    have hV00 : V 0 0 = 1 := hEv.1 0 hmem
    have hVb0 : ‖V 0 0‖ ≤ K := by
      have := hVb 0 0 le_rfl le_rfl (by norm_num)
      simpa using this
    refine (Comp28.smooth_zero_w P hK hc ℱ V hV00 hVb0 X₀ X₀' hX₀ hX₀' M Sg G Cb Z Zb R (hZ 0 hmem) (hZb 0 hmem)
      hZm hZbm hRm X Xb (fun ω => ?_) (fun ω => ?_)).trans ?_
    · have := hXd 0 hmem ω
      rwa [hV00] at this ⊢
    · have := hXbd 0 hmem ω
      rwa [hV00] at this ⊢
    · simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
      exact le_self_add
  · exact Comp28.smooth_pos_w P ha hT hpos hK hc ℱ V hEv.2.2 hVb X₀ X₀' hX₀ hX₀' M Sg hM G Cb hCb hG Z Zb R hZ hZb
      hZc hZbc hRc hZm hZbm hRm X Xb hXd hXbd

example := (@comparison_smooth_proof : type_of% @HRS.Uniform.comparison_smooth)

theorem comparison_wasserstein_proof (K c T Cmax : ℝ) (hK : 0 ≤ K) (hc : 0 ≤ c) (hT : 0 ≤ T) (p : ℝ)
    (hp : p = 1 ∨ p = 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 ≤ a →
    ∀ (Ω : Type u) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ mΩ)
      (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
      (V : ℝ → ℝ → H →L[ℝ] H) (_ : IsPlainEvolution V (a + T))
      (_ : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ a + T → ‖V t r‖ ≤ K * Real.exp (-c * (t - r)))
      (_ : MaxWindows.{u, _} V T Cmax)
      (X₀ X₀' : Ω → H) (_ : Measurable[ℱ 0] X₀) (_ : Measurable[ℱ 0] X₀')
      {κ : Type} [Countable κ] (W : ℝ≥0 → Ω → κ → ℝ) (_ : IsCylindricalBrownian P ℱ W)
      (Φ : ℝ → Ω → κ → H) (_ : ∀ T' : ℝ, IsHSIntegrand P ℱ T' Φ)
      (M : ℝ → Ω → H) (_ : IsHilbertItoIntegral P ℱ W Φ M)
      (G : ℝ → Ω → H) (Cb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)) (_ : IsDetCovDensity (a + T) Cb)
      (_ : IsHilbertMartingaleWithCovariation P ℱ (a + T) G (fun r _ => Cb r))
      (Z Zb R : ℝ → Ω → H)
      (_ : ∀ t ∈ Set.Icc (0 : ℝ) (a + T),
        IsStochConv P V (ContinuousLinearMap.id ℝ H) M 0 t (Z t))
      (_ : ∀ t ∈ Set.Icc (0 : ℝ) (a + T),
        IsStochConv P V (ContinuousLinearMap.id ℝ H) G 0 t (Zb t))
      (_ : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 (a + T)))
      (_ : ∀ᵐ ω ∂P, ContinuousOn (fun t => Zb t ω) (Set.Icc 0 (a + T)))
      (_ : ∀ᵐ ω ∂P, ContinuousOn (fun t => R t ω) (Set.Icc 0 (a + T)))
      (_ : ∀ t, Measurable (Z t)) (_ : ∀ t, Measurable (Zb t)) (_ : ∀ t, Measurable (R t))
      (X Xb : ℝ → Ω → H)
      (_ : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), ∀ ω, X t ω = V t 0 (X₀ ω) + Z t ω + R t ω)
      (_ : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), ∀ ω, Xb t ω = V t 0 (X₀' ω) + Zb t ω),
      wassersteinE p (law P (windowPath a T X)) (law P (windowPath a T Xb)) ≤
        ENNReal.ofReal (C * Real.exp (-c * a)) * (∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ^ p ∂P) ^ (1 / p) +
          (∫⁻ ω, ‖windowPath a T R ω‖ₑ ^ p ∂P) ^ (1 / p) +
          ENNReal.ofReal C *
            (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T), ENNReal.ofReal
              (Real.exp (-c * max (a - r) 0) ^ 2 *
                traceNormForm (hsCovForm (Φ r ω) - Cb r))) ∂P) ^ (1 / 2 : ℝ) := by
  exact Comp28.wasserstein_main K c T Cmax hK hc hT p hp

example := (@comparison_wasserstein_proof : type_of% @HRS.Uniform.comparison_wasserstein)

end Uniform

end HRS
