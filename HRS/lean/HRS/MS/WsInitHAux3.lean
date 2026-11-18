import HRS.MS.WsInitHAux2
import HRS.Main.Headline

/-!
# S21H packet H, part 3: the projection / smoothing assembly of the `W_1` rate `δ^{3/20}` (abstract form)

Setting (everything abstract, no S21 objects): `ι : E →L X` a bounded linear map from the coefficient space `E` (in S21: `ℓ²`
of the feature coordinates `ζ_N(f_{n,j})`) to the path space `X` (`C([0,T];B_m)`), `μ, γ` probability measures on `E` with finite
second moments, `δ ∈ (0,1]`, and

* `hcomp : S21hDerivComp μ γ (√δ) A₁ A₂`: the derivative-only static comparison (merged `StaticFieldConclusion`, 4th conjunct);
* `hscheme`: for every `Q ≥ 1` a coordinate map `c : E → ℝ^p`, an embedding `e : ℝ^p → E` (both of norm `≤ 1`), with `p ≤ K Q²`
  (rank `Q²`: the box `n, j ≤ Q`) and projection tails `∫ ‖v - e c v‖ dμ, ∫ ‖v - e c v‖ dγ ≤ τ Q^{-3/4}`.

Then `W_1^X(ι_*μ, ι_*γ) ≤ ‖ι‖ (2τ + 4√K + A₁ + A₂) δ^{3/20}` (`s21h_w1_abstract`).  Proof: triangle inequality
`ι_*μ → (ι e c)_*μ → (ι e c)_*γ → ι_*γ`; the outer legs are the coupling `(ι, ι e c)` (cost `‖ι‖ τ Q^{-3/4}`), the middle one is
`‖ι e‖ W_1(c_*μ, c_*γ)` (`s21h_w1_coord`); choice `Q = ⌈δ^{-1/5}⌉`, `ε = δ^{7/20}`: all three terms are `≲ δ^{3/20}`
(`Q^{-3/4} = δ^{3/20}`, `ε Q = δ^{3/20}`, `√δ/ε = δ^{3/20}`; the supplement L3589-3601).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal Real

namespace HRS.MS.S21

/-- The exponent bookkeeping for `Q = ⌈δ^{-1/5}⌉`, `ε = δ^{7/20}`. -/
theorem s21h_rate_alg {δ K τ A₁ A₂ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hK : 0 ≤ K) (hτ : 0 ≤ τ) {Q p : ℕ} (hQ1 : δ ^ (-(1 : ℝ) / 5) ≤ Q) (hQ2 : (Q : ℝ) ≤ 2 * δ ^ (-(1 : ℝ) / 5))
    (hp : (p : ℝ) ≤ K * (Q : ℝ) ^ 2) :
    τ / (Q : ℝ) ^ ((3 : ℝ) / 4) ≤ τ * δ ^ ((3 : ℝ) / 20) ∧
      2 * δ ^ ((7 : ℝ) / 20) * Real.sqrt p + Real.sqrt δ * (A₁ + A₂ / δ ^ ((7 : ℝ) / 20)) ≤
        (4 * Real.sqrt K + A₁ + A₂) * δ ^ ((3 : ℝ) / 20) := by
  have hq0 : 0 < δ ^ (-(1 : ℝ) / 5) := Real.rpow_pos_of_pos hδ0 _
  have hQpos : (0 : ℝ) < Q := hq0.trans_le hQ1
  have e1 : δ ^ (-(3 : ℝ) / 20) ≤ (Q : ℝ) ^ ((3 : ℝ) / 4) := by
    calc δ ^ (-(3 : ℝ) / 20) = (δ ^ (-(1 : ℝ) / 5)) ^ ((3 : ℝ) / 4) := by
          rw [← Real.rpow_mul hδ0.le]; congr 1; ring
      _ ≤ (Q : ℝ) ^ ((3 : ℝ) / 4) := Real.rpow_le_rpow hq0.le hQ1 (by norm_num)
  have hd3 : 0 < δ ^ ((3 : ℝ) / 20) := Real.rpow_pos_of_pos hδ0 _
  have hneg : δ ^ (-(3 : ℝ) / 20) = (δ ^ ((3 : ℝ) / 20))⁻¹ := by
    rw [show -(3 : ℝ) / 20 = -((3 : ℝ) / 20) by ring, Real.rpow_neg hδ0.le]
  refine ⟨?_, ?_⟩
  · rw [div_le_iff₀ (Real.rpow_pos_of_pos hQpos _)]
    calc τ = τ * δ ^ ((3 : ℝ) / 20) * (δ ^ ((3 : ℝ) / 20))⁻¹ := by field_simp
      _ ≤ τ * δ ^ ((3 : ℝ) / 20) * (Q : ℝ) ^ ((3 : ℝ) / 4) := by
          rw [hneg] at e1
          gcongr
  · have hsp : Real.sqrt p ≤ Real.sqrt K * ((Q : ℝ)) := by
      calc Real.sqrt p ≤ Real.sqrt (K * (Q : ℝ) ^ 2) := Real.sqrt_le_sqrt hp
        _ = Real.sqrt K * (Q : ℝ) := by
          rw [Real.sqrt_mul hK, Real.sqrt_sq hQpos.le]
    have h7 : δ ^ ((7 : ℝ) / 20) * δ ^ (-(1 : ℝ) / 5) = δ ^ ((3 : ℝ) / 20) := by
      rw [← Real.rpow_add hδ0]; congr 1; ring
    have h7p : 0 < δ ^ ((7 : ℝ) / 20) := Real.rpow_pos_of_pos hδ0 _
    have hA : 2 * δ ^ ((7 : ℝ) / 20) * Real.sqrt p ≤ 4 * Real.sqrt K * δ ^ ((3 : ℝ) / 20) := by
      calc 2 * δ ^ ((7 : ℝ) / 20) * Real.sqrt p ≤
            2 * δ ^ ((7 : ℝ) / 20) * (Real.sqrt K * (2 * δ ^ (-(1 : ℝ) / 5))) := by
            gcongr
            exact hsp.trans (by gcongr)
        _ = 4 * Real.sqrt K * (δ ^ ((7 : ℝ) / 20) * δ ^ (-(1 : ℝ) / 5)) := by ring
        _ = 4 * Real.sqrt K * δ ^ ((3 : ℝ) / 20) := by rw [h7]
    have hs : Real.sqrt δ ≤ δ ^ ((3 : ℝ) / 20) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by norm_num)
    have hB : Real.sqrt δ / δ ^ ((7 : ℝ) / 20) = δ ^ ((3 : ℝ) / 20) := by
      rw [Real.sqrt_eq_rpow, div_eq_iff h7p.ne', ← Real.rpow_add hδ0]; congr 1; norm_num
    have hC : Real.sqrt δ * (A₁ + A₂ / δ ^ ((7 : ℝ) / 20)) ≤ (A₁ + A₂) * δ ^ ((3 : ℝ) / 20) := by
      calc Real.sqrt δ * (A₁ + A₂ / δ ^ ((7 : ℝ) / 20)) = A₁ * Real.sqrt δ + A₂ * (Real.sqrt δ / δ ^ ((7 : ℝ) / 20)) := by
            ring
        _ ≤ A₁ * δ ^ ((3 : ℝ) / 20) + A₂ * δ ^ ((3 : ℝ) / 20) := by
            rw [hB]; gcongr
        _ = (A₁ + A₂) * δ ^ ((3 : ℝ) / 20) := by ring
    nlinarith [hA, hC]


section Abstract

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [CompleteSpace X]

/-- The projection-error leg: `W_1(ι_*μ, (ι∘r)_*μ) ≤ ‖ι‖ ∫ ‖v - r v‖ dμ` for a measurable `r` (both orientations). -/
theorem s21h_leg_tail (ι : E →L[ℝ] X) (μ : Measure E) [IsProbabilityMeasure μ] {r : E → E}
    (hr : Measurable r) {b : ℝ≥0∞} (hb : ∫⁻ v, ‖v - r v‖ₑ ∂μ ≤ b) :
    wassersteinE 1 (μ.map ι) (μ.map (fun v => ι (r v))) ≤ ENNReal.ofReal ‖ι‖ * b ∧
      wassersteinE 1 (μ.map (fun v => ι (r v))) (μ.map ι) ≤ ENNReal.ofReal ‖ι‖ * b := by
  have hιm : Measurable ι := ι.continuous.measurable
  have key : ∫⁻ ω, ENNReal.ofReal ‖ι ω - ι (r ω)‖ ∂μ ≤ ENNReal.ofReal ‖ι‖ * b := by
    calc ∫⁻ ω, ENNReal.ofReal ‖ι ω - ι (r ω)‖ ∂μ ≤ ∫⁻ ω, ENNReal.ofReal ‖ι‖ * ‖ω - r ω‖ₑ ∂μ := by
          refine lintegral_mono fun ω => ?_
          rw [← map_sub, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (ι.le_opNorm _)
      _ = ENNReal.ofReal ‖ι‖ * ∫⁻ ω, ‖ω - r ω‖ₑ ∂μ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ‖ι‖ * b := by gcongr
  constructor
  · have h := HRS.wassersteinE_le_of_coupling μ 1 le_rfl (fun v => ι v) (fun v => ι (r v))
      hιm.aemeasurable (hιm.comp hr).aemeasurable
    refine h.trans ?_
    simpa only [Real.rpow_one, div_one, ENNReal.rpow_one] using key
  · have h := HRS.wassersteinE_le_of_coupling μ 1 le_rfl (fun v => ι (r v)) (fun v => ι v)
      (hιm.comp hr).aemeasurable hιm.aemeasurable
    refine h.trans ?_
    simp only [Real.rpow_one, div_one, ENNReal.rpow_one]
    refine le_trans (le_of_eq ?_) key
    refine lintegral_congr fun ω => ?_
    rw [norm_sub_rev]

/-- The abstract `W_1` rate `δ^{3/20}`. -/
theorem s21h_w1_abstract (ι : E →L[ℝ] X) (μ γ : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure γ]
    (hμ2 : MemLp id 2 μ) (hγ2 : MemLp id 2 γ) {δ A₁ A₂ K τ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hK : 0 ≤ K) (hτ : 0 ≤ τ)
    (hcomp : S21hDerivComp μ γ (Real.sqrt δ) A₁ A₂)
    (hscheme : ∀ Q : ℕ, 1 ≤ Q → ∃ (p : ℕ) (c : E →L[ℝ] EuclideanSpace ℝ (Fin p))
        (e : EuclideanSpace ℝ (Fin p) →L[ℝ] E), ‖c‖ ≤ 1 ∧ ‖e‖ ≤ 1 ∧ (p : ℝ) ≤ K * (Q : ℝ) ^ 2 ∧
        ∫⁻ v, ‖v - e (c v)‖ₑ ∂μ ≤ ENNReal.ofReal (τ / (Q : ℝ) ^ ((3 : ℝ) / 4)) ∧
        ∫⁻ v, ‖v - e (c v)‖ₑ ∂γ ≤ ENNReal.ofReal (τ / (Q : ℝ) ^ ((3 : ℝ) / 4))) :
    wassersteinE 1 (μ.map ι) (γ.map ι) ≤
      ENNReal.ofReal (‖ι‖ * ((2 * τ + 4 * Real.sqrt K + A₁ + A₂) * δ ^ ((3 : ℝ) / 20))) := by
  set Q : ℕ := ⌈δ ^ (-(1 : ℝ) / 5)⌉₊ with hQdef
  have hq1 : 1 ≤ δ ^ (-(1 : ℝ) / 5) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ0 hδ1 (by norm_num)
  have hQ1 : δ ^ (-(1 : ℝ) / 5) ≤ Q := Nat.le_ceil _
  have hQ2 : (Q : ℝ) ≤ 2 * δ ^ (-(1 : ℝ) / 5) := by
    have : (Q : ℝ) < δ ^ (-(1 : ℝ) / 5) + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith [hq1]
  have hQ0 : 1 ≤ Q := by exact_mod_cast hq1.trans hQ1
  obtain ⟨p, c, e, hc, he, hp, hμt, hγt⟩ := hscheme Q hQ0
  have hε : 0 < δ ^ ((7 : ℝ) / 20) := Real.rpow_pos_of_pos hδ0 _
  obtain ⟨hr1, hr2⟩ := s21h_rate_alg hδ0 hδ1 hA₁ hA₂ hK hτ hQ1 hQ2 hp
  set ι' : EuclideanSpace ℝ (Fin p) →L[ℝ] X := ι.comp e with hι'
  have hcm : Measurable c := c.continuous.measurable
  have hem : Measurable e := e.continuous.measurable
  have hrm : Measurable (fun v => e (c v)) := hem.comp hcm
  haveI : IsProbabilityMeasure (μ.map ι) :=
    (Measure.isProbabilityMeasure_map_iff ι.continuous.measurable.aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure (γ.map ι) :=
    (Measure.isProbabilityMeasure_map_iff ι.continuous.measurable.aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure (μ.map (fun v => ι (e (c v)))) :=
    (Measure.isProbabilityMeasure_map_iff (ι.continuous.measurable.comp hrm).aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure (γ.map (fun v => ι (e (c v)))) :=
    (Measure.isProbabilityMeasure_map_iff (ι.continuous.measurable.comp hrm).aemeasurable).2 inferInstance
  have l1 := (s21h_leg_tail ι μ hrm hμt).1
  have l3 := (s21h_leg_tail ι γ hrm hγt).2
  haveI : IsProbabilityMeasure (μ.map c) :=
    (Measure.isProbabilityMeasure_map_iff hcm.aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure (γ.map c) :=
    (Measure.isProbabilityMeasure_map_iff hcm.aemeasurable).2 inferInstance
  have l2a := s21h_w1_coord μ γ hμ2 hγ2 c hc hcomp hε
  have l2b := HRS.Main.wassersteinE_map_clm_le ι' 1 le_rfl (μ.map c) (γ.map c)
  have eμ : (μ.map c).map ι' = μ.map (fun v => ι (e (c v))) := by
    rw [Measure.map_map ι'.continuous.measurable hcm]; rfl
  have eγ : (γ.map c).map ι' = γ.map (fun v => ι (e (c v))) := by
    rw [Measure.map_map ι'.continuous.measurable hcm]; rfl
  rw [eμ, eγ] at l2b
  have hn' : ‖ι'‖ ≤ ‖ι‖ := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    calc ‖ι‖ * ‖e‖ ≤ ‖ι‖ * 1 := by gcongr
      _ = ‖ι‖ := mul_one _
  have tri := wassersteinE_triangle 1 le_rfl (μ.map ι) (μ.map (fun v => ι (e (c v)))) (γ.map ι)
  have tri2 := wassersteinE_triangle 1 le_rfl (μ.map (fun v => ι (e (c v)))) (γ.map (fun v => ι (e (c v))))
    (γ.map ι)
  set t : ℝ := 2 * δ ^ ((7 : ℝ) / 20) * Real.sqrt p + Real.sqrt δ * (A₁ + A₂ / δ ^ ((7 : ℝ) / 20)) with ht
  have hd3 : 0 ≤ δ ^ ((3 : ℝ) / 20) := (Real.rpow_pos_of_pos hδ0 _).le
  have hnι : 0 ≤ ‖ι‖ := norm_nonneg _
  have b1 : ENNReal.ofReal (τ / (Q : ℝ) ^ ((3 : ℝ) / 4)) ≤ ENNReal.ofReal (τ * δ ^ ((3 : ℝ) / 20)) :=
    ENNReal.ofReal_le_ofReal hr1
  have b2 : wassersteinE 1 (μ.map c) (γ.map c) ≤ ENNReal.ofReal ((4 * Real.sqrt K + A₁ + A₂) * δ ^ ((3 : ℝ) / 20)) :=
    l2a.trans (ENNReal.ofReal_le_ofReal hr2)
  have hw : wassersteinE 1 (μ.map ι) (γ.map ι) ≤
      ENNReal.ofReal ‖ι‖ * ENNReal.ofReal (τ * δ ^ ((3 : ℝ) / 20)) +
        (ENNReal.ofReal ‖ι‖ * ENNReal.ofReal ((4 * Real.sqrt K + A₁ + A₂) * δ ^ ((3 : ℝ) / 20)) +
          ENNReal.ofReal ‖ι‖ * ENNReal.ofReal (τ * δ ^ ((3 : ℝ) / 20))) := by
    have c1 : wassersteinE 1 (μ.map ι) (μ.map (fun v => ι (e (c v)))) ≤
        ENNReal.ofReal ‖ι‖ * ENNReal.ofReal (τ * δ ^ ((3 : ℝ) / 20)) :=
      l1.trans (by gcongr)
    have c3 : wassersteinE 1 (γ.map (fun v => ι (e (c v)))) (γ.map ι) ≤
        ENNReal.ofReal ‖ι‖ * ENNReal.ofReal (τ * δ ^ ((3 : ℝ) / 20)) :=
      l3.trans (by gcongr)
    have c2 : wassersteinE 1 (μ.map (fun v => ι (e (c v)))) (γ.map (fun v => ι (e (c v)))) ≤
        ENNReal.ofReal ‖ι‖ * ENNReal.ofReal ((4 * Real.sqrt K + A₁ + A₂) * δ ^ ((3 : ℝ) / 20)) := by
      refine l2b.trans ?_
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal hn') b2
    exact tri.trans (add_le_add c1 (tri2.trans (add_le_add c2 c3)))
  refine hw.trans (le_of_eq ?_)
  have hτd : 0 ≤ τ * δ ^ ((3 : ℝ) / 20) := mul_nonneg hτ hd3
  have hKd : 0 ≤ (4 * Real.sqrt K + A₁ + A₂) * δ ^ ((3 : ℝ) / 20) :=
    mul_nonneg (by positivity) hd3
  rw [← ENNReal.ofReal_mul hnι, ← ENNReal.ofReal_mul hnι, ← ENNReal.ofReal_add (mul_nonneg hnι hKd)
    (mul_nonneg hnι hτd), ← ENNReal.ofReal_add (mul_nonneg hnι hτd) (add_nonneg (mul_nonneg hnι hKd)
    (mul_nonneg hnι hτd))]
  congr 1
  ring

end Abstract

end HRS.MS.S21
