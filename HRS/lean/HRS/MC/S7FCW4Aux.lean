import HRS.MC.S7FCDefs

/-!
# Auxiliary entropy facts for the `field_chaos` packets D1/D2 (worker fcw4)

* `S7FCW4_x_log_x_le`, `S7FCW4_x_log_x_ge`, `S7FCW4_abs_x_log_x_le`: elementary inequalities for `x log x`.
* `S7FCW4_kl_le_of_Lp`: for probability measures `Q0 ≪ Q` whose density `h = dQ0/dQ` lies in `L^p(Q)`
  with `‖h‖_p ≤ M`, `klDiv Q0 Q ≤ ofReal ((M^p - 1)/(p - 1))`.
-/

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCW4

/-- `x log x ≤ (x^p - x)/(p-1)` for `x ≥ 0`, `p > 1`. -/
lemma S7FCW4_x_log_x_le {p x : ℝ} (hp : 1 < p) (hx : 0 ≤ x) :
    x * Real.log x ≤ (x ^ p - x) / (p - 1) := by
  have hp1 : 0 < p - 1 := by linarith
  rcases hx.eq_or_lt with h0 | hpos
  · subst h0
    simp [Real.zero_rpow (show p ≠ 0 by linarith)]
  · have h1 : Real.log (x ^ (p - 1)) ≤ x ^ (p - 1) - 1 :=
      Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hpos _)
    rw [Real.log_rpow hpos] at h1
    have hxp : x ^ p = x * x ^ (p - 1) := by
      conv_lhs => rw [show p = 1 + (p - 1) by ring]
      rw [Real.rpow_add hpos, Real.rpow_one]
    rw [le_div_iff₀ hp1]
    have h2 := mul_le_mul_of_nonneg_left h1 hx
    nlinarith [h2, hxp]

/-- `x log x ≥ -1` for `x ≥ 0`. -/
lemma S7FCW4_x_log_x_ge {x : ℝ} (hx : 0 ≤ x) : -1 ≤ x * Real.log x := by
  rcases hx.eq_or_lt with h0 | hpos
  · subst h0; simp
  · have h1 : Real.log x⁻¹ ≤ x⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.2 hpos)
    rw [Real.log_inv] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 hx
    have h3 : x * x⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
    nlinarith [h2, h3]

/-- `|x log x| ≤ 1 + x^p/(p-1)` for `x ≥ 0`, `p > 1`. -/
lemma S7FCW4_abs_x_log_x_le {p x : ℝ} (hp : 1 < p) (hx : 0 ≤ x) :
    |x * Real.log x| ≤ 1 + x ^ p / (p - 1) := by
  have hp1 : 0 < p - 1 := by linarith
  have hxp : 0 ≤ x ^ p := Real.rpow_nonneg hx p
  have hu := S7FCW4_x_log_x_le hp hx
  have hdiv : (x ^ p - x) / (p - 1) ≤ x ^ p / (p - 1) :=
    div_le_div_of_nonneg_right (by linarith [hx]) hp1.le
  have hd0 : 0 ≤ x ^ p / (p - 1) := div_nonneg hxp hp1.le
  have hl := S7FCW4_x_log_x_ge hx
  rw [abs_le]
  constructor <;> linarith

/-- Entropy from an `L^p` density bound: for probability measures `Q0 ≪ Q` with `‖dQ0/dQ‖_{L^p(Q)} ≤ M`
(`p > 1`, `M ≥ 0`), `H(Q0 | Q) = klDiv Q0 Q ≤ (M^p - 1)/(p - 1)`. -/
lemma S7FCW4_kl_le_of_Lp {α : Type*} [MeasurableSpace α] (Q0 Q : Measure α)
    [IsProbabilityMeasure Q0] [IsProbabilityMeasure Q] (hac : Q0 ≪ Q) {p M : ℝ} (hp : 1 < p) (hM : 0 ≤ M)
    (hL : eLpNorm (fun x => (Q0.rnDeriv Q x).toReal) (ENNReal.ofReal p) Q ≤ ENNReal.ofReal M) :
    klDiv Q0 Q ≤ ENNReal.ofReal ((M ^ p - 1) / (p - 1)) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  set h : α → ℝ := fun x => (Q0.rnDeriv Q x).toReal with hh
  have hmeas : Measurable h := (Measure.measurable_rnDeriv Q0 Q).ennreal_toReal
  have hpR : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hpne0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp0).ne'
  have hpneTop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hMemLp : MemLp h (ENNReal.ofReal p) Q := lt_of_le_of_lt hL ENNReal.ofReal_lt_top
  have hIp : Integrable (fun x => ‖h x‖ ^ p) Q := by
    have := hMemLp.integrable_norm_rpow hpne0 hpneTop
    rwa [hpR] at this
  have hIntp : ∫ x, ‖h x‖ ^ p ∂Q ≤ M ^ p := by
    have e := hMemLp.eLpNorm_eq_integral_rpow_norm hpne0 hpneTop
    rw [hpR] at e
    rw [e] at hL
    have h2 : (∫ x, ‖h x‖ ^ p ∂Q) ^ p⁻¹ ≤ M := (ENNReal.ofReal_le_ofReal_iff hM).1 hL
    have hnn : 0 ≤ ∫ x, ‖h x‖ ^ p ∂Q := integral_nonneg fun x => by positivity
    have h3 : ((∫ x, ‖h x‖ ^ p ∂Q) ^ p⁻¹) ^ p ≤ M ^ p :=
      Real.rpow_le_rpow (Real.rpow_nonneg hnn _) h2 hp0.le
    rwa [← Real.rpow_mul hnn, inv_mul_cancel₀ hp0.ne', Real.rpow_one] at h3
  have hIh : Integrable h Q := by
    have := (integrable_rnDeriv_smul_iff hac (f := fun _ : α => (1 : ℝ))).2 (integrable_const (1 : ℝ))
    simpa [hh, smul_eq_mul] using this
  have hlog : Integrable (fun x => h x * Real.log (h x)) Q := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add (hIp.div_const (p - 1)))
      (hmeas.mul (Real.measurable_log.comp hmeas)).aestronglyMeasurable ?_
    refine Eventually.of_forall fun x => ?_
    have hx : 0 ≤ h x := ENNReal.toReal_nonneg
    have key := S7FCW4_abs_x_log_x_le hp hx
    show ‖h x * Real.log (h x)‖ ≤ 1 + ‖h x‖ ^ p / (p - 1)
    rw [Real.norm_eq_abs, Real.norm_of_nonneg hx]
    exact key
  have hllr : Integrable (llr Q0 Q) Q0 := by
    rw [← integrable_rnDeriv_smul_iff hac]
    refine hlog.congr (Eventually.of_forall fun x => ?_)
    simp [llr, smul_eq_mul, hh]
  rw [klDiv_of_ac_of_integrable hac hllr]
  apply ENNReal.ofReal_le_ofReal
  have hchg : ∫ x, llr Q0 Q x ∂Q0 = ∫ x, h x * Real.log (h x) ∂Q := by
    rw [← integral_rnDeriv_smul (f := llr Q0 Q) hac]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [llr, smul_eq_mul, hh]
  have hint1 : ∫ x, h x ∂Q = 1 := by
    have := integral_rnDeriv_smul (f := fun _ : α => (1 : ℝ)) hac
    simpa [hh, smul_eq_mul] using this
  have hIle : ∫ x, h x * Real.log (h x) ∂Q ≤ (M ^ p - 1) / (p - 1) := by
    have hg : Integrable (fun x => (‖h x‖ ^ p - h x) / (p - 1)) Q :=
      (hIp.sub hIh).div_const _
    calc ∫ x, h x * Real.log (h x) ∂Q ≤ ∫ x, (‖h x‖ ^ p - h x) / (p - 1) ∂Q := by
          refine integral_mono hlog hg fun x => ?_
          have hx : 0 ≤ h x := ENNReal.toReal_nonneg
          rw [Real.norm_of_nonneg hx]
          exact S7FCW4_x_log_x_le hp hx
      _ = (∫ x, ‖h x‖ ^ p ∂Q - ∫ x, h x ∂Q) / (p - 1) := by
          rw [integral_div, integral_sub hIp hIh]
      _ ≤ (M ^ p - 1) / (p - 1) := by
          rw [hint1]
          exact div_le_div_of_nonneg_right (by linarith [hIntp]) hp1.le
  have hQ0 : Q0.real Set.univ = 1 := probReal_univ
  have hQ : Q.real Set.univ = 1 := probReal_univ
  rw [hQ0, hQ, hchg]
  linarith [hIle]

end HRS.MC.Sec7.S7FCW4

end
