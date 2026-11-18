import Mathlib

/-!
# S81G, packet G3: relative-entropy facts

* `s81g_kl_dom`: one-sided domination `c Q ≤ Q'` (probability measures) gives
  `H(η | Q') ≤ H(η | Q) - log c` (both finite when the right side is), no integrability assumption on a density;
* `s81g_exp_moment`, `s81g_second_moment`: a Gibbs law `sb1Gam D k N` with the Gaussian majorant has
  `H(η | Γ) < ∞  ⇒  ∫ ‖x‖² dη < ∞`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S81G

theorem s81g_klFun_bound {v w c : ℝ} (hv : 0 ≤ v) (hw : 0 ≤ w) (hc : 0 < c) (hwc : c * w ≤ 1) :
    klFun (v * w) ≤ w * klFun v - Real.log c * (v * w) + 1 - w := by
  rcases hw.eq_or_lt with h0 | hwp
  · subst h0; simp [klFun]
  rcases hv.eq_or_lt with h0 | hvp
  · subst h0; simp [klFun]
  have hw1 : w ≤ 1 / c := (le_div_iff₀ hc).2 (by linarith [mul_comm c w])
  have hlogw : Real.log w ≤ -Real.log c := by
    have := Real.log_le_log hwp hw1
    rwa [one_div, Real.log_inv] at this
  have hlog : Real.log (v * w) = Real.log v + Real.log w := Real.log_mul hvp.ne' hwp.ne'
  unfold klFun
  rw [hlog]
  nlinarith [mul_le_mul_of_nonneg_left hlogw (mul_nonneg hv hw)]

theorem s81g_kl_dom {α : Type*} [MeasurableSpace α] (η Q Q' : Measure α)
    [IsProbabilityMeasure η] [IsProbabilityMeasure Q] [IsProbabilityMeasure Q']
    {c : ℝ} (hc : 0 < c) (hdom : ENNReal.ofReal c • Q ≤ Q') (hfin : klDiv η Q ≠ ⊤) :
    klDiv η Q' ≠ ⊤ ∧ (klDiv η Q').toReal ≤ (klDiv η Q).toReal - Real.log c := by
  obtain ⟨hηQ, hint⟩ := klDiv_ne_top_iff.1 hfin
  have hQQ' : Q ≪ Q' := by
    intro A hA
    have h1 := hdom A
    rw [hA, Measure.smul_apply, smul_eq_mul] at h1
    exact (mul_eq_zero.1 (le_antisymm h1 bot_le)).resolve_left (ENNReal.ofReal_pos.2 hc).ne'
  have hηQ' : η ≪ Q' := hηQ.trans hQQ'
  set v : α → ℝ := fun x => (η.rnDeriv Q x).toReal with hvdef
  set w : α → ℝ := fun x => (Q.rnDeriv Q' x).toReal with hwdef
  set u : α → ℝ := fun x => (η.rnDeriv Q' x).toReal with hudef
  have hu : ∀ᵐ x ∂Q', u x = v x * w x := by
    filter_upwards [Measure.rnDeriv_mul_rnDeriv hηQ (κ := Q')] with x hx
    simp only [hudef, hvdef, hwdef]
    rw [← ENNReal.toReal_mul, ← Pi.mul_apply, hx]
  have hwle : ∀ᵐ x ∂Q', c * w x ≤ 1 := by
    filter_upwards [Measure.rnDeriv_le_one_of_le hdom,
      Measure.rnDeriv_smul_left_of_ne_top Q Q' (ENNReal.ofReal_ne_top (r := c)),
      Measure.rnDeriv_lt_top Q Q'] with x hx1 hx2 hx3
    rw [hx2] at hx1
    simp only [Pi.smul_apply, smul_eq_mul, Pi.one_apply] at hx1
    have := ENNReal.toReal_mono ENNReal.one_ne_top hx1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le, ENNReal.toReal_one] at this
  have hwI : Integrable w Q' := Measure.integrable_toReal_rnDeriv
  have huI : Integrable u Q' := Measure.integrable_toReal_rnDeriv
  have hvwI : Integrable (fun x => v x * w x) Q' := huI.congr hu
  have hkv : Integrable (fun x => klFun (v x)) Q := (integrable_klFun_rnDeriv_iff hηQ).2 hint
  have hwk : Integrable (fun x => w x * klFun (v x)) Q' :=
    (integrable_toReal_rnDeriv_mul_iff hQQ').2 hkv
  have i3 : Integrable (fun x => Real.log c * (v x * w x)) Q' := hvwI.const_mul _
  have i1 : Integrable (fun x => w x * klFun (v x) - Real.log c * (v x * w x)) Q' := hwk.sub i3
  have i2 : Integrable (fun x => w x * klFun (v x) - Real.log c * (v x * w x) + 1) Q' :=
    i1.add (integrable_const 1)
  have hBI : Integrable (fun x => w x * klFun (v x) - Real.log c * (v x * w x) + 1 - w x) Q' :=
    i2.sub hwI
  have hbd : ∀ᵐ x ∂Q', klFun (u x) ≤ w x * klFun (v x) - Real.log c * (v x * w x) + 1 - w x := by
    filter_upwards [hu, hwle] with x hx1 hx2
    rw [hx1]
    exact s81g_klFun_bound ENNReal.toReal_nonneg ENNReal.toReal_nonneg hc hx2
  have hkI : Integrable (fun x => klFun (u x)) Q' := by
    refine hBI.mono' ?_ ?_
    · exact (measurable_klFun.comp (Measure.measurable_rnDeriv η Q').ennreal_toReal).aestronglyMeasurable
    · filter_upwards [hbd] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (klFun_nonneg ENNReal.toReal_nonneg)]
      exact hx
  have hint' : Integrable (llr η Q') η := (integrable_klFun_rnDeriv_iff hηQ').1 hkI
  refine ⟨klDiv_ne_top hηQ' hint', ?_⟩
  rw [toReal_klDiv_eq_integral_klFun hηQ']
  have h1 : ∫ x, klFun (u x) ∂Q' ≤ ∫ x, (w x * klFun (v x) - Real.log c * (v x * w x) + 1 - w x) ∂Q' :=
    integral_mono_ae hkI hBI hbd
  refine h1.trans (le_of_eq ?_)
  have e1 : ∫ x, w x * klFun (v x) ∂Q' = (klDiv η Q).toReal := by
    rw [toReal_klDiv_eq_integral_klFun hηQ]
    exact integral_toReal_rnDeriv_mul hQQ'
  have e2 : ∫ x, v x * w x ∂Q' = 1 := by
    have : ∫ x, v x * w x ∂Q' = ∫ x, u x ∂Q' := integral_congr_ae (hu.mono fun x h => h.symm)
    rw [this]
    simp [hudef, Measure.integral_toReal_rnDeriv hηQ']
  have e3 : ∫ x, w x ∂Q' = 1 := by
    simp [hwdef, Measure.integral_toReal_rnDeriv hQQ']
  rw [integral_sub i2 hwI, integral_add i1 (integrable_const 1), integral_sub hwk i3,
    integral_const_mul, e1, e2, e3]
  simp

end HRS.MS.S81G
