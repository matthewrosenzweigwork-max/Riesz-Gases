import HRS.Commutator.Torus.TEXTAux9
import HRS.Commutator.Torus.TEXTAux2

/-!
# T-EXT-A helpers, part 10: `L^p → L^q` bound for convolution with a kernel `≲ tdist^{σ-d}`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

lemma text_exps (hd : 1 ≤ d) {σ : ℝ} (p q : ℝ≥0∞) (hp : 1 < p) (hpq : p < q) (hq : q < ⊤)
    (hσ : 0 < σ) (hrel : q⁻¹ = p⁻¹ - ENNReal.ofReal (σ / d)) :
    1 < p.toReal ∧ p.toReal < q.toReal ∧ 1 / q.toReal = 1 / p.toReal - σ / d ∧ σ < d := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hpt : p ≠ ⊤ := (hpq.trans hq).ne
  have hqt : q ≠ ⊤ := hq.ne
  have h1 : 1 < p.toReal := by
    have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hpt).2 hp
    simpa using this
  have h2 : p.toReal < q.toReal := (ENNReal.toReal_lt_toReal hpt hqt).2 hpq
  have hx : ENNReal.ofReal (σ / d) ≤ p⁻¹ := by
    by_contra hcon
    push Not at hcon
    have : p⁻¹ - ENNReal.ofReal (σ / d) = 0 := tsub_eq_zero_of_le hcon.le
    rw [← hrel] at this
    exact hqt (ENNReal.inv_eq_zero.1 this)
  have h3 : 1 / q.toReal = 1 / p.toReal - σ / d := by
    have := congrArg ENNReal.toReal hrel
    rw [ENNReal.toReal_inv, ENNReal.toReal_sub_of_le hx (ENNReal.inv_ne_top.2 (by
      intro h0; rw [h0] at hp; exact absurd hp (by simp))),
      ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity)] at this
    simpa [one_div] using this
  refine ⟨h1, h2, h3, ?_⟩
  have hq0 : 0 < 1 / q.toReal := by
    have : 0 < q.toReal := by linarith
    positivity
  have hp1 : 1 / p.toReal < 1 := by
    rw [div_lt_one (by linarith)]; exact h1
  have : σ / d < 1 := by linarith
  rwa [div_lt_one hdpos] at this

lemma text_conv_Lq (hd : 1 ≤ d) {σ : ℝ} (p q : ℝ≥0∞) (hp : 1 < p) (hpq : p < q) (hq : q < ⊤)
    (hσ : 0 < σ) (hrel : q⁻¹ = p⁻¹ - ENNReal.ofReal (σ / d)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K f : Torus d → ℝ) (C' : ℝ), 0 ≤ C' → Integrable K →
      (∀ z : Torus d, z ≠ 0 → |K z| ≤ C' * KernelGrad.tdist z 0 ^ (σ - d)) →
      MemLp f p volume →
      MemLp (textConv K f) q volume ∧
        eLpNorm (textConv K f) q volume ≤ ENNReal.ofReal (C * C') * eLpNorm f p volume := by
  obtain ⟨hp1, hpq1, hrel1, hσd⟩ := text_exps hd p q hp hpq hq hσ hrel
  have hpt : p ≠ ⊤ := (hpq.trans hq).ne
  have hqt : q ≠ ⊤ := hq.ne
  set pr := p.toReal with hpr
  set qr := q.toReal with hqr
  have hqr1 : 1 < qr := by linarith
  obtain ⟨Ct, hCt, htr⟩ := text_transfer hd hσ hp1 hpq1 hrel1
  set Cq : ℝ≥0∞ := Ct ^ (1 / qr) with hCq
  have hCqt : Cq ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hCt
  refine ⟨Cq.toReal + 1, by positivity, fun K f C' hC' hK hb hf => ?_⟩
  have hf1 : Integrable f := hf.integrable hp.le
  have hconvm : AEStronglyMeasurable (textConv K f) volume :=
    (text_integrable_conv hK hf1).aestronglyMeasurable
  -- the main estimate
  have hmain : eLpNorm (textConv K f) q volume ≤ ENNReal.ofReal C' * Cq * eLpNorm f p volume := by
    classical
    set fm := hf.aestronglyMeasurable.mk f with hfm
    have hae : f =ᵐ[volume] fm := hf.aestronglyMeasurable.ae_eq_mk
    have hfmm : Measurable fm := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
    set g : Torus d → ℝ≥0 := fun y => ‖fm y‖₊ with hg
    have hgm : Measurable g := hfmm.nnnorm
    set Φ : Torus d → ℝ≥0∞ := fun x =>
      ∫⁻ y, ENNReal.ofReal (KernelGrad.tdist x y ^ (σ - d)) * (g y : ℝ≥0∞) with hΦ
    have hpt1 : ∀ x : Torus d, ‖textConv K f x‖ₑ ≤ ENNReal.ofReal C' * Φ x := by
      intro x
      unfold textConv
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      rw [hΦ]
      simp only
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono_ae ?_
      filter_upwards [text_ae_ne hd x, hae] with y hyx hy
      rw [enorm_mul]
      have hz : x - y ≠ 0 := sub_ne_zero.2 (Ne.symm hyx)
      have h1 := hb (x - y) hz
      have h2 : ‖K (x - y)‖ₑ ≤ ENNReal.ofReal C' *
          ENNReal.ofReal (KernelGrad.tdist x y ^ (σ - d)) := by
        rw [← ENNReal.ofReal_mul hC', Real.enorm_eq_ofReal_abs]
        refine ENNReal.ofReal_le_ofReal ?_
        have : KernelGrad.tdist (x - y) 0 = KernelGrad.tdist x y := by
          simp [KernelGrad.tdist]
        rw [this] at h1
        exact h1
      rw [hy, ← mul_assoc]
      refine mul_le_mul' h2 ?_
      simp [hg, enorm_eq_nnnorm]
    have hqr0 : 0 < qr := by linarith
    have hq0 : q ≠ 0 := (zero_lt_one.trans (hp.trans hpq)).ne'
    have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
    have hpr0 : 0 < pr := by linarith
    have hfeq : eLpNorm f p volume = (∫⁻ y, (g y : ℝ≥0∞) ^ pr) ^ (1 / pr) := by
      rw [eLpNorm_congr_ae hae,
        eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hfmm.aestronglyMeasurable]
      have : ∀ y, ‖fm y‖ₑ ^ p.toReal = (g y : ℝ≥0∞) ^ pr := fun y => by
        simp [hg, enorm_eq_nnnorm, hpr]
      simp_rw [this]
      rfl
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt hconvm, hfeq]
    calc (∫⁻ x, ‖textConv K f x‖ₑ ^ qr) ^ (1 / qr)
        ≤ (∫⁻ x, (ENNReal.ofReal C' * Φ x) ^ qr) ^ (1 / qr) :=
          ENNReal.rpow_le_rpow (lintegral_mono fun x => ENNReal.rpow_le_rpow (hpt1 x) hqr0.le)
            (by positivity)
      _ = ENNReal.ofReal C' * (∫⁻ x, Φ x ^ qr) ^ (1 / qr) := by
          simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hqr0.le]
          rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hqr0.le ENNReal.ofReal_ne_top),
            ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
            mul_one_div_cancel hqr0.ne', ENNReal.rpow_one]
      _ ≤ ENNReal.ofReal C' * (Ct * (∫⁻ y, (g y : ℝ≥0∞) ^ pr) ^ (qr / pr)) ^ (1 / qr) := by
          refine mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (htr g hgm) (by positivity))
      _ = ENNReal.ofReal C' * Cq * (∫⁻ y, (g y : ℝ≥0∞) ^ pr) ^ (1 / pr) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, hCq, mul_assoc]
          congr 3
          field_simp
  refine ⟨memLp_iff.2 (lt_of_le_of_lt hmain (ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hCqt.lt_top) hf.eLpNorm_lt_top)), ?_⟩
  refine hmain.trans (mul_le_mul' ?_ le_rfl)
  have hCq' : Cq = ENNReal.ofReal Cq.toReal := (ENNReal.ofReal_toReal hCqt).symm
  calc ENNReal.ofReal C' * Cq = ENNReal.ofReal C' * ENNReal.ofReal Cq.toReal := by rw [← hCq']
    _ = ENNReal.ofReal (C' * Cq.toReal) := (ENNReal.ofReal_mul hC').symm
    _ ≤ ENNReal.ofReal ((Cq.toReal + 1) * C') :=
        ENNReal.ofReal_le_ofReal (by nlinarith [ENNReal.toReal_nonneg (a := Cq)])

end HRS.Commutator.TorusNote
