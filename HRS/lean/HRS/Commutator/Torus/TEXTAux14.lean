import HRS.Commutator.Torus.TEXTAux2
import HRS.Commutator.Torus.TEXTAux13

/-!
# T-EXT-A helpers, part 14: interpolation and Hölder estimates on the torus (for `bernstein_T`)
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

/-- Interpolation: `‖f‖_q ≤ M^{(q-p)/q} ‖f‖_p^{p/q}` when `‖f‖_∞ ≤ M < ∞`. -/
lemma text_interp {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ} {p q : ℝ≥0∞}
    (hp : 1 ≤ p) (hpq : p ≤ q) (hq : q < ⊤) (hf : MemLp f p μ) {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hbd : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ M) :
    eLpNorm f q μ ≤ M ^ ((q.toReal - p.toReal) / q.toReal) * (eLpNorm f p μ) ^ (p.toReal / q.toReal) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hpt : p ≠ ⊤ := ne_top_of_le_ne_top hq.ne hpq
  have hq0 : q ≠ 0 := (lt_of_lt_of_le (zero_lt_one.trans_le hp) hpq).ne'
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hs : 0 < q.toReal := ENNReal.toReal_pos hq0 hq.ne
  have hrs : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq.ne hpq
  have hmeas := hf.aestronglyMeasurable
  have hB : eLpNorm f p μ = (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) :=
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hmeas
  have hIB : (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) = (eLpNorm f p μ) ^ p.toReal := by
    rw [hB, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hr.ne', ENNReal.rpow_one]
  have hpoint : ∀ᵐ x ∂μ, ‖f x‖ₑ ^ q.toReal ≤ M ^ (q.toReal - p.toReal) * ‖f x‖ₑ ^ p.toReal := by
    filter_upwards [hbd] with x hx
    have e : ‖f x‖ₑ ^ q.toReal = ‖f x‖ₑ ^ (q.toReal - p.toReal) * ‖f x‖ₑ ^ p.toReal := by
      rw [← ENNReal.rpow_add_of_nonneg (x := ‖f x‖ₑ) (q.toReal - p.toReal) p.toReal
        (sub_nonneg.2 hrs) hr.le, sub_add_cancel]
    rw [e]
    gcongr
  have hlint : ∫⁻ x, ‖f x‖ₑ ^ q.toReal ∂μ
      ≤ M ^ (q.toReal - p.toReal) * ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ := by
    calc ∫⁻ x, ‖f x‖ₑ ^ q.toReal ∂μ
        ≤ ∫⁻ x, M ^ (q.toReal - p.toReal) * ‖f x‖ₑ ^ p.toReal ∂μ := lintegral_mono_ae hpoint
      _ = M ^ (q.toReal - p.toReal) * ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ :=
          lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.2 hrs) hM)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq.ne hmeas]
  calc (∫⁻ x, ‖f x‖ₑ ^ q.toReal ∂μ) ^ (1 / q.toReal)
      ≤ (M ^ (q.toReal - p.toReal) * ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ^ (1 / q.toReal) :=
        ENNReal.rpow_le_rpow hlint (by positivity)
    _ = M ^ ((q.toReal - p.toReal) / q.toReal) * (eLpNorm f p μ) ^ (p.toReal / q.toReal) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), hIB, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul, div_eq_mul_one_div (q.toReal - p.toReal), div_eq_mul_one_div p.toReal]

lemma text_fcoef_sub {u v : Torus d → ℝ} (hu : Integrable u) (hv : Integrable v) (k : Lattice d) :
    Torus.fcoef (fun x => u x - v x) k = Torus.fcoef u k - Torus.fcoef v k := by
  have h := text_fcoef_add (v := fun x => -v x) hu hv.neg k
  have hneg : Torus.fcoef (fun x => -v x) k = - Torus.fcoef v k := by
    unfold Torus.fcoef
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    push_cast; ring
  have e : (fun x => u x - v x) = fun x => u x + -v x := by funext x; ring
  rw [e, h, hneg]; ring

/-- Hölder for the convolution at a point: `|(K ⋆ a)(x)| ≤ ‖K‖_{p'} ‖a‖_p`. -/
lemma text_conv_enorm_le {p p' : ℝ≥0∞} [p.HolderConjugate p'] {K a : Torus d → ℝ}
    (hK : MemLp K p' volume) (ha : MemLp a p volume) (x : Torus d) :
    ‖textConv K a x‖ₑ ≤ eLpNorm K p' volume * eLpNorm a p volume := by
  unfold textConv
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  have hmp : MeasurePreserving (fun y : Torus d => x - y) volume volume :=
    (volume : Measure (Torus d)).measurePreserving_sub_left x
  have hm1 : AEStronglyMeasurable (fun y => K (x - y)) volume :=
    hK.aestronglyMeasurable.comp_measurePreserving hmp
  have h1 : eLpNorm (fun y => K (x - y)) p' volume = eLpNorm K p' volume :=
    eLpNorm_comp_measurePreserving hK.aestronglyMeasurable hmp
  have h2 := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (μ := volume) (p := p') (q := p)
    (r := 1) (fun x y : ℝ => x * y) (1 : NNReal) continuous_mul hm1 ha.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by simp [nnnorm_mul])
  have hmeas : AEStronglyMeasurable (fun y => K (x - y) * a y) volume :=
    hm1.mul ha.aestronglyMeasurable
  rw [h1] at h2
  have h3 : ∫⁻ y, ‖K (x - y) * a y‖ₑ = eLpNorm (fun y => K (x - y) * a y) 1 volume :=
    (eLpNorm_one_eq_lintegral_enorm hmeas).symm
  rw [h3]
  simpa using h2

end HRS.Commutator.TorusNote
