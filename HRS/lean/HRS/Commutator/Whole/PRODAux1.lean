import HRS.Commutator.Whole.External

/-!
# CMX-PROD helper file 1: convolution and correlation with `L¹` / Schwartz kernels

`prod_conv K h = ∫ K(t) h(y-t) dt`, `prod_cor K h = ∫ K(t) h(y+t) dt`; Young's inequality for complex
kernels; measurability.
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

noncomputable section

namespace HRS.Commutator.Whole.PROD

open HRS HRS.Whole HRS.Commutator.Whole

variable {d : ℕ}

/-- `∫ K(t) h(y-t) dt`. -/
def prod_conv (K h : Euc d → ℂ) (y : Euc d) : ℂ := ∫ t, K t * h (y - t)

/-- `∫ K(t) h(y+t) dt`. -/
def prod_cor (K h : Euc d → ℂ) (y : Euc d) : ℂ := ∫ t, K t * h (y + t)

lemma prod_cor_eq_conv {K : Euc d → ℂ} (hK : ∀ t, K (-t) = K t) (h : Euc d → ℂ) :
    prod_cor K h = prod_conv K h := by
  funext y
  unfold prod_cor prod_conv
  rw [← integral_neg_eq_self (fun t => K t * h (y + t)) volume]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [hK, sub_eq_add_neg]

lemma prod_aesm_conv {K h : Euc d → ℂ} (hK : AEStronglyMeasurable K volume)
    (hh : AEStronglyMeasurable h volume) : AEStronglyMeasurable (prod_conv K h) volume := by
  have := AEStronglyMeasurable.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hK hh
    (μ := volume) (ν := volume)
  exact this.integral_prod_right'

lemma prod_aesm_cor {K h : Euc d → ℂ} (hK : AEStronglyMeasurable K volume)
    (hh : AEStronglyMeasurable h volume) : AEStronglyMeasurable (prod_cor K h) volume := by
  have hF : AEStronglyMeasurable (fun q : Euc d × Euc d => K q.2 * h (q.1 + q.2))
      (volume.prod volume) :=
    (hK.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_snd)).mul
      (hh.comp_quasiMeasurePreserving (quasiMeasurePreserving_add volume volume))
  exact hF.integral_prod_right'

/-- Young's inequality with an `L¹` kernel (complex version). -/
lemma prod_eLpNorm_conv_le {p : ℝ} (hp : 1 < p) {K h : Euc d → ℂ} (hK : Integrable K)
    (hh : AEStronglyMeasurable h volume) :
    eLpNorm (prod_conv K h) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (∫ t, ‖K t‖) * eLpNorm h (ENNReal.ofReal p) volume := by
  have hY := HRS.Commutator.Whole.SAMP1.eLpNorm_conv_le (E := ℝ) (d := d) (k := fun t => ‖K t‖)
    hK.norm (f := fun x => ‖h x‖) hh.norm hp
  have h1 : eLpNorm (prod_conv K h) (ENNReal.ofReal p) volume ≤
      eLpNorm (fun x => ∫ y, ‖K y‖ • ‖h (x - y)‖) (ENNReal.ofReal p) volume := by
    refine eLpNorm_mono_ae (prod_aesm_conv hK.1 hh) (Filter.Eventually.of_forall fun x => ?_)
    have h2 : ‖∫ y, ‖K y‖ • ‖h (x - y)‖‖ = ∫ y, ‖K y‖ • ‖h (x - y)‖ :=
      Real.norm_of_nonneg (integral_nonneg fun y => by positivity)
    rw [h2]
    unfold prod_conv
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp
  refine h1.trans (hY.trans ?_)
  rw [eLpNorm_norm _ hh]
  simp only [norm_norm]
  exact le_rfl

end HRS.Commutator.Whole.PROD
