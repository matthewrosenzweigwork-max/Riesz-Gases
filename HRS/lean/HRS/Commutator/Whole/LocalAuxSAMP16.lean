import HRS.Commutator.Whole.LocalAuxSAMP15

/-!
# Scalar convolution facts for `vhi_Lp` (packet CMX-SAMP, helper file 16)
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff Convolution

noncomputable section

namespace HRS.Commutator.Whole.SAMP1

open HRS HRS.Whole HRS.Commutator.Whole

variable {d : ℕ}

lemma measurable_conv_real {k f : Euc d → ℝ} (hk : Measurable k) (hf : Measurable f) :
    Measurable (fun x => ∫ y, k y * f (x - y)) := by
  have h : StronglyMeasurable (fun q : Euc d × Euc d => k q.2 * f (q.1 - q.2)) :=
    ((hk.comp measurable_snd).mul (hf.comp (measurable_fst.sub measurable_snd))).stronglyMeasurable
  exact (h.integral_prod_right' (ν := volume)).measurable

lemma eLpNorm_conv_real {k f : Euc d → ℝ} (hk : Integrable k) (hf : AEStronglyMeasurable f volume)
    {p : ℝ} (hp : 1 < p) :
    eLpNorm (fun x => ∫ y, k y * f (x - y)) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (∫ y, ‖k y‖) * eLpNorm f (ENNReal.ofReal p) volume := by
  have := eLpNorm_conv_le (E := ℝ) hk hf hp
  simpa [smul_eq_mul] using this

lemma memLp_conv_real {k f : Euc d → ℝ} (hk : Integrable k) {p : ℝ} (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    MemLp (fun x => ∫ y, k y * f (x - y)) (ENNReal.ofReal p) volume := by
  rw [memLp_iff]
  exact lt_of_le_of_lt (eLpNorm_conv_real hk hf.aestronglyMeasurable hp)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLpNorm_lt_top)

end HRS.Commutator.Whole.SAMP1
