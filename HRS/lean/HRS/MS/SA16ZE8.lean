import HRS.MS.SA16ZE7

/-!
# S.A.16 (SA16Z) E8: integrals of `|f|^p` from `L^p` bounds, and the bound of the error pairing
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.BreakdownSA16

section E8
variable {d : ℕ} {s : ℝ}

lemma sa16z_rpow_int_of_eLpNorm {f : Euc d → ℝ} (hf : AEStronglyMeasurable f volume) {p : ℝ} (hp : 0 < p)
    {a : ℝ≥0∞} (ha : a ≠ ⊤) (h : eLpNorm f (ENNReal.ofReal p) volume ≤ a) :
    Integrable (fun x => |f x| ^ p) ∧ ∫ x, |f x| ^ p ≤ a.toReal ^ p := by
  have hlin := sa16z_lintegral_rpow_eq hf hp
  have hle : ∫⁻ x, ENNReal.ofReal (|f x| ^ p) ≤ a ^ p := by
    rw [hlin]; exact ENNReal.rpow_le_rpow h hp.le
  have hfin : ∫⁻ x, ENNReal.ofReal (|f x| ^ p) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.rpow_ne_top_of_nonneg hp.le ha) hle
  have hm : AEStronglyMeasurable (fun x => |f x| ^ p) volume := hf.norm.aemeasurable.pow_const p |>.aestronglyMeasurable
  have hint : Integrable (fun x => |f x| ^ p) :=
    (lintegral_ofReal_ne_top_iff_integrable hm (Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg _) _)).1 hfin
  refine ⟨hint, ?_⟩
  have h1 : ENNReal.ofReal (∫ x, |f x| ^ p) = ∫⁻ x, ENNReal.ofReal (|f x| ^ p) :=
    ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg _) _)
  have h2 : ENNReal.ofReal (∫ x, |f x| ^ p) ≤ a ^ p := h1 ▸ hle
  have := ENNReal.toReal_mono (ENNReal.rpow_ne_top_of_nonneg hp.le ha) h2
  rwa [ENNReal.toReal_ofReal (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _),
    ← ENNReal.toReal_rpow] at this

end E8

end HRS.Whole.AppendixA.Phase2SA16R
