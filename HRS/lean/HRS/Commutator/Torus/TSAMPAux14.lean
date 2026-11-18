import HRS.Commutator.Torus.TSAMPAux13

/-!
# T-SAMP helpers, part 14: `vhi_Lp_T`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s : ℝ}

/-- `c · (f - K⋆f + k⋆f)`. -/
def tsampWf (c : ℝ) (K kb f : Torus d → ℝ) (x : Torus d) : ℝ :=
  c * (f x - tsampConv K f x + tsampConv kb f x)

lemma tsamp_Wf_fcoef {K kb f : Torus d → ℝ} (hK : Integrable K) (hkb : Integrable kb)
    (hf : Integrable f) (c : ℝ) (k : Lattice d) :
    Torus.fcoef (tsampWf c K kb f) k =
      (c : ℂ) * (Torus.fcoef f k - Torus.fcoef K k * Torus.fcoef f k +
        Torus.fcoef kb k * Torus.fcoef f k) := by
  have h1 : Integrable (textConv K f) := text_integrable_conv hK hf
  have h2 : Integrable (textConv kb f) := text_integrable_conv hkb hf
  unfold tsampWf
  rw [tsamp_fcoef_const_mul]
  congr 1
  have e : (fun x => f x - tsampConv K f x + tsampConv kb f x) =
      fun x => (f x - textConv K f x) + textConv kb f x := by
    funext x
    rw [tsamp_conv_real, tsamp_conv_real]
  have h3 := text_fcoef_add (u := fun x => f x - textConv K f x) (v := textConv kb f) (hf.sub h1) h2 k
  rw [e, h3, text_fcoef_sub hf h1, text_fcoef_conv hK hf, text_fcoef_conv hkb hf]

lemma tsamp_Wf_norm {K kb f : Torus d → ℝ} (hK : Integrable K) (hKm : Measurable K)
    (hkb : Integrable kb) (hkbm : Measurable kb) (hf : Measurable f) {p : ℝ} (hp : 1 < p) (c : ℝ) :
    eLpNorm (tsampWf c K kb f) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal |c| * (eLpNorm f (ENNReal.ofReal p) volume +
        ENNReal.ofReal (∫ y, ‖K y‖) * eLpNorm f (ENNReal.ofReal p) volume +
        ENNReal.ofReal (∫ y, ‖kb y‖) * eLpNorm f (ENNReal.ofReal p) volume) := by
  have hP1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  have hcK := tsamp_aesm_conv (E := ℝ) hKm hf
  have hckb := tsamp_aesm_conv (E := ℝ) hkbm hf
  have e : tsampWf c K kb f = c • (fun x => f x - tsampConv K f x + tsampConv kb f x) := by
    funext x; simp [tsampWf]
  rw [e, eLpNorm_const_smul]
  refine mul_le_mul' (by rw [Real.enorm_eq_ofReal_abs]) ?_
  have e2 : (fun x => f x - tsampConv K f x + tsampConv kb f x) =
      (f - tsampConv K f) + tsampConv kb f := by
    funext x; simp
  rw [e2]
  refine (eLpNorm_add_le hP1).trans ?_
  refine add_le_add ((eLpNorm_sub_le hP1).trans ?_)
    (tsamp_conv_eLpNorm_le hkb hkbm hf hp)
  exact add_le_add le_rfl (tsamp_conv_eLpNorm_le hK hKm hf hp)

end HRS.Commutator.TorusNote
