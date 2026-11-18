import HRS.Commutator.Torus.TSAMPAux12

/-!
# T-SAMP helpers, part 13: coefficient calculus for `P_>` and `vhi_Lp_T`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s : ℝ}

lemma tsamp_conv_real (K f : Torus d → ℝ) : tsampConv K f = textConv K f := by
  funext x; simp [tsampConv, textConv]

lemma tsamp_fcoef_const_mul (c : ℝ) (f : Torus d → ℝ) (k : Lattice d) :
    Torus.fcoef (fun x => c * f x) k = (c : ℂ) * Torus.fcoef f k := by
  unfold Torus.fcoef
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  push_cast; ring

/-- Coefficients of `P_>` components. -/
lemma tsamp_fcoef_Pgt (hd : 1 ≤ d) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    {v : Torus d → Euc d} {L : ℝ} (hL : 0 ≤ L) (hv : IsLipschitzVF L v) (i : Fin d) (k : Lattice d) :
    Torus.fcoef (fun x => PgtT η v x i) k =
      (1 - ((Whole.chi (η • Lattice.toEuc k) : ℝ) : ℂ)) * Torus.fcoef (fun x => v x i) k := by
  obtain ⟨B, C₁, C₂, hB, hC₁, hC₂, hker⟩ := tsamp_psi_kernel (d := d) hd
  obtain ⟨hKint, hKb, hK1, hKcoef, -⟩ := hker η hη hη1
  set Kη : Torus d → ℝ := perio (Whole.psiL (d := d) η⁻¹) with hKη
  have hKm : Measurable Kη := by
    obtain ⟨hc, -⟩ := text_psiL_props (d := d) η⁻¹ (inv_pos.2 hη)
    exact tpos_perio_measurable hc.measurable
  have hvint : Integrable v := tsamp_integrable_of_lip hL hv
  have hvi : Integrable (fun x => v x i) :=
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).integrable_comp hvint
  have hconv := tsamp_conv_fcoef_comp hd hKm hKint hKb hvint i k
  have hci : Integrable (fun x => (tsampConv Kη v x) i) := by
    have : (fun x => (tsampConv Kη v x) i) = textConv Kη (fun x => v x i) := by
      funext x
      rw [tsamp_conv_apply (tsamp_conv_integrable hd hKm hKb hvint x) i]
      rfl
    rw [this]
    exact text_integrable_conv hKint hvi
  have : (fun x => PgtT η v x i) = fun x => v x i - (tsampConv Kη v x) i := by
    funext x; simp [PgtT, PleqT, tsampConv, hKη]
  rw [this, text_fcoef_sub hvi hci, hconv, hKcoef k]
  ring

end HRS.Commutator.TorusNote
