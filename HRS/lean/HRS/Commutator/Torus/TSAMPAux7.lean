import HRS.Commutator.Torus.TSAMPAux6

/-!
# T-SAMP helpers, part 7: `vhi_bounded_T`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

lemma tsamp_Pgt_eq {K : Torus d → ℝ} (hKi : Integrable K) (hK1 : ∫ x, K x = 1)
    {v : Torus d → Euc d} {L : ℝ} (hL : 0 ≤ L) (hv : IsLipschitzVF L v) (x : Torus d) :
    v x - tsampConv K v x = ∫ z, K z • (v x - v (x - z)) := by
  rw [tsamp_conv_eq_flip]
  have h1 : Integrable (fun z => K z • v x) := hKi.smul_const _
  have h2 := tsamp_conv_flip_integrable hKi hL hv x
  have e : ∀ z, K z • (v x - v (x - z)) = K z • v x - K z • v (x - z) := fun z => smul_sub _ _ _
  simp_rw [e]
  rw [integral_sub h1 h2, integral_smul_const, hK1, one_smul]

theorem tsamp_vhi_bounded_core (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ (v : Torus d → Euc d) (L : ℝ), 0 ≤ L →
      IsLipschitzVF L v → Continuous (PgtT η v) ∧ ∀ x, ‖PgtT η v x‖ ≤ C * η * L := by
  obtain ⟨B, C₁, C₂, hB, hC₁, hC₂, hker⟩ := tsamp_psi_kernel (d := d) hd
  refine ⟨C₂, hC₂, fun η hη hη1 v L hL hv => ?_⟩
  obtain ⟨hKint, hKb, hK1, hKcoef, hmom⟩ := hker η hη hη1
  set Kη : Torus d → ℝ := perio (Whole.psiL (d := d) η⁻¹) with hKη
  have hKm : Measurable Kη := by
    obtain ⟨hc, -⟩ := text_psiL_props (d := d) η⁻¹ (inv_pos.2 hη)
    exact tpos_perio_measurable hc.measurable
  have hint1 : ∫ x, Kη x = 1 := tsamp_integral_psi_kernel hKint hKcoef
  have hpg : ∀ x, PgtT η v x = ∫ z, Kη z • (v x - v (x - z)) := fun x =>
    tsamp_Pgt_eq hKint hint1 hL hv x
  refine ⟨?_, fun x => ?_⟩
  · have hlip := tsamp_conv_lip hKint hL hv
    have hcont := tsamp_lip_continuous hlip
    exact (tsamp_lip_continuous hv).sub hcont
  · rw [hpg x]
    have hb : ∀ z, ‖Kη z • (v x - v (x - z))‖ ≤ |Kη z| * KernelGrad.tdist z 0 * L := by
      intro z
      rw [norm_smul, Real.norm_eq_abs]
      have h1 := hv x (x - z)
      have h2 : KernelGrad.tdist x (x - z) = KernelGrad.tdist z 0 := by
        rw [KernelGrad.tdist_eq_sub_zero]; congr 1; abel
      rw [h2] at h1
      calc |Kη z| * ‖v x - v (x - z)‖ ≤ |Kη z| * (L * KernelGrad.tdist z 0) :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = |Kη z| * KernelGrad.tdist z 0 * L := by ring
    have hmi : Integrable (fun z => |Kη z| * KernelGrad.tdist z 0) := by
      refine (hKint.norm.mul_const (d : ℝ)).mono' ?_ (Eventually.of_forall fun z => ?_)
      · exact (hKint.1.norm.mul (tsamp_measurable_tdist 0).aestronglyMeasurable).congr
          (Eventually.of_forall fun z => by simp)
      · rw [norm_mul, Real.norm_eq_abs, abs_abs, Real.norm_eq_abs, abs_of_nonneg (KernelGrad.tdist_nonneg _ _)]
        exact mul_le_mul_of_nonneg_left (KernelGrad.tdist_le_card z) (abs_nonneg _)
    calc ‖∫ z, Kη z • (v x - v (x - z))‖
        ≤ ∫ z, |Kη z| * KernelGrad.tdist z 0 * L :=
          norm_integral_le_of_norm_le (hmi.mul_const L) (Eventually.of_forall hb)
      _ = (∫ z, |Kη z| * KernelGrad.tdist z 0) * L := by rw [integral_mul_const]
      _ ≤ (C₂ * η) * L := mul_le_mul_of_nonneg_right hmom hL
      _ = C₂ * η * L := rfl

end HRS.Commutator.TorusNote
