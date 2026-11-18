import HRS.MH.ScreenedF1
import HRS.MH.ScreenedF2
import HRS.MH.ScreenedFar
import HRS.MH.ScreenedA3a

/-! Assembly of `screened_far` (frozen `HRS.Whole.screened_far`, S.B.4(i)) from the proved packets:
`flow_lip_sep` (CF), `flow_origin`, `far_core`, `cellWeight_tsum_lt_top`.  Coefficients `Kc z z' = ω_{z'}`. -/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

theorem sfa_weight_bound (hd : 1 ≤ d) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∑' z : Fin d → ℤ, ENNReal.ofReal (cellWeight d z) ≤ ENNReal.ofReal Cw :=
  ⟨(∑' z : Fin d → ℤ, ENNReal.ofReal (cellWeight d z)).toReal, ENNReal.toReal_nonneg,
    (ENNReal.ofReal_toReal (ne_top_of_lt (cellWeight_tsum_lt_top_proof hd))).symm.le⟩

theorem sfa_sep_le {CF T τ : ℝ} (hCF0 : 0 ≤ CF) (hτT : τ ≤ |T|) :
    4 / Real.exp (CF * |T|) ≤ 4 * Real.exp (-(CF * τ)) := by
  rw [div_eq_mul_inv, ← Real.exp_neg]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hτT hCF0)))
    (by norm_num)

theorem screened_far_proof : type_of% @HRS.Whole.screened_far := by
  intro d hd s hs0 hsd m Λ Cb T χ χh hχ
  obtain ⟨CF, hCF0, hCF⟩ := flow_lip_sep_proof hd m Cb T χ χh hχ
  have hL1 : 1 ≤ Real.exp (CF * |T|) := Real.one_le_exp (mul_nonneg hCF0 (abs_nonneg T))
  have hB0 : 0 ≤ Real.exp (|Cb| * |T|) - 1 := by
    have : 1 ≤ Real.exp (|Cb| * |T|) := Real.one_le_exp (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    linarith
  obtain ⟨C₀, hC₀0, hfar⟩ := far_core_proof hd hs0 hsd m Λ χ χh hχ (Real.exp (CF * |T|))
    (Real.exp (|Cb| * |T|) - 1) hL1 hB0
  obtain ⟨Cw, hCw0, hCw⟩ := sfa_weight_bound hd
  refine ⟨C₀ + Cw, fun b Ψ hb hΨ μ hμ τ hτ => ?_⟩
  have hτ0 : 0 ≤ τ := hτ.1
  have hτT : τ ≤ |T| := le_trans hτ.2 (le_abs_self T)
  obtain ⟨hlipF, hlipI, hsep⟩ := hCF b Ψ hb hΨ τ hτ
  have hexp : Real.exp (CF * τ) ≤ Real.exp (CF * |T|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hτT hCF0)
  have hlipL : ∀ x y : Euc d, ‖Ψ τ x - Ψ τ y‖ ≤ Real.exp (CF * |T|) * ‖x - y‖ := fun x y =>
    le_trans (hlipF x y) (mul_le_mul_of_nonneg_right hexp (norm_nonneg _))
  have hlipIL : ∀ x y : Euc d,
      ‖Function.invFun (Ψ τ) x - Function.invFun (Ψ τ) y‖ ≤ Real.exp (CF * |T|) * ‖x - y‖ := fun x y =>
    le_trans (hlipI x y) (mul_le_mul_of_nonneg_right hexp (norm_nonneg _))
  have hsepL : ∀ z : Euc d, ∀ x y : Euc d, x ∈ tsupport (advCutoff χ Ψ τ z) →
      y ∈ tsupport (fun y => 1 - advCutoff χh Ψ τ z y) → 4 / Real.exp (CF * |T|) ≤ ‖x - y‖ :=
    fun z x y hx hy => le_trans (sfa_sep_le hCF0 hτT) (hsep z x y hx hy)
  have hB : ‖Ψ τ 0‖ ≤ Real.exp (|Cb| * |T|) - 1 := by
    refine le_trans (flow_origin_proof m Cb T b Ψ hb hΨ τ hτ)
      (sub_le_sub_right (Real.exp_le_exp.mpr ?_) 1)
    exact le_trans (mul_le_mul_of_nonneg_right (le_abs_self Cb) hτ0)
      (mul_le_mul_of_nonneg_left hτT (abs_nonneg _))
  have hbij : Function.Bijective (Ψ τ) := hΨ.bij τ hτ
  have hfar' := hfar Ψ τ hbij hlipL hlipIL hsepL hB
  refine ⟨fun _ z' => Real.toNNReal (cellWeight d z'), ?_, ?_, ?_⟩
  · refine iSup_le fun z => ?_
    exact le_trans hCw (ENNReal.ofReal_le_ofReal (by linarith))
  · intro z'
    calc ∑' z, ENNReal.ofReal (cellWeight d z) * ENNReal.ofReal (cellWeight d z')
        = (∑' z, ENNReal.ofReal (cellWeight d z)) * ENNReal.ofReal (cellWeight d z') :=
          ENNReal.tsum_mul_right
      _ ≤ ENNReal.ofReal Cw * ENNReal.ofReal (cellWeight d z') := mul_le_mul_of_nonneg_right hCw zero_le
      _ ≤ ENNReal.ofReal (C₀ + Cw) * ENNReal.ofReal (cellWeight d z') :=
          mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (by linarith)) zero_le
  · intro j hj idx i ψ hψ z
    obtain ⟨h1, h2⟩ := hfar' μ hμ j hj idx i ψ hψ z
    have hC : ENNReal.ofReal (C₀ * Λ ^ 2) ≤ ENNReal.ofReal ((C₀ + Cw) * Λ ^ 2) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg Λ))
    exact ⟨le_trans h1 (mul_le_mul_of_nonneg_right hC zero_le),
      fun hlt => h2 (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hC zero_le) hlt)⟩

end HRS.MH.Screened
