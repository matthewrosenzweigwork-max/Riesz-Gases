import HRS.Commutator.Torus.TSAMPAux31

/-!
# T-SAMP helpers, part 32: pointwise profile of the low-pass kernel
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

theorem tsamp_psi_profile (hd : 1 ≤ d) :
    ∃ B Cm : ℝ, 0 ≤ B ∧ 0 ≤ Cm ∧ ∀ η : ℝ, 0 < η → η ≤ 1 →
      (∀ x : Torus d, x ≠ 0 → |perio (Whole.psiL (d := d) η⁻¹) x| ≤ B * η ^ (-(d : ℝ))) ∧
      (∀ x : Torus d, η ≤ KernelGrad.tdist x 0 →
        |perio (Whole.psiL (d := d) η⁻¹) x| ≤
          Cm * η ^ ((0 : ℝ) - d + ((d + 1 : ℕ) : ℝ)) * KernelGrad.tdist x 0 ^ (-((d + 1 : ℕ) : ℝ))) := by
  obtain ⟨hcont, hint, ⟨Bs, hBs0, hBs⟩, hdec, hft⟩ := text_psiL_props (d := d) 1 one_pos
  choose A hA using hdec
  set ψ : Euc d → ℝ := Whole.psiL (d := d) 1 with hψ
  obtain ⟨C, hC, Cm, hCm, hmain⟩ := tsamp_gk hd 0 0 le_rfl (by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith) le_rfl (Kt := ψ) hcont.measurable hint (C₀ := Bs + 1) (by linarith)
    (fun x _ _ => by
      rw [Real.rpow_zero, mul_one]; linarith [hBs x])
    (fun m => A m + 1) (fun m => by linarith [(hA m).1])
    (fun m x hx => by
      have hx0 : x ≠ 0 := by
        intro h; rw [h, norm_zero] at hx; linarith
      have := (hA m).2 x hx0
      nlinarith [Real.rpow_nonneg (norm_nonneg x) (-(m : ℝ))])
  refine ⟨max C (Cm 0), Cm (d + 1), le_trans hC.le (le_max_left _ _), (hCm _).le, fun η hη hη1 => ?_⟩
  obtain ⟨-, -, hnear, hfar, -⟩ := hmain η hη hη1
  have e : textKeta ψ 0 η = Whole.psiL (d := d) η⁻¹ := (tsamp_psi_scale hη).symm
  rw [e] at hnear hfar
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · by_cases h1 : KernelGrad.tdist x 0 ≤ η
    · have := hnear x hx h1
      simp only [zero_sub, sub_zero, Real.rpow_zero, mul_one] at this
      refine this.trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_pos_of_pos hη _).le
    · push Not at h1
      have := hfar 0 x h1.le
      simp only [Nat.cast_zero, add_zero, zero_sub, neg_zero, Real.rpow_zero, mul_one] at this
      refine this.trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_pos_of_pos hη _).le
  · have := hfar (d + 1) x hx
    exact this

end HRS.Commutator.TorusNote
