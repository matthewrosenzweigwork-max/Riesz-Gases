import HRS.Commutator.Torus.TSAMPAux11

/-!
# T-SAMP helpers, part 12: the torus kernels `K_{α,η}` and the Bessel remainder
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

lemma tsamp_L1_of_lintegral {f : Torus d → ℝ} (hf : Integrable f) {B : ℝ} (hB : 0 ≤ B)
    (h : ∫⁻ x, ‖f x‖ₑ ≤ ENNReal.ofReal B) : ∫ x, |f x| ≤ B := by
  have h1 : ∫ x, |f x| = (∫⁻ x, ‖f x‖ₑ).toReal := by
    rw [← integral_norm_eq_lintegral_enorm hf.1]
    simp
  rw [h1]
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_ofReal hB] at this

theorem tsamp_Kalpha_torus (hd : 3 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : γ < d) :
    ∃ CL : ℝ, 0 < CL ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ K : Torus d → ℝ, Measurable K ∧ Integrable K ∧
      (∀ k : Lattice d, Torus.fcoef K k = ((if k = 0 then 0 else
          (1 - Whole.chi (η • Lattice.toEuc k)) * (2 * Real.pi * Lattice.enorm k) ^ (-γ) : ℝ) : ℂ)) ∧
      ∫ x, |K x| ≤ CL * η ^ γ := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  obtain ⟨Kt, hKm, hKi, hFT, C₀, hC₀, hnear, Cf, hCf, hfar⟩ := tsamp_Kalpha_data hd1 γ hγ hγd
  obtain ⟨C, hC, Cm, hCm, hmain⟩ := tsamp_gk hd1 (γ - d) γ (by linarith) (by linarith) hγ.le hKm hKi hC₀
    hnear Cf hCf hfar
  have hI0 : 0 ≤ ∫ y, ‖Kt y‖ := integral_nonneg fun y => norm_nonneg _
  refine ⟨(∫ y, ‖Kt y‖) + 1, by linarith, fun η hη hη1 => ?_⟩
  obtain ⟨hint, hcoef, -, -, hL1⟩ := hmain η hη hη1
  refine ⟨perio (textKeta Kt γ η), tpos_perio_measurable (text_Keta_measurable hKm γ η), hint,
    fun k => ?_, ?_⟩
  · rw [hcoef k, hFT, text_symbol_scale hγ.ne' hη k]
  · have hB : 0 ≤ η ^ γ * ∫ y, ‖Kt y‖ := mul_nonneg (Real.rpow_nonneg hη.le _) hI0
    have := tsamp_L1_of_lintegral hint hB hL1
    refine this.trans ?_
    have : 0 ≤ η ^ γ := Real.rpow_nonneg hη.le _
    nlinarith

theorem tsamp_bessel_torus (hd : 3 ≤ d) (α : ℝ) (hα : 0 < α) :
    ∃ CB : ℝ, 0 < CB ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ k : Torus d → ℝ, Measurable k ∧ Integrable k ∧
      (∀ m : Lattice d, Torus.fcoef k m =
        (((1 + 4 * Real.pi ^ 2 * ‖η • Lattice.toEuc m‖ ^ 2) ^ (α / 2) *
          ((1 - Whole.chi (η • Lattice.toEuc m)) * (2 * Real.pi * ‖η • Lattice.toEuc m‖) ^ (-α)) : ℝ) : ℂ) -
          (((1 - Whole.chi (η • Lattice.toEuc m) : ℝ)) : ℂ)) ∧
      ∫ x, |k x| ≤ CB := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨kt, hKm, hKi, hFT, C₀, hC₀, hnear, Cf, hCf, hfar⟩ := tsamp_bessel_data hd α hα
  obtain ⟨C, hC, Cm, hCm, hmain⟩ := tsamp_gk hd1 ((2 : ℝ) - d) 0 (by linarith) (by linarith) le_rfl hKm hKi hC₀
    hnear Cf hCf hfar
  have hI0 : 0 ≤ ∫ y, ‖kt y‖ := integral_nonneg fun y => norm_nonneg _
  refine ⟨(∫ y, ‖kt y‖) + 1, by linarith, fun η hη hη1 => ?_⟩
  obtain ⟨hint, hcoef, -, -, hL1⟩ := hmain η hη hη1
  refine ⟨perio (textKeta kt 0 η), tpos_perio_measurable (text_Keta_measurable hKm 0 η), hint,
    fun m => ?_, ?_⟩
  · rw [hcoef m, eq_sub_iff_add_eq, Real.rpow_zero, Complex.ofReal_one, one_mul, add_comm, ← hFT]
  · have hB : 0 ≤ η ^ (0 : ℝ) * ∫ y, ‖kt y‖ := mul_nonneg (Real.rpow_nonneg hη.le _) hI0
    have := tsamp_L1_of_lintegral hint hB hL1
    rw [Real.rpow_zero, one_mul] at this
    linarith

end HRS.Commutator.TorusNote
