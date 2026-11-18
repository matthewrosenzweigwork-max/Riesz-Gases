import HRS.Commutator.Torus.TSAMPAux30
import HRS.Commutator.Whole.LocalAuxSAMP2Bessel

/-!
# T-SAMP helpers, part 31: the periodised Bessel multiplier kernel `B_{α,η}` (band-limited input)
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

lemma tsamp_schwartz_decay (Om : SchwartzMap (Euc d) ℂ) :
    (∃ A : ℝ, 0 ≤ A ∧ ∀ z : Euc d, ‖Om z‖ ≤ A) ∧
      ∀ N : ℕ, ∃ A : ℝ, 0 ≤ A ∧ ∀ z : Euc d, z ≠ 0 → ‖Om z‖ ≤ A * ‖z‖ ^ (-(N : ℝ)) := by
  obtain ⟨_, hdec⟩ := Whole.cmxHLS_schwartz_dec Om
  refine ⟨?_, fun N => ?_⟩
  · obtain ⟨C, hC0, hC⟩ := hdec 0 0
    refine ⟨C, hC0, fun z => ?_⟩
    have := hC z
    simpa using this
  · obtain ⟨C, hC0, hC⟩ := hdec 0 N
    refine ⟨C, hC0, fun z hz => ?_⟩
    have h1 := hC z
    simp only [norm_iteratedFDeriv_zero] at h1
    have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
    have h2 : ‖z‖ ^ N ≤ (1 + ‖z‖) ^ N := pow_le_pow_left₀ hzpos.le (by linarith) N
    have h3 : ‖z‖ ^ N * ‖Om z‖ ≤ C :=
      (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)).trans h1
    rw [Real.rpow_neg hzpos.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    linarith

lemma tsamp_FT_Br (α : ℝ) (ξ : Euc d) :
    𝓕 (fun x : Euc d => ((Whole.SAMP2.Br (d := d) α x : ℝ) : ℂ)) ξ =
      (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (α / 2) * Whole.chi ((3 : ℝ)⁻¹ • ξ) : ℝ) : ℂ) := by
  have h1 : (fun x : Euc d => ((Whole.SAMP2.Br (d := d) α x : ℝ) : ℂ)) = ⇑(Whole.SAMP2.Bker (d := d) α) := by
    funext x; exact (Whole.SAMP2.Bker_eq_ofReal α x).symm
  rw [h1, ← SchwartzMap.fourier_coe, Whole.SAMP2.fourier_Bker, Whole.SAMP2.bsymS_apply]
  simp only [Whole.SAMP2.bsymCut, Whole.SAMP2.bsym, Whole.cmxFB_gL]
  push_cast
  rfl

theorem tsamp_Br_torus (hd : 1 ≤ d) (α : ℝ) :
    ∃ CB : ℝ, 0 < CB ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ Φ : Torus d → ℝ, Measurable Φ ∧ Integrable Φ ∧
      (∀ k : Lattice d, Torus.fcoef Φ k =
        (((1 + 4 * Real.pi ^ 2 * ‖η • Lattice.toEuc k‖ ^ 2) ^ (α / 2) *
          Whole.chi ((3 : ℝ)⁻¹ • (η • Lattice.toEuc k)) : ℝ) : ℂ)) ∧
      ∫ x, |Φ x| ≤ CB := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set Bk : Euc d → ℝ := Whole.SAMP2.Br (d := d) α with hBk
  have hBkc : Continuous Bk := Whole.SAMP2.Br_continuous α
  have hBki : Integrable Bk := Whole.SAMP2.Br_integrable α
  have hnorm : ∀ x, |Bk x| ≤ ‖Whole.SAMP2.Bker (d := d) α x‖ := by
    intro x
    have := Whole.SAMP2.Bker_eq_ofReal (d := d) α x
    rw [this, Complex.norm_real, Real.norm_eq_abs]
  obtain ⟨⟨A0, hA00, hA0⟩, hdec⟩ := tsamp_schwartz_decay (Whole.SAMP2.Bker (d := d) α)
  choose A hA using hdec
  obtain ⟨C, hC, Cm, hCm, hmain⟩ := tsamp_gk hd 0 0 le_rfl (by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith) le_rfl (Kt := Bk) hBkc.measurable hBki (C₀ := A0 + 1) (by linarith)
    (fun x _ _ => by rw [Real.rpow_zero, mul_one]; linarith [(hnorm x).trans (hA0 x)])
    (fun m => A m + 1) (fun m => by linarith [(hA m).1])
    (fun m x hx => by
      have hx0 : x ≠ 0 := by
        intro h; rw [h, norm_zero] at hx; linarith
      have := ((hnorm x).trans ((hA m).2 x hx0))
      nlinarith [Real.rpow_nonneg (norm_nonneg x) (-(m : ℝ))])
  have hI0 : 0 ≤ ∫ y, ‖Bk y‖ := integral_nonneg fun y => norm_nonneg _
  refine ⟨(∫ y, ‖Bk y‖) + 1, by linarith, fun η hη hη1 => ?_⟩
  obtain ⟨hint, hcoef, -, -, hL1⟩ := hmain η hη hη1
  refine ⟨perio (textKeta Bk 0 η), tpos_perio_measurable (text_Keta_measurable hBkc.measurable 0 η), hint,
    fun k => ?_, ?_⟩
  · rw [hcoef k, tsamp_FT_Br]
    simp
  · have hB : 0 ≤ η ^ (0 : ℝ) * ∫ y, ‖Bk y‖ := mul_nonneg (Real.rpow_nonneg hη.le _) hI0
    have := tsamp_L1_of_lintegral hint hB hL1
    rw [Real.rpow_zero, one_mul] at this
    linarith

end HRS.Commutator.TorusNote
