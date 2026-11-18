import HRS.Commutator.Torus.TEXTAux16

/-!
# T-EXT-A helpers, part 17: `L^{p'}` norm of the kernel by interpolation
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

lemma text_kernel_Lp' (p p' : ℝ≥0∞) [hpp : p.HolderConjugate p'] (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    {Ψ : Torus d → ℝ} (hΨ : Integrable Ψ) {b C₁ : ℝ} (hb : 0 ≤ b) (hC₁ : 0 ≤ C₁)
    (hsup : ∀ x, |Ψ x| ≤ b) (h1 : eLpNorm Ψ 1 volume ≤ ENNReal.ofReal C₁) :
    eLpNorm Ψ p' volume ≤
      ENNReal.ofReal (b ^ (p⁻¹).toReal * C₁ ^ (1 - (p⁻¹).toReal)) := by
  have hinv := hpp.inv_add_inv_eq_one
  have hbd : ∀ x, ‖Ψ x‖ₑ ≤ ENNReal.ofReal b := fun x => by
    rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (hsup x)
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hθ0 : 0 ≤ (p⁻¹).toReal := ENNReal.toReal_nonneg
  have hΨ1 : MemLp Ψ 1 volume := memLp_one_iff_integrable.2 hΨ
  have hbound : eLpNorm Ψ ⊤ volume ≤ ENNReal.ofReal b := by
    have h := eLpNorm_le_of_ae_bound (p := ⊤) (μ := (volume : Measure (Torus d)))
      hΨ.aestronglyMeasurable (C := b) (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hsup x)
    simpa using h
  rcases eq_or_lt_of_le hp with h | h
  · -- `p = 1`, `p' = ⊤`
    subst h
    have hp'top : p' = ⊤ := by
      have h0 : (1 : ℝ≥0∞)⁻¹ + p'⁻¹ = 1 := hinv
      rw [inv_one] at h0
      have h00 : p'⁻¹ = 0 := (ENNReal.add_right_inj ENNReal.one_ne_top).1 (h0.trans (add_zero 1).symm)
      exact ENNReal.inv_eq_zero.1 h00
    rw [hp'top]
    refine hbound.trans ?_
    simp
  · have hp'top : p' ≠ ⊤ := by
      intro h0
      rw [h0, ENNReal.inv_top, add_zero] at hinv
      exact absurd (ENNReal.inv_eq_one.1 hinv) h.ne'
    have hp'1 : 1 ≤ p' := hpp.symm.le
    have hθ : (p⁻¹).toReal + (p'⁻¹).toReal = 1 := by
      have := congrArg ENNReal.toReal hinv
      rwa [ENNReal.toReal_add (ENNReal.inv_ne_top.2 hp0) (ENNReal.inv_ne_top.2
        (zero_lt_one.trans_le hp'1).ne'), ENNReal.toReal_one] at this
    have hp'0 : 0 < p'.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le hp'1).ne' hp'top
    have hp'inv : (p'⁻¹).toReal = 1 / p'.toReal := by
      rw [ENNReal.toReal_inv, one_div]
    have hint' := text_interp (μ := (volume : Measure (Torus d))) (f := Ψ) (p := 1) (q := p')
      le_rfl hp'1 (lt_top_iff_ne_top.2 hp'top) hΨ1 (M := ENNReal.ofReal b) ENNReal.ofReal_ne_top
      (Filter.Eventually.of_forall hbd)
    simp only [ENNReal.toReal_one] at hint'
    have e1 : (p'.toReal - 1) / p'.toReal = (p⁻¹).toReal := by
      rw [sub_div, div_self hp'0.ne']
      have : (p⁻¹).toReal = 1 - (p'⁻¹).toReal := by linarith
      rw [this, hp'inv]
    have e2 : 1 / p'.toReal = 1 - (p⁻¹).toReal := by rw [← hp'inv]; linarith
    rw [e1, e2] at hint'
    refine hint'.trans ?_
    rw [ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_rpow_of_nonneg hb hθ0,
      ← ENNReal.ofReal_rpow_of_nonneg hC₁ (by linarith [ENNReal.toReal_nonneg (a := p'⁻¹)])]
    refine mul_le_mul' le_rfl (ENNReal.rpow_le_rpow h1 (by linarith [ENNReal.toReal_nonneg (a := p'⁻¹)]))

end HRS.Commutator.TorusNote
