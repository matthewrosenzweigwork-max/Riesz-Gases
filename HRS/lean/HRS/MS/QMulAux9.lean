import HRS.MS.QMulAux8

/-!
# MS-QMUL, part 9: Plancherel on `Lp`, `QOk ⊆ L¹ ∩ L²`, an elementary weighted inequality
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform ContDiff

namespace HRS.MS.QMul
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

theorem qm_QOk_L1L2 {m : ℕ} {g : Euc d → ℂ} (hg : QOk m g) :
    Integrable g volume ∧ MemLp g 2 volume := by
  have h0 := hg.2 0 (Nat.zero_le _)
  have hc : Continuous g := hg.1.continuous
  have e : ∀ x, ‖g x‖ ≤ ‖iteratedFDeriv ℝ 0 g x‖ := fun x => by simp
  exact ⟨h0.1.norm.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall e),
    h0.2.of_le hc.aestronglyMeasurable (Filter.Eventually.of_forall e)⟩

theorem qm_lint_Lp (c : Lp (α := Euc d) ℂ 2) : ∫⁻ x, ‖c x‖ₑ ^ 2 = ‖c‖ₑ ^ 2 := by
  rw [qm_lint_sq_eq (Lp.memLp c), Lp.enorm_def]

theorem qm_plancherel_Lp (a b : Lp (α := Euc d) ℂ 2) :
    ∫⁻ ξ, ‖(FT d a) ξ - (FT d b) ξ‖ₑ ^ 2 = ∫⁻ x, ‖a x - b x‖ₑ ^ 2 := by
  have e1 : FT d (a - b) = FT d a - FT d b := map_sub _ _ _
  have h1 : ∫⁻ ξ, ‖(FT d a) ξ - (FT d b) ξ‖ₑ ^ 2 = ∫⁻ ξ, ‖(FT d (a - b)) ξ‖ₑ ^ 2 := by
    refine lintegral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (FT d a) (FT d b)] with ξ hξ
    rw [e1, hξ]; rfl
  have h2 : ∫⁻ x, ‖a x - b x‖ₑ ^ 2 = ∫⁻ x, ‖(a - b) x‖ₑ ^ 2 := by
    refine lintegral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub a b] with x hx
    rw [hx]; rfl
  rw [h1, h2, qm_lint_Lp, qm_lint_Lp]
  congr 1
  exact (FT d).toLinearIsometry.enorm_map (a - b)

theorem qm_elem (a b : ℂ) {e : ℝ} (he : 0 < e) {w : ℝ} (hw : 0 ≤ w) :
    ENNReal.ofReal (w * ‖a‖ ^ 2) ≤ ENNReal.ofReal (1 + e) * ENNReal.ofReal (w * ‖b‖ ^ 2) +
      ENNReal.ofReal (1 + 1 / e) * ENNReal.ofReal (w * ‖a - b‖ ^ 2) := by
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  set x := ‖b‖ with hx
  set y := ‖a - b‖ with hy
  have h1 : ‖a‖ ≤ x + y := by
    have := norm_le_norm_add_norm_sub' a b
    rw [hx, hy]; linarith [norm_le_insert' a b]
  have h2 : 2 * x * y ≤ e * x ^ 2 + y ^ 2 / e := by
    rw [← sub_nonneg]
    have : e * x ^ 2 + y ^ 2 / e - 2 * x * y = (e * x - y) ^ 2 / e := by field_simp; ring
    rw [this]; positivity
  have h3 : ‖a‖ ^ 2 ≤ (1 + e) * x ^ 2 + (1 + 1 / e) * y ^ 2 := by
    calc ‖a‖ ^ 2 ≤ (x + y) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = x ^ 2 + 2 * x * y + y ^ 2 := by ring
      _ ≤ x ^ 2 + (e * x ^ 2 + y ^ 2 / e) + y ^ 2 := by linarith
      _ = _ := by field_simp; ring
  calc w * ‖a‖ ^ 2 ≤ w * ((1 + e) * x ^ 2 + (1 + 1 / e) * y ^ 2) := mul_le_mul_of_nonneg_left h3 hw
    _ = _ := by ring

end HRS.MS.QMul
