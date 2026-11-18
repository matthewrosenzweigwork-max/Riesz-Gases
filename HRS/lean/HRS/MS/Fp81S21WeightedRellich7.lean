import HRS.MS.Fp81S21WeightedRellich6

/-!
Scaled spatial cutoffs for the weighted Rellich argument.  The fixed cutoff
is one on the unit ball and supported in the ball of radius two.  Scaling it
by ρ⁻¹ gives support in radius 2ρ; since ρ ≥ 1, its derivatives through
the prescribed finite order have a bound independent of ρ.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.FixEq
open scoped ContDiff

/-- A smooth cutoff equal to one on B_ρ, supported in B_(2ρ), with its
ordered derivatives through order q + 2 uniformly bounded for ρ ≥ 1.
The uniformity follows from the ρ⁻ʲ factor in the derivative of order j.
-/
theorem fp81s21_weightedRellich_scaledCutoff
    {d q : ℕ} {ρ : ℝ} (hρ : 1 ≤ ρ) :
    ∃ χ : Euc d → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ x, ‖x‖ ≤ ρ → χ x = 1) ∧
      (∀ x, 2 * ρ ≤ ‖x‖ → χ x = 0) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ j ≤ q + 2, ∀ x, ‖iteratedFDeriv ℝ j χ x‖ ≤ C := by
  have hρpos : 0 < ρ := lt_of_lt_of_le (by norm_num) hρ
  let b : ContDiffBump (0 : Euc d) := ⟨1, 2, one_pos, one_lt_two⟩
  obtain ⟨C, hC0, hC⟩ :=
    b.hasCompactSupport.exists_bound_iteratedFDeriv b.contDiff (q + 2)
  let χ : Euc d → ℝ := fun x => b (ρ⁻¹ • x)
  have hχs : ContDiff ℝ ∞ χ := b.contDiff.comp (contDiff_const_smul _)
  have hχc : HasCompactSupport χ := b.hasCompactSupport.comp_smul (inv_ne_zero hρpos.ne')
  have hχone : ∀ x, ‖x‖ ≤ ρ → χ x = 1 := by
    intro x hx
    dsimp [χ]
    apply b.one_of_mem_closedBall
    have hn : ‖ρ⁻¹ • x‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρpos)]
      rw [inv_mul_le_iff₀ hρpos]
      simpa only [mul_one] using hx
    simpa [Metric.mem_closedBall, dist_zero_right] using hn
  have hχzero : ∀ x, 2 * ρ ≤ ‖x‖ → χ x = 0 := by
    intro x hx
    dsimp [χ]
    have hx' : 2 ≤ ‖ρ⁻¹ • x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρpos)]
      calc
        2 ≤ ‖x‖ / ρ := (le_div_iff₀ hρpos).2 hx
        _ = ρ⁻¹ * ‖x‖ := by rw [div_eq_mul_inv]; ring
    exact b.zero_of_le_dist (by simpa [dist_zero_right] using hx')
  refine ⟨χ, hχs, hχc, hχone, hχzero, C, hC0, ?_⟩
  intro j hj x
  have hcomp := iteratedFDeriv_comp_const_smul (𝕜 := ℝ) (i := j)
    (f := (b : Euc d → ℝ)) ρ⁻¹ (b.contDiff.of_le (by exact_mod_cast le_top))
  rw [show χ = fun y : Euc d => b (ρ⁻¹ • y) from rfl, hcomp]
  simp only [norm_smul, norm_pow, norm_inv, Real.norm_eq_abs, abs_of_pos hρpos]
  have hp : (ρ⁻¹) ^ j ≤ 1 :=
    pow_le_one₀ (inv_nonneg.2 hρpos.le) (inv_le_one_of_one_le₀ hρ)
  calc
    ρ⁻¹ ^ j * ‖iteratedFDeriv ℝ j (b : Euc d → ℝ) (ρ⁻¹ • x)‖ ≤ 1 * C :=
      mul_le_mul hp (hC j hj _) (norm_nonneg _) zero_le_one
    _ = C := one_mul C

#print axioms HRS.Fp81.S21.fp81s21_weightedRellich_scaledCutoff

end HRS.Fp81.S21
