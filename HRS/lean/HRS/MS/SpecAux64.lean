import HRS.MS.SpecAux63

/-!
# S8R: the diagonal semigroup contracts exponentially (S8.7, packet C6)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.

* `s8p_coord_semiDiag`: `coord (semiDiag om s z) l = e^{-s om_l} coord z l` for `s ≥ 0`;
* `s8p_semiDiag_enorm_sq_le`: `‖semiDiag om s z‖² ≤ e^{-2 s om_0} ‖z‖²`;
* `s8p_lintegral_exp_le`: `∫_0^t e^{-c(t-r)} dr ≤ 1/c`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace HRS.MS.Spec

open HRS HRS.Whole

theorem s8p_coord_semiDiag {om : ℕ → ℝ} (hom : ∀ l, 0 < om l) {s : ℝ} (hs : 0 ≤ s) (z : SeqL2)
    (l : ℕ) : SeqL2.coord (semiDiag om s z) l = Real.exp (-s * om l) * SeqL2.coord z l :=
  u11_coord_ofSeq (u11_diag_memℓp om hom hs z) l

theorem s8p_semiDiag_enorm_sq_le {om : ℕ → ℝ} (hom : ∀ l, 0 < om l) (hmono : Monotone om) {s : ℝ}
    (hs : 0 ≤ s) (z : SeqL2) :
    ‖semiDiag om s z‖ₑ ^ 2 ≤ ENNReal.ofReal (Real.exp (-(2 * s * om 0))) * ‖z‖ₑ ^ 2 := by
  rw [s8p_seq_enorm_sq, s8p_seq_enorm_sq, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun l => ?_
  rw [s8p_coord_semiDiag hom hs, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : Real.exp (-s * om l) ^ 2 ≤ Real.exp (-(2 * s * om 0)) := by
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.2 ?_
    have := hmono (Nat.zero_le l)
    push_cast
    nlinarith
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)

theorem s8p_lintegral_exp_le {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ r in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(c * (t - r)))) ≤ ENNReal.ofReal (1 / c) := by
  have hcont : Continuous fun r : ℝ => Real.exp (-(c * (t - r))) := by fun_prop
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc)
    (Filter.Eventually.of_forall fun r => (Real.exp_pos _).le)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]
  have hderiv : ∀ r ∈ Set.uIcc 0 t, HasDerivAt (fun r : ℝ => Real.exp (-(c * (t - r))) / c)
      (Real.exp (-(c * (t - r)))) r := by
    intro r _
    have h1 : HasDerivAt (fun r : ℝ => -(c * (t - r))) c r := by
      have h := ((((hasDerivAt_id r).const_sub t).const_mul c).neg)
      convert h using 1
      · funext y; simp
      · simp
    have h2 := (h1.exp).div_const c
    convert h2 using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  have h0 : 0 ≤ Real.exp (-(c * (t - 0))) / c := by positivity
  simp only [sub_self, mul_zero, neg_zero, Real.exp_zero]
  linarith

end HRS.MS.Spec
