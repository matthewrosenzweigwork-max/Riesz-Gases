import HRS.MS.Fp81S21WeightedGenNL10
import HRS.MS.R26T8AP10a1

/-! Gaussian multipliers for weighted source jets. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.ProClosureS111 HRS.MS.R26T8A HRS.MS.Wad

/-- A Gaussian times a polynomial weight is both bounded and square integrable. -/
theorem fp81s21_gaussian_weight_bounds {d : ℕ} {P c : ℝ}
    (hP : 0 ≤ P) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ x : Euc d, ‖Real.exp (-c * ‖x‖ ^ 2) * jbracket x ^ P‖ ≤ C) ∧
      MemLp (fun x : Euc d => Real.exp (-c * ‖x‖ ^ 2) * jbracket x ^ P) 2 volume := by
  obtain ⟨C, hC, hbound⟩ := r26t8a_p10a_poly_gauss P hc
  let g : Euc d → ℝ := fun x => Real.exp (-c * ‖x‖ ^ 2) * jbracket x ^ P
  have hgcont : Continuous g := by
    dsimp [g]
    apply Continuous.mul (by fun_prop)
    apply Continuous.rpow_const
    · unfold jbracket
      fun_prop
    · intro x
      exact Or.inl (s83_jb_pos x).ne'
  have hmajor : ∀ x, 0 ≤ g x ∧ g x ≤ C * Real.exp (-(c / 2) * ‖x‖ ^ 2) := by
    intro x
    have hp : 0 ≤ jbracket x ^ P := Real.rpow_nonneg (s83_jb_pos x).le _
    constructor
    · dsimp [g]; positivity
    · dsimp [g]
      have h := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (s83_jb_pos x).le (s83_jb_le_one_add x) hP)
        (Real.exp_pos (-c * ‖x‖ ^ 2)).le
      have hh := hbound ‖x‖ (norm_nonneg x)
      nlinarith
  have hexp : ∀ x : Euc d, Real.exp (-(c / 2) * ‖x‖ ^ 2) ≤ 1 := by
    intro x
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg ‖x‖]
  have hgb : ∀ x, ‖g x‖ ≤ C := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hmajor x).1]
    exact (hmajor x).2.trans (by nlinarith [hexp x])
  have hsq : Integrable (fun x => (g x) ^ 2) := by
    have hi := (r26t8a_p10a_gauss_int (d := d) (show 0 < c / 2 by positivity)).const_mul (C ^ 2)
    refine hi.mono' (hgcont.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hm := (hmajor x).2
    have hb := hgb x
    rw [Real.norm_eq_abs, abs_of_nonneg (hmajor x).1] at hb
    have he := (Real.exp_pos (-(c / 2) * ‖x‖ ^ 2)).le
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) (hmajor x).1,
      mul_nonneg (sub_nonneg.mpr hm) hC]
  exact ⟨C, hC, hgb, (memLp_two_iff_integrable_sq hgcont.aestronglyMeasurable).2 hsq⟩

#print axioms HRS.Fp81.S21.fp81s21_gaussian_weight_bounds
end HRS.Fp81.S21
