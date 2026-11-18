import HRS.MS.SpecAux90
import HRS.MS.SpecAux87

/-!
# S8M: weighted bounds for `∇ log ρ` and Gaussian-majorant calculus (S8.7, R4)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_lgr ρ = ∇ log ρ`.  Under `Mov2eRho`, `Mov2eEll`:
`D_v ρ = ρ ⟨ℓ, v⟩` (`s8p_fderiv_rho`), `ρ ‖ℓ‖² ≤ B₀` and `ρ ‖ℓ‖² ∈ L¹` (`s8p_lgr_bounds`), and elementary Gaussian
majorants (`s8p_r2_gauss`, `s8p_lin_gauss`, `s8p_good_of_gauss`) used to show that the functions entering the
`L⁴` estimate for `∇U` are bounded and integrable.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovDec

variable {d : ℕ} {ρ : Euc d → ℝ}

/-- `ℓ = ∇ log ρ`. -/
def s8p_lgr (ρ : Euc d → ℝ) (x : Euc d) : Euc d := gradient (fun y => Real.log (ρ y)) x

theorem s8p_fderiv_apply_grad (f : Euc d → ℝ) (x v : Euc d) :
    fderiv ℝ f x v = inner ℝ (gradient f x) v := by
  have := (InnerProductSpace.toDual ℝ (Euc d)).apply_symm_apply (fderiv ℝ f x)
  rw [← InnerProductSpace.toDual_apply_apply, gradient, this]

theorem s8p_fderiv_rho (hρ : Mov2eRho d ρ) (x v : Euc d) :
    fderiv ℝ ρ x v = ρ x * inner ℝ (s8p_lgr ρ x) v := by
  have hd : HasFDerivAt ρ (fderiv ℝ ρ x) x := ((hρ.data.smooth.differentiable (by simp)) x).hasFDerivAt
  have h1 := (hd.log (hρ.pos x).ne').fderiv
  have h2 : fderiv ℝ ρ x = ρ x • fderiv ℝ (fun y => Real.log (ρ y)) x := by
    rw [h1, smul_smul, mul_inv_cancel₀ (hρ.pos x).ne', one_smul]
  rw [h2]
  simp only [smul_apply, smul_eq_mul]
  rw [s8p_fderiv_apply_grad]; rfl

theorem s8p_r2_gauss {c : ℝ} (hc : 0 < c) (r : ℝ) :
    r ^ 2 * Real.exp (-c * r ^ 2) ≤ (2 / c) * Real.exp (-(c / 2) * r ^ 2) := by
  have h1 : (c / 2) * r ^ 2 ≤ Real.exp ((c / 2) * r ^ 2) := by
    linarith [Real.add_one_le_exp ((c / 2) * r ^ 2)]
  have e : Real.exp (-c * r ^ 2) = Real.exp (-(c / 2) * r ^ 2) * Real.exp (-(c / 2) * r ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (-(c / 2) * r ^ 2) * Real.exp ((c / 2) * r ^ 2) = 1 := by
    rw [← Real.exp_add]; simp
  have hp : 0 < Real.exp (-(c / 2) * r ^ 2) := Real.exp_pos _
  rw [e]
  have : r ^ 2 * (Real.exp (-(c / 2) * r ^ 2) * Real.exp (-(c / 2) * r ^ 2)) =
      (2 / c) * Real.exp (-(c / 2) * r ^ 2) * ((c / 2) * r ^ 2 * Real.exp (-(c / 2) * r ^ 2)) := by
    field_simp
  rw [this]
  have h3 : (c / 2) * r ^ 2 * Real.exp (-(c / 2) * r ^ 2) ≤ 1 := by
    calc (c / 2) * r ^ 2 * Real.exp (-(c / 2) * r ^ 2) ≤ Real.exp ((c / 2) * r ^ 2) * Real.exp (-(c / 2) * r ^ 2) :=
          mul_le_mul_of_nonneg_right h1 hp.le
      _ = 1 := by rw [mul_comm]; exact h2
  have h4 : 0 ≤ (2 / c) * Real.exp (-(c / 2) * r ^ 2) := by positivity
  nlinarith

theorem s8p_lin_gauss {c a M0 : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (hM0 : 0 ≤ M0) (r : ℝ) (hr : 0 ≤ r) :
    (a * r + M0) * Real.exp (-c * r ^ 2) ≤ (a / c + a / 2 + M0) * Real.exp (-(c / 2) * r ^ 2) := by
  have h1 := s8p_r2_gauss hc r
  have h2 : Real.exp (-c * r ^ 2) ≤ Real.exp (-(c / 2) * r ^ 2) :=
    Real.exp_le_exp.2 (by nlinarith [sq_nonneg r])
  have h3 : a * r ≤ (a / 2) * r ^ 2 + a / 2 := by nlinarith [sq_nonneg (r - 1)]
  have hp : 0 ≤ Real.exp (-c * r ^ 2) := (Real.exp_pos _).le
  calc (a * r + M0) * Real.exp (-c * r ^ 2) ≤ ((a / 2) * r ^ 2 + a / 2 + M0) * Real.exp (-c * r ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) hp
    _ = (a / 2) * (r ^ 2 * Real.exp (-c * r ^ 2)) + (a / 2 + M0) * Real.exp (-c * r ^ 2) := by ring
    _ ≤ (a / 2) * ((2 / c) * Real.exp (-(c / 2) * r ^ 2)) + (a / 2 + M0) * Real.exp (-(c / 2) * r ^ 2) := by
        gcongr
    _ = _ := by field_simp; ring

/-- Continuous functions with a Gaussian majorant are good. -/
theorem s8p_good_of_gauss {f : Euc d → ℝ} (hf : Continuous f) {C c : ℝ} (hc : 0 < c)
    (hb : ∀ x, |f x| ≤ C * Real.exp (-c * ‖x‖ ^ 2)) : s8p_Good f := by
  refine ⟨hf.measurable, ?_, |C|, fun x => ?_⟩
  · refine Integrable.mono' ((s8p_integrable_exp_neg_mul_sq_norm (V := Euc d) hc).const_mul C)
      hf.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]; exact hb x
  · refine (hb x).trans ?_
    have h1 : Real.exp (-c * ‖x‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖])
    calc C * Real.exp (-c * ‖x‖ ^ 2) ≤ |C| * Real.exp (-c * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
      _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = |C| := mul_one _

theorem s8p_lgr_bounds (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ) :
    ∃ B0 : ℝ, 0 ≤ B0 ∧ (∀ x, ρ x * ‖s8p_lgr ρ x‖ ^ 2 ≤ B0) ∧
      Integrable (fun x => ρ x * ‖s8p_lgr ρ x‖ ^ 2) := by
  obtain ⟨c, a, M0, hc, ha, hM0, hψb, hfs, hM0b, -⟩ := hE.ex
  obtain ⟨C, hC⟩ := hψb 0
  have hC' : ∀ x, Real.sqrt (ρ x) ≤ C * Real.exp (-c * ‖x‖ ^ 2) := fun x => by
    have := hC x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at this
  have hC0 : 0 ≤ C := by
    have h1 := hC' 0
    have h2 : 0 < Real.sqrt (ρ 0) := Real.sqrt_pos.2 (hρ.pos 0)
    by_contra hneg
    push_neg at hneg
    have : C * Real.exp (-c * ‖(0 : Euc d)‖ ^ 2) < 0 := mul_neg_of_neg_of_pos hneg (Real.exp_pos _)
    linarith
  set K : ℝ := 2 * C ^ 2 * (2 / c * a ^ 2 + M0 ^ 2) with hK
  have hK0 : 0 ≤ K := by positivity
  have key : ∀ x, ρ x * ‖s8p_lgr ρ x‖ ^ 2 ≤ K * Real.exp (-(c / 2) * ‖x‖ ^ 2) := by
    intro x
    set r := ‖x‖ with hr
    have hρx : ρ x ≤ C ^ 2 * Real.exp (-c * r ^ 2) ^ 2 := by
      have h1 : ρ x = Real.sqrt (ρ x) ^ 2 := (Real.sq_sqrt (hρ.pos x).le).symm
      rw [h1, ← mul_pow]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (hC' x) 2
    have hℓ : ‖s8p_lgr ρ x‖ ^ 2 ≤ 2 * a ^ 2 * r ^ 2 + 2 * M0 ^ 2 := by
      have h1 := hM0b x
      have h2 : ‖s8p_lgr ρ x‖ ≤ a * r + M0 := h1
      calc ‖s8p_lgr ρ x‖ ^ 2 ≤ (a * r + M0) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
        _ ≤ _ := by nlinarith [sq_nonneg (a * r - M0)]
    have he2 : Real.exp (-c * r ^ 2) ^ 2 = Real.exp (-c * r ^ 2) * Real.exp (-c * r ^ 2) := sq _
    have hr2 := s8p_r2_gauss hc r
    have hexp : Real.exp (-c * r ^ 2) ≤ Real.exp (-(c / 2) * r ^ 2) :=
      Real.exp_le_exp.2 (by nlinarith [sq_nonneg r])
    have hp : 0 < Real.exp (-c * r ^ 2) := Real.exp_pos _
    have hp2 : 0 < Real.exp (-(c / 2) * r ^ 2) := Real.exp_pos _
    calc ρ x * ‖s8p_lgr ρ x‖ ^ 2 ≤ (C ^ 2 * Real.exp (-c * r ^ 2) ^ 2) * (2 * a ^ 2 * r ^ 2 + 2 * M0 ^ 2) :=
          mul_le_mul hρx hℓ (sq_nonneg _) (by positivity)
      _ = 2 * C ^ 2 * (a ^ 2 * (r ^ 2 * Real.exp (-c * r ^ 2)) * Real.exp (-c * r ^ 2) +
            M0 ^ 2 * (Real.exp (-c * r ^ 2) * Real.exp (-c * r ^ 2))) := by rw [he2]; ring
      _ ≤ 2 * C ^ 2 * (a ^ 2 * ((2 / c) * Real.exp (-(c / 2) * r ^ 2)) * 1 +
            M0 ^ 2 * (Real.exp (-(c / 2) * r ^ 2) * 1)) := by
          have e1 : Real.exp (-c * r ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg r])
          gcongr
      _ = _ := by rw [hK]; ring
  refine ⟨K, hK0, fun x => (key x).trans ?_, ?_⟩
  · have : Real.exp (-(c / 2) * ‖x‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖])
    nlinarith
  · have hcont : Continuous fun x => ρ x * ‖s8p_lgr ρ x‖ ^ 2 := by
      have h1 : Continuous ρ := hρ.data.smooth.continuous
      have h2 : Continuous (s8p_lgr ρ) := hfs.continuous
      exact h1.mul (h2.norm.pow 2)
    refine Integrable.mono' ((s8p_integrable_exp_neg_mul_sq_norm (V := Euc d) (b := c / 2)
      (by positivity)).const_mul K) hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ.pos x).le (sq_nonneg _))]
    exact key x

end HRS.MS.Spec
