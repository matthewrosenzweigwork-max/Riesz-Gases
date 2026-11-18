import HRS.MC.Sec7Vocab

/-!
# Packet `slow_correction` (S16f), part 1: `v(z) = exp(-|z|^2)` is in `C_b^5(R^2)`

`exp(-x^2/2)` has the derivatives `(-1)^n He_n(x) exp(-x^2/2)` (Mathlib, Hermite polynomials), which are bounded;
`v(z) = exp(-(sqrt 2 z_0)^2/2) exp(-(sqrt 2 z_1)^2/2)` is a product of two such functions composed with
continuous linear forms.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S16f

open HRS HRS.Sec7 HRS.MC.Sec7

/-- `|x|^n exp(-x^2/2)` is bounded. -/
theorem s16f_pow_gauss_le (n : ℕ) (x : ℝ) :
    |x| ^ n * Real.exp (-(x ^ 2 / 2)) ≤ 1 + 2 ^ n * (n.factorial : ℝ) := by
  have h1 : (x ^ 2 / 2) ^ n / (n.factorial : ℝ) ≤ Real.exp (x ^ 2 / 2) :=
    Real.pow_div_factorial_le_exp _ (by positivity) n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have h2 : |x| ^ (2 * n) ≤ 2 ^ n * n.factorial * Real.exp (x ^ 2 / 2) := by
    have : |x| ^ (2 * n) = (x ^ 2) ^ n := by rw [pow_mul, sq_abs]
    rw [this]
    have h3 : (x ^ 2 / 2) ^ n = (x ^ 2) ^ n / 2 ^ n := by rw [div_pow]
    rw [h3, div_div, div_le_iff₀ (by positivity)] at h1
    calc (x ^ 2) ^ n ≤ Real.exp (x ^ 2 / 2) * (2 ^ n * n.factorial) := h1
      _ = _ := by ring
  have hE : 0 < Real.exp (-(x ^ 2 / 2)) := Real.exp_pos _
  have hE1 : Real.exp (-(x ^ 2 / 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg x]
  have hmul : Real.exp (x ^ 2 / 2) * Real.exp (-(x ^ 2 / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have h4 : |x| ^ n ≤ 1 + |x| ^ (2 * n) := by
    rcases le_total |x| 1 with h | h
    · have := pow_le_one₀ (abs_nonneg x) h (n := n)
      have : 0 ≤ |x| ^ (2 * n) := by positivity
      linarith
    · calc |x| ^ n ≤ |x| ^ (2 * n) := pow_le_pow_right₀ h (by omega)
        _ ≤ _ := by linarith
  calc |x| ^ n * Real.exp (-(x ^ 2 / 2)) ≤ (1 + |x| ^ (2 * n)) * Real.exp (-(x ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_right h4 hE.le
    _ = Real.exp (-(x ^ 2 / 2)) + |x| ^ (2 * n) * Real.exp (-(x ^ 2 / 2)) := by ring
    _ ≤ 1 + 2 ^ n * n.factorial := by
        have : |x| ^ (2 * n) * Real.exp (-(x ^ 2 / 2)) ≤
            2 ^ n * n.factorial * Real.exp (x ^ 2 / 2) * Real.exp (-(x ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_right h2 hE.le
        rw [mul_assoc, hmul, mul_one] at this
        linarith

/-- a polynomial times the Gaussian is bounded -/
theorem s16f_poly_gauss_bdd (p : Polynomial ℤ) :
    ∃ C : ℝ, ∀ x : ℝ, |Polynomial.aeval x p| * Real.exp (-(x ^ 2 / 2)) ≤ C := by
  refine ⟨∑ i ∈ Finset.range (p.natDegree + 1), |(p.coeff i : ℝ)| * (1 + 2 ^ i * (i.factorial : ℝ)), fun x => ?_⟩
  rw [Polynomial.aeval_eq_sum_range]
  simp only [zsmul_eq_mul]
  calc |∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i : ℝ) * x ^ i| * Real.exp (-(x ^ 2 / 2))
      ≤ (∑ i ∈ Finset.range (p.natDegree + 1), |(p.coeff i : ℝ) * x ^ i|) * Real.exp (-(x ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Real.exp_pos _).le
    _ = ∑ i ∈ Finset.range (p.natDegree + 1), |(p.coeff i : ℝ)| * (|x| ^ i * Real.exp (-(x ^ 2 / 2))) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [abs_mul, abs_pow]; ring
    _ ≤ _ := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (s16f_pow_gauss_le i x) (abs_nonneg _)

theorem s16f_gauss1_contDiff : ContDiff ℝ ⊤ (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) := by
  fun_prop

theorem s16f_gauss1_iter_bdd (j : ℕ) :
    ∃ M : ℝ, ∀ y : ℝ, ‖iteratedFDeriv ℝ j (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) y‖ ≤ M := by
  obtain ⟨C, hC⟩ := s16f_poly_gauss_bdd (Polynomial.hermite j)
  refine ⟨C, fun y => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
    Polynomial.deriv_gaussian_eq_hermite_mul_gaussian, Real.norm_eq_abs]
  have : |(-1 : ℝ) ^ j * Polynomial.aeval y (Polynomial.hermite j) * Real.exp (-(y ^ 2 / 2))| =
      |Polynomial.aeval y (Polynomial.hermite j)| * Real.exp (-(y ^ 2 / 2)) := by
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos (Real.exp_pos _)]
  rw [this]
  exact hC y

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem s16f_memCb_gauss1 (L : E →L[ℝ] ℝ) :
    MemCb 5 (fun x : E => Real.exp (-((L x) ^ 2 / 2))) := by
  refine ⟨(s16f_gauss1_contDiff.of_le le_top).comp L.contDiff, fun j hj => ?_⟩
  obtain ⟨M, hM⟩ := s16f_gauss1_iter_bdd j
  refine ⟨M * ‖L‖ ^ j, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hcd : ContDiff ℝ j (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) :=
    (s16f_gauss1_contDiff.of_le le_top)
  have e := L.iteratedFDeriv_comp_right (f := fun y : ℝ => Real.exp (-(y ^ 2 / 2))) hcd x
    (i := j) le_rfl
  show ‖iteratedFDeriv ℝ j ((fun y : ℝ => Real.exp (-(y ^ 2 / 2))) ∘ L) x‖ ≤ M * ‖L‖ ^ j
  rw [e]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul_of_nonneg_right (hM _) (by positivity)

/-- the radial Gaussian `v(z) = exp(-|z|^2)` on `R^2` -/
def s16f_v : EuclideanSpace ℝ (Fin 2) → ℝ := fun z => Real.exp (-‖z‖ ^ 2)

theorem s16f_v_eq (z : EuclideanSpace ℝ (Fin 2)) :
    s16f_v z = Real.exp (-((Real.sqrt 2 * z 0) ^ 2 / 2)) * Real.exp (-((Real.sqrt 2 * z 1) ^ 2 / 2)) := by
  unfold s16f_v
  rw [← Real.exp_add, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp only [Real.norm_eq_abs, sq_abs]
  congr 1
  rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
  ring

theorem s16f_memCb_v : MemCb 5 s16f_v := by
  let L0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
    Real.sqrt 2 • (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
  let L1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
    Real.sqrt 2 • (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
  have h0 := s16f_memCb_gauss1 L0
  have h1 := s16f_memCb_gauss1 L1
  have := (Tilt715Aux.memCb_mul_bound h0 h1).1
  have e : s16f_v = fun x => Real.exp (-((L1 x) ^ 2 / 2)) * Real.exp (-((L0 x) ^ 2 / 2)) := by
    funext x
    rw [s16f_v_eq, mul_comm]
    rfl
  rw [e]
  exact this

theorem s16f_memCb_v_sq : MemCb 5 (fun z => s16f_v z ^ 2) := by
  have := (Tilt715Aux.memCb_mul_bound s16f_memCb_v s16f_memCb_v).1
  simpa [sq] using this

theorem s16f_v_pos (z : EuclideanSpace ℝ (Fin 2)) : 0 < s16f_v z := Real.exp_pos _

theorem s16f_v_le_one (z : EuclideanSpace ℝ (Fin 2)) : s16f_v z ≤ 1 := by
  unfold s16f_v
  rw [Real.exp_le_one_iff]
  nlinarith [sq_nonneg ‖z‖]

end HRS.MC.Sec7.S16f

end
