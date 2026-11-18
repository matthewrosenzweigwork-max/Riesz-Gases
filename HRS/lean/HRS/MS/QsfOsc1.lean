import HRS.MS.QsfAsm11

/-!
# S4.5 oscillator clause, part 1: the ladder identity for Hermite functions

`h_n' = √(n/2) h_{n-1} - √((n+1)/2) h_{n+1}` and its `d`-dimensional form
`D h_α = ∑_i (√(α_i/2) h_{α-e_i} - √((α_i+1)/2) h_{α+e_i}) dx_i`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc cbNorm MemCb)

theorem s45_hc_succ (n : ℕ) : hermiteConst (n + 1) * Real.sqrt ((n : ℝ) + 1) = hermiteConst n := by
  unfold hermiteConst
  rw [Nat.factorial_succ]
  push_cast
  have h1 : 0 < ((n : ℝ) + 1) := by positivity
  have h2 : 0 < (n.factorial : ℝ) * Real.sqrt Real.pi := by positivity
  rw [mul_assoc, Real.sqrt_mul h1.le, mul_inv]
  have h3 : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.2 h1
  field_simp

theorem s45_hasDerivAt_hermiteFun (n : ℕ) (x : ℝ) :
    HasDerivAt (hermiteFun n)
      (Real.sqrt ((n : ℝ) / 2) * hermiteFun (n - 1) x -
        Real.sqrt (((n : ℝ) + 1) / 2) * hermiteFun (n + 1) x) x := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := by positivity
  have h := ((hasDerivAt_hermitePoly_sqrt n x).const_mul (hermiteConst n)).mul (hasDerivAt_gauss x)
  have hfun : hermiteFun n = fun y => hermiteConst n * hermitePoly n (Real.sqrt 2 * y) * gauss y := rfl
  rw [hfun]
  refine h.congr_deriv ?_
  cases n with
  | zero =>
    have hd0 : Polynomial.derivative (Polynomial.hermite 0) = 0 := by simp
    have c1 := s45_hc_succ 0
    simp only [hd0, map_zero, mul_zero, zero_mul, zero_add, Nat.cast_zero, zero_div, Real.sqrt_zero,
      Nat.zero_sub, zero_sub, Nat.zero_add, Nat.cast_one]
    simp only [hermiteFun_eq, hermitePoly, Polynomial.hermite_zero, Polynomial.hermite_one, map_one,
      Polynomial.aeval_X] at *
    simp only [Nat.cast_zero, zero_add, Nat.cast_one, Real.sqrt_one, mul_one] at c1
    have e : Real.sqrt (1 / 2) * Real.sqrt 2 = 1 := by
      rw [← Real.sqrt_mul (by norm_num)]; norm_num
    rw [← c1]
    linear_combination (hermiteConst 1 * x * gauss x) * e
  | succ k =>
    have hA : Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.derivative (Polynomial.hermite (k + 1))) =
        ((k : ℝ) + 1) * hermitePoly k (Real.sqrt 2 * x) :=
      (deriv_hermitePoly (k + 1) _).symm.trans (deriv_hermitePoly_succ k _)
    have hrec : hermitePoly (k + 2) (Real.sqrt 2 * x) = Real.sqrt 2 * x * hermitePoly (k + 1) (Real.sqrt 2 * x) -
        ((k : ℝ) + 1) * hermitePoly k (Real.sqrt 2 * x) := by
      rw [hermitePoly_succ (k + 1), deriv_hermitePoly_succ k]
    have c1 := s45_hc_succ k
    have c2 := s45_hc_succ (k + 1)
    push_cast at c2
    have hk1 : 0 < (k : ℝ) + 1 := by positivity
    have hk2 : 0 < (k : ℝ) + 1 + 1 := by positivity
    have hu : Real.sqrt ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1) = (k : ℝ) + 1 := Real.mul_self_sqrt hk1.le
    have hu0 : 0 < Real.sqrt ((k : ℝ) + 1) := Real.sqrt_pos.2 hk1
    have hv0 : 0 < Real.sqrt ((k : ℝ) + 1 + 1) := Real.sqrt_pos.2 hk2
    have hd1 : Real.sqrt (((k + 1 : ℕ) : ℝ) / 2) = Real.sqrt ((k : ℝ) + 1) / Real.sqrt 2 := by
      push_cast; exact Real.sqrt_div hk1.le 2
    have hd2 : Real.sqrt ((((k + 1 : ℕ) : ℝ) + 1) / 2) = Real.sqrt ((k : ℝ) + 1 + 1) / Real.sqrt 2 := by
      push_cast; exact Real.sqrt_div hk2.le 2
    rw [hd1, hd2, Nat.add_sub_cancel, hA]
    simp only [hermiteFun_eq]
    have e2 : (k + 1 + 1 : ℕ) = k + 2 := rfl
    rw [e2, hrec]
    have hc0 : hermiteConst k = hermiteConst (k + 1) * Real.sqrt ((k : ℝ) + 1) := c1.symm
    have hc2 : hermiteConst (k + 1) = hermiteConst (k + 2) * Real.sqrt ((k : ℝ) + 1 + 1) := c2.symm
    rw [hc0, hc2]
    field_simp
    have hu2 : Real.sqrt ((k : ℝ) + 1) ^ 2 = (k : ℝ) + 1 := Real.sq_sqrt hk1.le
    rw [hu2]
    linear_combination (hermiteConst (k + 2) * gauss x * ((k : ℝ) + 1) * hermitePoly k (Real.sqrt 2 * x)) * hs2

end S45

end
