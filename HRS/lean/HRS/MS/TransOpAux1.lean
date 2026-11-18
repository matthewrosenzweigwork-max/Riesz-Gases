import HRS.Whole.Oscillator

/-!
# S611 (row S6.11): translation operator on `B_m` -- plan, and Hermite facts (packet P1a)

Namespace `HRS.MS.TransOp`, helper prefix `s611_`.  See `docs/handoff/S611_PLAN.md` for the full plan; summary:

Goal: `mov_translated_prepared` / `mov_translated_stationary` (`HRS/Whole/MovingDyn.lean`) as clean conditional reductions on
`h21ii : type_of% @HRS.Whole.whole_space_prepared`, `h21i : type_of% @HRS.Whole.whole_space_stationary`.
Missing infrastructure (previous worker S64, `MovSchAux17`): (a) the translation operator `Lambda_c` on `B_m = OscDual d m`,
(b) conjugation of the linear Gaussian evolution by translation, (c) `IsResultingSolution` for the constant solution.

Packets:
* `TransOpAux1` (this file): Hermite derivative recurrence `h_n' = sqrt(n/2) h_{n-1} - sqrt((n+1)/2) h_{n+1}`, Gaussian decay
  `|h_alpha(x)| <= C exp(-|x|^2/8)`, derivative of `t -> h_alpha(y + t e_i)`.
* `TransOpAux2`: the coefficient ODE `A_alpha' = a_alpha A_{alpha - e_i} - b_alpha A_{alpha + e_i}` of `A_alpha(t) = <f, h_alpha(. + t e_i)>`,
  and the capped-weight energy estimate `|E_N'| <= K E_N`, `K = 2 m 3^m` (the boundary terms vanish because the weight is capped).
* `TransOpAux3`: Gronwall; `Sigma^m` bound for the axis translations and for `phi(. + c)`: `MemOsc m phi -> MemOsc m phi(. + c)`,
  `oscNorm m phi(. + c) <= exp(K |c|_1 / 2) oscNorm m phi` (the TeX has the polynomial bound `C (1+|c|)^m`; the exponential bound
  suffices because the constants of S6.11 may depend on `b`).
* `TransOpAux4+`: the dual operator `Lambda_c`, path operator, conjugation of propagator / noise covariance / susceptibility,
  `IsResultingSolution` for `rho_beta`, and the final ties.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.TransOp

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s611_hermiteConst_nonneg (n : ℕ) : 0 ≤ hermiteConst n := by
  unfold hermiteConst; positivity

theorem s611_hermiteConst_succ (n : ℕ) :
    hermiteConst (n + 1) * Real.sqrt ((n : ℝ) + 1) = hermiteConst n := by
  have h1 : 0 ≤ hermiteConst (n + 1) * Real.sqrt ((n : ℝ) + 1) :=
    mul_nonneg (s611_hermiteConst_nonneg _) (Real.sqrt_nonneg _)
  have h2 := s611_hermiteConst_nonneg n
  refine (sq_eq_sq₀ h1 h2).1 ?_
  rw [mul_pow, Real.sq_sqrt (by positivity), hermiteConst_sq, hermiteConst_sq, Nat.factorial_succ]
  push_cast
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  field_simp

/-- The derivative recurrence `h_n' = sqrt(n/2) h_{n-1} - sqrt((n+1)/2) h_{n+1}`. -/
theorem s611_hasDerivAt_hermiteFun (n : ℕ) (x : ℝ) :
    HasDerivAt (hermiteFun n)
      (Real.sqrt n / Real.sqrt 2 * hermiteFun (n - 1) x -
        Real.sqrt ((n : ℝ) + 1) / Real.sqrt 2 * hermiteFun (n + 1) x) x := by
  have hfun : hermiteFun n = fun y => hermiteConst n * hermitePoly n (Real.sqrt 2 * y) * gauss y :=
    funext fun y => hermiteFun_eq n y
  have d1 := hasDerivAt_hermitePoly_sqrt n x
  have d2 := hasDerivAt_gauss x
  have hd := (d1.const_mul (hermiteConst n)).mul d2
  rw [hfun]
  refine hd.congr_deriv ?_
  set s := Real.sqrt 2 with hs
  have hs2 : s * s = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < s := Real.sqrt_pos.2 (by norm_num)
  set y := s * x with hy
  have hP : Polynomial.aeval y (Polynomial.derivative (Polynomial.hermite n)) =
      deriv (hermitePoly n) y := (deriv_hermitePoly n y).symm
  rw [hP]
  cases n with
  | zero =>
    have h0 : deriv (hermitePoly 0) y = 0 := by
      rw [deriv_hermitePoly]; simp
    have hH0 : hermitePoly 0 y = 1 := by simp [hermitePoly]
    have hH1 : hermitePoly 1 y = y := by
      have := hermitePoly_succ 0 y
      rw [h0, hH0] at this
      simpa using this
    have hc1 := s611_hermiteConst_succ 0
    simp only [Nat.cast_zero, zero_add, Real.sqrt_one, mul_one] at hc1
    rw [hermiteFun_eq 1 x, hH1, hc1, h0, hH0]
    simp only [Nat.cast_zero, Real.sqrt_zero, zero_div, zero_mul, zero_sub, mul_zero, zero_add, one_mul]
    simp only [hy]
    field_simp
    ring
  | succ k =>
    have hP' : deriv (hermitePoly (k + 1)) y = ((k : ℝ) + 1) * hermitePoly k y := by
      rw [deriv_hermitePoly_succ]
    have hF1 := hermitePoly_succ (k + 1) y
    rw [hP'] at hF1
    have hc1 := s611_hermiteConst_succ k
    have hc2 := s611_hermiteConst_succ (k + 1)
    have hk1 : Real.sqrt ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1) = (k : ℝ) + 1 :=
      Real.mul_self_sqrt (by positivity)
    have hk2 : Real.sqrt (((k + 1 : ℕ) : ℝ) + 1) * Real.sqrt (((k + 1 : ℕ) : ℝ) + 1) = (k : ℝ) + 2 := by
      rw [Real.mul_self_sqrt (by positivity)]; push_cast; ring
    have hsk : 0 < Real.sqrt ((k : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    have hsk2 : 0 < Real.sqrt (((k + 1 : ℕ) : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    simp only [Nat.add_sub_cancel]
    rw [hermiteFun_eq k x, hermiteFun_eq (k + 2) x, ← hy]
    have hxy : x = y / s := by rw [hy]; field_simp
    have hNk : hermiteConst k = hermiteConst (k + 1) * Real.sqrt ((k : ℝ) + 1) := hc1.symm
    have hNk2 : hermiteConst (k + 1) = hermiteConst (k + 1 + 1) *
        Real.sqrt (((k + 1 : ℕ) : ℝ) + 1) := hc2.symm
    rw [hNk]
    push_cast at hk2 ⊢
    have e1 : hermitePoly (k + 2) y = y * hermitePoly (k + 1) y - ((k : ℝ) + 1) * hermitePoly k y := by
      have := hF1; push_cast at this ⊢; linarith
    rw [e1, hxy, hP']
    have hN' : hermiteConst (k + 1) = hermiteConst (k + 2) * Real.sqrt ((k : ℝ) + 1 + 1) := by
      simpa using hNk2
    rw [hN']
    field_simp
    linear_combination (hermiteConst (k + 2) * gauss (y / s) *
        hermitePoly k y * ((k : ℝ) + 1)) * hs2 -
      (hermiteConst (k + 2) * gauss (y / s) * hermitePoly k y) * hk1

/-! ### Gaussian decay -/

theorem s611_abs_poly_le (p : Polynomial ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |p.eval x| ≤ C * Real.exp (3 * x ^ 2 / 8) := by
  refine ⟨∑ k ∈ Finset.range (p.natDegree + 1),
    |p.coeff k| * (k.factorial : ℝ) * Real.exp (2 / 3), by positivity, fun x => ?_⟩
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul, abs_pow]
  have h1 := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) k
  have hk : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have h2 : |x| ^ k ≤ (k.factorial : ℝ) * Real.exp |x| := by
    rwa [div_le_iff₀ hk, mul_comm] at h1
  have h3 : Real.exp |x| ≤ Real.exp (2 / 3) * Real.exp (3 * x ^ 2 / 8) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith [sq_nonneg (|x| - 4 / 3), sq_abs x]
  calc |p.coeff k| * |x| ^ k ≤ |p.coeff k| * ((k.factorial : ℝ) * Real.exp |x|) :=
        mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ ≤ |p.coeff k| * ((k.factorial : ℝ) * (Real.exp (2 / 3) * Real.exp (3 * x ^ 2 / 8))) := by
        gcongr
    _ = |p.coeff k| * (k.factorial : ℝ) * Real.exp (2 / 3) * Real.exp (3 * x ^ 2 / 8) := by ring

theorem s611_hermiteFun_gauss_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |hermiteFun n x| ≤ C * Real.exp (-(x ^ 2 / 8)) := by
  obtain ⟨p, hp⟩ := hermiteFun_eq_poly' n
  obtain ⟨C, hC0, hC⟩ := s611_abs_poly_le p
  refine ⟨C, hC0, fun x => ?_⟩
  have hg : gauss x = Real.exp (-(x ^ 2 / 2)) := rfl
  rw [hp x, abs_mul, hg, abs_of_pos (Real.exp_pos _)]
  calc |p.eval x| * Real.exp (-(x ^ 2 / 2)) ≤ C * Real.exp (3 * x ^ 2 / 8) * Real.exp (-(x ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_right (hC x) (Real.exp_pos _).le
    _ = C * Real.exp (-(x ^ 2 / 8)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem s611_hermiteFunD_gauss_bound (α : MultiIndex d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Euc d, |hermiteFunD α x| ≤ C * Real.exp (-(‖x‖ ^ 2 / 8)) := by
  choose C0 hC0 hC using fun i : Fin d => s611_hermiteFun_gauss_bound (α i)
  refine ⟨∏ i, C0 i, Finset.prod_nonneg fun i _ => hC0 i, fun x => ?_⟩
  unfold hermiteFunD
  rw [Finset.abs_prod]
  calc ∏ i, |hermiteFun (α i) (x i)| ≤ ∏ i, (C0 i * Real.exp (-(x i ^ 2 / 8))) :=
        Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => hC i (x i)
    _ = (∏ i, C0 i) * Real.exp (-(‖x‖ ^ 2 / 8)) := by
        rw [Finset.prod_mul_distrib, ← Real.exp_sum, EuclideanSpace.real_norm_sq_eq]
        congr 2
        rw [Finset.sum_neg_distrib, ← Finset.sum_div]

/-! ### Axis derivatives of `h_alpha` -/

/-- The unit vector `e_i`. -/
def s611_e (i : Fin d) : Euc d := EuclideanSpace.single i (1 : ℝ)

/-- `alpha - e_i` (truncated at `0`). -/
def s611_dec (α : MultiIndex d) (i : Fin d) : MultiIndex d := Function.update α i (α i - 1)

/-- `alpha + e_i`. -/
def s611_inc (α : MultiIndex d) (i : Fin d) : MultiIndex d := Function.update α i (α i + 1)

theorem s611_hermiteFunD_update (α : MultiIndex d) (i : Fin d) (k : ℕ) (z : Euc d) :
    hermiteFunD (Function.update α i k) z =
      (∏ j ∈ Finset.univ.erase i, hermiteFun (α j) (z j)) * hermiteFun k (z i) := by
  rw [hermiteFunD_split (Function.update α i k) i z]
  congr 1
  · refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  · simp

theorem s611_hasDerivAt_axis (α : MultiIndex d) (i : Fin d) (y : Euc d) (t : ℝ) :
    HasDerivAt (fun τ : ℝ => hermiteFunD α (y + τ • s611_e i))
      (Real.sqrt (α i) / Real.sqrt 2 * hermiteFunD (s611_dec α i) (y + t • s611_e i) -
        Real.sqrt ((α i : ℝ) + 1) / Real.sqrt 2 * hermiteFunD (s611_inc α i) (y + t • s611_e i)) t := by
  have hcoord : ∀ τ : ℝ, (y + τ • s611_e i) i = y i + τ := fun τ => by
    simp [s611_e]
  have hother : ∀ (τ : ℝ) (j : Fin d), j ≠ i → (y + τ • s611_e i) j = y j := fun τ j hj => by
    simp [s611_e, hj]
  have hfun : (fun τ : ℝ => hermiteFunD α (y + τ • s611_e i)) =
      fun τ => (∏ j ∈ Finset.univ.erase i, hermiteFun (α j) (y j)) * hermiteFun (α i) (y i + τ) := by
    funext τ
    rw [hermiteFunD_split α i, hcoord]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [hother τ j (Finset.ne_of_mem_erase hj)]
  rw [hfun]
  have h1 := s611_hasDerivAt_hermiteFun (α i) (y i + t)
  have h2 : HasDerivAt (fun τ : ℝ => hermiteFun (α i) (y i + τ)) _ t :=
    HasDerivAt.comp_const_add (y i) t (by simpa using h1)
  have h3 := h2.const_mul (∏ j ∈ Finset.univ.erase i, hermiteFun (α j) (y j))
  refine h3.congr_deriv ?_
  unfold s611_dec s611_inc
  rw [s611_hermiteFunD_update, s611_hermiteFunD_update, hcoord]
  have hprod : (∏ j ∈ Finset.univ.erase i, hermiteFun (α j) ((y + t • s611_e i) j)) =
      ∏ j ∈ Finset.univ.erase i, hermiteFun (α j) (y j) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [hother t j (Finset.ne_of_mem_erase hj)]
  rw [hprod]
  ring

end HRS.MS.TransOp

end
