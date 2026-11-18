import HRS.Whole.Oscillator

/-!
# MOV-A1, part 1: the Hermite ladder and the coefficient formulas

Namespace `HRS.MS.MovOsc` (helpers `mova1_`, main statements `mo_`).  Infrastructure for the calculus of the
oscillator scale `Σ^r`; these are not manuscript rows.

* one-dimensional ladder: `x h_n = √((n+1)/2) h_{n+1} + √(n/2) h_{n-1}`,
  `h_n' = √(n/2) h_{n-1} - √((n+1)/2) h_{n+1}` (`mova1_x_hermiteFun`, `mova1_deriv_hermiteFun`);
* `d`-dimensional: with `α ± e_j` realised by `Function.update` (`mova1_up`, `mova1_dn`; `α - e_j = α`
  if `α_j = 0`, where the coefficient `√(α_j/2)` vanishes),
  `mo_coeff_xmul : c_α(x_j f) = √((α_j+1)/2) c_{α+e_j}(f) + √(α_j/2) c_{α-e_j}(f)` and
  `mo_coeff_partial : c_α(∂_j f) = √((α_j+1)/2) c_{α+e_j}(f) - √(α_j/2) c_{α-e_j}(f)`
  for Schwartz `f` (`c_α = hermiteCoeff`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovOsc

open HRS HRS.Whole

variable {d : ℕ}

/-! ### One-dimensional ladder -/

theorem mova1_hermiteConst_pos (n : ℕ) : 0 < hermiteConst n := by
  unfold hermiteConst
  have : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  positivity

/-- `c_m = √(m+1) c_{m+1}`. -/
theorem mova1_const_succ (m : ℕ) :
    hermiteConst m = Real.sqrt ((m : ℝ) + 1) * hermiteConst (m + 1) := by
  have h1 := hermiteConst_sq m
  have h2 := hermiteConst_sq (m + 1)
  have hp := mova1_hermiteConst_pos m
  have hq := mova1_hermiteConst_pos (m + 1)
  have hfac : (((m + 1).factorial : ℕ) : ℝ) = ((m : ℝ) + 1) * (m.factorial : ℝ) := by
    push_cast [Nat.factorial_succ]; ring
  have hf : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hsq : hermiteConst m ^ 2 = ((m : ℝ) + 1) * hermiteConst (m + 1) ^ 2 := by
    rw [h1, h2, hfac]
    field_simp
  have h3 : (Real.sqrt ((m : ℝ) + 1) * hermiteConst (m + 1)) ^ 2 = hermiteConst m ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), hsq]
  exact ((pow_left_inj₀ hp.le (by positivity) two_ne_zero).1 h3.symm)

/-- `y He_n(y) = He_{n+1}(y) + n He_{n-1}(y)` (`n - 1` truncated; for `n = 0` the second term vanishes). -/
theorem mova1_poly_rec (n : ℕ) (y : ℝ) :
    y * hermitePoly n y = hermitePoly (n + 1) y + (n : ℝ) * hermitePoly (n - 1) y := by
  cases n with
  | zero =>
    have h := hermitePoly_succ 0 y
    have h0 : hermitePoly 0 = fun _ => (1 : ℝ) := by
      funext z; simp [hermitePoly]
    rw [h0] at h
    simp at h
    simp [h0, h]
  | succ m =>
    have h := hermitePoly_succ (m + 1) y
    rw [deriv_hermitePoly_succ m y] at h
    simp only [Nat.add_sub_cancel]
    push_cast
    linarith

theorem mova1_deriv_poly (n : ℕ) (y : ℝ) :
    deriv (hermitePoly n) y = (n : ℝ) * hermitePoly (n - 1) y := by
  cases n with
  | zero =>
    have h0 : hermitePoly 0 = fun _ => (1 : ℝ) := by
      funext z; simp [hermitePoly]
    simp [h0]
  | succ m =>
    rw [deriv_hermitePoly_succ m y]
    simp

theorem mova1_xP (n : ℕ) (x : ℝ) :
    Real.sqrt 2 * (x * hermitePoly n (Real.sqrt 2 * x)) =
      hermitePoly (n + 1) (Real.sqrt 2 * x) + (n : ℝ) * hermitePoly (n - 1) (Real.sqrt 2 * x) := by
  have := mova1_poly_rec n (Real.sqrt 2 * x)
  linarith

theorem mova1_hasDerivAt_hermiteFun (n : ℕ) (x : ℝ) :
    HasDerivAt (hermiteFun n)
      (hermiteConst n * (Real.sqrt 2 * ((n : ℝ) * hermitePoly (n - 1) (Real.sqrt 2 * x)) * gauss x +
        hermitePoly n (Real.sqrt 2 * x) * (-x * gauss x))) x := by
  have h1 := hasDerivAt_hermitePoly_sqrt n x
  have h2 := hasDerivAt_gauss x
  have h3 := (h1.mul h2).const_mul (hermiteConst n)
  have e : hermiteFun n = fun y => hermiteConst n * (hermitePoly n (Real.sqrt 2 * y) * gauss y) := by
    funext y; rw [hermiteFun_eq]; ring
  rw [e]
  refine h3.congr_deriv ?_
  rw [← deriv_hermitePoly, mova1_deriv_poly]

/-- `x h_n(x) = √((n+1)/2) h_{n+1}(x) + √(n/2) h_{n-1}(x)`. -/
theorem mova1_x_hermiteFun (n : ℕ) (x : ℝ) :
    x * hermiteFun n x = Real.sqrt (((n : ℝ) + 1) / 2) * hermiteFun (n + 1) x +
      Real.sqrt ((n : ℝ) / 2) * hermiteFun (n - 1) x := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2p : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hr := mova1_xP n x
  rw [hermiteFun_eq, hermiteFun_eq, hermiteFun_eq]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hc1 : hermiteConst 0 = hermiteConst 1 := by
      have := mova1_const_succ 0
      simpa using this
    simp only [Nat.cast_zero, zero_add, zero_div, Real.sqrt_zero, zero_mul, add_zero, Nat.zero_sub] at hr ⊢
    rw [← hc1, Real.sqrt_div (by norm_num), Real.sqrt_one]
    generalize Real.sqrt 2 * x = y at hr ⊢
    field_simp
    linear_combination (hermiteConst 0 * gauss x) * hr
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hc0 : hermiteConst m = Real.sqrt ((m : ℝ) + 1) * hermiteConst (m + 1) := mova1_const_succ m
    have hc2 : hermiteConst (m + 1) = Real.sqrt ((m : ℝ) + 1 + 1) * hermiteConst (m + 2) :=
      mova1_const_succ (m + 1) |>.trans (by push_cast; rfl)
    simp only [Nat.add_sub_cancel] at hr ⊢
    push_cast at hr ⊢
    have e1 : Real.sqrt (((m : ℝ) + 1 + 1) / 2) = Real.sqrt ((m : ℝ) + 1 + 1) / Real.sqrt 2 :=
      Real.sqrt_div (by positivity) _
    have e2 : Real.sqrt (((m : ℝ) + 1) / 2) = Real.sqrt ((m : ℝ) + 1) / Real.sqrt 2 :=
      Real.sqrt_div (by positivity) _
    have q1 : Real.sqrt ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1) = (m : ℝ) + 1 :=
      Real.mul_self_sqrt (by positivity)
    have hcc : hermiteConst (m + 1 + 1) = hermiteConst (m + 2) := rfl
    rw [e1, e2, hc0, hc2, hcc]
    generalize Real.sqrt 2 * x = y at hr ⊢
    field_simp
    linear_combination (hermiteConst (m + 2) * gauss x) * hr -
      (hermiteConst (m + 2) * gauss x * hermitePoly m y) * q1

/-- `h_n' = √(n/2) h_{n-1} - √((n+1)/2) h_{n+1}`. -/
theorem mova1_deriv_hermiteFun (n : ℕ) (x : ℝ) :
    deriv (hermiteFun n) x = Real.sqrt ((n : ℝ) / 2) * hermiteFun (n - 1) x -
      Real.sqrt (((n : ℝ) + 1) / 2) * hermiteFun (n + 1) x := by
  rw [(mova1_hasDerivAt_hermiteFun n x).deriv]
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2p : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hr := mova1_xP n x
  rw [hermiteFun_eq, hermiteFun_eq]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hc1 : hermiteConst 0 = hermiteConst 1 := by
      have := mova1_const_succ 0
      simpa using this
    simp only [Nat.cast_zero, zero_add, zero_div, Real.sqrt_zero, zero_mul, add_zero, Nat.zero_sub,
      mul_zero] at hr ⊢
    rw [← hc1, Real.sqrt_div (by norm_num), Real.sqrt_one]
    generalize Real.sqrt 2 * x = y at hr ⊢
    field_simp
    linear_combination (-(hermiteConst 0 * gauss x)) * hr
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hc0 : hermiteConst m = Real.sqrt ((m : ℝ) + 1) * hermiteConst (m + 1) := mova1_const_succ m
    have hc2 : hermiteConst (m + 1) = Real.sqrt ((m : ℝ) + 1 + 1) * hermiteConst (m + 2) :=
      mova1_const_succ (m + 1) |>.trans (by push_cast; rfl)
    simp only [Nat.add_sub_cancel] at hr ⊢
    push_cast at hr ⊢
    have e1 : Real.sqrt (((m : ℝ) + 1 + 1) / 2) = Real.sqrt ((m : ℝ) + 1 + 1) / Real.sqrt 2 :=
      Real.sqrt_div (by positivity) _
    have e2 : Real.sqrt (((m : ℝ) + 1) / 2) = Real.sqrt ((m : ℝ) + 1) / Real.sqrt 2 :=
      Real.sqrt_div (by positivity) _
    have q1 : Real.sqrt ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1) = (m : ℝ) + 1 :=
      Real.mul_self_sqrt (by positivity)
    have hcc : hermiteConst (m + 1 + 1) = hermiteConst (m + 2) := rfl
    rw [e1, e2, hc0, hc2, hcc]
    generalize Real.sqrt 2 * x = y at hr ⊢
    field_simp
    linear_combination (hermiteConst (m + 2) * gauss x) *
      (((m : ℝ) + 1) * hermitePoly m y * hs2 - hermitePoly m y * q1 - hr)

/-! ### Multi-index shifts -/

/-- `α + e_j`. -/
def mova1_up (j : Fin d) (α : MultiIndex d) : MultiIndex d := Function.update α j (α j + 1)

/-- `α - e_j` (equal to `α` if `α_j = 0`; the coefficient of this term then vanishes). -/
def mova1_dn (j : Fin d) (α : MultiIndex d) : MultiIndex d := Function.update α j (α j - 1)

theorem mova1_prod_update (h : Fin d → ℕ → ℝ) (α : MultiIndex d) (j : Fin d) (v : ℕ) :
    ∏ i, h i (Function.update α j v i) = (∏ i ∈ Finset.univ.erase j, h i (α i)) * h j v := by
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
  simp only [Function.update_self]
  congr 1
  exact Finset.prod_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

theorem mova1_prod_self (h : Fin d → ℕ → ℝ) (α : MultiIndex d) (j : Fin d) :
    ∏ i, h i (α i) = (∏ i ∈ Finset.univ.erase j, h i (α i)) * h j (α j) :=
  (Finset.prod_erase_mul _ _ (Finset.mem_univ j)).symm

theorem mova1_hermiteFunD_update (α : MultiIndex d) (j : Fin d) (v : ℕ) (x : Euc d) :
    hermiteFunD (Function.update α j v) x =
      (∏ i ∈ Finset.univ.erase j, hermiteFun (α i) (x i)) * hermiteFun v (x j) :=
  mova1_prod_update (fun i n => hermiteFun n (x i)) α j v

theorem mova1_degree_update (α : MultiIndex d) (j : Fin d) (v : ℕ) :
    MultiIndex.degree (Function.update α j v) + α j = α.degree + v := by
  unfold MultiIndex.degree
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), ← Finset.add_sum_erase _ α (Finset.mem_univ j)]
  simp only [Function.update_self]
  rw [Finset.sum_congr rfl fun i hi => Function.update_of_ne (Finset.ne_of_mem_erase hi) _ _]
  ring

theorem mova1_up_degree (j : Fin d) (α : MultiIndex d) : (mova1_up j α).degree = α.degree + 1 := by
  have := mova1_degree_update α j (α j + 1)
  unfold mova1_up; omega

theorem mova1_dn_degree (j : Fin d) (α : MultiIndex d) (h : 1 ≤ α j) :
    (mova1_dn j α).degree + 1 = α.degree := by
  have := mova1_degree_update α j (α j - 1)
  unfold mova1_dn; omega

theorem mova1_eigen_up (j : Fin d) (α : MultiIndex d) :
    oscEigenvalue d (mova1_up j α) = oscEigenvalue d α + 2 := by
  unfold oscEigenvalue; rw [mova1_up_degree]; push_cast; ring

theorem mova1_eigen_dn (j : Fin d) (α : MultiIndex d) (h : 1 ≤ α j) :
    oscEigenvalue d (mova1_dn j α) + 2 = oscEigenvalue d α := by
  have := mova1_dn_degree j α h
  unfold oscEigenvalue
  have h' : ((mova1_dn j α).degree : ℝ) + 1 = (α.degree : ℝ) := by exact_mod_cast this
  linarith

theorem mova1_up_injective (j : Fin d) : Function.Injective (mova1_up (d := d) j) := by
  intro α β h
  funext i
  by_cases hi : i = j
  · subst hi
    have := congrFun h i
    simp [mova1_up] at this
    exact this
  · have := congrFun h i
    simpa [mova1_up, Function.update_of_ne hi] using this

theorem mova1_dn_up (j : Fin d) (α : MultiIndex d) : mova1_dn j (mova1_up j α) = α := by
  funext i
  by_cases hi : i = j
  · subst hi; simp [mova1_dn, mova1_up]
  · simp [mova1_dn, mova1_up, Function.update_of_ne hi]

theorem mova1_up_dn (j : Fin d) (α : MultiIndex d) (h : 1 ≤ α j) : mova1_up j (mova1_dn j α) = α := by
  funext i
  by_cases hi : i = j
  · subst hi; simp [mova1_dn, mova1_up]; omega
  · simp [mova1_dn, mova1_up, Function.update_of_ne hi]

theorem mova1_up_ne_dn_range (j : Fin d) (β : MultiIndex d) (h : 1 ≤ β j) :
    β ∈ Set.range (mova1_up (d := d) j) := ⟨mova1_dn j β, mova1_up_dn j β h⟩

theorem mova1_up_apply (j : Fin d) (α : MultiIndex d) : mova1_up j α j = α j + 1 := by
  simp [mova1_up]

theorem mova1_dn_apply (j : Fin d) (α : MultiIndex d) : mova1_dn j α j = α j - 1 := by
  simp [mova1_dn]

/-! ### Pointwise ladder for `h_α` -/

theorem mova1_x_hD (α : MultiIndex d) (j : Fin d) (x : Euc d) :
    x j * hermiteFunD α x =
      Real.sqrt (((α j : ℝ) + 1) / 2) * hermiteFunD (mova1_up j α) x +
        Real.sqrt ((α j : ℝ) / 2) * hermiteFunD (mova1_dn j α) x := by
  rw [hermiteFunD_split α j x, mova1_up, mova1_dn, mova1_hermiteFunD_update, mova1_hermiteFunD_update]
  have := mova1_x_hermiteFun (α j) (x j)
  linear_combination (∏ i ∈ Finset.univ.erase j, hermiteFun (α i) (x i)) * this

theorem mova1_dQ_hD (α : MultiIndex d) (j : Fin d) (x : Euc d) :
    (∏ i ∈ Finset.univ.erase j, hermiteFun (α i) (x i)) * deriv (hermiteFun (α j)) (x j) =
      Real.sqrt ((α j : ℝ) / 2) * hermiteFunD (mova1_dn j α) x -
        Real.sqrt (((α j : ℝ) + 1) / 2) * hermiteFunD (mova1_up j α) x := by
  rw [mova1_up, mova1_dn, mova1_hermiteFunD_update, mova1_hermiteFunD_update]
  have := mova1_deriv_hermiteFun (α j) (x j)
  linear_combination (∏ i ∈ Finset.univ.erase j, hermiteFun (α i) (x i)) * this

/-! ### Coefficient formulas -/

/-- `c_α(x_j f) = √((α_j+1)/2) c_{α+e_j}(f) + √(α_j/2) c_{α-e_j}(f)` for Schwartz `f`. -/
theorem mo_coeff_xmul (f : SchwartzMap (Euc d) ℝ) (j : Fin d) (α : MultiIndex d) :
    hermiteCoeff (fun x => x j * f x) α =
      Real.sqrt (((α j : ℝ) + 1) / 2) * hermiteCoeff f (mova1_up j α) +
        Real.sqrt ((α j : ℝ) / 2) * hermiteCoeff f (mova1_dn j α) := by
  unfold hermiteCoeff
  have I1 := int_schwartz_mul f _ (hermiteFunD_poly (mova1_up j α)).1 (hermiteFunD_poly (mova1_up j α)).2
  have I2 := int_schwartz_mul f _ (hermiteFunD_poly (mova1_dn j α)).1 (hermiteFunD_poly (mova1_dn j α)).2
  have e : ∀ x : Euc d, (x j * f x) * hermiteFunD α x =
      Real.sqrt (((α j : ℝ) + 1) / 2) * (f x * hermiteFunD (mova1_up j α) x) +
        Real.sqrt ((α j : ℝ) / 2) * (f x * hermiteFunD (mova1_dn j α) x) := by
    intro x
    have := mova1_x_hD α j x
    linear_combination f x * this
  simp_rw [e]
  rw [integral_add (I1.const_mul _) (I2.const_mul _), integral_const_mul, integral_const_mul]

/-- `c_α(∂_j f) = √((α_j+1)/2) c_{α+e_j}(f) - √(α_j/2) c_{α-e_j}(f)` for Schwartz `f`. -/
theorem mo_coeff_partial (f : SchwartzMap (Euc d) ℝ) (j : Fin d) (α : MultiIndex d) :
    hermiteCoeff (fun x => fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ))) α =
      Real.sqrt (((α j : ℝ) + 1) / 2) * hermiteCoeff f (mova1_up j α) -
        Real.sqrt ((α j : ℝ) / 2) * hermiteCoeff f (mova1_dn j α) := by
  obtain ⟨hA, hB⟩ := hermiteFunD_line_data α j
  obtain ⟨hD1c, hD2c, hhc, hD1p, hD2p, hhp⟩ := hermiteFunD_regularity α j
  have key := ibp_schwartz f (hermiteFunD α) _ (EuclideanSpace.single j (1 : ℝ) : Euc d) hA hhc hhp hD1c hD1p
  have hl : ∀ x : Euc d, fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ)) =
      lineDeriv ℝ (⇑f) x (EuclideanSpace.single j (1 : ℝ)) :=
    fun x => ((f.differentiableAt (x := x)).lineDeriv_eq_fderiv).symm
  unfold hermiteCoeff
  simp_rw [hl]
  rw [key]
  have I1 := int_schwartz_mul f _ (hermiteFunD_poly (mova1_up j α)).1 (hermiteFunD_poly (mova1_up j α)).2
  have I2 := int_schwartz_mul f _ (hermiteFunD_poly (mova1_dn j α)).1 (hermiteFunD_poly (mova1_dn j α)).2
  have e : ∀ x : Euc d, f x * ((∏ i ∈ Finset.univ.erase j, hermiteFun (α i) (x i)) *
        deriv (hermiteFun (α j)) (x j)) =
      Real.sqrt ((α j : ℝ) / 2) * (f x * hermiteFunD (mova1_dn j α) x) -
        Real.sqrt (((α j : ℝ) + 1) / 2) * (f x * hermiteFunD (mova1_up j α) x) := by
    intro x
    rw [mova1_dQ_hD]; ring
  simp_rw [e]
  rw [integral_sub (I2.const_mul _) (I1.const_mul _), integral_const_mul, integral_const_mul]
  ring

end HRS.MS.MovOsc
