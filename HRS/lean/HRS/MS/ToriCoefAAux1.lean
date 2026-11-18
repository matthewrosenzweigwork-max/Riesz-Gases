import HRS.Whole.AppendixALemmas

/-!
# MS-TORI-COEFA, helper file 1: generic lemmas

* operator norm of `iteratedFDeriv` bounded by the basis (partial derivative) sums;
* weighted bounds from `weightedSupE`;
* the periodization `perL` of a function vanishing outside `B(0, L/3)`: local single-term
  description, smoothness, and derivative transfer;
* the tail `∫_{‖y‖ ≥ N} ⟨y⟩^{-(d+3)}`, and the bounds on scaled cutoffs.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ToriCoefA

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

/-- `⟨x⟩ ≥ 1`. -/
theorem tca_one_le_jbracket (x : Euc d) : 1 ≤ jbracket x := by
  unfold jbracket
  have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + ‖x‖ ^ 2 by nlinarith [norm_nonneg x])
  simpa using h

theorem tca_jbracket_pos (x : Euc d) : 0 < jbracket x :=
  lt_of_lt_of_le one_pos (tca_one_le_jbracket x)

/-- Basis expansion: the operator norm of a `k`-th derivative is at most the sum of the absolute values
of its values on the basis tuples. -/
theorem tca_norm_iteratedFDeriv_le_sum (k : ℕ) (f : Euc d → ℝ) (x : Euc d) :
    ‖iteratedFDeriv ℝ k f x‖ ≤ ∑ i : Fin k → Fin d, |partialDeriv i f x| := by
  classical
  have hsum : 0 ≤ ∑ i : Fin k → Fin d, |partialDeriv i f x| :=
    Finset.sum_nonneg (fun i _ => abs_nonneg _)
  apply ContinuousMultilinearMap.opNorm_le_bound hsum
  intro m
  have hm : m = fun l : Fin k => ∑ a : Fin d, (m l a) • EuclideanSpace.single a (1 : ℝ) := by
    funext l
    ext b
    simp [Finset.sum_apply, Pi.single_apply, mul_ite]
  have e1 : iteratedFDeriv ℝ k f x m =
      ∑ r : Fin k → Fin d, iteratedFDeriv ℝ k f x (fun l => (m l (r l)) • EuclideanSpace.single (r l) (1 : ℝ)) := by
    conv_lhs => rw [hm]
    exact ContinuousMultilinearMap.map_sum _ _
  have e2 : ∀ r : Fin k → Fin d, iteratedFDeriv ℝ k f x (fun l => (m l (r l)) • EuclideanSpace.single (r l) (1 : ℝ))
      = (∏ l, m l (r l)) • partialDeriv r f x := by
    intro r
    exact ContinuousMultilinearMap.map_smul_univ _ (fun l => m l (r l)) (fun l => EuclideanSpace.single (r l) (1 : ℝ))
  rw [e1]
  calc ‖∑ r : Fin k → Fin d, iteratedFDeriv ℝ k f x (fun l => (m l (r l)) • EuclideanSpace.single (r l) (1 : ℝ))‖
      = ‖∑ r : Fin k → Fin d, (∏ l, m l (r l)) • partialDeriv r f x‖ := by
        simp only [e2]
    _ ≤ ∑ r : Fin k → Fin d, ‖(∏ l, m l (r l)) • partialDeriv r f x‖ := norm_sum_le _ _
    _ ≤ ∑ r : Fin k → Fin d, (∏ l, ‖m l‖) * |partialDeriv r f x| := by
        apply Finset.sum_le_sum
        intro r _
        simp only [norm_smul, Real.norm_eq_abs]
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        rw [Finset.abs_prod]
        gcongr with l _
        have h := PiLp.norm_apply_le (m l) (r l)
        rwa [Real.norm_eq_abs] at h
    _ = (∑ r : Fin k → Fin d, |partialDeriv r f x|) * ∏ l, ‖m l‖ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro r _
        ring

/-- Weighted bound: `⟨x⟩^L |∇^j f(x)| ≤ d^j · sup`, from the `weightedSupE` norm. -/
theorem tca_weight_le (k : ℕ) (L : ℝ) (f : Euc d → ℝ) (hW : weightedSupE k L f ≠ ⊤)
    (j : ℕ) (hj : j ≤ k) (x : Euc d) :
    jbracket x ^ L * ‖iteratedFDeriv ℝ j f x‖ ≤ (d : ℝ) ^ j * (weightedSupE k L f).toReal := by
  have hterm : ∀ i : Fin j → Fin d,
      jbracket x ^ L * |partialDeriv i f x| ≤ (weightedSupE k L f).toReal := by
    intro i
    have h1 : ENNReal.ofReal (jbracket x ^ L * |partialDeriv i f x|) ≤ weightedSupE k L f := by
      unfold weightedSupE derivSupE
      exact le_iSup_of_le ⟨j, Nat.lt_succ_of_le hj⟩ (le_iSup_of_le i (le_iSup_of_le x le_rfl))
    exact (ENNReal.ofReal_le_iff_le_toReal hW).1 h1
  have hS : jbracket x ^ L * ‖iteratedFDeriv ℝ j f x‖ ≤
      ∑ i : Fin j → Fin d, jbracket x ^ L * |partialDeriv i f x| := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (tca_norm_iteratedFDeriv_le_sum j f x)
      (Real.rpow_nonneg (tca_jbracket_pos x).le _)
  refine hS.trans ?_
  calc ∑ i : Fin j → Fin d, jbracket x ^ L * |partialDeriv i f x|
      ≤ ∑ i : Fin j → Fin d, (weightedSupE k L f).toReal := Finset.sum_le_sum (fun i _ => hterm i)
    _ = (d : ℝ) ^ j * (weightedSupE k L f).toReal := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]

/-! ### The periodization `perL` of a function vanishing outside `B(0, L/3)` -/

/-- The open `ℓ^∞`-cube of half-side `2L/3` around `Lz`. -/
def tca_U (L : ℝ) (z : Fin d → ℤ) : Set (Euc d) :=
  {y | ∀ i, |y i - L * (z i : ℝ)| < 2 * L / 3}

theorem tca_U_isOpen (L : ℝ) (z : Fin d → ℤ) : IsOpen (tca_U L z) := by
  have : tca_U L z = ⋂ i : Fin d, {y : Euc d | |y i - L * (z i : ℝ)| < 2 * L / 3} := by
    ext y; simp [tca_U]
  rw [this]
  refine isOpen_iInter_of_finite fun i => isOpen_lt ?_ continuous_const
  fun_prop

theorem tca_exists_U (L : ℝ) (hL : 0 < L) (x : Euc d) : ∃ z : Fin d → ℤ, x ∈ tca_U L z := by
  refine ⟨fun i => ⌊x i / L + 1 / 2⌋, fun i => ?_⟩
  have h1 := Int.floor_le (x i / L + 1 / 2)
  have h2 := Int.lt_floor_add_one (x i / L + 1 / 2)
  have hx : x i = L * (x i / L) := by field_simp
  show |x i - L * ((⌊x i / L + 1 / 2⌋ : ℤ) : ℝ)| < 2 * L / 3
  rw [abs_lt]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h1 hL.le]
  · nlinarith [mul_lt_mul_of_pos_left h2 hL]

theorem tca_perL_eq_on (L : ℝ) (hL : 0 < L) (f : Euc d → ℝ)
    (hf : ∀ y : Euc d, L / 3 ≤ ‖y‖ → f y = 0) (z : Fin d → ℤ) (y : Euc d) (hy : y ∈ tca_U L z) :
    perL L f y = f (y - L • latticePt z) := by
  unfold perL
  apply tsum_eq_single z
  intro z' hz'
  apply hf
  obtain ⟨i, hi⟩ : ∃ i, z' i ≠ z i := by
    by_contra h
    push_neg at h
    exact hz' (funext h)
  have hint : (1 : ℝ) ≤ |(z' i : ℝ) - (z i : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |z' i - z i| := Int.one_le_abs (sub_ne_zero.2 hi)
    have h2 : ((|z' i - z i| : ℤ) : ℝ) = |(z' i : ℝ) - (z i : ℝ)| := by
      push_cast; rfl
    rw [← h2]; exact_mod_cast h1
  have hyi := hy i
  have hw : (y - L • latticePt z') i = y i - L * (z' i : ℝ) := by
    simp [latticePt, smul_eq_mul]
  have e : L * |(z' i : ℝ) - (z i : ℝ)| ≤ |L * (z' i : ℝ) - L * (z i : ℝ)| := by
    rw [← mul_sub, abs_mul, abs_of_pos hL]
  have t1 : |L * (z' i : ℝ) - L * (z i : ℝ)| ≤ |y i - L * (z' i : ℝ)| + |y i - L * (z i : ℝ)| := by
    have := abs_sub_le (L * (z' i : ℝ)) (y i) (L * (z i : ℝ))
    rwa [abs_sub_comm (L * (z' i : ℝ)) (y i)] at this
  have t2 : L * 1 ≤ L * |(z' i : ℝ) - (z i : ℝ)| := mul_le_mul_of_nonneg_left hint hL.le
  have key : L / 3 < |y i - L * (z' i : ℝ)| := by linarith
  have h3 := PiLp.norm_apply_le (y - L • latticePt z') i
  rw [Real.norm_eq_abs, hw] at h3
  linarith

theorem tca_perL_locally (L : ℝ) (hL : 0 < L) (f : Euc d → ℝ)
    (hf : ∀ y : Euc d, L / 3 ≤ ‖y‖ → f y = 0) (z : Fin d → ℤ) (y : Euc d) (hy : y ∈ tca_U L z) :
    perL L f =ᶠ[𝓝 y] fun w => f (w - L • latticePt z) :=
  Filter.eventually_of_mem ((tca_U_isOpen L z).mem_nhds hy)
    (fun w hw => tca_perL_eq_on L hL f hf z w hw)

theorem tca_perL_contDiff (n : WithTop ℕ∞) (L : ℝ) (hL : 0 < L) (f : Euc d → ℝ)
    (hfc : ContDiff ℝ n f) (hf : ∀ y : Euc d, L / 3 ≤ ‖y‖ → f y = 0) :
    ContDiff ℝ n (perL L f) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  obtain ⟨z, hz⟩ := tca_exists_U L hL y
  have hc : ContDiff ℝ n (fun w : Euc d => f (w - L • latticePt z)) :=
    hfc.comp (contDiff_id.sub contDiff_const)
  exact hc.contDiffAt.congr_of_eventuallyEq (tca_perL_locally L hL f hf z y hz)

theorem tca_iter_translate (j : ℕ) (f : Euc d → ℝ) (c y : Euc d) :
    iteratedFDeriv ℝ j (fun w => f (w - c)) y = iteratedFDeriv ℝ j f (y - c) := by
  have : (fun w : Euc d => f (w - c)) = fun w => f (w + (-c)) := by
    funext w; rw [sub_eq_add_neg]
  rw [this, iteratedFDeriv_comp_add_right, sub_eq_add_neg]

theorem tca_perL_iter_norm (L : ℝ) (hL : 0 < L) (f : Euc d → ℝ)
    (hf : ∀ y : Euc d, L / 3 ≤ ‖y‖ → f y = 0) (z : Fin d → ℤ) (y : Euc d) (hy : y ∈ tca_U L z)
    (j : ℕ) :
    iteratedFDeriv ℝ j (perL L f) y = iteratedFDeriv ℝ j f (y - L • latticePt z) := by
  rw [((tca_perL_locally L hL f hf z y hy).iteratedFDeriv ℝ j).eq_of_nhds, tca_iter_translate]

theorem tca_latticePt_zero : latticePt (0 : Fin d → ℤ) = 0 := by
  ext i; simp [latticePt]

theorem tca_perL_norm_le (L : ℝ) (hL : 0 < L) (f : Euc d → ℝ)
    (hf : ∀ y : Euc d, L / 3 ≤ ‖y‖ → f y = 0) (j : ℕ) (B : ℝ)
    (hB : ∀ w : Euc d, ‖iteratedFDeriv ℝ j f w‖ ≤ B) (x : Euc d) :
    ‖iteratedFDeriv ℝ j (perL L f) x‖ ≤ B := by
  obtain ⟨z, hz⟩ := tca_exists_U L hL x
  rw [tca_perL_iter_norm L hL f hf z x hz j]
  exact hB _

theorem tca_perL_central (L : ℝ) (hL : 0 < L) (f : Euc d → ℝ)
    (hf : ∀ y : Euc d, L / 3 ≤ ‖y‖ → f y = 0) (x : Euc d) (hx : ‖x‖ ≤ L / 2) (j : ℕ) :
    iteratedFDeriv ℝ j (perL L f) x = iteratedFDeriv ℝ j f x := by
  have hU : x ∈ tca_U L 0 := by
    intro i
    have h1 : |x i| ≤ ‖x‖ := by
      have := PiLp.norm_apply_le x i
      rwa [Real.norm_eq_abs] at this
    simp only [Pi.zero_apply, Int.cast_zero, mul_zero, sub_zero]
    linarith
  rw [tca_perL_iter_norm L hL f hf 0 x hU j, tca_latticePt_zero, smul_zero, sub_zero]

/-! ### Scaled cutoffs -/

theorem tca_scaled_iter (j : ℕ) (ζ : Euc d → ℝ) (hζ : ContDiff ℝ (j : WithTop ℕ∞) ζ) (L : ℝ)
    (y : Euc d) :
    ‖iteratedFDeriv ℝ j (fun z => ζ (L⁻¹ • z)) y‖ = |L⁻¹| ^ j * ‖iteratedFDeriv ℝ j ζ (L⁻¹ • y)‖ := by
  have h := congrFun (iteratedFDeriv_comp_const_smul (𝕜 := ℝ) (f := ζ) (i := j) (a := L⁻¹) hζ) y
  rw [h, norm_smul, norm_pow, Real.norm_eq_abs]

theorem tca_bdd_iter (ζ : Euc d → ℝ) (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) (j : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y, ‖iteratedFDeriv ℝ j ζ y‖ ≤ K := by
  have hc : Continuous (iteratedFDeriv ℝ j ζ) :=
    hζ.1.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)
  have hcs : HasCompactSupport (iteratedFDeriv ℝ j ζ) := hζ.2.1.iteratedFDeriv j
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
  exact ⟨max C 0, le_max_right _ _, fun y => (hC y).trans (le_max_left _ _)⟩

theorem tca_zero_far (L : ℝ) (hL : 0 < L) (ζ : Euc d → ℝ) (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ)
    (j : ℕ) (hζj : ContDiff ℝ (j : WithTop ℕ∞) ζ) (y : Euc d) (hy : L / 3 ≤ ‖y‖) :
    ‖iteratedFDeriv ℝ j (fun z => ζ (L⁻¹ • z)) y‖ = 0 := by
  have hn : 1 / 3 ≤ ‖L⁻¹ • y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hL), inv_mul_eq_div]
    rw [le_div_iff₀ hL]
    linarith
  have hnot : L⁻¹ • y ∉ tsupport ζ := by
    intro h
    have := hζ.2.2.1 h
    rw [Metric.mem_ball, dist_zero_right] at this
    linarith
  have h0 : iteratedFDeriv ℝ j ζ (L⁻¹ • y) = 0 := by
    by_contra h
    exact hnot (support_iteratedFDeriv_subset j h)
  rw [tca_scaled_iter j ζ hζj L y, h0, norm_zero, mul_zero]

end HRS.MS.ToriCoefA
