import HRS.MS.R26T8AG01b

/-!
# S8.2 observed-time layer, packet T8A.G01 (helper c): derivative bounds of finite products

If each factor has `|f_p x| ≤ 1`, then at `x`
`‖∂(∏ f_p) x‖ ≤ Σ_p ‖∂f_p x‖` and `‖∂²(∏ f_p) x‖ ≤ Σ_p ‖∂²f_p x‖ + (Σ_p ‖∂f_p x‖)²`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- the first two Leibniz bounds for a product of two smooth real functions -/
theorem r26t8a_g01c_mul {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : E) :
    ‖iteratedFDeriv ℝ 1 (fun y => f y * g y) x‖ ≤
        ‖f x‖ * ‖iteratedFDeriv ℝ 1 g x‖ + ‖iteratedFDeriv ℝ 1 f x‖ * ‖g x‖ ∧
      ‖iteratedFDeriv ℝ 2 (fun y => f y * g y) x‖ ≤
        ‖f x‖ * ‖iteratedFDeriv ℝ 2 g x‖ + 2 * ‖iteratedFDeriv ℝ 1 f x‖ * ‖iteratedFDeriv ℝ 1 g x‖ +
          ‖iteratedFDeriv ℝ 2 f x‖ * ‖g x‖ := by
  constructor
  · have := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := f) (g := g) hf hg x (n := 1) (by simp)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, norm_iteratedFDeriv_zero,
      norm_iteratedFDeriv_one, Real.norm_eq_abs, Nat.reduceSub, Nat.sub_zero, Nat.sub_self] at this ⊢
    norm_num at this ⊢
    linarith
  · have := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := f) (g := g) hf hg x (n := 2) (by simp)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, norm_iteratedFDeriv_zero,
      norm_iteratedFDeriv_one, Real.norm_eq_abs, Nat.reduceSub, Nat.sub_zero, Nat.sub_self] at this ⊢
    norm_num at this ⊢
    linarith

/-- finite products: first and second derivative bounds at `x`, with factors bounded by one at `x` -/
theorem r26t8a_g01d_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ p, ContDiff ℝ ∞ (f p)) (x : E) (hbd : ∀ p, |f p x| ≤ 1) :
    ‖iteratedFDeriv ℝ 1 (fun y => ∏ p ∈ s, f p y) x‖ ≤ ∑ p ∈ s, ‖iteratedFDeriv ℝ 1 (f p) x‖ ∧
      ‖iteratedFDeriv ℝ 2 (fun y => ∏ p ∈ s, f p y) x‖ ≤
        ∑ p ∈ s, ‖iteratedFDeriv ℝ 2 (f p) x‖ + (∑ p ∈ s, ‖iteratedFDeriv ℝ 1 (f p) x‖) ^ 2 := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty, zero_add]
    constructor
    · rw [norm_iteratedFDeriv_one]
      simp
    · rw [iteratedFDeriv_const_of_ne (by norm_num)]
      simp
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hP : ContDiff ℝ ∞ (fun y => ∏ p ∈ s, f p y) := contDiff_prod fun p _ => hf p
    have hPab : |∏ p ∈ s, f p x| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun p _ => abs_nonneg _) fun p _ => hbd p
    have hfun : (fun y => ∏ p ∈ insert a s, f p y) = fun y => f a y * ∏ p ∈ s, f p y := by
      funext y
      rw [Finset.prod_insert ha]
    rw [hfun, Finset.sum_insert ha, Finset.sum_insert ha]
    obtain ⟨hL1, hL2⟩ := r26t8a_g01c_mul (hf a) hP x
    have hA1 := hbd a
    have hA1' : ‖f a x‖ ≤ 1 := by rw [Real.norm_eq_abs]; exact hA1
    have hPn : ‖∏ p ∈ s, f p x‖ ≤ 1 := by rw [Real.norm_eq_abs]; exact hPab
    have hS1 : 0 ≤ ∑ p ∈ s, ‖iteratedFDeriv ℝ 1 (f p) x‖ :=
      Finset.sum_nonneg fun p _ => norm_nonneg _
    have hm1 : 0 ≤ ‖iteratedFDeriv ℝ 1 (f a) x‖ := norm_nonneg _
    have hm2 : 0 ≤ ‖iteratedFDeriv ℝ 2 (f a) x‖ := norm_nonneg _
    have hD1 : 0 ≤ ‖iteratedFDeriv ℝ 1 (fun y => ∏ p ∈ s, f p y) x‖ := norm_nonneg _
    have hD2 : 0 ≤ ‖iteratedFDeriv ℝ 2 (fun y => ∏ p ∈ s, f p y) x‖ := norm_nonneg _
    constructor
    · refine hL1.trans ?_
      have e1 : ‖f a x‖ * ‖iteratedFDeriv ℝ 1 (fun y => ∏ p ∈ s, f p y) x‖ ≤ ∑ p ∈ s, ‖iteratedFDeriv ℝ 1 (f p) x‖ :=
        (mul_le_of_le_one_left hD1 hA1').trans ih1
      have e2 : ‖iteratedFDeriv ℝ 1 (f a) x‖ * ‖∏ p ∈ s, f p x‖ ≤ ‖iteratedFDeriv ℝ 1 (f a) x‖ :=
        mul_le_of_le_one_right hm1 hPn
      linarith
    · refine hL2.trans ?_
      have e1 : ‖f a x‖ * ‖iteratedFDeriv ℝ 2 (fun y => ∏ p ∈ s, f p y) x‖ ≤
          ‖iteratedFDeriv ℝ 2 (fun y => ∏ p ∈ s, f p y) x‖ :=
        mul_le_of_le_one_left hD2 hA1'
      have e2 : 2 * ‖iteratedFDeriv ℝ 1 (f a) x‖ * ‖iteratedFDeriv ℝ 1 (fun y => ∏ p ∈ s, f p y) x‖ ≤
          2 * ‖iteratedFDeriv ℝ 1 (f a) x‖ * ∑ p ∈ s, ‖iteratedFDeriv ℝ 1 (f p) x‖ := by
        apply mul_le_mul_of_nonneg_left ih1 (by positivity)
      have e3 : ‖iteratedFDeriv ℝ 2 (f a) x‖ * ‖∏ p ∈ s, f p x‖ ≤ ‖iteratedFDeriv ℝ 2 (f a) x‖ :=
        mul_le_of_le_one_right hm2 hPn
      nlinarith [sq_nonneg ‖iteratedFDeriv ℝ 1 (f a) x‖, ih2]

end HRS.MS.R26T8A

end
