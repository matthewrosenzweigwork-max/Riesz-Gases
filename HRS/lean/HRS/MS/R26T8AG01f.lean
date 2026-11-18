import HRS.MS.R26T8AG01e

/-!
# S8.2 observed-time layer, packet T8A.G01 (helper f): spatial cutoff with uniform derivative bounds

For `m ≥ 1`, the spatial factor `1 - ψ(m⁻² ‖L X‖²)` has first and second derivatives bounded uniformly in `X`
(its derivatives are supported where `‖L X‖ ≥ m ≥ 1`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F]

theorem r26t8a_g01f_spatial (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hz : ∀ t : ℝ, (t < 1 ∨ 4 < t) → deriv ψ t = 0 ∧ deriv (deriv ψ) t = 0)
    {K1 K2 : ℝ} (hK1 : ∀ t : ℝ, |deriv ψ t| ≤ K1)
    (hK2 : ∀ t : ℝ, |deriv (deriv ψ) t| ≤ K2) (hK1n : 0 ≤ K1) (hK2n : 0 ≤ K2)
    {m : ℝ} (hm : 1 ≤ m) (L : E →L[ℝ] F) (X : E) :
    ‖iteratedFDeriv ℝ 1 (fun y => 1 - ψ (m⁻¹ ^ 2 * ‖L y‖ ^ 2)) X‖ ≤ 8 * K1 * ‖L‖ ∧
      ‖iteratedFDeriv ℝ 2 (fun y => 1 - ψ (m⁻¹ ^ 2 * ‖L y‖ ^ 2)) X‖ ≤ (8 * K1 + 64 * K2) * ‖L‖ ^ 2 := by
  set ψ' : ℝ → ℝ := fun t => 1 - ψ t with hψ'
  have hψ'c : ContDiff ℝ ∞ ψ' := contDiff_const.sub hψ
  have hd1 : deriv ψ' = fun t => -deriv ψ t := funext fun t => deriv_const_sub 1
  have hd2 : deriv (deriv ψ') = fun t => -deriv (deriv ψ) t := by
    rw [hd1]
    funext t
    exact deriv.neg
  have hz' : ∀ t : ℝ, (t < 1 ∨ 4 < t) → deriv ψ' t = 0 ∧ deriv (deriv ψ') t = 0 := by
    intro t ht
    have := hz t ht
    refine ⟨?_, ?_⟩
    · rw [hd1]
      simp [this.1]
    · rw [hd2]
      simp [this.2]
  have hK1' : ∀ t : ℝ, |deriv ψ' t| ≤ K1 := by
    intro t
    rw [hd1]
    simp only [abs_neg]
    exact hK1 t
  have hK2' : ∀ t : ℝ, |deriv (deriv ψ') t| ≤ K2 := by
    intro t
    rw [hd2]
    simp only [abs_neg]
    exact hK2 t
  have hm0 : 0 < m⁻¹ := inv_pos.2 (by linarith)
  have hpair := r26t8a_g01e_pair ψ' hψ'c hz' hK1' hK2' hK1n hK2n (m := m⁻¹) L X
  simp only [hψ'] at hpair
  by_cases hbig : 1 ≤ ‖L X‖
  · have hLn : 0 ≤ ‖L‖ := norm_nonneg _
    constructor
    · refine hpair.1.trans ?_
      exact div_le_self (by positivity) hbig
    · refine hpair.2.trans ?_
      exact div_le_self (by positivity) (one_le_pow₀ hbig)
  · push_neg at hbig
    have hsmall : m⁻¹ ^ 2 * ‖L X‖ ^ 2 < 1 := by
      have h1 : m⁻¹ ^ 2 ≤ 1 := by
        have : m⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hm
        exact pow_le_one₀ hm0.le this
      have h2 : ‖L X‖ ^ 2 < 1 := by nlinarith [norm_nonneg (L X)]
      nlinarith [sq_nonneg ‖L X‖, norm_nonneg (L X)]
    have hh : ContDiff ℝ ∞ (fun y => m⁻¹ ^ 2 * ‖L y‖ ^ 2) :=
      contDiff_const.mul ((contDiff_norm_sq ℝ).comp L.contDiff)
    have h1 := r26t8a_g01b_fderiv hψ'c hh X
    have h2 := r26t8a_g01b_iter2 hψ'c hh X
    beta_reduce at h1 h2
    obtain ⟨hz1, hz2⟩ := hz' _ (Or.inl hsmall)
    rw [norm_iteratedFDeriv_one]
    constructor
    · refine h1.trans ?_
      rw [hz1, abs_zero, zero_mul]
      positivity
    · refine h2.trans ?_
      rw [hz1, hz2, abs_zero, zero_mul, zero_mul, zero_add]
      positivity

end HRS.MS.R26T8A

end
