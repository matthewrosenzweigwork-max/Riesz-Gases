import HRS.MS.R26T8AG01d

/-!
# S8.2 observed-time layer, packet T8A.G01 (helper e): derivative bounds of a pair cutoff

For a continuous linear map `L : E → F` into an inner product space and `m > 0`, the pair cutoff
`P(X) = ψ(m² ‖L X‖²)` satisfies, at every `X` with `L X ≠ 0`,
`‖∂P X‖ ≤ 8 K₁ ‖L‖ / ‖L X‖` and `‖∂²P X‖ ≤ (8 K₁ + 64 K₂) ‖L‖² / ‖L X‖²`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F]

/-- `‖∂^k (‖L·‖²)(X)‖` for `k = 1, 2` -/
theorem r26t8a_g01e_sq_comp (L : E →L[ℝ] F) (X : E) :
    ‖iteratedFDeriv ℝ 1 (fun y => ‖L y‖ ^ 2) X‖ ≤ 2 * ‖L X‖ * ‖L‖ ∧
      ‖iteratedFDeriv ℝ 2 (fun y => ‖L y‖ ^ 2) X‖ ≤ 2 * ‖L‖ ^ 2 := by
  have hg : ContDiff ℝ ∞ (fun y : F => ‖y‖ ^ 2) := contDiff_norm_sq ℝ
  have key : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i (fun y => ‖L y‖ ^ 2) X‖ ≤
      ‖iteratedFDeriv ℝ i (fun y : F => ‖y‖ ^ 2) (L X)‖ * ‖L‖ ^ i := by
    intro i hi
    have h := ContinuousLinearMap.iteratedFDeriv_comp_right L hg X (i := i) (by first | simp | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    have hfun : (fun y => ‖L y‖ ^ 2) = (fun y : F => ‖y‖ ^ 2) ∘ L := rfl
    rw [hfun, h]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp [Finset.prod_const]
  constructor
  · refine (key 1 (by norm_num)).trans ?_
    rw [r26t8a_g01d_sq_iter1, pow_one]
  · refine (key 2 le_rfl).trans ?_
    exact mul_le_mul_of_nonneg_right (r26t8a_g01d_sq_iter2 _) (by positivity)

/-- the pair cutoff `ψ(m² ‖L X‖²)`: derivative bounds away from `L X = 0` -/
theorem r26t8a_g01e_pair (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hz : ∀ t : ℝ, (t < 1 ∨ 4 < t) → deriv ψ t = 0 ∧ deriv (deriv ψ) t = 0)
    {K1 K2 : ℝ} (hK1 : ∀ t : ℝ, |deriv ψ t| ≤ K1)
    (hK2 : ∀ t : ℝ, |deriv (deriv ψ) t| ≤ K2) (hK1n : 0 ≤ K1) (hK2n : 0 ≤ K2)
    {m : ℝ} (L : E →L[ℝ] F) (X : E) :
    ‖iteratedFDeriv ℝ 1 (fun y => ψ (m ^ 2 * ‖L y‖ ^ 2)) X‖ ≤ 8 * K1 * ‖L‖ / ‖L X‖ ∧
      ‖iteratedFDeriv ℝ 2 (fun y => ψ (m ^ 2 * ‖L y‖ ^ 2)) X‖ ≤
        (8 * K1 + 64 * K2) * ‖L‖ ^ 2 / ‖L X‖ ^ 2 := by
  set c : ℝ := m ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hsq : ContDiff ℝ ∞ (fun y => ‖L y‖ ^ 2) := (contDiff_norm_sq ℝ).comp L.contDiff
  have hh : ContDiff ℝ ∞ (fun y => c * ‖L y‖ ^ 2) := contDiff_const.mul hsq
  -- derivatives of `h = c ‖L·‖²`
  have hcd : ∀ i : ℕ, i ≤ 2 → ContDiffAt ℝ (i : WithTop ℕ∞) (fun y => ‖L y‖ ^ 2) X := fun i hi =>
    hsq.contDiffAt.of_le (by first | simp | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hD1 : ‖fderiv ℝ (fun y => c * ‖L y‖ ^ 2) X‖ ≤ 2 * c * ‖L X‖ * ‖L‖ := by
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ), show (fun y => c * ‖L y‖ ^ 2) = c • (fun y => ‖L y‖ ^ 2) from rfl,
      iteratedFDeriv_const_smul_apply (hcd 1 (by norm_num))]
    refine (r26t8a_g01b_smul_norm c (iteratedFDeriv ℝ 1 (fun y => ‖L y‖ ^ 2) X)).trans ?_
    rw [abs_of_nonneg hc0]
    exact (mul_le_mul_of_nonneg_left (r26t8a_g01e_sq_comp L X).1 hc0).trans_eq (by ring)
  have hD2 : ‖iteratedFDeriv ℝ 2 (fun y => c * ‖L y‖ ^ 2) X‖ ≤ 2 * c * ‖L‖ ^ 2 := by
    rw [show (fun y => c * ‖L y‖ ^ 2) = c • (fun y => ‖L y‖ ^ 2) from rfl,
      iteratedFDeriv_const_smul_apply (hcd 2 le_rfl)]
    refine (r26t8a_g01b_smul_norm c (iteratedFDeriv ℝ 2 (fun y => ‖L y‖ ^ 2) X)).trans ?_
    rw [abs_of_nonneg hc0]
    exact (mul_le_mul_of_nonneg_left (r26t8a_g01e_sq_comp L X).2 hc0).trans_eq (by ring)
  have h1 := r26t8a_g01b_fderiv hψ hh X
  have h2 := r26t8a_g01b_iter2 hψ hh X
  beta_reduce at h1 h2
  rw [norm_iteratedFDeriv_one]
  set v : ℝ := c * ‖L X‖ ^ 2 with hv
  have hLn : 0 ≤ ‖L‖ := norm_nonneg _
  by_cases hin : 1 ≤ v ∧ v ≤ 4
  · obtain ⟨hv1, hv4⟩ := hin
    have hzn : 0 < ‖L X‖ := by
      by_contra hc'
      have h0 : ‖L X‖ = 0 := le_antisymm (not_lt.1 hc') (norm_nonneg _)
      have hv0' : v = 0 := by rw [hv, h0]; ring
      linarith
    have hz2 : 0 < ‖L X‖ ^ 2 := by positivity
    have hv0 : 0 ≤ v := by linarith
    have hX1 : |deriv ψ v| ≤ K1 := hK1 _
    have hX2 : |deriv (deriv ψ) v| ≤ K2 := hK2 _
    constructor
    · refine h1.trans ?_
      have hk : 2 * c * ‖L X‖ * ‖L‖ ≤ 8 * ‖L‖ / ‖L X‖ := by
        rw [le_div_iff₀ hzn]
        nlinarith
      calc |deriv ψ (c * ‖L X‖ ^ 2)| * ‖fderiv ℝ (fun y => c * ‖L y‖ ^ 2) X‖
          ≤ K1 * (2 * c * ‖L X‖ * ‖L‖) := mul_le_mul hX1 (hD1.trans_eq' rfl) (norm_nonneg _) hK1n
        _ ≤ K1 * (8 * ‖L‖ / ‖L X‖) := mul_le_mul_of_nonneg_left hk hK1n
        _ = 8 * K1 * ‖L‖ / ‖L X‖ := by ring
    · refine h2.trans ?_
      have hL2 : 0 ≤ ‖L‖ ^ 2 := by positivity
      have hA : |deriv ψ (c * ‖L X‖ ^ 2)| * ‖iteratedFDeriv ℝ 2 (fun y => c * ‖L y‖ ^ 2) X‖ ≤
          K1 * (2 * c * ‖L‖ ^ 2) :=
        mul_le_mul hX1 hD2 (norm_nonneg _) hK1n
      have hB : |deriv (deriv ψ) (c * ‖L X‖ ^ 2)| *
          ‖fderiv ℝ (fun y => c * ‖L y‖ ^ 2) X‖ ^ 2 ≤ K2 * (2 * c * ‖L X‖ * ‖L‖) ^ 2 := by
        refine mul_le_mul hX2 (pow_le_pow_left₀ (norm_nonneg _) hD1 2) (by positivity) hK2n
      have hT : K1 * (2 * c * ‖L‖ ^ 2) + K2 * (2 * c * ‖L X‖ * ‖L‖) ^ 2 ≤
          (8 * K1 + 64 * K2) * ‖L‖ ^ 2 / ‖L X‖ ^ 2 := by
        rw [le_div_iff₀ hz2]
        have eq : (K1 * (2 * c * ‖L‖ ^ 2) + K2 * (2 * c * ‖L X‖ * ‖L‖) ^ 2) * ‖L X‖ ^ 2 =
            2 * K1 * v * ‖L‖ ^ 2 + 4 * K2 * v ^ 2 * ‖L‖ ^ 2 := by
          rw [hv]; ring
        have f1 : 2 * K1 * v * ‖L‖ ^ 2 ≤ 8 * K1 * ‖L‖ ^ 2 := by
          have : 2 * K1 * v ≤ 8 * K1 := by nlinarith [mul_le_mul_of_nonneg_left hv4 hK1n]
          nlinarith [sq_nonneg ‖L‖]
        have f2 : 4 * K2 * v ^ 2 * ‖L‖ ^ 2 ≤ 64 * K2 * ‖L‖ ^ 2 := by
          have hv2 : v ^ 2 ≤ 16 := by nlinarith
          have : 4 * K2 * v ^ 2 ≤ 64 * K2 := by nlinarith [mul_le_mul_of_nonneg_left hv2 hK2n]
          nlinarith [sq_nonneg ‖L‖]
        have e8 : (8 * K1 + 64 * K2) * ‖L‖ ^ 2 = 8 * K1 * ‖L‖ ^ 2 + 64 * K2 * ‖L‖ ^ 2 := by ring
        rw [eq, e8]
        linarith
      linarith
  · have hz1 : deriv ψ v = 0 ∧ deriv (deriv ψ) v = 0 :=
      hz v (by
        rcases not_and_or.1 hin with h | h
        · left; linarith [not_le.1 h]
        · right; linarith [not_le.1 h])
    obtain ⟨hz1', hz2'⟩ := hz1
    constructor
    · refine h1.trans ?_
      rw [hz1', abs_zero, zero_mul]
      positivity
    · refine h2.trans ?_
      rw [hz1', hz2', abs_zero, zero_mul, zero_mul, zero_add]
      positivity

end HRS.MS.R26T8A

end
