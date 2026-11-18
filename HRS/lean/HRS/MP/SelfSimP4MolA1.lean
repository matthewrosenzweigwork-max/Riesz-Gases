import HRS.MP.SelfSimP4Spec

/-!
# MPP4MOL stage 5a (1): coordinates, the Euclidean square `q` and the Gaussian kernel on `(ℝ^d)^N`
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP4Mol

variable {d N : ℕ}

/-- The Euclidean square `∑_i ‖w_i‖²`. -/
def p4m_q (w : EucConfig d N) : ℝ := ∑ i, ‖w i‖ ^ 2

theorem p4m_q_eq (w : EucConfig d N) : p4m_q w = ∑ k : Fin N × Fin d, (w k.1 k.2) ^ 2 := by
  unfold p4m_q
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.real_norm_sq_eq]

theorem p4m_q_nonneg (w : EucConfig d N) : 0 ≤ p4m_q w := Finset.sum_nonneg fun i _ => by positivity

theorem p4m_q_neg (w : EucConfig d N) : p4m_q (-w) = p4m_q w := by simp [p4m_q]

theorem p4m_q_zero : p4m_q (0 : EucConfig d N) = 0 := by simp [p4m_q]

theorem p4m_norm_sq_le_q (w : EucConfig d N) : ‖w‖ ^ 2 ≤ p4m_q w := by
  rcases isEmpty_or_nonempty (Fin N) with h | h
  · have : w = 0 := Subsingleton.elim _ _
    simp [this, p4m_q]
  · obtain ⟨i, hi⟩ := Finite.exists_max (fun i => ‖w i‖)
    have : ‖w‖ = ‖w i‖ := by
      apply le_antisymm
      · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 hi
      · exact norm_le_pi_norm w i
    rw [this]
    exact Finset.single_le_sum (f := fun i => ‖w i‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ i)

theorem p4m_q_le (w : EucConfig d N) : p4m_q w ≤ N * ‖w‖ ^ 2 := by
  unfold p4m_q
  calc ∑ i, ‖w i‖ ^ 2 ≤ ∑ _i : Fin N, ‖w‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => by gcongr; exact norm_le_pi_norm w i
    _ = N * ‖w‖ ^ 2 := by simp

theorem p4m_coord_sq_le (w : EucConfig d N) (k : Fin N × Fin d) : (w k.1 k.2) ^ 2 ≤ p4m_q w := by
  rw [p4m_q_eq]
  exact Finset.single_le_sum (f := fun k : Fin N × Fin d => (w k.1 k.2) ^ 2) (fun i _ => by positivity)
    (Finset.mem_univ k)

theorem p4m_contDiff_q {n : WithTop ℕ∞} : ContDiff ℝ n (p4m_q : EucConfig d N → ℝ) := by
  unfold p4m_q
  refine ContDiff.sum fun i _ => ?_
  exact (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (Euc d) i)

theorem p4m_continuous_q : Continuous (p4m_q : EucConfig d N → ℝ) := (p4m_contDiff_q (n := 0)).continuous

/-- Symmetric form: `p4InnerL y h = ∑_k y_k h_k`. -/
theorem p4m_inner_eq (y h : EucConfig d N) :
    p4InnerL y h = ∑ k : Fin N × Fin d, y k.1 k.2 * h k.1 k.2 := by
  simp only [p4InnerL, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, innerSL_apply_apply]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mul_comm]

theorem p4m_inner_comm (y h : EucConfig d N) : p4InnerL y h = p4InnerL h y := by
  rw [p4m_inner_eq, p4m_inner_eq]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem p4m_inner_self (y : EucConfig d N) : p4InnerL y y = p4m_q y := by
  rw [p4m_inner_eq, p4m_q_eq]
  exact Finset.sum_congr rfl fun k _ => (sq _).symm

theorem p4m_basis_apply (k : Fin N × Fin d) (i : Fin N) (j : Fin d) :
    configBasis d N k i j = if (i, j) = k then 1 else 0 := by
  obtain ⟨a, b⟩ := k
  simp only [configBasis, Pi.single_apply, Prod.mk.injEq]
  by_cases h1 : i = a
  · subst h1
    by_cases h2 : j = b
    · subst h2; simp
    · simp [h2, EuclideanSpace.single_apply]
  · simp [h1]

theorem p4m_inner_single (y : EucConfig d N) (k : Fin N × Fin d) :
    p4InnerL y (configBasis d N k) = y k.1 k.2 := by
  rw [p4m_inner_eq]
  simp [p4m_basis_apply]

theorem p4m_inner_single_left (h : EucConfig d N) (k : Fin N × Fin d) :
    p4InnerL (configBasis d N k) h = h k.1 k.2 := by
  rw [p4m_inner_comm, p4m_inner_single]

theorem p4m_inner_bound (y h : EucConfig d N) : |p4InnerL y h| ≤ N * (‖y‖ * ‖h‖) := by
  simp only [p4InnerL, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, innerSL_apply_apply]
  calc |∑ i, inner ℝ (y i) (h i)| ≤ ∑ i, |inner ℝ (y i) (h i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin N, ‖y‖ * ‖h‖ := Finset.sum_le_sum fun i _ => by
        refine (abs_real_inner_le_norm _ _).trans ?_
        exact mul_le_mul (norm_le_pi_norm y i) (norm_le_pi_norm h i) (norm_nonneg _) (norm_nonneg _)
    _ = N * (‖y‖ * ‖h‖) := by simp

/-- The decomposition `h = ∑_k h_k e_k`. -/
theorem p4m_sum_basis (h : EucConfig d N) : h = ∑ k : Fin N × Fin d, h k.1 k.2 • configBasis d N k := by
  ext i j
  simp only [Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, PiLp.add_apply]
  rw [Fintype.sum_prod_type]
  simp [p4m_basis_apply, ite_and, Finset.sum_ite_eq]

theorem p4m_fderiv_apply_sum (f : EucConfig d N → ℝ) (x h : EucConfig d N) :
    fderiv ℝ f x h = ∑ k : Fin N × Fin d, h k.1 k.2 * fderiv ℝ f x (configBasis d N k) := by
  conv_lhs => rw [p4m_sum_basis h]
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [map_smul, smul_eq_mul]

theorem p4m_hasFDerivAt_q (w : EucConfig d N) :
    HasFDerivAt (p4m_q : EucConfig d N → ℝ) ((2 : ℝ) • p4InnerL w) w := by
  have : (p4m_q : EucConfig d N → ℝ) = fun w => ∑ i, ‖w i‖ ^ 2 := rfl
  rw [this]
  have h1 : ∀ i ∈ Finset.univ, HasFDerivAt (fun w : EucConfig d N => ‖w i‖ ^ 2)
      ((2 : ℝ) • ((innerSL ℝ (w i)).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i))) w := by
    intro i _
    have := (hasStrictFDerivAt_norm_sq (w i)).hasFDerivAt.comp w
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i).hasFDerivAt
    refine HasFDerivAt.congr_fderiv this ?_
    ext h
    simp
  have := HasFDerivAt.fun_sum h1
  convert this using 1
  simp only [p4InnerL, Finset.smul_sum]

/-! ### The Gaussian kernel -/

/-- The normalising constant. -/
def p4m_cst (d N : ℕ) (v : ℝ) : ℝ := (2 * Real.pi * v) ^ (-((N * d : ℕ) : ℝ) / 2)

theorem p4m_gauss_eq (v : ℝ) (w : EucConfig d N) :
    p4Gauss d N v w = p4m_cst d N v * Real.exp (-(p4m_q w) / (2 * v)) := rfl

theorem p4m_cst_pos {v : ℝ} (hv : 0 < v) : 0 < p4m_cst d N v := by
  unfold p4m_cst; positivity

theorem p4m_gauss_pos {v : ℝ} (hv : 0 < v) (w : EucConfig d N) : 0 < p4Gauss d N v w := by
  rw [p4m_gauss_eq]; have := p4m_cst_pos (d := d) (N := N) hv; positivity

theorem p4m_gauss_le {v : ℝ} (hv : 0 < v) (w : EucConfig d N) : p4Gauss d N v w ≤ p4m_cst d N v := by
  rw [p4m_gauss_eq]
  have := p4m_cst_pos (d := d) (N := N) hv
  have h2 : Real.exp (-(p4m_q w) / (2 * v)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := p4m_q_nonneg w
    have : 0 ≤ p4m_q w / (2 * v) := by positivity
    rw [neg_div]; linarith
  nlinarith

theorem p4m_gauss_neg (v : ℝ) (w : EucConfig d N) : p4Gauss d N v (-w) = p4Gauss d N v w := by
  simp [p4m_gauss_eq, p4m_q_neg]

theorem p4m_contDiff_gauss (v : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (p4Gauss d N v : EucConfig d N → ℝ) := by
  have : (p4Gauss d N v : EucConfig d N → ℝ) = fun w => p4m_cst d N v * Real.exp (-(p4m_q w) / (2 * v)) :=
    funext fun w => rfl
  rw [this]
  exact contDiff_const.mul (Real.contDiff_exp.comp (p4m_contDiff_q.neg.div_const _))

theorem p4m_hasFDerivAt_gauss {v : ℝ} (hv : 0 < v) (w : EucConfig d N) :
    HasFDerivAt (p4Gauss d N v : EucConfig d N → ℝ) ((-(1 / v) * p4Gauss d N v w) • p4InnerL w) w := by
  have h1 := (p4m_hasFDerivAt_q w).const_mul (-(1 / (2 * v)))
  have h2 := (h1.exp).const_mul (p4m_cst d N v)
  have e : (p4Gauss d N v : EucConfig d N → ℝ) = fun w => p4m_cst d N v * Real.exp (-(1 / (2 * v)) * p4m_q w) := by
    funext w
    rw [p4m_gauss_eq]
    congr 2
    field_simp
  rw [e]
  convert h2 using 1
  ext h
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, p4m_gauss_eq]
  have : -(1 / (2 * v)) * p4m_q w = -(p4m_q w) / (2 * v) := by field_simp
  rw [this]
  field_simp

theorem p4m_fderiv_gauss {v : ℝ} (hv : 0 < v) (w : EucConfig d N) :
    fderiv ℝ (p4Gauss d N v : EucConfig d N → ℝ) w = (-(1 / v) * p4Gauss d N v w) • p4InnerL w :=
  (p4m_hasFDerivAt_gauss hv w).fderiv

end HRS.MP.SelfSimP4Mol
