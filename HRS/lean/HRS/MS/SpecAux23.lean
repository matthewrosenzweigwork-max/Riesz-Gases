import HRS.Whole.Oscillator
import HRS.MS.SpecAux5

/-!
# S8P: compactness of diagonal operators on `ℓ²` (generic, for S8.7)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_diag_compact`: a bounded operator on `ℓ²(ι)` acting by `(D x)_i = a_i x_i`
with `a_i → 0` along `cofinite` is compact (norm limit of the finite-rank truncations).
Application: the embedding `Σ^r → Σ^{r'}` (`r' < r`) of the oscillator scale is compact.
-/

noncomputable section

open Filter Topology
open scoped ENNReal

namespace HRS.MS.Spec

variable {ι : Type*} [DecidableEq ι]

/-- Coordinate functional on `ℓ²(ι)`. -/
def s8p_coordL (i : ι) : lp (fun _ : ι => ℝ) 2 →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun x => x i
      map_add' := fun x y => rfl
      map_smul' := fun a x => rfl } 1
    (fun x => by
      have := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) x i
      show ‖x i‖ ≤ 1 * ‖x‖
      rw [one_mul]; exact this)

theorem s8p_coordL_apply (i : ι) (x : lp (fun _ : ι => ℝ) 2) : s8p_coordL i x = x i := rfl

/-- The finite-rank truncation of the diagonal operator to the index set `F`. -/
def s8p_trunc (a : ι → ℝ) (F : Finset ι) : lp (fun _ : ι => ℝ) 2 →L[ℝ] lp (fun _ : ι => ℝ) 2 :=
  ∑ i ∈ F, (s8p_coordL i).smulRight (a i • lp.single (E := fun _ : ι => ℝ) 2 i (1 : ℝ))

theorem s8p_trunc_apply (a : ι → ℝ) (F : Finset ι) (x : lp (fun _ : ι => ℝ) 2)
    (j : ι) : s8p_trunc a F x j = if j ∈ F then a j * x j else 0 := by
  unfold s8p_trunc
  rw [ContinuousLinearMap.sum_apply]
  rw [show (∑ i ∈ F, ((s8p_coordL i).smulRight (a i • lp.single (E := fun _ : ι => ℝ) 2 i (1 : ℝ))) x) =
      ∑ i ∈ F, (x i * a i) • lp.single (E := fun _ : ι => ℝ) 2 i (1 : ℝ) from Finset.sum_congr rfl fun i _ => by
        simp only [ContinuousLinearMap.smulRight_apply, s8p_coordL_apply, smul_smul, mul_comm]]
  rw [lp.coeFn_sum]
  simp only [Finset.sum_apply, Pi.smul_apply, lp.coeFn_smul, lp.coeFn_single, smul_eq_mul]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs <;> simp [mul_comm]

theorem s8p_trunc_compact (a : ι → ℝ) (F : Finset ι) : IsCompactOperator (s8p_trunc a F) := by
  set W : Submodule ℝ (lp (fun _ : ι => ℝ) 2) :=
    Submodule.span ℝ ((fun i => lp.single (E := fun _ : ι => ℝ) 2 i (1 : ℝ)) '' (F : Set ι)) with hW
  haveI : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (F.finite_toSet.image _)
  have hmem : ∀ x, s8p_trunc a F x ∈ W := by
    intro x
    unfold s8p_trunc
    rw [ContinuousLinearMap.sum_apply]
    refine Submodule.sum_mem _ fun i hi => ?_
    simp only [ContinuousLinearMap.smulRight_apply]
    refine Submodule.smul_mem _ _ ?_
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  let T' : lp (fun _ : ι => ℝ) 2 →L[ℝ] W := (s8p_trunc a F).codRestrict W hmem
  have hid : IsCompactOperator (id : W → W) :=
    (isCompactOperator_id_iff_finiteDimensional (𝕜 := ℝ)).2 inferInstance
  have h1 : IsCompactOperator (id ∘ T') := hid.comp_clm T'
  have h2 := h1.clm_comp W.subtypeL
  exact h2

theorem s8p_diag_compact (a : ι → ℝ) (ha : Tendsto a cofinite (𝓝 0))
    (D : lp (fun _ : ι => ℝ) 2 →L[ℝ] lp (fun _ : ι => ℝ) 2) (hD : ∀ x i, D x i = a i * x i) :
    IsCompactOperator D := by
  have hfin : ∀ ε : ℝ, 0 < ε → {i | ε ≤ |a i|}.Finite := by
    intro ε hε
    have h := ha.eventually (Metric.ball_mem_nhds (0 : ℝ) hε)
    rw [Filter.eventually_cofinite] at h
    refine h.subset fun i hi => ?_
    simp only [Set.mem_ofPred_eq] at hi ⊢
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, not_lt]
    exact hi
  set F : ℕ → Finset ι := fun n => (hfin (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat).toFinset with hF
  have hbd : ∀ n, ‖D - s8p_trunc a (F n)‖ ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    refine ContinuousLinearMap.opNorm_le_bound _ Nat.one_div_pos_of_nat.le fun x => ?_
    set ε : ℝ := 1 / ((n : ℝ) + 1) with hε
    have hε0 : 0 < ε := Nat.one_div_pos_of_nat
    have hcoord : ∀ j, ((D - s8p_trunc a (F n)) x) j ^ 2 ≤ ε ^ 2 * x j ^ 2 := by
      intro j
      rw [ContinuousLinearMap.sub_apply, lp.coeFn_sub, Pi.sub_apply, hD, s8p_trunc_apply]
      by_cases hj : j ∈ F n
      · simp only [hj, if_true, sub_self]
        have := mul_nonneg (sq_nonneg ε) (sq_nonneg (x j))
        simpa using this
      · have hj' : |a j| < ε := by
          simp only [hF, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_le] at hj
          exact hj
        simp only [hj, ite_false, sub_zero]
        have h2 : a j ^ 2 ≤ ε ^ 2 := sq_le_sq.2 (by rw [abs_of_pos hε0]; exact hj'.le)
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    have h1 : ‖(D - s8p_trunc a (F n)) x‖ ^ 2 ≤ (ε * ‖x‖) ^ 2 := by
      rw [HRS.Whole.lp_two_norm_sq, mul_pow, HRS.Whole.lp_two_norm_sq, ← tsum_mul_left]
      exact Summable.tsum_le_tsum hcoord (HRS.Whole.lp_two_summable _)
        ((HRS.Whole.lp_two_summable x).mul_left _)
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 h1 |>.trans_eq (by rw [mul_comm])
  have hlim : Tendsto (fun n => s8p_trunc a (F n)) atTop (𝓝 D) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [norm_sub_rev]; exact hbd n
  exact isCompactOperator_of_tendsto hlim (Eventually.of_forall fun n => s8p_trunc_compact a (F n))

end HRS.MS.Spec
