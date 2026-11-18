import HRS.MS.S81R_Cls

/-!
# S81R, packet R5: finite measures on `(ℝ^m)^n` are determined by integrals of products of test functions

If two finite measures on `Fin n → Euc m` give the same integral to every product `∏ₖ fₖ(xₖ)` with `fₖ ∈ s81r_S`
(bounded `C²` with bounded derivatives up to order 2), they are equal.  Proof: characteristic functionals
(`Measure.ext_of_charFunDual`), `exp(i ∑ θₖ) = ∏ (cos θₖ + i sin θₖ)` expanded over subsets of `Fin n`.
-/

noncomputable section

open MeasureTheory Complex
open scoped ContDiff
open HRS

namespace HRS.MS.S81R

variable {m n : ℕ}

theorem s81r_det_expand (L : (Fin n → Euc m) →L[ℝ] ℝ) (ρ : Measure (Fin n → Euc m)) [IsFiniteMeasure ρ] :
    ∫ v, Complex.exp ((L v : ℂ) * I) ∂ρ =
      ∑ t ∈ (Finset.univ : Finset (Fin n)).powerset, I ^ t.card *
        ((∫ v, ∏ k, (if k ∈ t then Real.sin ((L.comp (ContinuousLinearMap.single ℝ
            (fun _ : Fin n => Euc m) k)) (v k)) else Real.cos ((L.comp (ContinuousLinearMap.single ℝ
            (fun _ : Fin n => Euc m) k)) (v k))) ∂ρ : ℝ) : ℂ) := by
  classical
  set Lk : Fin n → (Euc m →L[ℝ] ℝ) := fun k =>
    L.comp (ContinuousLinearMap.single ℝ (fun _ : Fin n => Euc m) k) with hLk
  have hLv : ∀ v : Fin n → Euc m, (L v : ℂ) * I = ∑ k, ((Lk k (v k) : ℂ) * I) := fun v => by
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, hLk]
    simp only [ContinuousLinearMap.sum_comp_single]
  have hpt : ∀ v : Fin n → Euc m, Complex.exp ((L v : ℂ) * I) =
      ∑ t ∈ (Finset.univ : Finset (Fin n)).powerset, I ^ t.card *
        ((∏ k, (if k ∈ t then Real.sin (Lk k (v k)) else Real.cos (Lk k (v k))) : ℝ) : ℂ) := by
    intro v
    rw [hLv v, Complex.exp_sum]
    have e1 : ∀ k, Complex.exp ((Lk k (v k) : ℂ) * I) =
        ((Real.sin (Lk k (v k)) : ℝ) : ℂ) * I + ((Real.cos (Lk k (v k)) : ℝ) : ℂ) := fun k => by
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      ring
    simp_rw [e1]
    rw [Finset.prod_add]
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht' : t ⊆ Finset.univ := Finset.mem_powerset.1 ht
    rw [Finset.prod_mul_distrib, Finset.prod_const]
    have e2 : (∏ k, (if k ∈ t then Real.sin (Lk k (v k)) else Real.cos (Lk k (v k))) : ℝ) =
        (∏ k ∈ t, Real.sin (Lk k (v k))) * ∏ k ∈ Finset.univ \ t, Real.cos (Lk k (v k)) := by
      rw [Finset.prod_ite]
      congr 2
      · ext k; simp
      · ext k; simp
    rw [e2]
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun t _ => ?_
    rw [integral_const_mul]
    congr 1
    exact integral_ofReal (𝕜 := ℂ)
  · intro t _
    refine Integrable.const_mul ?_ _
    refine Integrable.of_bound (C := 1) ?_ (Filter.Eventually.of_forall fun v => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      refine Complex.continuous_ofReal.comp (continuous_finset_prod _ fun k _ => ?_)
      by_cases hk : k ∈ t
      · simp only [hk, ite_true]
        exact Real.continuous_sin.comp ((Lk k).continuous.comp (continuous_apply k))
      · simp only [hk, ite_false]
        exact Real.continuous_cos.comp ((Lk k).continuous.comp (continuous_apply k))
    · rw [Complex.norm_real]
      rw [Real.norm_eq_abs, Finset.abs_prod]
      refine Finset.prod_le_one₀ (fun k _ => abs_nonneg _) fun k _ => ?_
      by_cases hk : k ∈ t
      · simp only [hk, ite_true]; exact Real.abs_sin_le_one _
      · simp only [hk, ite_false]; exact Real.abs_cos_le_one _

/-- measures on `(ℝ^m)^n` are determined by products of test functions -/
theorem s81r_det (μ ν : Measure (Fin n → Euc m)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ f : Fin n → (Euc m → ℝ), (∀ k, s81r_S (f k)) →
      ∫ x, ∏ k, f k (x k) ∂μ = ∫ x, ∏ k, f k (x k) ∂ν) : μ = ν := by
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  simp only [charFunDual_apply]
  rw [s81r_det_expand L μ, s81r_det_expand L ν]
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 2
  have := h (fun k y => if k ∈ t then Real.sin ((L.comp (ContinuousLinearMap.single ℝ
    (fun _ : Fin n => Euc m) k)) y) else Real.cos ((L.comp (ContinuousLinearMap.single ℝ
    (fun _ : Fin n => Euc m) k)) y)) (fun k => by
      by_cases hk : k ∈ t
      · simp only [hk, ite_true]; exact s81r_S_sin _
      · simp only [hk, ite_false]; exact s81r_S_cos _)
  exact this

end HRS.MS.S81R
