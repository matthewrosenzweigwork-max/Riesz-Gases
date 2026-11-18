import HRS.MS.R2InterpAux30

/-!
# S10.2 (worker S102), part 31 (packet B1): the Gram identity
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MS.FixEq

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ}

theorem s102_vv_apply (hT : 0 < T) (L : ℕ) (u : ℝ) (x : Euc d) (a : Fin d) (k : Fin (s102_q d L)) :
    s102_vv C m hT L u x a k = if u ≤ s102_tk hT L k then
      gradient (propagatorW C u (s102_tk hT L k) (oscTestFun m (s102_alk L k))) x a else 0 := rfl

theorem s102_vv_mul_sum (hT : 0 < T) (L : ℕ) (u : ℝ) (x : Euc d) (k k' : Fin (s102_q d L)) :
    ∑ a, s102_vv C m hT L u x a k * s102_vv C m hT L u x a k' =
      if u ≤ min (s102_tk hT L k) (s102_tk hT L k') then
        inner ℝ (gradient (propagatorW C u (s102_tk hT L k) (oscTestFun m (s102_alk L k))) x)
          (gradient (propagatorW C u (s102_tk hT L k') (oscTestFun m (s102_alk L k'))) x) else 0 := by
  by_cases h1 : u ≤ s102_tk hT L k <;> by_cases h2 : u ≤ s102_tk hT L k'
  · have : u ≤ min (s102_tk hT L k) (s102_tk hT L k') := le_min h1 h2
    rw [if_pos this, s102_inner_eq_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [s102_vv_apply, h1, h2]
  · have : ¬ u ≤ min (s102_tk hT L k) (s102_tk hT L k') := fun h => h2 (h.trans (min_le_right _ _))
    rw [if_neg this]; simp [s102_vv_apply, h2]
  · have : ¬ u ≤ min (s102_tk hT L k) (s102_tk hT L k') := fun h => h1 (h.trans (min_le_left _ _))
    rw [if_neg this]; simp [s102_vv_apply, h1]
  · have : ¬ u ≤ min (s102_tk hT L k) (s102_tk hT L k') := fun h => h1 (h.trans (min_le_left _ _))
    rw [if_neg this]; simp [s102_vv_apply, h1]

theorem s102_gram_identity_B (hD : S101Data C m T r c) (hT : 0 < T) (L : ℕ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T)
    (hρ : Integrable (C.ρ u)) (B : Fin (s102_q d L) → Fin (s102_q d L) → ℝ) :
    ∑ k, ∑ k', s102_rateM C m hT L u k k' * B k k' =
      2 * C.ν * ∫ x, C.ρ u x * ∑ a, ∑ k, ∑ k', s102_vv C m hT L u x a k * s102_vv C m hT L u x a k' * B k k' := by
  classical
  -- integrability of the terms
  have hint : ∀ a k k', Integrable (fun x => C.ρ u x *
      (s102_vv C m hT L u x a k * s102_vv C m hT L u x a k' * B k k')) := by
    intro a k k'
    have hmeas : Continuous fun x => s102_vv C m hT L u x a k * s102_vv C m hT L u x a k' * B k k' := by
      refine ((?_ : Continuous fun x => s102_vv C m hT L u x a k).mul
        (?_ : Continuous fun x => s102_vv C m hT L u x a k')).mul continuous_const
      · exact s102_cc_continuous hD hT L hu a (s102_pk d L k)
      · exact s102_cc_continuous hD hT L hu a (s102_pk d L k')
    have hbd : ∀ x, ‖s102_vv C m hT L u x a k * s102_vv C m hT L u x a k' * B k k'‖ ≤
        c (s102_pk d L k).2 * c (s102_pk d L k').2 * |B k k'| := by
      intro x
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul (s102_cc_bound hD hT L hu x a _) (s102_cc_bound hD hT L hu x a _)
        (abs_nonneg _) (hD.nonneg _)) le_rfl (abs_nonneg _)
        (mul_nonneg (hD.nonneg _) (hD.nonneg _))
    have := Integrable.bdd_mul hρ hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hbd)
    simpa [mul_comm] using this
  have hrew : ∀ x, C.ρ u x * ∑ a, ∑ k, ∑ k', s102_vv C m hT L u x a k * s102_vv C m hT L u x a k' * B k k' =
      ∑ a, ∑ k, ∑ k', C.ρ u x * (s102_vv C m hT L u x a k * s102_vv C m hT L u x a k' * B k k') := by
    intro x
    simp_rw [Finset.mul_sum]
  simp_rw [hrew]
  rw [s102_integral_triple_sum _ _ hint]
  have key : ∀ k k', ∑ a, ∫ x, C.ρ u x * (s102_vv C m hT L u x a k * s102_vv C m hT L u x a k' * B k k') =
      B k k' * (if u ≤ min (s102_tk hT L k) (s102_tk hT L k') then s102_gram C m hT L u k k' else 0) := by
    intro k k'
    rw [← integral_finset_sum _ (fun a _ => hint a k k')]
    have e1 : ∀ x, ∑ a, C.ρ u x * (s102_vv C m hT L u x a k * s102_vv C m hT L u x a k' * B k k') =
        B k k' * (C.ρ u x * ∑ a, s102_vv C m hT L u x a k * s102_vv C m hT L u x a k') := by
      intro x
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => by ring
    simp_rw [e1, s102_vv_mul_sum]
    rw [integral_const_mul]
    congr 1
    by_cases h : u ≤ min (s102_tk hT L k) (s102_tk hT L k')
    · simp only [if_pos h]
      unfold s102_gram
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [mul_comm]
    · simp only [if_neg h, mul_zero, integral_zero]
  have hperm : ∀ F : Fin d → Fin (s102_q d L) → Fin (s102_q d L) → ℝ,
      ∑ a, ∑ k, ∑ k', F a k k' = ∑ k, ∑ k', ∑ a, F a k k' := by
    intro F
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_comm
  rw [hperm (fun a k k' => ∫ x, C.ρ u x * (s102_vv C m hT L u x a k * s102_vv C m hT L u x a k' * B k k'))]
  simp_rw [key]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k' _ => ?_
  simp only [s102_rateM, Matrix.of_apply]
  ring


theorem s102_gram_identity (hD : S101Data C m T r c) (hT : 0 < T) (L : ℕ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T)
    (hρ : Integrable (C.ρ u)) (N : OscPath d m T [×2]→L[ℝ] ℝ) :
    ∑ k, ∑ k', s102_rateM C m hT L u k k' *
        N ![s102_Lam T L (EuclideanSpace.single k (1 : ℝ)), s102_Lam T L (EuclideanSpace.single k' (1 : ℝ))] =
      2 * C.ν * ∫ x, C.ρ u x * ∑ a, N ![s102_Lam T L (s102_vv C m hT L u x a),
        s102_Lam T L (s102_vv C m hT L u x a)] := by
  classical
  set B : Fin (s102_q d L) → Fin (s102_q d L) → ℝ := fun k k' =>
    N ![s102_Lam T L (EuclideanSpace.single k (1 : ℝ)), s102_Lam T L (EuclideanSpace.single k' (1 : ℝ))] with hB
  have hexp : ∀ x a, N ![s102_Lam T L (s102_vv C m hT L u x a), s102_Lam T L (s102_vv C m hT L u x a)] =
      ∑ k, ∑ k', s102_vv C m hT L u x a k * s102_vv C m hT L u x a k' * B k k' := by
    intro x a
    rw [s102_Lam_vec, s102_bilin_expand N]
  simp_rw [hexp]
  exact s102_gram_identity_B hD hT L hu hρ B

end HRS.MS.R2Interp

end
