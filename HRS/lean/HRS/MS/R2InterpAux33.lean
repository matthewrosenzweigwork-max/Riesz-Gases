import HRS.MS.R2InterpAux32

/-!
# S10.2 (worker S102), part 33 (packet S7): the covariance rate of the grid observations is symmetric positive semidefinite
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff MatrixOrder Matrix

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MS.FixEq

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ}

theorem s102_gram_symm (hT : 0 < T) (L : ℕ) (u : ℝ) (k k' : Fin (s102_q d L)) :
    s102_gram C m hT L u k k' = s102_gram C m hT L u k' k := by
  unfold s102_gram
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [real_inner_comm]

theorem s102_rateM_symm (hT : 0 < T) (L : ℕ) (u : ℝ) (k k' : Fin (s102_q d L)) :
    s102_rateM C m hT L u k k' = s102_rateM C m hT L u k' k := by
  simp only [s102_rateM, Matrix.of_apply, min_comm (s102_tk hT L k) (s102_tk hT L k')]
  rw [s102_gram_symm]

theorem s102_rateM_psd (hD : S101Data C m T r c) (hT : 0 < T) (L : ℕ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T)
    (hρ : Integrable (C.ρ u)) (hρnn : ∀ x, 0 ≤ C.ρ u x) (hν : 0 ≤ C.ν) :
    (s102_rateM C m hT L u).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext k k'
    simp [Matrix.conjTranspose_apply, s102_rateM_symm hT L u k k']
  · intro z
    have h := s102_gram_identity_B hD hT L hu hρ (fun k k' => z k * z k')
    have e : z ⬝ᵥ (s102_rateM C m hT L u) *ᵥ z = ∑ k, ∑ k', s102_rateM C m hT L u k k' * (z k * z k') := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
      ring
    rw [star_trivial, e, h]
    refine mul_nonneg (by positivity) (integral_nonneg fun x => mul_nonneg (hρnn x) ?_)
    refine Finset.sum_nonneg fun a _ => ?_
    have : ∑ k, ∑ k', s102_vv C m hT L u x a k * s102_vv C m hT L u x a k' * (z k * z k') =
        (∑ k, z k * s102_vv C m hT L u x a k) ^ 2 := by
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
      ring
    rw [this]
    exact sq_nonneg _

end HRS.MS.R2Interp

end
