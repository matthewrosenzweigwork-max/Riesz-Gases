import HRS.MS.R2InterpAux36

/-!
# S10.2 (worker S102), part 37 (packet B2, step B): the covariance increment `Δ = ∫_{(v,u]} rate` is positive semidefinite
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators MatrixOrder Matrix

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}

/-- The covariance increment `Δ = ∫_{(v,u]} rate`. -/
def s102_Delta (C : WholeCoeff d) (m : ℝ) (hT : 0 < T) (L : ℕ) (v u : ℝ) :
    Matrix (Fin (s102_q d L)) (Fin (s102_q d L)) ℝ :=
  Matrix.of fun k k' => ∫ ρ in Ioc v u, s102_rateM C m hT L ρ k k'

theorem s102_rateM_integrableOn (hT : 0 < T) (L : ℕ)
    (hG : S102GramInt C m hT L) (k k' : Fin (s102_q d L)) :
    IntegrableOn (fun ρ => s102_rateM C m hT L ρ k k') (Icc 0 T) := by
  have : (fun ρ => s102_rateM C m hT L ρ k k') = fun ρ => 2 * C.ν *
      (if ρ ≤ min (s102_tk hT L k) (s102_tk hT L k') then s102_gram C m hT L ρ k k' else 0) := by
    funext ρ
    simp [s102_rateM]
  rw [this]
  exact ((hG k k').const_mul _)

theorem s102_Delta_psd (hD : S101Data C m T r c) (hT : 0 < T) (L : ℕ)
    (hG : S102GramInt C m hT L)
    (hρint : ∀ u ∈ Icc (0 : ℝ) T, Integrable (C.ρ u)) (hρnn : ∀ u ∈ Icc (0 : ℝ) T, ∀ x, 0 ≤ C.ρ u x)
    (hν : 0 ≤ C.ν) {v u : ℝ} (hv : 0 ≤ v) (hvu : v ≤ u) (huT : u ≤ T) :
    (s102_Delta C m hT L v u).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext k k'
    simp only [s102_Delta, Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    exact setIntegral_congr_fun measurableSet_Ioc fun ρ _ => s102_rateM_symm (C := C) (m := m) hT L ρ k' k
  · intro z
    have hsub : Ioc v u ⊆ Icc 0 T := Ioc_subset_Icc_self.trans (Icc_subset_Icc hv huT)
    have e : star z ⬝ᵥ (s102_Delta C m hT L v u) *ᵥ z =
        ∫ ρ in Ioc v u, ∑ k, ∑ k', s102_rateM C m hT L ρ k k' * (z k * z k') := by
      rw [star_trivial]
      have hint : ∀ k k', IntegrableOn (fun ρ => s102_rateM C m hT L ρ k k' * (z k * z k')) (Ioc v u) :=
        fun k k' => ((s102_rateM_integrableOn hT L hG k k').mono_set hsub).mul_const _
      rw [integral_finsetSum _ (fun k _ => integrable_finset_sum _ fun k' _ => hint k k')]
      simp only [dotProduct, Matrix.mulVec, s102_Delta, Matrix.of_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_finsetSum _ (fun k' _ => hint k k')]
      refine Finset.sum_congr rfl fun k' _ => ?_
      rw [integral_mul_const]
      ring
    rw [e]
    refine setIntegral_nonneg measurableSet_Ioc fun ρ hρ => ?_
    have hρT : ρ ∈ Icc (0 : ℝ) T := hsub hρ
    have hpsd := s102_rateM_psd hD hT L hρT (hρint ρ hρT) (hρnn ρ hρT) hν
    have := (Matrix.posSemidef_iff_dotProduct_mulVec.1 hpsd).2 z
    rw [star_trivial] at this
    have e2 : z ⬝ᵥ (s102_rateM C m hT L ρ) *ᵥ z = ∑ k, ∑ k', s102_rateM C m hT L ρ k k' * (z k * z k') := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
      ring
    rwa [e2] at this

end HRS.MS.R2Interp

end
