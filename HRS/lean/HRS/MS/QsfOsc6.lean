import HRS.MS.QsfOsc5

/-!
# S4.5 oscillator clause, part 6: `ζ_N = Ψ⁻¹ (feature vector)`
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

/-- The isometry `B_m ≃ ℓ²(ℕ)` of an enumeration of the multi-indices. -/
def s45_Psi (m : ℝ) (e : ℕ ≃ MultiIndex d) : OscDual d m ≃ₗᵢ[ℝ] SeqL2 := s45_reindex e

theorem s45_Psi_coord (m : ℝ) (e : ℕ ≃ MultiIndex d) (u : OscDual d m) (j : ℕ) :
    SeqL2.coord (s45_Psi m e u) j = OscDual.coord u (e j) := rfl

theorem s45_coord_eq_hermiteCoeff {m : ℝ} (u : OscDual d m) (α : MultiIndex d) :
    OscDual.coord u α = oscEigenvalue d α ^ (-(m / 2)) * OscDual.hermiteCoeff u α := by
  unfold OscDual.hermiteCoeff
  rw [← mul_assoc, rpow_neg_half_mul m _ (oscEv_pos α), one_mul]

theorem s45_zetaB_coord {m : ℝ} (hm : (d : ℝ) < m) (P : Measure (EucConfig d N))
    [IsProbabilityMeasure P] (hN : 1 ≤ N) (X : EucConfig d N) (α : MultiIndex d) :
    OscDual.coord (zetaB m P X) α = Real.sqrt N * (oscEigenvalue d α ^ (-(m / 2)) *
      (pair (empirical X) (hermiteFunD α) - pair (meanEmpirical P) (hermiteFunD α))) := by
  haveI : IsProbabilityMeasure (meanEmpirical P) := meanEmpirical_isProbabilityMeasure P hN
  haveI : IsProbabilityMeasure (empirical X) := empirical_isProbabilityMeasure hN X
  have h1 : OscDual.coord (zetaB m P X) α = Real.sqrt N * OscDual.coord
      (OscDual.ofMeasureDiff m (empirical X) (meanEmpirical P)) α := rfl
  rw [h1, s45_coord_eq_hermiteCoeff (OscDual.ofMeasureDiff m (empirical X) (meanEmpirical P)) α,
    OscDual.hermiteCoeff_ofMeasureDiff hm]
  rfl

theorem s45_Psi_zetaB {m : ℝ} (hm : (d : ℝ) < m) (e : ℕ ≃ MultiIndex d)
    {J : ℕ} (hφ : HRS.Whole.IsSummableFeatureFamily J (fun j : ℕ => oscTestFun m (e j)))
    (P : Measure (EucConfig d N)) [IsProbabilityMeasure P] (hex : IsExchangeable P) (hN : 1 ≤ N)
    (X : EucConfig d N) :
    s45_Psi m e (zetaB m P X) =
      featureVec (fun j : ℕ => oscTestFun m (e j)) (firstMarginal P) X := by
  haveI : IsProbabilityMeasure (firstMarginal P) := by
    have : firstMarginal P = meanEmpirical P := (meanEmpirical_eq_firstMarginal P hex hN).symm
    rw [this]; exact meanEmpirical_isProbabilityMeasure P hN
  refine lp.ext (funext fun j => ?_)
  show SeqL2.coord (s45_Psi m e (zetaB m P X)) j = SeqL2.coord (featureVec
    (fun j : ℕ => oscTestFun m (e j)) (firstMarginal P) X) j
  rw [s45_Psi_coord, s45_zetaB_coord hm P hN X (e j)]
  unfold featureVec
  rw [s45_coord_ofSeq (s45_feature_memℓp hN hφ X), ← meanEmpirical_eq_firstMarginal P hex hN]
  unfold pair oscTestFun
  rw [integral_const_mul, integral_const_mul]
  ring

end S45

end
