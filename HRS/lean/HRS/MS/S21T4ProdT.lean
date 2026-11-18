import HRS.MS.S21T4ProdS

/-! Equality of the auxiliary finite-rank CLT Gaussian law and the common isonormal law. -/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

/-- The Gaussian measure supplied by the finite-rank CLT is exactly the
finite-coordinate law of the canonical product-Gaussian field whenever
both have the covariance of the same reference tests. -/
theorem s21t4_finite_rank_gaussian_identification
    (I : ProductGaussian μ) {n m : ℕ}
    (f : Fin n → Euc d → ℝ) (u : Fin m → Euc d → ℝ)
    (hf : ∀ i, MemLp (f i) 2 μ) (hu : ∀ j, MemLp (u j) 2 μ)
    (G : Measure ((Fin n → ℝ) × (Fin m → ℝ)))
    (hG : HRS.IsCenteredGaussian G)
    (hcovG : ∀ L M : ((Fin n → ℝ) × (Fin m → ℝ)) →L[ℝ] ℝ,
      (∫ z, L z * M z ∂G) =
      ∫ x, L ((fun i => HRS.Whole.projMean μ (f i) x),
                  (fun j => HRS.Whole.projMean μ (u j) x)) *
             M ((fun i => HRS.Whole.projMean μ (f i) x),
                  (fun j => HRS.Whole.projMean μ (u j) x)) ∂μ) :
    G = I.P.map (fun ω =>
      ((fun i => I.η (f i) ω), (fun j => I.η (u j) ω))) := by
  letI := I.mΩ
  letI := I.prob
  let V : Measure ((Fin n → ℝ) × (Fin m → ℝ)) := I.P.map (fun ω =>
    ((fun i => I.η (f i) ω), (fun j => I.η (u j) ω)))
  have hV : HRS.IsCenteredGaussian V :=
    s21t4_product_joint_gaussian_law I f u hf hu
  haveI : IsGaussian G := hG.1
  haveI : IsGaussian V := hV.1
  apply s21t4_gaussian_pair_law_unique G V hG hV
  intro L
  have hG2 := hcovG L L
  have hV2 := s21t4_product_joint_covariance I f u hf hu L L
  have heq : (∫ z, L z * L z ∂G) =
      (∫ z, L z * L z ∂V) := hG2.trans hV2.symm
  rw [covarianceBilinDual_apply (μ := G) IsGaussian.memLp_two_id,
      covarianceBilinDual_apply (μ := V) IsGaussian.memLp_two_id]
  simp only [hG.2 L, hV.2 L, sub_zero]
  exact heq

end HRS.MS.R26T3
