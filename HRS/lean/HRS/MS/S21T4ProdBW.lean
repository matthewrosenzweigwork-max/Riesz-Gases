import HRS.MS.S21T4ProdBV
import HRS.MS.S21T4ProdBE
import HRS.MS.S21T4ProdAH

/-!
# S13: finite-family product CLT with the actual second-chaos polynomial

The same original ProductGaussian witnesses drive the finite-family joint
particle limit, even for finite atomic μ. There is no infinite-ONB assumption
or zero-chaos fallback. Finite-rank inputs are smooth test functions.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_finite_family_joint_second_one_space
    (I : ProductGaussian μ) {n r m : ℕ}
    (f : Fin n → Euc d → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (c : Fin m → Fin r → Fin r → ℝ) (u : Fin r → Euc d → ℝ)
    (hu : ∀ i, IsR2Test (u i)) (hc : ∀ k i j, c k i j = c k j i) :
    ∃ Q : Fin m → I.Ω → ℝ,
      (∀ k, InSecondChaos I.P I.ξ 3 (Q k)) ∧
      (∀ k, MemLp (Q k) 2 I.P) ∧
      TendstoInDistribution
        (fun N (X : EucConfig d N) =>
          (WithLp.toLp 2 (Fin.append
            (fun i : Fin n => r2EmpDistr μ X (f i))
            (fun k : Fin m => (N : ℝ) * pairEnergy (r2FiniteRankKernel (c k) u) X μ)) :
              EuclideanSpace ℝ (Fin (n + m)))) atTop
        (fun ω : I.Ω =>
          (WithLp.toLp 2 (Fin.append
            (fun i : Fin n => I.η (f i) ω)
            (fun k : Fin m => Q k ω - (1 / 2 : ℝ) *
              ∫ x, ∫ y, r2FiniteRankKernel (c k) u x y ∂μ ∂μ)) :
              EuclideanSpace ℝ (Fin (n + m))))
        (fun N => Measure.pi fun _ : Fin N => μ) I.P := by
  classical
  letI := I.mΩ
  letI := I.prob
  have hu2 : ∀ i, MemLp (u i) 2 μ := fun i =>
    (hu i).1.continuous.memLp_of_hasCompactSupport (hu i).2
  have hdata : ∀ k, IsR2FiniteRankData (c k) u :=
    fun k => ⟨hc k, (fun i => (hu i).1), (fun i => (hu i).2)⟩
  let Q : Fin m → I.Ω → ℝ := fun k ω => (1 / 2 : ℝ) *
    ∑ a : Fin r, ∑ b : Fin r, c k a b *
      (I.η (u a) ω * I.η (u b) ω -
        ∫ ζ, I.η (u a) ζ * I.η (u b) ζ ∂I.P)
  have hQ2 : ∀ k, MemLp (Q k) 2 I.P := fun k =>
    s21t4_generic_product_finite_rank_quadratic_L2 I u hu2 (c k)
  have hQsecond : ∀ k, InSecondChaos I.P I.ξ 3 (Q k) := fun k =>
    s21t4_generic_product_finite_rank_quadratic_second I u hu2 (c k)
  refine ⟨Q, hQsecond, hQ2, ?_⟩
  have hdist := s21t4_finite_family_joint_one_space I f hf c u hu hc
  have hlim : (fun ω : I.Ω =>
      (WithLp.toLp 2 (Fin.append
        (fun i : Fin n => I.η (f i) ω)
        (fun k : Fin m => (1 / 2 : ℝ) * ∑ a : Fin r, ∑ b : Fin r,
          c k a b * (I.η (u a) ω * I.η (u b) ω -
            HRS.Whole.pair μ (fun x => u a x * u b x)))) :
          EuclideanSpace ℝ (Fin (n + m)))) =ᵐ[I.P]
      (fun ω : I.Ω =>
      (WithLp.toLp 2 (Fin.append
        (fun i : Fin n => I.η (f i) ω)
        (fun k : Fin m => Q k ω - (1 / 2 : ℝ) *
          ∫ x, ∫ y, r2FiniteRankKernel (c k) u x y ∂μ ∂μ)) :
          EuclideanSpace ℝ (Fin (n + m)))) := by
    apply ae_of_all
    intro ω
    dsimp only
    congr 1
    funext i
    refine Fin.addCases (fun j => ?_) (fun k => ?_) i
    · simp
    · simp only [Fin.append_right]
      dsimp [Q]
      linarith only [s21t4_finite_rank_wick_offset I (c k) u (hdata k) ω]
  exact TendstoInDistribution.congr (fun N => ae_of_all _ fun X => rfl) hlim hdist

end HRS.MS.R26T3
