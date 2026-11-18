import HRS.MS.S21T4ProdBE
import HRS.MS.S21T4ProdAH

/-!
# S13: centered finite-rank joint CLT for a common finite test family

This is the exact half-Wick normalization, including the half-double-mean
correction to each particle pair-energy coordinate.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem pro_s13_finite_family_centered_joint
    (I : ProductGaussian μ) {n r m : ℕ}
    (f : Fin n → Euc d → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (c : Fin m → Fin r → Fin r → ℝ) (u : Fin r → Euc d → ℝ)
    (hu : ∀ i, IsR2Test (u i))
    (hc : ∀ k i j, c k i j = c k j i) :
    TendstoInDistribution
      (fun N (X : EucConfig d N) =>
        (WithLp.toLp 2 (Fin.append
          (fun i : Fin n => r2EmpDistr μ X (f i))
          (fun k : Fin m => (N : ℝ) *
            pairEnergy (r2FiniteRankKernel (c k) u) X μ +
              (1 / 2 : ℝ) * ∫ x, ∫ y,
                r2FiniteRankKernel (c k) u x y ∂μ ∂μ)) :
          EuclideanSpace ℝ (Fin (n + m)))) atTop
      (fun ω : I.Ω =>
        (WithLp.toLp 2 (Fin.append
          (fun i : Fin n => I.η (f i) ω)
          (fun k : Fin m =>
            (1 / 2 : ℝ) * ∑ a : Fin r, ∑ b : Fin r, c k a b *
              (I.η (u a) ω * I.η (u b) ω -
                ∫ ζ, I.η (u a) ζ * I.η (u b) ζ ∂I.P))) :
          EuclideanSpace ℝ (Fin (n + m))))
      (fun N => Measure.pi fun _ : Fin N => μ) I.P := by
  classical
  let b : Fin m → ℝ := fun k =>
    (1 / 2 : ℝ) * ∫ x, ∫ y, r2FiniteRankKernel (c k) u x y ∂μ ∂μ
  let B : EuclideanSpace ℝ (Fin (n + m)) :=
    WithLp.toLp 2 (Fin.append (fun _ : Fin n => (0 : ℝ)) b)
  let F : EuclideanSpace ℝ (Fin (n + m)) →
      EuclideanSpace ℝ (Fin (n + m)) := fun z => z + B
  have hF : Continuous F := continuous_id.add continuous_const
  have hdist := (s21t4_finite_family_joint_one_space I f hf c u hu hc).continuous_comp hF
  have hdata : ∀ k, IsR2FiniteRankData (c k) u :=
    fun k => ⟨hc k, (fun i => (hu i).1), (fun i => (hu i).2)⟩
  have hY : ∀ N (X : EucConfig d N),
      F (WithLp.toLp 2 (Fin.append
        (fun i : Fin n => r2EmpDistr μ X (f i))
        (fun k : Fin m => (N : ℝ) * pairEnergy (r2FiniteRankKernel (c k) u) X μ))) =
        (WithLp.toLp 2 (Fin.append
          (fun i : Fin n => r2EmpDistr μ X (f i))
          (fun k : Fin m => (N : ℝ) * pairEnergy (r2FiniteRankKernel (c k) u) X μ + b k)) :
          EuclideanSpace ℝ (Fin (n + m))) := by
    intro N X
    ext i
    refine Fin.addCases (fun j => ?_) (fun k => ?_) i
    · simp [F, B]
    · simp [F, B]
  have hZ : ∀ ω : I.Ω,
      F (WithLp.toLp 2 (Fin.append
        (fun i : Fin n => I.η (f i) ω)
        (fun k : Fin m => (1 / 2 : ℝ) * ∑ a : Fin r, ∑ b : Fin r,
          c k a b * (I.η (u a) ω * I.η (u b) ω -
            HRS.Whole.pair μ (fun x => u a x * u b x))))) =
        (WithLp.toLp 2 (Fin.append
          (fun i : Fin n => I.η (f i) ω)
          (fun k : Fin m => (1 / 2 : ℝ) * ∑ a : Fin r, ∑ b : Fin r,
            c k a b * (I.η (u a) ω * I.η (u b) ω -
              ∫ ζ, I.η (u a) ζ * I.η (u b) ζ ∂I.P))) :
          EuclideanSpace ℝ (Fin (n + m))) := by
    intro ω
    ext i
    refine Fin.addCases (fun j => ?_) (fun k => ?_) i
    · simp [F, B]
    · simp only [F, B, PiLp.add_apply, Fin.append_right]
      exact (s21t4_finite_rank_wick_offset I (c k) u (hdata k) ω)
  convert hdist using 1
  · funext N X
    exact (hY N X).symm
  · funext ω
    exact (hZ ω).symm

end HRS.MS.R26T3
