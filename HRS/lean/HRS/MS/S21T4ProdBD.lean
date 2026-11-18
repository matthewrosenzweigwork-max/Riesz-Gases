import HRS.MS.S21T4ProdBC
import HRS.MS.S21T4ProdAX
import HRS.MS.S21T4ProdAT

/-!
# R26-T3.S13: exact Cramér-Wold projections of finite-rank families

The particle projection is the genuine pair energy of the combined kernel
(pointwise, including the centering). The Gaussian projection is the
half-Wick polynomial of the same combined matrix.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos

variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_finite_family_particle_projection {n r m N : ℕ}
    (f : Fin n → Euc d → ℝ)
    (c : Fin m → Fin r → Fin r → ℝ) (u : Fin r → Euc d → ℝ)
    (hu : ∀ i, IsR2Test (u i))
    (hc : ∀ k i j, c k i j = c k j i)
    (X : EucConfig d N) (t : EuclideanSpace ℝ (Fin (n + m))) :
    inner ℝ
      (WithLp.toLp 2 (Fin.append
        (fun i : Fin n => r2EmpDistr μ X (f i))
        (fun k : Fin m => (N : ℝ) * pairEnergy (r2FiniteRankKernel (c k) u) X μ)) :
        EuclideanSpace ℝ (Fin (n + m))) t =
      (∑ i : Fin n, t (Fin.castAdd m i) * r2EmpDistr μ X (f i)) +
      (N : ℝ) * pairEnergy
        (r2FiniteRankKernel
          (fun a b => ∑ k : Fin m, t (Fin.natAdd n k) * c k a b) u) X μ := by
  let α : Fin m → ℝ := fun k => t (Fin.natAdd n k)
  let h : Fin m → Euc d → Euc d → ℝ := fun k => r2FiniteRankKernel (c k) u
  have hdata : ∀ k, IsR2FiniteRankData (c k) u :=
    fun k => ⟨hc k, (fun i => (hu i).1), (fun i => (hu i).2)⟩
  have hK : ∀ k, S94KOK μ (h k) :=
    fun k => s21t4_finite_rank_KOK (c k) u (hdata k)
  have heq : r2FiniteRankKernel (fun a b => ∑ k, α k * c k a b) u =
      (fun x y => ∑ k, α k * h k x y) := by
    funext x y
    exact s21t4_finite_rank_kernel_combination c u α x y
  have hcomb : pairEnergy
      (r2FiniteRankKernel (fun a b => ∑ k, α k * c k a b) u) X μ =
      ∑ k, α k * pairEnergy (h k) X μ := by
    rw [heq]
    exact s21t4_pairEnergy_family_linear h hK α X
  calc
    _ = (∑ i : Fin n, t (Fin.castAdd m i) * r2EmpDistr μ X (f i)) +
      ∑ k : Fin m, α k * ((N : ℝ) * pairEnergy (h k) X μ) :=
      s21t4_finappend_inner _ _ t
    _ = _ := by
      rw [hcomb]
      change (∑ i : Fin n, t (Fin.castAdd m i) * r2EmpDistr μ X (f i)) +
        ∑ k : Fin m, α k * ((N : ℝ) * pairEnergy (h k) X μ) =
        (∑ i : Fin n, t (Fin.castAdd m i) * r2EmpDistr μ X (f i)) +
        (N : ℝ) * ∑ k : Fin m, α k * pairEnergy (h k) X μ
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring

theorem s21t4_finite_family_limit_projection
    (I : ProductGaussian μ) {n r m : ℕ}
    (f : Fin n → Euc d → ℝ)
    (c : Fin m → Fin r → Fin r → ℝ) (u : Fin r → Euc d → ℝ)
    (ω : I.Ω) (t : EuclideanSpace ℝ (Fin (n + m))) :
    inner ℝ
      (WithLp.toLp 2 (Fin.append
        (fun i : Fin n => I.η (f i) ω)
        (fun k : Fin m => (1 / 2 : ℝ) *
          ∑ a : Fin r, ∑ b : Fin r, c k a b *
            (I.η (u a) ω * I.η (u b) ω -
              HRS.Whole.pair μ (fun x => u a x * u b x)))) :
        EuclideanSpace ℝ (Fin (n + m))) t =
      (∑ i : Fin n, t (Fin.castAdd m i) * I.η (f i) ω) +
      (1 / 2 : ℝ) * ∑ a : Fin r, ∑ b : Fin r,
        (∑ k : Fin m, t (Fin.natAdd n k) * c k a b) *
          (I.η (u a) ω * I.η (u b) ω -
            HRS.Whole.pair μ (fun x => u a x * u b x)) := by
  let α : Fin m → ℝ := fun k => t (Fin.natAdd n k)
  let z : Fin r → ℝ := fun a => I.η (u a) ω
  let v : Fin r → Fin r → ℝ :=
    fun a b => HRS.Whole.pair μ (fun x => u a x * u b x)
  calc
    _ = (∑ i : Fin n, t (Fin.castAdd m i) * I.η (f i) ω) +
        ∑ k : Fin m, α k * ((1 / 2 : ℝ) *
          ∑ a : Fin r, ∑ b : Fin r, c k a b *
            (z a * z b - v a b)) := s21t4_finappend_inner _ _ t
    _ = _ := by
      rw [← s21t4_finite_rank_polynomial_combination c α z v]

end HRS.MS.R26T3
