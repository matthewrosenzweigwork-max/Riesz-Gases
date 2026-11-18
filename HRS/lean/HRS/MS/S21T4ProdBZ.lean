import HRS.MS.S21T4ProdBY
import HRS.MS.S21T4ProdV
import HRS.MS.S21T4ProdAH

/-!
# S13: second-moment control for the *actual* Gaussian quadratic polynomial

The weak limit of the centered particle pair statistic is identified on
the original ProductGaussian probability space. Portmanteau together
with the direct particle L² integrability and the exact product
U-statistic estimate transfers a uniform L² bound to the limit.
No infinite orthonormal basis or nonatomic hypothesis is required.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_generic_product_finite_rank_quadratic_sq_bound
    (I : ProductGaussian μ) {r : ℕ}
    (c : Fin r → Fin r → ℝ) (u : Fin r → Euc d → ℝ)
    (hu : IsR2FiniteRankData c u) :
    (∫ ω : I.Ω, ((1 / 2 : ℝ) *
      ∑ i : Fin r, ∑ j : Fin r, c i j *
        (I.η (u i) ω * I.η (u j) ω -
          ∫ ζ, I.η (u i) ζ * I.η (u j) ζ ∂I.P)) ^ 2 ∂I.P) ≤
    18 * ∫ z : Euc d × Euc d, (r2FiniteRankKernel c u z.1 z.2) ^ 2 ∂(μ.prod μ) := by
  letI := I.mΩ
  letI := I.prob
  let h : Euc d → Euc d → ℝ := r2FiniteRankKernel c u
  let b : ℝ := (1 / 2 : ℝ) * ∫ x, ∫ y, h x y ∂μ ∂μ
  let Q : I.Ω → ℝ := fun ω => (1 / 2 : ℝ) *
    ∑ i : Fin r, ∑ j : Fin r, c i j *
      (I.η (u i) ω * I.η (u j) ω -
        ∫ ζ, I.η (u i) ζ * I.η (u j) ζ ∂I.P)
  have ht : ∀ i, IsR2Test (u i) :=
    fun i => ⟨hu.smooth i, hu.compactSupport i⟩
  have hu2 : ∀ i, MemLp (u i) 2 μ := fun i =>
    (hu.smooth i).continuous.memLp_of_hasCompactSupport (hu.compactSupport i)
  have hh : MemLp (fun z : Euc d × Euc d => h z.1 z.2) 2 (μ.prod μ) :=
    s21t4_finite_rank_memLp c u hu
  have hs : ∀ x y, h x y = h y x :=
    s21t4_finite_rank_symmetric c u hu
  have hZi : Integrable (fun ω => (Q ω) ^ 2) I.P :=
    (s21t4_generic_product_finite_rank_quadratic_L2 I u hu2 c).integrable_sq
  have hclt := s21t4_finite_rank_joint_one_space I
    (fun i : Fin 0 => i.elim0) (fun i => i.elim0) c u hu
  let g : ((Fin 0 → ℝ) × ℝ) → ℝ := fun v => v.2 + b
  have hg : Continuous g := continuous_snd.add continuous_const
  have hproj := hclt.continuous_comp hg
  have hlim : (fun ω : I.Ω => g
      ((fun i : Fin 0 => I.η ((fun j : Fin 0 => j.elim0) i) ω),
       (1 / 2 : ℝ) * ∑ i : Fin r, ∑ j : Fin r, c i j *
        (I.η (u i) ω * I.η (u j) ω -
          HRS.Whole.pair μ (fun x => u i x * u j x)))) =ᵐ[I.P] Q := by
    apply ae_of_all
    intro ω
    dsimp only [g, Q, b, h]
    linarith only [s21t4_finite_rank_wick_offset I c u hu ω]
  have hweak : TendstoInDistribution
      (fun N (X : EucConfig d N) => (N : ℝ) * pairEnergy h X μ + b) atTop
      Q (fun N => Measure.pi fun _ : Fin N => μ) I.P := by
    refine TendstoInDistribution.congr (fun N => ae_of_all _ fun X => rfl) hlim hproj
  have hYi : ∀ᶠ N in atTop, Integrable
      (fun X : EucConfig d N => ((N : ℝ) * pairEnergy h X μ + b) ^ 2)
      (Measure.pi fun _ : Fin N => μ) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    exact (s21t4_generic_particle_centered_memLp hN h hh hs).integrable_sq
  have hYb : ∀ᶠ N in atTop,
      (∫ X : EucConfig d N,
        ((N : ℝ) * pairEnergy h X μ + b) ^ 2
          ∂(Measure.pi fun _ : Fin N => μ)) ≤
      18 * ∫ z : Euc d × Euc d, (h z.1 z.2) ^ 2 ∂(μ.prod μ) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    exact s21l_s13_variance μ hN h hh hs
  have hC : 0 ≤ 18 * ∫ z : Euc d × Euc d,
      (h z.1 z.2) ^ 2 ∂(μ.prod μ) :=
    mul_nonneg (by norm_num) (integral_nonneg fun z => sq_nonneg _)
  exact s21t4_weak_limit_second_moment
    (fun N => Measure.pi fun _ : Fin N => μ) I.P
    (fun N (X : EucConfig d N) => (N : ℝ) * pairEnergy h X μ + b) Q
    hweak _ hC hYi hYb hZi

end HRS.MS.R26T3
