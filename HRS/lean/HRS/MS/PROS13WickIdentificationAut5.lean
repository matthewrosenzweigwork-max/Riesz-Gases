import HRS.MS.PROS13WickConvergenceAut5
import HRS.MS.PROS13CrossLimitLinear

/-!
# S13: every actual Gaussian quadratic limit satisfies all-ONB Wick chaos

The proof compares the arbitrary product-L² finite-rank limit with the Wick
limit of a symmetric measurable representative. This retains the correct
nonzero quadratic limit for atomic measures, even when the frozen ONB
predicate is empty.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem pro_s13_actual_product_quadratic_all_ONB_wick
    (I : ProductGaussian μ)
    (h : Euc d → Euc d → ℝ)
    (hh : MemLp (fun z : Euc d × Euc d => h z.1 z.2) 2 (μ.prod μ))
    (hs : ∀ x y, h x y = h y x)
    (Q : I.Ω → ℝ)
    (hQ : HasActualProductQuadraticLimit I h Q)
    (a : ℕ → Euc d → ℝ) (ha : IsR2ZeroMeanONB μ a) :
    IsR2WickChaos I.P μ a (fun j => I.η (a j))
      (r2CenterKernel μ h) (fun ω => 2 * Q ω) := by
  classical
  letI := I.mΩ
  letI := I.prob
  obtain ⟨hQL2, r, c, u, hd, happrox, hlim⟩ := hQ
  obtain ⟨K, hKm, hKs, hK2, hKH⟩ :=
    pro_s13_symmetric_measurable_representative h hh hs
  have hz : S94GSeq I.P (fun i ω => I.η (a i) ω) 1 :=
    s21l_gseq (s21t4_product_eta_bundle I) ha.1 ha.2.1
  obtain ⟨W, hW, _⟩ :=
    s94_wick_exists hz (by norm_num : (0 : ℝ) ≤ 1)
      ha.1 ha.2.1 hKm hKs hK2
  let Qj : ℕ → I.Ω → ℝ := fun j ω =>
    (1 / 2 : ℝ) *
      ∑ p : Fin (r j), ∑ q : Fin (r j), c j p q *
        (I.η (u j p) ω * I.η (u j q) ω -
          ∫ ζ, I.η (u j p) ζ * I.η (u j q) ζ ∂I.P)
  have hQjm : ∀ j, MemLp (Qj j) 2 I.P := by
    intro j
    have hu : ∀ i, MemLp (u j i) 2 μ :=
      fun i => ((hd j).smooth i).continuous.memLp_of_hasCompactSupport
        ((hd j).compactSupport i)
    exact s21t4_generic_product_finite_rank_quadratic_L2 I (u j) hu (c j)
  have hQ2jm : ∀ j, MemLp (fun ω => 2 * Qj j ω) 2 I.P :=
    fun j => (hQjm j).const_mul 2
  have hWlim : Tendsto
      (fun j => ∫ ω : I.Ω, (W ω - 2 * Qj j ω) ^ 2 ∂I.P)
      atTop (𝓝 0) := by
    simpa only [Qj] using
      (pro_s13_Wick_actual_approximation_L2
        I h K hh hKm hKs hK2 hKH a ha r c u hd happrox W hW)
  have hWlim' : Tendsto
      (fun j => ∫ ω : I.Ω, (2 * Qj j ω - W ω) ^ 2 ∂I.P)
      atTop (𝓝 0) := by
    convert hWlim using 1
    funext j
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    ring
  have hQlim' : Tendsto
      (fun j => ∫ ω : I.Ω, (2 * Qj j ω - 2 * Q ω) ^ 2 ∂I.P)
      atTop (𝓝 0) := by
    have hsquared := hlim.const_mul (4 : ℝ)
    have he : ∀ j,
        (∫ ω : I.Ω, (2 * Qj j ω - 2 * Q ω) ^ 2 ∂I.P) =
        4 * (∫ ω : I.Ω, (Qj j ω - Q ω) ^ 2 ∂I.P) := by
      intro j
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      ring
    have hT : Tendsto
        (fun j => 4 * ∫ ω : I.Ω, (Qj j ω - Q ω) ^ 2 ∂I.P)
        atTop (𝓝 0) := by
      simpa only [Qj, mul_zero] using hsquared
    exact hT.congr' (Filter.Eventually.of_forall fun j => (he j).symm)
  have hunique : (fun ω : I.Ω => 2 * Q ω) =ᵐ[I.P] W :=
    pro_s13_L2_squared_limit_unique I.P
      (fun j ω => 2 * Qj j ω)
      (fun ω => 2 * Q ω) W
      hQ2jm (hQL2.const_mul 2) hW.1 hQlim' hWlim'
  have hWQ : s94WickL2 I.P μ a
      (fun j ω => I.η (a j) ω)
      K (fun ω => 2 * Q ω) := by
    refine ⟨hQL2.const_mul 2, ?_⟩
    refine hW.2.congr fun n => integral_congr_ae ?_
    filter_upwards [hunique] with ω hω
    rw [hω]
  have hcoef : (fun i j =>
      r2WickCoeff μ a (r2CenterKernel μ h) i j) =
      (fun i j => r2WickCoeff μ a K i j) := by
    funext i j
    have hi : Integrable
        (fun z : Euc d × Euc d => h z.1 z.2) (μ.prod μ) :=
      hh.integrable one_le_two
    have hKi : Integrable
        (fun z : Euc d × Euc d => K z.1 z.2) (μ.prod μ) :=
      hK2.integrable one_le_two
    rw [s21l_coeff_center ha.1 hi,
      s21l_coeff_prod ha.1 hi, s21l_coeff_prod ha.1 hKi]
    refine integral_congr_ae ?_
    filter_upwards [hKH] with z hz
    rw [hz]
  have hWQh : s94WickL2 I.P μ a
      (fun j ω => I.η (a j) ω)
      (r2CenterKernel μ h) (fun ω => 2 * Q ω) := by
    unfold s94WickL2 at hWQ ⊢
    simpa only [hcoef] using hWQ
  exact s94WickL2.isWick hz hWQh

#print axioms pro_s13_actual_product_quadratic_all_ONB_wick
end HRS.MS.R26T3
