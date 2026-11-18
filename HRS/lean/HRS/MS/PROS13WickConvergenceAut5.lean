import HRS.MS.PROS13WickL2UniqueAut5
import HRS.MS.PROS13CompletionE
import HRS.MS.S21L_G11D

/-!
# S13: convergence of finite-rank quadratic polynomials to an ONB Wick chaos

The limiting Wick chaos is built from a measurable symmetric product-L²
representative. The finite-rank polynomials use the actual shared
ProductGaussian field, without assuming an ONB exists for arbitrary μ.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem pro_s13_Wick_actual_approximation_L2
    (I : ProductGaussian μ)
    (h K : Euc d → Euc d → ℝ)
    (hh : MemLp (fun z : Euc d × Euc d => h z.1 z.2) 2 (μ.prod μ))
    (hKm : Measurable (fun z : Euc d × Euc d => K z.1 z.2))
    (hKs : ∀ x y, K x y = K y x)
    (hK2 : MemLp (fun z : Euc d × Euc d => K z.1 z.2) 2 (μ.prod μ))
    (hKH : (fun z : Euc d × Euc d => K z.1 z.2) =ᵐ[μ.prod μ]
      (fun z => h z.1 z.2))
    (a : ℕ → Euc d → ℝ) (ha : IsR2ZeroMeanONB μ a)
    (r : ℕ → ℕ)
    (c : (j : ℕ) → Fin (r j) → Fin (r j) → ℝ)
    (u : (j : ℕ) → Fin (r j) → Euc d → ℝ)
    (hd : ∀ j, IsR2FiniteRankData (c j) (u j))
    (happrox : Tendsto (fun j => eLpNorm
      (fun z : Euc d × Euc d =>
        r2FiniteRankKernel (c j) (u j) z.1 z.2 - h z.1 z.2)
      2 (μ.prod μ)) atTop (𝓝 0))
    (W : I.Ω → ℝ)
    (hW : s94WickL2 I.P μ a (fun j ω => I.η (a j) ω) K W) :
    Tendsto
      (fun j => ∫ ω : I.Ω,
        (W ω - 2 * ((1 / 2 : ℝ) *
          ∑ p : Fin (r j), ∑ q : Fin (r j), c j p q *
            (I.η (u j p) ω * I.η (u j q) ω -
              ∫ ζ, I.η (u j p) ζ * I.η (u j q) ζ ∂I.P))) ^ 2 ∂I.P)
      atTop (𝓝 0) := by
  classical
  letI := I.mΩ
  letI := I.prob
  let hj : ℕ → Euc d → Euc d → ℝ :=
    fun j => r2FiniteRankKernel (c j) (u j)
  let Qj : ℕ → I.Ω → ℝ := fun j ω =>
    (1 / 2 : ℝ) *
      ∑ p : Fin (r j), ∑ q : Fin (r j), c j p q *
        (I.η (u j p) ω * I.η (u j q) ω -
          ∫ ζ, I.η (u j p) ζ * I.η (u j q) ζ ∂I.P)
  have hmj : ∀ j, MemLp
      (fun z : Euc d × Euc d => hj j z.1 z.2)
      2 (μ.prod μ) :=
    fun j => s21t4_finite_rank_memLp (c j) (u j) (hd j)
  have hmeasj : ∀ j, Measurable
      (fun z : Euc d × Euc d => hj j z.1 z.2) := by
    intro j
    exact s94_finiteRank_measurable
      (fun i => ⟨(hd j).smooth i, (hd j).compactSupport i⟩)
  have hsymj : ∀ j x y, hj j x y = hj j y x :=
    fun j x y => s21t4_finite_rank_symmetric
      (c j) (u j) (hd j) x y
  have hz : S94GSeq I.P (fun i ω => I.η (a i) ω) 1 :=
    s21l_gseq (s21t4_product_eta_bundle I) ha.1 ha.2.1
  have hWj : ∀ j, s94WickL2 I.P μ a
      (fun i ω => I.η (a i) ω) (hj j)
      (fun ω => 2 * Qj j ω) := by
    intro j
    have hw := pro_s13_actual_finite_rank_wick
      I (c j) (u j) (hd j) a ha
    have hcenter := s94_isWick_to_L2 hz hw
    have hcoef : (fun i k =>
      r2WickCoeff μ a (r2CenterKernel μ (hj j)) i k) =
      (fun i k => r2WickCoeff μ a (hj j) i k) := by
      funext i k
      exact s21l_coeff_center ha.1
        ((hmj j).integrable one_le_two) i k
    unfold s94WickL2 at hcenter ⊢
    simpa only [hcoef, Qj, hj] using hcenter
  have hkSq : Tendsto (fun j =>
      ∫ z : Euc d × Euc d,
        (K z.1 z.2 - hj j z.1 z.2) ^ 2 ∂(μ.prod μ))
      atTop (𝓝 0) := by
    have hNorm : Tendsto (fun j => eLpNorm
        (fun z : Euc d × Euc d =>
          hj j z.1 z.2 - h z.1 z.2) 2 (μ.prod μ))
        atTop (𝓝 0) := by
      simpa only [hj] using happrox
    have hMem : ∀ j, MemLp
        (fun z : Euc d × Euc d =>
          hj j z.1 z.2 - h z.1 z.2) 2 (μ.prod μ) :=
      fun j => (hmj j).sub hh
    have hSq := s21t4_integral_sq_tendsto_zero
      (fun j (z : Euc d × Euc d) =>
        hj j z.1 z.2 - h z.1 z.2) hMem hNorm
    convert hSq using 1
    funext j
    refine integral_congr_ae ?_
    filter_upwards [hKH] with z hz
    rw [hz]
    ring
  have hbd : ∀ j, (∫ ω : I.Ω,
      (W ω - 2 * Qj j ω) ^ 2 ∂I.P) ≤
      2 * (1 : ℝ) ^ 2 * ∫ z : Euc d × Euc d,
        (K z.1 z.2 - hj j z.1 z.2) ^ 2 ∂(μ.prod μ) := by
    intro j
    exact s94_wick_lipschitz hz (by norm_num)
      ha.1 ha.2.1 hKm hKs hK2
      (hmeasj j) (hsymj j) (hmj j)
      hW (hWj j)
  have hupper : Tendsto (fun j =>
      2 * (1 : ℝ) ^ 2 * ∫ z : Euc d × Euc d,
        (K z.1 z.2 - hj j z.1 z.2) ^ 2 ∂(μ.prod μ))
      atTop (𝓝 0) := by
    simpa using hkSq.const_mul (2 : ℝ)
  have hWsq : Tendsto (fun j => ∫ ω : I.Ω,
      (W ω - 2 * Qj j ω) ^ 2 ∂I.P) atTop (𝓝 0) := by
    refine squeeze_zero (fun j => integral_nonneg fun ω => sq_nonneg _)
      hbd hupper
  simpa only [Qj] using hWsq

#print axioms pro_s13_Wick_actual_approximation_L2
end HRS.MS.R26T3
