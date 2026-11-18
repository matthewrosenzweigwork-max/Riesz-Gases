import HRS.MS.PROS13QuadraticChaos
import HRS.MS.S21T4ProdF
import HRS.MS.S21L_G11C

/-!
# Generic S13: actual quadratic Gaussian polynomials have the correct Wick sections

For arbitrary probability laws admitting a complete infinite centered ONB,
the original Gaussian finite-rank polynomial is exactly one-half the
L²-Wick series of its associated doubly centered pair kernel.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem pro_s13_actual_finite_rank_wick
    (I : ProductGaussian μ)
    {r : ℕ} (c : Fin r → Fin r → ℝ)
    (u : Fin r → Euc d → ℝ)
    (hd : IsR2FiniteRankData c u)
    (a : ℕ → Euc d → ℝ)
    (ha : IsR2ZeroMeanONB μ a) :
    IsR2WickChaos I.P μ a (fun j => I.η (a j))
      (r2CenterKernel μ (r2FiniteRankKernel c u))
      (fun ω => 2 * ((1 / 2 : ℝ) *
        ∑ i : Fin r, ∑ j : Fin r, c i j *
          (I.η (u i) ω * I.η (u j) ω -
            ∫ ζ, I.η (u i) ζ * I.η (u j) ζ ∂I.P))) := by
  letI := I.mΩ
  letI := I.prob
  have hu : ∀ i : Fin r, IsR2Test (u i) :=
    fun i => ⟨hd.smooth i, hd.compactSupport i⟩
  have hwick :=
    s21l_wick_finiteRank (s21t4_product_eta_bundle I)
      (by norm_num : (0 : ℝ) ≤ 1)
      ha.1 ha.2.1 ha.2.2 c hu
  have heq : (fun ω : I.Ω => 2 * ((1 / 2 : ℝ) *
        ∑ i : Fin r, ∑ j : Fin r, c i j *
          (I.η (u i) ω * I.η (u j) ω -
            ∫ ζ, I.η (u i) ζ * I.η (u j) ζ ∂I.P))) =
      (fun ω : I.Ω => ∑ i : Fin r, ∑ j : Fin r, c i j *
        (I.η (u i) ω * I.η (u j) ω -
          ∫ ζ, I.η (u i) ζ * I.η (u j) ζ ∂I.P)) := by
    funext ω
    ring
  have hz : S94GSeq I.P (fun j ω => I.η (a j) ω) 1 :=
    s21l_gseq (s21t4_product_eta_bundle I) ha.1 ha.2.1
  have hT := s94WickL2.isWick hz hwick
  rw [heq]
  exact hT

end HRS.MS.R26T3
