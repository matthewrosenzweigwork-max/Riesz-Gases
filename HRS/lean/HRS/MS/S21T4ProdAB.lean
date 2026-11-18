import HRS.MS.S21T4ProdAA
import HRS.MS.S21T4ProdK

/-! S13: uniform-in-particle-number approximation in probability for S9.1 kernels. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

/-- For the native S9.1 approximation the centered pair-energy differences vanish
in probability uniformly over all N ≥ 2. No absolute-continuity assumption is
added here: the reference measure enters only through its established
finite-rank approximation and L² properties. -/
theorem s21t4_round2_uniform_probability (s C B : ℝ)
    (hs : 2 * s < (d : ℝ)) (h : Euc d → Euc d → ℝ)
    (hh : MemLp (fun z : Euc d × Euc d => h z.1 z.2) 2 (μ.prod μ))
    (hsymm : ∀ x y, h x y = h y x)
    (hj : ℕ → Euc d → Euc d → ℝ)
    (hA : IsRound2Approx s C B μ h hj)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ j in atTop, ∀ (N : ℕ), 2 ≤ N →
      (Measure.pi fun _ : Fin N => μ).real
        {X : EucConfig d N | ε ^ 2 ≤
          ((N : ℝ) * (pairEnergy (hj j) X μ - pairEnergy h X μ) +
            (1 / 2) * ∫ x, ∫ y, (hj j x y - h x y) ∂μ ∂μ) ^ 2} < δ := by
  choose m c u hdata heq using hA.finiteRank
  have hjmem : ∀ j, MemLp (fun z : Euc d × Euc d => hj j z.1 z.2) 2
      (μ.prod μ) := by
    intro j
    rw [heq j]
    exact s21t4_finite_rank_memLp (c j) (u j) (hdata j)
  have hjs : ∀ j x y, hj j x y = hj j y x := by
    intro j x y
    rw [heq j]
    exact s21t4_finite_rank_symmetric (c j) (u j) (hdata j) x y
  have hL := s21t4_round2_approx_integral_sq_zero s C B hs h hh hj hA
  have hlim : ∀ᶠ j in atTop,
      (∫ z : Euc d × Euc d,
        (hj j z.1 z.2 - h z.1 z.2) ^ 2 ∂(μ.prod μ)) < δ * ε ^ 2 / 18 :=
    hL.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hlim] with j hjerr N hN
  have ht := s21t4_s13_approx_tail μ hN (hj j) h (hjmem j) hh (hjs j) hsymm ε
  nlinarith [sq_nonneg ε]

end HRS.MS.R26T3
