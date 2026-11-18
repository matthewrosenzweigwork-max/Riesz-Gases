import HRS.MS.Fp81S21WeightedRellich4
import HRS.MS.S21K2_W09E

/-!
The weighted chart norm is the square root of an ordered-jet weighted `L²`
energy, with terms `⟨x⟩^(-2 P) |∂^i f|²`.  The source/target pair is
`(q + 2, P)` and `(q, P + 2)`: lowering the jet order by two and raising the
weight parameter by two gives a fourth-power spatial weight gain.

W09C supplies the Fourier `H¹` bridge for each smooth compactly supported
coordinate, and W09E packages the resulting local `L²` Rellich argument for
functions supported in one fixed ball.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.FixEq

/-- Fourier-side `H¹` energy is bounded by the physical `L²` energy of a
compactly supported smooth function and its first coordinate derivatives.
The equality underlying this estimate is the Plancherel identity proved in
W09C from the Fourier derivative formula. -/
theorem fp81s21_weightedRellich_fourierH1_bound
    {d : ℕ} {u : Euc d → ℝ}
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hcs : HasCompactSupport u) {K : ℝ}
    (hL2 : ∫ x, u x ^ 2 ≤ K)
    (hgrad : ∀ k : Fin d,
      ∫ x, (fderiv ℝ u x (EuclideanSpace.single k (1 : ℝ))) ^ 2 ≤ K) :
    HRS.PDE.ToolboxRd.MemSobolev (1 : ℝ) u ∧
      ∫ ξ, (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (1 : ℝ) *
        ‖HRS.PDE.ToolboxRd.fourierL2 u ξ‖ ^ 2 ≤ ((d : ℝ) + 1) * K := by
  obtain ⟨hmem, hid⟩ := HRS.MS.R26T3.s21k2_w09_sobolev hu hcs
  refine ⟨hmem, ?_⟩
  rw [hid]
  have hsum : ∑ k : Fin d,
      ∫ x, (fderiv ℝ u x (EuclideanSpace.single k (1 : ℝ))) ^ 2 ≤ (d : ℝ) * K := by
    calc
      _ ≤ ∑ _k : Fin d, K := Finset.sum_le_sum fun k _ => hgrad k
      _ = (d : ℝ) * K := by simp
  linarith

/-- A uniformly bounded ball of weighted tests with one common compact
support has a subsequence Cauchy in the weaker weighted ordered-jet norm.
This is the local Rellich conclusion used after fixing a spatial cutoff. -/
theorem fp81s21_weightedRellich_localSupport_cauchy
    (d q : ℕ) (P L : ℝ) (hL : 0 < L)
    (f : ℕ → Euc d → ℝ)
    (hreg : ∀ n, IsR2Test (f n))
    (hsupp : ∀ n, tsupport (f n) ⊆ Metric.closedBall 0 L)
    (hE : ∀ n, weightedSobolevE (q + 2) P (f n) ≤ 1) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      CauchySeq (fun n => HRS.MS.R26T3.r26t3_jet q (P + 2) (f (σ n))) := by
  obtain ⟨σ, hσ, hc⟩ := HRS.MS.R26T3.r26t3_local_jet_compact
    d (q + 2) P L (by omega) hL f hreg hsupp hE
  have hq : q + 2 - 2 = q := by omega
  rw [hq] at hc
  exact ⟨σ, hσ, hc⟩

#print axioms HRS.Fp81.S21.fp81s21_weightedRellich_fourierH1_bound
#print axioms HRS.Fp81.S21.fp81s21_weightedRellich_localSupport_cauchy

end HRS.Fp81.S21
