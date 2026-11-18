import HRS.MS.Fp81S21WeightedRellich2
import HRS.MS.S21K2_W09B

/-!
The weighted chart norm is the square root of an ordered-jet weighted
`L²` energy (`s57pS`), rather than a weighted supremum norm.  W09 supplies
the local `L²` Rellich input for a finite family of compactly supported
derivative coordinates, provided the uniform Fourier-side `H¹` bounds have
been established.  This file packages its common-subsequence consequence
with the ordered-jet index used by the weighted charts.

The reduction from a bounded weighted chart ball, after multiplication by a
smooth cutoff, to the W09 hypotheses remains a separate step: it must prove
the derivative-coordinate `MemSobolev 1` and Fourier energy bounds from the
weighted `L²` jet bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.FixEq

/-- Indices for the ordered partial derivatives of orders at most `q`. -/
abbrev fp81s21_weightedRellich_JetIndex (q d : ℕ) :=
  Σ j : Fin (q + 1), (Fin j.1 → Fin d)

/-- A finite family of compactly supported local derivative coordinates
with uniform W09 bounds has one subsequence that is `L²`-Cauchy in every
ordered-jet coordinate.  In applications the coordinates are cutoff
derivatives; the W09 bounds are the analytic bridge from the weighted chart
ball to local Rellich compactness. -/
theorem fp81s21_weightedRellich_localJet_cauchy
    {d q : ℕ} {L K : ℝ} (hL : 0 ≤ L)
    (u : ℕ → fp81s21_weightedRellich_JetIndex q d → Euc d → ℝ)
    (hcont : ∀ n i, Continuous (u n i))
    (hcs : ∀ n i, HasCompactSupport (u n i))
    (hsupp : ∀ n i, tsupport (u n i) ⊆ Metric.closedBall 0 L)
    (hL2 : ∀ n i, ∫ x, (u n i x) ^ 2 ≤ K)
    (hs : ∀ n i, HRS.PDE.ToolboxRd.MemSobolev (1 : ℝ) (u n i))
    (hK : ∀ n i, ∫ ξ,
      (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (1 : ℝ) *
        ‖HRS.PDE.ToolboxRd.fourierL2 (u n i) ξ‖ ^ 2 ≤ K) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ i, ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
        ∫ x, (u (σ m) i x - u (σ n) i x) ^ 2 < ε := by
  classical
  obtain ⟨σ, hσ, hc⟩ := HRS.MS.R26T3.s21k2_w09_cauchy_subseq_fin
    (d := d) hL Finset.univ u hcont hcs hsupp hL2 hs hK
  refine ⟨σ, hσ, ?_⟩
  intro i ε hε
  exact hc i (Finset.mem_univ i) ε hε

#print axioms HRS.Fp81.S21.fp81s21_weightedRellich_localJet_cauchy

end HRS.Fp81.S21
