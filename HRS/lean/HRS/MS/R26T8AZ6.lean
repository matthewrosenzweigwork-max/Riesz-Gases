import HRS.MS.R26T8AZ5d3

/-!
# S8.2 T8A Z6 (= P07 same-k): `r26t8a_raw_newton_bound_same`
The Pro P07 contract verbatim for every `σ < d` (no `0 ≤ σ`, no extra regularity): `Conormal k b M σ A F` implies integrability of the Newton integrand and
`Conormal k (b+1) M (σ-2) (C A) (rawNewton ν χ F)`.  Proof: Z5d3 with `N = ⌈-σ⌉` (the derivative induction replaces the Taylor split).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_raw_newton_bound_same (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (nu M sigma : ℝ) (hnu : 0 < nu) (hM : 0 ≤ M)
    (hsd : sigma < d) (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A → Conormal k b M sigma A F →
      (∀ x y, x ≠ y → Integrable (fun z => newtonKernel d nu (x - y - z) * chi z *
        midPair F ((1 / 2 : ℝ) • (x + y)) z)) ∧
      Conormal k (b + 1) M (sigma - 2) (C * A) (rawNewton nu chi F) := by
  refine r26t8a_Z5d3_same_k hd nu hnu hchi ⌈-sigma⌉₊ k b M sigma hM ?_ hsd
  have := Nat.le_ceil (-sigma)
  linarith

end HRS.MS.R26T8A
