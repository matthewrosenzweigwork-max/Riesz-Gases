import HRS.MS.S21H2_S03

/-!
# S21L S04 -- `r26t3_static_transport` (R26-T3.S04): a summable family of screened velocities

Contract of packet R26-T3.S04 (`origin/pro/fine-breakdown`), statement verbatim.  Route: S03 (`r26t3_transport_one`) produces ONE
constant `C` before the index `j` (each `q j` is `C_b^J` because the family is summable), then the velocities `v j` are chosen
independently with that `C`; the divergence equation and the derivative bound are exactly the two outputs of S03.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

open HRS HRS.Whole

theorem r26t3_static_transport {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1/2)
    (R : Trajectory p δ) (hγ : 0 < p.γ) (q : ℕ → Euc p.d → ℝ)
    (hq : IsSummableFeatureFamily (r26t3_J p.d) q) : Nonempty (StaticTransport R q) := by
  obtain ⟨C, hC0, hC⟩ := r26t3_transport_one hδ hδh R hγ
  choose v hv1 hv2 using fun j => hC (q j) (hq.1 j)
  exact ⟨⟨hq, v, C, hC0, hv1, hv2⟩⟩

end HRS.MS.R26T3
