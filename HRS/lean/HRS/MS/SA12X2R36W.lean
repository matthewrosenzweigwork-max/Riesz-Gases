import HRS.MH.AdjRdE3R3

/-!
# S.A.12 R36 (SA12X2), part W: integration by parts onto the test function

For `φ ∈ C^1_c`, `G ∈ C^1_c` and `K` locally integrable, the classical pairing equals the weak one:
`∫ φ ∂_e (K ⋆ G) = -∫ ∂_e φ (K ⋆ G)`. This is the link between the classical R36 object and the
weak (kernel-side) pairings used by the near/far split.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12

variable {d : ℕ}

theorem sa12x2_ibp_conv_test {K : Euc d → ℝ} (hK : LocallyIntegrable K (volume : Measure (Euc d)))
    {φ G : Euc d → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hG : ContDiff ℝ 1 G) (hGc : HasCompactSupport G) (e : Euc d) :
    ∫ x, φ x * fderiv ℝ (fun x => ∫ y, K (x - y) * G y) x e =
      -∫ x, fderiv ℝ φ x e * ∫ y, K (x - y) * G y := by
  have hconv : ContDiff ℝ 1 (fun x => ∫ y, K (x - y) * G y) :=
    HRS.MH.AdjointRdP.r3_contDiff_conv hK hG hGc
  exact HRS.MH.AdjointRdP.r3_ibp_cs e hφ hconv hφc

end HRS.MH.AdjointRd.Phase2SA12
