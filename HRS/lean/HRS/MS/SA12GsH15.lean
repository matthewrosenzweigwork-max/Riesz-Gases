import HRS.Whole.AppendixAAdjoint
import HRS.PDE.ToolboxRd.Fourier

/-!
# S.A.12 H15: the Sobolev inner product is invariant under a.e. equality in its first slot
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Global

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

-- BEGIN SA12.H15
theorem sobolevInner_congr_ae (m : ℕ) (u v h : Euc d → ℝ) (huv : u =ᵐ[volume] v) :
    sobolevInnerRd m u h=sobolevInnerRd m v h := by
  unfold sobolevInnerRd HRS.PDE.ToolboxRd.symbolForm
  rw [HRS.PDE.ToolboxRd.FourierAux.fourierL2_congr_ae huv]
-- END SA12.H15

end HRS.MH.AdjointRd.Phase2SA12Global
