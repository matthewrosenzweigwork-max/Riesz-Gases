import HRS.MS.GenPathAux32
import HRS.MS.SuppU9

/-!
# S5.6 packet P6e: the remainder `R = Ξ - A(k₀) - 𝒯M` is controlled by the interaction energy
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.GenPath

open HRS.Whole HRS.MP.RdRem

variable {d : ℕ}

theorem s56_enorm_eq_l2NormE {m : ℝ} (u : OscDual d m) :
    ‖u‖ₑ = l2NormE (fun α => OscDual.coord u α) := by
  unfold l2NormE
  have hs := OscDual.coord_sq_summable' u
  have h1 : ∑' α, ENNReal.ofReal (OscDual.coord u α ^ 2) = ENNReal.ofReal (∑' α, OscDual.coord u α ^ 2) :=
    (ENNReal.ofReal_tsum_of_nonneg (fun α => sq_nonneg _) hs).symm
  rw [h1, ENNReal.ofReal_rpow_of_nonneg (tsum_nonneg fun α => sq_nonneg _) (by norm_num),
    ← Real.sqrt_eq_rpow, ← OscDual.norm_eq_coord, ofReal_norm]

end HRS.MS.GenPath
