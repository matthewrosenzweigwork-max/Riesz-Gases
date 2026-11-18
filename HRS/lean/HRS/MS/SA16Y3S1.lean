import HRS.MS.SA16SNl4

/-!
# S.A.16 (SA16Y3) S1: the sub-case nonlocal operator on `C_c^∞` (SA16S P8 item S1)

`sa16y3_G_Jcc_wrep`: if `SA16SubOp` admits a realisation, then `sa16so_G` acts on `Jcc φ` by the nonlocal operator
`eucNonlocal s M μ φ` in the zeroth component.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

theorem sa16y3_G_Jcc_wrep {d m : ℕ} {p : ℝ} [Fact (2 ≤ p)] (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ)
    (μ : Euc d → ℝ) (hT : ∃ T, SA16SubOp d m p s M μ T) (φ : ccSub d) :
    wrep d m p (sa16so_G d m p s M μ (sa16r_Jcc d m p φ)) =ᵐ[volume]
      HRS.MH.AdjointRd.eucNonlocal s M μ φ.1 := by
  unfold sa16so_G
  rw [dif_pos hT]
  exact Classical.choose_spec hT φ

end HRS.Whole.AppendixA.Phase2SA16R
