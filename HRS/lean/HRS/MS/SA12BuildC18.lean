import HRS.MS.Ker1Aux6
import HRS.MH.AdjointRdDefs

/-!
# S.A.12 C18: the local form of the periodic Riesz kernel

`γ_L(u) = g(u) + c + L^{-s} q(u / L)` for `0 < |u| < δ L`, with a universal smooth `q`, `c = log L` for
`s = 0` and `c = 0` otherwise (from the implemented `Ker1` sources).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

-- BEGIN SA12.C18
theorem periodic_kernel_local (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ (δ : ℝ) (q : Euc d → ℝ), 0 < δ ∧ ContDiff ℝ ∞ q ∧ ∀ L : ℝ, 1 ≤ L →
      ∀ γ : Euc d → ℝ, HRS.Whole.AppendixALemmas.IsPeriodicRieszKernel d s L γ →
        ∃ c : ℝ, (s ≠ 0 → c = 0) ∧ ∀ u : Euc d, u ≠ 0 → ‖u‖ < δ * L →
          γ u = rieszKernel d s u + c + L ^ (-s) * q (L⁻¹ • u) := by
  obtain ⟨q, δ0, hδ0, hq, hloc⟩ := HRS.MS.Ker1.ker1_decomp hd hs0 hsd
  refine ⟨min δ0 (1 / 2), q, lt_min hδ0 (by norm_num), hq, fun L hL γ hγ => ?_⟩
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  refine ⟨if s = 0 then Real.log L else 0, fun hs => by simp [hs], fun u hu0 hu => ?_⟩
  have hu1 : ‖u‖ < δ0 * L := lt_of_lt_of_le hu (mul_le_mul_of_nonneg_right (min_le_left _ _) hL0.le)
  have hu2 : ‖u‖ ≤ L / 2 := by
    have : min δ0 (1 / 2) * L ≤ 1 / 2 * L :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hL0.le
    linarith
  have hoff := HRS.MS.Ker1.ker1_offLattice_of_half hL0 hu0 hu2
  have h1 : γ u = HRS.MS.Ker1.ker1_gam d s L u :=
    HRS.MS.Ker1.ker1_eq_gam hd hs0 hsd hL0 hγ u hoff
  have h2 := (HRS.MS.Ker1.ker1_gam_eventually hd hloc hL0 hu0 hu1).self_of_nhds
  rw [h1, h2]
-- END SA12.C18

end HRS.MH.AdjointRd.Phase2SA12Construction
