import HRS.MS.SA12X3N1J
import HRS.MS.SA12K22

/-!
# S.A.12 N1/N2 (SA12X3), part K: N1 (uniform decay) and N2 (locally uniform convergence) of the boxed periodic nonlocal test term
-/

set_option autoImplicit false
set_option maxHeartbeats 25600000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd HRS.MS.ToriConv
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x3n_regMF_jets {s : ℝ} {r : ℕ} {Λ T : ℝ} {ρ : ℝ → Euc d → ℝ} (h : IsRegularMFRd s r Λ T ρ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ContDiff ℝ r (ρ t) ∧ ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j (ρ t) x‖ ≤ max Λ 0 := by
  obtain ⟨hmem, hsum, hle⟩ := (h.1 t ht)
  refine ⟨hmem.1, fun j hj x => ?_⟩
  have hbdd := hmem.2 j hj
  have hsingle : ‖iteratedFDeriv ℝ j (ρ t) x‖ ≤ ⨆ z, ‖iteratedFDeriv ℝ j (ρ t) z‖ := le_ciSup hbdd x
  have hsum_le : (⨆ z, ‖iteratedFDeriv ℝ j (ρ t) z‖) ≤ cbNorm r (ρ t) := by
    unfold cbNorm
    exact Finset.single_le_sum (f := fun j' => ⨆ z, ‖iteratedFDeriv ℝ j' (ρ t) z‖)
      (fun j' _ => Real.iSup_nonneg fun z => norm_nonneg _) (Finset.mem_range.2 (by omega))
  have := ENNReal.toReal_nonneg (a := weightedSupE r ((d : ℝ) + 3) (ρ t))
  linarith [le_max_left Λ 0]

theorem sa12x3n_norm_one_sub (f g : Euc d → ℝ) (x : Euc d) :
    ‖iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 g x‖ = ‖fderiv ℝ f x - fderiv ℝ g x‖ := by
  have h1 := tcv_iter_fderiv_sub_norm f g 0 x
  have h2 := tcv_iter_zero_sub_norm (fderiv ℝ f) (fderiv ℝ g) x
  rw [zero_add] at h1
  rw [← h1, h2]

end HRS.MH.AdjointRd.Phase2SA12Limit
