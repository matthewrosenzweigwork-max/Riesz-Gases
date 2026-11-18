import HRS.MS.SA12X5D5C

/-!
# S.A.12 X5 D5E: linearity of `perNonlocal` in the density `μ`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x5_perNonlocal_sub_mu {L : ℝ} (hL : 0 < L) {γ : Euc d → ℝ} (hγ : LocallyIntegrable γ volume)
    (hγp : ∀ (x : Euc d) (k : Fin d → ℤ), γ (x + L • latticePt k) = γ x) (M : Matrix (Fin d) (Fin d) ℝ)
    {μ μ' F : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ) (hμ' : ContDiff ℝ ∞ μ') (hF : ContDiff ℝ ∞ F)
    (hμp : ∀ (x : Euc d) (k : Fin d → ℤ), μ (x + L • latticePt k) = μ x)
    (hμp' : ∀ (x : Euc d) (k : Fin d → ℤ), μ' (x + L • latticePt k) = μ' x)
    (hFp : ∀ (x : Euc d) (k : Fin d → ℤ), F (x + L • latticePt k) = F x) (x : Euc d) :
    perNonlocal L γ M (fun y => μ y - μ' y) F x = perNonlocal L γ M μ F x - perNonlocal L γ M μ' F x := by
  unfold perNonlocal
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_sub]
  congr 1
  have hμμ : ContDiff ℝ ∞ (fun y => μ y - μ' y) := hμ.sub hμ'
  have hμμp : ∀ (x : Euc d) (k : Fin d → ℤ), (fun y => μ y - μ' y) (x + L • latticePt k) =
      (fun y => μ y - μ' y) x := fun x k => by simp only [hμp, hμp']
  rw [sa12x5_perNonlocal_term hL hγ hγp hμμ hF hμμp hFp i j x,
    sa12x5_perNonlocal_term hL hγ hγp hμ hF hμp hFp i j x,
    sa12x5_perNonlocal_term hL hγ hγp hμ' hF hμp' hFp i j x]
  have hDj := sa12y_D1_contDiff hF j
  have e1 : (fun y => (fun y => μ y - μ' y) y * HRS.MS.UniqT3.D1 j F y) =
      fun y => μ y * HRS.MS.UniqT3.D1 j F y - μ' y * HRS.MS.UniqT3.D1 j F y := by
    funext y; ring
  rw [e1, sa12x5_D1_sub (hμ.mul hDj) (hμ'.mul hDj) i]
  have hc1 : ContDiff ℝ ∞ (HRS.MS.UniqT3.D1 i (fun y => μ y * HRS.MS.UniqT3.D1 j F y)) :=
    sa12y_D1_contDiff (hμ.mul hDj) i
  have hc2 : ContDiff ℝ ∞ (HRS.MS.UniqT3.D1 i (fun y => μ' y * HRS.MS.UniqT3.D1 j F y)) :=
    sa12y_D1_contDiff (hμ'.mul hDj) i
  have hp1 : ∀ (x : Euc d) (k : Fin d → ℤ), HRS.MS.UniqT3.D1 i (fun y => μ y * HRS.MS.UniqT3.D1 j F y)
      (x + L • latticePt k) = HRS.MS.UniqT3.D1 i (fun y => μ y * HRS.MS.UniqT3.D1 j F y) x := fun x k =>
    sa12x5_D1_periodic (fun x k => by simp only [hμp, sa12x5_D1_periodic hFp j]) i x k
  have hp2 : ∀ (x : Euc d) (k : Fin d → ℤ), HRS.MS.UniqT3.D1 i (fun y => μ' y * HRS.MS.UniqT3.D1 j F y)
      (x + L • latticePt k) = HRS.MS.UniqT3.D1 i (fun y => μ' y * HRS.MS.UniqT3.D1 j F y) x := fun x k =>
    sa12x5_D1_periodic (fun x k => by simp only [hμp', sa12x5_D1_periodic hFp j]) i x k
  exact sa12x5_perConv_sub hL hγ hγp hc1.continuous hc2.continuous hp1 hp2 x

end HRS.MH.AdjointRd.Phase2SA12X5
