import HRS.MS.SA12X5D5E

/-!
# S.A.12 X5 F1: `perConv` and `perNonlocal` of smooth periodic data are `C^∞`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x5_perConv_smooth_nat {L : ℝ} (hL : 0 < L) {γ : Euc d → ℝ} (hγ : LocallyIntegrable γ volume)
    (hγp : ∀ (x : Euc d) (k : Fin d → ℤ), γ (x + L • latticePt k) = γ x) (n : ℕ) :
    ∀ h : Euc d → ℝ, ContDiff ℝ ∞ h → (∀ (x : Euc d) (k : Fin d → ℤ), h (x + L • latticePt k) = h x) →
      ContDiff ℝ (n : WithTop ℕ∞) (perConv L γ h) := by
  induction n with
  | zero =>
    intro h hh hhp
    have hfun : perConv L γ h = fun x => ∫ z in periodBox d L, γ (-z) * h (x + z) :=
      funext fun x => sa12c20_perConv_eq L hL γ h hγp hhp x
    rw [hfun]
    have := fun x => (sa12c20_hasFDerivAt L hγ (hh.of_le (by simp)) x).differentiableAt
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun x => (this x).continuousAt)
  | succ n ih =>
    intro h hh hhp
    have hfun : perConv L γ h = fun x => ∫ z in periodBox d L, γ (-z) * h (x + z) :=
      funext fun x => sa12c20_perConv_eq L hL γ h hγp hhp x
    refine contDiff_succ_iff_hasFDerivAt.2 ⟨fun x => ∑ i : Fin d,
      perConv L γ (HRS.MS.UniqT3.D1 i h) x • (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ), ?_, fun x => ?_⟩
    · refine ContDiff.sum fun i _ => ?_
      exact (ih _ (sa12y_D1_contDiff hh i) (sa12x5_D1_periodic hhp i)).smul contDiff_const
    · have hd := sa12c20_hasFDerivAt L hγ (hh.of_le (by simp)) x
      rw [← hfun] at hd
      have key : fderiv ℝ (perConv L γ h) x = ∑ i : Fin d,
          perConv L γ (HRS.MS.UniqT3.D1 i h) x • (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) := by
        refine ContinuousLinearMap.coe_injective ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis.ext fun i => ?_)
        simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe,
          ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
        rw [periodic_convolution_derivative L hL γ h hγ hγp (hh.of_le (by simp)) hhp i x]
        rw [Finset.sum_eq_single i]
        · simp [HRS.MS.UniqT3.D1]; rfl
        · intro j _ hji; simp [EuclideanSpace.single_apply, hji.symm]
        · simp
      show HasFDerivAt (perConv L γ h) (∑ i : Fin d,
          perConv L γ (HRS.MS.UniqT3.D1 i h) x • (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)) x
      rw [← key]
      exact hd.differentiableAt.hasFDerivAt

theorem sa12x5_perConv_smooth {L : ℝ} (hL : 0 < L) {γ : Euc d → ℝ} (hγ : LocallyIntegrable γ volume)
    (hγp : ∀ (x : Euc d) (k : Fin d → ℤ), γ (x + L • latticePt k) = γ x) {h : Euc d → ℝ}
    (hh : ContDiff ℝ ∞ h) (hhp : ∀ (x : Euc d) (k : Fin d → ℤ), h (x + L • latticePt k) = h x) :
    ContDiff ℝ ∞ (perConv L γ h) :=
  contDiff_infty.2 fun n => sa12x5_perConv_smooth_nat hL hγ hγp n h hh hhp

theorem sa12x5_perNonlocal_smooth {L : ℝ} (hL : 0 < L) {γ : Euc d → ℝ} (hγ : LocallyIntegrable γ volume)
    (hγp : ∀ (x : Euc d) (k : Fin d → ℤ), γ (x + L • latticePt k) = γ x) (M : Matrix (Fin d) (Fin d) ℝ)
    {μ F : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ) (hF : ContDiff ℝ ∞ F)
    (hμp : ∀ (x : Euc d) (k : Fin d → ℤ), μ (x + L • latticePt k) = μ x)
    (hFp : ∀ (x : Euc d) (k : Fin d → ℤ), F (x + L • latticePt k) = F x) :
    ContDiff ℝ ∞ (fun x => perNonlocal L γ M μ F x) := by
  have e : (fun x => perNonlocal L γ M μ F x) = fun x => ∑ i : Fin d, ∑ j : Fin d, M j i *
      perConv L γ (HRS.MS.UniqT3.D1 i (fun y => μ y * HRS.MS.UniqT3.D1 j F y)) x := by
    funext x
    unfold perNonlocal
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [sa12x5_perNonlocal_term hL hγ hγp hμ hF hμp hFp i j x]
  rw [e]
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => contDiff_const.mul ?_
  have hDj := sa12y_D1_contDiff hF j
  exact sa12x5_perConv_smooth hL hγ hγp (sa12y_D1_contDiff (hμ.mul hDj) i)
    (sa12x5_D1_periodic (fun x k => by simp only [hμp, sa12x5_D1_periodic hFp j]) i)

end HRS.MH.AdjointRd.Phase2SA12X5
