import HRS.MS.SA12X5D5B
import HRS.MS.SA12BuildC20

/-!
# S.A.12 X5 D5C: linearity of `perNonlocal` in the function `F`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x5_perConv_sub {L : ℝ} (hL : 0 < L) {γ : Euc d → ℝ} (hγ : LocallyIntegrable γ volume)
    (hγp : ∀ (x : Euc d) (k : Fin d → ℤ), γ (x + L • latticePt k) = γ x) {h₁ h₂ : Euc d → ℝ}
    (hc₁ : Continuous h₁) (hc₂ : Continuous h₂)
    (hp₁ : ∀ (x : Euc d) (k : Fin d → ℤ), h₁ (x + L • latticePt k) = h₁ x)
    (hp₂ : ∀ (x : Euc d) (k : Fin d → ℤ), h₂ (x + L • latticePt k) = h₂ x) (x : Euc d) :
    perConv L γ (fun y => h₁ y - h₂ y) x = perConv L γ h₁ x - perConv L γ h₂ x := by
  have hp : ∀ (x : Euc d) (k : Fin d → ℤ), (fun y => h₁ y - h₂ y) (x + L • latticePt k) =
      (fun y => h₁ y - h₂ y) x := fun x k => by simp only [hp₁, hp₂]
  rw [sa12c20_perConv_eq L hL γ _ hγp hp, sa12c20_perConv_eq L hL γ h₁ hγp hp₁,
    sa12c20_perConv_eq L hL γ h₂ hγp hp₂, ← integral_sub]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [mul_sub]
  · obtain ⟨B, hB⟩ := sa12v_bdd L hL h₁ hc₁ hp₁
    exact (sa12c20_integrableOn_neg hγ L).mul_bdd (c := B)
      (hc₁.comp (continuous_const.add continuous_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hB _)
  · obtain ⟨B, hB⟩ := sa12v_bdd L hL h₂ hc₂ hp₂
    exact (sa12c20_integrableOn_neg hγ L).mul_bdd (c := B)
      (hc₂.comp (continuous_const.add continuous_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hB _)

theorem sa12x5_D1_sub {f g : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (i : Fin d) :
    HRS.MS.UniqT3.D1 i (fun y => f y - g y) = fun y => HRS.MS.UniqT3.D1 i f y - HRS.MS.UniqT3.D1 i g y := by
  funext y
  unfold HRS.MS.UniqT3.D1
  have hfd : DifferentiableAt ℝ f y := (hf.differentiable (by simp)) y
  have hgd : DifferentiableAt ℝ g y := (hg.differentiable (by simp)) y
  have h : HasFDerivAt (fun y => f y - g y) (fderiv ℝ f y - fderiv ℝ g y) y :=
    hfd.hasFDerivAt.sub hgd.hasFDerivAt
  rw [h.fderiv]
  rfl

/-- `perNonlocal` is the periodic convolution of `∂_i(μ ∂_jF)`. -/
theorem sa12x5_perNonlocal_term {L : ℝ} (hL : 0 < L) {γ : Euc d → ℝ} (hγ : LocallyIntegrable γ volume)
    (hγp : ∀ (x : Euc d) (k : Fin d → ℤ), γ (x + L • latticePt k) = γ x) {μ F : Euc d → ℝ}
    (hμ : ContDiff ℝ ∞ μ) (hF : ContDiff ℝ ∞ F)
    (hμp : ∀ (x : Euc d) (k : Fin d → ℤ), μ (x + L • latticePt k) = μ x)
    (hFp : ∀ (x : Euc d) (k : Fin d → ℤ), F (x + L • latticePt k) = F x) (i j : Fin d) (x : Euc d) :
    fderiv ℝ (perConv L γ (fun y => μ y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ)))) x
        (EuclideanSpace.single i (1 : ℝ)) =
      perConv L γ (HRS.MS.UniqT3.D1 i (fun y => μ y * HRS.MS.UniqT3.D1 j F y)) x := by
  have hDj : ContDiff ℝ ∞ (HRS.MS.UniqT3.D1 j F) := sa12y_D1_contDiff hF j
  have hh : ContDiff ℝ ∞ (fun y => μ y * HRS.MS.UniqT3.D1 j F y) := hμ.mul hDj
  have hhp : ∀ (x : Euc d) (k : Fin d → ℤ), (fun y => μ y * HRS.MS.UniqT3.D1 j F y) (x + L • latticePt k) =
      (fun y => μ y * HRS.MS.UniqT3.D1 j F y) x := fun x k => by
    simp only [hμp, sa12x5_D1_periodic hFp j]
  exact periodic_convolution_derivative L hL γ _ hγ hγp (hh.of_le (by simp)) hhp i x

theorem sa12x5_perNonlocal_sub {L : ℝ} (hL : 0 < L) {γ : Euc d → ℝ} (hγ : LocallyIntegrable γ volume)
    (hγp : ∀ (x : Euc d) (k : Fin d → ℤ), γ (x + L • latticePt k) = γ x) (M : Matrix (Fin d) (Fin d) ℝ)
    {μ F F' : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ) (hF : ContDiff ℝ ∞ F) (hF' : ContDiff ℝ ∞ F')
    (hμp : ∀ (x : Euc d) (k : Fin d → ℤ), μ (x + L • latticePt k) = μ x)
    (hFp : ∀ (x : Euc d) (k : Fin d → ℤ), F (x + L • latticePt k) = F x)
    (hFp' : ∀ (x : Euc d) (k : Fin d → ℤ), F' (x + L • latticePt k) = F' x) (x : Euc d) :
    perNonlocal L γ M μ (fun y => F y - F' y) x = perNonlocal L γ M μ F x - perNonlocal L γ M μ F' x := by
  unfold perNonlocal
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_sub]
  congr 1
  have hFF : ContDiff ℝ ∞ (fun y => F y - F' y) := hF.sub hF'
  have hFFp : ∀ (x : Euc d) (k : Fin d → ℤ), (fun y => F y - F' y) (x + L • latticePt k) =
      (fun y => F y - F' y) x := fun x k => by simp only [hFp, hFp']
  rw [sa12x5_perNonlocal_term hL hγ hγp hμ hFF hμp hFFp i j x,
    sa12x5_perNonlocal_term hL hγ hγp hμ hF hμp hFp i j x,
    sa12x5_perNonlocal_term hL hγ hγp hμ hF' hμp hFp' i j x]
  have hDj := sa12y_D1_contDiff hF j
  have hDj' := sa12y_D1_contDiff hF' j
  have e1 : (fun y => μ y * HRS.MS.UniqT3.D1 j (fun y => F y - F' y) y) =
      fun y => μ y * HRS.MS.UniqT3.D1 j F y - μ y * HRS.MS.UniqT3.D1 j F' y := by
    funext y
    rw [sa12x5_D1_sub hF hF' j]
    ring
  rw [e1, sa12x5_D1_sub (hμ.mul hDj) (hμ.mul hDj') i]
  have hc1 : ContDiff ℝ ∞ (HRS.MS.UniqT3.D1 i (fun y => μ y * HRS.MS.UniqT3.D1 j F y)) :=
    sa12y_D1_contDiff (hμ.mul hDj) i
  have hc2 : ContDiff ℝ ∞ (HRS.MS.UniqT3.D1 i (fun y => μ y * HRS.MS.UniqT3.D1 j F' y)) :=
    sa12y_D1_contDiff (hμ.mul hDj') i
  have hp1 : ∀ (x : Euc d) (k : Fin d → ℤ), HRS.MS.UniqT3.D1 i (fun y => μ y * HRS.MS.UniqT3.D1 j F y)
      (x + L • latticePt k) = HRS.MS.UniqT3.D1 i (fun y => μ y * HRS.MS.UniqT3.D1 j F y) x := fun x k =>
    sa12x5_D1_periodic (fun x k => by simp only [hμp, sa12x5_D1_periodic hFp j]) i x k
  have hp2 : ∀ (x : Euc d) (k : Fin d → ℤ), HRS.MS.UniqT3.D1 i (fun y => μ y * HRS.MS.UniqT3.D1 j F' y)
      (x + L • latticePt k) = HRS.MS.UniqT3.D1 i (fun y => μ y * HRS.MS.UniqT3.D1 j F' y) x := fun x k =>
    sa12x5_D1_periodic (fun x k => by simp only [hμp, sa12x5_D1_periodic hFp' j]) i x k
  exact sa12x5_perConv_sub hL hγ hγp hc1.continuous hc2.continuous hp1 hp2 x

end HRS.MH.AdjointRd.Phase2SA12X5
