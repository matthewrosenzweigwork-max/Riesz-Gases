import HRS.MS.SA16PForce6
import HRS.MS.SA16Y10Bd3

/-!
# S.A.16 (SA16Y10) Fd1: the cancellation-convention force map `ρ ↦ convGradConvW (rieszKernelGrad d s) ρ` is linear on
weighted `C¹` densities
-/

set_option autoImplicit false

noncomputable section
open scoped ContDiff
open Filter MeasureTheory

namespace HRS.Whole.AppendixA.Phase2SA16P
open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma sa16y10_phiI_sub {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (K : 𝔼 → ℝ) (ρ₁ ρ₂ : 𝔼 → F) (x z : 𝔼) :
    sa16p_phiI K (fun y => ρ₁ y - ρ₂ y) x z = sa16p_phiI K ρ₁ x z - sa16p_phiI K ρ₂ x z := by
  unfold sa16p_phiI
  by_cases h : ‖z‖ ≤ 1 / 4
  · simp only [if_pos h]
    simp only [smul_sub]
    abel
  · simp only [if_neg h]
    simp [smul_sub]

theorem sa16y10_force_sub (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ₁ ρ₂ : 𝔼 → ℝ} {A₁ A₂ : ℝ}
    (h₁ : ContDiff ℝ 1 ρ₁) (h₂ : ContDiff ℝ 1 ρ₂) (hw₁ : ∀ y, ‖ρ₁ y‖ ≤ A₁ * sa16p_w d y)
    (hw₂ : ∀ y, ‖ρ₂ y‖ ≤ A₂ * sa16p_w d y) (hg₁ : ∀ y, ‖fderiv ℝ ρ₁ y‖ ≤ A₁) (hg₂ : ∀ y, ‖fderiv ℝ ρ₂ y‖ ≤ A₂) :
    convGradConvW (rieszKernelGrad d s) (fun y => ρ₁ y - ρ₂ y) =
      fun x => convGradConvW (rieszKernelGrad d s) ρ₁ x - convGradConvW (rieszKernelGrad d s) ρ₂ x := by
  set Kf : Fin d → 𝔼 → ℝ := fun j z => rieszKernelGrad d s z j with hKf
  have hKe : ∀ j z, Kf j z = fderiv ℝ (rieszKernel d s) z (EuclideanSpace.single j 1) := fun j z => by
    simp only [hKf, rieszKernelGrad]; exact q09_gradient_apply _ _ _
  have hKm : ∀ j, Measurable (Kf j) := fun j => by
    have : Kf j = fun z => fderiv ℝ (rieszKernel d s) z (EuclideanSpace.single j 1) := funext (hKe j)
    rw [this]; exact measurable_fderiv_apply_const ℝ (rieszKernel d s) _
  have hKb : ∀ j, ∀ z, z ≠ 0 → |Kf j z| ≤ HRS.CZ.Hls.hlsg_c s * ‖z‖ ^ (-s - 1) := fun j z hz => by
    rw [hKe]; exact HRS.CZ.Hls.force_kernel_bound_coord hs0 hz j
  have hc : 0 ≤ HRS.CZ.Hls.hlsg_c s := HRS.CZ.Hls.hlsg_c_nonneg hs0
  have hd₁ : Differentiable ℝ ρ₁ := h₁.differentiable (by norm_num)
  have hd₂ : Differentiable ℝ ρ₂ := h₂.differentiable (by norm_num)
  funext x
  have hi₁ := fun j => (sa16p_phi_bound hd (hKm j) hc hs0 hsd (hKb j) hd₁ hw₁ hg₁ x).1
  have hi₂ := fun j => (sa16p_phi_bound hd (hKm j) hc hs0 hsd (hKb j) hd₂ hw₂ hg₂ x).1
  have hi₁₂ : ∀ j, Integrable (sa16p_phiI (fun z => rieszKernelGrad d s z j) (fun y => ρ₁ y - ρ₂ y) x) volume := fun j => by
    have := (hi₁ j).sub (hi₂ j)
    refine this.congr (Eventually.of_forall fun z => ?_)
    exact (sa16y10_phiI_sub (Kf j) ρ₁ ρ₂ x z).symm
  rw [sa16p_conv_eq_phi _ _ x hi₁₂, sa16p_conv_eq_phi _ ρ₁ x hi₁, sa16p_conv_eq_phi _ ρ₂ x hi₂,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← sub_smul]
  congr 1
  unfold sa16p_phiF
  rw [← integral_sub (hi₁ j) (hi₂ j)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  exact sa16y10_phiI_sub (Kf j) ρ₁ ρ₂ x z

end HRS.Whole.AppendixA.Phase2SA16P

end
