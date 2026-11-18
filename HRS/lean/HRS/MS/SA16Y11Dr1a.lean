import HRS.MS.SA16PForce6

/-!
# S.A.16 (SA16Y11) Dr1a: linearity of the force convolution `convGradConvW (rieszKernelGrad d s)` in the density

For `ρ1, ρ2` with the weighted bounds of `sa16p_phi_bound` (`‖ρ_i‖ ≤ A_i w`, `‖Dρ_i‖ ≤ A_i`), `0 ≤ s < d`:
`convGradConvW (rieszKernelGrad d s) (ρ1 - ρ2) x = convGradConvW .. ρ1 x - convGradConvW .. ρ2 x`.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16P
open HRS HRS.Whole HRS.Whole.AppendixA

section Dr1a
variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

theorem sa16y11_conv_sub (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ1 ρ2 : 𝔼 → ℝ} {A1 A2 : ℝ}
    (hρ1 : Differentiable ℝ ρ1) (hρ2 : Differentiable ℝ ρ2)
    (hw1 : ∀ y, ‖ρ1 y‖ ≤ A1 * sa16p_w d y) (hw2 : ∀ y, ‖ρ2 y‖ ≤ A2 * sa16p_w d y)
    (hd1 : ∀ y, ‖fderiv ℝ ρ1 y‖ ≤ A1) (hd2 : ∀ y, ‖fderiv ℝ ρ2 y‖ ≤ A2) (x : 𝔼) :
    convGradConvW (rieszKernelGrad d s) (fun y => ρ1 y - ρ2 y) x =
      convGradConvW (rieszKernelGrad d s) ρ1 x - convGradConvW (rieszKernelGrad d s) ρ2 x := by
  set Kf : Fin d → 𝔼 → ℝ := fun j z => rieszKernelGrad d s z j with hKf
  have hKe : ∀ j z, Kf j z = fderiv ℝ (rieszKernel d s) z (EuclideanSpace.single j 1) := fun j z => by
    simp only [hKf, rieszKernelGrad]; exact q09_gradient_apply _ _ _
  have hKm : ∀ j, Measurable (Kf j) := fun j => by
    have : Kf j = fun z => fderiv ℝ (rieszKernel d s) z (EuclideanSpace.single j 1) := funext (hKe j)
    rw [this]; exact measurable_fderiv_apply_const ℝ (rieszKernel d s) _
  have hKb : ∀ j, ∀ z, z ≠ 0 → |Kf j z| ≤ HRS.CZ.Hls.hlsg_c s * ‖z‖ ^ (-s - 1) := fun j z hz => by
    rw [hKe]; exact HRS.CZ.Hls.force_kernel_bound_coord hs0 hz j
  have hc : 0 ≤ HRS.CZ.Hls.hlsg_c s := HRS.CZ.Hls.hlsg_c_nonneg hs0
  have hint1 := fun j => (sa16p_phi_bound hd (hKm j) hc hs0 hsd (hKb j) hρ1 hw1 hd1 x).1
  have hint2 := fun j => (sa16p_phi_bound hd (hKm j) hc hs0 hsd (hKb j) hρ2 hw2 hd2 x).1
  have hlin : ∀ (K : 𝔼 → ℝ) (z : 𝔼), sa16p_phiI K (fun y => ρ1 y - ρ2 y) x z =
      sa16p_phiI K ρ1 x z - sa16p_phiI K ρ2 x z := by
    intro K z
    unfold sa16p_phiI
    by_cases h : ‖z‖ ≤ 1 / 4
    · simp only [if_pos h]; rw [← smul_sub]; congr 1; ring
    · simp only [if_neg h, sub_zero]; rw [← smul_sub]
  have hint3 : ∀ j, Integrable (sa16p_phiI (fun z => rieszKernelGrad d s z j) (fun y => ρ1 y - ρ2 y) x) volume :=
    fun j => by
      have := (hint1 j).sub (hint2 j)
      have e : sa16p_phiI (fun z => rieszKernelGrad d s z j) (fun y => ρ1 y - ρ2 y) x =
          sa16p_phiI (fun z => rieszKernelGrad d s z j) ρ1 x - sa16p_phiI (fun z => rieszKernelGrad d s z j) ρ2 x :=
        funext (hlin _)
      rw [e]; exact this
  rw [sa16p_conv_eq_phi _ _ x hint3, sa16p_conv_eq_phi _ _ x hint1, sa16p_conv_eq_phi _ _ x hint2,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← sub_smul]
  congr 1
  unfold sa16p_phiF
  rw [← integral_sub (hint1 j) (hint2 j)]
  exact integral_congr_ae (Eventually.of_forall fun z => hlin _ z)

end Dr1a

end HRS.Whole.AppendixA.Phase2SA16P

end
