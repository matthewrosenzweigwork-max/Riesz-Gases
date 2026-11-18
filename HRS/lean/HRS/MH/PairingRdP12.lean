import HRS.MH.PairingRdP6
import HRS.MH.DualityRdB1Aux
import HRS.MH.DualityRdC1a

/-!
# PairingRd packet PR12 (`phi_bounded_rd`): measurability and boundedness of `φ₁`, `φ₂`

Statement copied verbatim from `HRS/MH/PairingRdSpec.lean`. Route: `φ₁ x = ⟨∇f x, M (∇g * ρ)(x)⟩` is bounded by
`A (CM K_ρ)` (`abs_real_inner_le_norm`, `db1_grad_bound`, `db1_matVec_bound`); `φ₂ x = ∑_a (∇g * ψ_a)(x)_a` is bounded by
`∑_a K_a` (`dc1a_abs_sum_le'`, `PiLp.norm_apply_le`). Measurability: PR6 (`measurable_conv_rd`) for every convolution,
`db1_gradient_continuous`, `db1_matVec_continuous`, `Measurable.inner`, `Finset.measurable_sum`.
The hypotheses `hKρ`, `hKψ` (uniform bounds of the convolutions) are used for the bounds.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MH.PairingRdP

open HRS HRS.Duality HRS.MH.PairingRd

variable {d N : ℕ}

/-- **PR12** `phi_bounded_rd` (proof). -/
theorem phi_bounded_rd {s : ℝ} (M : Matrix (Fin d) (Fin d) ℝ) {f : Euc d → ℝ} (hf : MemCb 2 f) {ρ : Euc d → ℝ}
    (hρm : Measurable ρ)
    (hKρ : ∃ K : ℝ, ∀ x, ‖Whole.convGradConvW (Whole.rieszKernelGrad d s) ρ x‖ ≤ K)
    (hKψ : ∀ a : Fin d, ∃ K : ℝ, ∀ x, ‖Whole.convGradConvW (Whole.rieszKernelGrad d s) (psiRd f M ρ a) x‖ ≤ K) :
    Measurable (fun x => inner ℝ (gradient f x)
        (Torus.matVec M (Whole.convGradConvW (Whole.rieszKernelGrad d s) ρ x))) ∧
      Measurable (divConvBRd f M s ρ) ∧
      ∃ K : ℝ, ∀ x, |inner ℝ (gradient f x)
          (Torus.matVec M (Whole.convGradConvW (Whole.rieszKernelGrad d s) ρ x))| ≤ K ∧
        |divConvBRd f M s ρ x| ≤ K := by
  have hcf : ContDiff ℝ 2 f := hf.1
  have hg : Continuous (gradient f) := HRS.MH.DualityRd.db1_gradient_continuous hcf
  have hmat : Continuous (Torus.matVec M : Euc d → Euc d) := HRS.MH.DualityRd.db1_matVec_continuous M
  have hconv : Measurable (fun x => Whole.convGradConvW (Whole.rieszKernelGrad d s) ρ x) :=
    measurable_conv_rd hρm
  have hψm : ∀ a : Fin d, Measurable (psiRd f M ρ a) := fun a => by
    have hc : Continuous (fun y => Torus.matVec M.transpose (gradient f y) a) :=
      (EuclideanSpace.proj a : Euc d →L[ℝ] ℝ).continuous.comp
        ((HRS.MH.DualityRd.db1_matVec_continuous M.transpose).comp hg)
    exact hρm.mul hc.measurable
  have hcoord : ∀ a : Fin d, Measurable
      (fun x => Whole.convGradConvW (Whole.rieszKernelGrad d s) (psiRd f M ρ a) x a) := fun a =>
    (EuclideanSpace.proj a : Euc d →L[ℝ] ℝ).continuous.measurable.comp (measurable_conv_rd (hψm a))
  have hφ1m : Measurable (fun x => inner ℝ (gradient f x)
      (Torus.matVec M (Whole.convGradConvW (Whole.rieszKernelGrad d s) ρ x))) :=
    hg.measurable.inner (hmat.measurable.comp hconv)
  have hφ2m : Measurable (divConvBRd f M s ρ) := by
    unfold divConvBRd
    exact Finset.measurable_sum _ fun a _ => hcoord a
  obtain ⟨Kρ, hKρ'⟩ := hKρ
  choose Kψ hKψ' using hKψ
  obtain ⟨A, hA0, hA⟩ := HRS.MH.DualityRd.db1_grad_bound hf
  obtain ⟨CM, hCM0, hCM⟩ := HRS.MH.DualityRd.db1_matVec_bound M
  have h1 : ∀ x, |inner ℝ (gradient f x)
      (Torus.matVec M (Whole.convGradConvW (Whole.rieszKernelGrad d s) ρ x))| ≤ A * (CM * max Kρ 0) := by
    intro x
    refine (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_mul (hA x) ((hCM _).trans (mul_le_mul_of_nonneg_left
      ((hKρ' x).trans (le_max_left _ _)) hCM0)) (norm_nonneg _) hA0
  have h2 : ∀ x, |divConvBRd f M s ρ x| ≤ ∑ a : Fin d, max (Kψ a) 0 := by
    intro x
    unfold divConvBRd
    refine HRS.MH.DualityRd.dc1a_abs_sum_le' Finset.univ
      (fun a => Whole.convGradConvW (Whole.rieszKernelGrad d s) (psiRd f M ρ a) x a)
      (fun a => max (Kψ a) 0) fun a _ => ?_
    have hc := PiLp.norm_apply_le (Whole.convGradConvW (Whole.rieszKernelGrad d s) (psiRd f M ρ a) x) a
    rw [Real.norm_eq_abs] at hc
    exact hc.trans ((hKψ' a x).trans (le_max_left _ _))
  refine ⟨hφ1m, hφ2m, max (A * (CM * max Kρ 0)) (∑ a : Fin d, max (Kψ a) 0), fun x => ⟨?_, ?_⟩⟩
  · exact (h1 x).trans (le_max_left _ _)
  · exact (h2 x).trans (le_max_right _ _)

end HRS.MH.PairingRdP
