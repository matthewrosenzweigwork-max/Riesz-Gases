import HRS.MH.PairingRdP7
import HRS.MH.DualityRdC1a

/-!
# PairingRd packet PR8 (`integral_pairKernel_eq_rd`): the fibre identity `∫ K(x,y) dμ(y) = ½ (φ₁ - φ₂)(x)`

Statement copied verbatim from `HRS/MH/PairingRdSpec.lean`. Route: `dc1a_integral_withDensity` turns the `μ`-integral into
`∫ ρ y * K(x,y)`, the pointwise identity `pairKernel_pointwise_rd` (PR7) is integrated termwise (`integral_sub`,
`integral_inner`, `integral_finsetSum`, `ContinuousLinearMap.integral_comp_comm` with `EuclideanSpace.proj a`), and
`dc1a_inner_matVec` moves `Mᵀ` back. Template: `HRS.Duality.integral_pairKernel_eq` (`HRS/Duality/PairingExpansion.lean:546`)
without the change of variables.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MH.PairingRdP

open HRS HRS.Duality HRS.MH.PairingRd

variable {d N : ℕ}

/-- **PR8** `integral_pairKernel_eq_rd` (proof). -/
theorem integral_pairKernel_eq_rd {s : ℝ} (M : Matrix (Fin d) (Fin d) ℝ) {f : Euc d → ℝ} {ρ : Euc d → ℝ}
    (hρ : Whole.IsProbDensity ρ) (x : Euc d)
    (hKρ : Integrable (convInt (Whole.rieszKernelGrad d s) ρ x))
    (hKψ : ∀ a : Fin d, Integrable (convInt (Whole.rieszKernelGrad d s) (psiRd f M ρ a) x)) :
    ∫ y, pairKernelRdB f M s x y ∂(Whole.withDensityReal ρ) =
      (1 / 2 : ℝ) * (inner ℝ (gradient f x)
        (Torus.matVec M (Whole.convGradConvW (Whole.rieszKernelGrad d s) ρ x)) - divConvBRd f M s ρ x) := by
  have step1 : ∫ y, pairKernelRdB f M s x y ∂(Whole.withDensityReal ρ)
      = ∫ y, ρ y * pairKernelRdB f M s x y :=
    HRS.MH.DualityRd.dc1a_integral_withDensity hρ.measurable hρ.nonneg (fun y => pairKernelRdB f M s x y)
  have hI1 : Integrable (fun y => inner ℝ (Torus.matVec M.transpose (gradient f x))
      (convInt (Whole.rieszKernelGrad d s) ρ x y)) :=
    ContinuousLinearMap.integrable_comp (innerSL ℝ (Torus.matVec M.transpose (gradient f x))) hKρ
  have hI2 : ∀ a : Fin d, Integrable (fun y => (convInt (Whole.rieszKernelGrad d s) (psiRd f M ρ a) x y) a) :=
    fun a => ContinuousLinearMap.integrable_comp (EuclideanSpace.proj a : Euc d →L[ℝ] ℝ) (hKψ a)
  have hI3 : Integrable (fun y => ∑ a : Fin d, (convInt (Whole.rieszKernelGrad d s) (psiRd f M ρ a) x y) a) :=
    integrable_finsetSum _ fun a _ => hI2 a
  have hpt : (fun y => ρ y * pairKernelRdB f M s x y) = fun y => (1 / 2 : ℝ) *
      (inner ℝ (Torus.matVec M.transpose (gradient f x)) (convInt (Whole.rieszKernelGrad d s) ρ x y)
        - ∑ a : Fin d, (convInt (Whole.rieszKernelGrad d s) (psiRd f M ρ a) x y) a) :=
    funext fun y => pairKernel_pointwise_rd f M s ρ x y
  have hA : ∫ y, inner ℝ (Torus.matVec M.transpose (gradient f x)) (convInt (Whole.rieszKernelGrad d s) ρ x y)
      = inner ℝ (Torus.matVec M.transpose (gradient f x)) (Whole.convGradConvW (Whole.rieszKernelGrad d s) ρ x) :=
    integral_inner hKρ _
  have hB : ∫ y, ∑ a : Fin d, (convInt (Whole.rieszKernelGrad d s) (psiRd f M ρ a) x y) a
      = ∑ a : Fin d, (Whole.convGradConvW (Whole.rieszKernelGrad d s) (psiRd f M ρ a) x) a := by
    rw [integral_finsetSum _ fun a _ => hI2 a]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj a : Euc d →L[ℝ] ℝ) (hKψ a)
  rw [step1, hpt, integral_const_mul, integral_sub hI1 hI3, hA, hB, HRS.MH.DualityRd.dc1a_inner_matVec]
  rfl

end HRS.MH.PairingRdP
