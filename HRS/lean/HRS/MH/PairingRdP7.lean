import HRS.MH.PairingRdDefs
import HRS.MH.DualityRdC1a
import HRS.Whole.Q09BAux2

/-!
# PairingRd packet PR7 (`pairKernel_pointwise_rd`): pointwise algebraic identity

Statement copied verbatim from `HRS/MH/PairingRdSpec.lean`. Route: `dc1a_inner_matVec_sum` and `dc1a_matVec_sub`
(`HRS/MH/DualityRdC1a.lean`) turn the inner product into a coordinate sum; the cases `‖x - y‖ ≤ 1/4` and `> 1/4`
are handled by `simp only` on `convInt`, then `Finset.sum_sub_distrib` and a termwise `ring`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MH.PairingRdP

open HRS HRS.Duality HRS.MH.PairingRd

variable {d N : ℕ}

/-- **PR7** `pairKernel_pointwise_rd` (proof). -/
theorem pairKernel_pointwise_rd (f : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (s : ℝ) (ρ : Euc d → ℝ) (x y : Euc d) :
    ρ y * pairKernelRdB f M s x y =
      (1 / 2 : ℝ) * (inner ℝ (Torus.matVec M.transpose (gradient f x))
          (convInt (Whole.rieszKernelGrad d s) ρ x y)
        - ∑ a : Fin d, (convInt (Whole.rieszKernelGrad d s) (psiRd f M ρ a) x y) a) := by
  by_cases hxy : x = y
  · subst hxy
    norm_num [pairKernelRdB, convInt, psiRd]
  · unfold pairKernelRdB
    rw [if_neg hxy, HRS.MH.DualityRd.dc1a_inner_matVec_sum, HRS.MH.DualityRd.dc1a_matVec_sub]
    by_cases hc : ‖x - y‖ ≤ 1 / 4
    · simp only [convInt, psiRd, hc, ↓reduceIte, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
        HRS.Whole.Q09B.q09b_inner_euc]
      rw [← Finset.sum_sub_distrib]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · simp only [convInt, psiRd, hc, ↓reduceIte, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
        HRS.Whole.Q09B.q09b_inner_euc]
      rw [← Finset.sum_sub_distrib]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

end HRS.MH.PairingRdP
