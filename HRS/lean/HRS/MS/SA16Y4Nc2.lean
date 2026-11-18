import HRS.MS.SA16Y4Wk2
import HRS.MS.SA16SNl4
import HRS.MS.AdjRdWeakTerm

/-!
# S.A.16 (SA16Y4) Nc2: the nonlocal pairing with the derivative on the solution

`sa16y4_nl_ibp`: for a `C^1` coefficient `a = C.ρ τ'`, `T` the nonlocal operator on `W^{m,p}` (`SA16SubOp`), `m ≥ 1`, and `ψ ∈ C_c^∞`:
`ℓ_ψ(T y) = -∑_{i,j} M_{ji} ∫ y_{e_j} (a · κ_i)`, `κ_i = ∂_i (g ⋆ ψ) = kernelConvDeriv d s i ψ`,
provided `a κ_i ∈ L^{p'}`.  Only `a` itself (no derivative of `a`) enters the right-hand side, so convergence of the
coefficients in `C^0` with a common decay bound suffices for the limit.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Nc2
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16y4_nlTest_eq (C : WholeCoeff d) (τ' : ℝ) (hs0 : 0 ≤ C.s) (hsd : C.s < d)
    {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ) (x : EuclideanSpace ℝ (Fin d)) :
    nonlocalTestRd C τ' ψ x = ∑ i : Fin d, ∑ j : Fin d, C.M j i *
      fderiv ℝ (fun y => C.ρ τ' y * kernelConvDeriv d C.s i ψ y) x (EuclideanSpace.single j (1 : ℝ)) := by
  have hl := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have hψ1 : ContDiff ℝ 1 ψ := hψ.1.of_le (by simp)
  unfold nonlocalTestRd
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hg : ∀ y, gradient (HRS.Whole.convFun (rieszKernel d C.s) ψ) y i = kernelConvDeriv d C.s i ψ y := by
    intro y
    rw [q09_gradient_apply]
    exact HRS.MS.UniqT3.convFun_D1 hl hψ1 hψ.2 i y
  show C.M j i * partialDeriv (fun _ : Fin 1 => j)
    (fun y => C.ρ τ' y * gradient (HRS.Whole.convFun (rieszKernel d C.s) ψ) y i) x = _
  congr 1
  simp only [hg]
  unfold partialDeriv
  rw [iteratedFDeriv_one_apply]

end Nc2

end HRS.Whole.AppendixA.Phase2SA16R
