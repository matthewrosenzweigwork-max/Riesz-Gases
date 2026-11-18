import HRS.MS.SA12LimitL7
import HRS.MS.SA16TAp3b

/-!
# S.A.16 (SA16T) Lm1: the nonlocal test function in terms of the density, with growth bounds independent of the density

`sa16t_nl_rep`: for `ψ ∈ C_c^∞` there is `CH` such that, for every coefficient `C` with `C.s = s` and every `τ'` with
`C.ρ τ' ∈ C^1`, `nonlocalTestRd C τ' ψ x = ∑_{ij} M_{ji} (∂_jρ H_i + ρ ∂_j H_i)` with `H_i = ∂_i (g*ψ)`
(`kernelConvDeriv`), and `|H_i|, |∂_j H_i| ≤ CH (1+|x|)`.  So `nonlocalTestRd` depends on `ρ` only through `ρ, ∇ρ`
pointwise (convergence of densities gives pointwise convergence) and is dominated by `CH (1+|x|) (|ρ| + |∇ρ|)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd

section Lm1
variable {d : ℕ}

theorem sa16t_nl_rep (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) :
    ∃ CH : ℝ, 0 ≤ CH ∧ (∀ i x, |kernelConvDeriv d s i ψ x| ≤ CH * (1 + ‖x‖)) ∧
      (∀ i j x, |HRS.MS.UniqT3.D1 j (kernelConvDeriv d s i ψ) x| ≤ CH * (1 + ‖x‖)) ∧
      ∀ (C : WholeCoeff d) (τ' : ℝ), C.s = s → ContDiff ℝ 1 (C.ρ τ') → ∀ x,
        nonlocalTestRd C τ' ψ x = ∑ i : Fin d, ∑ j : Fin d, C.M j i *
          (HRS.MS.UniqT3.D1 j (C.ρ τ') x * kernelConvDeriv d s i ψ x + C.ρ τ' x *
            HRS.MS.UniqT3.D1 j (kernelConvDeriv d s i ψ) x) := by
  have hl := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have hψ2 : ContDiff ℝ 2 ψ := hψ.1.of_le (by simp)
  have hψ1 : ContDiff ℝ 1 ψ := hψ.1.of_le (by simp)
  choose C1 hC1 using fun i : Fin d => HRS.MS.UniqT3.conv_bound hs0 hsd
    (HRS.MS.UniqT3.D1_contDiff hψ2 i).continuous (HRS.MS.UniqT3.D1_supp hψ.2 i)
  choose C2 hC2 using fun i j : Fin d => HRS.MS.UniqT3.conv_bound hs0 hsd
    (HRS.MS.UniqN2b.n2b_D1D1_cont hψ2 i j)
    (HRS.MS.UniqT3.D1_supp (HRS.MS.UniqT3.D1_supp hψ.2 i) j)
  set CH : ℝ := ∑ i, |C1 i| with hCH
  set CHH : ℝ := ∑ i, ∑ j, |C2 i j| with hCHH
  have hCH0 : 0 ≤ CH := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hCHH0 : 0 ≤ CHH := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hH : ∀ i x, |kernelConvDeriv d s i ψ x| ≤ CH * (1 + ‖x‖) := by
    intro i x
    have h1 : |kernelConvDeriv d s i ψ x| ≤ |C1 i| * (1 + ‖x‖) :=
      (hC1 i x).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    exact h1.trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := fun i => |C1 i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i))
      (by positivity))
  have hHH : ∀ i j x, |HRS.MS.UniqT3.D1 j (kernelConvDeriv d s i ψ) x| ≤ CHH * (1 + ‖x‖) := by
    intro i j x
    rw [HRS.MS.UniqN1c.n1c_D1_kcd hs0 hsd hψ2 hψ.2 i j x]
    have h1 : |HRS.Whole.convFun (rieszKernel d s) (HRS.MS.UniqT3.D1 j (HRS.MS.UniqT3.D1 i ψ)) x| ≤
        |C2 i j| * (1 + ‖x‖) :=
      (hC2 i j x).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    calc |C2 i j| ≤ ∑ j', |C2 i j'| :=
          Finset.single_le_sum (f := fun j' => |C2 i j'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', |C2 i' j'| :=
          Finset.single_le_sum (f := fun i' => ∑ j', |C2 i' j'|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  refine ⟨CH + CHH, add_nonneg hCH0 hCHH0, fun i x => (hH i x).trans (mul_le_mul_of_nonneg_right
    (le_add_of_nonneg_right hCHH0) (by positivity)), fun i j x => (hHH i j x).trans (mul_le_mul_of_nonneg_right
    (le_add_of_nonneg_left hCH0) (by positivity)), fun C τ' hCs hρ1 x => ?_⟩
  unfold nonlocalTestRd
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hg : ∀ y, gradient (HRS.Whole.convFun (rieszKernel d C.s) ψ) y i = kernelConvDeriv d C.s i ψ y := by
    intro y
    rw [q09_gradient_apply]
    exact HRS.MS.UniqT3.convFun_D1 (hCs ▸ hl) hψ1 hψ.2 i y
  show C.M j i * partialDeriv (fun _ : Fin 1 => j)
    (fun y => C.ρ τ' y * gradient (HRS.Whole.convFun (rieszKernel d C.s) ψ) y i) x = _
  rw [hCs] at hg ⊢
  congr 1
  simp only [hg]
  unfold partialDeriv
  rw [iteratedFDeriv_one_apply]
  have h := HRS.MS.UniqN2b.n2b_fderiv_prod hs0 hsd hρ1 hψ2 hψ.2 i j x
  rw [HRS.MS.UniqN1c.n1c_D1_kcd hs0 hsd hψ2 hψ.2 i j x]
  exact h

end Lm1

end HRS.Whole.AppendixA.Phase2SA16R
