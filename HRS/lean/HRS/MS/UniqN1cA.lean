import HRS.MS.UniqN2bD
import HRS.MS.UniqN1aF
import HRS.MS.UniqN1bB

/-!
# N1c of `UniqPlan.md`, part (a): the general product-rule identity and the local Hessian bound

* `n1c_D1_kcd`: `∂_j H_i = g * ∂_j∂_iψ` for `ψ ∈ C²_c` and `H_i = kernelConvDeriv d s i ψ`.
* `n1c_nMain_eq`: with no condition on `M`,
  `nMain D ρ' f ψ = ∑_{ij} M_{ji} (∫ f (∂_jρ' H_i) + ∫ f (ρ' ∂_jH_i))`.
* `n1c_hess_local`: for `s ≤ d - 2` the local Hessian bound of `n1a_hess_local` / `n1b_hess_local`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN1c

open HRS HRS.Whole HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqM1 HRS.MS.UniqNDefs
  HRS.MS.UniqN2b

variable {d : ℕ}

/-- `∂_j H_i = g * ∂_j∂_iψ`. -/
theorem n1c_D1_kcd {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hψc : HasCompactSupport ψ) (i j : Fin d) (y : Euc d) :
    D1 j (kernelConvDeriv d s i ψ) y =
      HRS.Whole.convFun (rieszKernel d s) (D1 j (D1 i ψ)) y := by
  have hl := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have hK : kernelConvDeriv d s i ψ = HRS.Whole.convFun (rieszKernel d s) (D1 i ψ) := rfl
  rw [hK]
  exact convFun_D1 hl (D1_contDiff hψ i) (D1_supp hψc i) j y

theorem n1c_D1_kcd_cont {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) (i j : Fin d) :
    Continuous (D1 j (kernelConvDeriv d s i ψ)) := by
  have : D1 j (kernelConvDeriv d s i ψ) =
      HRS.Whole.convFun (rieszKernel d s) (D1 j (D1 i ψ)) :=
    funext (n1c_D1_kcd hs0 hsd hψ hψc i j)
  rw [this]
  exact K_cont hs0 hsd (n2b_D1D1_cont hψ i j) (D1_supp (D1_supp hψc i) j)

/-- **The general product-rule identity** (no antisymmetry of `M`). -/
theorem n1c_nMain_eq {D : WholeDyn d} (hs0 : 0 ≤ D.s) (hsd : D.s < d)
    {ρ' : Euc d → ℝ} (hρ : ContDiff ℝ 1 ρ') {Cρ : ℝ}
    (hρ0 : ∀ y, |ρ' y| ≤ Cρ * (1 + ‖y‖) ^ (-((d : ℝ) + 3)))
    (hρ1 : ∀ y, ‖fderiv ℝ ρ' y‖ ≤ Cρ * (1 + ‖y‖) ^ (-((d : ℝ) + 3)))
    {A : ℝ} {f : Euc d → ℝ} (hf : LocMass A f)
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
    nMain D ρ' f ψ =
      ∑ i, ∑ j, D.M j i * ((∫ y, f y * (D1 j ρ' y * kernelConvDeriv d D.s i ψ y)) +
        ∫ y, f y * (ρ' y * D1 j (kernelConvDeriv d D.s i ψ) y)) := by
  have hρc : Continuous ρ' := hρ.continuous
  have hDρ : ∀ j, Continuous (D1 j ρ') := fun j =>
    (hρ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hHc : ∀ i, Continuous (kernelConvDeriv d D.s i ψ) := fun i =>
    K_cont hs0 hsd (D1_contDiff hψ i).continuous (D1_supp hψc i)
  have I1 : ∀ i j, Integrable (fun y => f y * (D1 j ρ' y * kernelConvDeriv d D.s i ψ y)) volume := by
    intro i j
    obtain ⟨C1, hC1⟩ := conv_bound hs0 hsd (D1_contDiff hψ i).continuous (D1_supp hψc i)
    exact key_int hf.1 (A ^ 2) hf.2 ((hDρ j).mul (hHc i)).aestronglyMeasurable (Cρ * C1)
      (n2b_wt_dom (fun y => (n2b_D1_le j ρ' y).trans (hρ1 y)) (fun y => hC1 y))
  have I2 : ∀ i j, Integrable (fun y => f y * (ρ' y *
      D1 j (kernelConvDeriv d D.s i ψ) y)) volume := by
    intro i j
    obtain ⟨C1, hC1⟩ := conv_bound hs0 hsd (n2b_D1D1_cont hψ i j) (D1_supp (D1_supp hψc i) j)
    refine key_int hf.1 (A ^ 2) hf.2 (hρc.mul (n1c_D1_kcd_cont hs0 hsd hψ hψc i j)).aestronglyMeasurable
      (Cρ * C1) (n2b_wt_dom hρ0 (fun y => ?_))
    rw [n1c_D1_kcd hs0 hsd hψ hψc]
    exact hC1 y
  unfold nMain
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [← integral_add (I1 i j) (I2 i j)]
  congr 1; funext y
  rw [n2b_fderiv_prod hs0 hsd hρ hψ hψc i j y, ← n1c_D1_kcd hs0 hsd hψ hψc i j y]
  ring

/-- The local Hessian bound for `s ≤ d - 2`. -/
theorem n1c_hess_local (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ (d : ℝ) - 2) :
    ∃ C₀ C : ℝ, ∀ (i j : Fin d) (ρ : ℝ), 1 ≤ ρ → ∀ (c : Euc d) (ψ : Euc d → ℝ),
      ContDiff ℝ 2 ψ → HasCompactSupport ψ → Function.support ψ ⊆ closedBall c ρ →
      ∀ (c' : Euc d) (r' : ℝ), r' ≤ ρ →
        eLpNorm ((closedBall c' r').indicator (fun y => D1 j (kernelConvDeriv d s i ψ) y)) 2 volume ≤
          ENNReal.ofReal (C * ρ ^ C₀) * eLpNorm ψ 2 volume := by
  rcases lt_or_eq_of_le hs2 with h | h
  · exact HRS.MS.UniqN1a.n1a_hess_local hd hs0 h
  · exact HRS.MS.UniqN1b.n1b_hess_local hd hs0 h

end HRS.MS.UniqN1c
