import HRS.MS.UniqN2bD
import HRS.MS.UniqN3aI
import HRS.MS.UniqN3bC

/-!
# N3c, part A: the splitting of `nMain` without antisymmetry

For `ψ ∈ C²_c`, `ρ' ∈ C¹` with decay and `f` of uniform local `L²` mass (no hypothesis on `M`):
`nMain D ρ' f ψ = ∑_{ij} M_{ji} ∫ f · (∂_jρ' · H_i) + ∫ f · ρ' · ∑_{ij} M_{ji} G_{ij}`, `G_{ij} = g * ∂_j∂_iψ`.
(The proof of `n2b_nMain_eq` without the final cancellation.)
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN3c

open HRS HRS.Whole HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqM1 HRS.MS.UniqNDefs HRS.MS.UniqN2b

variable {d : ℕ}

theorem n3c_nMain_split {D : WholeDyn d} (hs0 : 0 ≤ D.s) (hsd : D.s < d)
    {ρ' : Euc d → ℝ} (hρ : ContDiff ℝ 1 ρ') {Cρ : ℝ}
    (hρ0 : ∀ y, |ρ' y| ≤ Cρ * (1 + ‖y‖) ^ (-((d : ℝ) + 3)))
    (hρ1 : ∀ y, ‖fderiv ℝ ρ' y‖ ≤ Cρ * (1 + ‖y‖) ^ (-((d : ℝ) + 3)))
    {A : ℝ} {f : Euc d → ℝ} (hf : LocMass A f)
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
    nMain D ρ' f ψ =
      (∑ i, ∑ j, D.M j i * ∫ y, f y * (D1 j ρ' y * kernelConvDeriv d D.s i ψ y)) +
      ∫ y, f y * (ρ' y * ∑ i, ∑ j, D.M j i *
        HRS.Whole.convFun (rieszKernel d D.s) (D1 j (D1 i ψ)) y) := by
  have hρc : Continuous ρ' := hρ.continuous
  have hDρ : ∀ j, Continuous (D1 j ρ') := fun j =>
    (hρ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hHc : ∀ i, Continuous (kernelConvDeriv d D.s i ψ) := fun i =>
    K_cont hs0 hsd (D1_contDiff hψ i).continuous (D1_supp hψc i)
  have hGc : ∀ i j, Continuous (HRS.Whole.convFun (rieszKernel d D.s) (D1 j (D1 i ψ))) :=
    fun i j => K_cont hs0 hsd (n2b_D1D1_cont hψ i j) (D1_supp (D1_supp hψc i) j)
  have I1 : ∀ i j, Integrable (fun y => f y * (D1 j ρ' y * kernelConvDeriv d D.s i ψ y)) volume := by
    intro i j
    obtain ⟨C1, hC1⟩ := conv_bound hs0 hsd (D1_contDiff hψ i).continuous (D1_supp hψc i)
    exact key_int hf.1 (A ^ 2) hf.2 ((hDρ j).mul (hHc i)).aestronglyMeasurable (Cρ * C1)
      (n2b_wt_dom (fun y => (n2b_D1_le j ρ' y).trans (hρ1 y)) (fun y => hC1 y))
  have I2 : ∀ i j, Integrable (fun y => f y * (ρ' y *
      HRS.Whole.convFun (rieszKernel d D.s) (D1 j (D1 i ψ)) y)) volume := by
    intro i j
    obtain ⟨C1, hC1⟩ := conv_bound hs0 hsd (n2b_D1D1_cont hψ i j) (D1_supp (D1_supp hψc i) j)
    exact key_int hf.1 (A ^ 2) hf.2 (hρc.mul (hGc i j)).aestronglyMeasurable (Cρ * C1)
      (n2b_wt_dom hρ0 (fun y => hC1 y))
  unfold nMain
  have step : ∀ i j, (∫ x, f x * fderiv ℝ (fun y => ρ' y * kernelConvDeriv d D.s i ψ y) x
        (EuclideanSpace.single j (1 : ℝ))) =
      (∫ y, f y * (D1 j ρ' y * kernelConvDeriv d D.s i ψ y)) +
        ∫ y, f y * (ρ' y * HRS.Whole.convFun (rieszKernel d D.s) (D1 j (D1 i ψ)) y) := by
    intro i j
    rw [← integral_add (I1 i j) (I2 i j)]
    congr 1; funext y
    rw [n2b_fderiv_prod hs0 hsd hρ hψ hψc i j y]
    ring
  have hsecond : ∑ i, ∑ j, D.M j i * ∫ y, f y * (ρ' y *
      HRS.Whole.convFun (rieszKernel d D.s) (D1 j (D1 i ψ)) y) =
      ∫ y, f y * (ρ' y * ∑ i, ∑ j, D.M j i *
        HRS.Whole.convFun (rieszKernel d D.s) (D1 j (D1 i ψ)) y) := by
    have hI : ∀ i j, Integrable (fun y => D.M j i * (f y * (ρ' y *
        HRS.Whole.convFun (rieszKernel d D.s) (D1 j (D1 i ψ)) y))) volume :=
      fun i j => (I2 i j).const_mul _
    have h1 : ∑ i, ∑ j, D.M j i * ∫ y, f y * (ρ' y *
        HRS.Whole.convFun (rieszKernel d D.s) (D1 j (D1 i ψ)) y) =
        ∫ y, ∑ i, ∑ j, D.M j i * (f y * (ρ' y *
          HRS.Whole.convFun (rieszKernel d D.s) (D1 j (D1 i ψ)) y)) := by
      rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hI i j]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => hI i j]
      exact Finset.sum_congr rfl fun j _ => (integral_const_mul _ _).symm
    rw [h1]
    congr 1; funext y
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hsplit : ∀ i j, D.M j i * (∫ x, f x * fderiv ℝ (fun y => ρ' y * kernelConvDeriv d D.s i ψ y) x
        (EuclideanSpace.single j (1 : ℝ))) =
      D.M j i * (∫ y, f y * (D1 j ρ' y * kernelConvDeriv d D.s i ψ y)) +
        D.M j i * ∫ y, f y * (ρ' y * HRS.Whole.convFun (rieszKernel d D.s) (D1 j (D1 i ψ)) y) := by
    intro i j; rw [step, mul_add]
  simp_rw [hsplit, Finset.sum_add_distrib]
  rw [hsecond]

end HRS.MS.UniqN3c
