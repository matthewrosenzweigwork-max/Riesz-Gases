import HRS.MS.UniqN3cA

/-!
# N3c, part B: the symmetric part of `M` and the Hessian

* `n3c_hess_symm`: `∂_j∂_iψ = ∂_i∂_jψ` for `ψ ∈ C²`.
* `n3c_D2q`: `D_q² ψ = ∑_{ij} q_i q_j ∂_j∂_iψ`.
* `n3c_conv_lin`: linearity of `g *` on the Hessian entries.
* `n3c_G_sum`: if `symPart M = -∑_l λ_l q_l q_lᵀ` then
  `∑_{ij} M_{ji} G_{ij} = - ∑_l λ_l (g * D_{q_l}² ψ)` pointwise.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN3c

open HRS HRS.Whole HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqM1 HRS.MS.UniqNDefs HRS.MS.UniqN2b

variable {d : ℕ}

theorem n3c_hess_symm {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ) (i j : Fin d) (x : Euc d) :
    D1 j (D1 i ψ) x = D1 i (D1 j ψ) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ ψ) x :=
    ((hψ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  have h1 : ∀ k l, D1 l (D1 k ψ) x =
      fderiv ℝ (fderiv ℝ ψ) x (EuclideanSpace.single l 1) (EuclideanSpace.single k 1) := by
    intro k l
    unfold D1
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  have hsymm := (hψ.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  rw [h1, h1]; exact hsymm _ _

/-- A linear functional is determined by its values on the basis. -/
theorem n3c_clm_sum (L : Euc d →L[ℝ] ℝ) (q : Euc d) :
    L q = ∑ i, q i * L (EuclideanSpace.single i (1 : ℝ)) := by
  have h := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr q
  conv_lhs => rw [← h]
  simp [map_sum, map_smul]

theorem n3c_D2q {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ) (q x : Euc d) :
    fderiv ℝ (fun z => fderiv ℝ ψ z q) x q = ∑ i, ∑ j, q i * q j * D1 j (D1 i ψ) x := by
  have hd : Differentiable ℝ (fderiv ℝ ψ) :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hDi : ∀ i, Differentiable ℝ (D1 i ψ) := fun i z => by
    unfold D1; exact (hd z).clm_apply (differentiableAt_const _)
  have e1 : (fun z => fderiv ℝ ψ z q) = fun z => ∑ i, q i * D1 i ψ z := by
    funext z
    rw [n3c_clm_sum (fderiv ℝ ψ z) q]; rfl
  rw [e1, fderiv_fun_sum (fun i _ => ((hDi i).const_mul (q i)) x)]
  simp only [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_const_mul (hDi i x), ContinuousLinearMap.smul_apply, smul_eq_mul,
    n3c_clm_sum (fderiv ℝ (D1 i ψ) x) q, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : D1 j (D1 i ψ) x = fderiv ℝ (D1 i ψ) x (EuclideanSpace.single j (1 : ℝ)) := rfl
  rw [this]; ring

/-- Linearity of `g *` on the Hessian entries. -/
theorem n3c_conv_lin {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hψc : HasCompactSupport ψ) (a : Fin d → Fin d → ℝ) (y : Euc d) :
    ∑ i, ∑ j, a i j * HRS.Whole.convFun (rieszKernel d s) (D1 j (D1 i ψ)) y =
      HRS.Whole.convFun (rieszKernel d s) (fun x => ∑ i, ∑ j, a i j * D1 j (D1 i ψ) x) y := by
  have hint : ∀ i j, Integrable (fun x => rieszKernel d s (y - x) * D1 j (D1 i ψ) x) volume :=
    fun i j => n2b_conv_integrable hs0 hsd (n2b_D1D1_cont hψ i j)
      (D1_supp (D1_supp hψc i) j) y
  have hint' : ∀ i j, Integrable (fun x => a i j * (rieszKernel d s (y - x) * D1 j (D1 i ψ) x))
      volume := fun i j => (hint i j).const_mul (a i j)
  have hpt : ∀ x, rieszKernel d s (y - x) * ∑ i, ∑ j, a i j * D1 j (D1 i ψ) x =
      ∑ i, ∑ j, a i j * (rieszKernel d s (y - x) * D1 j (D1 i ψ) x) := by
    intro x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  show _ = ∫ x, rieszKernel d s (y - x) * ∑ i, ∑ j, a i j * D1 j (D1 i ψ) x
  simp_rw [hpt]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint' i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint' i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  rfl

/-- The symmetric-part algebra: `∑ M_{ji} G_{ij} = ∑ (symPart M)_{ij} G_{ij}` for symmetric `G`. -/
theorem n3c_sym_sum (M : Matrix (Fin d) (Fin d) ℝ) (G : Fin d → Fin d → ℝ)
    (hG : ∀ i j, G i j = G j i) :
    ∑ i, ∑ j, M j i * G i j = ∑ i, ∑ j, Torus.symPart M i j * G i j := by
  have h1 : ∑ i, ∑ j, M j i * G i j = ∑ i, ∑ j, M i j * G i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hG i j]
  have h2 : ∀ i j, Torus.symPart M i j = (1 / 2) * (M i j + M j i) := by
    intro i j
    simp only [Torus.symPart, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
      smul_eq_mul]
  have h3 : ∑ i, ∑ j, Torus.symPart M i j * G i j =
      (1 / 2) * (∑ i, ∑ j, M j i * G i j + ∑ i, ∑ j, M i j * G i j) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h2]; ring
  rw [h3, ← h1]; ring

theorem n3c_G_sum {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hψc : HasCompactSupport ψ) {M : Matrix (Fin d) (Fin d) ℝ} {lam : Fin d → ℝ}
    {q : Fin d → Euc d} (hdiag : ∀ i j, Torus.symPart M i j = -∑ l, lam l * q l i * q l j)
    (y : Euc d) :
    ∑ i, ∑ j, M j i * HRS.Whole.convFun (rieszKernel d s) (D1 j (D1 i ψ)) y =
      -∑ l, lam l * HRS.Whole.convFun (rieszKernel d s)
        (fun z => fderiv ℝ (fun w => fderiv ℝ ψ w (q l)) z (q l)) y := by
  have hG : ∀ i j, HRS.Whole.convFun (rieszKernel d s) (D1 j (D1 i ψ)) y =
      HRS.Whole.convFun (rieszKernel d s) (D1 i (D1 j ψ)) y := fun i j => by
    unfold HRS.Whole.convFun
    simp_rw [n3c_hess_symm hψ i j]
  rw [n3c_sym_sum M _ hG]
  have hl : ∀ l, HRS.Whole.convFun (rieszKernel d s)
        (fun z => fderiv ℝ (fun w => fderiv ℝ ψ w (q l)) z (q l)) y =
      ∑ i, ∑ j, (q l i * q l j) * HRS.Whole.convFun (rieszKernel d s) (D1 j (D1 i ψ)) y := by
    intro l
    rw [n3c_conv_lin hs0 hsd hψ hψc (fun i j => q l i * q l j) y]
    congr 1; funext z
    exact n3c_D2q hψ (q l) z
  have e1 : ∀ i j, (-∑ l, lam l * q l i * q l j) *
      HRS.Whole.convFun (rieszKernel d s) (D1 j (D1 i ψ)) y =
      -∑ l, lam l * ((q l i * q l j) *
        HRS.Whole.convFun (rieszKernel d s) (D1 j (D1 i ψ)) y) := by
    intro i j
    rw [neg_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [hl, hdiag, e1, Finset.sum_neg_distrib, Finset.mul_sum]
  congr 1
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]

end HRS.MS.UniqN3c
