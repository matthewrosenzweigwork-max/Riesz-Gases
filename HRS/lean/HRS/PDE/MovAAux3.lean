import HRS.PDE.MovAAux2

/-!
# MOVA Aux3: configuration-space algebra for the regularised source (generator of one-body sums,
pair-term symmetrisation, expansion of the commutator statistic).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem mova_psiL_hasFDerivAt {φ : Torus d → ℝ} (hφ : Torus.IsCk 1 φ) (Y : Fin N → Euc d) :
    HasFDerivAt (fun Y : Fin N → Euc d => ∑ i, Torus.lift φ (Y i))
      (∑ i, (fderiv ℝ (Torus.lift φ) (Y i)).comp (ContinuousLinearMap.proj i)) Y := by
  have hd : Differentiable ℝ (Torus.lift φ) :=
    (show ContDiff ℝ 1 (Torus.lift φ) from hφ).differentiable one_ne_zero
  refine HasFDerivAt.fun_sum fun i _ => ?_
  exact (hd (Y i)).hasFDerivAt.comp Y
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i).hasFDerivAt

theorem mova_psiL_fderiv {φ : Torus d → ℝ} (hφ : Torus.IsCk 1 φ) :
    fderiv ℝ (fun Y : Fin N → Euc d => ∑ i, Torus.lift φ (Y i)) =
      fun Y => ∑ i, (fderiv ℝ (Torus.lift φ) (Y i)).comp (ContinuousLinearMap.proj i) :=
  funext fun Y => (mova_psiL_hasFDerivAt hφ Y).fderiv

theorem mova_psiL_fderiv2 {φ : Torus d → ℝ} (hφ : Torus.IsCk 2 φ) (Y v w : Fin N → Euc d) :
    fderiv ℝ (fderiv ℝ (fun Y : Fin N → Euc d => ∑ i, Torus.lift φ (Y i))) Y v w =
      ∑ i, fderiv ℝ (fderiv ℝ (Torus.lift φ)) (Y i) (v i) (w i) := by
  have h1 : Torus.IsCk 1 φ := mova_isCk_one_of_two hφ
  rw [mova_psiL_fderiv h1]
  have hc : ContDiff ℝ 2 (Torus.lift φ) := hφ
  have hd2 : Differentiable ℝ (fderiv ℝ (Torus.lift φ)) :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hterm : ∀ i : Fin N, HasFDerivAt
      (fun Y : Fin N → Euc d => (fderiv ℝ (Torus.lift φ) (Y i)).comp (ContinuousLinearMap.proj i))
      (((ContinuousLinearMap.compL ℝ (Fin N → Euc d) (Euc d) ℝ).flip
          (ContinuousLinearMap.proj i : (Fin N → Euc d) →L[ℝ] Euc d)).comp
        ((fderiv ℝ (fderiv ℝ (Torus.lift φ)) (Y i)).comp (ContinuousLinearMap.proj i))) Y := by
    intro i
    have hA := (hd2 (Y i)).hasFDerivAt.comp Y
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i).hasFDerivAt
    exact ((ContinuousLinearMap.compL ℝ (Fin N → Euc d) (Euc d) ℝ).flip
          (ContinuousLinearMap.proj i : (Fin N → Euc d) →L[ℝ] Euc d)).hasFDerivAt.comp Y hA
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => hterm i
  rw [hs.fderiv]
  simp

theorem mova_laplacian_eq_second (φ : Torus d → ℝ) (x : Torus d) :
    Torus.laplacian φ x = ∑ j : Fin d, fderiv ℝ (fderiv ℝ (Torus.lift φ)) (Torus.rep x)
      (EuclideanSpace.single j 1) (EuclideanSpace.single j 1) := by
  unfold Torus.laplacian
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (Torus.lift φ)
    (EuclideanSpace.basisFun (Fin d) ℝ)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iteratedFDeriv_two_apply]
  simp [EuclideanSpace.basisFun_apply]

theorem mova_fderiv_lift_rep (φ : Torus d → ℝ) (x : Torus d) (w : Euc d) :
    fderiv ℝ (Torus.lift φ) (Torus.rep x) w = inner ℝ (Torus.grad φ x) w := by
  unfold Torus.grad gradient
  rw [InnerProductSpace.toDual_symm_apply]

/-- The generator of `dX = b dt + √(2κ) dW` applied to a one-body sum `∑_i φ(x_i)`. -/
theorem mova_gen_sum (κ : ℝ) (bC : Config d N → Fin N → Euc d) {φ : Torus d → ℝ}
    (hφ : Torus.IsCk 2 φ) (X : Config d N) :
    d1_configGen κ bC (fun X => ∑ i, φ (X i)) X =
      κ * ∑ i, Torus.laplacian φ (X i) + ∑ i, inner ℝ (Torus.grad φ (X i)) (bC X i) := by
  have h1 : Torus.IsCk 1 φ := mova_isCk_one_of_two hφ
  have hL : configLift (fun _ => fun X : Config d N => ∑ i, φ (X i)) 0 =
      fun Y : Fin N → Euc d => ∑ i, Torus.lift φ (Y i) := rfl
  unfold d1_configGen
  rw [hL]
  congr 1
  · congr 1
    simp_rw [mova_psiL_fderiv2 hφ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mova_laplacian_eq_second, Fintype.sum_prod_type, Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp [configBasis]
    · intro a _ ha
      refine Finset.sum_eq_zero fun j _ => ?_
      simp [configBasis, Pi.single_apply, Ne.symm ha]
    · intro h; exact absurd (Finset.mem_univ i) h
  · rw [mova_psiL_fderiv h1]
    simp [mova_fderiv_lift_rep]

/-! ### The commutator kernel -/

theorem mova_fderiv_odd_of_even {H : Euc d → ℝ} (hH : Differentiable ℝ H) (hev : ∀ w, H (-w) = H w)
    (w : Euc d) : fderiv ℝ H (-w) = -fderiv ℝ H w := by
  have h1 : HasFDerivAt (fun w => H (-w))
      ((fderiv ℝ H (-w)).comp (-ContinuousLinearMap.id ℝ (Euc d))) w :=
    (hH (-w)).hasFDerivAt.comp w (hasFDerivAt_id w).neg
  have e : (fun w => H (-w)) = H := funext hev
  rw [e] at h1
  rw [h1.fderiv]
  ext u
  simp

/-- The gradient of an even `C¹` function on the torus is odd. -/
theorem mova_grad_odd {h : Torus d → ℝ} (h1 : Torus.IsCk 1 h) (hev : ∀ x, h (-x) = h x)
    (x : Torus d) : Torus.grad h (-x) = -Torus.grad h x := by
  have hd : Differentiable ℝ (Torus.lift h) :=
    (show ContDiff ℝ 1 (Torus.lift h) from h1).differentiable one_ne_zero
  have hl : ∀ w, Torus.lift h (-w) = Torus.lift h w := fun w => by
    simp only [Torus.lift, Function.comp, KernelGrad.mk_neg]
    exact hev _
  ext j
  rw [mova_grad_apply, PiLp.neg_apply, mova_grad_apply]
  have hx : x = Torus.mk (Torus.rep x) := (Torus.mk_rep x).symm
  rw [hx, ← KernelGrad.mk_neg, PDE.partialDeriv_mk j h h1, PDE.partialDeriv_mk j h h1,
    mova_fderiv_odd_of_even hd hl]
  simp


theorem mova_commKernel_eq (G v : Torus d → Euc d) (x y : Torus d) :
    commKernel G v x y = inner ℝ (v x) (G (x - y)) - inner ℝ (v y) (G (x - y)) := by
  unfold commKernel
  by_cases h : x = y
  · subst h; simp
  · simp only [h, if_false, inner_sub_left]

theorem mova_pair_sum_comm (G v : Torus d → Euc d) (hG : ∀ z, G (-z) = -G z) (X : Config d N) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, commKernel G v (X i) (X j) =
      2 * ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (v (X i)) (G (X i - X j)) := by
  simp_rw [mova_commKernel_eq, Finset.sum_sub_distrib]
  have h2 : ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (v (X j)) (G (X i - X j)) =
      -∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (v (X i)) (G (X i - X j)) := by
    rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun j => Finset.univ.erase j)
      (f := fun i j => inner ℝ (v (X j)) (G (X i - X j)))
      (fun i j => by simp [Finset.mem_erase, and_comm, eq_comm])]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← neg_sub (X j) (X i), hG, inner_neg_right]
  rw [h2]
  ring

theorem mova_matVec_neg_one (v : Euc d) :
    Torus.matVec (-(1 : Matrix (Fin d) (Fin d) ℝ)) v = -v := by
  unfold Torus.matVec
  ext j
  simp [Matrix.toEuclideanLin, Matrix.mulVec]

end HRS
