import HRS.MC.S7PIHPde

/-!
# Packet piH, `C^{1,2}` extension, part 1: derivatives in `c` of the time derivative `W`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIH

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIS3

variable {q : ℕ}

/-- Derivative of `y ↦ D^nφ(y) m` in the direction `u`. -/
theorem S7PIH_fderiv_iter {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {φ : E → ℝ} {n : ℕ}
    (hφ : ContDiff ℝ (n + 1) φ) (x u : E) (m : Fin n → E) :
    fderiv ℝ (fun y => iteratedFDeriv ℝ n φ y m) x u = iteratedFDeriv ℝ (n + 1) φ x (Fin.cons u m) := by
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n φ) x :=
    hφ.differentiable_iteratedFDeriv (m := n) (by exact_mod_cast Nat.lt_succ_self n) x
  rw [fderiv_continuousMultilinear_apply_const_apply hd, iteratedFDeriv_succ_apply_left]
  simp

theorem S7PIH_fderiv_sumprod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : Fin q → Fin q → E → ℝ} {x : E} (hg : ∀ i j, DifferentiableAt ℝ (g i j) x)
    (α : Fin q → Fin q → ℝ) (u : E) :
    fderiv ℝ (fun y => -(1 / 2) * ∑ i, ∑ j, α i j * g i j y) x u =
      -(1 / 2) * ∑ i, ∑ j, α i j * fderiv ℝ (g i j) x u := by
  have h : HasFDerivAt (fun y => -(1 / 2) * ∑ i, ∑ j, α i j * g i j y)
      ((-(1 / 2 : ℝ)) • ∑ i, ∑ j, α i j • fderiv ℝ (g i j) x) x :=
    (HasFDerivAt.fun_sum fun i _ => HasFDerivAt.fun_sum fun j _ =>
      ((hg i j).hasFDerivAt.const_mul (α i j))).const_mul (-(1 / 2 : ℝ))
  rw [h.fderiv]
  simp [ContinuousLinearMap.sum_apply]

/-- The (negative half) Hessian pairing with a weight matrix. -/
def S7PIH_Wphi (α : Fin q → Fin q → ℝ) (φ : EuclideanSpace ℝ (Fin q) → ℝ)
    (c : EuclideanSpace ℝ (Fin q)) : ℝ :=
  -(1 / 2) * ∑ i, ∑ j, α i j *
    iteratedFDeriv ℝ 2 φ c ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]

theorem S7PIH_Wphi_contDiff (α : Fin q → Fin q → ℝ) {φ : EuclideanSpace ℝ (Fin q) → ℝ}
    (hφ : ContDiff ℝ 4 φ) : ContDiff ℝ 2 (S7PIH_Wphi α φ) := by
  have hit : ContDiff ℝ 2 (iteratedFDeriv ℝ 2 φ) :=
    hφ.iteratedFDeriv_right (m := 2) (i := 2) (by norm_num)
  have hev : ∀ m : Fin 2 → EuclideanSpace ℝ (Fin q),
      ContDiff ℝ 2 (fun c => iteratedFDeriv ℝ 2 φ c m) := fun m =>
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => EuclideanSpace ℝ (Fin q)) ℝ m).contDiff.comp hit
  unfold S7PIH_Wphi
  refine contDiff_const.mul ?_
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  exact contDiff_const.mul (hev _)

theorem S7PIH_Wphi_fderiv (α : Fin q → Fin q → ℝ) {φ : EuclideanSpace ℝ (Fin q) → ℝ}
    (hφ : ContDiff ℝ 4 φ) (x u : EuclideanSpace ℝ (Fin q)) :
    fderiv ℝ (S7PIH_Wphi α φ) x u = -(1 / 2) * ∑ i, ∑ j, α i j *
      iteratedFDeriv ℝ 3 φ x (Fin.cons u ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]) := by
  have hit : ContDiff ℝ 1 (iteratedFDeriv ℝ 2 φ) :=
    hφ.iteratedFDeriv_right (m := 1) (i := 2) (by norm_num)
  have hev : ∀ m : Fin 2 → EuclideanSpace ℝ (Fin q),
      DifferentiableAt ℝ (fun c => iteratedFDeriv ℝ 2 φ c m) x := fun m =>
    ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => EuclideanSpace ℝ (Fin q)) ℝ m).contDiff.comp
      hit).differentiable (by norm_num) x
  have := S7PIH_fderiv_sumprod (g := fun i j c => iteratedFDeriv ℝ 2 φ c
    ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]) (x := x) (fun i j => hev _) α u
  unfold S7PIH_Wphi
  rw [this]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [S7PIH_fderiv_iter (n := 2) (hφ.of_le (by norm_num))]

theorem S7PIH_Wphi_fderiv2 (α : Fin q → Fin q → ℝ) {φ : EuclideanSpace ℝ (Fin q) → ℝ}
    (hφ : ContDiff ℝ 4 φ) (x v u : EuclideanSpace ℝ (Fin q)) :
    fderiv ℝ (fderiv ℝ (S7PIH_Wphi α φ)) x v u = -(1 / 2) * ∑ i, ∑ j, α i j *
      iteratedFDeriv ℝ 4 φ x (Fin.cons v (Fin.cons u
        ![EuclideanSpace.single i 1, EuclideanSpace.single j 1])) := by
  have hW : ContDiff ℝ 2 (S7PIH_Wphi α φ) := S7PIH_Wphi_contDiff α hφ
  have hd : DifferentiableAt ℝ (fderiv ℝ (S7PIH_Wphi α φ)) x :=
    (hW.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have h1 : fderiv ℝ (fderiv ℝ (S7PIH_Wphi α φ)) x v u =
      fderiv ℝ (fun y => fderiv ℝ (S7PIH_Wphi α φ) y u) x v := by
    have : HasFDerivAt (fun y => fderiv ℝ (S7PIH_Wphi α φ) y u)
        ((ContinuousLinearMap.apply ℝ ℝ u).comp (fderiv ℝ (fderiv ℝ (S7PIH_Wphi α φ)) x)) x :=
      (ContinuousLinearMap.apply ℝ ℝ u).hasFDerivAt.comp x hd.hasFDerivAt
    rw [this.fderiv]
    rfl
  have hfun : (fun y => fderiv ℝ (S7PIH_Wphi α φ) y u) = fun y => -(1 / 2) * ∑ i, ∑ j, α i j *
      iteratedFDeriv ℝ 3 φ y (Fin.cons u ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]) := by
    funext y; exact S7PIH_Wphi_fderiv α hφ y u
  have hit : ContDiff ℝ 1 (iteratedFDeriv ℝ 3 φ) :=
    hφ.iteratedFDeriv_right (m := 1) (i := 3) (by norm_num)
  have hev : ∀ m : Fin 3 → EuclideanSpace ℝ (Fin q),
      DifferentiableAt ℝ (fun c => iteratedFDeriv ℝ 3 φ c m) x := fun m =>
    ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin q)) ℝ m).contDiff.comp
      hit).differentiable (by norm_num) x
  rw [h1, hfun]
  have := S7PIH_fderiv_sumprod (g := fun i j c => iteratedFDeriv ℝ 3 φ c
    (Fin.cons u ![EuclideanSpace.single i 1, EuclideanSpace.single j 1])) (x := x)
    (fun i j => hev _) α v
  rw [this]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [S7PIH_fderiv_iter (n := 3) (hφ.of_le (by norm_num))]

end HRS.MC.Sec7.S7PIH

end
