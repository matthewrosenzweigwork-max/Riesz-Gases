import HRS.MC.S7PIHC2Ext

/-!
# Packet piH, `C^{1,2}` extension, part 3: spatial derivatives of the extension
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIH

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIS3

variable {q : ℕ}

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem S7PIH_comb_fderiv {φ ψ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ) (s : ℝ) :
    ContDiff ℝ 2 (fun c => φ c + s * ψ c) ∧
    (∀ y u, fderiv ℝ (fun c => φ c + s * ψ c) y u = fderiv ℝ φ y u + s * fderiv ℝ ψ y u) ∧
    (∀ x v u, fderiv ℝ (fderiv ℝ (fun c => φ c + s * ψ c)) x v u =
      fderiv ℝ (fderiv ℝ φ) x v u + s * fderiv ℝ (fderiv ℝ ψ) x v u) := by
  have dφ : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have dψ : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have dφ' : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have dψ' : Differentiable ℝ (fderiv ℝ ψ) :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have e1 : fderiv ℝ (fun c => φ c + s * ψ c) = fun y => fderiv ℝ φ y + s • fderiv ℝ ψ y := by
    funext y
    exact ((dφ y).hasFDerivAt.add ((dψ y).hasFDerivAt.const_mul s)).fderiv
  refine ⟨hφ.add (contDiff_const.mul hψ), fun y u => ?_, fun x v u => ?_⟩
  · rw [e1]; simp
  · have h2 : HasFDerivAt (fun y => fderiv ℝ φ y + s • fderiv ℝ ψ y)
        (fderiv ℝ (fderiv ℝ φ) x + s • fderiv ℝ (fderiv ℝ ψ) x) x :=
      (dφ' x).hasFDerivAt.add ((dψ' x).hasFDerivAt.const_smul s)
    rw [e1, h2.fderiv]
    simp

end Generic

variable {a b : ℝ} {A S : ℝ → Matrix (Fin q) (Fin q) ℝ} {G : EuclideanSpace ℝ (Fin q) → ℝ}

theorem S7PIH_ext_contDiff (hG : MemCb 4 G) (r : ℝ) : ContDiff ℝ 2 (S7PIH_ext a b A S G r) := by
  have h4 := S7PIH_heat_cd4 (S := S) G hG (S7PIH_rho a b r)
  exact (S7PIH_comb_fderiv (h4.of_le (by norm_num))
    (S7PIH_Wphi_contDiff (fun i j => A (S7PIH_rho a b r) i j) h4) _).1

theorem S7PIH_ext_fderiv (hG : MemCb 4 G) (r : ℝ) (y u : EuclideanSpace ℝ (Fin q)) :
    fderiv ℝ (S7PIH_ext a b A S G r) y u =
      iteratedFDeriv ℝ 1 (gaussHeat S G (S7PIH_rho a b r)) y ![u] +
      (r - S7PIH_rho a b r) * (-(1 / 2) * ∑ i, ∑ j, A (S7PIH_rho a b r) i j *
        iteratedFDeriv ℝ 3 (gaussHeat S G (S7PIH_rho a b r)) y
          (Fin.cons u ![EuclideanSpace.single i 1, EuclideanSpace.single j 1])) := by
  have h4 := S7PIH_heat_cd4 (S := S) G hG (S7PIH_rho a b r)
  have := (S7PIH_comb_fderiv (h4.of_le (by norm_num))
    (S7PIH_Wphi_contDiff (fun i j => A (S7PIH_rho a b r) i j) h4) (r - S7PIH_rho a b r)).2.1 y u
  unfold S7PIH_ext
  rw [this, S7PIH_Wphi_fderiv _ h4, iteratedFDeriv_one_apply]
  simp

theorem S7PIH_ext_fderiv2 (hG : MemCb 4 G) (r : ℝ) (x v u : EuclideanSpace ℝ (Fin q)) :
    fderiv ℝ (fderiv ℝ (S7PIH_ext a b A S G r)) x v u =
      iteratedFDeriv ℝ 2 (gaussHeat S G (S7PIH_rho a b r)) x ![v, u] +
      (r - S7PIH_rho a b r) * (-(1 / 2) * ∑ i, ∑ j, A (S7PIH_rho a b r) i j *
        iteratedFDeriv ℝ 4 (gaussHeat S G (S7PIH_rho a b r)) x
          (Fin.cons v (Fin.cons u ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]))) := by
  have h4 := S7PIH_heat_cd4 (S := S) G hG (S7PIH_rho a b r)
  have := (S7PIH_comb_fderiv (h4.of_le (by norm_num))
    (S7PIH_Wphi_contDiff (fun i j => A (S7PIH_rho a b r) i j) h4) (r - S7PIH_rho a b r)).2.2 x v u
  unfold S7PIH_ext
  rw [this, S7PIH_Wphi_fderiv2 _ h4, iteratedFDeriv_two_apply]
  simp

end HRS.MC.Sec7.S7PIH

end
