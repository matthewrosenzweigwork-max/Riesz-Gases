import HRS.MS.SA12DE7J
import HRS.MS.SA12DE7H

/-!
# S.A.12(c), packet E7.07 (worker S82Z2), part K: ordered derivatives and integration by parts for smooth functions

`sa12de7_partialDeriv_cons`: for `F ∈ C^∞`, `∂^{(i, idx)} F = ∂_i (∂^{idx} F)` (`partialDeriv` of the consed index tuple).
`sa12de7_ibp_smooth`: for `P ∈ C^∞` and a real `C_c^∞` test `ψ`, `∫ (∂_i P) ψ = -∫ P ∂_iψ`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.SA12DE7

open HRS HRS.Whole HRS.MH.AdjointRd HRS.Whole.AppendixA HRS.Whole.Q09A

variable {d : ℕ}

theorem sa12de7_partialDeriv_cons {F : Euc d → ℝ} (hF : ContDiff ℝ ∞ F) {j : ℕ} (i : Fin d)
    (idx : Fin j → Fin d) (x : Euc d) :
    partialDeriv (Fin.cons i idx : Fin (j + 1) → Fin d) F x =
      fderiv ℝ (partialDeriv idx F) x (EuclideanSpace.single i (1 : ℝ)) := by
  have hdiff : Differentiable ℝ (iteratedFDeriv ℝ j F) :=
    hF.differentiable_iteratedFDeriv (by exact_mod_cast ENat.coe_lt_top j)
  have h1 : partialDeriv idx F = fun y => iteratedFDeriv ℝ j F y (fun l => EuclideanSpace.single (idx l) (1 : ℝ)) :=
    rfl
  rw [h1, fderiv_continuousMultilinear_apply_const_apply (hdiff x)]
  unfold partialDeriv
  rw [iteratedFDeriv_succ_apply_left]
  congr 1

theorem sa12de7_ibp_smooth {P ψ : Euc d → ℝ} (hP : ContDiff ℝ ∞ P) (hψ : IsCcInfty ψ) (i : Fin d) :
    ∫ x, fderiv ℝ P x (EuclideanSpace.single i (1 : ℝ)) * ψ x =
      -∫ x, P x * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)) := by
  obtain ⟨hψs, hψc⟩ := hψ
  set e : Euc d := EuclideanSpace.single i (1 : ℝ) with he
  have hPd : Differentiable ℝ P := hP.differentiable (by simp)
  have hψd : Differentiable ℝ ψ := hψs.differentiable (by simp)
  have hPc : Continuous P := hP.continuous
  have hψcont : Continuous ψ := hψs.continuous
  have hdψc : Continuous fun x => fderiv ℝ ψ x e :=
    ((hψs.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hdPc : Continuous fun x => fderiv ℝ P x e :=
    ((hP.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hdψsupp : HasCompactSupport fun x => fderiv ℝ ψ x e := by
    have : HasCompactSupport (fderiv ℝ ψ) := hψc.fderiv (𝕜 := ℝ)
    exact this.comp_left (g := fun A : Euc d →L[ℝ] ℝ => A e) (by simp)
  have i1 : Integrable (fun x => fderiv ℝ P x e * ψ x) volume :=
    (hdPc.mul hψcont).integrable_of_hasCompactSupport hψc.mul_left
  have i2 : Integrable (fun x => P x * fderiv ℝ ψ x e) volume :=
    (hPc.mul hdψc).integrable_of_hasCompactSupport hdψsupp.mul_left
  have i3 : Integrable (fun x => P x * ψ x) volume :=
    (hPc.mul hψcont).integrable_of_hasCompactSupport hψc.mul_left
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Euc d))) (v := e)
    (f := P) (g := ψ) i1 i2 i3 (fun x _ => hPd x) (fun x _ => hψd x)
  rw [this]
  ring

end HRS.MS.SA12DE7
