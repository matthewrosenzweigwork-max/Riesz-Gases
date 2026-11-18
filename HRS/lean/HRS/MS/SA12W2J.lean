import HRS.MS.SA12W2I
import HRS.MS.SA12V3
import HRS.Kernel.D1
import HRS.PDE.Classical

/-!
# S.A.12 C5 (SA12W2 worker), part J: scaling identity for the nonlocal term (`R26-T5.T05`, nonlocal half)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ComplexConjugate ContDiff

namespace HRS.PDE.SA12W2

variable {d : ℕ}

open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Construction

theorem sa12w2_fderiv_dil {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) {c : ℝ} (hc : c ≠ 0) (w : Euc d) (v : Euc d) :
    fderiv ℝ (fun x => f (c • x)) w v = c * fderiv ℝ f (c • w) v := by
  have h1 : HasFDerivAt (fun x : Euc d => c • x) (c • (ContinuousLinearMap.id ℝ (Euc d))) w :=
    (hasFDerivAt_id w).const_smul c
  have h2 : HasFDerivAt (fun x : Euc d => f (c • x))
      ((fderiv ℝ f (c • w)).comp (c • (ContinuousLinearMap.id ℝ (Euc d)))) w :=
    ((hf.differentiable (by simp)) (c • w)).hasFDerivAt.comp w h1
  rw [h2.fderiv]
  simp

theorem sa12w2_Xi_scale {s L : ℝ} (hL : 0 < L) (M : Matrix (Fin d) (Fin d) ℝ) {μt : Euc d → ℝ}
    (hμp : ∀ (x : Euc d) (z : Fin d → ℤ), μt (x + L • latticePt z) = μt x) (u : Torus d → ℝ)
    (hu : ContDiff ℝ ∞ (Torus.lift u)) (i : Fin d) (w : Euc d) :
    ∑ j, M j i * (μt (L • w) * fderiv ℝ (fun x => Torus.lift u (L⁻¹ • x)) (L • w)
        (EuclideanSpace.single j (1 : ℝ))) =
      L ^ (s + 1 - d) * Torus.lift (fun y => sa12w2_dens L μt y *
        (Torus.matVec ((L ^ (-s - 2)) • M).transpose (Torus.grad u y)) i) w := by
  have hdens : sa12w2_dens L μt (Torus.mk w) = L ^ d * μt (L • w) := sa12w2_dens_lift hμp w
  obtain ⟨m0, hm0⟩ := HRS.KernelAux.rep_mk_eq w
  have hgrad : ∀ j : Fin d, Torus.grad u (Torus.mk w) j =
      fderiv ℝ (Torus.lift u) w (EuclideanSpace.single j (1 : ℝ)) := by
    intro j
    rw [ClassicalAux.grad_apply]
    unfold Torus.partialDeriv
    rw [hm0, HRS.KernelGrad.fderiv_lift_add]
  have hF : ∀ j : Fin d, fderiv ℝ (fun x => Torus.lift u (L⁻¹ • x)) (L • w)
      (EuclideanSpace.single j (1 : ℝ)) =
      L⁻¹ * fderiv ℝ (Torus.lift u) w (EuclideanSpace.single j (1 : ℝ)) := by
    intro j
    rw [sa12w2_fderiv_dil (hu.of_le (by simp)) (inv_ne_zero hL.ne'), inv_smul_smul₀ hL.ne']
  have hexp : L ^ (s + 1 - d) * L ^ d * L ^ (-s - 2) = L⁻¹ := by
    rw [← Real.rpow_natCast L d, ← Real.rpow_add hL, ← Real.rpow_add hL]
    have : s + 1 - (d : ℝ) + (d : ℝ) + (-s - 2) = -1 := by ring
    rw [this, Real.rpow_neg_one]
  show _ = L ^ (s + 1 - d) * (sa12w2_dens L μt (Torus.mk w) *
    (Torus.matVec ((L ^ (-s - 2)) • M).transpose (Torus.grad u (Torus.mk w))) i)
  rw [hdens, ClassicalAux.matVec_apply]
  simp only [hF, hgrad, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : L ^ (s + 1 - d) * (L ^ d * μt (L • w) * (L ^ (-s - 2) * M j i *
      fderiv ℝ (Torus.lift u) w (EuclideanSpace.single j (1 : ℝ)))) =
      (L ^ (s + 1 - d) * L ^ d * L ^ (-s - 2)) * (μt (L • w) * (M j i *
        fderiv ℝ (Torus.lift u) w (EuclideanSpace.single j (1 : ℝ)))) := by ring
  rw [e, hexp]
  ring

theorem sa12w2_partialDeriv_lift (φ : Torus d → ℝ) (i : Fin d) (w : Euc d) :
    Torus.partialDeriv i φ (Torus.mk w) = fderiv ℝ (Torus.lift φ) w (EuclideanSpace.single i (1 : ℝ)) := by
  obtain ⟨m0, hm0⟩ := HRS.KernelAux.rep_mk_eq w
  unfold Torus.partialDeriv
  rw [hm0, HRS.KernelGrad.fderiv_lift_add]

theorem sa12w2_kk_scale {s L : ℝ} (hL : 0 < L) (M : Matrix (Fin d) (Fin d) ℝ) {μt : Euc d → ℝ}
    (hμ : ContDiff ℝ ∞ μt)
    (hμp : ∀ (x : Euc d) (z : Fin d → ℤ), μt (x + L • latticePt z) = μt x) (u : Torus d → ℝ)
    (hu : ContDiff ℝ ∞ (Torus.lift u)) (w : Euc d) :
    ∑ i : Fin d, ∑ j : Fin d, M j i * fderiv ℝ (fun y => μt y * fderiv ℝ (fun x => Torus.lift u (L⁻¹ • x)) y
        (EuclideanSpace.single j (1 : ℝ))) (L • w) (EuclideanSpace.single i (1 : ℝ)) =
      L ^ (s - d) * ∑ i : Fin d, Torus.partialDeriv i (fun y => sa12w2_dens L μt y *
        (Torus.matVec ((L ^ (-s - 2)) • M).transpose (Torus.grad u y)) i) (Torus.mk w) := by
  set F : Euc d → ℝ := fun x => Torus.lift u (L⁻¹ • x) with hFdef
  have hF : ContDiff ℝ ∞ F := hu.comp (contDiff_const_smul L⁻¹)
  have hfd : ∀ j : Fin d, ContDiff ℝ ∞ (fun y => fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))) := fun j =>
    (hF.fderiv_right (m := ∞) (by exact_mod_cast le_top)).clm_apply contDiff_const
  have hh : ∀ j : Fin d, ContDiff ℝ ∞ (fun y => μt y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))) :=
    fun j => hμ.mul (hfd j)
  set Ξ : Fin d → Euc d → ℝ := fun i y => ∑ j, M j i * (μt y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ)))
    with hΞ
  have hΞs : ∀ i, ContDiff ℝ ∞ (Ξ i) := fun i =>
    ContDiff.sum fun j _ => contDiff_const.mul (hh j)
  have hexp : L ^ (s - d) = L⁻¹ * L ^ (s + 1 - d) := by
    have : s - (d : ℝ) = (s + 1 - d) + (-1) := by ring
    rw [this, Real.rpow_add hL, Real.rpow_neg_one]; ring
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- the derivative of the combination
  have h1 : ∑ j : Fin d, M j i * fderiv ℝ (fun y => μt y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ)))
      (L • w) (EuclideanSpace.single i (1 : ℝ)) =
      fderiv ℝ (Ξ i) (L • w) (EuclideanSpace.single i (1 : ℝ)) := by
    have hd : ∀ j ∈ Finset.univ, HasFDerivAt (fun y => M j i * (μt y * fderiv ℝ F y
        (EuclideanSpace.single j (1 : ℝ)))) (M j i • fderiv ℝ (fun y => μt y * fderiv ℝ F y
          (EuclideanSpace.single j (1 : ℝ))) (L • w)) (L • w) := fun j _ =>
      (((hh j).differentiable (by simp)) (L • w)).hasFDerivAt.const_mul (M j i)
    have := (HasFDerivAt.fun_sum hd).fderiv
    rw [show Ξ i = fun y => ∑ j, M j i * (μt y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))) from rfl,
      this]
    simp
  rw [h1]
  have hlift : ∀ x : Euc d, Torus.lift (fun y => sa12w2_dens L μt y *
      (Torus.matVec ((L ^ (-s - 2)) • M).transpose (Torus.grad u y)) i) x =
      (L ^ (s + 1 - d))⁻¹ * Ξ i (L • x) := by
    intro x
    have h := sa12w2_Xi_scale (s := s) hL M hμp u hu i x
    rw [eq_inv_mul_iff_mul_eq₀ (Real.rpow_pos_of_pos hL _).ne']
    exact h.symm
  rw [sa12w2_partialDeriv_lift, show Torus.lift (fun y => sa12w2_dens L μt y *
      (Torus.matVec ((L ^ (-s - 2)) • M).transpose (Torus.grad u y)) i) =
      fun x => (L ^ (s + 1 - d))⁻¹ * Ξ i (L • x) from funext hlift]
  have hdil := sa12w2_fderiv_dil ((hΞs i).of_le (by simp)) hL.ne' w (EuclideanSpace.single i (1 : ℝ))
  have hdiffΞ : DifferentiableAt ℝ (fun x : Euc d => Ξ i (L • x)) w :=
    (((hΞs i).comp (contDiff_const_smul L)).differentiable (by simp)) w
  rw [fderiv_const_mul hdiffΞ, smul_apply, hdil, hexp, smul_eq_mul]
  have : L ^ (s + 1 - d) ≠ 0 := (Real.rpow_pos_of_pos hL _).ne'
  field_simp

end HRS.PDE.SA12W2
