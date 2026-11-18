import HRS.MS.MovSchAux11

/-!
# S64 (S6.9), part 7: the directional derivative of the canonical Hamiltonian away from collisions

Namespace `HRS.MS.MovSch`, prefix `s64_`.  `s64_H_hasDeriv`: for a non-collision configuration `Z`,
`σ ↦ H_N(ℓ_{ik}(Z,σ))` has derivative `s64_drift d s q N i k Z = q Z_{ik} + N⁻¹ ∑_{j≠i} ∂_k g(Z_i - Z_j)` at `σ = 0`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovSch

open HRS.Whole
open HRS (Euc)

variable {d N : ℕ}

/-- No collisions. -/
def s64_NC (Z : EucConfig d N) : Prop := ∀ a b : Fin N, a ≠ b → Z a ≠ Z b

lemma s64_NC_of_not_mem {Z : EucConfig d N} (h : Z ∉ eucCollisionSet d N) : s64_NC Z := by
  intro a b hab hZ
  exact h ⟨a, b, hab, hZ⟩

lemma s64_not_mem_of_NC {Z : EucConfig d N} (h : s64_NC Z) : Z ∉ eucCollisionSet d N := by
  rintro ⟨a, b, hab, hZ⟩
  exact h a b hab hZ

lemma s64_g_contDiffAt (s : ℝ) {z : Euc d} (hz : z ≠ 0) : ContDiffAt ℝ ∞ (rieszKernel d s) z := by
  have hn : ContDiffAt ℝ ∞ (fun y : Euc d => ‖y‖) z := contDiffAt_norm ℝ hz
  have hnpos : ‖z‖ ≠ 0 := (norm_pos_iff.2 hz).ne'
  unfold rieszKernel
  by_cases h : s = 0
  · simp only [h, ite_true]
    exact (hn.log hnpos).neg
  · simp only [h, ite_false]
    exact hn.rpow_const_of_ne hnpos

lemma s64_g_diff (s : ℝ) {z : Euc d} (hz : z ≠ 0) : DifferentiableAt ℝ (rieszKernel d s) z :=
  (s64_g_contDiffAt s hz).differentiableAt (by simp)

/-- `G_k z = ∂_k g (z) = (∇g z)_k` is differentiable away from `0`. -/
lemma s64_G_diff (s : ℝ) (k : Fin d) {z : Euc d} (hz : z ≠ 0) :
    DifferentiableAt ℝ (fun y : Euc d => rieszKernelGrad d s y k) z := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ (rieszKernel d s)) z :=
    (s64_g_contDiffAt s hz).fderiv_right (m := 1) (by simp)
  have h2 : DifferentiableAt ℝ (fun y : Euc d => fderiv ℝ (rieszKernel d s) y (EuclideanSpace.single k (1 : ℝ))) z :=
    (h1.differentiableAt (by simp)).clm_apply (differentiableAt_const _)
  have : (fun y : Euc d => rieszKernelGrad d s y k) =
      fun y : Euc d => fderiv ℝ (rieszKernel d s) y (EuclideanSpace.single k (1 : ℝ)) := by
    funext y
    exact movtr_gradient_apply (rieszKernel d s) y k
  rw [this]
  exact h2

lemma s64_G_eq (s : ℝ) (k : Fin d) (z : Euc d) :
    rieszKernelGrad d s z k = fderiv ℝ (rieszKernel d s) z (EuclideanSpace.single k (1 : ℝ)) :=
  movtr_gradient_apply (rieszKernel d s) z k

lemma s64_G_odd (s : ℝ) (k : Fin d) {z : Euc d} (hz : z ≠ 0) :
    rieszKernelGrad d s (-z) k = - rieszKernelGrad d s z k := by
  have hz' : -z ≠ 0 := neg_ne_zero.2 hz
  have h1 : HasFDerivAt (rieszKernel d s) (fderiv ℝ (rieszKernel d s) (-z)) (-z) :=
    (s64_g_diff s hz').hasFDerivAt
  have h2 : HasFDerivAt (fun y : Euc d => rieszKernel d s (-y))
      ((fderiv ℝ (rieszKernel d s) (-z)).comp (-(ContinuousLinearMap.id ℝ (Euc d)))) z :=
    h1.comp z (hasFDerivAt_id z).neg
  have heven : (fun y : Euc d => rieszKernel d s (-y)) = rieszKernel d s := by
    funext y; unfold rieszKernel; simp [norm_neg]
  rw [heven] at h2
  have h3 := h2.fderiv
  rw [s64_G_eq, s64_G_eq, h3]
  simp

lemma s64_pair_hasDeriv (s : ℝ) {Z : EucConfig d N} {a b : Fin N} (hab : Z a ≠ Z b) (i : Fin N) (k : Fin d) :
    HasDerivAt (fun σ : ℝ => rieszKernel d s (s64_ell Z i k σ a - s64_ell Z i k σ b))
      ((if a = i then rieszKernelGrad d s (Z a - Z b) k else 0) -
        (if b = i then rieszKernelGrad d s (Z a - Z b) k else 0)) 0 := by
  have hz : Z a - Z b ≠ 0 := sub_ne_zero.2 hab
  set w : Euc d := (if a = i then EuclideanSpace.single k (1 : ℝ) else 0) -
    (if b = i then EuclideanSpace.single k (1 : ℝ) else 0) with hw
  have hfun : (fun σ : ℝ => s64_ell Z i k σ a - s64_ell Z i k σ b) = fun σ : ℝ => (Z a - Z b) + σ • w := by
    funext σ
    rw [s64_ell_apply, s64_ell_apply, hw, smul_sub]
    abel
  have hline : HasDerivAt (fun σ : ℝ => (Z a - Z b) + σ • w) w 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add (Z a - Z b)
    simpa using this
  have hg : HasFDerivAt (rieszKernel d s) (fderiv ℝ (rieszKernel d s) (Z a - Z b)) ((Z a - Z b) + (0 : ℝ) • w) := by
    simpa using (s64_g_diff s hz).hasFDerivAt
  have hcomp := hg.comp_hasDerivAt (0 : ℝ) hline
  rw [← hfun] at hcomp
  refine hcomp.congr_deriv ?_
  rw [hw, map_sub, s64_G_eq]
  by_cases h1 : a = i <;> by_cases h2 : b = i <;> simp [h1, h2]

end HRS.MS.MovSch

end
