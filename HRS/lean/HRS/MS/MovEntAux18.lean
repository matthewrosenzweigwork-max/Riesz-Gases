import HRS.MS.MovEntAux5
import HRS.MH.DualityRdA4
import HRS.Whole.MovtrAux9

/-!
# S6.6, packet P5 (part 1): the Itô drift of `N⁻¹∑|x_i|²` along the particle system

Namespace `HRS.MS.MovEnt`.  Deterministic algebra for the window estimate of clause (3):

* `s66_fderiv_normsq`, `s66_fderiv2_normsq`: derivatives of `x ↦ |x|²`.
* `s66_sum_fderiv2`: `∑_k D² f(σ_k,σ_k) = 4 β⁻¹ d` for `f = N⁻¹∑|x_i|²`.
* `s66_inner_drift`: for a collision-free configuration, `∑_i ⟨x_i, b_i(X)⟩ = -q∑|x_i|² + (σ_s/(2N))∑_{i≠j}|x_i-x_j|^{-s}`
  (the quadratic confinement, `M = -1`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovEnt

open HRS.Whole

variable {d : ℕ}

theorem s66_fderiv_normsq (x v : Euc d) :
    fderiv ℝ (fun y : Euc d => ‖y‖ ^ 2) x v = 2 * inner ℝ x v := by
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  rw [h.fderiv]
  simp [two_mul]

theorem s66_fderiv2_normsq (x u v : Euc d) :
    fderiv ℝ (fderiv ℝ (fun y : Euc d => ‖y‖ ^ 2)) x u v = 2 * inner ℝ u v := by
  have e : fderiv ℝ (fun y : Euc d => ‖y‖ ^ 2) = fun y => (2 : ℕ) • innerSL ℝ y := by
    funext y
    exact (hasStrictFDerivAt_norm_sq y).hasFDerivAt.fderiv
  rw [e]
  have h3 : HasFDerivAt (fun y : Euc d => (2 : ℕ) • innerSL ℝ y)
      ((2 : ℕ) • (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ)) x :=
    ((innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ).hasFDerivAt).const_smul (2 : ℕ)
  rw [h3.fderiv]
  simp [two_mul]
  rfl

theorem s66_sum_fderiv2 {N : ℕ} (hN : 0 < N) (D : WholeDyn d) (hinv : 0 ≤ D.invβ) (Y : EucConfig d N) :
    ∑ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ (HRS.sumLift N (fun x : Euc d => ‖x‖ ^ 2))) Y
        (HRS.MH.DualityRd.noiseDir D k) (HRS.MH.DualityRd.noiseDir D k) = 4 * D.invβ * d := by
  rw [HRS.MH.DualityRd.da2_sum_fderiv_fderiv D hinv (contDiff_norm_sq ℝ) Y]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h2 : ∀ (i : Fin N) (j : Fin d), fderiv ℝ (fderiv ℝ (fun x : Euc d => ‖x‖ ^ 2)) (Y i)
      (EuclideanSpace.single j 1) (EuclideanSpace.single j 1) = 2 := by
    intro i j
    rw [s66_fderiv2_normsq]
    simp
  simp only [h2]
  simp
  field_simp
  ring

theorem s66_fderiv_sumLift_normsq {N : ℕ} (Y u : EucConfig d N) :
    fderiv ℝ (HRS.sumLift N (fun x : Euc d => ‖x‖ ^ 2)) Y u =
      (N : ℝ)⁻¹ * ∑ i, 2 * inner ℝ (Y i) (u i) := by
  rw [HRS.fderiv_sumLift_apply ((contDiff_norm_sq ℝ : ContDiff ℝ 1 (fun x : Euc d => ‖x‖ ^ 2)).differentiable one_ne_zero) Y u]
  simp only [s66_fderiv_normsq]

theorem s66_dot_grad {s : ℝ} {z : Euc d} (hz : z ≠ 0) :
    inner ℝ z (rieszKernelGrad d s z) = -(movtr_sigma s * ‖z‖ ^ (-s)) := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [movtr_rieszKernelGrad_eq s hz, inner_smul_right, real_inner_self_eq_norm_sq]
  have : ‖z‖ ^ (-s - 2) * ‖z‖ ^ 2 = ‖z‖ ^ (-s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hzpos]
    norm_num
  calc -(movtr_sigma s * ‖z‖ ^ (-s - 2)) * ‖z‖ ^ 2 = -(movtr_sigma s * (‖z‖ ^ (-s - 2) * ‖z‖ ^ 2)) := by ring
    _ = _ := by rw [this]

theorem s66_grad_odd {s : ℝ} {z : Euc d} (hz : z ≠ 0) :
    rieszKernelGrad d s (-z) = -rieszKernelGrad d s z := by
  have hz' : -z ≠ 0 := neg_ne_zero.2 hz
  rw [movtr_rieszKernelGrad_eq s hz', movtr_rieszKernelGrad_eq s hz, norm_neg, smul_neg, neg_smul]

theorem s66_inner_drift {N : ℕ} (s q β : ℝ) (Y : EucConfig d N) (hY : Y ∉ eucCollisionSet d N) :
    ∑ i, inner ℝ (Y i) (particleDriftW (quadraticGradientDyn d s q β) Y i) =
      -q * ∑ i, ‖Y i‖ ^ 2 +
        movtr_sigma s / (2 * N) * ∑ i, ∑ j ∈ Finset.univ.erase i, ‖Y i - Y j‖ ^ (-s) := by
  have hne : ∀ i j, i ≠ j → Y i ≠ Y j := by
    intro i j hij hEq
    exact hY ⟨i, j, hij, hEq⟩
  set G : Fin N → Fin N → Euc d := fun i j => rieszKernelGrad d s (Y i - Y j) with hG
  have hdrift : ∀ i, inner ℝ (Y i) (particleDriftW (quadraticGradientDyn d s q β) Y i) =
      -(1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i, inner ℝ (Y i) (G i j) - q * ‖Y i‖ ^ 2 := by
    intro i
    unfold particleDriftW
    have hgrad : gradient (quadraticGradientDyn d s q β).V (Y i) = q • Y i := movtr_gradient_confinement q (Y i)
    have hM : ∀ v : Euc d, Torus.matVec (quadraticGradientDyn d s q β).M v = -v := by
      intro v; simp [quadraticGradientDyn, Torus.matVec]
    have hs : (quadraticGradientDyn d s q β).s = s := rfl
    simp only [hM, hgrad, hs, inner_sub_right, inner_smul_right, inner_sum, inner_neg_right,
      real_inner_self_eq_norm_sq]
    simp only [hG]
    rw [Finset.sum_neg_distrib]
    ring
  simp only [hdrift]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  -- the symmetrisation of `S = ∑_i ∑_{j ≠ i} ⟪Y i, G i j⟫`
  set S : ℝ := ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (Y i) (G i j) with hS
  have hcomm : S = ∑ j, ∑ i ∈ Finset.univ.erase j, inner ℝ (Y i) (G i j) := by
    rw [hS]
    refine Finset.sum_comm' ?_
    intro i j
    simp [Finset.mem_erase, and_comm, ne_comm]
  have hS2 : S = ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (Y j) (G j i) := by
    rw [hcomm]
  have hodd : ∀ i, ∀ j ∈ Finset.univ.erase i, G j i = -G i j := by
    intro i j hj
    have hji : j ≠ i := (Finset.mem_erase.1 hj).1
    simp only [hG]
    rw [← neg_sub, s66_grad_odd (sub_ne_zero.2 (hne i j hji.symm))]
  have hS3 : S = -∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (Y j) (G i j) := by
    rw [hS2, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hodd i j hj, inner_neg_right]
  have h2S : 2 * S = ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (Y i - Y j) (G i j) := by
    have : 2 * S = S + S := by ring
    rw [this]
    nth_rewrite 2 [hS3]
    rw [hS, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_sub_left]
  have hterm : ∀ i, ∀ j ∈ Finset.univ.erase i, inner ℝ (Y i - Y j) (G i j) =
      -(movtr_sigma s * ‖Y i - Y j‖ ^ (-s)) := by
    intro i j hj
    exact s66_dot_grad (sub_ne_zero.2 (hne i j (Finset.mem_erase.1 hj).1.symm))
  have h2S' : 2 * S = -(movtr_sigma s * ∑ i, ∑ j ∈ Finset.univ.erase i, ‖Y i - Y j‖ ^ (-s)) := by
    rw [h2S, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j hj => hterm i j hj
  have hNN : (N : ℝ) ≠ 0 ∨ N = 0 := by
    by_cases h : N = 0
    · exact Or.inr h
    · exact Or.inl (by exact_mod_cast h)
  rcases hNN with hN0 | hN0
  · have : S = -(movtr_sigma s * ∑ i, ∑ j ∈ Finset.univ.erase i, ‖Y i - Y j‖ ^ (-s)) / 2 := by linarith
    rw [this]
    field_simp
    ring
  · subst hN0
    simp
end HRS.MS.MovEnt

end
