import HRS.MS.UniqN4bB

/-!
# N4b of `UniqPlan.md`, part C: far-field bounds for `H_i = g * ∂_iψ` from a separation hypothesis

These are the versions of `n0_far_bound` / `n0_far_grad_bound` in which the geometry `n0_far_geom`
is replaced by the hypothesis `δ ≤ ‖y - x‖` for all `x ∈ tsupport ψ`:

* `n4b_far_H`: `|H_i(y)| ≤ max(1,s) δ^{-s-1} ‖ψ‖₁`;
* `n4b_far_dH`: `|∂_j H_i(y)| ≤ max(1,s)(s+3) δ^{-s-2} ‖ψ‖₁`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN4b

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqN0

variable {d : ℕ}

theorem n4b_notMem {ψ : Euc d → ℝ} {δ : ℝ} (hδ : 0 < δ) {y : Euc d}
    (hy : ∀ x ∈ tsupport ψ, δ ≤ ‖y - x‖) : y ∉ tsupport ψ := fun hmem => by
  have := hy y hmem
  simp at this
  linarith

theorem n4b_far_H {s : ℝ} (hs0 : 0 ≤ s) (i : Fin d) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) {δ : ℝ} (hδ : 0 < δ) {y : Euc d}
    (hy : ∀ x ∈ tsupport ψ, δ ≤ ‖y - x‖) :
    |kernelConvDeriv d s i ψ y| ≤ (max 1 s * δ ^ (-s - 1)) * ∫ x, |ψ x| := by
  have hyn := n4b_notMem hδ hy
  rw [n0_kcd_eq_gradConv i hψ hψc hyn]
  have hint : Integrable (fun x => |ψ x|) volume :=
    (hψ.continuous.integrable_of_hasCompactSupport hψc).abs
  have hK : ∀ x, ψ x ≠ 0 → |rieszKernelGrad d s (y - x) i| ≤ max 1 s * δ ^ (-s - 1) := by
    intro x hx
    have hxt : x ∈ tsupport ψ := subset_tsupport ψ hx
    have hge := hy x hxt
    have hpos : 0 < ‖y - x‖ := lt_of_lt_of_le hδ hge
    have hne : y - x ≠ 0 := norm_pos_iff.1 hpos
    rw [n0_gradRK s i hne]
    refine (n0_qH_bound hs0 i hne).trans ?_
    have h1 : ‖y - x‖ ^ (-s - 1) ≤ δ ^ (-s - 1) :=
      Real.rpow_le_rpow_of_nonpos hδ hge (by linarith)
    gcongr
  have hbd : ∀ x, ‖rieszKernelGrad d s (y - x) i * ψ x‖ ≤
      (max 1 s * δ ^ (-s - 1)) * |ψ x| := by
    intro x
    by_cases hx : ψ x = 0
    · simp [hx]
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hK x hx) (abs_nonneg _)
  have := norm_integral_le_of_norm_le (hint.const_mul _) (Eventually.of_forall hbd)
  rw [integral_const_mul] at this
  simpa [Real.norm_eq_abs] using this

theorem n4b_far_dH {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i j : Fin d) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) {δ : ℝ} (hδ : 0 < δ) {y : Euc d}
    (hy : ∀ x ∈ tsupport ψ, δ ≤ ‖y - x‖) :
    |fderiv ℝ (kernelConvDeriv d s i ψ) y (EuclideanSpace.single j (1 : ℝ))| ≤
      (max 1 s * (s + 3) * δ ^ (-s - 2)) * ∫ x, |ψ x| := by
  have hyn := n4b_notMem hδ hy
  have hl := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have hF1 : ContDiff ℝ 1 (D1 i ψ) := D1_contDiff hψ i
  have hF1c : HasCompactSupport (D1 i ψ) := D1_supp hψc i
  have hsupp1 : Function.support (D1 i ψ) ⊆ tsupport ψ := fun x hx => by
    have : fderiv ℝ ψ x ≠ 0 := fun h0 => hx (by simp [D1, h0])
    exact (support_fderiv_subset (𝕜 := ℝ)) (Function.mem_support.2 this)
  have hy1 : y ∉ tsupport (D1 i ψ) := fun hmem =>
    hyn ((closure_minimal hsupp1 isClosed_closure : tsupport (D1 i ψ) ⊆ tsupport ψ) hmem)
  have hD : fderiv ℝ (kernelConvDeriv d s i ψ) y (EuclideanSpace.single j (1 : ℝ)) =
      kernelConvDeriv d s j (D1 i ψ) y := by
    have := convFun_D1 hl hF1 hF1c j y
    exact this
  rw [hD, n0_kcd_eq_gradConv j hF1 hF1c hy1]
  have hne : ∀ x ∈ tsupport ψ, y - x ≠ 0 := fun x hx h0 => hyn (by
    rw [sub_eq_zero] at h0; rwa [h0])
  have hk : ∀ x ∈ tsupport ψ, ContDiffAt ℝ 1 (fun x => q09_H s j (y - x)) x := fun x hx =>
    ((n0_qH_contDiffAt s j (hne x hx)).of_le (by exact_mod_cast le_top)).comp x
      (contDiffAt_const.sub contDiffAt_id)
  have hpt : ∀ x, rieszKernelGrad d s (y - x) j * D1 i ψ x = q09_H s j (y - x) * D1 i ψ x := by
    intro x
    by_cases hx : x ∈ tsupport ψ
    · rw [n0_gradRK s j (hne x hx)]
    · have : D1 i ψ x = 0 := by
        have h0 : fderiv ℝ ψ x = 0 := by
          by_contra h
          exact hx ((support_fderiv_subset (𝕜 := ℝ)) (Function.mem_support.2 h))
        simp [D1, h0]
      simp [this]
  simp_rw [hpt]
  have hibp := n0_ibp (hψ.of_le (by norm_num)) hψc hk (EuclideanSpace.single i (1 : ℝ))
  have hIBP : ∫ x, q09_H s j (y - x) * D1 i ψ x = -∫ x, fderiv ℝ (fun x => q09_H s j (y - x)) x
      (EuclideanSpace.single i (1 : ℝ)) * ψ x := hibp
  rw [hIBP]
  have hint : Integrable (fun x => |ψ x|) volume :=
    (hψ.continuous.integrable_of_hasCompactSupport hψc).abs
  have hder : ∀ x ∈ tsupport ψ, fderiv ℝ (fun x => q09_H s j (y - x)) x
      (EuclideanSpace.single i (1 : ℝ)) = -(q09_DH s j (y - x) (EuclideanSpace.single i (1 : ℝ))) := by
    intro x hx
    have hd : HasFDerivAt (fun x => q09_H s j (y - x))
        ((q09_DH s j (y - x)).comp (0 - ContinuousLinearMap.id ℝ (Euc d))) x :=
      (q09_H_hasFDerivAt s j (hne x hx)).comp x ((hasFDerivAt_const y x).sub (hasFDerivAt_id x))
    rw [hd.fderiv]
    simp
  have hbd : ∀ x, ‖fderiv ℝ (fun x => q09_H s j (y - x)) x (EuclideanSpace.single i (1 : ℝ)) * ψ x‖ ≤
      (max 1 s * (s + 3) * δ ^ (-s - 2)) * |ψ x| := by
    intro x
    by_cases hx : ψ x = 0
    · simp [hx]
    · have hxt : x ∈ tsupport ψ := subset_tsupport ψ hx
      have hge := hy x hxt
      have hpos : 0 < ‖y - x‖ := lt_of_lt_of_le hδ hge
      rw [hder x hxt, norm_mul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      refine (n0_qDH_bound hs0 j i (hne x hxt)).trans ?_
      have h1 : ‖y - x‖ ^ (-s - 2) ≤ δ ^ (-s - 2) :=
        Real.rpow_le_rpow_of_nonpos hδ hge (by linarith)
      have hc : 0 ≤ max 1 s * (s + 3) :=
        mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (by linarith)
      gcongr
  have := norm_integral_le_of_norm_le (hint.const_mul _) (Eventually.of_forall hbd)
  rw [integral_const_mul] at this
  rw [abs_neg]
  simpa [Real.norm_eq_abs] using this

end HRS.MS.UniqN4b
