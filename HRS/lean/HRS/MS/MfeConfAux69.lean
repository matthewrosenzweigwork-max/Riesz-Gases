import HRS.MS.MfeConfAux68
import HRS.Whole.MovtrAux2

/-!
# S.B.1, packet F8 (part 1): the truncated kernels `IsP4Kernel` are regular admissible kernels

For `k` with `IsP4Kernel d s r₀ k` (the level-`M` kernels of the regularised particle system):

* `sb1_lv_norm_fderiv`: `‖fderiv k z‖ = ‖gradient k z‖`;
* `sb1_lv_grad_bound`: `‖fderiv k z‖ ≤ Lg` for a constant `Lg` (the gradient is `0` at the origin and Lipschitz,
  hence `≤ L r₀` on the ball, and equals `∇g` outside, where `‖∇g‖ ≤ σ r₀^{-s-1}`);
* `sb1_lv_hess_bound`: `‖D² k‖ ≤ L` (the gradient is Lipschitz);
* `sb1_lv_kerR`: `Sb1KerR d k Lg`.
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d : ℕ}

theorem sb1_lv_norm_fderiv (k : Euc d → ℝ) (z : Euc d) : ‖fderiv ℝ k z‖ = ‖gradient k z‖ := by
  unfold gradient
  rw [LinearIsometryEquiv.norm_map]

theorem sb1_lv_grad_zero {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) : gradient k 0 = 0 := by
  have h := p4k_grad_odd (hk.smooth.differentiable (by norm_num)) hk.even 0
  simp only [neg_zero] at h
  have h2 : (2 : ℝ) • gradient k 0 = 0 := by
    rw [two_smul]; nth_rw 2 [h]; exact add_neg_cancel _
  exact (smul_eq_zero.1 h2).resolve_left (by norm_num)

theorem sb1_lv_grad_far {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) {x : Euc d} (hx : r₀ < ‖x‖) :
    gradient k x = gradient (Whole.rieszKernel d s) x := by
  have hev : k =ᶠ[𝓝 x] Whole.rieszKernel d s := by
    have : {y : Euc d | r₀ < ‖y‖} ∈ 𝓝 x := (isOpen_lt continuous_const continuous_norm).mem_nhds hx
    filter_upwards [this] with y hy using hk.eq_far y hy.le
  unfold gradient
  rw [hev.fderiv_eq]

theorem sb1_lv_grad_bound {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) (hs0 : 0 ≤ s) :
    ∃ Lg : ℝ, 0 ≤ Lg ∧ ∀ z, ‖fderiv ℝ k z‖ ≤ Lg := by
  obtain ⟨L, hL⟩ := hk.lipGrad
  have hr0 := hk.scale.1
  have hσ : 0 ≤ Whole.movtr_sigma s := by unfold Whole.movtr_sigma; split_ifs <;> linarith
  refine ⟨max (L * r₀) (Whole.movtr_sigma s * r₀ ^ (-s - 1)), le_max_of_le_left (by positivity), fun z => ?_⟩
  rw [sb1_lv_norm_fderiv]
  by_cases hz : ‖z‖ ≤ r₀
  · refine le_max_of_le_left ?_
    have := hL.dist_le_mul z 0
    rw [dist_eq_norm, dist_eq_norm, sb1_lv_grad_zero hk, sub_zero, sub_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_left hz L.2)
  · refine le_max_of_le_right ?_
    replace hz := not_le.1 hz
    rw [sb1_lv_grad_far hk hz]
    have := Whole.movtr_rieszKernelGrad_norm (d := d) s hs0 (norm_pos_iff.1 (hr0.trans hz))
    change ‖gradient (Whole.rieszKernel d s) z‖ ≤ _
    have e : gradient (Whole.rieszKernel d s) z = Whole.rieszKernelGrad d s z := rfl
    rw [e, this]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hr0 hz.le (by linarith)) hσ

theorem sb1_lv_lip_fderiv {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) :
    ∃ L : ℝ≥0, LipschitzWith L (fderiv ℝ k) := by
  obtain ⟨L, hL⟩ := hk.lipGrad
  refine ⟨L, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have := hL.dist_le_mul x y
  rw [dist_eq_norm, dist_eq_norm] at this ⊢
  have e : gradient k x - gradient k y = (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ k x - fderiv ℝ k y) := by
    unfold gradient; simp
  rw [e, LinearIsometryEquiv.norm_map] at this
  exact this

theorem sb1_lv_hess_bound {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) :
    ∃ L2 : ℝ, 0 ≤ L2 ∧ ∀ z, ‖fderiv ℝ (fderiv ℝ k) z‖ ≤ L2 := by
  obtain ⟨L, hL⟩ := sb1_lv_lip_fderiv hk
  refine ⟨L, L.2, fun z => norm_fderiv_le_of_lipschitz ℝ hL⟩

theorem sb1_lv_kerR {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) (hs0 : 0 ≤ s) :
    ∃ Lg : ℝ, Sb1KerR d k Lg := by
  obtain ⟨Lg, -, h⟩ := sb1_lv_grad_bound hk hs0
  exact ⟨Lg, hk.smooth, hk.even, h⟩

end HRS.MS.MfeConf
