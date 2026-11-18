import HRS.MS.MfeConfAux125

/-!
# S.B.1 (SB5), R1 (part 3): `e_j = rgT (∂_jk) ρ - rgT (∂_jg) ρ`, the kernel `∂_jk_M` and the estimate E0

`sb1_E0`: `‖e(x)‖ ≤ d K₀ η_M (1+|x|)^{-(d+3)}` for `k = k_M`, where `η_M = ∫_{|z| ≤ r_M} |z|^{-s} dz`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.RdGen HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d : ℕ}

section Ker

theorem sb1_dk_rgKer {s : ℝ} (hs0 : 0 ≤ s) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (M : ℕ) (j : Fin d), RgKer d s A (sb1_lv_dk (sb1kM d s M) j) := by
  obtain ⟨A, hA0, hA⟩ := sb1kM_grad_pow (d := d) s hs0
  refine ⟨A, hA0, fun M j => ⟨hA0, ?_, fun z hz => ?_⟩⟩
  · exact (sb1_lv_dk_cont (sb1kM_isKernel s hs0 M).smooth j).measurable
  · have := hA M z hz (sb1e j)
    have h1 : ‖sb1e j‖ = 1 := by simp [sb1e]
    rw [h1, mul_one] at this
    exact this

theorem sb1_dk_supp {s : ℝ} (hs0 : 0 ≤ s) (M : ℕ) (j : Fin d) {z : Euc d} (hz : 1 / ((M : ℝ) + 1) < ‖z‖) :
    sb1_lv_dk (sb1kM d s M) j z = (rieszKernelGrad d s z) j := by
  have hev : sb1kM d s M =ᶠ[𝓝 z] rieszKernel d s := by
    have : {y : Euc d | 1 / ((M : ℝ) + 1) < ‖y‖} ∈ 𝓝 z :=
      (isOpen_lt continuous_const continuous_norm).mem_nhds hz
    filter_upwards [this] with y hy using (sb1kM_isKernel (d := d) s hs0 M).eq_far y hy.le
  unfold sb1_lv_dk rieszKernelGrad
  rw [sb1_grad_apply, hev.fderiv_eq]

end Ker

section Defect

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ) (hT : 0 ≤ T)
  {r₀ : ℝ} {k : Euc d → ℝ}

include H hT

theorem sb1_e_eq_rgT (hk4 : IsP4Kernel d D.s r₀ k) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (x : Euc d) (j : Fin d) :
    sb1_lv_e D k hT ρ r x j =
      rgT (sb1_lv_dk k j) (ρ r) x - rgT (fun z => (rieszKernelGrad d D.s z) j) (ρ r) x := by
  obtain ⟨Lg, hRg⟩ := sb1_lv_kerR hk4 H.tr.hs0
  have hrb : sb1_lv_rb hT ρ r = ρ r := sb1_lv_rb_mem hT ρ hr
  have hee : sb1_lv_e D k hT ρ r x j = sb1_lv_a k (ρ r) j x - sb1F d D.s (ρ r) j x := by
    have := sb1_lv_u_sub_v hk4 H.tr.hd H.tr.hs0 H.tr.hsd hRg H.tr.V (sb1_lv_rb_rho H hT r)
      (sb1_lv_rb_slice H hT r) (sb1_lv_rb_pos H hT r) x j
    unfold sb1_lv_e sb1_lv_U
    rw [hrb] at this ⊢
    simpa using this
  rw [hee]
  have hS := H.tr.slice r hr
  have h1 : sb1_lv_a k (ρ r) j x = rgT (sb1_lv_dk k j) (ρ r) x := by
    unfold sb1_lv_a
    rw [sb1_lv_dG_eq hk4 H.tr.hd H.tr.hs0 H.tr.hsd hRg (H.rho H.tr.hd hr) j x]
    exact sb1_cv_eq_rgT (sb1_lv_dk_cont hk4.smooth j).measurable (sb1_lv_dk_bound hRg.gbd j)
      (fun z => sb1_fderiv_odd (hk4.smooth.differentiable (by norm_num)) hk4.even z (sb1e j)) (H.rho H.tr.hd hr).integrable x
  have h2 : sb1F d D.s (ρ r) j x = rgT (fun z => (rieszKernelGrad d D.s z) j) (ρ r) x := by
    rw [sb1F_eq_rgT H.tr.hd H.tr.hs0 H.tr.hsd hS j]
  rw [h1, h2]

/-- **E0**: the force defect is `η_M`-small, with the decay of `ρ` -/
theorem sb1_E0 (hs0 : 0 ≤ D.s) (M : ℕ) {A : ℝ} (hA : ∀ j : Fin d, RgKer d D.s A (sb1_lv_dk (sb1kM d D.s M) j))
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (x : Euc d) (j : Fin d) :
    |sb1_lv_e D (sb1kM d D.s M) hT ρ r x j| ≤
      (A + Whole.movtr_sigma D.s) * ((4 * 2 ^ ((d : ℝ) + 3)) * C3 * sb1w ((d : ℝ) + 3) x) *
        sb1eta d D.s (1 / ((M : ℝ) + 1)) := by
  rw [sb1_e_eq_rgT H hT (sb1kM_isKernel D.s hs0 M) hr x j]
  have hφd : Differentiable ℝ (ρ r) := (H.tr.slice r hr).decay.1.differentiable (by norm_num)
  have := sb1_rgT_diff H.tr.hd H.tr.hs0 H.tr.hsd (hA j) (rgKerComp_ok H.tr.hs0 j) (sb1_rM_le M)
    (fun z hz => sb1_dk_supp hs0 M j hz) hφd (b := C3)
    (fun y => by rw [abs_of_pos (H.pos r hr y)]; exact H.rho_le hr y) (fun y => H.drho_le hr y) x
  exact this

end Defect

end HRS.MS.MfeConf
