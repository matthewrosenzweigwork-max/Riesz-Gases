import HRS.MS.MfeConfAux126

/-!
# S.B.1 (SB5), R1 (part 4): the estimate E1 (divergence of the force defect)

`sb1_dEM_bound`: for `φ_i = ∂_iρ`, `|rgT (∂_jk_M) φ_i - rgT (∂_jg) φ_i| ≤ (A+σ)·4·2^{d+3}·C₃·η_M·(1+|x|)^{-(d+3)}`.
`sb1_E1`: `|∑_j cv(h_jj) ρ - ∑_j ∂_jF_j| ≤ d·` the same bound.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.RdGen HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d : ℕ}

section Deriv

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ)

include H

theorem sb1_phi_facts {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (i : Fin d) :
    Differentiable ℝ (fun y => fderiv ℝ (ρ r) y (sb1e i)) ∧
    (∀ y, |fderiv ℝ (ρ r) y (sb1e i)| ≤ C3 * sb1w ((d : ℝ) + 3) y) ∧
    (∀ y, ‖fderiv ℝ (fun y => fderiv ℝ (ρ r) y (sb1e i)) y‖ ≤ C3 * sb1w ((d : ℝ) + 3) y) := by
  have hc := (H.tr.slice r hr).decay.1
  have hf : ContDiff ℝ 2 (fderiv ℝ (ρ r)) := hc.fderiv_right (m := 2) (by norm_num)
  refine ⟨(hf.clm_apply contDiff_const).differentiable (by norm_num),
    fun y => (sb1_apply_single_le _ i).trans (H.drho_le hr y), fun y => ?_⟩
  have h1 := norm_iteratedFDeriv_clm_apply_const (c := sb1e i) (x := y) (hf.contDiffAt) (n := 1)
    (by exact_mod_cast (by norm_num : 1 ≤ 2))
  have h3 : ‖sb1e i‖ = 1 := by simp [sb1e]
  rw [h3, one_mul, norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at h1
  exact h1.trans (by simpa using H.dec r hr 2 (by norm_num) y)

theorem sb1_dEM_bound (hs0 : 0 ≤ D.s) (M : ℕ) {A : ℝ} (hA : ∀ j : Fin d, RgKer d D.s A (sb1_lv_dk (sb1kM d D.s M) j))
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (x : Euc d) (i j : Fin d) :
    |rgT (sb1_lv_dk (sb1kM d D.s M) j) (fun y => fderiv ℝ (ρ r) y (sb1e i)) x -
        rgT (fun z => (rieszKernelGrad d D.s z) j) (fun y => fderiv ℝ (ρ r) y (sb1e i)) x| ≤
      (A + Whole.movtr_sigma D.s) * ((4 * 2 ^ ((d : ℝ) + 3)) * C3 * sb1w ((d : ℝ) + 3) x) *
        sb1eta d D.s (1 / ((M : ℝ) + 1)) := by
  obtain ⟨hd', h0, h1⟩ := sb1_phi_facts H hr i
  exact sb1_rgT_diff H.tr.hd H.tr.hs0 H.tr.hsd (hA j) (rgKerComp_ok H.tr.hs0 j) (sb1_rM_le M)
    (fun z hz => sb1_dk_supp hs0 M j hz) hd' (b := C3) h0 h1 x

end Deriv

section E1

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ)

include H

theorem sb1_E1 (M : ℕ) {A : ℝ} (hA : ∀ j : Fin d, RgKer d D.s A (sb1_lv_dk (sb1kM d D.s M) j))
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (x : Euc d) :
    |∑ j, sb1_lv_cv (sb1_lv_hjj (sb1kM d D.s M) j) (ρ r) x - ∑ j, fderiv ℝ (sb1F d D.s (ρ r) j) x (sb1e j)| ≤
      d * ((A + Whole.movtr_sigma D.s) * ((4 * 2 ^ ((d : ℝ) + 3)) * C3 * sb1w ((d : ℝ) + 3) x) *
        sb1eta d D.s (1 / ((M : ℝ) + 1))) := by
  have hs0 := H.tr.hs0
  have hk4 := sb1kM_isKernel (d := d) D.s hs0 M
  obtain ⟨Lg, hRg⟩ := sb1_lv_kerR hk4 hs0
  obtain ⟨L2, -, hL2⟩ := sb1_lv_hess_bound hk4
  have hT : 0 ≤ T := hr.1.trans hr.2
  have hrb : sb1_lv_rb hT ρ r = ρ r := sb1_lv_rb_mem hT ρ hr
  have hρd : Differentiable ℝ (ρ r) := (H.tr.slice r hr).decay.1.differentiable (by norm_num)
  have hρ' : Continuous (fderiv ℝ (ρ r)) := (H.tr.slice r hr).decay.1.continuous_fderiv (by norm_num)
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ j : Fin d, sb1_lv_cv (sb1_lv_hjj (sb1kM d D.s M) j) (ρ r) x -
      fderiv ℝ (sb1F d D.s (ρ r) j) x (sb1e j) =
      rgT (sb1_lv_dk (sb1kM d D.s M) j) (fun y => fderiv ℝ (ρ r) y (sb1e j)) x -
        rgT (fun z => (rieszKernelGrad d D.s z) j) (fun y => fderiv ℝ (ρ r) y (sb1e j)) x := by
    intro j
    have hint : Integrable (fun y => fderiv ℝ (ρ r) y (sb1e j)) := by
      have := (sb1_lv_dh_facts H hT r j).1
      rwa [hrb] at this
    rw [sb1_lv_hjj_ibp hk4 hRg.gbd hL2 (H.rho H.tr.hd hr) hρd hρ' j hint x,
      sb1_cv_eq_rgT (sb1_lv_dk_cont hk4.smooth j).measurable (sb1_lv_dk_bound hRg.gbd j)
        (fun z => sb1_fderiv_odd (hk4.smooth.differentiable (by norm_num)) hk4.even z (sb1e j)) hint x,
      sb1_lv_dF_scalar H.tr.hd hs0 H.tr.hsd (H.tr.slice r hr) j x]
  simp only [hterm]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j : Fin d, |rgT (sb1_lv_dk (sb1kM d D.s M) j) (fun y => fderiv ℝ (ρ r) y (sb1e j)) x -
        rgT (fun z => (rieszKernelGrad d D.s z) j) (fun y => fderiv ℝ (ρ r) y (sb1e j)) x|
      ≤ ∑ _j : Fin d, ((A + Whole.movtr_sigma D.s) * ((4 * 2 ^ ((d : ℝ) + 3)) * C3 * sb1w ((d : ℝ) + 3) x) *
        sb1eta d D.s (1 / ((M : ℝ) + 1))) :=
        Finset.sum_le_sum fun j _ => sb1_dEM_bound H hs0 M hA hr x j j
    _ = _ := by simp

end E1

end HRS.MS.MfeConf
