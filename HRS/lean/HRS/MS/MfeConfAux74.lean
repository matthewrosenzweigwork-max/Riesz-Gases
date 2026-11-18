import HRS.MS.MfeConfAux73

/-!
# S.B.1, packet F8 (part 6): the divergence of the force `F = ∇g * ρ` is Lipschitz

For a slice `h` (`Sb1Slice d C h`, so `h ∈ C³` with decaying derivatives up to order `3`), `x ↦ ∂_kF_k(x)` has derivative
`rgT κ_k (D²h)` which is bounded (`rg_norm_T_le`), hence `div F = ∑_k ∂_kF_k` is Lipschitz (`sb1_lv_divF_lip`).
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.RdGen
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d : ℕ}

/-- the bound of `D(∂F)` -/
def sb1_lv_cdF (d : ℕ) (s C : ℝ) : ℝ :=
  Whole.movtr_sigma s * (C * rgNear d s + 4 ^ (s + 1) * C * rgW d)

/-- evaluation commutes with the cancellation-convention convolution -/
theorem sb1_lv_rgT_apply (hd : 1 ≤ d) {s σ : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {κ : Euc d → ℝ}
    (hκ : RgKer d s σ κ) {g : Euc d → (Euc d →L[ℝ] ℝ)} (hg : Differentiable ℝ g) {b0 b1 : ℝ} (hb0 : 0 ≤ b0)
    (hb1 : 0 ≤ b1) (h0 : ∀ y, ‖g y‖ ≤ b0 * (1 + ‖y‖) ^ (-((d : ℝ) + 1)))
    (h1 : ∀ y, ‖fderiv ℝ g y‖ ≤ b1) (x v : Euc d) :
    rgT κ g x v = rgT κ (fun y => g y v) x := by
  unfold rgT
  rw [ContinuousLinearMap.integral_apply (rg_integrable hd hs0 hsd hκ hg hb0 hb1 h0 h1 x)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [rgR]
  split_ifs <;> simp

/-- scalar form of `∂_kF_k`: `∂_k F_k = rgT κ_k (∂_k h)` -/
theorem sb1_lv_dF_scalar (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {C : ℝ} {h : Euc d → ℝ}
    (S : Sb1Slice d C h) (k : Fin d) (x : Euc d) :
    fderiv ℝ (sb1F d s h k) x (sb1e k) =
      rgT (fun z => (Whole.rieszKernelGrad d s z) k) (fun y => fderiv ℝ h y (sb1e k)) x := by
  obtain ⟨hc, h0, h1, h1', h2', -⟩ := sb1_slice_facts S
  rw [(sb1F_fderiv hd hs0 hsd S k x).fderiv]
  exact sb1_lv_rgT_apply hd hs0 hsd (rgKerComp_ok hs0 k)
    ((hc.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)) S.C_nonneg S.C_nonneg h1 h2' x (sb1e k)

theorem sb1_lv_decay_g1 {C : ℝ} {h : Euc d → ℝ} (S : Sb1Slice d C h) (k : Fin d) :
    RgDecay 2 (fun _ => C) (fun y => fderiv ℝ h y (sb1e k)) := by
  have hf : ContDiff ℝ 2 (fderiv ℝ h) := S.decay.1.fderiv_right (m := 2) (by norm_num)
  refine ⟨hf.clm_apply contDiff_const, fun l hl y => ?_⟩
  have h1 := norm_iteratedFDeriv_clm_apply_const (c := sb1e k) (x := y) (hf.contDiffAt) (n := l)
    (by exact_mod_cast hl)
  have h3 : ‖sb1e k‖ = 1 := by simp [sb1e]
  rw [h3, one_mul, norm_iteratedFDeriv_fderiv] at h1
  exact h1.trans (S.decay.2 (l + 1) (by omega) y)

theorem sb1_lv_divF_lip (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {C : ℝ} {h : Euc d → ℝ}
    (S : Sb1Slice d C h) (x x' : Euc d) :
    |∑ k, fderiv ℝ (sb1F d s h k) x (sb1e k) - ∑ k, fderiv ℝ (sb1F d s h k) x' (sb1e k)| ≤
      d * sb1_lv_cdF d s C * ‖x - x'‖ := by
  rw [← Finset.sum_sub_distrib]
  have hw : ∀ y : Euc d, (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ 1 := by
    intro y
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y])
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hk : ∀ k : Fin d, |fderiv ℝ (sb1F d s h k) x (sb1e k) - fderiv ℝ (sb1F d s h k) x' (sb1e k)| ≤
      sb1_lv_cdF d s C * ‖x - x'‖ := by
    intro k
    have hdec := sb1_lv_decay_g1 S k
    set g1 : Euc d → ℝ := fun y => fderiv ℝ h y (sb1e k) with hg1
    have hD : ∀ y, HasFDerivAt (fun y => fderiv ℝ (sb1F d s h k) y (sb1e k))
        (rgT (fun z => (Whole.rieszKernelGrad d s z) k) (fderiv ℝ g1) y) y := by
      intro y
      have e : (fun y => fderiv ℝ (sb1F d s h k) y (sb1e k)) =
          rgT (fun z => (Whole.rieszKernelGrad d s z) k) g1 :=
        funext fun y => sb1_lv_dF_scalar hd hs0 hsd S k y
      rw [e]
      exact rg_hasFDerivAt_decay hd hs0 hsd (rgKerComp_ok hs0 k) (by norm_num : 2 ≤ 2) (fun _ => S.C_nonneg)
        hdec y
    have hb : ∀ y ∈ (Set.univ : Set (Euc d)), ‖rgT (fun z => (Whole.rieszKernelGrad d s z) k) (fderiv ℝ g1) y‖ ≤
        sb1_lv_cdF d s C := by
      intro y _
      have hg1d : ContDiff ℝ 2 g1 := hdec.1
      have h0 : ∀ y, ‖fderiv ℝ g1 y‖ ≤ C * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := fun y => by
        rw [← norm_iteratedFDeriv_one]; exact hdec.2 1 (by norm_num) y
      have h1 : ∀ y, ‖fderiv ℝ (fderiv ℝ g1) y‖ ≤ C := fun y => by
        rw [sb1_norm_fderiv_fderiv]
        exact (hdec.2 2 le_rfl y).trans (mul_le_of_le_one_right S.C_nonneg (hw y))
      exact rg_norm_T_le hd hs0 hsd (rgKerComp_ok hs0 k)
        ((hg1d.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) S.C_nonneg S.C_nonneg h0 h1 y
    have := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := fun y => fderiv ℝ (sb1F d s h k) y (sb1e k))
      (s := Set.univ) (C := sb1_lv_cdF d s C) (fun y _ => (hD y).hasFDerivWithinAt) hb convex_univ
      (Set.mem_univ x') (Set.mem_univ x)
    rw [← Real.norm_eq_abs]
    exact this
  calc |∑ k, (fderiv ℝ (sb1F d s h k) x (sb1e k) - fderiv ℝ (sb1F d s h k) x' (sb1e k))|
      ≤ ∑ k, |fderiv ℝ (sb1F d s h k) x (sb1e k) - fderiv ℝ (sb1F d s h k) x' (sb1e k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin d, sb1_lv_cdF d s C * ‖x - x'‖ := Finset.sum_le_sum fun k _ => hk k
    _ = d * sb1_lv_cdF d s C * ‖x - x'‖ := by
        simp [Finset.sum_const]; ring

end HRS.MS.MfeConf
