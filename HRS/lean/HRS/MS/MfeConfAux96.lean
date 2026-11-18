import HRS.MS.MfeConfAux95

/-!
# S.B.1, packet F8 (part 28): bounds of `Ġ`, of `∂_jρ`, and of `u - v` along the clamped trajectory
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section Traj

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ) (hT : 0 ≤ T)
  {r₀ : ℝ} {k : Euc d → ℝ}

include H hT

theorem sb1_lv_gd_bound (hk4 : IsP4Kernel d D.s r₀ k) (s : ℝ) (x : Euc d) :
    |sb1_lv_cv k (sb1At D hT ρ s) x| ≤ sb1CGd d D.s (sb1CA D B C C3) * (1 + ‖x‖) :=
  (sb1_Gd_facts H (sb1KerU_of_p4 H.tr.hs0 hk4) (sb1_lv_cl'_mem hT s) x).2

theorem sb1_lv_gd_lip (hk4 : IsP4Kernel d D.s r₀ k) {Lg : ℝ} (hL : ∀ z, ‖fderiv ℝ k z‖ ≤ Lg) (s : ℝ) (x y : Euc d) :
    |sb1_lv_cv k (sb1At D hT ρ s) x - sb1_lv_cv k (sb1At D hT ρ s) y| ≤
      Lg * ‖x - y‖ * (sb1CA D B C C3 * ∫ z : Euc d, sb1w ((d : ℝ) + 2) z) := by
  obtain ⟨A, hA⟩ := sb1_lv_gr_k hk4 H.tr.hs0
  have hd := H.tr.hd
  have hw := sb1w_int hd (p := (d : ℝ) + 2) (by linarith)
  have hwm := sb1w_mom hd
  have hCA := H.CA_nonneg
  have hle := sb1_lv_At_le H hT s
  have hm : AEStronglyMeasurable (sb1At D hT ρ s) volume :=
    ((sb1_lv_curry_x (F := fun s x => sb1At D hT ρ s x) (sb1At_cont H.tr hT) s)).aestronglyMeasurable
  have h1 : Integrable (sb1At D hT ρ s) :=
    (hw.const_mul (sb1CA D B C C3)).mono' hm (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hle y)
  have h2 : Integrable (fun y => |sb1At D hT ρ s y| * ‖y‖) := by
    refine (hwm.const_mul (sb1CA D B C C3)).mono' (hm.norm.mul (continuous_norm.aestronglyMeasurable)) (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _))]
    have := mul_le_mul_of_nonneg_right (hle y) (norm_nonneg y)
    linarith
  have := sb1_lv_cv_lip hA (fun z z' => sb1_lv_k_lip hk4.smooth hL z z') hm h1 h2 x y
  refine this.trans ?_
  have hint : ∫ z, |sb1At D hT ρ s z| ≤ sb1CA D B C C3 * ∫ z : Euc d, sb1w ((d : ℝ) + 2) z := by
    rw [← integral_const_mul]
    exact integral_mono h1.abs (hw.const_mul _) (fun z => hle z)
  have hLg : 0 ≤ Lg := (norm_nonneg _).trans (hL 0)
  exact mul_le_mul_of_nonneg_left hint (by positivity)

theorem sb1_lv_dh_facts (s : ℝ) (j : Fin d) :
    Integrable (fun y => fderiv ℝ (sb1_lv_rb hT ρ s) y (sb1e j)) ∧
    Integrable (fun y => |fderiv ℝ (sb1_lv_rb hT ρ s) y (sb1e j)| * ‖y‖) ∧
    ∫ y, |fderiv ℝ (sb1_lv_rb hT ρ s) y (sb1e j)| ≤ C3 * ∫ z : Euc d, sb1w ((d : ℝ) + 2) z := by
  have hd := H.tr.hd
  have hw := sb1w_int hd (p := (d : ℝ) + 2) (by linarith)
  have hwm := sb1w_mom hd
  have hle := sb1_lv_drb_le H hT s j
  have hdc : Continuous fun y => fderiv ℝ (sb1_lv_rb hT ρ s) y (sb1e j) :=
    sb1_lv_curry_x (F := fun s y => fderiv ℝ (sb1_lv_rb hT ρ s) y (sb1e j)) (sb1_lv_drb_cont H hT j) s
  have h1 : Integrable (fun y => fderiv ℝ (sb1_lv_rb hT ρ s) y (sb1e j)) :=
    (hw.const_mul C3).mono' hdc.aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hle y)
  refine ⟨h1, ?_, ?_⟩
  · refine (hwm.const_mul C3).mono' (hdc.abs.aestronglyMeasurable.mul continuous_norm.aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _))]
    have := mul_le_mul_of_nonneg_right (hle y) (norm_nonneg y)
    linarith
  · rw [← integral_const_mul]
    exact integral_mono h1.abs (hw.const_mul _) (fun z => hle z)

theorem sb1_lv_e_norm (hk4 : IsP4Kernel d D.s r₀ k) {Lg : ℝ} (hRg : Sb1KerR d k Lg) (s : ℝ) (x : Euc d) :
    ‖sb1_lv_U D k hT ρ s x - Whole.mfeTransportW D (sb1_lv_rb hT ρ s) x‖ ≤ d * (Lg + sb1BF d D.s C) := by
  refine (sb1_lv_norm_le_sum _).trans ?_
  calc ∑ j, |(sb1_lv_U D k hT ρ s x - Whole.mfeTransportW D (sb1_lv_rb hT ρ s) x) j| ≤
        ∑ j : Fin d, (Lg + sb1BF d D.s C) := by
        refine Finset.sum_le_sum fun j _ => ?_
        simp only [PiLp.sub_apply]
        have := sb1_lv_u_sub_v hk4 H.tr.hd H.tr.hs0 H.tr.hsd hRg H.tr.V (sb1_lv_rb_rho H hT s)
          (sb1_lv_rb_slice H hT s) (sb1_lv_rb_pos H hT s) x j
        change |sb1_lv_u D k (sb1_lv_rb hT ρ s) x j - Whole.mfeTransportW D (sb1_lv_rb hT ρ s) x j| ≤ _
        rw [this]
        exact (abs_sub _ _).trans (add_le_add (sb1_lv_a_bound hk4 H.tr.hd H.tr.hs0 H.tr.hsd hRg hRg.gbd (sb1_lv_rb_rho H hT s) j x)
          (sb1_lv_F_bound H.tr.hd H.tr.hs0 H.tr.hsd (sb1_lv_rb_slice H hT s) j x))
    _ = _ := by simp; ring

end Traj

end HRS.MS.MfeConf
