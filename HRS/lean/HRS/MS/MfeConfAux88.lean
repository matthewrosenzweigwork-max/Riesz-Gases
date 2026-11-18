import HRS.MS.MfeConfAux87

/-!
# S.B.1, packet F8 (part 20): gradient, `C¹`, divergence continuity and time derivative of the one-body data
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d : ℕ}

section Traj

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ) (hT : 0 ≤ T)
  {r₀ : ℝ} {k : Euc d → ℝ}

include H hT

theorem sb1_lv_Psi_grad (hk4 : IsP4Kernel d D.s r₀ k) (s : ℝ) (x : Euc d) :
    HasFDerivAt (sb1_lv_Psi D k hT ρ s) (innerSL ℝ (-(sb1_lv_U D k hT ρ s x))) x := by
  obtain ⟨Lg, hRg⟩ := sb1_lv_kerR hk4 H.tr.hs0
  have hS := sb1_lv_rb_slice H hT s
  have h1 := sb1_lv_hasFDerivAt_psi hk4 H.tr.hd H.tr.hs0 H.tr.hsd hRg (sb1_lv_rb_rho H hT s)
    (sb1_lv_rb_pos H hT s) (hS.decay.1.differentiable (by norm_num)) (H.tr.V.c3.differentiable (by norm_num)) x
  have hd : DifferentiableAt ℝ (sb1_lv_psi D k (sb1_lv_rb hT ρ s)) x := h1.differentiableAt
  unfold sb1_lv_Psi sb1_lv_U sb1_lv_u
  rw [neg_neg]
  have : innerSL ℝ (gradient (sb1_lv_psi D k (sb1_lv_rb hT ρ s)) x) = fderiv ℝ (sb1_lv_psi D k (sb1_lv_rb hT ρ s)) x := by
    ext v
    simp [p4k_inner_grad]
  rw [this]
  exact hd.hasFDerivAt

theorem sb1_lv_U_contDiff (hk4 : IsP4Kernel d D.s r₀ k) (s : ℝ) : ContDiff ℝ 1 (sb1_lv_U D k hT ρ s) := by
  obtain ⟨Lg, hRg⟩ := sb1_lv_kerR hk4 H.tr.hs0
  obtain ⟨L2, -, hL2⟩ := sb1_lv_hess_bound hk4
  exact sb1_lv_u_contDiff H.tr.V hk4 H.tr.hd H.tr.hs0 H.tr.hsd hRg hRg.gbd hL2 (sb1_lv_rb_rho H hT s)
    (sb1_lv_rb_slice H hT s) (sb1_lv_rb_pos H hT s)

theorem sb1_lv_divU_cont (hk4 : IsP4Kernel d D.s r₀ k) :
    Continuous (Function.uncurry fun s x => sb1divE (sb1_lv_U D k hT ρ s) x) := by
  obtain ⟨Lg, hRg⟩ := sb1_lv_kerR hk4 H.tr.hs0
  obtain ⟨L2, -, hL2⟩ := sb1_lv_hess_bound hk4
  have e : (fun p : ℝ × Euc d => sb1divE (sb1_lv_U D k hT ρ p.1) p.2) = fun p => ∑ j,
      (D.invβ * ((sb1_lv_rb hT ρ p.1 p.2 * fderiv ℝ (fun y => fderiv ℝ (sb1_lv_rb hT ρ p.1) y (sb1e j)) p.2 (sb1e j) -
        fderiv ℝ (sb1_lv_rb hT ρ p.1) p.2 (sb1e j) ^ 2) / sb1_lv_rb hT ρ p.1 p.2 ^ 2) +
        sb1_lv_cv (sb1_lv_hjj k j) (sb1_lv_rb hT ρ p.1) p.2 +
        fderiv ℝ (fun y => fderiv ℝ D.V y (sb1e j)) p.2 (sb1e j)) :=
    funext fun p => sb1_lv_divu_eq H.tr.V hk4 H.tr.hd H.tr.hs0 H.tr.hsd hRg hRg.gbd hL2 (sb1_lv_rb_rho H hT p.1)
      (sb1_lv_rb_slice H hT p.1) (sb1_lv_rb_pos H hT p.1) p.2
  show Continuous fun p : ℝ × Euc d => sb1divE (sb1_lv_U D k hT ρ p.1) p.2
  rw [e]
  refine continuous_finset_sum _ fun j _ => ?_
  have hr := sb1_lv_rb_cont H hT
  have hpos : ∀ p : ℝ × Euc d, sb1_lv_rb hT ρ p.1 p.2 ^ 2 ≠ 0 := fun p => (pow_pos (sb1_lv_rb_pos H hT p.1 p.2) 2).ne'
  have h1 := ((hr.mul (sb1_lv_ddrb_cont H hT j)).sub ((sb1_lv_drb_cont H hT j).pow 2)).div (hr.pow 2) hpos
  have h2 := sb1_lv_cv_rb_cont H hT (sb1_lv_gr_hjj hk4.smooth hL2 j) (sb1_lv_hjj_cont hk4.smooth j)
  have h3 : Continuous fun p : ℝ × Euc d => fderiv ℝ (fun y => fderiv ℝ D.V y (sb1e j)) p.2 (sb1e j) :=
    (((sb1_dV_k_contDiff H.tr.V j).continuous_fderiv (by norm_num)).clm_apply continuous_const).comp continuous_snd
  exact ((continuous_const.mul h1).add h2).add h3

theorem sb1_lv_Psi_dt (hk4 : IsP4Kernel d D.s r₀ k) {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) T) (x : Euc d) :
    HasDerivAt (fun r => sb1_lv_Psi D k hT ρ r x) (sb1_lv_W D k hT ρ s x) s := by
  have hIcc : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.le⟩
  have hρ := sb1_hasDerivAt H.tr hT hs x
  have hG := sb1_hasDerivAt_G H hT (sb1KerU_of_p4 H.tr.hs0 hk4) hs x
  have hlog := hρ.log (H.pos s hIcc x).ne'
  have hall := ((hlog.const_mul D.invβ).add hG).add_const (D.V x) |>.neg
  have hev : (fun r => sb1_lv_Psi D k hT ρ r x) =ᶠ[𝓝 s] fun r => -(D.invβ * Real.log (ρ r x) + sb1G k (ρ r) x + D.V x) := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
    have : sb1_lv_rb hT ρ r = ρ r := by
      unfold sb1_lv_rb; rw [Set.projIcc_of_mem hT ⟨hr.1.le, hr.2.le⟩]
    simp only [sb1_lv_Psi, sb1_lv_psi, this]
  refine (hall.congr_deriv ?_).congr_of_eventuallyEq hev
  have e1 : sb1_lv_rb hT ρ s = ρ s := by unfold sb1_lv_rb; rw [Set.projIcc_of_mem hT hIcc]
  have e2 : sb1At D hT ρ s = sb1A D (ρ s) := by
    funext y; exact sb1At_eq hT hIcc y
  unfold sb1_lv_W
  rw [e1, e2]
  unfold sb1Gd
  show _ = _
  have : sb1_lv_cv k (sb1A D (ρ s)) x = ∫ y, sb1A D (ρ s) y * k (x - y) := rfl
  rw [this]

end Traj

end HRS.MS.MfeConf
