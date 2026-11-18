import HRS.MS.MfeConfAux86

/-!
# S.B.1, packet F8 (part 19): the time-dependent one-body data and their continuity / derivatives

For the clamped trajectory `ρb` and a truncated kernel `k` (`IsP4Kernel`):
`sb1_lv_Psi s = ψ_s = -(θ log ρb_s + k*ρb_s + V)`, `sb1_lv_U s = u_s = -∇ψ_s`,
`sb1_lv_W s x = -(θ A(ρb_s)/ρb_s + Ġ_s) = ∂_sψ`.  Proved: joint continuity of `ψ, u, div u, W`, `∇ψ_s = -u_s`,
`u_s ∈ C¹`, `∂_sψ_s(x) = W_s(x)` on `(0,T)`.
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d : ℕ}

def sb1_lv_Psi (D : Whole.WholeDyn d) (k : Euc d → ℝ) {T : ℝ} (hT : 0 ≤ T) (ρ : ℝ → Euc d → ℝ) (s : ℝ) :
    Euc d → ℝ := sb1_lv_psi D k (sb1_lv_rb hT ρ s)

def sb1_lv_U (D : Whole.WholeDyn d) (k : Euc d → ℝ) {T : ℝ} (hT : 0 ≤ T) (ρ : ℝ → Euc d → ℝ) (s : ℝ) :
    Euc d → Euc d := sb1_lv_u D k (sb1_lv_rb hT ρ s)

def sb1_lv_W (D : Whole.WholeDyn d) (k : Euc d → ℝ) {T : ℝ} (hT : 0 ≤ T) (ρ : ℝ → Euc d → ℝ) (s : ℝ)
    (x : Euc d) : ℝ :=
  -(D.invβ * (sb1At D hT ρ s x / sb1_lv_rb hT ρ s x) + sb1_lv_cv k (sb1At D hT ρ s) x)

section Traj

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ) (hT : 0 ≤ T)
  {r₀ : ℝ} {k : Euc d → ℝ}

include H hT

theorem sb1_lv_rb_pos (s : ℝ) (y : Euc d) : 0 < sb1_lv_rb hT ρ s y := H.pos _ (sb1_lv_cl hT s) y

theorem sb1_lv_rb_rho (s : ℝ) : Sb1Rho (sb1_lv_rb hT ρ s) C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y) :=
  H.rho H.tr.hd (sb1_lv_cl hT s)

theorem sb1_lv_rb_slice (s : ℝ) : Sb1Slice d C (sb1_lv_rb hT ρ s) := H.tr.slice _ (sb1_lv_cl hT s)

theorem sb1_lv_psi_cont (hk4 : IsP4Kernel d D.s r₀ k) :
    Continuous (Function.uncurry fun s x => sb1_lv_Psi D k hT ρ s x) := by
  obtain ⟨A, hA⟩ := sb1_lv_gr_k hk4 H.tr.hs0
  have hG := sb1_lv_G_cont H hT hA hk4.smooth.continuous
  have hr := sb1_lv_rb_cont H hT
  have hlog : Continuous fun p : ℝ × Euc d => Real.log (sb1_lv_rb hT ρ p.1 p.2) :=
    continuous_iff_continuousAt.2 fun p => (hr.continuousAt).log (sb1_lv_rb_pos H hT p.1 p.2).ne'
  have hV : Continuous fun p : ℝ × Euc d => D.V p.2 := H.tr.V.c3.continuous.comp continuous_snd
  exact ((continuous_const.mul hlog).add hG |>.add hV).neg

theorem sb1_lv_U_apply (hk4 : IsP4Kernel d D.s r₀ k) (s : ℝ) (x : Euc d) (j : Fin d) :
    sb1_lv_U D k hT ρ s x j = D.invβ * (fderiv ℝ (sb1_lv_rb hT ρ s) x (sb1e j) / sb1_lv_rb hT ρ s x) +
      sb1_lv_cv (sb1_lv_dk k j) (sb1_lv_rb hT ρ s) x + fderiv ℝ D.V x (sb1e j) := by
  obtain ⟨Lg, hRg⟩ := sb1_lv_kerR hk4 H.tr.hs0
  have hS := sb1_lv_rb_slice H hT s
  have e := sb1_lv_u_apply hk4 H.tr.hd H.tr.hs0 H.tr.hsd hRg (sb1_lv_rb_rho H hT s) (sb1_lv_rb_pos H hT s)
    (hS.decay.1.differentiable (by norm_num)) (H.tr.V.c3.differentiable (by norm_num)) x j
  unfold sb1_lv_U
  rw [e]
  unfold sb1_lv_a
  rw [sb1_lv_dG_eq hk4 H.tr.hd H.tr.hs0 H.tr.hsd hRg (sb1_lv_rb_rho H hT s) j x]

theorem sb1_lv_U_cont (hk4 : IsP4Kernel d D.s r₀ k) :
    Continuous (Function.uncurry fun s x => sb1_lv_U D k hT ρ s x) := by
  obtain ⟨Lg, hRg⟩ := sb1_lv_kerR hk4 H.tr.hs0
  have hL : ∀ z, ‖fderiv ℝ k z‖ ≤ Lg := hRg.gbd
  refine contDiff_zero.1 (contDiff_euclidean.2 fun j => contDiff_zero.2 ?_)
  have e : (fun p : ℝ × Euc d => sb1_lv_U D k hT ρ p.1 p.2 j) = fun p => D.invβ *
      (fderiv ℝ (sb1_lv_rb hT ρ p.1) p.2 (sb1e j) / sb1_lv_rb hT ρ p.1 p.2) +
      sb1_lv_cv (sb1_lv_dk k j) (sb1_lv_rb hT ρ p.1) p.2 + fderiv ℝ D.V p.2 (sb1e j) :=
    funext fun p => sb1_lv_U_apply H hT hk4 p.1 p.2 j
  show Continuous fun p : ℝ × Euc d => sb1_lv_U D k hT ρ p.1 p.2 j
  rw [e]
  have h1 := (sb1_lv_drb_cont H hT j).div (sb1_lv_rb_cont H hT) (fun p => (sb1_lv_rb_pos H hT p.1 p.2).ne')
  have h2 := sb1_lv_cv_rb_cont H hT (sb1_lv_gr_dk hk4.smooth hL j) (sb1_lv_dk_cont hk4.smooth j)
  have h3 : Continuous fun p : ℝ × Euc d => fderiv ℝ D.V p.2 (sb1e j) :=
    (sb1_dV_k_contDiff H.tr.V j).continuous.comp continuous_snd
  exact ((continuous_const.mul h1).add h2).add h3

theorem sb1_lv_W_cont (hk4 : IsP4Kernel d D.s r₀ k) :
    Continuous (Function.uncurry fun s x => sb1_lv_W D k hT ρ s x) := by
  obtain ⟨A, hA⟩ := sb1_lv_gr_k hk4 H.tr.hs0
  have h1 := (sb1At_cont H.tr hT).div (sb1_lv_rb_cont H hT) (fun p => (sb1_lv_rb_pos H hT p.1 p.2).ne')
  have h2 := sb1_lv_Gd_cont H hT hA hk4.smooth.continuous
  exact ((continuous_const.mul h1).add h2).neg

end Traj

end HRS.MS.MfeConf
