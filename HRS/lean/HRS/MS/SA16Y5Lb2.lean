import HRS.MS.SA16Y5Lb1

/-!
# S.A.16 (SA16Y5) Lb2: the decomposition identity for `Tm` (K2, part 2)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Lb2
variable {d : ℕ} {s : ℝ}

lemma sa16y5_cc_mul {μ' v : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ') (hv : IsCcInfty v) :
    IsCcInfty (fun y => μ' y * v y) := ⟨hμ.mul hv.1, hv.2.mul_left⟩

lemma sa16y5_cc_dmu {μ' v : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ') (hv : IsCcInfty v) (j : Fin d) :
    IsCcInfty (fun y => fderiv ℝ μ' y (sa16z_e j) * v y) :=
  sa16y5_cc_mul ((hμ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const) hv

theorem sa16y5_Tm_eq (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hsd1 : (d : ℝ) < s + 1) {a : ℝ} (ha : 0 < a)
    {ε : ℝ} (hε : 0 < ε) {μ' v : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ') (hv : IsCcInfty v) (i j : Fin d) (x : Euc d) :
    sa16y5_Tm d s a μ' i j v x =
      sa16r_cv (sa16y5_rn d s ε) (sa16r_cv (sa16y5_ddg d a j i) (fun y => μ' y * v y)) x
      - sa16r_cv (sa16y5_rn d s ε) (sa16r_cv (sa16r_dg d a i) (fun y => fderiv ℝ μ' y (sa16z_e j) * v y)) x
      + sa16r_cv (sa16y5_V d s ε i) (sa16r_cv (sa16r_dg d a j) (fun y => μ' y * v y)) x
      - sa16r_cv (sa16y5_V d s ε i) (sa16r_cv (sa16r_g d a) (fun y => fderiv ℝ μ' y (sa16z_e j) * v y)) x := by
  set P : Euc d → ℝ := fun y => μ' y * v y with hPdef
  set Q : Euc d → ℝ := fun y => fderiv ℝ μ' y (sa16z_e j) * v y with hQdef
  set w : Euc d → ℝ := fun y => μ' y * fderiv ℝ v y (sa16z_e j) with hwdef
  have hP : IsCcInfty P := sa16y5_cc_mul hμ hv
  have hQ : IsCcInfty Q := sa16y5_cc_dmu hμ hv j
  have hvj : IsCcInfty (fun y => fderiv ℝ v y (sa16z_e j)) := sa16s_cc_fderiv hv (sa16z_e j)
  have hw : IsCcInfty w := sa16y5_cc_mul hμ hvj
  have hPj : IsCcInfty (fun y => fderiv ℝ P y (sa16z_e j)) := sa16s_cc_fderiv hP (sa16z_e j)
  have hrn : Integrable (sa16y5_rn d s ε) := (sa16y5_rn_L1 hd hs hsd hε).1
  obtain ⟨Cf, -, hCf⟩ := sa16y5_V_L1 hd hs hsd1 (s := s)
  have hV : Integrable (sa16y5_V d s ε i) := (hCf ε hε i).1
  have hgi : Integrable (sa16r_g d a) := sa16r_g_int ha
  have hwdiff : w = fun y => fderiv ℝ P y (sa16z_e j) - Q y := by
    funext y
    have h1 : DifferentiableAt ℝ μ' y := hμ.differentiable (by simp) y
    have h2 : DifferentiableAt ℝ v y := hv.1.differentiable (by simp) y
    have : fderiv ℝ P y = μ' y • fderiv ℝ v y + v y • fderiv ℝ μ' y := fderiv_mul h1 h2
    show μ' y * fderiv ℝ v y (sa16z_e j) = fderiv ℝ P y (sa16z_e j) - Q y
    rw [this]
    simp only [hQdef, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  -- the inner function `S = ∂_i (ρ ⋆ w)`
  set A1 : Euc d → ℝ := fun y => fderiv ℝ (fun y' => fderiv ℝ P y' (sa16z_e j)) y (sa16z_e i) with hA1
  set A2 : Euc d → ℝ := fun y => fderiv ℝ Q y (sa16z_e i) with hA2
  have hA1c : IsCcInfty A1 := sa16s_cc_fderiv hPj (sa16z_e i)
  have hA2c : IsCcInfty A2 := sa16s_cc_fderiv hQ (sa16z_e i)
  have hdw : (fun y => fderiv ℝ w y (sa16z_e i)) = fun y => A1 y - A2 y := by
    funext y
    rw [hwdiff]
    have h1 : DifferentiableAt ℝ (fun y' => fderiv ℝ P y' (sa16z_e j)) y :=
      hPj.1.differentiable (by simp) y
    have h2 : DifferentiableAt ℝ Q y := hQ.1.differentiable (by simp) y
    rw [fderiv_fun_sub h1 h2]
    rfl
  have hS : ∀ y, fderiv ℝ (sa16r_cv (rieszKernel d s) w) y (sa16z_e i) =
      (sa16r_cv (sa16y5_rn d s ε) A1 y - sa16r_cv (sa16y5_rn d s ε) A2 y) +
      (sa16r_cv (sa16y5_V d s ε i) (fun y => fderiv ℝ P y (sa16z_e j)) y -
        sa16r_cv (sa16y5_V d s ε i) Q y) := by
    intro y
    rw [sa16y5_D1 hd hs hsd hw i hε y, hdw]
    congr 1
    · obtain ⟨b1, hb1⟩ := sa16r_cc_bdd hA1c
      obtain ⟨b2, hb2⟩ := sa16r_cc_bdd hA2c
      exact sa16y5_cv_sub_bdd hrn hA1c.1.continuous hA2c.1.continuous hb1 hb2 y
    · obtain ⟨b1, hb1⟩ := sa16r_cc_bdd hPj
      obtain ⟨b2, hb2⟩ := sa16r_cc_bdd hQ
      have e : w = fun y => fderiv ℝ P y (sa16z_e j) - Q y := hwdiff
      rw [e]
      exact sa16y5_cv_sub_bdd hV hPj.1.continuous hQ.1.continuous hb1 hb2 y
  -- convolve with `g_a`
  have hT : sa16y5_Tm d s a μ' i j v x = sa16r_cv (sa16r_g d a)
      (fun y => fderiv ℝ (sa16r_cv (rieszKernel d s) w) y (sa16z_e i)) x := rfl
  rw [hT, show (fun y => fderiv ℝ (sa16r_cv (rieszKernel d s) w) y (sa16z_e i)) = _ from funext hS]
  have hF1 := sa16y5_cv_cont hrn hA1c
  have hF2 := sa16y5_cv_cont hrn hA2c
  have hF3 := sa16y5_cv_cont hV hPj
  have hF4 := sa16y5_cv_cont hV hQ
  obtain ⟨b1, hb1⟩ := sa16y5_cv_bdd hrn hA1c
  obtain ⟨b2, hb2⟩ := sa16y5_cv_bdd hrn hA2c
  obtain ⟨b3, hb3⟩ := sa16y5_cv_bdd hV hPj
  obtain ⟨b4, hb4⟩ := sa16y5_cv_bdd hV hQ
  have h12 : ∀ y, |sa16r_cv (sa16y5_rn d s ε) A1 y - sa16r_cv (sa16y5_rn d s ε) A2 y| ≤ b1 + b2 := fun y =>
    (abs_sub _ _).trans (add_le_add (hb1 y) (hb2 y))
  have h34 : ∀ y, |sa16r_cv (sa16y5_V d s ε i) (fun y => fderiv ℝ P y (sa16z_e j)) y -
      sa16r_cv (sa16y5_V d s ε i) Q y| ≤ b3 + b4 := fun y =>
    (abs_sub _ _).trans (add_le_add (hb3 y) (hb4 y))
  have hF12 : Continuous (fun y => sa16r_cv (sa16y5_rn d s ε) A1 y - sa16r_cv (sa16y5_rn d s ε) A2 y) :=
    hF1.sub hF2
  have hF34 : Continuous (fun y => sa16r_cv (sa16y5_V d s ε i) (fun y => fderiv ℝ P y (sa16z_e j)) y -
      sa16r_cv (sa16y5_V d s ε i) Q y) := hF3.sub hF4
  rw [sa16y5_cv_add_bdd hgi hF12 hF34 h12 h34 x,
    sa16y5_cv_sub_bdd hgi hF1 hF2 hb1 hb2 x, sa16y5_cv_sub_bdd hgi hF3 hF4 hb3 hb4 x]
  have hrnm : Measurable (sa16y5_rn d s ε) := sa16y5_rn_meas ε
  have hVm : Measurable (sa16y5_V d s ε i) := sa16y5_V_meas ε i
  have hgm : Measurable (sa16r_g d a) := sa16r_g_meas
  have e1 : sa16r_cv (sa16r_g d a) (sa16r_cv (sa16y5_rn d s ε) A1) x =
      sa16r_cv (sa16y5_rn d s ε) (sa16r_cv (sa16y5_ddg d a j i) P) x := by
    rw [sa16y5_cv_comm hgm hrnm hgi hrn hA1c x]
    congr 1
    funext y
    exact (sa16y5_ddg_cv ha hP j i y).symm
  have e2 : sa16r_cv (sa16r_g d a) (sa16r_cv (sa16y5_rn d s ε) A2) x =
      sa16r_cv (sa16y5_rn d s ε) (sa16r_cv (sa16r_dg d a i) Q) x := by
    rw [sa16y5_cv_comm hgm hrnm hgi hrn hA2c x]
    congr 1
    funext y
    exact (sa16r_ibp_g ha hQ y i).symm
  have e3 : sa16r_cv (sa16r_g d a) (sa16r_cv (sa16y5_V d s ε i) (fun y => fderiv ℝ P y (sa16z_e j))) x =
      sa16r_cv (sa16y5_V d s ε i) (sa16r_cv (sa16r_dg d a j) P) x := by
    rw [sa16y5_cv_comm hgm hVm hgi hV hPj x]
    congr 1
    funext y
    exact (sa16r_ibp_g ha hP y j).symm
  have e4 : sa16r_cv (sa16r_g d a) (sa16r_cv (sa16y5_V d s ε i) Q) x =
      sa16r_cv (sa16y5_V d s ε i) (sa16r_cv (sa16r_g d a) Q) x :=
    sa16y5_cv_comm hgm hVm hgi hV hQ x
  rw [e1, e2, e3, e4]
  ring

end Lb2

end HRS.Whole.AppendixA.Phase2SA16R
