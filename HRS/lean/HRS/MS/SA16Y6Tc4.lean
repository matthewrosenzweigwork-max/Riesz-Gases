import HRS.MS.SA16Y6Tc3
import HRS.MS.SA16Y5Lb1
import HRS.MS.SA16Y5Lb4
import HRS.MS.SA16StrongSL10Aux

/-!
# S.A.16 (SA16Y6) Tc4: the critical-case heat-composed bilinear operator `Tc(P,Q)` (boundary `s = d-1`)

`sa16y6_Tc a i j P Q = -c_s · g_a ⋆ (R_i(∂_jP) - R_iQ)`.  For `P, Q ∈ C_c^∞`: smooth (`sa16y6_Tc_smooth`), additive/homogeneous in `(P,Q)`,
commutes with partial derivatives (`sa16y6_Tc_pd`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q HRS.MS.ToriCoefA

section Tc4
variable {d : ℕ}

/-- `c_s` at `s = d-1` -/
def sa16y6_cs (d : ℕ) : ℝ := HRS.CZ.Hls.hlsg_c ((d : ℝ) - 1)

/-- the inner function `R_i(∂_jP) - R_iQ` -/
def sa16y6_Wf (d : ℕ) (i j : Fin d) (P Q : Euc d → ℝ) : Euc d → ℝ := fun y =>
  sa16y6_R d i (fun z => fderiv ℝ P z (sa16z_e j)) y - sa16y6_R d i Q y

def sa16y6_Tc (d : ℕ) (a : ℝ) (i j : Fin d) (P Q : Euc d → ℝ) : Euc d → ℝ := fun x =>
  -(sa16y6_cs d) * sa16r_cv (sa16r_g d a) (sa16y6_Wf d i j P Q) x

lemma sa16y6_Wf_BS (hd : 1 ≤ d) (i j : Fin d) {P Q : Euc d → ℝ} (hP : IsCcInfty P) (hQ : IsCcInfty Q) :
    sa16y6_BS (sa16y6_Wf d i j P Q) :=
  sa16y6_BS_sub (sa16y6_R_BS hd rfl (sa16s_cc_fderiv hP (sa16z_e j)) i) (sa16y6_R_BS hd rfl hQ i)

lemma sa16y6_Tc_smooth (hd : 1 ≤ d) {a : ℝ} (ha : 0 < a) (i j : Fin d) {P Q : Euc d → ℝ} (hP : IsCcInfty P)
    (hQ : IsCcInfty Q) : ContDiff ℝ ∞ (sa16y6_Tc d a i j P Q) :=
  contDiff_const.mul (sa16y6_cv_contDiff (sa16r_g_meas) (sa16r_g_int ha) (sa16y6_Wf_BS hd i j hP hQ))

lemma sa16y6_Wf_cont (hd : 1 ≤ d) (i j : Fin d) {P Q : Euc d → ℝ} (hP : IsCcInfty P) (hQ : IsCcInfty Q) :
    Continuous (sa16y6_Wf d i j P Q) := (sa16y6_Wf_BS hd i j hP hQ).1.continuous

lemma sa16y6_Wf_bdd (hd : 1 ≤ d) (i j : Fin d) {P Q : Euc d → ℝ} (hP : IsCcInfty P) (hQ : IsCcInfty Q) :
    ∃ B : ℝ, ∀ y, |sa16y6_Wf d i j P Q y| ≤ B := by
  obtain ⟨⟨B0, h0⟩, -⟩ := sa16y6_BS_bounds (sa16y6_Wf_BS hd i j hP hQ)
  exact ⟨B0, fun y => by simpa using h0 y⟩

lemma sa16y6_D_add' {f g : Euc d → ℝ} (hf : IsCcInfty f) (hg : IsCcInfty g) (v : Euc d) :
    (fun y => fderiv ℝ (fun z => f z + g z) y v) = fun y => fderiv ℝ f y v + fderiv ℝ g y v :=
  sa16y6_D_add hf hg v

lemma sa16y6_Wf_add (hd : 1 ≤ d) (i j : Fin d) {P P' Q Q' : Euc d → ℝ} (hP : IsCcInfty P) (hP' : IsCcInfty P')
    (hQ : IsCcInfty Q) (hQ' : IsCcInfty Q') :
    sa16y6_Wf d i j (fun y => P y + P' y) (fun y => Q y + Q' y) =
      fun y => sa16y6_Wf d i j P Q y + sa16y6_Wf d i j P' Q' y := by
  funext y
  unfold sa16y6_Wf
  rw [sa16y6_D_add hP hP' (sa16z_e j)]
  rw [sa16y6_R_add hd rfl (sa16s_cc_fderiv hP (sa16z_e j)) (sa16s_cc_fderiv hP' (sa16z_e j)) i y,
    sa16y6_R_add hd rfl hQ hQ' i y]
  ring

lemma sa16y6_Wf_smul (hd : 1 ≤ d) (i j : Fin d) {P Q : Euc d → ℝ} (hP : IsCcInfty P) (hQ : IsCcInfty Q) (c : ℝ) :
    sa16y6_Wf d i j (fun y => c * P y) (fun y => c * Q y) = fun y => c * sa16y6_Wf d i j P Q y := by
  funext y
  unfold sa16y6_Wf
  have hD : (fun z => fderiv ℝ (fun w => c * P w) z (sa16z_e j)) = fun z => c * fderiv ℝ P z (sa16z_e j) := by
    funext z
    have hfd : DifferentiableAt ℝ P z := (hP.1.differentiable (by simp)) z
    have h : HasFDerivAt (fun w => c * P w) (c • fderiv ℝ P z) z := hfd.hasFDerivAt.const_mul c
    rw [h.fderiv]; simp
  rw [hD, sa16y6_R_smul hd rfl (sa16s_cc_fderiv hP (sa16z_e j)) c i y, sa16y6_R_smul hd rfl hQ c i y]
  ring

lemma sa16y6_Tc_add (hd : 1 ≤ d) {a : ℝ} (ha : 0 < a) (i j : Fin d) {P P' Q Q' : Euc d → ℝ} (hP : IsCcInfty P)
    (hP' : IsCcInfty P') (hQ : IsCcInfty Q) (hQ' : IsCcInfty Q') :
    sa16y6_Tc d a i j (fun y => P y + P' y) (fun y => Q y + Q' y) =
      fun x => sa16y6_Tc d a i j P Q x + sa16y6_Tc d a i j P' Q' x := by
  funext x
  unfold sa16y6_Tc
  rw [sa16y6_Wf_add hd i j hP hP' hQ hQ']
  obtain ⟨B, hB⟩ := sa16y6_Wf_bdd hd i j hP hQ
  obtain ⟨B', hB'⟩ := sa16y6_Wf_bdd hd i j hP' hQ'
  rw [sa16y5_cv_add_bdd (sa16r_g_int ha) (sa16y6_Wf_cont hd i j hP hQ) (sa16y6_Wf_cont hd i j hP' hQ') hB hB' x]
  ring

lemma sa16y6_Tc_smul (hd : 1 ≤ d) {a : ℝ} (ha : 0 < a) (i j : Fin d) {P Q : Euc d → ℝ} (hP : IsCcInfty P)
    (hQ : IsCcInfty Q) (c : ℝ) :
    sa16y6_Tc d a i j (fun y => c * P y) (fun y => c * Q y) = fun x => c * sa16y6_Tc d a i j P Q x := by
  funext x
  unfold sa16y6_Tc
  rw [sa16y6_Wf_smul hd i j hP hQ c, sa16r_cv_smul]
  ring

lemma sa16y6_pd_D {P : Euc d → ℝ} (hP : ContDiff ℝ ∞ P) (j : Fin d) :
    ∀ (n : ℕ) (idx : Fin n → Fin d),
      partialDeriv idx (fun y => fderiv ℝ P y (sa16z_e j)) = fun y => fderiv ℝ (partialDeriv idx P) y (sa16z_e j) := by
  intro n
  induction n with
  | zero =>
    intro idx
    have h1 : partialDeriv idx (fun y => fderiv ℝ P y (sa16z_e j)) = fun y => fderiv ℝ P y (sa16z_e j) :=
      funext fun x => sa16j_pd_zero idx _ x
    have h2 : partialDeriv idx P = P := funext fun x => sa16j_pd_zero idx P x
    rw [h1, h2]
  | succ n ih =>
    intro idx
    obtain ⟨l, idx', rfl⟩ : ∃ (l : Fin d) (idx' : Fin n → Fin d), idx = Fin.cons l idx' :=
      ⟨idx 0, Fin.tail idx, (Fin.cons_self_tail idx).symm⟩
    have hDj : ContDiff ℝ ∞ (fun y => fderiv ℝ P y (sa16z_e j)) :=
      (hP.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    funext y
    rw [sa16s_pd_cons hDj l idx' y, ih idx']
    rw [sa16y6_D_comm (sa16j_pd_smooth hP idx') j l y]
    have : (fun z => fderiv ℝ (partialDeriv idx' P) z (sa16z_e l)) = partialDeriv (Fin.cons l idx' : Fin (n + 1) → Fin d) P :=
      funext fun z => (sa16s_pd_cons hP l idx' z).symm
    rw [this]

lemma sa16y6_Wf_pd (hd : 1 ≤ d) (i j : Fin d) {P Q : Euc d → ℝ} (hP : IsCcInfty P) (hQ : IsCcInfty Q) {n : ℕ}
    (idx : Fin n → Fin d) :
    partialDeriv idx (sa16y6_Wf d i j P Q) = sa16y6_Wf d i j (partialDeriv idx P) (partialDeriv idx Q) := by
  have hRP := sa16y6_R_contDiff hd rfl (sa16s_cc_fderiv hP (sa16z_e j)) i
  have hRQ := sa16y6_R_contDiff hd rfl hQ i
  have e1 : sa16y6_Wf d i j P Q = fun y => sa16y6_R d i (fun z => fderiv ℝ P z (sa16z_e j)) y - sa16y6_R d i Q y := rfl
  rw [e1, sa16y_pd_sub hRP hRQ idx, sa16y6_R_pd hd rfl (sa16s_cc_fderiv hP (sa16z_e j)) i n idx,
    sa16y6_R_pd hd rfl hQ i n idx, sa16y6_pd_D hP.1 j n idx]
  rfl

lemma sa16y6_Tc_pd (hd : 1 ≤ d) {a : ℝ} (ha : 0 < a) (i j : Fin d) {P Q : Euc d → ℝ} (hP : IsCcInfty P)
    (hQ : IsCcInfty Q) {n : ℕ} (idx : Fin n → Fin d) :
    partialDeriv idx (sa16y6_Tc d a i j P Q) =
      sa16y6_Tc d a i j (partialDeriv idx P) (partialDeriv idx Q) := by
  have hcv : ContDiff ℝ ∞ (sa16r_cv (sa16r_g d a) (sa16y6_Wf d i j P Q)) :=
    sa16y6_cv_contDiff sa16r_g_meas (sa16r_g_int ha) (sa16y6_Wf_BS hd i j hP hQ)
  funext x
  have e : sa16y6_Tc d a i j P Q = fun y => (-(sa16y6_cs d)) * sa16r_cv (sa16r_g d a) (sa16y6_Wf d i j P Q) y := rfl
  rw [e, sa16q_pd_smul hcv _ idx x, sa16y6_cv_pd sa16r_g_meas (sa16r_g_int ha) (sa16y6_Wf_BS hd i j hP hQ) n idx,
    sa16y6_Wf_pd hd i j hP hQ idx]
  rfl

end Tc4

end HRS.Whole.AppendixA.Phase2SA16R
