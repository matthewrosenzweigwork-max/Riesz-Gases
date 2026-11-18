import HRS.MS.SA16Y6Tc5
import HRS.MS.SA16Y5Jt3

/-!
# S.A.16 (SA16Y6) Tc6: `g_a ⋆ eucNonlocal` in `Tc`-form and the family `Fam` (boundary `s = d-1`)

`sa16y6_Fam_eq`: for `s = d-1`, `g_a ⋆ eucNonlocal s M μ φ = ∑_{ij} M_{ji} Tc_{a,ij}(μφ, (∂_jμ)φ)`; `Fam` is additive, homogeneous and smooth in `φ`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q HRS.MS.ToriCoefA

section Tc6
variable {d : ℕ}

lemma sa16y6_D_mul {μ φ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ) (hφ : ContDiff ℝ ∞ φ) (y v : Euc d) :
    fderiv ℝ (fun z => μ z * φ z) y v = μ y * fderiv ℝ φ y v + φ y * fderiv ℝ μ y v := by
  have h1 : DifferentiableAt ℝ μ y := (hμ.differentiable (by simp)) y
  have h2 : DifferentiableAt ℝ φ y := (hφ.differentiable (by simp)) y
  rw [fderiv_fun_mul h1 h2]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

lemma sa16y6_S_eq (hd : 1 ≤ d) {s : ℝ} (hs : s = (d : ℝ) - 1) {μ φ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ)
    (hφ : IsCcInfty φ) (i j : Fin d) :
    sa16y5_S d s μ φ i j = fun y => -(sa16y6_cs d) * sa16y6_Wf d i j (fun z => μ z * φ z)
      (fun z => fderiv ℝ μ z (sa16z_e j) * φ z) y := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have hsd : s < d := by rw [hs]; linarith
  have hc := HRS.CZ.Hls.hlsg_c_pos hs0
  have hk := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have hw : IsCcInfty (fun y' => μ y' * fderiv ℝ φ y' (sa16z_e j)) :=
    sa16y5_cc_mul hμ (sa16s_cc_fderiv hφ (sa16z_e j))
  have hP : IsCcInfty (fun z => μ z * φ z) := sa16y5_cc_mul hμ hφ
  have hdm : ContDiff ℝ ∞ (fun y => fderiv ℝ μ y (sa16z_e j)) :=
    (hμ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hQ : IsCcInfty (fun z => fderiv ℝ μ z (sa16z_e j) * φ z) := sa16y5_cc_mul hdm hφ
  funext y
  -- `S = cv ρ (D_i f) = -c_s R_i f`
  have h1 : sa16y5_S d s μ φ i j y = -(HRS.CZ.Hls.hlsg_c s) * sa16y6_R d i
      (fun y' => μ y' * fderiv ℝ φ y' (sa16z_e j)) y := by
    unfold sa16y5_S
    rw [sa16y5_cv_fderiv hk hw y, sa16y6_R_eq hd hs hw i y]
    field_simp
  have hcs : sa16y6_cs d = HRS.CZ.Hls.hlsg_c s := by unfold sa16y6_cs; rw [hs]
  -- `μ ∂_jφ = ∂_j(μφ) - (∂_jμ)φ`
  have hf : (fun y' => μ y' * fderiv ℝ φ y' (sa16z_e j)) =
      fun y' => fderiv ℝ (fun z => μ z * φ z) y' (sa16z_e j) + (-1) * (fderiv ℝ μ y' (sa16z_e j) * φ y') := by
    funext y'
    rw [sa16y6_D_mul hμ hφ.1 y' (sa16z_e j)]
    ring
  have hDP := sa16s_cc_fderiv hP (sa16z_e j)
  rw [h1, hf, sa16y6_R_add hd hs hDP ⟨contDiff_const.mul hQ.1, hQ.2.mul_left⟩ i y,
    sa16y6_R_smul hd hs hQ (-1) i y, hcs]
  unfold sa16y6_Wf
  ring

def sa16y6_Fam (d : ℕ) (a : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (μ φ : Euc d → ℝ) : Euc d → ℝ :=
  fun x => ∑ i, ∑ j, M j i * sa16y6_Tc d a i j (fun y => μ y * φ y)
    (fun y => fderiv ℝ μ y (sa16z_e j) * φ y) x

theorem sa16y6_Fam_eq (hd : 1 ≤ d) {s : ℝ} (hs : s = (d : ℝ) - 1) {a : ℝ} (ha : 0 < a)
    (M : Matrix (Fin d) (Fin d) ℝ) {μ φ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ) (hφ : IsCcInfty φ) :
    sa16y6_Fam d a M μ φ = sa16r_cv (sa16r_g d a) (HRS.MH.AdjointRd.eucNonlocal s M μ φ) := by
  funext x
  rw [sa16y5_euc_eq]
  have hdm : ∀ j : Fin d, ContDiff ℝ ∞ (fun y => fderiv ℝ μ y (sa16z_e j)) := fun j =>
    (hμ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hS : ∀ i j, sa16y5_S d s μ φ i j = fun y => -(sa16y6_cs d) * sa16y6_Wf d i j (fun z => μ z * φ z)
      (fun z => fderiv ℝ μ z (sa16z_e j) * φ z) y := fun i j => sa16y6_S_eq hd hs hμ hφ i j
  rw [sa16y5_cv_finsum (sa16r_g_int ha) (fun i j => M j i)
    (fun i j => by rw [hS i j]; exact continuous_const.mul (sa16y6_Wf_cont hd i j (sa16y5_cc_mul hμ hφ)
      (sa16y5_cc_mul (hdm j) hφ)))
    (fun i j => by
      obtain ⟨B, hB⟩ := sa16y6_Wf_bdd hd i j (sa16y5_cc_mul hμ hφ) (sa16y5_cc_mul (hdm j) hφ)
      refine ⟨|sa16y6_cs d| * B, fun y => ?_⟩
      rw [hS i j]
      show |-(sa16y6_cs d) * _| ≤ _
      rw [abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left (hB y) (abs_nonneg _)) x]
  unfold sa16y6_Fam
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hS i j, sa16r_cv_smul]
  unfold sa16y6_Tc
  rfl

lemma sa16y6_Fam_add (hd : 1 ≤ d) {a : ℝ} (ha : 0 < a) (M : Matrix (Fin d) (Fin d) ℝ) {μ : Euc d → ℝ}
    (hμ : ContDiff ℝ ∞ μ) {φ ψ : Euc d → ℝ} (hφ : IsCcInfty φ) (hψ : IsCcInfty ψ) :
    sa16y6_Fam d a M μ (fun y => φ y + ψ y) = sa16y6_Fam d a M μ φ + sa16y6_Fam d a M μ ψ := by
  funext x
  simp only [Pi.add_apply]
  unfold sa16y6_Fam
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hdm : ContDiff ℝ ∞ (fun y => fderiv ℝ μ y (sa16z_e j)) :=
    (hμ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have := sa16y6_Tc_add hd ha i j (sa16y5_cc_mul hμ hφ) (sa16y5_cc_mul hμ hψ)
    (sa16y5_cc_mul hdm hφ) (sa16y5_cc_mul hdm hψ)
  have e1 : (fun y => μ y * (φ y + ψ y)) = fun y => μ y * φ y + μ y * ψ y := by funext y; ring
  have e2 : (fun y => fderiv ℝ μ y (sa16z_e j) * (φ y + ψ y)) =
      fun y => fderiv ℝ μ y (sa16z_e j) * φ y + fderiv ℝ μ y (sa16z_e j) * ψ y := by funext y; ring
  rw [e1, e2, this]
  beta_reduce
  ring

lemma sa16y6_Fam_smul (hd : 1 ≤ d) {a : ℝ} (ha : 0 < a) (M : Matrix (Fin d) (Fin d) ℝ) {μ : Euc d → ℝ}
    (hμ : ContDiff ℝ ∞ μ) {φ : Euc d → ℝ} (hφ : IsCcInfty φ) (c : ℝ) :
    sa16y6_Fam d a M μ (fun y => c * φ y) = c • sa16y6_Fam d a M μ φ := by
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  unfold sa16y6_Fam
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hdm : ContDiff ℝ ∞ (fun y => fderiv ℝ μ y (sa16z_e j)) :=
    (hμ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have := sa16y6_Tc_smul hd ha i j (sa16y5_cc_mul hμ hφ) (sa16y5_cc_mul hdm hφ) c
  have e1 : (fun y => μ y * (c * φ y)) = fun y => c * (μ y * φ y) := by funext y; ring
  have e2 : (fun y => fderiv ℝ μ y (sa16z_e j) * (c * φ y)) =
      fun y => c * (fderiv ℝ μ y (sa16z_e j) * φ y) := by funext y; ring
  rw [e1, e2, this]
  beta_reduce
  ring

lemma sa16y6_Fam_smooth (hd : 1 ≤ d) {a : ℝ} (ha : 0 < a) (M : Matrix (Fin d) (Fin d) ℝ) {μ φ : Euc d → ℝ}
    (hμ : ContDiff ℝ ∞ μ) (hφ : IsCcInfty φ) : ContDiff ℝ ∞ (sa16y6_Fam d a M μ φ) := by
  unfold sa16y6_Fam
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => contDiff_const.mul ?_
  have hdm : ContDiff ℝ ∞ (fun y => fderiv ℝ μ y (sa16z_e j)) :=
    (hμ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  exact sa16y6_Tc_smooth hd ha i j (sa16y5_cc_mul hμ hφ) (sa16y5_cc_mul hdm hφ)

end Tc6

end HRS.Whole.AppendixA.Phase2SA16R
