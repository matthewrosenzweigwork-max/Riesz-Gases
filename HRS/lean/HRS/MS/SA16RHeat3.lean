import HRS.MS.SA16RHeat2
import HRS.MS.SA16StrongSL4
import HRS.MS.SA16JetConvDiff

/-!
# S.A.16 (SA16R) Heat3: heat convolution of `C_c^∞` functions

For `φ ∈ C_c^∞`: `g_a ⋆ φ` is smooth, `∂^idx (g_a ⋆ φ) = g_a ⋆ ∂^idx φ`, and the gain formula
`∂_i ∂^idx (g_a ⋆ φ) = (∂_i g_a) ⋆ ∂^idx φ` (integration by parts).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16

section Heat3
variable {d : ℕ}

lemma sa16r_cv_eq_conv (k φ : Euc d → ℝ) :
    sa16r_cv k φ = convolution k φ (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  ext x
  simp [sa16r_cv, convolution, smul_eq_mul]

lemma sa16r_cv_contDiff {a : ℝ} (ha : 0 < a) {φ : Euc d → ℝ} (hφ : IsCcInfty φ) :
    ContDiff ℝ ∞ (sa16r_cv (sa16r_g d a) φ) := by
  rw [sa16r_cv_eq_conv]
  exact hφ.2.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) (n := ⊤)
    (sa16r_g_int ha).locallyIntegrable hφ.1

lemma sa16r_cv_fderiv {a : ℝ} (ha : 0 < a) {φ : Euc d → ℝ} (hφ : IsCcInfty φ) (x v : Euc d) :
    fderiv ℝ (sa16r_cv (sa16r_g d a) φ) x v = sa16r_cv (sa16r_g d a) (fun y => fderiv ℝ φ y v) x := by
  have h1 := hφ.2.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    (sa16r_g_int ha).locallyIntegrable (hφ.1.of_le (by exact_mod_cast le_top)) x
  rw [sa16r_cv_eq_conv, h1.fderiv]
  have hc : Continuous (fderiv ℝ φ) := hφ.1.continuous_fderiv (by simp)
  have hcs : HasCompactSupport (fderiv ℝ φ) := hφ.2.fderiv ℝ
  rw [convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) (sa16r_g_int ha).locallyIntegrable hcs hc x v,
    ← sa16r_cv_eq_conv]

lemma sa16r_cv_pd {a : ℝ} (ha : 0 < a) {φ : Euc d → ℝ} (hφ : IsCcInfty φ) :
    ∀ (j : ℕ) (idx : Fin j → Fin d),
      partialDeriv idx (sa16r_cv (sa16r_g d a) φ) = sa16r_cv (sa16r_g d a) (partialDeriv idx φ) := by
  intro j
  induction j with
  | zero =>
    intro idx
    funext x
    rw [sa16j_pd_zero]
    unfold sa16r_cv
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [sa16j_pd_zero]
  | succ j ih =>
    intro idx
    obtain ⟨i, idx', rfl⟩ : ∃ (i : Fin d) (idx' : Fin j → Fin d), idx = Fin.cons i idx' :=
      ⟨idx 0, Fin.tail idx, (Fin.cons_self_tail idx).symm⟩
    funext x
    rw [sa16s_pd_cons (sa16r_cv_contDiff ha hφ) i idx' x, ih idx',
      sa16r_cv_fderiv ha (sa16s_cc_partialDeriv hφ idx') x]
    unfold sa16r_cv
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [sa16s_pd_cons hφ.1 i idx']

lemma sa16r_ibp_g {a : ℝ} (ha : 0 < a) {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) (x : Euc d) (i : Fin d) :
    sa16r_cv (sa16r_dg d a i) ψ x =
      sa16r_cv (sa16r_g d a) (fun y => fderiv ℝ ψ y (EuclideanSpace.single i 1)) x := by
  set e : Euc d := EuclideanSpace.single i 1 with he
  set f : Euc d → ℝ := fun z => ψ (x - z) with hfdef
  have hf : ContDiff ℝ ∞ f := hψ.1.comp (contDiff_const.sub contDiff_id)
  have hfs : HasCompactSupport f := hψ.2.comp_homeomorph (Homeomorph.subLeft x)
  have hg : ContDiff ℝ ∞ (sa16r_g d a) := sa16r_g_contDiff
  have hfd : ∀ z, fderiv ℝ f z e = -fderiv ℝ ψ (x - z) e := by
    intro z
    have h1 : HasFDerivAt (fun z : Euc d => x - z) (-(ContinuousLinearMap.id ℝ (Euc d))) z :=
      (hasFDerivAt_id z).const_sub x
    have h2 := (hψ.1.differentiable (by simp) (x - z)).hasFDerivAt.comp z h1
    have h3 : HasFDerivAt f _ z := h2
    rw [h3.fderiv]
    simp
  have hdf : Continuous (fun z => fderiv ℝ f z e) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdg : Continuous (fun z => fderiv ℝ (sa16r_g d a) z e) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have h1 : Integrable (fun z => fderiv ℝ f z e * sa16r_g d a z) :=
    (hdf.mul hg.continuous).integrable_of_hasCompactSupport ((hfs.fderiv_apply ℝ e).mul_right)
  have h2 : Integrable (fun z => f z * fderiv ℝ (sa16r_g d a) z e) :=
    (hf.continuous.mul hdg).integrable_of_hasCompactSupport (hfs.mul_right)
  have h3 : Integrable (fun z => f z * sa16r_g d a z) :=
    (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport (hfs.mul_right)
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (v := e) h1 h2 h3
    (fun z _ => (hf.differentiable (by simp)) z) (fun z _ => (hg.differentiable (by simp)) z)
  unfold sa16r_cv
  have hL : ∫ z, sa16r_dg d a i z * ψ (x - z) = ∫ z, f z * fderiv ℝ (sa16r_g d a) z e := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hfdef, he, sa16r_g_fderiv ha z i]
    ring
  have hR : ∫ z, sa16r_g d a z * fderiv ℝ ψ (x - z) e = -∫ z, fderiv ℝ f z e * sa16r_g d a z := by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hfd z]
    ring
  rw [hL, hR]
  exact this

/-- the gain formula for the top-order derivative of a heat convolution -/
lemma sa16r_cv_pd_gain {a : ℝ} (ha : 0 < a) {φ : Euc d → ℝ} (hφ : IsCcInfty φ) {j : ℕ}
    (i : Fin d) (idx : Fin j → Fin d) (x : Euc d) :
    partialDeriv (Fin.cons i idx : Fin (j + 1) → Fin d) (sa16r_cv (sa16r_g d a) φ) x =
      sa16r_cv (sa16r_dg d a i) (partialDeriv idx φ) x := by
  rw [sa16r_cv_pd ha hφ (j + 1), sa16r_ibp_g ha (sa16s_cc_partialDeriv hφ idx) x i]
  unfold sa16r_cv
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [sa16s_pd_cons hφ.1 i idx]

end Heat3

end HRS.Whole.AppendixA.Phase2SA16R
