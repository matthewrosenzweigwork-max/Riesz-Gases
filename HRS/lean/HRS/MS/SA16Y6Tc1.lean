import HRS.MS.SA16ZT8
import HRS.MS.SA16Y5Cv4
import HRS.MS.CzPvAsmAux2

/-!
# S.A.16 (SA16Y6) Tc1: the Riesz transform `R_i = pvOdd d 1 (u_i)` on `C_c^∞` (boundary `s = d-1`)

For `s = d-1` and `f ∈ C_c^∞`: `R_i f = -(c_s)⁻¹ ρ ⋆ ∂_i f` (from `sa16z_conv_fderiv_pvOdd`), hence `R_i f` is smooth, additive and
homogeneous in `f`; it is bounded (uniform bound of the truncations, `pvasm_trunc_unif`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Tc1
variable {d : ℕ}

/-- the Riesz transform `R_i = pvOdd d 1 (u_i)` -/
def sa16y6_R (d : ℕ) (i : Fin d) (f : Euc d → ℝ) : Euc d → ℝ :=
  pvOdd d 1 (fun u : Euc d => u i) f

lemma sa16y6_R_eq (hd : 1 ≤ d) {s : ℝ} (hs : s = (d : ℝ) - 1) {f : Euc d → ℝ} (hf : IsCcInfty f) (i : Fin d)
    (x : Euc d) :
    sa16y6_R d i f x = -(HRS.CZ.Hls.hlsg_c s)⁻¹ *
      sa16r_cv (rieszKernel d s) (fun y => fderiv ℝ f y (sa16z_e i)) x := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have hsd : s < d := by rw [hs]; linarith
  have hc := HRS.CZ.Hls.hlsg_c_pos hs0
  have h := sa16z_conv_fderiv_pvOdd hd hs0 hsd hf i x
  have h1 : s + 2 - (d : ℝ) = 1 := by rw [hs]; ring
  rw [h1] at h
  have e : convFun (rieszKernel d s) f = sa16r_cv (rieszKernel d s) f := by
    funext y; rw [sa16sp_convFun_eq]; rfl
  have h2 : fderiv ℝ (convFun (rieszKernel d s) f) x (sa16z_e i) =
      sa16r_cv (rieszKernel d s) (fun y => fderiv ℝ f y (sa16z_e i)) x := by
    rw [e]; exact sa16y5_cv_fderiv (rieszKernel_locallyIntegrable hs0 hsd) hf x _
  rw [h2] at h
  unfold sa16y6_R
  rw [h]
  field_simp

lemma sa16y6_R_contDiff (hd : 1 ≤ d) {s : ℝ} (hs : s = (d : ℝ) - 1) {f : Euc d → ℝ} (hf : IsCcInfty f)
    (i : Fin d) : ContDiff ℝ ∞ (sa16y6_R d i f) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have hsd : s < d := by rw [hs]; linarith
  have e : sa16y6_R d i f = fun x => -(HRS.CZ.Hls.hlsg_c s)⁻¹ *
      sa16r_cv (rieszKernel d s) (fun y => fderiv ℝ f y (sa16z_e i)) x :=
    funext fun x => sa16y6_R_eq hd hs hf i x
  rw [e]
  exact contDiff_const.mul (sa16y5_cv_cc_contDiff (rieszKernel_locallyIntegrable hs0 hsd)
    (sa16s_cc_fderiv hf (sa16z_e i)))

lemma sa16y6_toSchwartz {f : Euc d → ℝ} (hf : IsCcInfty f) : ∃ W : 𝓢(Euc d, ℝ), (⇑W : Euc d → ℝ) = f :=
  ⟨hf.2.toSchwartzMap hf.1, rfl⟩

lemma sa16y6_R_bdd (hd : 1 ≤ d) {f : Euc d → ℝ} (hf : IsCcInfty f) (i : Fin d) :
    ∃ B : ℝ, ∀ x, |sa16y6_R d i f x| ≤ B := by
  obtain ⟨W, hW⟩ := sa16y6_toSchwartz hf
  obtain ⟨L, hL⟩ := hf.1.lipschitzWith_of_hasCompactSupport hf.2 (by simp)
  have hint : Integrable f := hf.1.continuous.integrable_of_hasCompactSupport hf.2
  obtain ⟨c, hc⟩ := HRS.CZ.PvAsm.pvasm_trunc_unif hd i hL hint
  refine ⟨c, fun x => ?_⟩
  have ht := HRS.CZ.PvAsm.pvasm_trunc_tendsto hd i W x
  rw [hW] at ht
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), |HRS.CZ.Pv.pvTrunc d 1 (fun v : Euc d => v i) f ε x| ≤ c := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with ε hε
    rw [HRS.CZ.PvAsm.pvasm_trunc_eq]
    exact hc ε hε.1 hε.2.le x
  exact le_of_tendsto ht.abs hev

lemma sa16y6_D_add {f g : Euc d → ℝ} (hf : IsCcInfty f) (hg : IsCcInfty g) (v : Euc d) :
    (fun y => fderiv ℝ (fun z => f z + g z) y v) =
      fun y => fderiv ℝ f y v + fderiv ℝ g y v := by
  funext y
  have hfd : DifferentiableAt ℝ f y := (hf.1.differentiable (by simp)) y
  have hgd : DifferentiableAt ℝ g y := (hg.1.differentiable (by simp)) y
  have h : HasFDerivAt (fun z => f z + g z) (fderiv ℝ f y + fderiv ℝ g y) y :=
    hfd.hasFDerivAt.add hgd.hasFDerivAt
  rw [h.fderiv]; rfl

lemma sa16y6_cv_add_cc {k F G : Euc d → ℝ} (hk : LocallyIntegrable k volume) (hF : IsCcInfty F) (hG : IsCcInfty G)
    (x : Euc d) : sa16r_cv k (fun y => F y + G y) x = sa16r_cv k F x + sa16r_cv k G x := by
  unfold sa16r_cv
  have h1 : Integrable (fun z => k z * F (x - z)) := by
    have := hk.integrable_smul_right_of_hasCompactSupport (hF.1.continuous.comp (continuous_const.sub continuous_id))
      ((sa16z_F_cc hF x).2)
    simpa [smul_eq_mul] using this
  have h2 : Integrable (fun z => k z * G (x - z)) := by
    have := hk.integrable_smul_right_of_hasCompactSupport (hG.1.continuous.comp (continuous_const.sub continuous_id))
      ((sa16z_F_cc hG x).2)
    simpa [smul_eq_mul] using this
  rw [← integral_add h1 h2]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [mul_add]

lemma sa16y6_R_add (hd : 1 ≤ d) {s : ℝ} (hs : s = (d : ℝ) - 1) {f g : Euc d → ℝ} (hf : IsCcInfty f)
    (hg : IsCcInfty g) (i : Fin d) (x : Euc d) :
    sa16y6_R d i (fun y => f y + g y) x = sa16y6_R d i f x + sa16y6_R d i g x := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have hsd : s < d := by rw [hs]; linarith
  have hfg : IsCcInfty (fun y => f y + g y) := ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  rw [sa16y6_R_eq hd hs hfg i x, sa16y6_R_eq hd hs hf i x, sa16y6_R_eq hd hs hg i x, sa16y6_D_add hf hg,
    sa16y6_cv_add_cc (rieszKernel_locallyIntegrable hs0 hsd) (sa16s_cc_fderiv hf (sa16z_e i))
      (sa16s_cc_fderiv hg (sa16z_e i)) x]
  ring

lemma sa16y6_R_smul (hd : 1 ≤ d) {s : ℝ} (hs : s = (d : ℝ) - 1) {f : Euc d → ℝ} (hf : IsCcInfty f) (c : ℝ)
    (i : Fin d) (x : Euc d) : sa16y6_R d i (fun y => c * f y) x = c * sa16y6_R d i f x := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have hsd : s < d := by rw [hs]; linarith
  have hcf : IsCcInfty (fun y => c * f y) := ⟨contDiff_const.mul hf.1, hf.2.mul_left⟩
  rw [sa16y6_R_eq hd hs hcf i x, sa16y6_R_eq hd hs hf i x]
  have hD : (fun y => fderiv ℝ (fun z => c * f z) y (sa16z_e i)) = fun y => c * fderiv ℝ f y (sa16z_e i) := by
    funext y
    have hfd : DifferentiableAt ℝ f y := (hf.1.differentiable (by simp)) y
    have h : HasFDerivAt (fun z => c * f z) (c • fderiv ℝ f y) y := hfd.hasFDerivAt.const_mul c
    rw [h.fderiv]; simp
  rw [hD]
  have hDi : IsCcInfty (fun y => fderiv ℝ f y (sa16z_e i)) := sa16s_cc_fderiv hf (sa16z_e i)
  have hint : Integrable (fun z => rieszKernel d s z * fderiv ℝ f (x - z) (sa16z_e i)) := by
    have := (rieszKernel_locallyIntegrable (d := d) hs0 hsd).integrable_smul_right_of_hasCompactSupport
      (hDi.1.continuous.comp (continuous_const.sub continuous_id)) ((sa16z_F_cc hDi x).2)
    simpa [smul_eq_mul] using this
  unfold sa16r_cv
  have : ∫ z, rieszKernel d s z * (c * fderiv ℝ f (x - z) (sa16z_e i)) =
      c * ∫ z, rieszKernel d s z * fderiv ℝ f (x - z) (sa16z_e i) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    ring
  rw [this]
  ring

end Tc1

end HRS.Whole.AppendixA.Phase2SA16R
