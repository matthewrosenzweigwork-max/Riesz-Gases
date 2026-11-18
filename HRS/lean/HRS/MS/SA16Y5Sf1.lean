import HRS.MS.SA16Y5Mi6
import HRS.MS.SA16Y5Sm1

/-!
# S.A.16 (SA16Y5) Sf1: the fractional-order operator class and its linearity in the density (B9)

`SA16FOp d m p s M μ N`: `N : W^{m+2,p} → W^{m,p}` has zeroth component `eucNonlocal s M μ φ` on the jet of `φ ∈ C_c^∞`.
`sa16y5f_fop_sum`: `∑ w_i N_i` is an operator for the density `∑ w_i μ_i` (smooth densities, `0 < s < d`, `d - 1 < s`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Sf1
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)] {s : ℝ}

def SA16FOp (d m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (μ : Euc d → ℝ)
    (T : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p) : Prop :=
  ∀ φ : ccSub d, wrep d m p (T (sa16r_Jcc d (m + 1 + 1) p φ)) =ᵐ[volume] HRS.MH.AdjointRd.eucNonlocal s M μ φ.1

lemma sa16y5f_cv_rho_add (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) {w w' : Euc d → ℝ} (hw : IsCcInfty w)
    (hw' : IsCcInfty w') (x : Euc d) :
    sa16r_cv (rieszKernel d s) (fun y => w y + w' y) x = sa16r_cv (rieszKernel d s) w x +
      sa16r_cv (rieszKernel d s) w' x := by
  unfold sa16r_cv
  have h1 := sa16z_g_mul_int hs.le hsd (w := fun z => w (x - z)) (sa16z_F_cc hw x).1.continuous (sa16z_F_cc hw x).2
  have h2 := sa16z_g_mul_int hs.le hsd (w := fun z => w' (x - z)) (sa16z_F_cc hw' x).1.continuous (sa16z_F_cc hw' x).2
  rw [← integral_add h1 h2]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [mul_add]

lemma sa16y5f_cv_rho_smul (c : ℝ) (w : Euc d → ℝ) :
    sa16r_cv (rieszKernel d s) (fun y => c * w y) = fun x => c * sa16r_cv (rieszKernel d s) w x := by
  funext x
  unfold sa16r_cv
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  ring

lemma sa16y5f_S_add (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) {a b φ : Euc d → ℝ} (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) (hφ : IsCcInfty φ) (i j : Fin d) (x : Euc d) :
    sa16y5_S d s (fun y => a y + b y) φ i j x = sa16y5_S d s a φ i j x + sa16y5_S d s b φ i j x := by
  have hwa : IsCcInfty (fun y' => a y' * fderiv ℝ φ y' (sa16z_e j)) :=
    sa16y5_cc_mul ha (sa16s_cc_fderiv hφ (sa16z_e j))
  have hwb : IsCcInfty (fun y' => b y' * fderiv ℝ φ y' (sa16z_e j)) :=
    sa16y5_cc_mul hb (sa16s_cc_fderiv hφ (sa16z_e j))
  unfold sa16y5_S
  have e : (fun y' => (a y' + b y') * fderiv ℝ φ y' (sa16z_e j)) =
      fun y' => a y' * fderiv ℝ φ y' (sa16z_e j) + b y' * fderiv ℝ φ y' (sa16z_e j) := by
    funext y'; ring
  rw [e]
  have e2 : sa16r_cv (rieszKernel d s) (fun y' => a y' * fderiv ℝ φ y' (sa16z_e j) +
      b y' * fderiv ℝ φ y' (sa16z_e j)) = fun y => sa16r_cv (rieszKernel d s) (fun y' => a y' *
        fderiv ℝ φ y' (sa16z_e j)) y + sa16r_cv (rieszKernel d s) (fun y' => b y' * fderiv ℝ φ y' (sa16z_e j)) y :=
    funext (sa16y5f_cv_rho_add hd hs hsd hwa hwb)
  rw [e2, fderiv_fun_add
    (((sa16y5_cv_cc_contDiff (sa16y5_rho_loc hd hs hsd) hwa).differentiable (by simp)) x)
    (((sa16y5_cv_cc_contDiff (sa16y5_rho_loc hd hs hsd) hwb).differentiable (by simp)) x)]
  rfl

lemma sa16y5f_S_smul (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) {a φ : Euc d → ℝ} (c : ℝ)
    (ha : ContDiff ℝ ∞ a) (hφ : IsCcInfty φ) (i j : Fin d) (x : Euc d) :
    sa16y5_S d s (fun y => c * a y) φ i j x = c * sa16y5_S d s a φ i j x := by
  have hwa : IsCcInfty (fun y' => a y' * fderiv ℝ φ y' (sa16z_e j)) :=
    sa16y5_cc_mul ha (sa16s_cc_fderiv hφ (sa16z_e j))
  unfold sa16y5_S
  have e : (fun y' => (c * a y') * fderiv ℝ φ y' (sa16z_e j)) =
      fun y' => c * (a y' * fderiv ℝ φ y' (sa16z_e j)) := by
    funext y'; ring
  rw [e, sa16y5f_cv_rho_smul]
  have hd' := ((sa16y5_cv_cc_contDiff (sa16y5_rho_loc hd hs hsd) hwa).differentiable (by simp)) x
  rw [fderiv_const_mul hd']
  simp

lemma sa16y5f_fop_add (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (M : Matrix (Fin d) (Fin d) ℝ) {m : ℕ}
    {a b : Euc d → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    {T T' : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p} (hT : SA16FOp d m p s M a T)
    (hT' : SA16FOp d m p s M b T') : SA16FOp d m p s M (fun y => a y + b y) (T + T') := by
  intro φ
  filter_upwards [hT φ, hT' φ, sa16r_wrep_add d m p (T (sa16r_Jcc d (m + 1 + 1) p φ))
    (T' (sa16r_Jcc d (m + 1 + 1) p φ))] with x e1 e2 e3
  rw [ContinuousLinearMap.add_apply, e3, e1, e2, sa16y5_euc_eq, sa16y5_euc_eq, sa16y5_euc_eq]
  simp only
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sa16y5f_S_add hd hs hsd ha hb φ.2 i j x]
  ring

lemma sa16y5f_fop_smul (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (M : Matrix (Fin d) (Fin d) ℝ) {m : ℕ} (c : ℝ)
    {a : Euc d → ℝ} (ha : ContDiff ℝ ∞ a) {T : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p}
    (hT : SA16FOp d m p s M a T) : SA16FOp d m p s M (fun y => c * a y) (c • T) := by
  intro φ
  filter_upwards [hT φ, sa16r_wrep_smul d m p c (T (sa16r_Jcc d (m + 1 + 1) p φ))] with x e1 e2
  rw [ContinuousLinearMap.smul_apply, e2, e1, sa16y5_euc_eq, sa16y5_euc_eq]
  simp only
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sa16y5f_S_smul hd hs hsd c ha φ.2 i j x]
  ring

theorem sa16y5f_fop_sum (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (M : Matrix (Fin d) (Fin d) ℝ) {m : ℕ}
    {ι : Type*} [DecidableEq ι] (w : ι → ℝ) (a : ι → Euc d → ℝ)
    (T : ι → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p) (S : Finset ι)
    (hG : ∀ i ∈ S, ContDiff ℝ ∞ (a i)) (hT : ∀ i ∈ S, SA16FOp d m p s M (a i) (T i)) :
    ContDiff ℝ ∞ (fun y => ∑ i ∈ S, w i * a i y) ∧
      SA16FOp d m p s M (fun y => ∑ i ∈ S, w i * a i y) (∑ i ∈ S, w i • T i) := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨contDiff_const, fun φ => ?_⟩
    simp only [Finset.sum_empty, ContinuousLinearMap.zero_apply]
    filter_upwards [sa16r_wrep_zero (d := d) (k := m) (p := p)] with x hx
    rw [hx, sa16y5_euc_eq]
    refine (Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_).symm
    have := sa16y5f_S_smul hd hs hsd (0 : ℝ) (a := fun _ : Euc d => (1 : ℝ)) contDiff_const φ.2 i j x
    simp only [zero_mul] at this
    rw [this]; simp
  | insert i S hi ih =>
    obtain ⟨ihG, ihT⟩ := ih (fun j hj => hG j (Finset.mem_insert_of_mem hj))
      (fun j hj => hT j (Finset.mem_insert_of_mem hj))
    have hGi : ContDiff ℝ ∞ (fun y => w i * a i y) := contDiff_const.mul (hG i (Finset.mem_insert_self _ _))
    have hTi := sa16y5f_fop_smul hd hs hsd M (w i) (hG i (Finset.mem_insert_self _ _))
      (hT i (Finset.mem_insert_self _ _))
    have e1 : (fun y => ∑ j ∈ insert i S, w j * a j y) = fun y => w i * a i y + ∑ j ∈ S, w j * a j y := by
      funext y; rw [Finset.sum_insert hi]
    rw [e1, Finset.sum_insert hi]
    exact ⟨hGi.add ihG, sa16y5f_fop_add hd hs hsd M hGi ihG hTi ihT⟩

end Sf1

end HRS.Whole.AppendixA.Phase2SA16R
