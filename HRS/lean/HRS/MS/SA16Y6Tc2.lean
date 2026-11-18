import HRS.MS.SA16Y6Tc1
import HRS.MS.SA16QSm5
import HRS.MS.ToriCoefAAux1

/-!
# S.A.16 (SA16Y6) Tc2: derivatives, jets and the `L^p` bound of the Riesz transform on `C_c^∞` (boundary `s = d-1`)

`sa16y6_R_fderiv`: `∂_l R_i f = R_i ∂_l f`; `sa16y6_R_pd`: all partial derivatives; `sa16y6_BS`: smooth with all jets bounded
(`sa16y6_R_BS`); `sa16y6_R_Lp`: `‖R_i f‖_p ≤ C ‖f‖_p` (Calderón-Zygmund, `p ≥ 2`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q HRS.MS.ToriCoefA

section Tc2
variable {d : ℕ}

/-- smooth with all jets bounded -/
def sa16y6_BS (V : Euc d → ℝ) : Prop :=
  ContDiff ℝ ∞ V ∧ ∀ n : ℕ, ∃ B : ℝ, ∀ x, ‖iteratedFDeriv ℝ n V x‖ ≤ B

lemma sa16y6_BS_fderiv {V : Euc d → ℝ} (hV : sa16y6_BS V) (j : Fin d) :
    sa16y6_BS (fun y => fderiv ℝ V y (sa16z_e j)) := by
  refine ⟨(hV.1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const, fun n => ?_⟩
  obtain ⟨B, hB⟩ := hV.2 (n + 1)
  exact ⟨B, fun x => (sa16q_norm_iter_pd_le hV.1 j n x).trans (hB x)⟩

lemma sa16y6_BS_sub {V W : Euc d → ℝ} (hV : sa16y6_BS V) (hW : sa16y6_BS W) :
    sa16y6_BS (fun y => V y - W y) := by
  refine ⟨hV.1.sub hW.1, fun n => ?_⟩
  obtain ⟨B1, h1⟩ := hV.2 n
  obtain ⟨B2, h2⟩ := hW.2 n
  refine ⟨B1 + B2, fun x => ?_⟩
  have e : (fun y => V y - W y) = V - W := rfl
  have hn : ((n : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  rw [e, iteratedFDeriv_sub_apply (hV.1.contDiffAt.of_le hn) (hW.1.contDiffAt.of_le hn)]
  exact (norm_sub_le _ _).trans (add_le_add (h1 x) (h2 x))

lemma sa16y6_D_comm {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (i l : Fin d) (y : Euc d) :
    fderiv ℝ (fun z => fderiv ℝ f z (sa16z_e i)) y (sa16z_e l) =
      fderiv ℝ (fun z => fderiv ℝ f z (sa16z_e l)) y (sa16z_e i) := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) y :=
    ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) y
  have hs := (hf.contDiffAt (x := y)).isSymmSndFDerivAt (by simp [minSmoothness])
  have e : ∀ v w : Euc d, fderiv ℝ (fun z => fderiv ℝ f z v) y w = fderiv ℝ (fderiv ℝ f) y w v := by
    intro v w
    rw [fderiv_clm_apply hdf (differentiableAt_const v)]
    simp
  rw [e, e]
  exact hs _ _

lemma sa16y6_R_fderiv (hd : 1 ≤ d) {s : ℝ} (hs : s = (d : ℝ) - 1) {f : Euc d → ℝ} (hf : IsCcInfty f) (i l : Fin d)
    (x : Euc d) :
    fderiv ℝ (sa16y6_R d i f) x (sa16z_e l) =
      sa16y6_R d i (fun y => fderiv ℝ f y (sa16z_e l)) x := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have hsd : s < d := by rw [hs]; linarith
  have hk := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have hDi := sa16s_cc_fderiv hf (sa16z_e i)
  have hDl := sa16s_cc_fderiv hf (sa16z_e l)
  have e : sa16y6_R d i f = fun x => -(HRS.CZ.Hls.hlsg_c s)⁻¹ *
      sa16r_cv (rieszKernel d s) (fun y => fderiv ℝ f y (sa16z_e i)) x :=
    funext fun x => sa16y6_R_eq hd hs hf i x
  have hdiff : DifferentiableAt ℝ (sa16r_cv (rieszKernel d s) (fun y => fderiv ℝ f y (sa16z_e i))) x :=
    ((sa16y5_cv_cc_contDiff hk hDi).differentiable (by simp)) x
  rw [e, fderiv_const_mul hdiff]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [sa16y5_cv_fderiv hk hDi x (sa16z_e l), sa16y6_R_eq hd hs hDl i x]
  congr 2
  funext y
  exact sa16y6_D_comm hf.1 i l y

lemma sa16y6_R_pd (hd : 1 ≤ d) {s : ℝ} (hs : s = (d : ℝ) - 1) {f : Euc d → ℝ} (hf : IsCcInfty f) (i : Fin d) :
    ∀ (j : ℕ) (idx : Fin j → Fin d),
      partialDeriv idx (sa16y6_R d i f) = sa16y6_R d i (partialDeriv idx f) := by
  intro j
  induction j with
  | zero =>
    intro idx
    funext x
    rw [sa16j_pd_zero]
    have : partialDeriv idx f = f := funext fun x => sa16j_pd_zero idx f x
    rw [this]
  | succ j ih =>
    intro idx
    obtain ⟨l, idx', rfl⟩ : ∃ (l : Fin d) (idx' : Fin j → Fin d), idx = Fin.cons l idx' :=
      ⟨idx 0, Fin.tail idx, (Fin.cons_self_tail idx).symm⟩
    funext x
    rw [sa16s_pd_cons (sa16y6_R_contDiff hd hs hf i) l idx' x, ih idx',
      sa16y6_R_fderiv hd hs (sa16s_cc_partialDeriv hf idx') i l x]
    congr 1
    funext y
    exact (sa16s_pd_cons hf.1 l idx' y).symm

lemma sa16y6_R_BS (hd : 1 ≤ d) {s : ℝ} (hs : s = (d : ℝ) - 1) {f : Euc d → ℝ} (hf : IsCcInfty f) (i : Fin d) :
    sa16y6_BS (sa16y6_R d i f) := by
  refine ⟨sa16y6_R_contDiff hd hs hf i, fun n => ?_⟩
  have hb : ∀ idx : Fin n → Fin d, ∃ B : ℝ, ∀ x, |partialDeriv idx (sa16y6_R d i f) x| ≤ B := by
    intro idx
    rw [sa16y6_R_pd hd hs hf i n idx]
    exact sa16y6_R_bdd hd (sa16s_cc_partialDeriv hf idx) i
  choose B hB using hb
  refine ⟨∑ idx : Fin n → Fin d, B idx, fun x => ?_⟩
  exact (tca_norm_iteratedFDeriv_le_sum n _ x).trans (Finset.sum_le_sum fun idx _ => hB idx x)

lemma sa16y6_R_Lp (hd : 1 ≤ d) {p : ℝ} (hp : 2 ≤ p) (i : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Euc d → ℝ, IsCcInfty f →
      eLpNorm (sa16y6_R d i f) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC⟩ := HRS.CZ.PvAsm.lp_screened_negative_order_theta_one_coord hd hp i
  refine ⟨max C 0, le_max_right _ _, fun f hf => ?_⟩
  have h1 : MemLp (fun _ : Euc d => (1 : ℝ)) ⊤ volume := memLp_top_const 1
  have hfL : MemLp f (ENNReal.ofReal p) volume := hf.1.continuous.memLp_of_hasCompactSupport hf.2
  have h := hC (fun _ => 1) f h1 hfL
  have e : (fun x => (fun _ : Euc d => (1 : ℝ)) x * f x) = f := funext fun x => one_mul _
  rw [e] at h
  have hne : (volume : Measure (Euc d)) ≠ 0 := by
    haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    exact NeZero.ne _
  have h2 : eLpNorm (fun _ : Euc d => (1 : ℝ)) ⊤ volume = 1 := by
    have := eLpNorm_const (μ := (volume : Measure (Euc d))) (p := (⊤ : ℝ≥0∞)) (1 : ℝ) ENNReal.top_ne_zero hne
    simpa using this
  rw [h2, mul_one] at h
  exact h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) le_rfl)

end Tc2

end HRS.Whole.AppendixA.Phase2SA16R
