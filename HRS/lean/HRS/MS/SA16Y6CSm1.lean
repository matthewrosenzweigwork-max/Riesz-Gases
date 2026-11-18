import HRS.MS.SA16Y6COp1
import HRS.MS.SA16Y4Nc8
import HRS.MS.SA16Y6C1
import HRS.MS.SA16Y5Sm1

/-! # SA16Y6 critical-case copy of SA16Y5Sm1 (s = d-1) -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Sm1
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]
lemma sa16y6c_cc_D {a φ : Euc d → ℝ} (ha1 : ContDiff ℝ 1 a) (hφ : IsCcInfty φ) (j : Fin d) :
    ContDiff ℝ 1 (fun y => a y * fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) ∧
      HasCompactSupport (fun y => a y * fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) := by
  have h := sa16s_cc_fderiv hφ (sa16z_e j)
  exact ⟨ha1.mul (h.1.of_le (by exact_mod_cast le_top)), h.2.mul_left⟩

lemma sa16y6c_convFun_int {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {f : Euc d → ℝ} (hf : Continuous f)
    (hfs : HasCompactSupport f) (x : Euc d) :
    Integrable (fun y => rieszKernel d s (x - y) * f y) := by
  have h := (rieszKernel_locallyIntegrable (d := d) hs0 hsd).integrable_smul_right_of_hasCompactSupport
    (hf.comp (continuous_const.sub continuous_id : Continuous fun z : Euc d => x - z))
    (by
      have : HasCompactSupport (fun z : Euc d => f (x - z)) := by
        have := hfs.comp_homeomorph (Homeomorph.subLeft x)
        exact this
      exact this)
  have h2 := h.comp_sub_left x
  refine h2.congr (Eventually.of_forall fun y => ?_)
  simp [smul_eq_mul, sub_sub_cancel]

lemma sa16y6c_F_add_a (hd : 1 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs1 : s = (d : ℝ) - 1) (M : Matrix (Fin d) (Fin d) ℝ)
    {a b : Euc d → ℝ} (ha1 : ContDiff ℝ 1 a) (hb1 : ContDiff ℝ 1 b) {φ : Euc d → ℝ} (hφ : IsCcInfty φ)
    (x : Euc d) :
    HRS.MH.AdjointRd.eucNonlocal s M (fun y => a y + b y) φ x =
      HRS.MH.AdjointRd.eucNonlocal s M a φ x + HRS.MH.AdjointRd.eucNonlocal s M b φ x := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by rw [hs1]; linarith
  have hk := rieszKernel_locallyIntegrable (d := d) hs hsd
  unfold HRS.MH.AdjointRd.eucNonlocal
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_add]
  congr 1
  obtain ⟨h1a, h2a⟩ := sa16y6c_cc_D ha1 hφ j
  obtain ⟨h1b, h2b⟩ := sa16y6c_cc_D hb1 hφ j
  have e : (fun x' => ∫ y, rieszKernel d s (x' - y) * ((a y + b y) *
      fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ)))) = fun x' =>
      convFun (rieszKernel d s) (fun y => a y * fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) x' +
      convFun (rieszKernel d s) (fun y => b y * fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) x' := by
    funext x'
    unfold convFun
    rw [← integral_add (sa16y6c_convFun_int hs hsd h1a.continuous h2a x')
      (sa16y6c_convFun_int hs hsd h1b.continuous h2b x')]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    ring
  have hda := (sa16sp_convFun_fderiv hk h1a h2a x).1
  have hdb := (sa16sp_convFun_fderiv hk h1b h2b x).1
  have e2 : (fun x' => ∫ y, rieszKernel d s (x' - y) * ((a y) *
      fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ)))) = convFun (rieszKernel d s)
      (fun y => a y * fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) := rfl
  have e3 : (fun x' => ∫ y, rieszKernel d s (x' - y) * ((b y) *
      fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ)))) = convFun (rieszKernel d s)
      (fun y => b y * fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) := rfl
  rw [e, e2, e3, fderiv_fun_add hda hdb]
  simp

lemma sa16y6c_F_smul_a (hd : 1 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs1 : s = (d : ℝ) - 1) (M : Matrix (Fin d) (Fin d) ℝ)
    {a : Euc d → ℝ} (ha1 : ContDiff ℝ 1 a) {φ : Euc d → ℝ} (hφ : IsCcInfty φ) (c : ℝ) (x : Euc d) :
    HRS.MH.AdjointRd.eucNonlocal s M (fun y => c * a y) φ x = c * HRS.MH.AdjointRd.eucNonlocal s M a φ x := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by rw [hs1]; linarith
  have hk := rieszKernel_locallyIntegrable (d := d) hs hsd
  unfold HRS.MH.AdjointRd.eucNonlocal
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, mul_comm c (M j i), mul_assoc]
  congr 1
  obtain ⟨h1a, h2a⟩ := sa16y6c_cc_D ha1 hφ j
  have e : (fun x' => ∫ y, rieszKernel d s (x' - y) * ((c * a y) *
      fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ)))) = fun x' =>
      c * convFun (rieszKernel d s) (fun y => a y * fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) x' := by
    funext x'
    unfold convFun
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    ring
  have hda := (sa16sp_convFun_fderiv hk h1a h2a x).1
  have e2 : (fun x' => ∫ y, rieszKernel d s (x' - y) * ((a y) *
      fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ)))) = convFun (rieszKernel d s)
      (fun y => a y * fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) := rfl
  rw [e, e2, fderiv_const_mul hda]
  simp

lemma sa16y6c_isoop_add (hd : 1 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs1 : s = (d : ℝ) - 1) (M : Matrix (Fin d) (Fin d) ℝ) {m : ℕ}
    {a b : EuclideanSpace ℝ (Fin d) → ℝ} (ha : sa16y4_Good a) (hb : sa16y4_Good b)
    {T T' : WmpSpace d (m + 1) p →L[ℝ] WmpSpace d m p} (hT : SA16IsoOp d m p s M a T) (hT' : SA16IsoOp d m p s M b T') :
    SA16IsoOp d m p s M (fun y => a y + b y) (T + T') := by
  obtain ⟨ha1, B0, B1, h0, h1⟩ := ha
  obtain ⟨hb1, B0', B1', h0', h1'⟩ := hb
  intro φ
  filter_upwards [hT φ, hT' φ, sa16r_wrep_add d m p (T (sa16r_Jcc d (m + 1) p φ)) (T' (sa16r_Jcc d (m + 1) p φ))] with x e1 e2 e3
  rw [ContinuousLinearMap.add_apply, e3, e1, e2]
  exact (sa16y6c_F_add_a hd hs hs1 M ha1 hb1 φ.2 x).symm

lemma sa16y6c_isoop_smul (hd : 1 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs1 : s = (d : ℝ) - 1) (M : Matrix (Fin d) (Fin d) ℝ) {m : ℕ}
    (c : ℝ) {a : EuclideanSpace ℝ (Fin d) → ℝ} (ha : sa16y4_Good a)
    {T : WmpSpace d (m + 1) p →L[ℝ] WmpSpace d m p} (hT : SA16IsoOp d m p s M a T) :
    SA16IsoOp d m p s M (fun y => c * a y) (c • T) := by
  obtain ⟨ha1, B0, B1, h0, h1⟩ := ha
  intro φ
  filter_upwards [hT φ, sa16r_wrep_smul d m p c (T (sa16r_Jcc d (m + 1) p φ))] with x e1 e2
  rw [ContinuousLinearMap.smul_apply, e2, e1]
  exact (sa16y6c_F_smul_a hd hs hs1 M ha1 φ.2 c x).symm

theorem sa16y6c_isoop_sum (hd : 1 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs1 : s = (d : ℝ) - 1) (M : Matrix (Fin d) (Fin d) ℝ) {m : ℕ}
    {ι : Type*} [DecidableEq ι] (w : ι → ℝ) (a : ι → EuclideanSpace ℝ (Fin d) → ℝ)
    (T : ι → WmpSpace d (m + 1) p →L[ℝ] WmpSpace d m p) (S : Finset ι)
    (hG : ∀ i ∈ S, sa16y4_Good (a i)) (hT : ∀ i ∈ S, SA16IsoOp d m p s M (a i) (T i)) :
    sa16y4_Good (fun y => ∑ i ∈ S, w i * a i y) ∧
      SA16IsoOp d m p s M (fun y => ∑ i ∈ S, w i * a i y) (∑ i ∈ S, w i • T i) := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨⟨contDiff_const, 0, 0, fun y => by simp, fun y => by simp⟩, fun φ => ?_⟩
    simp only [Finset.sum_empty, ContinuousLinearMap.zero_apply]
    filter_upwards [sa16r_wrep_zero (d := d) (k := m) (p := p)] with x hx
    rw [hx]
    simp [HRS.MH.AdjointRd.eucNonlocal]
  | insert i S hi ih =>
    obtain ⟨ihG, ihT⟩ := ih (fun j hj => hG j (Finset.mem_insert_of_mem hj)) (fun j hj => hT j (Finset.mem_insert_of_mem hj))
    have hGi := sa16y4_good_smul (w i) (hG i (Finset.mem_insert_self _ _))
    have hTi := sa16y6c_isoop_smul hd hs hs1 M (w i) (hG i (Finset.mem_insert_self _ _)) (hT i (Finset.mem_insert_self _ _))
    have e1 : (fun y => ∑ j ∈ insert i S, w j * a j y) = fun y => w i * a i y + ∑ j ∈ S, w j * a j y := by
      funext y; rw [Finset.sum_insert hi]
    rw [e1, Finset.sum_insert hi]
    exact ⟨sa16y4_good_add hGi ihG, sa16y6c_isoop_add hd hs hs1 M hGi ihG hTi ihT⟩

end Sm1

end HRS.Whole.AppendixA.Phase2SA16R
