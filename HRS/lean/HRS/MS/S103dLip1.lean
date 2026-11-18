import HRS.MS.MovSchAux4

/-!
# S10.3 (S103D), part 1: the weighted Lipschitz estimate of the divergence of the flux `Y_u`

Namespace `HRS.MS.MovSch`, prefix `s103d_`.  Paper: `S103_weighted_time_continuity` (estimate (nonlinlip)).  For `u, w ∈ Σ^m`
(`m : ℕ`, `K + d/2 + 4 < m`) with `‖u‖, ‖w‖ ≤ R`:
* `s103d_Y_diff`: `Y_u - Y_w = ν∇h_c + h_c • A + ρ • F_c + h_c • F_u + h_w • F_c` with `c = u - w` (pointwise, `A = q x + ∇g*ρ`).
* `s103d_Y_lip`: the difference `Y_u - Y_w` is in `s64_W (K+1) L` with constant `MY * ‖u - w‖`.
* `s103d_div_lip`: `x ↦ div Y_u x - div Y_w x` is `C^K` with `⟨x⟩^L ‖D^k ·‖ ≤ M * ‖u - w‖` for `k ≤ K`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovSch

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd HRS.MS.Mov63

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ} {m K : ℕ}

/-- The flux difference in terms of the increment `c = u - w`. -/
lemma s103d_Y_diff (H : Mov2dTh d s β q ρ) (hm : (d : ℝ) / 2 + 3 < m) (u w : OscSpace d (m : ℝ)) (x : Euc d) :
    mneY d s q β ρ hm u x - mneY d s q β ρ hm w x =
      β⁻¹ • gradient (mnc_hu ρ (mne_hn hm) (u - w)) x +
        mnc_hu ρ (mne_hn hm) (u - w) x • (q • x + movForce d s ρ x) +
        ρ x • mneFo d s ρ hm (u - w) x +
        mnc_hu ρ (mne_hn hm) (u - w) x • mneFo d s ρ hm u x +
        mnc_hu ρ (mne_hn hm) w x • mneFo d s ρ hm (u - w) x := by
  have hhc : mnc_hu ρ (mne_hn hm) (u - w) =
      fun y => mnc_hu ρ (mne_hn hm) u y - mnc_hu ρ (mne_hn hm) w y := mne_hu_sub hm u w
  have hgrad : gradient (mnc_hu ρ (mne_hn hm) (u - w)) x =
      gradient (mnc_hu ρ (mne_hn hm) u) x - gradient (mnc_hu ρ (mne_hn hm) w) x := by
    rw [hhc]
    unfold gradient
    have hd1 : DifferentiableAt ℝ (mnc_hu ρ (mne_hn hm) u) x :=
      ((mne_hu_cd hm H u).differentiable (by norm_num)) x
    have hd2 : DifferentiableAt ℝ (mnc_hu ρ (mne_hn hm) w) x :=
      ((mne_hu_cd hm H w).differentiable (by norm_num)) x
    have : fderiv ℝ (fun y => mnc_hu ρ (mne_hn hm) u y - mnc_hu ρ (mne_hn hm) w y) x =
        fderiv ℝ (mnc_hu ρ (mne_hn hm) u) x - fderiv ℝ (mnc_hu ρ (mne_hn hm) w) x :=
      (hd1.hasFDerivAt.sub hd2.hasFDerivAt).fderiv
    rw [this, map_sub]
  have hFc := mne_Fo_sub hm H u w x
  have hhcx : mnc_hu ρ (mne_hn hm) (u - w) x =
      mnc_hu ρ (mne_hn hm) u x - mnc_hu ρ (mne_hn hm) w x := by rw [hhc]
  rw [s64_Y_decomp H hm u x, s64_Y_decomp H hm w x, hgrad, hFc, hhcx]
  module

lemma s103d_Y_lip (H : Mov2dTh d s β q ρ) (hmK : (K : ℝ) + d / 2 + 4 < m) (L : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ MY : ℝ, 0 ≤ MY ∧ ∀ u w : OscSpace d (m : ℝ), ‖u‖ ≤ R → ‖w‖ ≤ R →
      s64_W (K + 1) L (fun x => mneY d s q β ρ (s64_hm3 hmK) u x - mneY d s q β ρ (s64_hm3 hmK) w x)
        (MY * ‖u - w‖) := by
  obtain ⟨Mh1, hMh1, h1⟩ := s64_h_W H hmK L
  obtain ⟨Mh2, hMh2, h2⟩ := s64_h_W H hmK (L + 1)
  obtain ⟨Mρ, hMρ⟩ := s64_rho_W H (K + 1) L
  obtain ⟨BA, hBA⟩ := s64_A_P H (K + 1)
  obtain ⟨CF, hCF0, hCF⟩ := s64_Fu_bdd H hmK
  have hMρ0 := s64_W_nonneg hMρ
  have hBA0 := s64_P_nonneg hBA
  set c : ℝ := 2 ^ (K + 1) with hc
  have hc0 : 0 < c := by positivity
  refine ⟨|β⁻¹| * Mh1 + c * (Mh2 * BA) + c * (Mρ * CF) + c * (Mh1 * CF * R) + c * (Mh1 * CF * R),
    by positivity, fun u w hu hw => ?_⟩
  have hn0 : 0 ≤ ‖u - w‖ := norm_nonneg _
  set h := mnc_hu ρ (mne_hn (s64_hm3 hmK)) (u - w) with hh
  set hw' := mnc_hu ρ (mne_hn (s64_hm3 hmK)) w with hhw
  set Fc := mneFo d s ρ (s64_hm3 hmK) (u - w) with hFc
  set Fu := mneFo d s ρ (s64_hm3 hmK) u with hFu
  have hFcP : s64_P (K + 1) 0 Fc (CF * ‖u - w‖) :=
    ⟨(hCF (u - w)).1, fun k hk x => by simpa using (hCF (u - w)).2 k hk x⟩
  have hFuP : s64_P (K + 1) 0 Fu (CF * ‖u‖) :=
    ⟨(hCF u).1, fun k hk x => by simpa using (hCF u).2 k hk x⟩
  have hT1 : s64_W (K + 1) L (fun x => β⁻¹ • gradient h x) (|β⁻¹| * (Mh1 * ‖u - w‖)) :=
    s64_W_const_smul β⁻¹ (s64_W_gradient (n := K + 1) (h1 (u - w)))
  have hT2 : s64_W (K + 1) L (fun x => h x • (q • x + movForce d s ρ x)) (c * ((Mh2 * ‖u - w‖) * BA)) :=
    s64_W_smul (L := L) (p := 1) (s64_W_mono_n (by omega) (h2 (u - w))) hBA
  have hT3 : s64_W (K + 1) L (fun x => ρ x • Fc x) (c * (Mρ * (CF * ‖u - w‖))) :=
    s64_W_smul (L := L) (p := 0) hMρ hFcP
  have hT4 : s64_W (K + 1) L (fun x => h x • Fu x) (c * ((Mh1 * ‖u - w‖) * (CF * ‖u‖))) :=
    s64_W_smul (L := L) (p := 0) (s64_W_mono_n (by omega) (h1 (u - w))) hFuP
  have hT5 : s64_W (K + 1) L (fun x => hw' x • Fc x) (c * ((Mh1 * ‖w‖) * (CF * ‖u - w‖))) :=
    s64_W_smul (L := L) (p := 0) (s64_W_mono_n (by omega) (h1 w)) hFcP
  have hsum := s64_W_add (s64_W_add (s64_W_add (s64_W_add hT1 hT2) hT3) hT4) hT5
  have hfun : (fun x => mneY d s q β ρ (s64_hm3 hmK) u x - mneY d s q β ρ (s64_hm3 hmK) w x) = fun x =>
      (((β⁻¹ • gradient h x + h x • (q • x + movForce d s ρ x)) + ρ x • Fc x) + h x • Fu x) +
        hw' x • Fc x := by
    funext x
    rw [s103d_Y_diff H (s64_hm3 hmK) u w x]
  rw [hfun]
  refine s64_W_mono_M ?_ hsum
  have h4 : (Mh1 * ‖u - w‖) * (CF * ‖u‖) ≤ (Mh1 * CF * R) * ‖u - w‖ := by
    have : (Mh1 * ‖u - w‖) * (CF * ‖u‖) = (Mh1 * CF * ‖u‖) * ‖u - w‖ := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu (mul_nonneg hMh1 hCF0)) hn0
  have h5 : (Mh1 * ‖w‖) * (CF * ‖u - w‖) ≤ (Mh1 * CF * R) * ‖u - w‖ := by
    have : (Mh1 * ‖w‖) * (CF * ‖u - w‖) = (Mh1 * CF * ‖w‖) * ‖u - w‖ := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw (mul_nonneg hMh1 hCF0)) hn0
  have h4' := mul_le_mul_of_nonneg_left h4 hc0.le
  have h5' := mul_le_mul_of_nonneg_left h5 hc0.le
  nlinarith

lemma s103d_div_lip (H : Mov2dTh d s β q ρ) (hmK : (K : ℝ) + d / 2 + 4 < m) (L : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u w : OscSpace d (m : ℝ), ‖u‖ ≤ R → ‖w‖ ≤ R →
      ContDiff ℝ (K : WithTop ℕ∞)
        (fun x => movDiv (mneY d s q β ρ (s64_hm3 hmK) u) x - movDiv (mneY d s q β ρ (s64_hm3 hmK) w) x) ∧
      ∀ k ≤ K, ∀ x : Euc d,
        movBracket x ^ L * ‖iteratedFDeriv ℝ k
          (fun x => movDiv (mneY d s q β ρ (s64_hm3 hmK) u) x - movDiv (mneY d s q β ρ (s64_hm3 hmK) w) x) x‖
          ≤ M * ‖u - w‖ := by
  obtain ⟨MY, hMY, hY⟩ := s103d_Y_lip H hmK L hR
  refine ⟨‖HRS.MS.MovForce.movb2_divL d‖ * MY, by positivity, fun u w hu hw => ?_⟩
  have hW := s64_W_div (n := K) (hY u w hu hw)
  have e : (fun x => movDiv (mneY d s q β ρ (s64_hm3 hmK) u) x - movDiv (mneY d s q β ρ (s64_hm3 hmK) w) x) =
      fun x => movDiv (fun y => mneY d s q β ρ (s64_hm3 hmK) u y - mneY d s q β ρ (s64_hm3 hmK) w y) x := by
    funext x
    rw [mne_movDiv_sub (((mne_Y_cd (s64_hm3 hmK) H u).differentiable one_ne_zero) x)
      (((mne_Y_cd (s64_hm3 hmK) H w).differentiable one_ne_zero) x)]
  rw [e]
  refine ⟨hW.1, fun k hk x => ?_⟩
  have := hW.2 k hk x
  rw [mul_assoc]
  exact this

end HRS.MS.MovSch

end
