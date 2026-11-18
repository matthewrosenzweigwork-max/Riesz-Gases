import HRS.MS.MovSchAux2

/-!
# S64 (S6.4 `mov_schwartz`), part 3: representatives, `h_u`, `F_u`, the flux decomposition and the weighted flux bound

Namespace `HRS.MS.MovSch`, prefix `s64_`.  For `u ∈ Σ^m` with `K + d/2 + 4 < m`:
* `s64_V_eq`: the `C³` representative `mneV hm u` equals the `C^{K+3}` representative;
* `s64_h_W`: `h_u = √ρ V_u ∈ s64_W (K+2) L` (every `L`) with constant linear in `‖u‖`;
* `s64_Fu_bdd`: `F_u = ∇g*h_u ∈ C^{K+1}`, `‖D^k F_u‖ ≤ C‖u‖` (`mn_force_bound`, `j = K`);
* `s64_Y_decomp`: `Y_u = ν∇h_u + h_u • A + (ρ + h_u) • F_u`, `A = q x + ∇g*ρ`;
* `s64_Y_W`: for `‖u‖ ≤ R`, `Y_u ∈ s64_W (K+1) L` with constant `MY ‖u‖` (`MY` independent of `u`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovSch

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd HRS.MS.Mov63

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

section Rep

variable {m K : ℕ}

lemma s64_hm3 (hmK : (K : ℝ) + d / 2 + 4 < m) : (d : ℝ) / 2 + 3 < m := by
  have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  linarith

lemma s64_hK3 (hmK : (K : ℝ) + d / 2 + 4 < m) : ((K + 3 : ℕ) : ℝ) + d / 2 < m := by
  push_cast
  linarith

/-- The `C³` representative equals the `C^{K+3}` representative. -/
lemma s64_V_eq (hmK : (K : ℝ) + d / 2 + 4 < m) (u : OscSpace d (m : ℝ)) :
    mn_repFun 3 m (mne_hn (s64_hm3 hmK)) u = mn_repFun (K + 3) m (s64_hK3 hmK) u := by
  refine mn_repFun_eq (mne_hn (s64_hm3 hmK)) ?_
  obtain ⟨hc, f, hf, hfu, hfg⟩ := mn_repFun_spec (K + 3) m (s64_hK3 hmK) u
  exact ⟨hc.of_le (by exact_mod_cast (by omega : 3 ≤ K + 3)), f, hf, hfu, hfg⟩

lemma s64_h_eq (hmK : (K : ℝ) + d / 2 + 4 < m) (u : OscSpace d (m : ℝ)) :
    mnc_hu ρ (mne_hn (s64_hm3 hmK)) u = fun y => Real.sqrt (ρ y) * mn_repFun (K + 3) m (s64_hK3 hmK) u y := by
  funext y
  simp only [mnc_hu]
  rw [s64_V_eq hmK u]

lemma s64_h_W (H : Mov2dTh d s β q ρ) (hmK : (K : ℝ) + d / 2 + 4 < m) (L : ℕ) :
    ∃ Mh : ℝ, 0 ≤ Mh ∧ ∀ u : OscSpace d (m : ℝ),
      s64_W (K + 2) L (mnc_hu ρ (mne_hn (s64_hm3 hmK)) u) (Mh * ‖u‖) := by
  obtain ⟨M0, hM0⟩ := s64_sqrt_W H (K + 2) L
  obtain ⟨C0, hC0, hC⟩ := mn_repFun_bound (K + 3) m (s64_hK3 hmK) (d := d)
  have hM00 := s64_W_nonneg hM0
  refine ⟨2 ^ (K + 2) * (M0 * C0), by positivity, fun u => ?_⟩
  have hV : s64_P (K + 2) 0 (mn_repFun (K + 3) m (s64_hK3 hmK) u) (C0 * ‖u‖) :=
    s64_P_of_bdd 0 ((mn_repFun_contDiff (K + 3) m (s64_hK3 hmK) u).of_le (by exact_mod_cast (by omega : K + 2 ≤ K + 3)))
      (fun k hk x => hC u k (by omega) x)
  have := s64_W_smul (L := L) (p := 0) hM0 hV
  rw [s64_h_eq hmK u]
  have e : 2 ^ (K + 2) * (M0 * (C0 * ‖u‖)) = 2 ^ (K + 2) * (M0 * C0) * ‖u‖ := by ring
  rw [e] at this
  simpa [smul_eq_mul] using this

lemma s64_Fu_bdd (H : Mov2dTh d s β q ρ) (hmK : (K : ℝ) + d / 2 + 4 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : OscSpace d (m : ℝ),
      ContDiff ℝ ((K + 1 : ℕ) : WithTop ℕ∞) (mneFo d s ρ (s64_hm3 hmK) u) ∧
      ∀ k ≤ K + 1, ∀ x, ‖iteratedFDeriv ℝ k (mneFo d s ρ (s64_hm3 hmK) u) x‖ ≤ C * ‖u‖ := by
  have hm0 : (d : ℝ) / 2 + (K : ℝ) + 2 < m := by linarith
  obtain ⟨C, hC0, hC⟩ := mn_force_bound H.hd H.hs0 H.hsd β q H.hβ H.hq ρ H.hρ K m hm0
  refine ⟨C, hC0, fun u => ?_⟩
  have hv := mneV_cd (s64_hm3 hmK) u
  obtain ⟨-, -, h1, -, h5⟩ := hC (mneV (s64_hm3 hmK) u) hv.continuous (mneV_memOsc (s64_hm3 hmK) u)
  rw [mneV_norm (s64_hm3 hmK) u] at h5
  have hB : 0 ≤ C * ‖u‖ := mul_nonneg hC0 (norm_nonneg _)
  exact ⟨h1, fun k hk x => mne_cbVec_le hB h5 k hk x⟩

lemma s64_Y_decomp (H : Mov2dTh d s β q ρ) (hm : (d : ℝ) / 2 + 3 < m) (u : OscSpace d (m : ℝ)) (x : Euc d) :
    mneY d s q β ρ hm u x =
      β⁻¹ • gradient (mnc_hu ρ (mne_hn hm) u) x + mnc_hu ρ (mne_hn hm) u x • (q • x + movForce d s ρ x) +
        (ρ x + mnc_hu ρ (mne_hn hm) u x) • mneFo d s ρ hm u x := by
  have hρ3 : ContDiff ℝ 3 ρ := (mnc_rho_smooth H).of_le (by simp)
  have hh3 := mne_hu_cd hm H u
  have hgrad : gradient (mneRho ρ hm u) x = gradient ρ x + gradient (mnc_hu ρ (mne_hn hm) u) x := by
    unfold gradient
    have hd1 : DifferentiableAt ℝ ρ x := (hρ3.differentiable (by norm_num)) x
    have hd2 : DifferentiableAt ℝ (mnc_hu ρ (mne_hn hm) u) x := (hh3.differentiable (by norm_num)) x
    have : fderiv ℝ (mneRho ρ hm u) x = fderiv ℝ ρ x + fderiv ℝ (mnc_hu ρ (mne_hn hm) u) x :=
      (hd1.hasFDerivAt.add hd2.hasFDerivAt).fderiv
    rw [this, map_add]
  have hA := s64_A_eq H x
  have hF : movForce d s ρ x = -(β⁻¹ • gradient (fun y => Real.log (ρ y)) x) - q • x := by
    rw [← hA]; abel
  unfold mneY
  rw [hgrad, mne_force_split hm H u x, mne_grad_rho H x, hF]
  simp only [mneRho]
  have hβ : β⁻¹ * β⁻¹⁻¹ = 1 := by
    have := H.hβ.ne'
    field_simp
  module

end Rep

end HRS.MS.MovSch

end
