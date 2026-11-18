import HRS.MS.S104eC2J

/-!
# S104E route C, packet C2, part K: jets of the directional derivative of a family, and the packed data of `k = ρ ∂_e f`

Prefix `s104c2_`, namespace `HRS.MS.S104e.C`.
* `s104c2_dirjet_sub`: `‖D^m (∂_e f)(y) - D^m (∂_e f')(y')‖ ≤ ‖e‖ ‖D^{m+1} f (y) - D^{m+1} f' (y')‖`;
* `s104c2_dir_jc`: `JC S j (fun v y => fderiv (G v) y e)` if the jets `≤ j+1` of `G` are jointly continuous;
* `s104c2_k_pack`: `movForce d s (ρ ∂_e f) · i = ultK κ_i k` with the Hölder/decay data of the jets of `k = ρ ∂_e f` (as in `s104c2_force_term`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.Ul HRS.MS.R2WinOrbNL

variable {d : ℕ}

lemma s104c2_dirjet_sub {m : ℕ} {f f' : Euc d → ℝ} (hf : ContDiff ℝ (m + 1) f) (hf' : ContDiff ℝ (m + 1) f')
    (e y y' : Euc d) :
    ‖iteratedFDeriv ℝ m (fun z => fderiv ℝ f z e) y - iteratedFDeriv ℝ m (fun z => fderiv ℝ f' z e) y'‖ ≤
      ‖e‖ * ‖iteratedFDeriv ℝ (m + 1) f y - iteratedFDeriv ℝ (m + 1) f' y'‖ := by
  set g : (Euc d →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ e with hg
  have hcd : ∀ {F : Euc d → ℝ}, ContDiff ℝ (m + 1) F → ContDiff ℝ m (fderiv ℝ F) := fun hF =>
    hF.fderiv_right (by exact_mod_cast le_refl (m + 1))
  have h1 : iteratedFDeriv ℝ m (fun z => fderiv ℝ f z e) y =
      g.compContinuousMultilinearMap (iteratedFDeriv ℝ m (fderiv ℝ f) y) :=
    g.iteratedFDeriv_comp_left (hcd hf).contDiffAt (by exact_mod_cast le_rfl)
  have h2 : iteratedFDeriv ℝ m (fun z => fderiv ℝ f' z e) y' =
      g.compContinuousMultilinearMap (iteratedFDeriv ℝ m (fderiv ℝ f') y') :=
    g.iteratedFDeriv_comp_left (hcd hf').contDiffAt (by exact_mod_cast le_rfl)
  have hsub : ∀ a b : Euc d [×m]→L[ℝ] (Euc d →L[ℝ] ℝ),
      g.compContinuousMultilinearMap a - g.compContinuousMultilinearMap b = g.compContinuousMultilinearMap (a - b) := by
    intro a b; ext v; simp
  rw [h1, h2, hsub]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  have hgn : ‖g‖ ≤ ‖e‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg e) fun T => by
      simpa [hg, mul_comm] using T.le_opNorm e
  have hr : ∀ (F : Euc d → ℝ) (z : Euc d), iteratedFDeriv ℝ m (fderiv ℝ F) z =
      (continuousMultilinearCurryRightEquiv' ℝ m (Euc d) ℝ) (iteratedFDeriv ℝ (m + 1) F z) := fun F z => by
    rw [iteratedFDeriv_succ_eq_comp_right]; simp
  rw [hr f y, hr f' y', ← (continuousMultilinearCurryRightEquiv' ℝ m (Euc d) ℝ).map_sub, LinearIsometryEquiv.norm_map]
  exact mul_le_mul_of_nonneg_right hgn (norm_nonneg _)

theorem s104c2_dir_jc {S : Set ℝ} {j : ℕ} {G : ℝ → Euc d → ℝ} (hG1 : ∀ v ∈ S, ContDiff ℝ (j + 1) (G v))
    (hGc : ∀ i ≤ j + 1, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (G p.1) p.2) (S ×ˢ univ))
    (e : Euc d) : JC S j (fun v y => fderiv ℝ (G v) y e) := by
  refine ⟨fun v hv => ((hG1 v hv).fderiv_right (by exact_mod_cast le_refl (j + 1))).clm_apply contDiff_const,
    fun m hm p0 hp0 => ?_⟩
  have hmj : m + 1 ≤ j + 1 := by omega
  have hcont := hGc (m + 1) hmj p0 hp0
  have h1 := (tendsto_iff_norm_sub_tendsto_zero.1 hcont).const_mul ‖e‖
  rw [mul_zero] at h1
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  refine squeeze_zero' (Filter.Eventually.of_forall fun p => norm_nonneg _) ?_ h1
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact s104c2_dirjet_sub ((hG1 p.1 hp.1).of_le (by exact_mod_cast hmj)) ((hG1 p0.1 hp0.1).of_le (by exact_mod_cast hmj)) e p.2 p0.2

theorem s104c2_k_pack (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (j : ℕ) {η : ℝ}
    (hη0 : max 0 (s - d + 1) < η) (hη1 : η < 1) {L : ℝ} (hL : (d : ℝ) + j + s + 4 < L) (i : Fin d)
    {A : ℝ} {ρ : Euc d → ℝ} (hρ : U2Dec (j + 1) L A ρ) {B : ℝ} {f : Euc d → ℝ} (hf : HolB j η B f)
    (e : Euc d) (he : ‖e‖ = 1) :
      (fun x => movForce d s (fun y => ρ y * fderiv ℝ f y e) x i) = ultK (u2_kap d s i) (fun y => ρ y * fderiv ℝ f y e) ∧
      (∀ m ≤ j, ∀ x, iteratedFDeriv ℝ m (ultK (u2_kap d s i) (fun y => ρ y * fderiv ℝ f y e)) x =
        ultK (u2_kap d s i) (iteratedFDeriv ℝ m (fun y => ρ y * fderiv ℝ f y e)) x) ∧
      ContDiff ℝ j (ultK (u2_kap d s i) (fun y => ρ y * fderiv ℝ f y e)) ∧
      ContDiff ℝ j (fun y => ρ y * fderiv ℝ f y e) ∧
      (∀ m ≤ j, HolNear η (2 ^ j * A * (B * 1 + 2 * (B * 1))) (iteratedFDeriv ℝ m (fun y => ρ y * fderiv ℝ f y e))) ∧
      (∀ m ≤ j, ∀ y, ‖iteratedFDeriv ℝ m (fun y => ρ y * fderiv ℝ f y e) y‖ ≤ A * (B * 1) * 2 ^ j * u2Wt L y) := by
  have hηp : 0 < η := lt_of_le_of_lt (le_max_left _ _) hη0
  have hηd : s + 1 - η < (d : ℝ) := by
    have := lt_of_le_of_lt (le_max_right _ _) hη0
    linarith
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hd1 : 1 ≤ d := by omega
  have hL' : (d : ℝ) < L := by linarith
  have hL0 : 0 ≤ L := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hker := ult_ker_kap (d := d) hs0 hsd i
  have hB0 : 0 ≤ B := hf.bd.nonneg
  have hA : 0 ≤ A := by
    have := (norm_nonneg _).trans (hρ.2 0 (Nat.zero_le _) 0)
    exact (mul_nonneg_iff_of_pos_right (u2Wt_pos (d := d) L 0)).1 this
  obtain ⟨hkd, hkh⟩ := s104c2_k_data hηp hη1.le hL0 hρ hf e
  rw [he] at hkd hkh
  have hA' : 0 ≤ A * (B * 1) * 2 ^ j := by positivity
  have hH : 0 ≤ 2 ^ j * A * (B * 1 + 2 * (B * 1)) := by positivity
  have hkb0 : ∀ y, ‖(fun y => ρ y * fderiv ℝ f y e) y‖ ≤ A * (B * 1) * 2 ^ j * u2Wt L y := fun y => by
    have := hkd.2 0 (Nat.zero_le _) y
    rwa [norm_iteratedFDeriv_zero] at this
  have hfun : (fun x => movForce d s (fun y => ρ y * fderiv ℝ f y e) x i) =
      ultK (u2_kap d s i) (fun y => ρ y * fderiv ℝ f y e) := by
    funext x
    exact (s104c2_conv_comp hd1 hs0 hsd hη1 hηd hH hL' hA' hkd.1.continuous
      (s104c2_hol_zero (hkh 0 (Nat.zero_le _))) hkb0 x).2 i
  obtain ⟨hit, hcd⟩ := s104c2_K_iter hd1 hker hη1 hηd hH hL' hA' hkd hkh
  exact ⟨hfun, hit, hcd, hkd.1, hkh, fun m hm y => hkd.2 m hm y⟩

end HRS.MS.S104e.C

end
