import HRS.MS.SA12X2R36W2

/-!
# S.A.12 R36 (SA12X2), part W3: weak top-piece bound `∫ ∂_eφ (K ⋆ ∂_vΦ)`

Split `K = Kn + Kf + c`. Near part: Schur with `‖Kn‖₁ = Cn r^(d-s)` (derivative on `φ`).
Far part: `∫ Kf(x-y) ∂_vΦ(y) dy = ∫ ∂_vKf(x-y) Φ(y) dy` (IBP in `y`), then W0 (IBP in `x` onto `φ`), leaving the
second derivative `∂_e∂_vKf = iteratedFDeriv 2 Kf (·) ![e,v]`, whose global L¹ norm is `C r^(-θ)` (`r3Kf_D2_l1`).
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12

open HRS HRS.Whole HRS.MH.AdjointRdP

variable {d : ℕ}

/-- The three-term split of the outer pairing for a continuous compactly supported `G`. -/
theorem sa12x2_split_G {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {r : ℝ} (hr : 0 < r)
    {G : Euc d → ℝ} (hG : Continuous G) (hGc : HasCompactSupport G)
    {φ : Euc d → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (e : Euc d) :
    ∫ x, fderiv ℝ φ x e * ∫ y, rieszKernel d s (x - y) * G y =
      (∫ x, fderiv ℝ φ x e * ∫ y, r3Kn d s r (x - y) * G y) +
        ∫ x, fderiv ℝ φ x e * ∫ y, r3Kf d s r (x - y) * G y := by
  have hKn_int : Integrable (r3Kn d s r) := r3Kn_integrable hd hs0 hsd hr
  have hKf1 : ContDiff ℝ 1 (r3Kf d s r) :=
    (r3Kf_contDiff (d := d) s hr).of_le (by exact_mod_cast r3_le_infty 1)
  have hKn_loc : LocallyIntegrable (r3Kn d s r) volume := hKn_int.locallyIntegrable
  have hKf_loc : LocallyIntegrable (r3Kf d s r) volume := hKf1.continuous.locallyIntegrable
  have hsplit : ∀ x : Euc d, ∫ y, rieszKernel d s (x - y) * G y =
      (∫ y, r3Kn d s r (x - y) * G y) + (∫ y, r3Kf d s r (x - y) * G y) + r3gp s r * ∫ y, G y := by
    intro x
    have hpt : ∀ y, rieszKernel d s (x - y) * G y =
        r3Kn d s r (x - y) * G y + r3Kf d s r (x - y) * G y + r3gp s r * G y := by
      intro y
      have h1 : rieszKernel d s (x - y) = r3Kn d s r (x - y) + r3Kf d s r (x - y) + r3gp s r := by
        linarith [r3_Kn_add_Kf s r (x - y)]
      rw [h1]; ring
    have i1 : Integrable (fun y => r3Kn d s r (x - y) * G y) := r3_conv_integrable hKn_loc hG hGc x
    have i2 : Integrable (fun y => r3Kf d s r (x - y) * G y) := r3_conv_integrable hKf_loc hG hGc x
    have i3 : Integrable (fun y => r3gp s r * G y) := (hG.integrable_of_hasCompactSupport hGc).const_mul _
    have i12 : Integrable (fun y => r3Kn d s r (x - y) * G y + r3Kf d s r (x - y) * G y) := i1.add i2
    simp_rw [hpt]
    rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul]
  have hcN : Continuous (fun x => ∫ y, r3Kn d s r (x - y) * G y) :=
    (r3_contDiff_conv hKn_loc (n := 0) (by exact contDiff_zero.mpr hG) hGc).continuous
  have hcF : Continuous (fun x => ∫ y, r3Kf d s r (x - y) * G y) :=
    (r3_contDiff_conv hKf_loc (n := 0) (by exact contDiff_zero.mpr hG) hGc).continuous
  have hdφ : Continuous (fun x => fderiv ℝ φ x e) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdφc : HasCompactSupport (fun x => fderiv ℝ φ x e) := hφc.fderiv_apply ℝ e
  have hI_N : Integrable (fun x => fderiv ℝ φ x e * ∫ y, r3Kn d s r (x - y) * G y) :=
    (hdφ.mul hcN).integrable_of_hasCompactSupport (hdφc.mul_right)
  have hI_F : Integrable (fun x => fderiv ℝ φ x e * ∫ y, r3Kf d s r (x - y) * G y) :=
    (hdφ.mul hcF).integrable_of_hasCompactSupport (hdφc.mul_right)
  have hI_NF : Integrable (fun x => fderiv ℝ φ x e * (∫ y, r3Kn d s r (x - y) * G y) +
      fderiv ℝ φ x e * (∫ y, r3Kf d s r (x - y) * G y)) :=
    (hI_N.add hI_F).congr (Eventually.of_forall fun x => by simp only [Pi.add_apply])
  have hint_c : Integrable (fun x => fderiv ℝ φ x e * (r3gp s r * ∫ y, G y)) :=
    (hdφ.mul continuous_const).integrable_of_hasCompactSupport (hdφc.mul_right)
  have hc : ∫ x, fderiv ℝ φ x e * (r3gp s r * ∫ y, G y) = 0 := by
    have hswap : (fun x => fderiv ℝ φ x e * (r3gp s r * ∫ y, G y)) =
        fun x => (r3gp s r * ∫ y, G y) * fderiv ℝ φ x e :=
      funext fun x => mul_comm _ _
    rw [hswap, integral_const_mul, sa12x2_mean_deriv_zero hφ hφc e, mul_zero]
  have hfun : ∫ x, fderiv ℝ φ x e * ∫ y, rieszKernel d s (x - y) * G y =
      ∫ x, ((fderiv ℝ φ x e * (∫ y, r3Kn d s r (x - y) * G y) +
        fderiv ℝ φ x e * (∫ y, r3Kf d s r (x - y) * G y)) +
        fderiv ℝ φ x e * (r3gp s r * ∫ y, G y)) :=
    integral_congr_ae (Eventually.of_forall fun x => by dsimp only; rw [hsplit x]; ring)
  rw [hfun, integral_add hI_NF hint_c, hc, add_zero]
  exact integral_add hI_N hI_F

/-- W3: weak top-piece bound for `∫ ∂_eφ (K ⋆ ∂_vΦ)`. -/
theorem sa12x2_weak_top {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hs2 : (d : ℝ) < s + 2) :
    ∃ C2 : ℝ, 0 ≤ C2 ∧ ∀ r : ℝ, 0 < r → ∀ (φ Φ : Euc d → ℝ) (e v : Euc d), ‖e‖ ≤ 1 → ‖v‖ ≤ 1 →
      ContDiff ℝ 1 φ → HasCompactSupport φ → ContDiff ℝ 1 Φ → HasCompactSupport Φ →
      |∫ x, fderiv ℝ φ x e * ∫ y, rieszKernel d s (x - y) * fderiv ℝ Φ y v| ≤
        (∫ h, |r3Kn d s r h|) * ((∫ x, (fderiv ℝ φ x e) ^ 2) + ∫ y, (fderiv ℝ Φ y v) ^ 2) / 2 +
          C2 * r ^ (-(s + 2 - d)) * ((∫ x, φ x ^ 2) + ∫ y, Φ y ^ 2) / 2 := by
  refine ⟨∫ k, ‖iteratedFDeriv ℝ 2 (r3F1 d s) k‖, integral_nonneg fun _ => norm_nonneg _, ?_⟩
  intro r hr φ Φ e v he hv hφ hφc hΦ hΦc
  have hKn_int : Integrable (r3Kn d s r) := r3Kn_integrable hd hs0 hsd hr
  have hKf2 : ContDiff ℝ 2 (r3Kf d s r) :=
    (r3Kf_contDiff (d := d) s hr).of_le (by exact_mod_cast r3_le_infty 2)
  have hKf1 : ContDiff ℝ 1 (r3Kf d s r) := hKf2.of_le (by exact_mod_cast le_refl _ |>.trans (by norm_num))
  have hG : Continuous (fun y => fderiv ℝ Φ y v) :=
    (hΦ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hGc : HasCompactSupport (fun y => fderiv ℝ Φ y v) := hΦc.fderiv_apply ℝ v
  rw [sa12x2_split_G hd hs0 hsd hr hG hGc hφ hφc e]
  -- squares
  have hdφ : Continuous (fun x => fderiv ℝ φ x e) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdφc : HasCompactSupport (fun x => fderiv ℝ φ x e) := hφc.fderiv_apply ℝ e
  have hdφ2 : Integrable (fun x => (fderiv ℝ φ x e) ^ 2) := by
    have hc2 : HasCompactSupport (fun x => (fderiv ℝ φ x e) ^ 2) :=
      hdφc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
    exact Continuous.integrable_of_hasCompactSupport (f := fun x => (fderiv ℝ φ x e) ^ 2)
      (hdφ.pow 2) hc2
  have hG2 : Integrable (fun y => (fderiv ℝ Φ y v) ^ 2) := by
    have hc2 : HasCompactSupport (fun y => (fderiv ℝ Φ y v) ^ 2) :=
      hGc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
    exact Continuous.integrable_of_hasCompactSupport (f := fun y => (fderiv ℝ Φ y v) ^ 2)
      (hG.pow 2) hc2
  have hφ2 : Integrable (fun x => φ x ^ 2) := by
    have hc2 : HasCompactSupport (fun x => φ x ^ 2) := hφc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
    exact Continuous.integrable_of_hasCompactSupport (f := fun x => φ x ^ 2)
      (hφ.continuous.pow 2) hc2
  have hΦ2 : Integrable (fun y => Φ y ^ 2) := by
    have hc2 : HasCompactSupport (fun y => Φ y ^ 2) := hΦc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
    exact Continuous.integrable_of_hasCompactSupport (f := fun y => Φ y ^ 2) (hΦ.continuous.pow 2) hc2
  -- near part
  have hN : |∫ x, fderiv ℝ φ x e * ∫ y, r3Kn d s r (x - y) * fderiv ℝ Φ y v| ≤
      (∫ h, |r3Kn d s r h|) * ((∫ x, (fderiv ℝ φ x e) ^ 2) + ∫ y, (fderiv ℝ Φ y v) ^ 2) / 2 :=
    r3_pair_le (K := r3Kn d s r) (A := fun x => fderiv ℝ φ x e) (B := fun y => fderiv ℝ Φ y v)
      (r3Kn_meas (d := d) s r) hdφ.measurable hG.measurable hKn_int hdφ2 hG2
  -- far part: y-IBP onto Kf, then x-IBP onto φ (W0), then the second derivative
  have hfarIBP : ∀ x : Euc d, ∫ y, r3Kf d s r (x - y) * fderiv ℝ Φ y v =
      ∫ y, fderiv ℝ (r3Kf d s r) (x - y) v * Φ y :=
    fun x => r3_ibp_conv hKf1 hΦ hΦc x v
  have hKd1 : ContDiff ℝ 1 (fun z => fderiv ℝ (r3Kf d s r) z v) :=
    (hKf2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hfar1 : ∫ x, fderiv ℝ φ x e * ∫ y, r3Kf d s r (x - y) * fderiv ℝ Φ y v =
      -∫ x, φ x * ∫ y, fderiv ℝ (fun z => fderiv ℝ (r3Kf d s r) z v) (x - y) e * Φ y := by
    have hw := sa12x2_ibp_kernel hKd1 hφ hφc hΦ.continuous hΦc e
    have hL : ∫ x, fderiv ℝ φ x e * ∫ y, r3Kf d s r (x - y) * fderiv ℝ Φ y v =
        ∫ x, fderiv ℝ φ x e * ∫ y, (fun z => fderiv ℝ (r3Kf d s r) z v) (x - y) * Φ y :=
      integral_congr_ae (Eventually.of_forall fun x => by dsimp only; rw [hfarIBP x])
    rw [hL]
    exact hw
  have hK2eq : ∀ h : Euc d, fderiv ℝ (fun z => fderiv ℝ (r3Kf d s r) z v) h e =
      iteratedFDeriv ℝ 2 (r3Kf d s r) h ![e, v] := fun h => r3_D_eq hKf2 e v h
  have hfar2 : ∫ x, fderiv ℝ φ x e * ∫ y, r3Kf d s r (x - y) * fderiv ℝ Φ y v =
      -∫ x, φ x * ∫ y, iteratedFDeriv ℝ 2 (r3Kf d s r) (x - y) ![e, v] * Φ y := by
    rw [hfar1]
    simp only [hK2eq]
  have hK2c : Continuous (fun h => iteratedFDeriv ℝ 2 (r3Kf d s r) h ![e, v]) :=
    (continuous_eval_const (![e, v] : Fin 2 → Euc d)).comp
      (hKf2.continuous_iteratedFDeriv (m := 2) (by norm_num))
  have hK2int : Integrable (fun h => iteratedFDeriv ℝ 2 (r3Kf d s r) h ![e, v]) :=
    Integrable.mono' (r3Kf_D2_l1 hd hs0 hs2 hr).1 hK2c.aestronglyMeasurable
      (Eventually.of_forall fun h => r3_D_bound e v h he hv)
  have hfar3 : |∫ x, φ x * ∫ y, iteratedFDeriv ℝ 2 (r3Kf d s r) (x - y) ![e, v] * Φ y| ≤
      (∫ h, |iteratedFDeriv ℝ 2 (r3Kf d s r) h ![e, v]|) * ((∫ x, φ x ^ 2) + ∫ y, Φ y ^ 2) / 2 :=
    r3_pair_le (K := fun h => iteratedFDeriv ℝ 2 (r3Kf d s r) h ![e, v]) (A := φ) (B := Φ)
      hK2c.measurable hφ.continuous.measurable hΦ.continuous.measurable hK2int hφ2 hΦ2
  have hK2abs : ∫ h, |iteratedFDeriv ℝ 2 (r3Kf d s r) h ![e, v]| ≤
      (∫ k, ‖iteratedFDeriv ℝ 2 (r3F1 d s) k‖) * r ^ (-(s + 2 - d)) := by
    have hexp : (d : ℝ) - s - 2 = -(s + 2 - d) := by ring
    rw [← hexp]
    refine le_trans ?_ (r3Kf_D2_l1 hd hs0 hs2 hr).2.le
    exact integral_mono (hK2int.abs) (r3Kf_D2_l1 hd hs0 hs2 hr).1 fun h => r3_D_bound e v h he hv
  have hS0 : 0 ≤ (∫ x, φ x ^ 2) + ∫ y, Φ y ^ 2 :=
    add_nonneg (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
  have hfar : |∫ x, fderiv ℝ φ x e * ∫ y, r3Kf d s r (x - y) * fderiv ℝ Φ y v| ≤
      (∫ k, ‖iteratedFDeriv ℝ 2 (r3F1 d s) k‖) * r ^ (-(s + 2 - d)) *
        ((∫ x, φ x ^ 2) + ∫ y, Φ y ^ 2) / 2 := by
    rw [hfar2, abs_neg]
    calc |∫ x, φ x * ∫ y, iteratedFDeriv ℝ 2 (r3Kf d s r) (x - y) ![e, v] * Φ y|
        ≤ (∫ h, |iteratedFDeriv ℝ 2 (r3Kf d s r) h ![e, v]|) * ((∫ x, φ x ^ 2) + ∫ y, Φ y ^ 2) / 2 := hfar3
      _ ≤ (∫ k, ‖iteratedFDeriv ℝ 2 (r3F1 d s) k‖) * r ^ (-(s + 2 - d)) *
            ((∫ x, φ x ^ 2) + ∫ y, Φ y ^ 2) / 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hK2abs hS0) two_pos.le
  refine (abs_add_le _ _).trans ?_
  linarith [hN, hfar]

end HRS.MH.AdjointRd.Phase2SA12
