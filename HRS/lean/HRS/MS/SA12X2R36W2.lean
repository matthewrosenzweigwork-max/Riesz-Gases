import HRS.MS.SA12X2R36W0
import HRS.MS.SA12X2R32B

/-!
# S.A.12 R36 (SA12X2), part W2: weak near/far bound for `∫ ∂_eφ (K ⋆ G)`, `G` continuous

Split `K = Kn + Kf + c` (`r3Kn`, `r3Kf`, `r3gp`) at scale `r`. The constant term vanishes (`∫∂_eφ = 0`).
Near part: Schur (`r3_pair_le`) with `‖Kn‖₁ = Cn r^(d-s)`, derivative kept on `φ`.
Far part: integration by parts onto `φ` (`sa12x2_ibp_kernel`), then Schur with `∂_eKf` cut to `B̄(0,2R)`, whose
L¹ norm is `≤ C r^(-(s+2-d))` (`sa12x2_kf_L1`).
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12

open HRS HRS.Whole HRS.MH.AdjointRdP

variable {d : ℕ}

/-- A `C^1_c` function has zero mean derivative. -/
theorem sa12x2_mean_deriv_zero {φ : Euc d → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (e : Euc d) : ∫ x, fderiv ℝ φ x e = 0 := by
  have h := r3_ibp_cs (f := φ) (g := fun _ => (1 : ℝ)) e hφ contDiff_const hφc
  simp only [fderiv_const_apply, ContinuousLinearMap.zero_apply, mul_zero, integral_zero, mul_one] at h
  linarith

theorem sa12x2_weak_low {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hs2 : (d : ℝ) < s + 2)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ (c : Euc d) (φ G : Euc d → ℝ) (e : Euc d), ‖e‖ ≤ 1 →
      ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ closedBall c R →
      Continuous G → HasCompactSupport G → tsupport G ⊆ closedBall c R →
      |∫ x, fderiv ℝ φ x e * ∫ y, rieszKernel d s (x - y) * G y| ≤
        (∫ h, |r3Kn d s r h|) * ((∫ x, (fderiv ℝ φ x e) ^ 2) + ∫ y, G y ^ 2) / 2 +
          C0 * r ^ (-(s + 2 - d)) * ((∫ x, φ x ^ 2) + ∫ y, G y ^ 2) / 2 := by
  obtain ⟨CD, hCD0, hCD⟩ := sa12x2_kf_L1 (d := d) hs0 hs2 (2 * R) (by linarith)
  refine ⟨CD, hCD0, ?_⟩
  intro r hr hr1 c φ G e he hφ hφc hφs hG hGc hGs
  have hKn_int : Integrable (r3Kn d s r) := r3Kn_integrable hd hs0 hsd hr
  have hKf1 : ContDiff ℝ 1 (r3Kf d s r) :=
    (r3Kf_contDiff (d := d) s hr).of_le (by exact_mod_cast r3_le_infty 1)
  have hKn_loc : LocallyIntegrable (r3Kn d s r) volume := hKn_int.locallyIntegrable
  have hKf_loc : LocallyIntegrable (r3Kf d s r) volume := hKf1.continuous.locallyIntegrable
  -- the three-term splitting of the inner integral
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
  -- continuity of the convolutions (for splitting the outer integral)
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
  -- the outer integral splits; the constant term vanishes
  have hint_c : Integrable (fun x => fderiv ℝ φ x e * (r3gp s r * ∫ y, G y)) :=
    (hdφ.mul continuous_const).integrable_of_hasCompactSupport (hdφc.mul_right)
  have hc : ∫ x, fderiv ℝ φ x e * (r3gp s r * ∫ y, G y) = 0 := by
    have hswap : (fun x => fderiv ℝ φ x e * (r3gp s r * ∫ y, G y)) =
        fun x => (r3gp s r * ∫ y, G y) * fderiv ℝ φ x e :=
      funext fun x => mul_comm _ _
    rw [hswap, integral_const_mul, sa12x2_mean_deriv_zero hφ hφc e, mul_zero]
  have hL : ∫ x, fderiv ℝ φ x e * ∫ y, rieszKernel d s (x - y) * G y =
      (∫ x, fderiv ℝ φ x e * ∫ y, r3Kn d s r (x - y) * G y) +
        ∫ x, fderiv ℝ φ x e * ∫ y, r3Kf d s r (x - y) * G y := by
    have hfun : ∫ x, fderiv ℝ φ x e * ∫ y, rieszKernel d s (x - y) * G y =
        ∫ x, ((fderiv ℝ φ x e * (∫ y, r3Kn d s r (x - y) * G y) +
          fderiv ℝ φ x e * (∫ y, r3Kf d s r (x - y) * G y)) +
          fderiv ℝ φ x e * (r3gp s r * ∫ y, G y)) :=
      integral_congr_ae (Eventually.of_forall fun x => by dsimp only; rw [hsplit x]; ring)
    rw [hfun, integral_add hI_NF hint_c, hc, add_zero]
    exact integral_add hI_N hI_F
  -- integrability of the squares
  have hdφ2 : Integrable (fun x => (fderiv ℝ φ x e) ^ 2) := by
    have hc2 : HasCompactSupport (fun x => (fderiv ℝ φ x e) ^ 2) :=
      hdφc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
    exact Continuous.integrable_of_hasCompactSupport (f := fun x => (fderiv ℝ φ x e) ^ 2)
      (hdφ.pow 2) hc2
  have hφ2 : Integrable (fun x => φ x ^ 2) := by
    have hc2 : HasCompactSupport (fun x => φ x ^ 2) := hφc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
    exact Continuous.integrable_of_hasCompactSupport (f := fun x => φ x ^ 2)
      (hφ.continuous.pow 2) hc2
  have hG2 : Integrable (fun y => G y ^ 2) := by
    have hc2 : HasCompactSupport (fun y => G y ^ 2) := hGc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
    exact Continuous.integrable_of_hasCompactSupport (f := fun y => G y ^ 2) (hG.pow 2) hc2
  -- near part: Schur with the derivative on φ
  have hN := r3_pair_le (K := r3Kn d s r) (A := fun x => fderiv ℝ φ x e) (B := G)
    (r3Kn_meas (d := d) s r) hdφ.measurable hG.measurable hKn_int hdφ2 hG2
  -- far part: integrate by parts onto φ, then Schur with the cut kernel
  obtain ⟨K', hK'⟩ : ∃ K' : Euc d → ℝ,
      K' = (closedBall (0 : Euc d) (2 * R)).indicator (fun h => fderiv ℝ (r3Kf d s r) h e) := ⟨_, rfl⟩
  have hcont : Continuous (fun h => fderiv ℝ (r3Kf d s r) h e) :=
    ((r3Kf_contDiff (d := d) s hr).continuous_fderiv (by simp)).clm_apply continuous_const
  have hK'meas : Measurable K' := by
    rw [hK']; exact hcont.measurable.indicator measurableSet_closedBall
  have hK'int : Integrable K' := by
    rw [hK']
    exact (hcont.continuousOn.integrableOn_compact (isCompact_closedBall (0 : Euc d) (2 * R))).integrable_indicator
      measurableSet_closedBall
  have hK'eq : ∀ x, φ x * ∫ y, fderiv ℝ (r3Kf d s r) (x - y) e * G y = φ x * ∫ y, K' (x - y) * G y := by
    intro x
    by_cases hx : φ x = 0
    · simp [hx]
    · congr 1
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      by_cases hy : G y = 0
      · simp [hy]
      · have hxs : x ∈ closedBall c R := hφs (subset_tsupport φ (Function.mem_support.2 hx))
        have hys : y ∈ closedBall c R := hGs (subset_tsupport G (Function.mem_support.2 hy))
        rw [mem_closedBall, dist_eq_norm] at hxs hys
        have hxy : x - y ∈ closedBall (0 : Euc d) (2 * R) := by
          rw [mem_closedBall_zero_iff]
          have h3 := norm_sub_le (x - c) (y - c)
          rw [sub_sub_sub_cancel_right] at h3
          linarith
        dsimp only
        rw [hK', indicator_of_mem hxy]
  have hFar : ∫ x, φ x * ∫ y, fderiv ℝ (r3Kf d s r) (x - y) e * G y =
      ∫ x, φ x * ∫ y, K' (x - y) * G y := integral_congr_ae (Eventually.of_forall hK'eq)
  have hKabs : ∫ h, |K' h| ≤ CD * r ^ (-(s + 2 - d)) := by
    have e1 : (fun h => |K' h|) = (closedBall (0 : Euc d) (2 * R)).indicator
        (fun h => |fderiv ℝ (r3Kf d s r) h e|) := by
      funext h
      by_cases hh : h ∈ closedBall (0 : Euc d) (2 * R)
      · rw [hK', indicator_of_mem hh, indicator_of_mem hh]
      · rw [hK', indicator_of_notMem hh, indicator_of_notMem hh, abs_zero]
    rw [e1]
    exact hCD r hr hr1 e he
  have hfar := r3_pair_le (K := K') (A := φ) (B := G) hK'meas hφ.continuous.measurable
    hG.measurable hK'int hφ2 hG2
  have hS0 : 0 ≤ (∫ x, φ x ^ 2) + ∫ y, G y ^ 2 :=
    add_nonneg (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
  have hfar' : |∫ x, φ x * ∫ y, K' (x - y) * G y| ≤
      CD * r ^ (-(s + 2 - d)) * ((∫ x, φ x ^ 2) + ∫ y, G y ^ 2) / 2 := by
    calc |∫ x, φ x * ∫ y, K' (x - y) * G y|
        ≤ (∫ h, |K' h|) * ((∫ x, φ x ^ 2) + ∫ y, G y ^ 2) / 2 := hfar
      _ ≤ CD * r ^ (-(s + 2 - d)) * ((∫ x, φ x ^ 2) + ∫ y, G y ^ 2) / 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hKabs hS0) two_pos.le
  rw [hL]
  refine (abs_add_le _ _).trans ?_
  rw [sa12x2_ibp_kernel hKf1 hφ hφc hG hGc e, abs_neg, hFar]
  linarith [hN, hfar']

end HRS.MH.AdjointRd.Phase2SA12
