import HRS.MS.SA16Y3Sk1
import HRS.MS.SA16ZR3

/-!
# S.A.16 (SA16Y3) Sk2: `L^p` bound of `Q^i(c χ) = ∂_i(g ⋆ (c χ))` (packet P7, Hilbert corner)

`sa16y3_Q_Lp`: `‖Q^i(cχ)‖_p ≤ C (B_c + L_c) (‖χ‖_p + ‖∇χ‖_p)`, `1 < θ = s+2-d < 2`.
`sa16y3_Q_jet`: for `χ = ∂^κ φ`: `‖Q^i(c ∂^κφ)‖_p ≤ C' (B_c + L_c) S_{r+1}(φ)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.MH.AdjointRd

section Sk2
variable {d : ℕ} {s : ℝ}

theorem sa16y3_Q_Lp (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) {p : ℝ} (hp : 1 < p) (i : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c χ : Euc d → ℝ}, ContDiff ℝ ∞ c → IsCcInfty χ → ∀ {Bc Lc : ℝ}, 0 ≤ Bc → 0 ≤ Lc →
      (∀ y, |c y| ≤ Bc) → (∀ y, ‖fderiv ℝ c y‖ ≤ Lc) →
      eLpNorm (sa16y3_Q s i (fun y => c y * χ y)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * (Bc + Lc)) * (eLpNorm χ (ENNReal.ofReal p) volume +
          eLpNorm (fun y => ‖fderiv ℝ χ y‖) (ENNReal.ofReal p) volume) := by
  have hθ2 : s + 2 - (d : ℝ) < 2 := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    have : (1 : ℝ) ≤ p := hp.le
    simpa using ENNReal.ofReal_le_ofReal this
  obtain ⟨Ci, hCi0, hCi⟩ := sa16z_pv_W1p hd hθ1 hθ2 hp i
  have hc0 := HRS.CZ.Hls.hlsg_c_nonneg hs0
  refine ⟨HRS.CZ.Hls.hlsg_c s * Ci, mul_nonneg hc0 hCi0, fun {c χ} hc hχ {Bc Lc} hBc hLc hab hLa => ?_⟩
  have hf : IsCcInfty (fun y => c y * χ y) := ⟨hc.mul hχ.1, hχ.2.mul_left⟩
  have hQ : sa16y3_Q s i (fun y => c y * χ y) = (-(HRS.CZ.Hls.hlsg_c s)) •
      pvOdd d (s + 2 - d) (fun u : Euc d => u i) (fun y => c y * χ y) := by
    funext x
    exact sa16z_conv_fderiv_pvOdd hd hs0 hsd hf i x
  set G := eLpNorm χ (ENNReal.ofReal p) volume with hG
  set H := eLpNorm (fun y => ‖fderiv ℝ χ y‖) (ENNReal.ofReal p) volume with hH
  have hg1 : Continuous χ := hχ.1.continuous
  have hg2 : Continuous (fun y => ‖fderiv ℝ χ y‖) := (hχ.1.continuous_fderiv (by simp)).norm
  have e1 : eLpNorm (fun y => c y * χ y) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal Bc * G := by
    refine sa16z_eLpNorm_le_mul hf.1.continuous.aestronglyMeasurable hBc (fun y => ?_) _
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hab y) (norm_nonneg _)
  have e2 : eLpNorm (fun y => ‖fderiv ℝ (fun y => c y * χ y) y‖) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal Lc * G + ENNReal.ofReal Bc * H := by
    have hm : AEStronglyMeasurable (fun y => ‖fderiv ℝ (fun y => c y * χ y) y‖) volume :=
      (hf.1.continuous_fderiv (by simp)).norm.aestronglyMeasurable
    have hle : eLpNorm (fun y => ‖fderiv ℝ (fun y => c y * χ y) y‖) (ENNReal.ofReal p) volume ≤
        eLpNorm ((fun y => Lc * ‖χ y‖) + fun y => Bc * ‖fderiv ℝ χ y‖) (ENNReal.ofReal p) volume := by
      refine eLpNorm_mono hm fun y => ?_
      have hd1 : DifferentiableAt ℝ c y := (hc.differentiable (by simp)) y
      have hd2 : DifferentiableAt ℝ χ y := (hχ.1.differentiable (by simp)) y
      rw [fderiv_fun_mul hd1 hd2, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), Pi.add_apply, Real.norm_eq_abs,
        abs_of_nonneg (add_nonneg (mul_nonneg hLc (norm_nonneg _)) (mul_nonneg hBc (norm_nonneg _)))]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm (|χ y|)]
      have h1 := hab y
      have h2 := hLa y
      have hn3 := abs_nonneg (χ y)
      have hn2 : 0 ≤ ‖fderiv ℝ χ y‖ := norm_nonneg _
      nlinarith [mul_le_mul_of_nonneg_right h2 hn3, mul_le_mul_of_nonneg_right h1 hn2]
    refine hle.trans ((eLpNorm_add_le hp1).trans (add_le_add ?_ ?_))
    · refine sa16z_eLpNorm_le_mul (continuous_const.mul hg1.norm).aestronglyMeasurable hLc (fun y => ?_) _
      simp [abs_of_nonneg hLc]
    · refine sa16z_eLpNorm_le_mul (continuous_const.mul hg2).aestronglyMeasurable hBc (fun y => ?_) _
      simp [abs_of_nonneg hBc]
  rw [hQ]
  refine (eLpNorm_const_smul_le).trans ?_
  rw [Real.enorm_eq_ofReal_abs, abs_neg, abs_of_nonneg hc0]
  have h1 := hCi _ hf
  have hBL : ENNReal.ofReal Bc ≤ ENNReal.ofReal (Bc + Lc) := ENNReal.ofReal_le_ofReal (by linarith)
  have hLB : ENNReal.ofReal Lc ≤ ENNReal.ofReal (Bc + Lc) := ENNReal.ofReal_le_ofReal (by linarith)
  calc ENNReal.ofReal (HRS.CZ.Hls.hlsg_c s) * eLpNorm (pvOdd d (s + 2 - d) (fun u : Euc d => u i)
        (fun y => c y * χ y)) (ENNReal.ofReal p) volume
      ≤ ENNReal.ofReal (HRS.CZ.Hls.hlsg_c s) * (ENNReal.ofReal Ci *
          (eLpNorm (fun y => c y * χ y) (ENNReal.ofReal p) volume +
            eLpNorm (fun y => ‖fderiv ℝ (fun y => c y * χ y) y‖) (ENNReal.ofReal p) volume)) := by gcongr
    _ ≤ ENNReal.ofReal (HRS.CZ.Hls.hlsg_c s) * (ENNReal.ofReal Ci *
          ((ENNReal.ofReal Bc * G) + (ENNReal.ofReal Lc * G + ENNReal.ofReal Bc * H))) := by gcongr
    _ ≤ ENNReal.ofReal (HRS.CZ.Hls.hlsg_c s) * (ENNReal.ofReal Ci * (ENNReal.ofReal (Bc + Lc) * (G + H))) := by
        gcongr
        have e : ENNReal.ofReal Bc * G + (ENNReal.ofReal Lc * G + ENNReal.ofReal Bc * H) =
            (ENNReal.ofReal Bc + ENNReal.ofReal Lc) * G + ENNReal.ofReal Bc * H := by ring
        rw [e, ← ENNReal.ofReal_add hBc hLc, mul_add]
        gcongr
    _ = ENNReal.ofReal (HRS.CZ.Hls.hlsg_c s * Ci * (Bc + Lc)) * (G + H) := by
        rw [← mul_assoc, ← mul_assoc, ENNReal.ofReal_mul (mul_nonneg hc0 hCi0), ENNReal.ofReal_mul hc0]

lemma sa16y3_fderiv_pd_le {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) {r : ℕ} (κ : Fin r → Fin d) (y : Euc d) :
    ‖fderiv ℝ (partialDeriv κ φ) y‖ ≤ (d : ℝ) * sa16sz_vn φ (r + 1) y := by
  refine (sa16z_opNorm_le_sum _).trans ?_
  have h1 : ∀ l : Fin d, |fderiv ℝ (partialDeriv κ φ) y (sa16z_e l)| ≤ sa16sz_vn φ (r + 1) y := fun l =>
    sa16z_pd_dm_abs hφ κ l y
  calc ∑ l : Fin d, |fderiv ℝ (partialDeriv κ φ) y (sa16z_e l)| ≤ ∑ l : Fin d, sa16sz_vn φ (r + 1) y :=
        Finset.sum_le_sum fun l _ => h1 l
    _ = _ := by simp

lemma sa16y3_chi_bound {p : ℝ} {φ : Euc d → ℝ} (hφ : IsCcInfty φ) {r : ℕ} (κ : Fin r → Fin d) :
    eLpNorm (partialDeriv κ φ) (ENNReal.ofReal p) volume +
      eLpNorm (fun y => ‖fderiv ℝ (partialDeriv κ φ) y‖) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (1 + d) * sa16z_S p φ (r + 1) := by
  have hψ : IsCcInfty (partialDeriv κ φ) := sa16s_cc_partialDeriv hφ κ
  have e1 : eLpNorm (partialDeriv κ φ) (ENNReal.ofReal p) volume ≤ sa16z_S p φ (r + 1) := by
    refine le_trans ?_ (sa16z_JJ_le_S φ (k := r) (N := r + 1) (by omega))
    unfold sa16z_JJ
    refine eLpNorm_mono hψ.1.continuous.aestronglyMeasurable fun y => ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sa16sz_vn_nonneg _ _ _)]
    exact sa16sz_abs_le_vn φ r κ y
  have e2 : eLpNorm (fun y => ‖fderiv ℝ (partialDeriv κ φ) y‖) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal d * sa16z_S p φ (r + 1) := by
    refine le_trans ?_ (by gcongr; exact sa16z_JJ_le_S φ (k := r + 1) (N := r + 1) le_rfl :
      ENNReal.ofReal d * sa16z_JJ p φ (r + 1) ≤ ENNReal.ofReal d * sa16z_S p φ (r + 1))
    unfold sa16z_JJ
    refine sa16z_eLpNorm_le_mul (hψ.1.continuous_fderiv (by simp)).norm.aestronglyMeasurable
      (Nat.cast_nonneg d) (fun y => ?_) _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), abs_of_nonneg (sa16sz_vn_nonneg _ _ _)]
    exact sa16y3_fderiv_pd_le hφ.1 κ y
  calc _ ≤ sa16z_S p φ (r + 1) + ENNReal.ofReal d * sa16z_S p φ (r + 1) := add_le_add e1 e2
    _ = ENNReal.ofReal (1 + d) * sa16z_S p φ (r + 1) := by
        rw [ENNReal.ofReal_add zero_le_one (Nat.cast_nonneg d)]
        simp [add_mul]

theorem sa16y3_Q_jet (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) {p : ℝ} (hp : 1 < p) (i : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c φ : Euc d → ℝ}, ContDiff ℝ ∞ c → IsCcInfty φ → ∀ {Bc Lc : ℝ}, 0 ≤ Bc → 0 ≤ Lc →
      (∀ y, |c y| ≤ Bc) → (∀ y, ‖fderiv ℝ c y‖ ≤ Lc) → ∀ {r : ℕ} (κ : Fin r → Fin d),
      eLpNorm (sa16y3_Q s i (fun y => c y * partialDeriv κ φ y)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * (Bc + Lc)) * sa16z_S p φ (r + 1) := by
  obtain ⟨C, hC, hQ⟩ := sa16y3_Q_Lp (s := s) hd hs0 hsd hθ1 hp i
  refine ⟨C * (1 + d), by positivity, fun {c φ} hc hφ {Bc Lc} hBc hLc hab hLa {r} κ => ?_⟩
  refine (hQ hc (sa16s_cc_partialDeriv hφ κ) hBc hLc hab hLa).trans ?_
  calc ENNReal.ofReal (C * (Bc + Lc)) * (eLpNorm (partialDeriv κ φ) (ENNReal.ofReal p) volume +
        eLpNorm (fun y => ‖fderiv ℝ (partialDeriv κ φ) y‖) (ENNReal.ofReal p) volume)
      ≤ ENNReal.ofReal (C * (Bc + Lc)) * (ENNReal.ofReal (1 + d) * sa16z_S p φ (r + 1)) := by
        gcongr; exact sa16y3_chi_bound hφ κ
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2; ring

end Sk2

end HRS.Whole.AppendixA.Phase2SA16R
