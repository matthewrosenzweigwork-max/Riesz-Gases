import HRS.MC.D3EGAux3

/-!
# Packet D3EG: Lemma D.3 on `ℝ^d`, item (ii) for the truncated kernel `g_λ = fdlTruncE`.

Spec: `HRS/Appendix/FDL.lean`, `HRS.fdl_kernel_euclid` (the `fdlTruncE` conjuncts of (ii)).
Key idea: `g_λ = c₀ + G_λ` with `G_λ(z) = ∫_λ^∞ b t^{-s-1}(φ(z/t) - ι) dt` manifestly smooth on all of `ℝ^d`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

namespace HRS.MC.D3EG

open HRS HRS.MC.FDLE HRS.MC.D3EW

variable {d : ℕ}

lemma d3eg_trunc_eq (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ)
    {b : ℝ} (hb : IsFDLConst ψ s b) :
    ∃ C : ℝ, ∀ lam : ℝ, 0 < lam →
      fdlTruncE ψ s b lam = fun z => d3eg_c0 s lam C + d3eg_G ψ s b lam z := by
  have hb0 := hb.1
  have hC : ∃ C : ℝ, ∀ lam : ℝ, 0 < lam → ∀ z : Euc d, z ≠ 0 →
      Whole.rieszKernel d s z - fdlWE ψ s b lam z = d3eg_c0 s lam C + d3eg_G ψ s b lam z := by
    rcases hs0.lt_or_eq with hs | hs
    · refine ⟨0, fun lam hl z hz => ?_⟩
      simp only [d3eg_c0, if_neg hs.ne', zero_add]
      exact d3eg_repr_pos hs hb hl hz
    · subst hs
      obtain ⟨C, hC⟩ := d3eg_repr_zero hd hψ hb
      exact ⟨C, fun lam hl z hz => by simpa [d3eg_c0] using hC lam hl z hz⟩
  obtain ⟨C, hC⟩ := hC
  refine ⟨C, fun lam hl => funext fun z => ?_⟩
  by_cases hz : z = 0
  · subst hz
    have : NeZero d := ⟨by omega⟩
    have hcont : Continuous (fun z => d3eg_c0 s lam C + d3eg_G ψ s b lam z) :=
      continuous_const.add (d3eg_G_contDiff hψ hs0 hb0 hl).continuous
    have htend : Tendsto (fun z' : Euc d => Whole.rieszKernel d s z' - fdlWE ψ s b lam z')
        (𝓝[≠] (0 : Euc d)) (𝓝 (d3eg_c0 s lam C + d3eg_G ψ s b lam 0)) := by
      refine (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z' hz'
      exact (hC lam hl z' hz').symm
    simp only [fdlTruncE, if_pos rfl]
    exact htend.limUnder_eq
  · simp only [fdlTruncE, if_neg hz]
    exact hC lam hl z hz

lemma d3eg_iter_trunc {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {s : ℝ} (hs0 : 0 ≤ s) {b : ℝ}
    (hb0 : 0 < b) {lam : ℝ} (hl : 0 < lam) (C : ℝ) (m : ℕ) (hm : 0 < (m : ℝ) + s) (z : Euc d) :
    iteratedFDeriv ℝ m (fun z => d3eg_c0 s lam C + d3eg_G ψ s b lam z) z
      = iteratedFDeriv ℝ m (d3eg_G ψ s b lam) z := by
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0
    have hs : s ≠ 0 := by
      intro h; subst h; simp at hm
    simp [d3eg_c0, hs]
  · have hG := d3eg_G_contDiff hψ hs0 hb0 hl
    have : (fun z => d3eg_c0 s lam C + d3eg_G ψ s b lam z)
        = (fun _ => d3eg_c0 s lam C) + d3eg_G ψ s b lam := rfl
    rw [this, iteratedFDeriv_add_apply contDiffAt_const (hG.contDiffAt.of_le (by exact_mod_cast le_top)),
      iteratedFDeriv_const_of_ne h0.ne']
    simp

theorem d3eg_deriv (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    ∀ j : ℕ, 0 < (j : ℝ) + s → ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ z : Euc d, z ≠ 0 →
      ‖iteratedFDeriv ℝ j (fdlTruncE ψ s b lam) z‖ ≤ C * (max lam ‖z‖) ^ (-s - (j : ℝ)) := by
  intro j hj
  obtain ⟨C0, hC0, hG⟩ := d3eg_G_deriv hψ hs0 hb.1 j hj
  obtain ⟨Cc, hCc⟩ := d3eg_trunc_eq hd hs0 hψ hb
  refine ⟨C0, hC0, fun lam hl _ z _ => ?_⟩
  rw [hCc lam hl, d3eg_iter_trunc hψ hs0 hb.1 hl Cc j hj z]
  exact hG lam hl z

theorem d3eg_smooth (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    ∀ lam : ℝ, 0 < lam → lam < 1 →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fdlTruncE ψ s b lam) := by
  intro lam hl _
  obtain ⟨Cc, hCc⟩ := d3eg_trunc_eq hd hs0 hψ hb
  rw [hCc lam hl]
  exact contDiff_const.add (d3eg_G_contDiff hψ hs0 hb.1 hl)

theorem d3eg_sup (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    ∀ j : ℕ, 0 < (j : ℝ) + s → ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ z : Euc d,
      ‖iteratedFDeriv ℝ j (fdlTruncE ψ s b lam) z‖ ≤ C * lam ^ (-s - (j : ℝ)) := by
  intro j hj
  obtain ⟨C0, hC0, hG⟩ := d3eg_G_deriv hψ hs0 hb.1 j hj
  obtain ⟨Cc, hCc⟩ := d3eg_trunc_eq hd hs0 hψ hb
  refine ⟨C0, hC0, fun lam hl _ z => ?_⟩
  rw [hCc lam hl, d3eg_iter_trunc hψ hs0 hb.1 hl Cc j hj z]
  refine (hG lam hl z).trans ?_
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hl (le_max_left lam ‖z‖) (show -s - (j : ℝ) ≤ 0 by linarith)) hC0

theorem d3eg_zero (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 →
      |fdlTruncE ψ s b lam 0| ≤ C * (lam ^ (-s) + (if s = 0 then |Real.log lam| else 0)) := by
  obtain ⟨Cc, hCc⟩ := d3eg_trunc_eq hd hs0 hψ hb
  rcases hs0.lt_or_eq with hs | hs
  · obtain ⟨C0, hC0, hG⟩ := d3eg_G_deriv hψ hs0 hb.1 0 (by simpa using hs)
    refine ⟨C0, hC0, fun lam hl _ => ?_⟩
    have h := hG lam hl 0
    rw [norm_iteratedFDeriv_zero, norm_zero, max_eq_left hl.le] at h
    rw [hCc lam hl]
    simp only [d3eg_c0, if_neg hs.ne', zero_add, if_neg hs.ne', add_zero]
    simpa [Real.norm_eq_abs] using h
  · subst hs
    refine ⟨|Cc| + 1, by positivity, fun lam hl _ => ?_⟩
    rw [hCc lam hl]
    have hG0 : d3eg_G ψ 0 b lam 0 = 0 := by
      unfold d3eg_G
      simp [d3eg_K, d3eg_iota]
    simp only [d3eg_c0, if_pos rfl, hG0, add_zero, neg_zero, Real.rpow_zero, if_true]
    calc |Cc - Real.log lam| ≤ |Cc| + |Real.log lam| := abs_sub _ _
      _ ≤ (|Cc| + 1) * (1 + |Real.log lam|) := by
          nlinarith [abs_nonneg Cc, abs_nonneg (Real.log lam)]

theorem d3eg_log (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    s = 0 → ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ z : Euc d, z ≠ 0 →
      |fdlTruncE ψ s b lam z| ≤ C * (1 + |Real.log (max lam ‖z‖)|) := by
  intro hs
  obtain ⟨C1, hC1, hsup⟩ := d3eg_sup hd hs0 hsd hψ hb 1 (by rw [hs]; norm_num)
  refine ⟨C1 + 1, by positivity, fun lam hl hl1 z hz => ?_⟩
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  -- value outside the ball
  have hout : ∀ w : Euc d, lam ≤ ‖w‖ → fdlTruncE ψ s b lam w = -Real.log ‖w‖ := by
    intro w hw
    have hw0 : w ≠ 0 := by
      intro h; rw [h, norm_zero] at hw; linarith
    simp only [fdlTruncE, if_neg hw0, fdle_W_vanish hψ hw hl, sub_zero]
    rw [hs, fdle_rk0]
  by_cases hzl : lam ≤ ‖z‖
  · rw [hout z hzl, max_eq_right hzl, abs_neg]
    nlinarith [abs_nonneg (Real.log ‖z‖), hC1]
  · push Not at hzl
    rw [max_eq_left hzl.le]
    set z' : Euc d := (lam / ‖z‖) • z with hz'
    have hz'n : ‖z'‖ = lam := by
      rw [hz', norm_smul, Real.norm_of_nonneg (div_nonneg hl.le hzpos.le)]
      field_simp
    have hz'v : fdlTruncE ψ s b lam z' = -Real.log lam := by
      rw [hout z' hz'n.ge, hz'n]
    have hsm := d3eg_smooth hd hs0 hsd hψ hb lam hl hl1
    have hdiff : ∀ x : Euc d, DifferentiableAt ℝ (fdlTruncE ψ s b lam) x := fun x =>
      hsm.differentiable (by simp) x
    have hmvt := (convex_univ (𝕜 := ℝ) (E := Euc d)).norm_image_sub_le_of_norm_fderiv_le
      (f := fdlTruncE ψ s b lam) (C := C1 * lam ^ (-s - ((1 : ℕ) : ℝ))) (fun x _ => hdiff x)
      (fun x _ => by
        have := hsup lam hl hl1 x
        rwa [norm_iteratedFDeriv_one] at this) (mem_univ z') (mem_univ z)
    have hdist : ‖z - z'‖ ≤ lam := by
      have : z - z' = (1 - lam / ‖z‖) • z := by rw [hz', sub_smul, one_smul]
      rw [this, norm_smul, Real.norm_eq_abs]
      have hr : 1 ≤ lam / ‖z‖ := by rw [le_div_iff₀ hzpos]; linarith
      rw [abs_of_nonpos (by linarith)]
      have : (lam / ‖z‖ - 1) * ‖z‖ = lam - ‖z‖ := by field_simp
      nlinarith
    have hpow : lam ^ (-s - ((1 : ℕ) : ℝ)) = lam⁻¹ := by
      rw [hs]; simp [Real.rpow_neg_one]
    rw [hpow] at hmvt
    have hb1 : C1 * lam⁻¹ * ‖z - z'‖ ≤ C1 := by
      calc C1 * lam⁻¹ * ‖z - z'‖ ≤ C1 * lam⁻¹ * lam := by gcongr
        _ = C1 := by field_simp
    have h2 : |fdlTruncE ψ s b lam z| ≤ |Real.log lam| + C1 := by
      have h3 : |fdlTruncE ψ s b lam z - fdlTruncE ψ s b lam z'| ≤ C1 := by
        rw [← Real.norm_eq_abs]; exact hmvt.trans hb1
      calc |fdlTruncE ψ s b lam z| = |(fdlTruncE ψ s b lam z - fdlTruncE ψ s b lam z') + fdlTruncE ψ s b lam z'| := by ring_nf
        _ ≤ |fdlTruncE ψ s b lam z - fdlTruncE ψ s b lam z'| + |fdlTruncE ψ s b lam z'| := abs_add_le _ _
        _ ≤ C1 + |Real.log lam| := by
          have e : |fdlTruncE ψ s b lam z'| = |Real.log lam| := by rw [hz'v, abs_neg]
          rw [e]; linarith
        _ = |Real.log lam| + C1 := by ring
    nlinarith [abs_nonneg (Real.log lam)]

end HRS.MC.D3EG
