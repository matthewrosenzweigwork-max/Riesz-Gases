import HRS.MC.D3TGAux6

/-!
# Packet D3TG: Lemma D.3 on `𝕋^d`, item (ii) for the truncated kernel `g_λ = fdlTruncT`.

Spec: `HRS/Appendix/FDL.lean`, `HRS.fdl_kernel_torus` (the `fdlTruncT` conjuncts of (ii)).
Each theorem below has the hypotheses of `fdl_kernel_torus` and the conclusion copied from the
corresponding conjunct.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

namespace HRS.MC.D3TG

open HRS HRS.MC.D3T1

variable {d : ℕ}

lemma d3tg_iter_sub_const {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℝ) (j : ℕ) (y : Euc d) :
    ‖iteratedFDeriv ℝ j (fun w => f w - c) y‖ ≤ ‖iteratedFDeriv ℝ j f y‖ + |c| := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    exact abs_sub _ _
  · have : (fun w => f w - c) = fun w => 1 * f w + (-c) := by funext w; ring
    rw [this, d3tg_diter_affine_pos hf 1 (-c) hj y]
    simp

lemma d3tgc_abs_le (hd : 1 ≤ d) {s : ℝ} (hsd : s < d) (ψ : Euc d → ℝ) (b : ℝ) {lam : ℝ}
    (hl0 : 0 < lam) (hl1 : lam < 1) :
    |d3tgc ψ s b lam| ≤ |b| * |∫ x, fdlPhi ψ x| / ((d : ℝ) - s) := by
  have hds : 0 < (d : ℝ) - s := by linarith
  unfold d3tgc
  have h1 : lam ^ ((d : ℝ) - s) ≤ 1 := Real.rpow_le_one hl0.le hl1.le hds.le
  have h2 : 0 ≤ lam ^ ((d : ℝ) - s) := Real.rpow_nonneg hl0.le _
  rw [abs_div, abs_of_pos hds, abs_mul, abs_mul, abs_of_nonneg h2]
  have : |b| * |∫ x, fdlPhi ψ x| * lam ^ ((d : ℝ) - s) ≤ |b| * |∫ x, fdlPhi ψ x| :=
    mul_le_of_le_one_right (by positivity) h1
  exact div_le_div_of_nonneg_right this hds.le

lemma d3tg_lift_fun (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) {lam : ℝ} (hl0 : 0 < lam)
    (hl1 : lam < 1) :
    Torus.lift (fdlTruncT ψ s b lam) = fun y => d3tgH ψ s b lam y - d3tgc ψ s b lam :=
  funext fun y => d3tg_lift_eq hd hs0 hsd hψ hb hl0 hl1 y

theorem d3tg_smooth (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    (∀ lam : ℝ, 0 < lam → lam < 1 → Torus.IsSmooth (fdlTruncT ψ s b lam)) := by
  intro lam hl0 hl1
  unfold Torus.IsSmooth Torus.IsCk
  rw [d3tg_lift_fun hd hs0 hsd hψ hb hl0 hl1]
  exact (d3tgH_contDiff hd hψ hs0 b hl0 hl1).sub contDiff_const

theorem d3tg_sup (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    (∀ j : ℕ, 0 < (j : ℝ) + s → ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ y : Euc d,
      ‖iteratedFDeriv ℝ j (Torus.lift (fdlTruncT ψ s b lam)) y‖ ≤ C * lam ^ (-s - (j : ℝ))) := by
  intro j hj
  obtain ⟨C1, hC1, hmain⟩ := d3tgH_deriv_pos hd hψ hs0 hsd b j hj
  set Cc : ℝ := |b| * |∫ x, fdlPhi ψ x| / ((d : ℝ) - s) with hCc
  have hds : 0 < (d : ℝ) - s := by linarith
  have hCc0 : 0 ≤ Cc := by positivity
  refine ⟨C1 + C1 + Cc, by positivity, fun lam hl0 hl1 y => ?_⟩
  rw [d3tg_lift_fun hd hs0 hsd hψ hb hl0 hl1]
  refine (d3tg_iter_sub_const (d3tgH_contDiff hd hψ hs0 b hl0 hl1) _ j y).trans ?_
  have h1 := hmain lam hl0 hl1 y 0 (fun n => norm_nonneg _)
  rw [max_eq_left hl0.le] at h1
  have h2 := d3tgc_abs_le hd hsd ψ b hl0 hl1
  have h3 : 1 ≤ lam ^ (-s - (j : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hl0 hl1.le (by linarith)
  nlinarith [mul_nonneg hC1 (sub_nonneg.2 h3), mul_nonneg hCc0 (sub_nonneg.2 h3)]

theorem d3tg_deriv (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    (∀ j : ℕ, 0 < (j : ℝ) + s → ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 →
      ∀ y : Euc d, Torus.mk y ≠ 0 →
        ‖iteratedFDeriv ℝ j (Torus.lift (fdlTruncT ψ s b lam)) y‖ ≤
          C * (max lam (KernelGrad.tdist (Torus.mk y) 0)) ^ (-s - (j : ℝ)) + C) := by
  intro j hj
  obtain ⟨C1, hC1, hmain⟩ := d3tgH_deriv_pos hd hψ hs0 hsd b j hj
  set Cc : ℝ := |b| * |∫ x, fdlPhi ψ x| / ((d : ℝ) - s) with hCc
  have hds : 0 < (d : ℝ) - s := by linarith
  have hCc0 : 0 ≤ Cc := by positivity
  refine ⟨C1 + Cc, by positivity, fun lam hl0 hl1 y _ => ?_⟩
  rw [d3tg_lift_fun hd hs0 hsd hψ hb hl0 hl1]
  refine (d3tg_iter_sub_const (d3tgH_contDiff hd hψ hs0 b hl0 hl1) _ j y).trans ?_
  have h1 := hmain lam hl0 hl1 y (KernelGrad.tdist (Torus.mk y) 0) (fun n => by
    have := d3t_tdist_mk_le (y + Lattice.toEuc n)
    rwa [d3t_mk_add] at this)
  have h2 := d3tgc_abs_le hd hsd ψ b hl0 hl1
  have h3 : 0 ≤ (max lam (KernelGrad.tdist (Torus.mk y) 0)) ^ (-s - (j : ℝ)) :=
    Real.rpow_nonneg (le_trans hl0.le (le_max_left _ _)) _
  nlinarith [mul_nonneg hCc0 h3]

theorem d3tg_log (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ x : Torus d,
      s = 0 → |fdlTruncT ψ s b lam x| ≤ C * (1 + |Real.log lam|)) := by
  by_cases hs : s = 0
  · subst hs
    obtain ⟨C1, hC1, hmain⟩ := d3tgH_log hd hψ (by exact_mod_cast hd) b
    set Cc : ℝ := |b| * |∫ x, fdlPhi ψ x| / ((d : ℝ) - 0) with hCc
    have hds : 0 < (d : ℝ) - 0 := by simp; omega
    have hCc0 : 0 ≤ Cc := by positivity
    refine ⟨C1 + Cc, by positivity, fun lam hl0 hl1 x _ => ?_⟩
    rw [d3tg_trunc_eq hd hs0 hsd hψ hb hl0 hl1]
    have h1 := hmain lam hl0 hl1 (Torus.rep x)
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h1
    have h2 := d3tgc_abs_le hd hsd ψ b hl0 hl1
    have h3 : 0 ≤ |Real.log lam| := abs_nonneg _
    calc |d3tgH ψ 0 b lam (Torus.rep x) - d3tgc ψ 0 b lam|
        ≤ |d3tgH ψ 0 b lam (Torus.rep x)| + |d3tgc ψ 0 b lam| := abs_sub _ _
      _ ≤ C1 * (1 + |Real.log lam|) + Cc := add_le_add h1 h2
      _ ≤ (C1 + Cc) * (1 + |Real.log lam|) := by nlinarith [mul_nonneg hCc0 h3]
  · exact ⟨0, le_refl _, fun lam _ _ x h => absurd h hs⟩

theorem d3tg_zero (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 →
      |fdlTruncT ψ s b lam 0| ≤
        C * (lam ^ (-s) + (if s = 0 then |Real.log lam| else 0))) := by
  by_cases hs : s = 0
  · obtain ⟨C, hC, hmain⟩ := d3tg_log hd hs0 hsd hψ hb
    refine ⟨C, hC, fun lam hl0 hl1 => ?_⟩
    have := hmain lam hl0 hl1 0 hs
    subst hs
    simpa using this
  · have hj : 0 < ((0 : ℕ) : ℝ) + s := by
      have : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
      simpa using this
    obtain ⟨C, hC, hmain⟩ := d3tg_sup hd hs0 hsd hψ hb 0 hj
    refine ⟨C, hC, fun lam hl0 hl1 => ?_⟩
    have := hmain lam hl0 hl1 0
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    have e0 : Torus.lift (fdlTruncT ψ s b lam) 0 = fdlTruncT ψ s b lam 0 := by
      show fdlTruncT ψ s b lam (Torus.mk 0) = _
      congr 1
    rw [e0] at this
    rw [if_neg hs, add_zero]
    simpa using this

/-- Fidelity check: the conclusions are literally the corresponding conjuncts of `fdl_kernel_torus`. -/
example (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) : True := by
  have h1 := (fdl_kernel_torus hd hs0 hsd hψ hb).2.2.2.1
  have _ : type_of% h1 := d3tg_log hd hs0 hsd hψ hb
  have h3 := (fdl_kernel_torus hd hs0 hsd hψ hb).2.2.2.2.1
  have _ : type_of% h3 := d3tg_smooth hd hs0 hsd hψ hb
  have h5 := (fdl_kernel_torus hd hs0 hsd hψ hb).2.2.2.2.2.1
  have _ : type_of% h5 := d3tg_sup hd hs0 hsd hψ hb
  have h7 := (fdl_kernel_torus hd hs0 hsd hψ hb).2.2.2.2.2.2.1
  have _ : type_of% h7 := d3tg_zero hd hs0 hsd hψ hb
  trivial

end HRS.MC.D3TG
