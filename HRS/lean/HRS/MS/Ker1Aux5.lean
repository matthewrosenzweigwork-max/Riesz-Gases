import HRS.MS.Ker1Aux4

/-!
# MS-KER1, helper file 5: local form and derivative bounds of the unit-period kernel `g₁`
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise ContDiff

namespace HRS.MS.Ker1

open HRS HRS.Whole

variable {d : ℕ}

theorem ker1_local_form (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ (r : Torus d → ℝ) (δ : ℝ), 0 < δ ∧ Torus.IsSmooth r ∧ ∀ x : Euc d, ‖x‖ < δ → x ≠ 0 →
      periodicRiesz d s (Torus.mk x) = rieszKernel d s x + r (Torus.mk x) := by
  rcases Nat.lt_or_ge d 2 with h | h
  · obtain rfl : d = 1 := by omega
    by_cases hs : s = 0
    · subst hs
      obtain ⟨r, δ, hδ, hr, hloc⟩ := periodicLog_local_singularity_d1
      refine ⟨r, δ, hδ, hr, fun x hx hx0 => ?_⟩
      rw [hloc x hx hx0]; simp [rieszKernel]
    · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
      have hs1 : s < 1 := by exact_mod_cast hsd
      obtain ⟨r, δ, hδ, hr, hloc⟩ := periodicRiesz_local_singularity_d1 hspos hs1
      refine ⟨r, δ, hδ, hr, fun x hx hx0 => ?_⟩
      rw [hloc x hx hx0]; simp [rieszKernel, hs]
  · by_cases hs : s = 0
    · subst hs
      obtain ⟨r, δ, hδ, hr, hloc⟩ := periodicLog_local_singularity h
      refine ⟨r, δ, hδ, hr, fun x hx hx0 => ?_⟩
      rw [hloc x hx hx0]; simp [rieszKernel]
    · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
      obtain ⟨r, δ, hδ, hr, hloc⟩ := periodicRiesz_local_singularity h hspos hsd
      refine ⟨r, δ, hδ, hr, fun x hx hx0 => ?_⟩
      rw [hloc x hx hx0]; simp [rieszKernel, hs]

theorem ker1_mk_ne_zero_of_norm {y : Euc d} (hy0 : y ≠ 0) (hy : ‖y‖ ≤ 1 / 2) : Torus.mk y ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := ker1_mk_eq_zero h
  have h1 : n ≠ 0 := by
    rintro rfl
    apply hy0; rw [hn]; ext i; simp [Lattice.toEuc]
  have h2 := one_le_enorm n h1
  have h3 : Lattice.enorm n = ‖Lattice.toEuc n‖ := rfl
  rw [← hn] at h3
  linarith

theorem ker1_g1_contDiffOn (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ContDiffOn ℝ ∞ (ker1_g1 d s) {y : Euc d | Torus.mk y ≠ 0} := fun y hy =>
  (KernelD1Aux.contDiffAt_lift_g hd hs0 hsd y (HRS.KernelGrad.wsq_pos_of_mk_ne_zero hy)).contDiffWithinAt

theorem ker1_continuousOn_iteratedFDeriv {f : Euc d → ℝ}
    (hf : ContDiffOn ℝ ∞ f {y : Euc d | Torus.mk y ≠ 0}) (n : ℕ) :
    ContinuousOn (iteratedFDeriv ℝ n f) {y : Euc d | Torus.mk y ≠ 0} := by
  have hU : IsOpen {y : Euc d | Torus.mk y ≠ 0} := HRS.KernelGrad.isOpen_mk_ne_zero
  have h1 := hf.continuousOn_iteratedFDerivWithin (m := n) (by exact_mod_cast le_top)
    hU.uniqueDiffOn
  exact h1.congr (iteratedFDerivWithin_of_isOpen n hU).symm

theorem ker1_isCompact_annulus {a b : ℝ} : IsCompact {w : Euc d | a ≤ ‖w‖ ∧ ‖w‖ ≤ b} := by
  have : {w : Euc d | a ≤ ‖w‖ ∧ ‖w‖ ≤ b} ⊆ Metric.closedBall (0 : Euc d) b := fun w hw => by
    simpa using hw.2
  refine (isCompact_closedBall (0 : Euc d) b).of_isClosed_subset ?_ this
  exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)


theorem ker1_decomp (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ (q : Euc d → ℝ) (δ : ℝ), 0 < δ ∧ ContDiff ℝ ∞ q ∧ ∀ y : Euc d, ‖y‖ < δ → y ≠ 0 →
      ker1_g1 d s y = rieszKernel d s y + q y := by
  obtain ⟨r, δ, hδ, hr, hloc⟩ := ker1_local_form hd hs0 hsd
  exact ⟨Torus.lift r, δ, hδ, hr, fun y hy hy0 => hloc y hy hy0⟩

theorem ker1_g1_bound (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (n : ℕ)
    (hn : 0 < (n : ℝ) + s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Euc d, y ≠ 0 → ‖y‖ ≤ 1 / 2 →
      ‖iteratedFDeriv ℝ n (ker1_g1 d s) y‖ ≤ C * ‖y‖ ^ (-s - n) := by
  obtain ⟨q, δ, hδ, hq, hloc⟩ := ker1_decomp hd hs0 hsd
  set δ₁ : ℝ := min (δ / 2) (1 / 2) with hδ₁
  have hδ₁0 : 0 < δ₁ := lt_min (by linarith) (by norm_num)
  have hδ₁δ : δ₁ < δ := by have := min_le_left (δ / 2) (1 / 2); linarith
  have hδ₁h : δ₁ ≤ 1 / 2 := min_le_right _ _
  obtain ⟨M1, hM1⟩ := (isCompact_closedBall (0 : Euc d) δ₁).exists_bound_of_continuousOn
    (hq.continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)).continuousOn
  obtain ⟨C1, hC10, hC1⟩ := ker1_E_bound (d := d) (s := s) hs0 n hn
  have hK := ker1_isCompact_annulus (d := d) (a := δ₁) (b := 1 / 2)
  have hsm := ker1_g1_contDiffOn hd hs0 hsd
  obtain ⟨M2, hM2⟩ := hK.exists_bound_of_continuousOn
    ((ker1_continuousOn_iteratedFDeriv hsm n).mono (by
      intro w hw
      exact ker1_mk_ne_zero_of_norm (norm_pos_iff.mp (lt_of_lt_of_le hδ₁0 hw.1)) hw.2))
  refine ⟨max (C1 + M1) (max M2 0), le_trans (le_max_right _ _) (le_max_right _ _), fun w hw0 hwb => ?_⟩
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have h1le : 1 ≤ ‖w‖ ^ (-s - (n : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hwpos (by linarith) (by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith)
  by_cases hnear : ‖w‖ ≤ δ₁
  · have hev : (ker1_g1 d s) =ᶠ[𝓝 w] fun y => rieszKernel d s y + q y := by
      have hopen : IsOpen (Metric.ball (0 : Euc d) δ ∩ {(0 : Euc d)}ᶜ) :=
        Metric.isOpen_ball.inter isOpen_compl_singleton
      have hw' : w ∈ Metric.ball (0 : Euc d) δ ∩ {(0 : Euc d)}ᶜ :=
        ⟨by rw [mem_ball_zero_iff]; linarith, hw0⟩
      filter_upwards [hopen.mem_nhds hw'] with y hy
      have hy1 : ‖y‖ < δ := by simpa using hy.1
      exact hloc y hy1 hy.2
    have hcd1 : ContDiffAt ℝ ∞ (rieszKernel d s) w := by
      by_cases hs : s = 0
      · subst hs
        have : rieszKernel d 0 = fun x : Euc d => -Real.log ‖x‖ := by funext x; simp [rieszKernel]
        rw [this]; exact ker1_contDiffAt_log_norm hw0
      · have : rieszKernel d s = fun x : Euc d => ‖x‖ ^ (-s) := by funext x; simp [rieszKernel, hs]
        rw [this]; exact (contDiffAt_norm ℝ hw0).rpow_const_of_ne (norm_ne_zero_iff.mpr hw0)
    rw [(hev.iteratedFDeriv ℝ n).eq_of_nhds]
    rw [show (fun y : Euc d => rieszKernel d s y + q y) = rieszKernel d s + q from rfl,
      iteratedFDeriv_add_apply (hcd1.of_le (by exact_mod_cast le_top))
      (hq.contDiffAt.of_le (by exact_mod_cast le_top))]
    refine (norm_add_le _ _).trans ?_
    have h1 := hC1 w hw0
    have h2 := hM1 w (by rw [mem_closedBall_zero_iff]; exact hnear)
    calc ‖iteratedFDeriv ℝ n (rieszKernel d s) w‖ + ‖iteratedFDeriv ℝ n q w‖
        ≤ C1 * ‖w‖ ^ (-s - (n : ℝ)) + M1 * 1 := add_le_add h1 (by linarith)
      _ ≤ C1 * ‖w‖ ^ (-s - (n : ℝ)) + M1 * ‖w‖ ^ (-s - (n : ℝ)) := by
          have hM1' : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0 (by simp [hδ₁0.le]))
          nlinarith
      _ ≤ max (C1 + M1) (max M2 0) * ‖w‖ ^ (-s - (n : ℝ)) := by
          have hp : 0 ≤ ‖w‖ ^ (-s - (n : ℝ)) := by positivity
          have : C1 + M1 ≤ max (C1 + M1) (max M2 0) := le_max_left _ _
          nlinarith
  · push_neg at hnear
    have h2 := hM2 w ⟨hnear.le, hwb⟩
    have hp : 0 ≤ ‖w‖ ^ (-s - (n : ℝ)) := by positivity
    calc ‖iteratedFDeriv ℝ n (ker1_g1 d s) w‖ ≤ M2 := h2
      _ ≤ M2 * ‖w‖ ^ (-s - (n : ℝ)) := by
          have hM2' : 0 ≤ M2 := (norm_nonneg _).trans h2
          nlinarith
      _ ≤ max (C1 + M1) (max M2 0) * ‖w‖ ^ (-s - (n : ℝ)) := by
          have : M2 ≤ max (C1 + M1) (max M2 0) := (le_max_left M2 0).trans (le_max_right _ _)
          nlinarith


theorem ker1_g1_log_bound (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Euc d, y ≠ 0 → ‖y‖ ≤ 1 / 2 →
      |ker1_g1 d 0 y + Real.log ‖y‖| ≤ C := by
  have hsd : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨q, δ, hδ, hq, hloc⟩ := ker1_decomp hd le_rfl hsd
  set δ₁ : ℝ := min (δ / 2) (1 / 2) with hδ₁
  have hδ₁0 : 0 < δ₁ := lt_min (by linarith) (by norm_num)
  have hδ₁δ : δ₁ < δ := by have := min_le_left (δ / 2) (1 / 2); linarith
  have hδ₁h : δ₁ ≤ 1 / 2 := min_le_right _ _
  obtain ⟨M1, hM1⟩ := (isCompact_closedBall (0 : Euc d) δ₁).exists_bound_of_continuousOn
    hq.continuous.continuousOn
  have hK := ker1_isCompact_annulus (d := d) (a := δ₁) (b := 1 / 2)
  have hsm := ker1_g1_contDiffOn hd le_rfl hsd
  obtain ⟨M2, hM2⟩ := hK.exists_bound_of_continuousOn
    (hsm.continuousOn.mono (by
      intro w hw
      exact ker1_mk_ne_zero_of_norm (norm_pos_iff.mp (lt_of_lt_of_le hδ₁0 hw.1)) hw.2))
  refine ⟨max M1 (M2 + |Real.log δ₁|), le_trans (norm_nonneg _) ((hM1 0 (by simp [hδ₁0.le])).trans
    (le_max_left _ _)), fun w hw0 hwb => ?_⟩
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  by_cases hnear : ‖w‖ ≤ δ₁
  · refine le_trans ?_ (le_max_left _ _)
    rw [hloc w (by linarith) hw0]
    simp only [rieszKernel, if_true]
    have := hM1 w (by rw [mem_closedBall_zero_iff]; exact hnear)
    simpa using this
  · push_neg at hnear
    refine le_trans ?_ (le_max_right _ _)
    have h2 := hM2 w ⟨hnear.le, hwb⟩
    have h3 : |Real.log ‖w‖| ≤ |Real.log δ₁| := by
      have hl1 : Real.log δ₁ ≤ Real.log ‖w‖ := Real.log_le_log hδ₁0 hnear.le
      have hl2 : Real.log ‖w‖ ≤ 0 := Real.log_nonpos hwpos.le (by linarith)
      rw [abs_of_nonpos hl2, abs_of_nonpos (by linarith : Real.log δ₁ ≤ 0)]
      linarith
    calc |ker1_g1 d 0 w + Real.log ‖w‖| ≤ |ker1_g1 d 0 w| + |Real.log ‖w‖| := abs_add_le _ _
      _ ≤ M2 + |Real.log δ₁| := add_le_add (by simpa using h2) h3


theorem ker1_contDiffAt_E {s : ℝ} {x : Euc d} (hx : x ≠ 0) : ContDiffAt ℝ ∞ (rieszKernel d s) x := by
  by_cases hs : s = 0
  · subst hs
    have : rieszKernel d 0 = fun x : Euc d => -Real.log ‖x‖ := by funext x; simp [rieszKernel]
    rw [this]; exact ker1_contDiffAt_log_norm hx
  · have : rieszKernel d s = fun x : Euc d => ‖x‖ ^ (-s) := by funext x; simp [rieszKernel, hs]
    rw [this]; exact (contDiffAt_norm ℝ hx).rpow_const_of_ne (norm_ne_zero_iff.mpr hx)

theorem ker1_gam_iter (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {L : ℝ} (hL : 0 < L)
    {x : Euc d} (hx : Torus.mk (L⁻¹ • x) ≠ 0) (n : ℕ) :
    iteratedFDeriv ℝ n (ker1_gam d s L) x =
      (L ^ (-s) * (L⁻¹) ^ n) • iteratedFDeriv ℝ n (ker1_g1 d s) (L⁻¹ • x) := by
  have h1 : ContDiffAt ℝ n (fun y : Euc d => ker1_g1 d s (L⁻¹ • y)) x :=
    ((ker1_g1_contDiffOn hd hs0 hsd (L⁻¹ • x) hx).contDiffAt
      ((HRS.KernelGrad.isOpen_mk_ne_zero).mem_nhds hx)).of_le (by exact_mod_cast le_top) |>.comp x
      ((contDiff_const_smul L⁻¹).contDiffAt)
  have h2 : ker1_gam d s L = fun y => L ^ (-s) • (fun y : Euc d => ker1_g1 d s (L⁻¹ • y)) y := rfl
  rw [h2, iteratedFDeriv_const_smul_apply' h1, ker1_iteratedFDeriv_comp_smul _ (inv_ne_zero hL.ne') n x,
    smul_smul]

theorem ker1_gam_eventually (hd : 1 ≤ d) {s : ℝ} {q : Euc d → ℝ} {δ : ℝ}
    (hloc : ∀ y : Euc d, ‖y‖ < δ → y ≠ 0 → ker1_g1 d s y = rieszKernel d s y + q y)
    {L : ℝ} (hL : 0 < L) {x : Euc d} (hx0 : x ≠ 0) (hx : ‖x‖ < δ * L) :
    ker1_gam d s L =ᶠ[𝓝 x] fun y => rieszKernel d s y + (if s = 0 then Real.log L else 0) +
      L ^ (-s) * q (L⁻¹ • y) := by
  have hopen : IsOpen (Metric.ball (0 : Euc d) (δ * L) ∩ {(0 : Euc d)}ᶜ) :=
    Metric.isOpen_ball.inter isOpen_compl_singleton
  have hx' : x ∈ Metric.ball (0 : Euc d) (δ * L) ∩ {(0 : Euc d)}ᶜ :=
    ⟨by rw [mem_ball_zero_iff]; exact hx, hx0⟩
  filter_upwards [hopen.mem_nhds hx'] with y hy
  have hy1 : ‖y‖ < δ * L := by simpa using hy.1
  have hy0 : y ≠ 0 := hy.2
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hn1 : ‖L⁻¹ • y‖ < δ := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hL, inv_mul_lt_iff₀ hL, mul_comm]; exact hy1
  have hn0 : L⁻¹ • y ≠ 0 := smul_ne_zero (inv_ne_zero hL.ne') hy0
  show L ^ (-s) * ker1_g1 d s (L⁻¹ • y) = _
  rw [hloc _ hn1 hn0]
  by_cases hs : s = 0
  · subst hs
    rw [show rieszKernel d 0 (L⁻¹ • y) = -Real.log ‖L⁻¹ • y‖ by simp [rieszKernel],
      show rieszKernel d 0 y = -Real.log ‖y‖ by simp [rieszKernel]]
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hL,
      Real.log_mul (inv_ne_zero hL.ne') hyn.ne', Real.log_inv]
    simp
  · rw [show rieszKernel d s (L⁻¹ • y) = ‖L⁻¹ • y‖ ^ (-s) by simp [rieszKernel, hs],
      show rieszKernel d s y = ‖y‖ ^ (-s) by simp [rieszKernel, hs]]
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hL,
      Real.mul_rpow (inv_nonneg.2 hL.le) hyn.le, Real.inv_rpow hL.le]
    have hp : 0 < L ^ (-s) := Real.rpow_pos_of_pos hL _
    simp only [hs, ite_false]
    field_simp
    ring


theorem ker1_gam_sub_E (hd : 1 ≤ d) {s : ℝ} {q : Euc d → ℝ} {δ : ℝ} (hq : ContDiff ℝ ∞ q)
    (hloc : ∀ y : Euc d, ‖y‖ < δ → y ≠ 0 → ker1_g1 d s y = rieszKernel d s y + q y)
    {L : ℝ} (hL : 0 < L) {x : Euc d} (hx0 : x ≠ 0) (hx : ‖x‖ < δ * L) {n : ℕ}
    (hn : n ≠ 0 ∨ s ≠ 0) :
    iteratedFDeriv ℝ n (ker1_gam d s L) x - iteratedFDeriv ℝ n (rieszKernel d s) x =
      (L ^ (-s) * (L⁻¹) ^ n) • iteratedFDeriv ℝ n q (L⁻¹ • x) := by
  have hev := ker1_gam_eventually hd hloc hL hx0 hx
  set c : ℝ := if s = 0 then Real.log L else 0 with hc
  have hcd1 : ContDiffAt ℝ n (rieszKernel d s) x :=
    (ker1_contDiffAt_E hx0).of_le (by exact_mod_cast le_top)
  have hq' : ContDiffAt ℝ n q (L⁻¹ • x) := hq.contDiffAt.of_le (by exact_mod_cast le_top)
  have hqc : ContDiffAt ℝ n (fun y : Euc d => q (L⁻¹ • y)) x :=
    hq'.comp x ((contDiff_const_smul L⁻¹).contDiffAt)
  have hcd2 : ContDiffAt ℝ n (fun y : Euc d => L ^ (-s) • q (L⁻¹ • y)) x :=
    hqc.const_smul (L ^ (-s))
  rw [(hev.iteratedFDeriv ℝ n).eq_of_nhds]
  have e1 : (fun y : Euc d => rieszKernel d s y + c + L ^ (-s) * q (L⁻¹ • y)) =
      (fun y => rieszKernel d s y + c) + (fun y : Euc d => L ^ (-s) • q (L⁻¹ • y)) := rfl
  have e2 : (fun y : Euc d => rieszKernel d s y + c) = rieszKernel d s + fun _ => c := rfl
  rw [e1, iteratedFDeriv_add_apply (hcd1.add contDiffAt_const) hcd2, e2,
    iteratedFDeriv_add_apply hcd1 contDiffAt_const]
  have h0 : iteratedFDeriv ℝ n (fun _ : Euc d => c) x = 0 := by
    rcases hn with hn | hs
    · rw [iteratedFDeriv_const_of_ne hn c]; rfl
    · have : c = 0 := by simp [hc, hs]
      rw [this]; simp
  have h3 : iteratedFDeriv ℝ n (fun y : Euc d => L ^ (-s) • q (L⁻¹ • y)) x =
      (L ^ (-s) * (L⁻¹) ^ n) • iteratedFDeriv ℝ n q (L⁻¹ • x) := by
    rw [iteratedFDeriv_const_smul_apply' hqc,
      ker1_iteratedFDeriv_comp_smul q (inv_ne_zero hL.ne') n x, smul_smul]
  rw [h0, add_zero, h3]
  abel


theorem ker1_gam_scale_pow {s : ℝ} {L : ℝ} (hL : 0 < L) (n : ℕ) :
    L ^ (-s) * (L⁻¹) ^ n = L ^ (-(s + n)) := by
  rw [Real.rpow_neg hL.le, Real.rpow_neg hL.le, Real.rpow_add hL, Real.rpow_natCast, inv_pow,
    mul_inv, mul_comm]

theorem ker1_conv_aux (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) {q : Euc d → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hq : ContDiff ℝ ∞ q)
    (hloc : ∀ y : Euc d, ‖y‖ < δ → y ≠ 0 → ker1_g1 d s y = rieszKernel d s y + q y)
    {K : Set (Euc d)} (hK : IsCompact K) (hK0 : ∀ x ∈ K, x ≠ 0) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∀ x ∈ K,
      ((n ≠ 0 ∨ s ≠ 0) → ‖iteratedFDeriv ℝ n (ker1_gam d s L) x - iteratedFDeriv ℝ n (rieszKernel d s) x‖ ≤ ε) ∧
      (n = 0 → s = 0 → |ker1_gam d s L x - rieszKernel d s x - (Real.log L + q 0)| ≤ ε) := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  set R' : ℝ := max R 1 with hR'
  have hR'0 : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hR'K : ∀ x ∈ K, ‖x‖ ≤ R' := fun x hx => (hR x hx).trans (le_max_left _ _)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Euc d) (δ / 2)).exists_bound_of_continuousOn
    (hq.continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)).continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Metric.mem_closedBall_self (by positivity)))
  obtain ⟨η, hη, hqη⟩ := Metric.continuousAt_iff.mp hq.continuous.continuousAt ε hε
  have e1 : ∀ᶠ L : ℝ in atTop, 2 * R' / δ ≤ L := eventually_ge_atTop _
  have e0 : ∀ᶠ L : ℝ in atTop, 1 ≤ L := eventually_ge_atTop _
  have e3 : ∀ᶠ L : ℝ in atTop, 2 * R' / η ≤ L := eventually_ge_atTop _
  have e2 : ∀ᶠ L : ℝ in atTop, 1 ≤ L → (n ≠ 0 ∨ s ≠ 0) → L ^ (-(s + n)) * M ≤ ε := by
    by_cases hns : n ≠ 0 ∨ s ≠ 0
    · have hpos : 0 < s + (n : ℝ) := by
        rcases hns with h | h
        · have : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
          linarith
        · have : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h)
          have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          linarith
      have ht := (tendsto_rpow_neg_atTop hpos).eventually
        (gt_mem_nhds (show (0 : ℝ) < ε / (M + 1) by positivity))
      filter_upwards [ht] with L hL h1L _
      have hLp : 0 < L := lt_of_lt_of_le one_pos h1L
      have h1 : L ^ (-(s + n)) * (M + 1) ≤ ε := by
        have := (lt_div_iff₀ (by positivity : (0 : ℝ) < M + 1)).mp hL
        linarith
      have h2 : 0 ≤ L ^ (-(s + n)) := Real.rpow_nonneg hLp.le _
      nlinarith
    · exact Filter.Eventually.of_forall fun L _ h => absurd h hns
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp (e1.and (e0.and (e3.and e2)))
  refine ⟨max L₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun L hL x hxK => ?_⟩
  obtain ⟨h1, h0, h3, h2⟩ := hL₀ L ((le_max_left _ _).trans hL)
  have hLp : 0 < L := lt_of_lt_of_le one_pos h0
  have hx0 := hK0 x hxK
  have hxR := hR'K x hxK
  have hδL : 2 * R' ≤ δ * L := by
    have := (div_le_iff₀ hδ).mp h1; linarith
  have hx : ‖x‖ < δ * L := by linarith
  have hnorm : ‖L⁻¹ • x‖ = ‖x‖ / L := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hLp, inv_mul_eq_div]
  have hxz : ‖L⁻¹ • x‖ ≤ δ / 2 := by
    rw [hnorm, div_le_iff₀ hLp]; nlinarith
  refine ⟨fun hns => ?_, fun hn hs => ?_⟩
  · rw [ker1_gam_sub_E hd hq hloc hLp hx0 hx hns, norm_smul, ker1_gam_scale_pow hLp,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hLp.le _)]
    have := hM (L⁻¹ • x) (by rw [mem_closedBall_zero_iff]; exact hxz)
    calc L ^ (-(s + n)) * ‖iteratedFDeriv ℝ n q (L⁻¹ • x)‖ ≤ L ^ (-(s + n)) * M :=
          mul_le_mul_of_nonneg_left this (Real.rpow_nonneg hLp.le _)
      _ ≤ ε := h2 h0 hns
  · subst hs
    have hev := (ker1_gam_eventually hd hloc hLp hx0 hx).self_of_nhds
    simp only [ite_true, neg_zero, Real.rpow_zero, one_mul] at hev
    rw [hev]
    have hlt : dist (L⁻¹ • x) 0 < η := by
      rw [dist_zero_right, hnorm, div_lt_iff₀ hLp]
      have := (div_le_iff₀ hη).mp h3
      nlinarith
    have := hqη hlt
    rw [Real.dist_eq] at this
    have e : rieszKernel d 0 x + Real.log L + q (L⁻¹ • x) - rieszKernel d 0 x - (Real.log L + q 0) =
        q (L⁻¹ • x) - q 0 := by ring
    rw [e]
    exact this.le

end HRS.MS.Ker1
