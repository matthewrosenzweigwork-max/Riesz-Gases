import HRS.MC.FDLEAux1

/-!
# Packet FDLE, auxiliary facts on the kernels `w_λ`, `F`, and the normalisation `b φ(0) = 1`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.MC.FDLE

open HRS

variable {d : ℕ}

/-- The integrand `F(t,z) = t^{d-s} φ_t(z) / t` of Definition D.2 is nonnegative. -/
lemma fdle_F_nonneg {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (s : ℝ) {t : ℝ} (ht : 0 < t) (z : Euc d) :
    0 ≤ t ^ ((d : ℝ) - s) * fdlPhiScale ψ t z / t :=
  div_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (fdle_phiScale_nonneg hψ ht z)) ht.le

/-- For `z ≠ 0` and `0 ≤ s < d`, the integrand is integrable on `(0, R]` (from `IsFDLConst`). -/
lemma fdle_F_integrable {ψ : Euc d → ℝ} {s : ℝ} (hs0 : 0 ≤ s) {b : ℝ}
    (hb : IsFDLConst ψ s b) {z : Euc d} (hz : z ≠ 0) {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - s) * fdlPhiScale ψ t z / t) (Ioc 0 R) := by
  rcases hs0.eq_or_lt with h | h
  · subst h
    obtain ⟨C, hC⟩ := hb.2.2.1 rfl
    exact (hC z hz).1 R hR
  · exact ((hb.2.1 h z hz).1).mono_set Ioc_subset_Ioi_self

/-- At `s = 0` the integrand is `φ(t⁻¹ • x) / t` for `t > 0`. -/
lemma fdle_F0_eq {ψ : Euc d → ℝ} {t : ℝ} (ht : 0 < t) (x : Euc d) :
    t ^ ((d : ℝ) - 0) * fdlPhiScale ψ t x / t = fdlPhi ψ (t⁻¹ • x) / t := by
  unfold fdlPhiScale
  rw [sub_zero, Real.rpow_natCast, ← mul_assoc, mul_inv_cancel₀ (pow_pos ht d).ne', one_mul]

/-- Change of variables `t = c u` in the `s = 0` profile integral. -/
lemma fdle_scale_identity {ψ : Euc d → ℝ} {c : ℝ} (hc : 0 < c) (e : Euc d) {R : ℝ} (hR : 0 ≤ R) :
    ∫ t in Ioc 0 R, fdlPhi ψ (t⁻¹ • (c • e)) / t
      = ∫ u in Ioc 0 (R / c), fdlPhi ψ (u⁻¹ • e) / u := by
  rw [← intervalIntegral.integral_of_le hR, ← intervalIntegral.integral_of_le (div_nonneg hR hc.le)]
  have key := intervalIntegral.integral_comp_mul_left
    (fun t => fdlPhi ψ (t⁻¹ • (c • e)) / t) (a := 0) (b := R / c) hc.ne'
  rw [mul_zero, mul_div_cancel₀ R hc.ne'] at key
  have hf : ∀ u : ℝ, fdlPhi ψ ((c * u)⁻¹ • (c • e)) / (c * u)
      = c⁻¹ * (fdlPhi ψ (u⁻¹ • e) / u) := by
    intro u
    rw [smul_smul]
    have h1 : (c * u)⁻¹ * c = u⁻¹ := by
      rw [mul_inv]
      by_cases hu : u = 0
      · simp [hu]
      · field_simp
    rw [h1, div_eq_inv_mul, mul_inv, ← div_eq_inv_mul]
    ring
  have hL : ∫ u in (0 : ℝ)..(R / c), fdlPhi ψ ((c * u)⁻¹ • (c • e)) / (c * u)
      = c⁻¹ * ∫ u in (0 : ℝ)..(R / c), fdlPhi ψ (u⁻¹ • e) / u := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext u
    exact hf u
  simp only [smul_eq_mul] at key
  have h3 := hL.symm.trans key
  exact (mul_left_cancel₀ (inv_ne_zero hc.ne') h3).symm

/-- Scaling of the `s = 0` truncated integral: `A(c x, R) = A(x, R/c)`. -/
lemma fdle_A_scale {ψ : Euc d → ℝ} {c : ℝ} (hc : 0 < c) (x : Euc d) {R : ℝ} (hR : 0 ≤ R) :
    ∫ t in Ioc 0 R, t ^ ((d : ℝ) - 0) * fdlPhiScale ψ t (c • x) / t
      = ∫ t in Ioc 0 (R / c), t ^ ((d : ℝ) - 0) * fdlPhiScale ψ t x / t := by
  have h1 : ∫ t in Ioc 0 R, t ^ ((d : ℝ) - 0) * fdlPhiScale ψ t (c • x) / t
      = ∫ t in Ioc 0 R, fdlPhi ψ (t⁻¹ • (c • x)) / t :=
    setIntegral_congr_fun measurableSet_Ioc (fun t ht => fdle_F0_eq ht.1 (c • x))
  have h2 : ∫ t in Ioc 0 (R / c), t ^ ((d : ℝ) - 0) * fdlPhiScale ψ t x / t
      = ∫ t in Ioc 0 (R / c), fdlPhi ψ (t⁻¹ • x) / t :=
    setIntegral_congr_fun measurableSet_Ioc (fun t ht => fdle_F0_eq ht.1 x)
  rw [h1, h2]
  exact fdle_scale_identity hc x hR

lemma fdle_rk0 (x : Euc d) : Whole.rieszKernel d 0 x = -Real.log ‖x‖ := by
  simp [Whole.rieszKernel]

lemma fdle_rk_pos (s : ℝ) (hs : s ≠ 0) (x : Euc d) : Whole.rieszKernel d s x = ‖x‖ ^ (-s) := by
  simp [Whole.rieszKernel, hs]

/-- `b φ(0) = 1` from the `s = 0` clause of `IsFDLConst` (scaling `x ↦ 2x`). -/
lemma fdle_b_phi0 {ψ : Euc d → ℝ} (hd : 1 ≤ d) {b : ℝ} (hb : IsFDLConst ψ 0 b) :
    b * fdlPhi ψ 0 = 1 := by
  obtain ⟨x0, hx0⟩ : ∃ x0 : Euc d, x0 ≠ 0 :=
    Module.finrank_pos_iff_exists_ne_zero.mp (by rw [finrank_euclideanSpace_fin]; omega)
  obtain ⟨C, hC⟩ := hb.2.2.1 rfl
  have hx := (hC x0 hx0).2
  have h2x := (hC ((2 : ℝ) • x0) (smul_ne_zero two_ne_zero hx0)).2
  set φ0 := fdlPhi ψ 0 with hφ0
  have hr : 0 < ‖x0‖ := norm_pos_iff.mpr hx0
  have hQ : Tendsto (fun R : ℝ => (∫ t in Ioc 0 (R / 2), t ^ ((d : ℝ) - 0) * fdlPhiScale ψ t x0 / t)
      - φ0 * Real.log (R / 2)) atTop (𝓝 ((Whole.rieszKernel d 0 x0 - C) / b)) :=
    hx.comp (tendsto_id.atTop_div_const two_pos)
  have hP : Tendsto (fun R : ℝ => (∫ t in Ioc 0 R, t ^ ((d : ℝ) - 0) * fdlPhiScale ψ t ((2 : ℝ) • x0) / t)
      - φ0 * Real.log R) atTop (𝓝 ((Whole.rieszKernel d 0 ((2 : ℝ) • x0) - C) / b)) := h2x
  have heq : (fun R : ℝ => (∫ t in Ioc 0 (R / 2), t ^ ((d : ℝ) - 0) * fdlPhiScale ψ t x0 / t)
      - φ0 * Real.log (R / 2)
      - ((∫ t in Ioc 0 R, t ^ ((d : ℝ) - 0) * fdlPhiScale ψ t ((2 : ℝ) • x0) / t)
      - φ0 * Real.log R))
      =ᶠ[atTop] fun _ => φ0 * Real.log 2 := by
    filter_upwards [eventually_gt_atTop 0] with R hR
    rw [fdle_A_scale two_pos x0 hR.le, Real.log_div hR.ne' two_ne_zero]
    ring
  have hconst : Tendsto (fun R : ℝ => (∫ t in Ioc 0 (R / 2), t ^ ((d : ℝ) - 0) * fdlPhiScale ψ t x0 / t)
      - φ0 * Real.log (R / 2)
      - ((∫ t in Ioc 0 R, t ^ ((d : ℝ) - 0) * fdlPhiScale ψ t ((2 : ℝ) • x0) / t)
      - φ0 * Real.log R)) atTop (𝓝 (φ0 * Real.log 2)) :=
    tendsto_const_nhds.congr' heq.symm
  have hdiff := hQ.sub hP
  have hlim := tendsto_nhds_unique hdiff hconst
  rw [fdle_rk0, fdle_rk0, norm_smul, Real.norm_two] at hlim
  have hl2 : Real.log (2 * ‖x0‖) = Real.log 2 + Real.log ‖x0‖ :=
    Real.log_mul two_ne_zero hr.ne'
  rw [hl2] at hlim
  have hb0 : b ≠ 0 := hb.1.ne'
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have key : φ0 * Real.log 2 * b = Real.log 2 := by
    field_simp at hlim
    linarith
  have : (b * φ0 - 1) * Real.log 2 = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · exact absurd h hlog2

/-- Lower bound of the integrand on `[aλ, Kλ]` once `φ` is bounded below on `‖y‖ ≤ 1/4`. -/
lemma fdle_F_lower {ψ : Euc d → ℝ} (s : ℝ) {c0 : ℝ}
    (hc0 : ∀ y : Euc d, ‖y‖ ≤ 1 / 4 → c0 ≤ fdlPhi ψ y) {t : ℝ} (ht : 0 < t) {z : Euc d}
    (hz : ‖t⁻¹ • z‖ ≤ 1 / 4) :
    c0 * (t ^ (-s) / t) ≤ t ^ ((d : ℝ) - s) * fdlPhiScale ψ t z / t := by
  have e : t ^ ((d : ℝ) - s) = t ^ d * t ^ (-s) := by
    rw [sub_eq_add_neg, Real.rpow_add ht, Real.rpow_natCast]
  have hφ := hc0 _ hz
  have eq : t ^ ((d : ℝ) - s) * fdlPhiScale ψ t z / t = t ^ (-s) / t * fdlPhi ψ (t⁻¹ • z) := by
    rw [e]
    unfold fdlPhiScale
    have : t ^ d ≠ 0 := (pow_pos ht d).ne'
    field_simp
  rw [eq, mul_comm]
  exact mul_le_mul_of_nonneg_left hφ (div_nonneg (Real.rpow_nonneg ht.le _) ht.le)

end HRS.MC.FDLE
