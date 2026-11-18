import HRS.Appendix.FDL

/-!
# Packet FDLE, auxiliary facts on the profile `φ = ψ * ψ` (Lemma D.3(i), (iv)).

Helpers only; names carry the prefix `fdle_`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.MC.FDLE

open HRS

variable {d : ℕ}

lemma fdle_psi_cont {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) : Continuous ψ :=
  hψ.smooth.continuous

lemma fdle_psi_compact {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) : HasCompactSupport ψ := by
  show IsCompact (tsupport ψ)
  exact (isCompact_closedBall (0 : Euc d) (1 / 2)).of_isClosed_subset (isClosed_tsupport ψ)
    (hψ.support.trans Metric.ball_subset_closedBall)

lemma fdle_phi_apply {ψ : Euc d → ℝ} (x : Euc d) : fdlPhi ψ x = ∫ t, ψ t * ψ (x - t) := by
  unfold fdlPhi
  rw [convolution_def]
  rfl

/-- Integrability of `t ↦ ψ t * g t` for continuous `g`. -/
lemma fdle_int_mul {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (g : Euc d → ℝ) (hg : Continuous g) :
    Integrable (fun t => ψ t * g t) := by
  apply Continuous.integrable_of_hasCompactSupport ((fdle_psi_cont hψ).mul hg)
  exact (fdle_psi_compact hψ).mul_right

lemma fdle_phi_cont {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) : Continuous (fdlPhi ψ) := by
  unfold fdlPhi
  exact HasCompactSupport.continuous_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    (fdle_psi_compact hψ) (fdle_psi_cont hψ).locallyIntegrable (fdle_psi_cont hψ)

lemma fdle_phi_nonneg {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (x : Euc d) : 0 ≤ fdlPhi ψ x := by
  rw [fdle_phi_apply]
  exact integral_nonneg fun t => mul_nonneg (hψ.nonneg t) (hψ.nonneg _)

lemma fdle_phi_eq_zero {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {x : Euc d} (hx : 1 ≤ ‖x‖) :
    fdlPhi ψ x = 0 := by
  rw [fdle_phi_apply]
  have hzero : ∀ t : Euc d, ψ t * ψ (x - t) = 0 := by
    intro t
    by_cases h1 : ψ t = 0
    · simp [h1]
    by_cases h2 : ψ (x - t) = 0
    · simp [h2]
    exfalso
    have a1 : ‖t‖ < 1 / 2 :=
      mem_ball_zero_iff.mp (hψ.support (subset_tsupport _ (Function.mem_support.mpr h1)))
    have a2 : ‖x - t‖ < 1 / 2 :=
      mem_ball_zero_iff.mp (hψ.support (subset_tsupport _ (Function.mem_support.mpr h2)))
    have h := norm_add_le t (x - t)
    rw [show t + (x - t) = x by abel] at h
    linarith
  simp [hzero]

lemma fdle_phi_le_phi0 {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (y : Euc d) :
    fdlPhi ψ y ≤ fdlPhi ψ 0 := by
  have hsq : ∫ t, ψ t * ψ t = fdlPhi ψ 0 := by
    rw [fdle_phi_apply]
    congr 1
    funext t
    rw [zero_sub, hψ.radial (-t) t (norm_neg t)]
  rw [← hsq, fdle_phi_apply]
  have hI1 : Integrable (fun t => ψ t * ψ t) := fdle_int_mul hψ ψ (fdle_psi_cont hψ)
  have hI2 : Integrable (fun t => ψ t * ψ (y - t)) :=
    fdle_int_mul hψ (fun t => ψ (y - t)) ((fdle_psi_cont hψ).comp (continuous_const.sub continuous_id))
  have hI3 : Integrable (fun t => ψ (y - t) * ψ (y - t)) := hI1.comp_sub_left y
  have hmono : ∫ t, 2 * (ψ t * ψ (y - t)) ≤ ∫ t, (ψ t * ψ t + ψ (y - t) * ψ (y - t)) :=
    integral_mono (hI2.const_mul 2) (hI1.add hI3)
      (fun t => by nlinarith [sq_nonneg (ψ t - ψ (y - t))])
  have hs := integral_sub_left_eq_self (fun t => ψ t * ψ t) volume y
  rw [integral_const_mul, integral_add hI1 hI3, hs] at hmono
  linarith

lemma fdle_phi_pos {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {y : Euc d} (hy : ‖y‖ ≤ 1 / 4) :
    0 < fdlPhi ψ y := by
  rw [fdle_phi_apply]
  have hc : Continuous (fun t => ψ t * ψ (y - t)) :=
    (fdle_psi_cont hψ).mul ((fdle_psi_cont hψ).comp (continuous_const.sub continuous_id))
  have hnn : 0 ≤ fun t => ψ t * ψ (y - t) := fun t => mul_nonneg (hψ.nonneg t) (hψ.nonneg _)
  have hint : Integrable (fun t => ψ t * ψ (y - t)) :=
    fdle_int_mul hψ (fun t => ψ (y - t)) ((fdle_psi_cont hψ).comp (continuous_const.sub continuous_id))
  rw [integral_pos_iff_support_of_nonneg hnn hint]
  have hopen : IsOpen (Function.support fun t => ψ t * ψ (y - t)) :=
    isOpen_ne_fun hc continuous_const
  set p : Euc d := (1 / 2 : ℝ) • y with hp
  have hpn : ‖p‖ < 1 / 4 := by
    rw [hp, norm_smul]
    norm_num
    linarith
  have hyp : y - p = p := by rw [hp]; module
  have hne : p ∈ Function.support fun t => ψ t * ψ (y - t) := by
    rw [Function.mem_support, hyp]
    exact mul_ne_zero (hψ.pos p hpn).ne' (hψ.pos p hpn).ne'
  exact hopen.measure_pos volume ⟨p, hne⟩

lemma fdle_phi_min {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) :
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ y : Euc d, ‖y‖ ≤ 1 / 4 → c0 ≤ fdlPhi ψ y := by
  obtain ⟨y0, hy0, hmin⟩ := (isCompact_closedBall (0 : Euc d) (1 / 4)).exists_isMinOn
    ⟨0, by simp⟩ (fdle_phi_cont hψ).continuousOn
  have hy0' : ‖y0‖ ≤ 1 / 4 := by simpa using hy0
  refine ⟨fdlPhi ψ y0, fdle_phi_pos hψ hy0', fun y hy => ?_⟩
  exact isMinOn_iff.mp hmin y (by simpa using hy)

lemma fdle_phi_integrable {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) :
    Integrable (fdlPhi ψ) := by
  apply (fdle_phi_cont hψ).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) 1)
  intro y hy
  apply fdle_phi_eq_zero hψ
  simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hy
  exact hy.le

/-- `φ_t` is nonnegative. -/
lemma fdle_phiScale_nonneg {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {t : ℝ} (ht : 0 < t)
    (x : Euc d) : 0 ≤ fdlPhiScale ψ t x :=
  mul_nonneg (inv_nonneg.2 (pow_nonneg ht.le _)) (fdle_phi_nonneg hψ _)

/-- `φ_t(x) = 0` when `t ≤ ‖x‖`. -/
lemma fdle_phiScale_eq_zero {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {t : ℝ} (ht : 0 < t)
    {z : Euc d} (h : t ≤ ‖z‖) : fdlPhiScale ψ t z = 0 := by
  unfold fdlPhiScale
  have h1 : 1 ≤ ‖t⁻¹ • z‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le)]
    rw [← div_eq_inv_mul, le_div_iff₀ ht]
    linarith
  rw [fdle_phi_eq_zero hψ h1, mul_zero]

lemma fdle_phiScale_integrable {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x => fdlPhiScale ψ t x) := by
  unfold fdlPhiScale
  exact ((fdle_phi_integrable hψ).comp_smul (inv_ne_zero ht.ne')).const_mul _

/-- Scaling: `∫ φ_t = ∫ φ` for `t > 0`. -/
lemma fdle_phiScale_integral {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {t : ℝ} (ht : 0 < t) :
    ∫ x, fdlPhiScale ψ t x = ∫ x, fdlPhi ψ x := by
  unfold fdlPhiScale
  rw [integral_const_mul]
  have h := Measure.integral_comp_inv_smul (volume : Measure (Euc d)) (fdlPhi ψ) t
  rw [h, finrank_euclideanSpace_fin, abs_of_pos (pow_pos ht d), smul_eq_mul]
  have : t ^ d ≠ 0 := (pow_pos ht d).ne'
  field_simp

end HRS.MC.FDLE
