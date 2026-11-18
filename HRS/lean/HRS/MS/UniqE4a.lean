import HRS.MS.UniqE3i
import HRS.MS.UniqN0f
import HRS.MS.UniqNDefs

/-!
# E4 of `UniqPlan.md`, part 1: weak-gradient identity for `C¹_c` tests

* `e4_moll_unif` : `η_δ * f → f` uniformly for `f` continuous with compact support.
* `e4_weak_c1`   : `IsWeakGrad u v` extends from `C_c^∞` to `C¹_c` test functions.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.UniqE4

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqM1 HRS.MS.UniqM2
  HRS.MS.UniqM3 HRS.MS.UniqT3 HRS.MS.UniqC3 HRS.MS.UniqE3

variable {d : ℕ}

theorem e4_integral_eta_sub {ε : ℝ} (hε : 0 < ε) (x : Euc d) : ∫ y, eta d ε (x - y) = 1 := by
  rw [integral_sub_left_eq_self (fun y => eta d ε y) volume x, integral_eta hε]

theorem e4_eta_integrable {ε : ℝ} (hε : 0 < ε) (x : Euc d) :
    Integrable (fun y => eta d ε (x - y)) volume :=
  (eta_contDiff.continuous.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
    ((eta_hasCompactSupport hε).comp_homeomorph (Homeomorph.subLeft x))

/-- `η_δ * f → f` uniformly, for `f` continuous with compact support. -/
theorem e4_moll_unif {f : Euc d → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) {a : ℝ}
    (ha : 0 < a) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ δ : ℝ, 0 < δ → δ < δ0 → ∀ x : Euc d, |moll d δ f x - f x| ≤ a := by
  have hu : UniformContinuous f :=
    hf.uniformContinuous_of_tendsto_cocompact hfc.is_zero_at_infty
  obtain ⟨δ0, hδ0, h⟩ := Metric.uniformContinuous_iff.1 hu a ha
  refine ⟨δ0, hδ0, fun δ hδ hδδ0 x => ?_⟩
  have hi1 := e4_eta_integrable hδ x
  have hi2 : Integrable (fun y => eta d δ (x - y) * f y) volume :=
    m3_kernel_integrable hδ x hf.locallyIntegrable
  have hi3 : Integrable (fun y => eta d δ (x - y) * f x) volume := hi1.mul_const _
  have e : moll d δ f x - f x = ∫ y, (eta d δ (x - y) * f y - eta d δ (x - y) * f x) := by
    rw [integral_sub hi2 hi3, integral_mul_const, e4_integral_eta_sub hδ, one_mul]
    rfl
  rw [e, ← Real.norm_eq_abs]
  have hb : Integrable (fun y => a * eta d δ (x - y)) volume := hi1.const_mul a
  refine (norm_integral_le_of_norm_le hb (Eventually.of_forall fun y => ?_)).trans ?_
  · by_cases hy : eta d δ (x - y) = 0
    · simp [hy]
    · have hmem : x - y ∈ Function.support (eta d δ) := Function.mem_support.2 hy
      have hball : ‖x - y‖ < δ := mem_ball_zero_iff.1 (eta_support hδ hmem)
      have hd : dist y x < δ0 := by
        rw [dist_eq_norm, norm_sub_rev]; linarith
      have := h hd
      rw [Real.dist_eq] at this
      have he : 0 ≤ eta d δ (x - y) := eta_nonneg hδ _
      rw [← mul_sub, norm_mul, Real.norm_eq_abs, abs_of_nonneg he, Real.norm_eq_abs]
      nlinarith
  · rw [integral_const_mul, e4_integral_eta_sub hδ]; simp

theorem e4_D1_mem {θ : Euc d → ℝ} (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ) (j : Fin d) :
    Continuous (D1 j θ) ∧ HasCompactSupport (D1 j θ) :=
  ⟨e3_continuous_D1 hθ j, D1_supp hθc j⟩

/-- A function vanishing outside `closedBall 0 R0` has mollification vanishing outside `closedBall 0 (R0+1)`. -/
theorem e4_moll_zero_outside {δ R0 : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {f : Euc d → ℝ}
    (hf : ∀ y, f y ≠ 0 → ‖y‖ ≤ R0) {x : Euc d} (hx : R0 + 1 < ‖x‖) : moll d δ f x = 0 := by
  unfold moll
  have : ∀ y, eta d δ (x - y) * f y = 0 := by
    intro y
    by_cases hy : f y = 0
    · simp [hy]
    · have h1 : ‖y‖ ≤ R0 := hf y hy
      have : eta d δ (x - y) = 0 := by
        by_contra hne
        have := eta_support hδ (Function.mem_support.2 hne)
        rw [mem_ball_zero_iff] at this
        have : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
          have := norm_add_le (x - y) y
          simpa using this
        linarith
      rw [this, zero_mul]
  simp [this]

theorem e4_D1_ne_zero {θ : Euc d → ℝ} {R0 : ℝ} (hθ : ∀ y, θ y ≠ 0 → ‖y‖ ≤ R0) {j : Fin d}
    {y : Euc d} (hy : D1 j θ y ≠ 0) : ‖y‖ ≤ R0 := by
  by_contra hcon
  apply hy
  have hz : ∀ᶠ x in 𝓝 y, θ x = 0 := by
    have : IsOpen {x : Euc d | R0 < ‖x‖} := isOpen_lt continuous_const continuous_norm
    filter_upwards [this.mem_nhds (not_le.1 hcon)] with x hx
    by_contra hne
    exact absurd (hθ x hne) (not_le.2 hx)
  have : fderiv ℝ θ y = 0 := by
    rw [(show θ =ᶠ[𝓝 y] 0 from hz).fderiv_eq]; simp
  simp [D1, this]

/-- The weak-gradient identity for `C¹_c` test functions. -/
theorem e4_weak_c1 {u : Euc d → ℝ} {v : Euc d → Euc d} (hu : LocallyIntegrable u volume)
    (hv : IsWeakGrad u v) (j : Fin d) (hvj : LocallyIntegrable (fun x => v x j) volume)
    {θ : Euc d → ℝ} (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ) :
    ∫ x, u x * D1 j θ x = - ∫ x, v x j * θ x := by
  obtain ⟨R0, hR0⟩ := hθc.isCompact.isBounded.subset_closedBall (0 : Euc d)
  have hθR : ∀ y, θ y ≠ 0 → ‖y‖ ≤ R0 := fun y hy => by
    simpa using hR0 (subset_tsupport θ hy)
  obtain ⟨hDc, hDcs⟩ := e4_D1_mem hθ hθc j
  set Ω : Set (Euc d) := closedBall (0 : Euc d) (R0 + 1) with hΩ
  have hΩc : IsCompact Ω := isCompact_closedBall _ _
  have hΩm : MeasurableSet Ω := measurableSet_closedBall
  have hU : IntegrableOn (fun x => ‖u x‖) Ω volume := (hu.integrableOn_isCompact hΩc).norm
  have hV : IntegrableOn (fun x => ‖v x j‖) Ω volume := (hvj.integrableOn_isCompact hΩc).norm
  set U : ℝ := ∫ x in Ω, ‖u x‖ with hUdef
  set V : ℝ := ∫ x in Ω, ‖v x j‖ with hVdef
  have hU0 : 0 ≤ U := integral_nonneg fun x => norm_nonneg _
  have hV0 : 0 ≤ V := integral_nonneg fun x => norm_nonneg _
  have hI1 : Integrable (fun x => u x * D1 j θ x) volume := e3_integrable_mul hu hDc hDcs
  have hI2 : Integrable (fun x => v x j * θ x) volume :=
    e3_integrable_mul hvj hθ.continuous hθc
  have key : ∀ a : ℝ, 0 < a →
      |(∫ x, u x * D1 j θ x) + ∫ x, v x j * θ x| ≤ a * (U + V) := by
    intro a ha
    obtain ⟨δ1, hδ1, h1⟩ := e4_moll_unif hθ.continuous hθc ha
    obtain ⟨δ2, hδ2, h2⟩ := e4_moll_unif hDc hDcs ha
    set δ : ℝ := min (min δ1 δ2) 1 / 2 with hδdef
    have hδ0 : 0 < δ := by
      have : 0 < min (min δ1 δ2) 1 := lt_min (lt_min hδ1 hδ2) one_pos
      positivity
    have hδ1' : δ < δ1 := by
      have : min (min δ1 δ2) 1 ≤ δ1 := (min_le_left _ _).trans (min_le_left _ _)
      have h0 : 0 < min (min δ1 δ2) 1 := lt_min (lt_min hδ1 hδ2) one_pos
      linarith
    have hδ2' : δ < δ2 := by
      have : min (min δ1 δ2) 1 ≤ δ2 := (min_le_left _ _).trans (min_le_right _ _)
      have h0 : 0 < min (min δ1 δ2) 1 := lt_min (lt_min hδ1 hδ2) one_pos
      linarith
    have hδle : δ ≤ 1 := by
      have : min (min δ1 δ2) 1 ≤ 1 := min_le_right _ _
      have h0 : 0 < min (min δ1 δ2) 1 := lt_min (lt_min hδ1 hδ2) one_pos
      linarith
    set θδ : Euc d → ℝ := moll d δ θ with hθδ
    have hθδs : ContDiff ℝ ∞ θδ := moll_contDiff hδ0 hθ.continuous.locallyIntegrable
    have hθδc : HasCompactSupport θδ := e3_moll_hasCompactSupport hδ0 hθc
    have hD : D1 j θδ = moll d δ (D1 j θ) := e3_D1_moll hδ0 hθ hθc j
    have hweak := hv.2 θδ hθδs hθδc j
    have hDδc : Continuous (D1 j θδ) := e3_continuous_D1 (hθδs.of_le (by simp)) j
    have hDδcs : HasCompactSupport (D1 j θδ) := D1_supp hθδc j
    have hI3 : Integrable (fun x => u x * D1 j θδ x) volume := e3_integrable_mul hu hDδc hDδcs
    have hI4 : Integrable (fun x => v x j * θδ x) volume :=
      e3_integrable_mul hvj hθδs.continuous hθδc
    have hweak' : ∫ x, u x * D1 j θδ x = - ∫ x, v x j * θδ x := hweak
    have eq1 : (∫ x, u x * D1 j θ x) + ∫ x, v x j * θ x =
        (∫ x, u x * (D1 j θ x - D1 j θδ x)) + ∫ x, v x j * (θ x - θδ x) := by
      simp_rw [mul_sub]
      rw [integral_sub hI1 hI3, integral_sub hI2 hI4]
      linarith
    have b1 : |∫ x, u x * (D1 j θ x - D1 j θδ x)| ≤ a * U := by
      rw [← Real.norm_eq_abs]
      have hb : Integrable (Ω.indicator (fun x => a * ‖u x‖)) volume :=
        (integrable_indicator_iff hΩm).2 (hU.const_mul a)
      refine (norm_integral_le_of_norm_le hb (Eventually.of_forall fun x => ?_)).trans ?_
      · by_cases hx : x ∈ Ω
        · rw [Set.indicator_of_mem hx, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, ← Real.norm_eq_abs]
          have := h2 δ hδ0 hδ2' x
          rw [hD]
          calc ‖u x‖ * |D1 j θ x - moll d δ (D1 j θ) x| ≤ ‖u x‖ * a :=
                mul_le_mul_of_nonneg_left (by rw [abs_sub_comm]; exact this) (norm_nonneg _)
            _ = a * ‖u x‖ := mul_comm _ _
        · rw [Set.indicator_of_notMem hx]
          have hxn : R0 + 1 < ‖x‖ := by
            by_contra hcon
            exact hx (by rw [hΩ, mem_closedBall_zero_iff]; linarith [not_lt.1 hcon])
          have e1 : D1 j θ x = 0 := by
            by_contra hne
            have := e4_D1_ne_zero hθR hne
            linarith
          have e2 : D1 j θδ x = 0 := by
            rw [hD]; exact e4_moll_zero_outside hδ0 hδle (fun y hy => e4_D1_ne_zero hθR hy) hxn
          simp [e1, e2]
      · rw [integral_indicator hΩm, integral_const_mul]
    have b2 : |∫ x, v x j * (θ x - θδ x)| ≤ a * V := by
      rw [← Real.norm_eq_abs]
      have hb : Integrable (Ω.indicator (fun x => a * ‖v x j‖)) volume :=
        (integrable_indicator_iff hΩm).2 (hV.const_mul a)
      refine (norm_integral_le_of_norm_le hb (Eventually.of_forall fun x => ?_)).trans ?_
      · by_cases hx : x ∈ Ω
        · rw [Set.indicator_of_mem hx, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, ← Real.norm_eq_abs]
          have := h1 δ hδ0 hδ1' x
          calc ‖v x j‖ * |θ x - θδ x| ≤ ‖v x j‖ * a :=
                mul_le_mul_of_nonneg_left (by rwa [abs_sub_comm]) (norm_nonneg _)
            _ = a * ‖v x j‖ := mul_comm _ _
        · rw [Set.indicator_of_notMem hx]
          have hxn : R0 + 1 < ‖x‖ := by
            by_contra hcon
            exact hx (by rw [hΩ, mem_closedBall_zero_iff]; linarith [not_lt.1 hcon])
          have e1 : θ x = 0 := by
            by_contra hne
            have := hθR x hne
            linarith
          have e2 : θδ x = 0 := e4_moll_zero_outside hδ0 hδle hθR hxn
          simp [e1, e2]
      · rw [integral_indicator hΩm, integral_const_mul]
    rw [eq1]
    calc _ ≤ |∫ x, u x * (D1 j θ x - D1 j θδ x)| + |∫ x, v x j * (θ x - θδ x)| := abs_add_le _ _
      _ ≤ a * U + a * V := add_le_add b1 b2
      _ = _ := by ring
  have h0 : |(∫ x, u x * D1 j θ x) + ∫ x, v x j * θ x| ≤ 0 := by
    refine le_of_forall_pos_le_add fun a ha => ?_
    have := key (a / (U + V + 1)) (by positivity)
    calc _ ≤ a / (U + V + 1) * (U + V) := this
      _ ≤ a := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
      _ = 0 + a := by ring
  have : (∫ x, u x * D1 j θ x) + ∫ x, v x j * θ x = 0 := abs_nonpos_iff.1 h0
  linarith

end HRS.MS.UniqE4
