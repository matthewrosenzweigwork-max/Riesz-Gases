import HRS.Commutator.Whole.XLIAux38

/-!
# X-LI part 39: the weighted Carleson embedding
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma vol_levelset_finite (hd : 1 ≤ d) {f : 𝔼 → ℝ≥0∞} (hf : Measurable f) (hfi : ∫⁻ y, f y ≠ ⊤)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤) {p : ℝ} (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    volume {x | ENNReal.ofReal t < (c * cmxHLS_Md f x) ^ p} ≠ ⊤ := by
  set θ : ℝ≥0∞ := (ENNReal.ofReal t) ^ (1 / p) / c with hθ
  have hθ0 : θ ≠ 0 := by
    rw [hθ]
    refine (ENNReal.div_pos ?_ hct).ne'
    exact (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 ht) ENNReal.ofReal_ne_top).ne'
  have hθt : θ ≠ ⊤ := by
    rw [hθ]
    exact ENNReal.div_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top) hc0
  have hsub : {x | ENNReal.ofReal t < (c * cmxHLS_Md f x) ^ p} ⊆ {x | θ < cmxHLS_Md f x} := by
    intro x hx
    have hx' : ENNReal.ofReal t < (c * cmxHLS_Md f x) ^ p := hx
    show θ < _
    by_contra hcon
    have h1 := not_lt.1 hcon
    have h2 : c * cmxHLS_Md f x ≤ c * θ := mul_le_mul_right h1 _
    have h3 : c * θ = (ENNReal.ofReal t) ^ (1 / p) := by
      rw [hθ, mul_comm, ENNReal.div_mul_cancel hc0 hct]
    rw [h3] at h2
    have h4 := ENNReal.rpow_le_rpow h2 hp.le
    rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one] at h4
    exact absurd hx' (not_lt.2 h4)
  have hw := cmxHLS_weak hd hf hθ0
  have hS : volume {x | θ < cmxHLS_Md f x} ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top hθ0] at hw
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) hfi (top_le_iff.1 hw)
  exact ne_top_of_le_ne_top hS (measure_mono hsub)

/-- **weighted Carleson embedding** -/
lemma carleson_embed (hd : 1 ≤ d) {K : ℤ → 𝔼 → ℂ} (hK : IsLPRep K) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (F : 𝔼 → ℂ), Measurable F → Integrable F → ∀ B : ℝ≥0∞, B ≠ ⊤ →
      (∀ x, ‖F x‖ₑ ≤ B) → ∀ (f : 𝔼 → ℝ≥0∞), Measurable f → ∫⁻ y, f y ≠ ⊤ →
      ∀ (u : ℤ → 𝔼 → ℝ≥0∞) (c1 : ℝ≥0∞), c1 ≠ ⊤ → c1 ≠ 0 → (∀ j, Measurable (u j)) →
      (∀ j x y, ‖x - y‖ < (2 : ℝ) ^ (-j) → u j x ≤ 2 ^ (d + 1) * u j y) →
      (∀ j y, u j y ≤ c1 * cmxHLS_Md f y) →
      ∀ (p : ℝ), 0 < p → ∀ w : 𝔼 → ℝ≥0∞, Measurable w →
      ∑' j, ∫⁻ x, (‖cv (K j) F x‖ₑ ^ 2 * w x) * u j x ^ p ≤
        C * B ^ 2 * ((2 ^ (d + 1) * c1) ^ p *
          ∫⁻ x, (w x + cmxHLS_Md (cmxHLS_Md w) x) * cmxHLS_Md f x ^ p) := by
  obtain ⟨Ct, hCt, htw⟩ := tent_weighted hd hK
  refine ⟨Ct, hCt, fun F hF hFi B hB hFB f hf hfi u c1 hc1t hc10 hum hu1 hu2 p hp w hw => ?_⟩
  set c : ℝ≥0∞ := 2 ^ (d + 1) * c1 with hc
  have hc0 : c ≠ 0 := mul_ne_zero (by simp) hc10
  have hct : c ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) hc1t
  have hMdf : Measurable (cmxHLS_Md f) := cmxHLS_Md_measurable hf
  set G' : 𝔼 → ℝ≥0∞ := fun y => (c * cmxHLS_Md f y) ^ p with hG'
  have hG'm : Measurable G' := (measurable_const.mul hMdf).pow_const p
  set Et : ℝ → Set 𝔼 := fun t => {y | ENNReal.ofReal t < G' y} with hEt
  have hEtm : ∀ t, MeasurableSet (Et t) := fun t => measurableSet_lt measurable_const hG'm
  have ham : ∀ j, Measurable (fun x => ‖cv (K j) F x‖ₑ ^ 2 * w x) := fun j =>
    (((measurable_cv (hK.lp.meas j) hF).enorm).pow_const 2).mul hw
  have hlayer : ∀ j, ∫⁻ x, (‖cv (K j) F x‖ₑ ^ 2 * w x) * u j x ^ p ≤
      ∫⁻ t in Set.Ioi (0 : ℝ), ∫⁻ x in tent (Et t) j, ‖cv (K j) F x‖ₑ ^ 2 * w x := by
    intro j
    rw [lintegral_mul_layer (ham j) ((hum j).pow_const p)]
    refine lintegral_mono fun t => ?_
    refine lintegral_mono_set ?_
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    intro y hy
    simp only [hEt, Set.mem_setOf_eq, hG']
    have hxy : ‖x - y‖ < (2 : ℝ) ^ (-j) := by rwa [norm_sub_rev]
    calc ENNReal.ofReal t < u j x ^ p := hx
      _ ≤ (2 ^ (d + 1) * u j y) ^ p := ENNReal.rpow_le_rpow (hu1 j x y hxy) hp.le
      _ ≤ (c * cmxHLS_Md f y) ^ p := by
          refine ENNReal.rpow_le_rpow ?_ hp.le
          rw [hc, mul_assoc]
          exact mul_le_mul_right (hu2 j y) _
  have hanti : ∀ j, Antitone (fun t : ℝ => ∫⁻ x in tent (Et t) j, ‖cv (K j) F x‖ₑ ^ 2 * w x) := by
    intro j t t' htt'
    refine lintegral_mono_set ?_
    intro x hx y hy
    have := hx y hy
    simp only [hEt, Set.mem_setOf_eq] at this ⊢
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal htt') this
  have hfin : ∀ t : ℝ, 0 < t → volume (Et t) ≠ ⊤ := fun t ht =>
    vol_levelset_finite hd hf hfi hc0 hct hp ht
  have hlayer2 := lintegral_mul_layer (f := fun x => w x + cmxHLS_Md (cmxHLS_Md w) x) (G := G')
    (hw.add (cmxHLS_Md_measurable (cmxHLS_Md_measurable hw))) hG'm
  calc ∑' j, ∫⁻ x, (‖cv (K j) F x‖ₑ ^ 2 * w x) * u j x ^ p
      ≤ ∑' j, ∫⁻ t in Set.Ioi (0 : ℝ), ∫⁻ x in tent (Et t) j, ‖cv (K j) F x‖ₑ ^ 2 * w x :=
        ENNReal.tsum_le_tsum hlayer
    _ = ∫⁻ t in Set.Ioi (0 : ℝ), ∑' j, ∫⁻ x in tent (Et t) j, ‖cv (K j) F x‖ₑ ^ 2 * w x := by
        rw [lintegral_tsum fun j => (hanti j).measurable.aemeasurable]
    _ ≤ ∫⁻ t in Set.Ioi (0 : ℝ), Ct * B ^ 2 *
          ∫⁻ x in Et t, (w x + cmxHLS_Md (cmxHLS_Md w) x) := by
        refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
        exact htw F hF hFi B hB hFB (Et t) (hEtm t) (hfin t ht) w hw
    _ = Ct * B ^ 2 * ∫⁻ t in Set.Ioi (0 : ℝ), ∫⁻ x in Et t, (w x + cmxHLS_Md (cmxHLS_Md w) x) := by
        rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top hCt (ENNReal.pow_ne_top hB))]
    _ = Ct * B ^ 2 * ∫⁻ x, (w x + cmxHLS_Md (cmxHLS_Md w) x) * G' x := by
        rw [hlayer2]
    _ = _ := by
        have hm : Measurable (fun x => (w x + cmxHLS_Md (cmxHLS_Md w) x) * cmxHLS_Md f x ^ p) :=
          (hw.add (cmxHLS_Md_measurable (cmxHLS_Md_measurable hw))).mul (hMdf.pow_const p)
        have : ∫⁻ x, (w x + cmxHLS_Md (cmxHLS_Md w) x) * G' x =
            c ^ p * ∫⁻ x, (w x + cmxHLS_Md (cmxHLS_Md w) x) * cmxHLS_Md f x ^ p := by
          rw [← lintegral_const_mul _ hm]
          refine lintegral_congr fun x => ?_
          simp only [hG']
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
          ring
        rw [this]

end HRS.Commutator.Whole.XLI
