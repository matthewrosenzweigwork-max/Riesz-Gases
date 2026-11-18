import Mathlib

/-!
# Packet N5, helper 4: recovering a bounded drift from a continuous process (pure real analysis)

For a continuous `Z : ℝ → ℝ` (vanishing on `(-∞, 0]`) whose increments on `[0, T₀]` are `∫ β` with
`0 ≤ β ≤ hi ≤ M₀`, the backward difference quotient limit `n5_dq Z` is a *measurable-by-construction*
bounded density of `Z` on `[0, T₀]`: either `β` is integrable on `[0, T₀]` and `n5_dq Z = β` a.e.
(Lebesgue differentiation), or `β` is not integrable and then `Z ≡ 0` on `[0, T₀]` (the Bochner integral
of a non-integrable function being `0`) and `n5_dq Z = 0`.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace HRS.MC.CepN5

/-- Backward difference quotient limit (limsup). -/
def n5_dq (Z : ℝ → ℝ) (s : ℝ) : ℝ :=
  limsup (fun n : ℕ => ((n : ℝ) + 1) * (Z s - Z (s - 1 / ((n : ℝ) + 1)))) atTop

/-- Clipping to `[0, M₀]`. -/
def n5_bcl (M₀ d : ℝ) : ℝ := max 0 (min d M₀)

theorem n5_bcl_nonneg (M₀ d : ℝ) : 0 ≤ n5_bcl M₀ d := le_max_left _ _

theorem n5_bcl_le {M₀ : ℝ} (hM : 0 ≤ M₀) (d : ℝ) : n5_bcl M₀ d ≤ M₀ :=
  max_le hM (min_le_right _ _)

theorem n5_bcl_of_mem {M₀ d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ M₀) : n5_bcl M₀ d = d := by
  unfold n5_bcl; rw [min_eq_left h1, max_eq_right h0]

theorem n5_bcl_zero {M₀ : ℝ} (hM : 0 ≤ M₀) : n5_bcl M₀ 0 = 0 := by
  unfold n5_bcl; rw [min_eq_left hM, max_self]

theorem n5_dq_of_zero {Z : ℝ → ℝ} {T₀ s : ℝ} (hZ : ∀ u ∈ Icc 0 T₀, Z u = 0) (hneg : ∀ u ≤ 0, Z u = 0)
    (hs : s ∈ Icc 0 T₀) : n5_dq Z s = 0 := by
  unfold n5_dq
  have : ∀ n : ℕ, ((n : ℝ) + 1) * (Z s - Z (s - 1 / ((n : ℝ) + 1))) = 0 := by
    intro n
    have h1 : Z s = 0 := hZ s hs
    have h2 : Z (s - 1 / ((n : ℝ) + 1)) = 0 := by
      have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      by_cases h : 0 ≤ s - 1 / ((n : ℝ) + 1)
      · exact hZ _ ⟨h, by linarith [hs.2]⟩
      · exact hneg _ (by linarith)
    rw [h1, h2]; simp
  simp only [this]
  exact limsup_const 0

theorem n5_dq_of_hasDerivAt {Z F : ℝ → ℝ} {T₀ x β : ℝ} (hx : x ∈ Ioo 0 T₀)
    (hF : HasDerivAt F β x) (hZF : ∀ u ∈ Icc 0 T₀, Z u = F u) : n5_dq Z x = β := by
  unfold n5_dq
  apply Tendsto.limsup_eq
  have h1 := hF.tendsto_slope_zero
  have h2 : Tendsto (fun n : ℕ => -(1 / ((n : ℝ) + 1))) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      simpa using this.neg
    · have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      simpa using this.ne'
  have h3 := h1.comp h2
  refine h3.congr' ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / x)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hxpos : 0 < x := hx.1
  have hn1 : (1 : ℝ) / x < (n : ℝ) + 1 := by
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hh : 1 / ((n : ℝ) + 1) < x := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hxpos] at hn1
    linarith
  have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have e1 : Z x = F x := hZF x ⟨hxpos.le, hx.2.le⟩
  have e2 : Z (x - 1 / ((n : ℝ) + 1)) = F (x - 1 / ((n : ℝ) + 1)) :=
    hZF _ ⟨by linarith, by linarith [hx.2]⟩
  simp only [Function.comp, smul_eq_mul, e1, e2]
  have : (n : ℝ) + 1 ≠ 0 := by positivity
  rw [← sub_eq_add_neg]
  field_simp
  ring

/-- The recovered density: on `[0, T₀]`, `Z s = ∫_{[0,s]} clip(n5_dq Z)`, and `clip(n5_dq Z)` lies in
`[0, hi]` almost everywhere. -/
theorem n5_Q {Z β hi : ℝ → ℝ} {T₀ M₀ : ℝ} (hT₀ : 0 ≤ T₀) (hM₀ : 0 ≤ M₀) (hZ0 : Z 0 = 0)
    (hneg : ∀ u ≤ 0, Z u = 0)
    (hZβ : ∀ s t, 0 ≤ s → s ≤ t → t ≤ T₀ → Z t - Z s = ∫ u in s..t, β u)
    (hβ : ∀ u ∈ Icc 0 T₀, 0 ≤ β u ∧ β u ≤ hi u) (hhi : ∀ u ∈ Icc 0 T₀, hi u ≤ M₀) :
    (∀ s ∈ Icc 0 T₀, Z s = ∫ u in Icc 0 s, n5_bcl M₀ (n5_dq Z u)) ∧
    (∀ᵐ u, u ∈ Icc 0 T₀ → n5_bcl M₀ (n5_dq Z u) ≤ hi u) := by
  by_cases hJ : IntervalIntegrable β volume 0 T₀
  · -- integrable case: Lebesgue differentiation
    have hZF : ∀ u ∈ Icc 0 T₀, Z u = ∫ t in (0 : ℝ)..u, β t := by
      intro u hu
      have := hZβ 0 u le_rfl hu.1 hu.2
      rwa [hZ0, sub_zero] at this
    have hae : ∀ᵐ x, x ∈ Icc 0 T₀ → n5_bcl M₀ (n5_dq Z x) = β x := by
      have hd := hJ.ae_hasDerivAt_integral
      have h0 : ∀ᵐ x : ℝ, x ≠ 0 := by simp [ae_iff, measure_singleton]
      have h1 : ∀ᵐ x : ℝ, x ≠ T₀ := by simp [ae_iff, measure_singleton]
      filter_upwards [hd, h0, h1] with x hx hx0 hxT hxI
      have hxo : x ∈ Ioo 0 T₀ := ⟨lt_of_le_of_ne hxI.1 (Ne.symm hx0), lt_of_le_of_ne hxI.2 hxT⟩
      have hdx := hx (by rw [uIcc_of_le hT₀]; exact hxI) 0 (by rw [uIcc_of_le hT₀]; exact ⟨le_rfl, hT₀⟩)
      rw [n5_dq_of_hasDerivAt hxo hdx hZF]
      exact n5_bcl_of_mem (hβ x hxI).1 ((hβ x hxI).2.trans (hhi x hxI))
    refine ⟨fun s hs => ?_, ?_⟩
    · rw [hZF s hs, intervalIntegral.integral_of_le hs.1, ← integral_Icc_eq_integral_Ioc]
      refine setIntegral_congr_ae measurableSet_Icc ?_
      filter_upwards [hae] with x hx hxs
      exact (hx ⟨hxs.1, hxs.2.trans hs.2⟩).symm
    · filter_upwards [hae] with x hx hxI
      rw [hx hxI]; exact (hβ x hxI).2
  · -- non-integrable case: `Z ≡ 0` on `[0, T₀]`
    have hT : Z T₀ = 0 := by
      have := hZβ 0 T₀ le_rfl hT₀ le_rfl
      rwa [hZ0, intervalIntegral.integral_undef hJ, sub_zero] at this
    have hzero : ∀ s ∈ Icc 0 T₀, Z s = 0 := by
      intro s hs
      by_contra hne
      have h1 : IntervalIntegrable β volume 0 s := by
        by_contra h
        have := hZβ 0 s le_rfl hs.1 hs.2
        rw [intervalIntegral.integral_undef h, hZ0] at this
        exact hne (by linarith)
      have h2 : IntervalIntegrable β volume s T₀ := by
        by_contra h
        have := hZβ s T₀ hs.1 hs.2 le_rfl
        rw [intervalIntegral.integral_undef h, hT] at this
        exact hne (by linarith)
      exact hJ (h1.trans h2)
    have hdq : ∀ u ∈ Icc 0 T₀, n5_dq Z u = 0 := fun u hu => n5_dq_of_zero hzero hneg hu
    refine ⟨fun s hs => ?_, ?_⟩
    · rw [hzero s hs]
      have : ∀ u ∈ Icc 0 s, n5_bcl M₀ (n5_dq Z u) = 0 := fun u hu => by
        rw [hdq u ⟨hu.1, hu.2.trans hs.2⟩, n5_bcl_zero hM₀]
      rw [setIntegral_congr_fun measurableSet_Icc this]
      simp
    · refine Eventually.of_forall fun u hu => ?_
      rw [hdq u hu, n5_bcl_zero hM₀]
      exact (hβ u hu).1.trans (hβ u hu).2

end HRS.MC.CepN5
