import HRS.Commutator.Whole.XLIAux25

/-!
# X-LI part 26: the pair estimate `‖QQ‖ ≲ ‖J^α φ‖_p ‖ψ‖_q` for all admissible exponents
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- the Carleson-type endpoint estimate (case `p = ∞`) for the exponent `r` -/
def E4At (α r : ℝ) : Prop :=
  ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ φ ψ : SchwartzMap 𝔼 ℂ,
    ∫⁻ x, QQ α φ ψ x ^ (r / 2) ≤
      C * ((eLpNorm (⇑(Fm α φ)) ⊤ volume) ^ r * ∫⁻ x, ‖ψ x‖ₑ ^ r)

lemma toReal_exps {p q r : ℝ≥0∞} (h : p⁻¹ + q⁻¹ = r⁻¹) (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hr : r ≠ ⊤)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hr0 : r ≠ 0) :
    1 / p.toReal + 1 / q.toReal = 1 / r.toReal := by
  have h1 := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add (ENNReal.inv_ne_top.2 hp0) (ENNReal.inv_ne_top.2 hq0),
    ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_inv] at h1
  simpa [one_div] using h1

section Pair

variable (α : ℝ)

lemma BILIN_qinf (hd : 1 ≤ d) {r : ℝ} (hr : 1 < r)
    (hE : E1At (fun j => dK (Ths (-α) : ℤ → 𝔼 → ℂ) j) (r / 2)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (φ ψ : SchwartzMap 𝔼 ℂ) (B : ℝ≥0∞), (∀ y, ‖ψ y‖ₑ ≤ B) →
      ∫⁻ x, QQ α φ ψ x ^ (r / 2) ≤ C * (B ^ r * ∫⁻ x, ‖Fm α φ x‖ₑ ^ r) := by
  obtain ⟨CE, hCE⟩ := hE
  have hr0 : 0 < r := by linarith
  set s : ℝ := r / 2 with hs
  have hs0 : 0 < s := by positivity
  set c4 : ℝ≥0∞ := 4 * KP d with hc4
  have hc4ne : c4 ≠ ⊤ := ENNReal.mul_ne_top (by simp) KP_ne_top
  refine ⟨c4 ^ (2 * s) * (CE : ℝ≥0∞), ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) hc4ne) (by simp), fun φ ψ B hB => ?_⟩
  set X : 𝔼 → ℝ≥0∞ := sqS (fun j => Fj α φ j) with hX
  have hMB : ∀ x, Mx ψ x ≤ B := fun x => Md_le_of_le hB x
  have hpt : ∀ x, QQ α φ ψ x ^ s ≤ c4 ^ (2 * s) * (B ^ r * X x ^ s) := by
    intro x
    have h1 := ENNReal.rpow_le_rpow (QQ_le α φ ψ x) hs0.le
    refine h1.trans ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ hs0.le, hc4]
    have e1 : ((4 * (KP d * Mx ψ x)) ^ 2) ^ s = (4 * KP d) ^ (2 * s) * Mx ψ x ^ (2 * s) := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      rw [show (4 * (KP d * Mx ψ x)) = (4 * KP d) * Mx ψ x by ring]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
      norm_num
    rw [e1]
    have e2 : Mx ψ x ^ (2 * s) ≤ B ^ r := by
      have : 2 * s = r := by rw [hs]; ring
      rw [this]
      exact ENNReal.rpow_le_rpow (hMB x) hr0.le
    calc X x ^ s * ((4 * KP d) ^ (2 * s) * Mx ψ x ^ (2 * s))
        ≤ X x ^ s * ((4 * KP d) ^ (2 * s) * B ^ r) := by gcongr
      _ = _ := by ring
  have hFjm : ∀ j, Measurable (Fj α φ j) := fun j => Fj_meas α φ j
  have hXm : Measurable X := sqS_measurable hFjm
  calc ∫⁻ x, QQ α φ ψ x ^ s ≤ ∫⁻ x, c4 ^ (2 * s) * (B ^ r * X x ^ s) := lintegral_mono hpt
    _ = c4 ^ (2 * s) * (B ^ r * ∫⁻ x, X x ^ s) := by
        have hm1 : Measurable (fun x => B ^ r * X x ^ s) := measurable_const.mul (hXm.pow_const s)
        have hm2 : Measurable (fun x => X x ^ s) := hXm.pow_const s
        rw [lintegral_const_mul'' (c4 ^ (2 * s)) hm1.aemeasurable,
          lintegral_const_mul'' (B ^ r) hm2.aemeasurable]
    _ ≤ c4 ^ (2 * s) * (B ^ r * (CE * ∫⁻ x, ‖Fm α φ x‖ₑ ^ r)) := by
        refine mul_le_mul_right (mul_le_mul_right ?_ _) _
        obtain ⟨Bf, hBf, hBfd⟩ := sch_enorm_bdd (Fm α φ)
        have := hCE (⇑(Fm α φ)) (Fm α φ).continuous.measurable (Fm α φ).integrable Bf hBf hBfd
        have e : 2 * (r / 2) = r := by ring
        rw [e] at this
        exact this
    _ = (c4 ^ (2 * s) * (CE : ℝ≥0∞)) * (B ^ r * ∫⁻ x, ‖Fm α φ x‖ₑ ^ r) := by ring

/-- **the pair estimate** for all admissible exponents -/
lemma PAIR (hd : 1 ≤ d) {r p q : ℝ≥0∞} (hr : 1 < r) (hr' : r < ⊤) (hp : 1 < p) (hq : 1 < q)
    (h : p⁻¹ + q⁻¹ = r⁻¹)
    (hE : ∀ u : ℝ, 1 < u → E1At (fun j => dK (Ths (-α) : ℤ → 𝔼 → ℂ) j) (u / 2))
    (hC : E4At (d := d) α r.toReal) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ φ ψ : SchwartzMap 𝔼 ℂ,
      (∫⁻ x, QQ α φ ψ x ^ (r.toReal / 2)) ^ (1 / r.toReal) ≤
        C * (eLpNorm (⇑(Fm α φ)) p volume * eLpNorm (⇑ψ) q volume) := by
  have hrne : r ≠ ⊤ := hr'.ne
  have hr0 : r ≠ 0 := by intro h0; rw [h0] at hr; simp at hr
  have hrr : 1 < r.toReal := by
    have := ENNReal.toReal_strict_mono hrne hr
    simpa using this
  have hrr0 : 0 < r.toReal := by linarith
  have hp0 : p ≠ 0 := by intro h0; rw [h0] at hp; simp at hp
  have hq0 : q ≠ 0 := by intro h0; rw [h0] at hq; simp at hq
  by_cases hpt : p = ⊤
  · -- `p = ∞`, hence `q = r`
    have hqr : q = r := by
      rw [hpt] at h; simp at h
      exact h
    subst hqr
    obtain ⟨C, hCne, hCb⟩ := hC
    refine ⟨C ^ (1 / q.toReal), ENNReal.rpow_ne_top_of_nonneg (by positivity) hCne, fun φ ψ => ?_⟩
    have h1 := ENNReal.rpow_le_rpow (hCb φ ψ) (show (0 : ℝ) ≤ 1 / q.toReal by positivity)
    refine h1.trans (le_of_eq ?_)
    rw [hpt, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
      ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hr'.ne ψ.continuous.aestronglyMeasurable]
    have : q.toReal * (1 / q.toReal) = 1 := by field_simp
    rw [this, ENNReal.rpow_one]
  by_cases hqt : q = ⊤
  · have hpr : p = r := by
      rw [hqt] at h; simp at h
      exact h
    subst hpr
    obtain ⟨C, hCne, hCb⟩ := BILIN_qinf α hd hrr (hE p.toReal hrr)
    refine ⟨C ^ (1 / p.toReal), ENNReal.rpow_ne_top_of_nonneg (by positivity) hCne, fun φ ψ => ?_⟩
    have h1 := ENNReal.rpow_le_rpow (hCb φ ψ (eLpNorm (⇑ψ) ⊤ volume)
      (fun y => enorm_le_eLpNorm_top ψ y)) (show (0 : ℝ) ≤ 1 / p.toReal by positivity)
    refine h1.trans (le_of_eq ?_)
    rw [hqt, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
      ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hr'.ne (Fm α φ).continuous.aestronglyMeasurable]
    have : p.toReal * (1 / p.toReal) = 1 := by field_simp
    rw [this, ENNReal.rpow_one]
    ring
  · have hu : 1 < p.toReal := by
      have := ENNReal.toReal_strict_mono hpt hp
      simpa using this
    have hv : 1 < q.toReal := by
      have := ENNReal.toReal_strict_mono hqt hq
      simpa using this
    have huv := toReal_exps h hpt hqt hrne hp0 hq0 hr0
    obtain ⟨C, hCne, hCb⟩ := BILIN_fin α hd hrr hu hv huv (hE p.toReal hu)
    refine ⟨C ^ (1 / r.toReal), ENNReal.rpow_ne_top_of_nonneg (by positivity) hCne, fun φ ψ => ?_⟩
    have h1 := ENNReal.rpow_le_rpow (hCb φ ψ) (show (0 : ℝ) ≤ 1 / r.toReal by positivity)
    refine h1.trans (le_of_eq ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
      ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt (Fm α φ).continuous.aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt ψ.continuous.aestronglyMeasurable]
    have e1 : r.toReal / p.toReal * (1 / r.toReal) = 1 / p.toReal := by field_simp
    have e2 : r.toReal / q.toReal * (1 / r.toReal) = 1 / q.toReal := by field_simp
    rw [e1, e2]

end Pair

end HRS.Commutator.Whole.XLI
