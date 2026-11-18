import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# S8.2 R02 (S82R), M1: a coupling-free transfer inequality for two probability densities
If `|u a - v b| <= s + 1_{a != b} (w a + w b)` then `int u k - int v k' <= s + int w |k - k'|`.
(The maximal coupling of `k mu` and `k' mu` is only used in the proof, never constructed.)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace HRS.MS.S82R

variable {E : Type*} [MeasurableSpace E]

lemma s82r_mc (μ : Measure E) [IsProbabilityMeasure μ] (k k' : E → ℝ)
    (hk0 : ∀ z, 0 ≤ k z) (hk'0 : ∀ z, 0 ≤ k' z) (hki : Integrable k μ) (hk'i : Integrable k' μ)
    (hk1 : ∫ z, k z ∂μ = 1) (hk'1 : ∫ z, k' z ∂μ = 1)
    (u v w : E → ℝ) (hum : Measurable u) (hvm : Measurable v) (hwm : Measurable w)
    {Bu Bv Bw : ℝ} (hub : ∀ z, |u z| ≤ Bu) (hvb : ∀ z, |v z| ≤ Bv) (hwb : ∀ z, |w z| ≤ Bw)
    (hw0 : ∀ z, 0 ≤ w z) {s : ℝ}
    (hdiag : ∀ a, u a - v a ≤ s) (hoff : ∀ a b, u a - v b ≤ s + w a + w b) :
    ∫ z, u z * k z ∂μ - ∫ z, v z * k' z ∂μ ≤ s + ∫ z, w z * |k z - k' z| ∂μ := by
  set r : E → ℝ := fun z => max (k z - k' z) 0 with hr
  set r' : E → ℝ := fun z => max (k' z - k z) 0 with hr'
  set m : E → ℝ := fun z => k z - r z with hm
  have hri : Integrable r μ := (hki.sub hk'i).pos_part
  have hr'i : Integrable r' μ := (hk'i.sub hki).pos_part
  have hr0 : ∀ z, 0 ≤ r z := fun z => le_max_right _ _
  have hr'0 : ∀ z, 0 ≤ r' z := fun z => le_max_right _ _
  have hmi : Integrable m μ := hki.sub hri
  have hm0 : ∀ z, 0 ≤ m z := by
    intro z; simp only [hm, hr]
    rcases le_total (k z) (k' z) with h1 | h1
    · rw [max_eq_right (by linarith)]; linarith [hk0 z]
    · rw [max_eq_left (by linarith)]; linarith [hk'0 z]
  have hk'm : ∀ z, k' z = m z + r' z := by
    intro z; simp only [hm, hr, hr']
    rcases le_total (k z) (k' z) with h1 | h1
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have habs : ∀ z, |k z - k' z| = r z + r' z := by
    intro z; simp only [hr, hr']
    rcases le_total (k z) (k' z) with h1 | h1
    · rw [max_eq_right (by linarith), max_eq_left (by linarith), abs_of_nonpos (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith), abs_of_nonneg (by linarith)]; ring
  have hmeas : ∀ f : E → ℝ, Integrable f μ → ∀ g : E → ℝ, Measurable g → ∀ {B : ℝ}, (∀ z, |g z| ≤ B) →
      Integrable (fun z => g z * f z) μ := fun f hf g hg B hB =>
    hf.bdd_mul (c := B) hg.aestronglyMeasurable (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hB z)
  have hr'm : Integrable r' μ := hr'i
  have hrr : ∫ z, r z ∂μ = ∫ z, r' z ∂μ := by
    have h1 : ∫ z, (r z - r' z) ∂μ = ∫ z, (k z - k' z) ∂μ := by
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      simp only [hr, hr']
      rcases le_total (k z) (k' z) with h1 | h1
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
    rw [integral_sub hri hr'i, integral_sub hki hk'i, hk1, hk'1] at h1
    linarith
  set ε : ℝ := ∫ z, r z ∂μ with hε
  have hε0 : 0 ≤ ε := integral_nonneg hr0
  have hmε : ∫ z, m z ∂μ = 1 - ε := by
    rw [hm]; simp only; rw [integral_sub hki hri, hk1]
  have hwri : Integrable (fun z => w z * r z) μ := hmeas r hri w hwm hwb
  have hwr'i : Integrable (fun z => w z * r' z) μ := hmeas r' hr'i w hwm hwb
  have hwabs : ∫ z, w z * |k z - k' z| ∂μ = ∫ z, w z * r z ∂μ + ∫ z, w z * r' z ∂μ := by
    rw [← integral_add hwri hwr'i]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    show w z * |k z - k' z| = w z * r z + w z * r' z
    rw [habs z]; ring
  have hwnn : 0 ≤ ∫ z, w z * r z ∂μ := integral_nonneg fun z => mul_nonneg (hw0 z) (hr0 z)
  have hwnn' : 0 ≤ ∫ z, w z * r' z ∂μ := integral_nonneg fun z => mul_nonneg (hw0 z) (hr'0 z)
  -- split
  have hs1 : ∫ z, u z * k z ∂μ - ∫ z, v z * k' z ∂μ =
      ∫ z, (u z - v z) * m z ∂μ + ∫ z, u z * r z ∂μ - ∫ z, v z * r' z ∂μ := by
    have e1 : ∫ z, u z * k z ∂μ = ∫ z, u z * m z ∂μ + ∫ z, u z * r z ∂μ := by
      rw [← integral_add (hmeas m hmi u hum hub) (hmeas r hri u hum hub)]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      simp only [hm]; ring
    have e2 : ∫ z, v z * k' z ∂μ = ∫ z, v z * m z ∂μ + ∫ z, v z * r' z ∂μ := by
      rw [← integral_add (hmeas m hmi v hvm hvb) (hmeas r' hr'i v hvm hvb)]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      show v z * k' z = v z * m z + v z * r' z
      rw [hk'm z]; ring
    have e3 : ∫ z, (u z - v z) * m z ∂μ = ∫ z, u z * m z ∂μ - ∫ z, v z * m z ∂μ := by
      rw [← integral_sub (hmeas m hmi u hum hub) (hmeas m hmi v hvm hvb)]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      ring
    rw [e1, e2, e3]; ring
  have hs2 : ∫ z, (u z - v z) * m z ∂μ ≤ s * (1 - ε) := by
    rw [← hmε, ← integral_const_mul]
    have hI : Integrable (fun z => (u z - v z) * m z) μ :=
      hmi.bdd_mul (c := Bu + Bv) (hum.sub hvm).aestronglyMeasurable
        (ae_of_all _ fun z => by
          rw [Real.norm_eq_abs]
          exact (abs_sub _ _).trans (add_le_add (hub z) (hvb z)))
    refine integral_mono hI (hmi.const_mul s) fun z => ?_
    exact mul_le_mul_of_nonneg_right (hdiag z) (hm0 z)
  rw [hs1, hwabs]
  by_cases hε' : ε = 0
  · have hr0a : ∀ᵐ z ∂μ, r z = 0 := by
      have := (integral_eq_zero_iff_of_nonneg hr0 hri).1 hε'
      filter_upwards [this] with z hz; exact hz
    have hr'0a : ∀ᵐ z ∂μ, r' z = 0 := by
      have h2 : ∫ z, r' z ∂μ = 0 := by rw [← hrr]; exact hε'
      have := (integral_eq_zero_iff_of_nonneg hr'0 hr'i).1 h2
      filter_upwards [this] with z hz; exact hz
    have e1 : ∫ z, u z * r z ∂μ = 0 := by
      rw [integral_eq_zero_of_ae]; filter_upwards [hr0a] with z hz; simp [hz]
    have e2 : ∫ z, v z * r' z ∂μ = 0 := by
      rw [integral_eq_zero_of_ae]; filter_upwards [hr'0a] with z hz; simp [hz]
    rw [e1, e2]
    rw [hε'] at hs2
    linarith
  · have hεpos : 0 < ε := lt_of_le_of_ne hε0 (Ne.symm hε')
    set Cb : ℝ := ∫ z, v z * r' z ∂μ with hCb
    -- pointwise in a
    have hpt : ∀ a, u a * ε - Cb ≤ (s + w a) * ε + ∫ z, w z * r' z ∂μ := by
      intro a
      have h1 : ∫ z, (u a - v z) * r' z ∂μ ≤ ∫ z, (s + w a + w z) * r' z ∂μ := by
        refine integral_mono ?_ ?_ fun z => ?_
        · have := (hr'i.const_mul (u a)).sub (hmeas r' hr'i v hvm hvb)
          exact this.congr (ae_of_all _ fun z => by simp only [Pi.sub_apply]; ring)
        · have := (hr'i.const_mul (s + w a)).add hwr'i
          exact this.congr (ae_of_all _ fun z => by simp only [Pi.add_apply]; ring)
        · exact mul_le_mul_of_nonneg_right (by linarith [hoff a z]) (hr'0 z)
      have e1 : ∫ z, (u a - v z) * r' z ∂μ = u a * ε - Cb := by
        have : ∫ z, (u a - v z) * r' z ∂μ = u a * ∫ z, r' z ∂μ - ∫ z, v z * r' z ∂μ := by
          rw [← integral_const_mul, ← integral_sub (hr'i.const_mul (u a)) (hmeas r' hr'i v hvm hvb)]
          refine integral_congr_ae (ae_of_all _ fun z => ?_)
          ring
        rw [this, ← hrr]
      have e2 : ∫ z, (s + w a + w z) * r' z ∂μ = (s + w a) * ε + ∫ z, w z * r' z ∂μ := by
        have : ∫ z, (s + w a + w z) * r' z ∂μ =
            (s + w a) * ∫ z, r' z ∂μ + ∫ z, w z * r' z ∂μ := by
          rw [← integral_const_mul, ← integral_add (hr'i.const_mul (s + w a)) hwr'i]
          refine integral_congr_ae (ae_of_all _ fun z => ?_)
          ring
        rw [this, ← hrr]
      linarith
    set W' : ℝ := ∫ z, w z * r' z ∂μ with hW'
    have hint : ε * (∫ z, u z * r z ∂μ - Cb) ≤ ε * (s * ε + ∫ z, w z * r z ∂μ + W') := by
      have hur := hmeas r hri u hum hub
      have h3 : ∫ z, (ε * (u z * r z) - Cb * r z) ∂μ ≤
          ∫ z, ((s * ε + W') * r z + ε * (w z * r z)) ∂μ := by
        refine integral_mono ((hur.const_mul ε).sub (hri.const_mul Cb))
          ((hri.const_mul _).add (hwri.const_mul ε)) fun z => ?_
        have := mul_le_mul_of_nonneg_right (hpt z) (hr0 z)
        nlinarith [this]
      rw [integral_sub (hur.const_mul ε) (hri.const_mul Cb), integral_add (hri.const_mul _)
        (hwri.const_mul ε), integral_const_mul, integral_const_mul, integral_const_mul,
        integral_const_mul] at h3
      rw [← hε] at h3
      nlinarith [h3]
    have h4 : ∫ z, u z * r z ∂μ - Cb ≤ s * ε + ∫ z, w z * r z ∂μ + W' :=
      le_of_mul_le_mul_left hint hεpos
    nlinarith [hs2, h4, hwnn, hwnn', hmε]
