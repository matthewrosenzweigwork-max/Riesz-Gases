import HRS.Energy.StaticLimitCoupling

/-!
# Exponentially tilted laws and their Wasserstein stability (work package STAT-4.21)
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.StaticLimitAux

section Tilt

variable {B : Type*} [MeasurableSpace B]

/-- The tilted (reweighted, renormalised) law `w ν / ν(w)`. -/
def tiltMeasure (w : B → ℝ) (ν : Measure B) : Measure B :=
  (ENNReal.ofReal (∫ x, w x ∂ν))⁻¹ • ν.withDensity (fun x => ENNReal.ofReal (w x))

theorem tiltMeasure_eq (w : B → ℝ) (ν : Measure B) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (hA : 0 < ∫ y, w y ∂ν) :
    tiltMeasure w ν = ν.withDensity (fun x => ENNReal.ofReal (w x / ∫ y, w y ∂ν)) := by
  unfold tiltMeasure
  have hm : Measurable fun x => ENNReal.ofReal (w x) := ENNReal.measurable_ofReal.comp hw
  rw [← withDensity_smul _ hm]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [div_eq_mul_inv, ENNReal.ofReal_mul (hw0 x), ENNReal.ofReal_inv_of_pos hA, mul_comm]

theorem map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (π : Measure α) (φ : α → β) (hφ : Measurable φ) (g : β → ℝ≥0∞) (hg : Measurable g) :
    (π.withDensity (g ∘ φ)).map φ = (π.map φ).withDensity g := by
  ext s hs
  rw [Measure.map_apply hφ hs, withDensity_apply _ (hφ hs), withDensity_apply _ hs,
    setLIntegral_map hs hg hφ]
  rfl

theorem lintegral_ofReal_div (w : B → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (ν : Measure B) (hint : Integrable w ν) (hA : 0 < ∫ y, w y ∂ν) :
    ∫⁻ x, ENNReal.ofReal (w x / ∫ y, w y ∂ν) ∂ν = 1 := by
  have e : ∀ x, ENNReal.ofReal (w x / ∫ y, w y ∂ν) =
      (ENNReal.ofReal (∫ y, w y ∂ν))⁻¹ * ENNReal.ofReal (w x) := by
    intro x
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (hw0 x), ENNReal.ofReal_inv_of_pos hA, mul_comm]
  simp_rw [e]
  have hm : Measurable fun x => ENNReal.ofReal (w x) := ENNReal.measurable_ofReal.comp hw
  rw [lintegral_const_mul _ hm,
    ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hw0)]
  exact ENNReal.inv_mul_cancel (by simpa using hA) ENNReal.ofReal_ne_top

end Tilt

section RealAux

theorem abs_div_sub_div_le {a b A₁ A₂ c L d : ℝ} (hc : 0 < c) (hA₁ : c ≤ A₁) (hA₂ : c ≤ A₂)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hab : |a - b| ≤ L * d) (hL : 0 ≤ L) (hd : 0 ≤ d) :
    |a / A₁ - b / A₂| ≤ L * d / c + |A₁ - A₂| / c ^ 2 := by
  have hA₁p : 0 < A₁ := hc.trans_le hA₁
  have hA₂p : 0 < A₂ := hc.trans_le hA₂
  have e : a / A₁ - b / A₂ = (a - b) / A₁ + b * ((A₂ - A₁) / (A₁ * A₂)) := by
    field_simp; ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_div, abs_of_pos hA₁p]
    calc |a - b| / A₁ ≤ (L * d) / A₁ := by gcongr
      _ ≤ (L * d) / c := by gcongr
  · rw [abs_mul, abs_of_nonneg hb0, abs_div, abs_of_pos (mul_pos hA₁p hA₂p), abs_sub_comm]
    calc b * (|A₁ - A₂| / (A₁ * A₂)) ≤ 1 * (|A₁ - A₂| / (A₁ * A₂)) := by
          gcongr
      _ ≤ |A₁ - A₂| / c ^ 2 := by
          rw [one_mul]
          gcongr
          nlinarith

theorem ofReal_sub_min_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (ENNReal.ofReal a - min (ENNReal.ofReal a) (ENNReal.ofReal b)) +
      (ENNReal.ofReal b - min (ENNReal.ofReal a) (ENNReal.ofReal b)) = ENNReal.ofReal |a - b| := by
  rcases le_total a b with h | h
  · have h' : ENNReal.ofReal a ≤ ENNReal.ofReal b := ENNReal.ofReal_le_ofReal h
    rw [min_eq_left h', tsub_self, zero_add, abs_of_nonpos (by linarith), neg_sub,
      ENNReal.ofReal_sub _ ha]
  · have h' : ENNReal.ofReal b ≤ ENNReal.ofReal a := ENNReal.ofReal_le_ofReal h
    rw [min_eq_right h', tsub_self, add_zero, abs_of_nonneg (by linarith),
      ENNReal.ofReal_sub _ hb]

end RealAux

section Transfer

variable {B E : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology B] [CompleteSpace B]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- The explicit modulus of the tilt transfer. -/
def tiltBound (L c Q δ : ℝ) : ℝ :=
  Real.sqrt (δ ^ 2 / c) +
    Real.sqrt (2 * (Real.sqrt (2 * L ^ 2 / c ^ 2 + 2 * L ^ 2 / c ^ 4) * δ) * Real.sqrt Q)


theorem abs_integral_sub_le (π₀ : Measure (B × B)) [IsProbabilityMeasure π₀]
    (w : B → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    (L : ℝ) (hL : 0 ≤ L) (hwL : ∀ x y, |w x - w y| ≤ L * ‖x - y‖)
    (ν₁ ν₂ : Measure B) (h1 : π₀.map Prod.fst = ν₁) (h2 : π₀.map Prod.snd = ν₂)
    (δ : ℝ) (hδ : 0 < δ)
    (hcost : ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π₀ ≤ ENNReal.ofReal (δ ^ 2)) :
    |∫ x, w x ∂ν₁ - ∫ x, w x ∂ν₂| ≤ L * δ := by
  have hb : ∀ x, ‖w x‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hw0 x)]; exact hw1 x
  have hi1 : Integrable (fun z : B × B => w z.1) π₀ :=
    Integrable.of_bound (hw.comp measurable_fst).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun z => hb _)
  have hi2 : Integrable (fun z : B × B => w z.2) π₀ :=
    Integrable.of_bound (hw.comp measurable_snd).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun z => hb _)
  have e1 : ∫ x, w x ∂ν₁ = ∫ z, w z.1 ∂π₀ := by
    rw [← h1, integral_map measurable_fst.aemeasurable hw.aestronglyMeasurable]
  have e2 : ∫ x, w x ∂ν₂ = ∫ z, w z.2 ∂π₀ := by
    rw [← h2, integral_map measurable_snd.aemeasurable hw.aestronglyMeasurable]
  rw [e1, e2, ← integral_sub hi1 hi2]
  refine (abs_integral_le_integral_abs).trans ?_
  have hm : Measurable fun z : B × B => |w z.1 - w z.2| :=
    ((hw.comp measurable_fst).sub (hw.comp measurable_snd)).abs
  have hdm : Measurable fun z : B × B => ‖z.1 - z.2‖ := (measurable_fst.sub measurable_snd).norm
  have hm2 : Measurable fun z : B × B => ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) :=
    ENNReal.measurable_ofReal.comp (hdm.pow_const (2 : ℝ))
  have hle : ∫⁻ z, ENNReal.ofReal |w z.1 - w z.2| ∂π₀ ≤ ENNReal.ofReal (L * δ) := by
    have hpt : ∀ z : B × B, ENNReal.ofReal |w z.1 - w z.2| ≤
        ENNReal.ofReal (L / (2 * δ)) * ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) +
          ENNReal.ofReal (L * δ / 2) := by
      intro z
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hd0 := norm_nonneg (z.1 - z.2)
      have := hwL z.1 z.2
      rw [Real.rpow_two]
      have h3 : ‖z.1 - z.2‖ ≤ ‖z.1 - z.2‖ ^ 2 / (2 * δ) + δ / 2 := by
        rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (‖z.1 - z.2‖ - δ)]
      calc |w z.1 - w z.2| ≤ L * ‖z.1 - z.2‖ := this
        _ ≤ L * (‖z.1 - z.2‖ ^ 2 / (2 * δ) + δ / 2) := by gcongr
        _ = L / (2 * δ) * ‖z.1 - z.2‖ ^ 2 + L * δ / 2 := by field_simp
    calc ∫⁻ z, ENNReal.ofReal |w z.1 - w z.2| ∂π₀
        ≤ ∫⁻ z, (ENNReal.ofReal (L / (2 * δ)) * ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) +
          ENNReal.ofReal (L * δ / 2)) ∂π₀ := lintegral_mono hpt
      _ = ENNReal.ofReal (L / (2 * δ)) * ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π₀ +
          ENNReal.ofReal (L * δ / 2) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hm2, lintegral_const, measure_univ, mul_one]
      _ ≤ ENNReal.ofReal (L / (2 * δ)) * ENNReal.ofReal (δ ^ 2) + ENNReal.ofReal (L * δ / 2) := by
        gcongr
      _ = ENNReal.ofReal (L * δ) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        field_simp
        ring
  have hint : Integrable (fun z : B × B => |w z.1 - w z.2|) π₀ := (hi1.sub hi2).abs
  calc ∫ z, |w z.1 - w z.2| ∂π₀ = (∫⁻ z, ENNReal.ofReal |w z.1 - w z.2| ∂π₀).toReal :=
        integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z => abs_nonneg _)
          hm.aestronglyMeasurable
    _ ≤ (ENNReal.ofReal (L * δ)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ = L * δ := ENNReal.toReal_ofReal (by positivity)


theorem tilt_final (π₀ : Measure (B × B)) [IsProbabilityMeasure π₀]
    (w : B → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    (L : ℝ) (hL : 0 ≤ L) (hwL : ∀ x y, |w x - w y| ≤ L * ‖x - y‖)
    (c : ℝ) (hc : 0 < c) (A₁ A₂ : ℝ) (hA₁ : c ≤ A₁) (hA₂ : c ≤ A₂)
    (δ : ℝ) (hδ : 0 < δ) (hΔ : |A₁ - A₂| ≤ L * δ) (Q : ℝ)
    (hcost : ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π₀ ≤ ENNReal.ofReal (δ ^ 2))
    (hQ : ∫⁻ z, ENNReal.ofReal (‖z.2‖ ^ 4) ∂π₀ ≤ ENNReal.ofReal Q) :
    (∫⁻ z, ENNReal.ofReal (w z.1 / A₁) * ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π₀) ^ (1 / (2 : ℝ)) +
      (2 * ∫⁻ z, ((ENNReal.ofReal (w z.1 / A₁) - min (ENNReal.ofReal (w z.1 / A₁))
            (ENNReal.ofReal (w z.2 / A₂))) +
          (ENNReal.ofReal (w z.2 / A₂) - min (ENNReal.ofReal (w z.1 / A₁))
            (ENNReal.ofReal (w z.2 / A₂)))) * ENNReal.ofReal (‖z.2‖ ^ 2) ∂π₀) ^ (1 / (2 : ℝ)) ≤
      ENNReal.ofReal (tiltBound L c Q δ) := by
  have hA₁p : 0 < A₁ := hc.trans_le hA₁
  have hA₂p : 0 < A₂ := hc.trans_le hA₂
  have hdm : Measurable fun z : B × B => ‖z.1 - z.2‖ := (measurable_fst.sub measurable_snd).norm
  have hm2 : Measurable fun z : B × B => ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) :=
    ENNReal.measurable_ofReal.comp (hdm.pow_const (2 : ℝ))
  have hnm : Measurable fun z : B × B => ‖z.2‖ := measurable_snd.norm
  unfold tiltBound
  rw [ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
  refine add_le_add ?_ ?_
  · have key : ∫⁻ z, ENNReal.ofReal (w z.1 / A₁) * ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π₀ ≤
        ENNReal.ofReal (δ ^ 2 / c) := by
      calc ∫⁻ z, ENNReal.ofReal (w z.1 / A₁) * ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π₀
          ≤ ∫⁻ z, ENNReal.ofReal (1 / c) * ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π₀ := by
            refine lintegral_mono fun z => ?_
            exact mul_le_mul_left (ENNReal.ofReal_le_ofReal
              (div_le_div₀ (by norm_num) (hw1 z.1) hc hA₁)) _
        _ = ENNReal.ofReal (1 / c) * ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π₀ :=
            lintegral_const_mul _ hm2
        _ ≤ ENNReal.ofReal (1 / c) * ENNReal.ofReal (δ ^ 2) := by gcongr
        _ = ENNReal.ofReal (δ ^ 2 / c) := by
            rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
    calc _ ≤ (ENNReal.ofReal (δ ^ 2 / c)) ^ (1 / (2 : ℝ)) :=
          ENNReal.rpow_le_rpow key (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt (δ ^ 2 / c)) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.sqrt_eq_rpow]
  · set D := Real.sqrt (2 * L ^ 2 / c ^ 2 + 2 * L ^ 2 / c ^ 4) with hD
    have hD0 : 0 ≤ D := Real.sqrt_nonneg _
    have hD2 : D ^ 2 = 2 * L ^ 2 / c ^ 2 + 2 * L ^ 2 / c ^ 4 :=
      Real.sq_sqrt (by positivity)
    set g : B × B → ℝ := fun z => L / c * ‖z.1 - z.2‖ + L * δ / c ^ 2 with hg
    have hg0 : ∀ z, 0 ≤ g z := fun z => by simp only [hg]; positivity
    have hpt : ∀ z : B × B, ((ENNReal.ofReal (w z.1 / A₁) - min (ENNReal.ofReal (w z.1 / A₁))
            (ENNReal.ofReal (w z.2 / A₂))) +
          (ENNReal.ofReal (w z.2 / A₂) - min (ENNReal.ofReal (w z.1 / A₁))
            (ENNReal.ofReal (w z.2 / A₂)))) ≤ ENNReal.ofReal (g z) := by
      intro z
      rw [ofReal_sub_min_add (div_nonneg (hw0 _) hA₁p.le) (div_nonneg (hw0 _) hA₂p.le)]
      apply ENNReal.ofReal_le_ofReal
      have h := abs_div_sub_div_le hc hA₁ hA₂ (hw0 z.1) (hw0 z.2) (hw1 z.2) (hwL z.1 z.2) hL
        (norm_nonneg (z.1 - z.2))
      refine h.trans ?_
      simp only [hg]
      have : |A₁ - A₂| / c ^ 2 ≤ L * δ / c ^ 2 := by gcongr
      calc L * ‖z.1 - z.2‖ / c + |A₁ - A₂| / c ^ 2 ≤ L * ‖z.1 - z.2‖ / c + L * δ / c ^ 2 := by
            gcongr
        _ = _ := by ring
    have hgm : Measurable g := (hdm.const_mul _).add_const _
    have hgsq : ∫⁻ z, (ENNReal.ofReal (g z)) ^ (2 : ℝ) ∂π₀ ≤ ENNReal.ofReal ((D * δ) ^ 2) := by
      have hpt2 : ∀ z : B × B, (ENNReal.ofReal (g z)) ^ (2 : ℝ) ≤
          ENNReal.ofReal (2 * (L / c) ^ 2) * ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) +
            ENNReal.ofReal (2 * (L * δ / c ^ 2) ^ 2) := by
        intro z
        rw [ENNReal.ofReal_rpow_of_nonneg (hg0 z) (by norm_num), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        rw [Real.rpow_two, Real.rpow_two]
        simp only [hg]
        nlinarith [sq_nonneg (L / c * ‖z.1 - z.2‖ - L * δ / c ^ 2)]
      calc ∫⁻ z, (ENNReal.ofReal (g z)) ^ (2 : ℝ) ∂π₀
          ≤ ∫⁻ z, (ENNReal.ofReal (2 * (L / c) ^ 2) * ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) +
            ENNReal.ofReal (2 * (L * δ / c ^ 2) ^ 2)) ∂π₀ := lintegral_mono hpt2
        _ = ENNReal.ofReal (2 * (L / c) ^ 2) * ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π₀ +
            ENNReal.ofReal (2 * (L * δ / c ^ 2) ^ 2) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hm2, lintegral_const,
            measure_univ, mul_one]
        _ ≤ ENNReal.ofReal (2 * (L / c) ^ 2) * ENNReal.ofReal (δ ^ 2) +
            ENNReal.ofReal (2 * (L * δ / c ^ 2) ^ 2) := by gcongr
        _ = ENNReal.ofReal ((D * δ) ^ 2) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          rw [mul_pow, hD2]
          field_simp
    have hn4 : ∫⁻ z, (ENNReal.ofReal (‖z.2‖ ^ 2)) ^ (2 : ℝ) ∂π₀ ≤ ENNReal.ofReal Q := by
      refine le_trans (le_of_eq ?_) hQ
      refine lintegral_congr fun z => ?_
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.rpow_two, ← pow_mul]
    have hCS : ∫⁻ z, (ENNReal.ofReal (g z)) * ENNReal.ofReal (‖z.2‖ ^ 2) ∂π₀ ≤
        ENNReal.ofReal (D * δ) * ENNReal.ofReal (Real.sqrt Q) := by
      have h := ENNReal.lintegral_mul_le_Lp_mul_Lq π₀ Real.HolderConjugate.two_two
        (f := fun z => ENNReal.ofReal (g z)) (g := fun z => ENNReal.ofReal (‖z.2‖ ^ 2))
        (ENNReal.measurable_ofReal.comp hgm).aemeasurable
        (ENNReal.measurable_ofReal.comp (hnm.pow_const 2)).aemeasurable
      refine h.trans (mul_le_mul' ?_ ?_)
      · calc _ ≤ (ENNReal.ofReal ((D * δ) ^ 2)) ^ (1 / (2 : ℝ)) :=
              ENNReal.rpow_le_rpow hgsq (by norm_num)
          _ = ENNReal.ofReal (D * δ) := by
              rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
                Real.sqrt_sq (by positivity)]
      · rcases le_or_gt 0 Q with hQ0 | hQ0
        · calc _ ≤ (ENNReal.ofReal Q) ^ (1 / (2 : ℝ)) := ENNReal.rpow_le_rpow hn4 (by norm_num)
            _ = ENNReal.ofReal (Real.sqrt Q) := by
                rw [ENNReal.ofReal_rpow_of_nonneg hQ0 (by norm_num), Real.sqrt_eq_rpow]
        · rw [ENNReal.ofReal_of_nonpos hQ0.le] at hn4
          have h0 : ∫⁻ z, (ENNReal.ofReal (‖z.2‖ ^ 2)) ^ (2 : ℝ) ∂π₀ = 0 := le_antisymm hn4 bot_le
          rw [h0, ENNReal.zero_rpow_of_pos (by norm_num)]
          exact bot_le
    have hbr : ∫⁻ z, ((ENNReal.ofReal (w z.1 / A₁) - min (ENNReal.ofReal (w z.1 / A₁))
            (ENNReal.ofReal (w z.2 / A₂))) +
          (ENNReal.ofReal (w z.2 / A₂) - min (ENNReal.ofReal (w z.1 / A₁))
            (ENNReal.ofReal (w z.2 / A₂)))) * ENNReal.ofReal (‖z.2‖ ^ 2) ∂π₀ ≤
        ENNReal.ofReal (D * δ) * ENNReal.ofReal (Real.sqrt Q) :=
      (lintegral_mono fun z => mul_le_mul_left (hpt z) _).trans hCS
    have h2 : 2 * ∫⁻ z, ((ENNReal.ofReal (w z.1 / A₁) - min (ENNReal.ofReal (w z.1 / A₁))
            (ENNReal.ofReal (w z.2 / A₂))) +
          (ENNReal.ofReal (w z.2 / A₂) - min (ENNReal.ofReal (w z.1 / A₁))
            (ENNReal.ofReal (w z.2 / A₂)))) * ENNReal.ofReal (‖z.2‖ ^ 2) ∂π₀ ≤
        ENNReal.ofReal (2 * (D * δ) * Real.sqrt Q) := by
      calc _ ≤ 2 * (ENNReal.ofReal (D * δ) * ENNReal.ofReal (Real.sqrt Q)) := by gcongr
        _ = _ := by
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
    calc _ ≤ (ENNReal.ofReal (2 * (D * δ) * Real.sqrt Q)) ^ (1 / (2 : ℝ)) :=
          ENNReal.rpow_le_rpow h2 (by norm_num)
      _ = _ := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.sqrt_eq_rpow (2 * (D * δ) * Real.sqrt Q)]

/-- A pair of laws with a coupling of small `W₂`-cost and a reweighting by a bounded Lipschitz
weight with non-degenerate mass stay close in `W₂` after reweighting and pushing forward. -/
theorem tilt_W2_le (w : B → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    (L : ℝ) (hL : 0 ≤ L) (hwL : ∀ x y, |w x - w y| ≤ L * ‖x - y‖)
    (T : B → E) (hT : Measurable T) (hTL : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖)
    (ν₁ ν₂ : Measure B) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (c : ℝ) (hc : 0 < c) (hA₂ : 2 * c ≤ ∫ x, w x ∂ν₂)
    (Q : ℝ) (hQ : ∫⁻ y, ENNReal.ofReal (‖y‖ ^ 4) ∂ν₂ ≤ ENNReal.ofReal Q)
    (δ : ℝ) (hδ : 0 ≤ δ) (hLδ : L * δ ≤ c) (hW : wassersteinE 2 ν₁ ν₂ < ENNReal.ofReal δ) :
    wassersteinE 2 ((tiltMeasure w ν₁).map T) ((tiltMeasure w ν₂).map T) ≤
      ENNReal.ofReal (tiltBound L c Q δ) := by
  -- the coupling
  obtain ⟨π, hπ⟩ := iInf_lt_iff.mp hW
  have hπprob : IsProbabilityMeasure π.1 := IsCoupling.isProbabilityMeasure π.2
  set π₀ : Measure (B × B) := π.1 with hπ₀
  have hπ1 : π₀.map Prod.fst = ν₁ := π.2.1
  have hπ2 : π₀.map Prod.snd = ν₂ := π.2.2
  have hcost : ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π₀ ≤ ENNReal.ofReal (δ ^ 2) := by
    have h1 := ENNReal.rpow_lt_rpow hπ (by norm_num : (0 : ℝ) < 2)
    rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ (by norm_num), ENNReal.rpow_one,
      ENNReal.ofReal_rpow_of_nonneg hδ (by norm_num), Real.rpow_two] at h1
    exact h1.le
  have hδ' : 0 < δ := by
    by_contra hneg
    rw [ENNReal.ofReal_of_nonpos (not_lt.mp hneg)] at hW
    exact not_lt_zero hW
  have hΔ := abs_integral_sub_le π₀ w hw hw0 hw1 L hL hwL ν₁ ν₂ hπ1 hπ2 δ hδ' hcost
  have hA₁ : c ≤ ∫ x, w x ∂ν₁ := by
    have := (abs_le.mp hΔ).1
    linarith
  have hA₂' : c ≤ ∫ x, w x ∂ν₂ := by linarith
  have hint1 : Integrable w ν₁ := Integrable.of_bound hw.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hw0 x)]; exact hw1 x)
  have hint2 : Integrable w ν₂ := Integrable.of_bound hw.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hw0 x)]; exact hw1 x)
  set A₁ := ∫ x, w x ∂ν₁ with hA₁d
  set A₂ := ∫ x, w x ∂ν₂ with hA₂d
  have hA₁p : 0 < A₁ := hc.trans_le hA₁
  have hA₂p : 0 < A₂ := hc.trans_le hA₂'
  set F₁ : B × B → ℝ≥0∞ := fun z => ENNReal.ofReal (w z.1 / A₁) with hF₁d
  set F₂ : B × B → ℝ≥0∞ := fun z => ENNReal.ofReal (w z.2 / A₂) with hF₂d
  have hF₁m : Measurable F₁ :=
    ENNReal.measurable_ofReal.comp ((hw.comp measurable_fst).div_const _)
  have hF₂m : Measurable F₂ :=
    ENNReal.measurable_ofReal.comp ((hw.comp measurable_snd).div_const _)
  have hgm₁ : Measurable fun x => ENNReal.ofReal (w x / A₁) :=
    ENNReal.measurable_ofReal.comp (hw.div_const _)
  have hgm₂ : Measurable fun x => ENNReal.ofReal (w x / A₂) :=
    ENNReal.measurable_ofReal.comp (hw.div_const _)
  have hI₁ : ∫⁻ z, F₁ z ∂π₀ = 1 := by
    have := lintegral_map hgm₁ measurable_fst (μ := π₀)
    rw [hπ1] at this
    rw [show (∫⁻ z, F₁ z ∂π₀) = ∫⁻ z, (fun x => ENNReal.ofReal (w x / A₁)) z.1 ∂π₀ from rfl,
      ← this]
    exact lintegral_ofReal_div w hw hw0 ν₁ hint1 hA₁p
  have hI₂ : ∫⁻ z, F₂ z ∂π₀ = 1 := by
    have := lintegral_map hgm₂ measurable_snd (μ := π₀)
    rw [hπ2] at this
    rw [show (∫⁻ z, F₂ z ∂π₀) = ∫⁻ z, (fun x => ENNReal.ofReal (w x / A₂)) z.2 ∂π₀ from rfl,
      ← this]
    exact lintegral_ofReal_div w hw hw0 ν₂ hint2 hA₂p
  have hM₁ : (π₀.withDensity F₁).map Prod.fst = tiltMeasure w ν₁ := by
    refine Eq.trans ?_ (tiltMeasure_eq w ν₁ hw hw0 hA₁p).symm
    have := map_withDensity_comp π₀ Prod.fst measurable_fst _ hgm₁
    rw [hπ1] at this
    exact this
  have hM₂ : (π₀.withDensity F₂).map Prod.snd = tiltMeasure w ν₂ := by
    refine Eq.trans ?_ (tiltMeasure_eq w ν₂ hw hw0 hA₂p).symm
    have := map_withDensity_comp π₀ Prod.snd measurable_snd _ hgm₂
    rw [hπ2] at this
    exact this
  have hprob : ∀ ν : Measure B, ∀ (hA : 0 < ∫ y, w y ∂ν), Integrable w ν → IsProbabilityMeasure ν →
      IsProbabilityMeasure (tiltMeasure w ν) := by
    intro ν hA hi hν
    rw [tiltMeasure_eq w ν hw hw0 hA]
    exact ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      lintegral_ofReal_div w hw hw0 ν hi hA]⟩
  have hT1p := hprob ν₁ hA₁p hint1 inferInstance
  have hT2p := hprob ν₂ hA₂p hint2 inferInstance
  have hmain := wassersteinE_two_reweight π₀ F₁ F₂ hF₁m hF₂m hI₁ hI₂
  rw [hM₁, hM₂] at hmain
  refine (wassersteinE_two_map_le T hT hTL _ _).trans (hmain.trans ?_)
  have hQ' : ∫⁻ z, ENNReal.ofReal (‖z.2‖ ^ 4) ∂π₀ ≤ ENNReal.ofReal Q := by
    have hm4 : Measurable fun y : B => ENNReal.ofReal (‖y‖ ^ 4) :=
      ENNReal.measurable_ofReal.comp (measurable_norm.pow_const 4)
    have := lintegral_map hm4 measurable_snd (μ := π₀)
    rw [hπ2] at this
    exact this.symm.le.trans hQ
  exact tilt_final π₀ w hw hw0 hw1 L hL hwL c hc A₁ A₂ hA₁ hA₂' δ hδ' hΔ Q hcost hQ'

end Transfer

end HRS.StaticLimitAux
