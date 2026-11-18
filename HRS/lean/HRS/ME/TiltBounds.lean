import HRS.Equilibrium.StaticLimits

/-!
# Bounds for the cosine tilt (Example 5.12, `HRS.cosine_tilt_example`)

* `HRS.ME.TiltBounds.tilt_density_bounds`: for a probability measure `P` and `|a| < 1`, the tilt
  `(1 + a cos Z x) / ∫ (1 + a cos Z y) dP` lies in `[(1-|a|)/(1+|a|), (1+|a|)/(1-|a|)]`.
* `HRS.ME.TiltBounds.cosineTiltDensity_not_gaussian`: for `a ≠ 0`, `|a| < 1`, `v > 0`, the
  measure with density `HRS.cosineTiltDensity a v` is not any Gaussian law `gaussianReal m w`.
  Proof: equal densities force `1 + a cos z = C exp(z²/(2v) - (z-m)²/(2w))`; taking logs and
  using `2π`-periodicity at `z = 0, 1, π, 1 + 2π, 2π` forces the quadratic coefficients to vanish,
  so `log(1 - a) = log(1 + a)`, contradicting `a ≠ 0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.ME.TiltBounds

theorem tilt_density_bounds {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (Z : X → ℝ) (hZ : Measurable Z) {a : ℝ} (ha : |a| < 1) (x : X) :
    (1 - |a|) / (1 + |a|) ≤ (1 + a * Real.cos (Z x)) / ∫ y, (1 + a * Real.cos (Z y)) ∂P ∧
      (1 + a * Real.cos (Z x)) / ∫ y, (1 + a * Real.cos (Z y)) ∂P ≤ (1 + |a|) / (1 - |a|) := by
  have hc : ∀ y, 1 - |a| ≤ 1 + a * Real.cos (Z y) ∧ 1 + a * Real.cos (Z y) ≤ 1 + |a| := by
    intro y
    have h1 : |a * Real.cos (Z y)| ≤ |a| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg a) (Real.abs_cos_le_one _)
    have h2 := abs_le.mp h1
    constructor <;> linarith [h2.1, h2.2]
  have hpos : 0 < 1 - |a| := by linarith
  have hpos' : (0 : ℝ) ≤ 1 + |a| := by linarith [abs_nonneg a]
  have hmeas : Measurable (fun y => 1 + a * Real.cos (Z y)) :=
    measurable_const.add (measurable_const.mul (Real.continuous_cos.measurable.comp hZ))
  have hint : Integrable (fun y => 1 + a * Real.cos (Z y)) P := by
    refine Integrable.mono' (integrable_const (1 + |a|)) hmeas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [(hc y).1, (hc y).2, abs_nonneg a]
  have hI1 : 1 - |a| ≤ ∫ y, (1 + a * Real.cos (Z y)) ∂P := by
    have h := integral_mono (integrable_const (1 - |a|)) hint (fun y => (hc y).1)
    simpa using h
  have hI2 : ∫ y, (1 + a * Real.cos (Z y)) ∂P ≤ 1 + |a| := by
    have h := integral_mono hint (integrable_const (1 + |a|)) (fun y => (hc y).2)
    simpa using h
  have hIpos : 0 < ∫ y, (1 + a * Real.cos (Z y)) ∂P := lt_of_lt_of_le hpos hI1
  constructor
  · rw [div_le_div_iff₀ (by linarith [abs_nonneg a]) hIpos]
    nlinarith [mul_le_mul_of_nonneg_left hI2 hpos.le,
      mul_le_mul_of_nonneg_right (hc x).1 hpos']
  · rw [div_le_div_iff₀ hIpos hpos]
    nlinarith [mul_le_mul_of_nonneg_right (hc x).2 hpos.le,
      mul_le_mul_of_nonneg_left hI1 hpos']

/-- Pure algebra: a quadratic `A z² + B z + G` that agrees with itself at `2π` and `1 + 2π`
(relative to `0` and `1`) has `A = B = 0`, hence `q π = q 0`. -/
theorem quad_eq_of_periodic (A B G : ℝ) (h1 : A * (2 * Real.pi) ^ 2 + B * (2 * Real.pi) + G = G)
    (h2 : A * (1 + 2 * Real.pi) ^ 2 + B * (1 + 2 * Real.pi) + G = A + B + G) :
    A * Real.pi ^ 2 + B * Real.pi + G = G := by
  have hA : A = 0 := by
    have h4 : A * (4 * Real.pi) = 0 := by linear_combination h2 - h1
    rcases mul_eq_zero.1 h4 with h | h
    · exact h
    · linarith [Real.pi_pos]
  subst hA
  have hB : B = 0 := by
    have h4 : B * (2 * Real.pi) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h4 with h | h
    · exact h
    · linarith [Real.pi_pos]
  subst hB
  ring

theorem cosineTiltDensity_not_gaussian {a v : ℝ} (ha0 : a ≠ 0) (ha1 : |a| < 1) (hv : 0 < v)
    (m : ℝ) (w : NNReal) :
    volume.withDensity (fun z => ENNReal.ofReal (HRS.cosineTiltDensity a v z)) ≠
      gaussianReal m w := by
  intro heq
  have ha := abs_lt.mp ha1
  by_cases hw : w = 0
  · subst hw
    rw [gaussianReal_zero_var] at heq
    have h1 : (volume.withDensity fun z => ENNReal.ofReal (HRS.cosineTiltDensity a v z)) {m} =
        Measure.dirac m {m} := by rw [heq]
    rw [withDensity_apply _ (measurableSet_singleton m),
      setLIntegral_measure_zero _ _ Real.volume_singleton] at h1
    simp at h1
  · rw [gaussianReal_of_var_ne_zero m hw] at heq
    have he0 : 0 < Real.exp (-v / 2) := Real.exp_pos _
    have he1 : Real.exp (-v / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hc0 : 0 < 1 + a * Real.exp (-v / 2) := by
      nlinarith [mul_le_mul_of_nonneg_right (neg_abs_le a) he0.le,
        mul_le_of_le_one_right (abs_nonneg a) he1]
    have hcos : ∀ z : ℝ, 0 < 1 + a * Real.cos z := by
      intro z
      have h1 : |a * Real.cos z| ≤ |a| := by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg a) (Real.abs_cos_le_one _)
      have h2 := abs_le.mp h1
      linarith [h2.1]
    have hw' : (0 : ℝ) < (w : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hw)
    have hs1 : 0 < Real.sqrt (2 * Real.pi * v) :=
      Real.sqrt_pos.2 (mul_pos (mul_pos two_pos Real.pi_pos) hv)
    have hs2 : 0 < Real.sqrt (2 * Real.pi * (w : ℝ)) :=
      Real.sqrt_pos.2 (mul_pos (mul_pos two_pos Real.pi_pos) hw')
    have hcontT : Continuous (HRS.cosineTiltDensity a v) := by
      unfold HRS.cosineTiltDensity
      fun_prop
    have hcontG : Continuous (gaussianPDFReal m w) := by
      unfold gaussianPDFReal
      fun_prop
    have hmeasT : Measurable (fun z => ENNReal.ofReal (HRS.cosineTiltDensity a v z)) :=
      hcontT.measurable.ennreal_ofReal
    have hmeasG : Measurable (gaussianPDF m w) := hcontG.measurable.ennreal_ofReal
    have heqA := (withDensity_eq_iff_of_sigmaFinite hmeasT.aemeasurable
      hmeasG.aemeasurable).1 heq
    have nonT : ∀ z, 0 ≤ HRS.cosineTiltDensity a v z := fun z => by
      unfold HRS.cosineTiltDensity
      exact mul_nonneg (div_nonneg (hcos z).le hc0.le)
        (div_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))
    have nonG : ∀ z, 0 ≤ gaussianPDFReal m w z := fun z => by
      unfold gaussianPDFReal
      exact mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) (Real.exp_pos _).le
    have hae : (HRS.cosineTiltDensity a v) =ᵐ[volume] (gaussianPDFReal m w) := by
      filter_upwards [heqA] with z hz
      have hz' : ENNReal.ofReal (HRS.cosineTiltDensity a v z) =
          ENNReal.ofReal (gaussianPDFReal m w z) := hz
      exact (ENNReal.ofReal_eq_ofReal_iff (nonT z) (nonG z)).1 hz'
    have hfun : HRS.cosineTiltDensity a v = gaussianPDFReal m w :=
      (Continuous.ae_eq_iff_eq volume hcontT hcontG).1 hae
    have hpt : ∀ z, HRS.cosineTiltDensity a v z = gaussianPDFReal m w z :=
      fun z => congrFun hfun z
    -- multiplicative form: `1 + a cos z = C · e^{z²/(2v)} e^{-(z-m)²/(2w)}`
    obtain ⟨c0, hc0def⟩ : ∃ c0 : ℝ, c0 = 1 + a * Real.exp (-v / 2) := ⟨_, rfl⟩
    obtain ⟨s1, hs1def⟩ : ∃ s1 : ℝ, s1 = Real.sqrt (2 * Real.pi * v) := ⟨_, rfl⟩
    obtain ⟨s2, hs2def⟩ : ∃ s2 : ℝ, s2 = Real.sqrt (2 * Real.pi * (w : ℝ)) := ⟨_, rfl⟩
    have hc0' : 0 < c0 := by rw [hc0def]; exact hc0
    have hs1' : 0 < s1 := by rw [hs1def]; exact hs1
    have hs2' : 0 < s2 := by rw [hs2def]; exact hs2
    have hCpos : 0 < c0 * s1 * s2⁻¹ := mul_pos (mul_pos hc0' hs1') (inv_pos.2 hs2')
    have key : ∀ z : ℝ, 1 + a * Real.cos z =
        c0 * s1 * s2⁻¹ * Real.exp (z ^ 2 / (2 * v) - (z - m) ^ 2 / (2 * (w : ℝ))) := by
      intro z
      have hp := hpt z
      unfold HRS.cosineTiltDensity gaussianPDFReal at hp
      rw [← hc0def, ← hs1def, ← hs2def] at hp
      have hE12 : Real.exp (-z ^ 2 / (2 * v)) * Real.exp (z ^ 2 / (2 * v)) = 1 := by
        rw [← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero]
      have hsplit : Real.exp (z ^ 2 / (2 * v) - (z - m) ^ 2 / (2 * (w : ℝ))) =
          Real.exp (z ^ 2 / (2 * v)) * Real.exp (-(z - m) ^ 2 / (2 * (w : ℝ))) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hid : (1 + a * Real.cos z) * Real.exp (-z ^ 2 / (2 * v)) * (c0 * s1)⁻¹ =
          Real.exp (-(z - m) ^ 2 / (2 * (w : ℝ))) * s2⁻¹ := by
        linear_combination hp
      have hκ : c0 * s1 * (c0 * s1)⁻¹ = 1 := mul_inv_cancel₀ (mul_pos hc0' hs1').ne'
      have h5 : (c0 * s1)⁻¹ * (1 + a * Real.cos z) =
          s2⁻¹ * Real.exp (-(z - m) ^ 2 / (2 * (w : ℝ))) * Real.exp (z ^ 2 / (2 * v)) := by
        linear_combination Real.exp (z ^ 2 / (2 * v)) * hid - ((c0 * s1)⁻¹ * (1 + a * Real.cos z)) * hE12
      rw [hsplit]
      linear_combination (-(1 + a * Real.cos z)) * hκ + (c0 * s1) * h5
    have hlogq : ∀ z : ℝ, Real.log (1 + a * Real.cos z) =
        Real.log (c0 * s1 * s2⁻¹) +
          (z ^ 2 / (2 * v) - (z - m) ^ 2 / (2 * (w : ℝ))) := by
      intro z
      rw [key z, Real.log_mul hCpos.ne' (Real.exp_pos _).ne', Real.log_exp]
    obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 1 / (2 * v) - 1 / (2 * (w : ℝ)) := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B : ℝ, B = m / (w : ℝ) := ⟨_, rfl⟩
    obtain ⟨G, hG⟩ : ∃ G : ℝ, G = -m ^ 2 / (2 * (w : ℝ)) := ⟨_, rfl⟩
    have hq : ∀ z : ℝ, z ^ 2 / (2 * v) - (z - m) ^ 2 / (2 * (w : ℝ)) = A * z ^ 2 + B * z + G := by
      intro z
      rw [hA, hB, hG]
      ring
    have hlog' : ∀ z : ℝ, Real.log (1 + a * Real.cos z) =
        Real.log (c0 * s1 * s2⁻¹) + (A * z ^ 2 + B * z + G) := by
      intro z
      rw [hlogq z, hq z]
    have e1 : A * (2 * Real.pi) ^ 2 + B * (2 * Real.pi) + G = G := by
      have h1 := hlog' (2 * Real.pi)
      have h0 := hlog' 0
      rw [Real.cos_two_pi] at h1
      rw [Real.cos_zero] at h0
      linear_combination h0 - h1
    have e2 : A * (1 + 2 * Real.pi) ^ 2 + B * (1 + 2 * Real.pi) + G = A + B + G := by
      have h2 := hlog' (1 + 2 * Real.pi)
      have h1' := hlog' 1
      rw [Real.cos_add_two_pi] at h2
      linear_combination h1' - h2
    have haux := quad_eq_of_periodic A B G e1 e2
    have hpi := hlog' Real.pi
    have h0 := hlog' 0
    rw [Real.cos_pi] at hpi
    rw [Real.cos_zero] at h0
    have hfin : Real.log (1 + a * -1) = Real.log (1 + a * 1) := by
      linear_combination hpi - h0 + haux
    have hp1 : (0 : ℝ) < 1 + a * -1 := by linarith
    have hp2 : (0 : ℝ) < 1 + a * 1 := by linarith
    have hinj := Real.log_injOn_pos (Set.mem_Ioi.2 hp1) (Set.mem_Ioi.2 hp2) hfin
    exact ha0 (by linarith)

end HRS.ME.TiltBounds
