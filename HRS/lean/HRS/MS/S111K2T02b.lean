import HRS.Whole.Static
import HRS.MS.R2PolyAux1

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.S111K2
open HRS HRS.Whole
variable {d : ℕ}

theorem s111k2_double (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (M c : ℝ) (hc : 0 < c)
    {Pw : ℝ} (hPw : 0 ≤ Pw) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M * Real.exp (-c * ‖x‖ ^ 2)) →
      ∫⁻ p : Euc d × Euc d, ENNReal.ofReal ((1 + ‖p.1‖) ^ (2 * Pw) * (1 + ‖p.2‖) ^ (2 * Pw) *
        (1 + rieszWeight s (p.1 - p.2)) ^ 2) ∂((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)) ≤
          ENNReal.ofReal K := by
  obtain ⟨C1, hC1, hmom⟩ := HRS.MS.R2Poly.s95_moment d M c hc hPw
  obtain ⟨Cp, hCp, hpow⟩ := HRS.MS.R2Poly.s95_pow_le_exp (a := 2 * Pw) (by positivity) (ε := 1) one_pos
  set Cm : ℝ := 2 ^ Pw * C1 with hCm
  set Mt : ℝ := max M 0 * Cp * Real.exp (1 / (4 * c)) with hMt
  obtain ⟨A, hA0, hrow⟩ := HRS.MS.R2Poly.s95_row_sq (d := d) (by omega) hs0 hs Mt
  have hCm0 : 0 ≤ Cm := by positivity
  refine ⟨Cm * (Cm * A), by positivity, fun ρ hρ hG => ?_⟩
  set a : Euc d → ℝ := fun y => (1 + ‖y‖) ^ (2 * Pw) with ha
  have ha_pos : ∀ y, 1 ≤ a y := fun y =>
    Real.one_le_rpow (by linarith [norm_nonneg y]) (by positivity)
  have ha_meas : Measurable a := (measurable_const.add measurable_norm).pow_const _
  have ha_le : ∀ y, a y ≤ 2 ^ Pw * (jbracket y ^ Pw) ^ 2 := by
    intro y
    have hjb := HRS.MS.R2Poly.s95_one_le_jb y
    have h1 : (1 + ‖y‖) ^ 2 ≤ 2 * jbracket y ^ 2 := by
      rw [HRS.MS.R2Poly.s95_jb_sq]; nlinarith [sq_nonneg (1 - ‖y‖), norm_nonneg y]
    calc a y = ((1 + ‖y‖) ^ 2) ^ Pw := by
          rw [ha]; simp only; rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith [norm_nonneg y])]
          norm_num
      _ ≤ (2 * jbracket y ^ 2) ^ Pw := Real.rpow_le_rpow (by positivity) h1 hPw
      _ = 2 ^ Pw * (jbracket y ^ Pw) ^ 2 := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast (jbracket y ^ Pw) 2,
            ← Real.rpow_mul (by linarith), ← Real.rpow_natCast (jbracket y) 2, ← Real.rpow_mul (by linarith)]
          try (congr 2; push_cast; ring)
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  -- moment of the weight
  have hmom' : ∫⁻ y, ENNReal.ofReal (a y) ∂μ ≤ ENNReal.ofReal Cm := by
    calc ∫⁻ y, ENNReal.ofReal (a y) ∂μ
        ≤ ∫⁻ y, ENNReal.ofReal (2 ^ Pw) * ENNReal.ofReal ((jbracket y ^ Pw) ^ 2) ∂μ := by
          refine lintegral_mono fun y => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal (ha_le y)
      _ = ENNReal.ofReal (2 ^ Pw) * ∫⁻ y, ENNReal.ofReal ((jbracket y ^ Pw) ^ 2) ∂μ :=
          lintegral_const_mul _ (ENNReal.measurable_ofReal.comp
            ((HRS.MS.R2Poly.s95_jb_meas.pow_const Pw).pow_const 2))
      _ ≤ ENNReal.ofReal (2 ^ Pw) * ENNReal.ofReal C1 := by
          gcongr; exact hmom ρ hρ hG
      _ = ENNReal.ofReal Cm := by rw [hCm, ENNReal.ofReal_mul (by positivity)]
  -- the weighted mass
  have hI : ∫⁻ y, ENNReal.ofReal (ρ y * a y) = ∫⁻ y, ENNReal.ofReal (a y) ∂μ := by
    have := HRS.Whole.Q34.lintegral_nu hρ (fun y => ENNReal.ofReal (a y))
      (ENNReal.measurable_ofReal.comp ha_meas)
    rw [this]
    refine lintegral_congr fun y => ?_
    rw [ENNReal.ofReal_mul (hρ.nonneg y)]
  have hρa_meas : Measurable fun y => ρ y * a y := hρ.measurable.mul ha_meas
  have hint : Integrable (fun y => ρ y * a y) := by
    rw [← lintegral_ofReal_ne_top_iff_integrable hρa_meas.aestronglyMeasurable
      (Eventually.of_forall fun y => mul_nonneg (hρ.nonneg y) (by linarith [ha_pos y]))]
    rw [hI]; exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmom'
  set Z : ℝ := ∫ y, ρ y * a y with hZ
  have hZeq : ENNReal.ofReal Z = ∫⁻ y, ENNReal.ofReal (a y) ∂μ := by
    rw [hZ, ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun y => mul_nonneg (hρ.nonneg y) (by linarith [ha_pos y])), hI]
  have hZle : Z ≤ Cm := by
    have := hZeq ▸ hmom'
    exact (ENNReal.ofReal_le_ofReal_iff hCm0).1 this
  have hρint : Integrable ρ := by
    by_contra h
    have : ∫ y, ρ y = 0 := integral_undef h
    rw [hρ.integral_one] at this; norm_num at this
  have hZge : 1 ≤ Z := by
    rw [← hρ.integral_one]
    exact integral_mono hρint hint fun y => by
      have := ha_pos y; nlinarith [hρ.nonneg y]
  have hZpos : 0 < Z := by linarith
  -- the weighted probability density
  set ρt : Euc d → ℝ := fun y => ρ y * a y / Z with hρt
  have hρt_nn : ∀ y, 0 ≤ ρt y := fun y =>
    div_nonneg (mul_nonneg (hρ.nonneg y) (by linarith [ha_pos y])) hZpos.le
  have hρtP : HRS.Whole.IsProbDensity ρt :=
    ⟨hρt_nn, hρa_meas.div_const Z, by
      simp only [hρt]; rw [integral_div, ← hZ]; exact div_self hZpos.ne'⟩
  have hρt_le : ∀ y, ρt y ≤ Mt := by
    intro y
    have h1 : ρt y ≤ ρ y * a y := by
      have : ρ y * a y ≤ ρ y * a y * Z := le_mul_of_one_le_right
        (mul_nonneg (hρ.nonneg y) (by linarith [ha_pos y])) hZge
      calc ρt y = ρ y * a y / Z := rfl
        _ ≤ ρ y * a y := div_le_self (mul_nonneg (hρ.nonneg y) (by linarith [ha_pos y])) hZge
    have h2 : a y ≤ Cp * Real.exp (1 * ‖y‖) := hpow ‖y‖ (norm_nonneg y)
    have h3 : ρ y * a y ≤ max M 0 * Real.exp (-c * ‖y‖ ^ 2) * (Cp * Real.exp (1 * ‖y‖)) := by
      refine mul_le_mul ?_ h2 (by linarith [ha_pos y]) (by positivity)
      exact (hG y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    have h4 : Real.exp (-c * ‖y‖ ^ 2) * Real.exp (1 * ‖y‖) ≤ Real.exp (1 / (4 * c)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have : 0 ≤ c * (‖y‖ - 1 / (2 * c)) ^ 2 := by positivity
      have e : c * (‖y‖ - 1 / (2 * c)) ^ 2 = c * ‖y‖ ^ 2 - ‖y‖ + 1 / (4 * c) := by
        field_simp; ring
      linarith
    calc ρt y ≤ max M 0 * Real.exp (-c * ‖y‖ ^ 2) * (Cp * Real.exp (1 * ‖y‖)) := h1.trans h3
      _ = max M 0 * Cp * (Real.exp (-c * ‖y‖ ^ 2) * Real.exp (1 * ‖y‖)) := by ring
      _ ≤ max M 0 * Cp * Real.exp (1 / (4 * c)) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρt) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hρtP
  set q : Euc d → Euc d → ℝ := fun x y => (1 + HRS.Whole.rieszWeight s (x - y)) ^ 2 with hq
  have hqm : ∀ x, Measurable (fun y => q x y) := fun x => by
    have := (measurable_const.add ((HRS.MS.Wr.wr3_measurable_rieszWeight s).comp
      (measurable_const.sub measurable_id)) : Measurable fun y : Euc d => 1 + HRS.Whole.rieszWeight s (x - y))
    exact this.pow_const 2
  have hqnn : ∀ x y, 0 ≤ q x y := fun x y => sq_nonneg _
  -- inner integral
  have hinner : ∀ x, ∫⁻ y, ENNReal.ofReal (a y) * ENNReal.ofReal (q x y) ∂μ ≤
      ENNReal.ofReal (Z * A) := by
    intro x
    have hH : Measurable fun y => ENNReal.ofReal (a y) * ENNReal.ofReal (q x y) :=
      (ENNReal.measurable_ofReal.comp ha_meas).mul (ENNReal.measurable_ofReal.comp (hqm x))
    rw [hμ, HRS.Whole.Q34.lintegral_nu hρ _ hH]
    have h2 := HRS.Whole.Q34.lintegral_nu hρtP (fun y => ENNReal.ofReal (q x y))
      (ENNReal.measurable_ofReal.comp (hqm x))
    have hpt : ∀ y, ENNReal.ofReal (ρ y) * (ENNReal.ofReal (a y) * ENNReal.ofReal (q x y)) =
        ENNReal.ofReal Z * (ENNReal.ofReal (ρt y) * ENNReal.ofReal (q x y)) := by
      intro y
      have : ρ y * a y = Z * ρt y := by simp only [hρt]; field_simp
      rw [← mul_assoc, ← ENNReal.ofReal_mul (hρ.nonneg y), this, ENNReal.ofReal_mul hZpos.le,
        mul_assoc]
    simp_rw [hpt]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← h2, ENNReal.ofReal_mul hZpos.le]
    exact mul_le_mul' le_rfl (hrow ρt hρtP hρt_le x)
  have hqpair : Measurable fun p : Euc d × Euc d => q p.1 p.2 :=
    (measurable_const.add ((HRS.MS.Wr.wr3_measurable_rieszWeight s).comp
      (measurable_fst.sub measurable_snd))).pow_const 2
  have hint2 : ∀ p : Euc d × Euc d, ENNReal.ofReal ((1 + ‖p.1‖) ^ (2 * Pw) * (1 + ‖p.2‖) ^ (2 * Pw) *
      (1 + HRS.Whole.rieszWeight s (p.1 - p.2)) ^ 2) =
      ENNReal.ofReal (a p.1) * (ENNReal.ofReal (a p.2) * ENNReal.ofReal (q p.1 p.2)) := by
    intro p
    rw [← ENNReal.ofReal_mul (show 0 ≤ a p.2 by linarith [ha_pos p.2]),
      ← ENNReal.ofReal_mul (show 0 ≤ a p.1 by linarith [ha_pos p.1])]
    congr 1; simp only [ha, hq]; ring
  simp_rw [hint2]
  have hmf : Measurable fun p : Euc d × Euc d =>
      ENNReal.ofReal (a p.1) * (ENNReal.ofReal (a p.2) * ENNReal.ofReal (q p.1 p.2)) :=
    (ENNReal.measurable_ofReal.comp (ha_meas.comp measurable_fst)).mul
      ((ENNReal.measurable_ofReal.comp (ha_meas.comp measurable_snd)).mul
        (ENNReal.measurable_ofReal.comp hqpair))
  rw [lintegral_prod _ hmf.aemeasurable]
  calc ∫⁻ x, ∫⁻ y, ENNReal.ofReal (a x) * (ENNReal.ofReal (a y) * ENNReal.ofReal (q x y)) ∂μ ∂μ
      ≤ ∫⁻ x, ENNReal.ofReal (a x) * ENNReal.ofReal (Z * A) ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact mul_le_mul' le_rfl (hinner x)
    _ = (∫⁻ x, ENNReal.ofReal (a x) ∂μ) * ENNReal.ofReal (Z * A) :=
        lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal Cm * ENNReal.ofReal (Z * A) := mul_le_mul' hmom' le_rfl
    _ = ENNReal.ofReal (Cm * (Z * A)) := (ENNReal.ofReal_mul hCm0).symm
    _ ≤ ENNReal.ofReal (Cm * (Cm * A)) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hZle hA0) hCm0

end HRS.MS.S111K2
