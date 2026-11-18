import HRS.MS.WhoAux2
import HRS.MS.UlTail

/-!
# S54 part 3: weighted bounds for the Riesz-type convolution operator `ultK` and the splitting of the nonlocal term

* `who_ultK_wSq`: `wSq P (ultK κ g) ≤ C (wSq P g + ‖g‖_{L¹}² ∫ ⟨x⟩^{-2P})` for a kernel `κ` with `|κ(z)| ≲ |z|^{-(s+1)}`, `s + 1 < d`
  (near part: weighted Young with an `L¹` kernel; far part: bounded kernel against `L¹`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff Matrix

namespace HRS.MS.Who

open HRS HRS.Whole HRS.MS.Ul

variable {d : ℕ}

theorem who_sq_add_le (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  have := ENNReal.rpow_add_le_mul_rpow_add_rpow a b (p := 2) (by norm_num)
  have h : (2:ℝ) - 1 = 1 := by norm_num
  rw [h, ENNReal.rpow_one] at this
  simpa [ENNReal.rpow_two] using this

theorem who_sq_add3_le (a b c : ℝ≥0∞) : (a + b + c) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  calc (a + b + c) ^ 2 ≤ 2 * ((a + b) ^ 2 + c ^ 2) := who_sq_add_le _ _
    _ ≤ 2 * (2 * (a ^ 2 + b ^ 2) + c ^ 2) := by gcongr; exact who_sq_add_le _ _
    _ ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2) := by
        have : 2 * (2 * (a ^ 2 + b ^ 2) + c ^ 2) = 4 * (a ^ 2 + b ^ 2) + 2 * c ^ 2 := by ring
        rw [this]
        calc 4 * (a ^ 2 + b ^ 2) + 2 * c ^ 2 ≤ 4 * (a ^ 2 + b ^ 2) + 4 * c ^ 2 := by gcongr; norm_num
          _ = _ := by ring

/-- Cauchy-Schwarz against a density: `(∫ a b)² ≤ (∫ a)(∫ a b²)` -/
theorem who_cs_density {α : Type*} [MeasurableSpace α] {μ : Measure α} {a b : α → ℝ≥0∞}
    (ha : Measurable a) (hb : Measurable b) :
    (∫⁻ x, a x * b x ∂μ) ^ 2 ≤ (∫⁻ x, a x ∂μ) * ∫⁻ x, a x * b x ^ 2 ∂μ := by
  have h := who_cs_lintegral (μ := μ) (f := fun x => a x ^ (1 / 2 : ℝ))
    (g := fun x => a x ^ (1 / 2 : ℝ) * b x) (ha.pow_const _).aemeasurable
    ((ha.pow_const _).mul hb).aemeasurable
  have e1 : ∀ x, a x ^ (1 / 2 : ℝ) * (a x ^ (1 / 2 : ℝ) * b x) = a x * b x := fun x => by
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have e2 : ∀ x, (a x ^ (1 / 2 : ℝ)) ^ 2 = a x := fun x => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  have e3 : ∀ x, (a x ^ (1 / 2 : ℝ) * b x) ^ 2 = a x * b x ^ 2 := fun x => by
    rw [mul_pow, e2]
  simp only [e1, e2, e3] at h
  exact h


theorem who_ofReal_abs_integral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) :
    ENNReal.ofReal |∫ x, f x ∂μ| ≤ ∫⁻ x, ENNReal.ofReal |f x| ∂μ := by
  by_cases hm : AEStronglyMeasurable f μ
  · have h1 : |∫ x, f x ∂μ| ≤ ∫ x, |f x| ∂μ := by
      have := norm_integral_le_integral_norm (μ := μ) f
      simpa [Real.norm_eq_abs] using this
    refine (ENNReal.ofReal_le_ofReal h1).trans ?_
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun w => abs_nonneg _)
      (by simpa [Real.norm_eq_abs] using hm.norm)]
    exact ENNReal.ofReal_toReal_le
  · rw [integral_undef (fun h => hm h.1)]
    simp

/-- the `L¹` mass of the near kernel -/
def nearMass (κ : Euc d → ℝ) : ℝ≥0∞ := ∫⁻ z, ENNReal.ofReal |ultKN κ z|

theorem who_nearMass_lt_top (hd : 1 ≤ d) {κ : Euc d → ℝ} {s : ℝ} (hK : UlKer κ s) (hs1 : s + 1 < d) :
    nearMass κ < ⊤ := by
  obtain ⟨C0, hC0, hb⟩ := ult_ker_bound hK
  have hint : IntegrableOn (fun z : Euc d => ‖z‖ ^ (-(s + 1))) (Metric.ball (0 : Euc d) 1) volume :=
    u2_integrableOn_ball_rpow hd (by linarith [hK.hs0]) hs1
  have h2 : Integrable ((Metric.ball (0 : Euc d) 1).indicator (fun z : Euc d => C0 * ‖z‖ ^ (-(s + 1)))) volume := by
    exact (integrable_indicator_iff measurableSet_ball).2 (hint.const_mul C0)
  have h3 : ∀ᵐ z : Euc d, ‖ultKN κ z‖ ≤ (Metric.ball (0 : Euc d) 1).indicator (fun z : Euc d => C0 * ‖z‖ ^ (-(s + 1))) z := by
    filter_upwards [u2_ae_ne_zero hd] with z hz
    by_cases h : ‖z‖ ≤ 1 / 4
    · have hzb : z ∈ Metric.ball (0 : Euc d) 1 := by
        rw [mem_ball_zero_iff]; linarith
      rw [Set.indicator_of_mem hzb]
      simp only [ultKN, h, if_true]
      exact hb z hz
    · simp only [ultKN, h, if_false, norm_zero]
      exact Set.indicator_nonneg (fun z _ => by positivity) z
  have := (h2.mono' (ultKN_meas hK.meas).aestronglyMeasurable h3)
  unfold nearMass
  exact this.abs.lintegral_lt_top


theorem who_ofReal_norm_integral_le {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (μ : Measure α) (f : α → F) :
    ENNReal.ofReal ‖∫ x, f x ∂μ‖ ≤ ∫⁻ x, ENNReal.ofReal ‖f x‖ ∂μ := by
  have := enorm_integral_le_lintegral_enorm (μ := μ) f
  simpa [ofReal_norm_eq_enorm] using this

theorem who_ultK_pt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {κ : Euc d → ℝ} {s : ℝ}
    (hK : UlKer κ s) :
    ∃ BF : ℝ, 0 ≤ BF ∧ ∀ {g : Euc d → F}, Continuous g → ∀ x : Euc d,
      ENNReal.ofReal ‖ultK κ g x‖ ≤
        (∫⁻ z, ENNReal.ofReal |ultKN κ z| * ENNReal.ofReal ‖g (x - z)‖) +
          nearMass κ * ENNReal.ofReal ‖g x‖ + ENNReal.ofReal BF * ∫⁻ y, ENNReal.ofReal ‖g y‖ := by
  obtain ⟨C0, hC0, hb⟩ := ult_ker_bound hK
  refine ⟨C0 * (1 / 4 : ℝ) ^ (-(s + 1)), by positivity, fun {g} hg x => ?_⟩
  have hKN := ultKN_meas hK.meas
  have hgn : Measurable fun y => ‖g y‖ := hg.norm.measurable
  unfold ultK
  have h1 : ENNReal.ofReal ‖ultNear κ g x‖ ≤
      (∫⁻ z, ENNReal.ofReal |ultKN κ z| * ENNReal.ofReal ‖g (x - z)‖) +
        nearMass κ * ENNReal.ofReal ‖g x‖ := by
    refine (who_ofReal_norm_integral_le volume _).trans ?_
    calc ∫⁻ z, ENNReal.ofReal ‖ultKN κ z • (g (x - z) - g x)‖
        ≤ ∫⁻ z, (ENNReal.ofReal |ultKN κ z| * ENNReal.ofReal ‖g (x - z)‖ +
            ENNReal.ofReal |ultKN κ z| * ENNReal.ofReal ‖g x‖) := by
          refine lintegral_mono fun z => ?_
          rw [← mul_add, norm_smul, Real.norm_eq_abs, ENNReal.ofReal_mul (abs_nonneg _)]
          gcongr
          rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (norm_sub_le _ _)
      _ = _ := by
          rw [lintegral_add_left (by
            exact (hKN.abs.ennreal_ofReal).mul ((hgn.comp (measurable_const.sub measurable_id)).ennreal_ofReal)),
            lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
          rfl
  have h2 : ENNReal.ofReal ‖u2Conv (ultKF κ) g x‖ ≤
      ENNReal.ofReal (C0 * (1 / 4 : ℝ) ^ (-(s + 1))) * ∫⁻ y, ENNReal.ofReal ‖g y‖ := by
    refine (who_ofReal_norm_integral_le volume _).trans ?_
    calc ∫⁻ z, ENNReal.ofReal ‖ultKF κ z • g (x - z)‖
        ≤ ∫⁻ z, ENNReal.ofReal (C0 * (1 / 4 : ℝ) ^ (-(s + 1))) * ENNReal.ofReal ‖g (x - z)‖ := by
          refine lintegral_mono fun z => ?_
          rw [norm_smul, Real.norm_eq_abs, ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal (mul_le_mul ?_ le_rfl (norm_nonneg _) (by positivity))
          simpa [Real.norm_eq_abs] using ult_far_bound hC0 hb hK.hs0 z
      _ = _ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          exact lintegral_sub_left_eq_self (fun y => ENNReal.ofReal ‖g y‖) x
  calc ENNReal.ofReal ‖ultNear κ g x + u2Conv (ultKF κ) g x‖
      ≤ ENNReal.ofReal ‖ultNear κ g x‖ + ENNReal.ofReal ‖u2Conv (ultKF κ) g x‖ := by
        rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (norm_add_le _ _)
    _ ≤ _ := add_le_add h1 h2

theorem who_wSq_eq_sq (P : ℝ) (G : Euc d → ℝ) (hG : ∀ x, 0 ≤ G x) :
    wSq P G = ∫⁻ x, ENNReal.ofReal (wt P x) * ENNReal.ofReal (G x) ^ 2 := by
  unfold wSq
  refine lintegral_congr fun x => ?_
  rw [← ENNReal.ofReal_pow (hG x), ← ENNReal.ofReal_mul (who_wt_pos P x).le]

/-- the near term in the weighted norm -/
theorem who_near_wSq (hd : 1 ≤ d) {P : ℝ} (hP : 0 ≤ P) {κ : Euc d → ℝ} {s : ℝ} (hK : UlKer κ s)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : Euc d → F} (hg : Continuous g) :
    ∫⁻ x, ENNReal.ofReal (wt P x) *
        (∫⁻ z, ENNReal.ofReal |ultKN κ z| * ENNReal.ofReal ‖g (x - z)‖) ^ 2 ≤
      nearMass κ ^ 2 * ENNReal.ofReal (4 ^ P) * wSq P (fun x => ‖g x‖) := by
  have hKN := ultKN_meas hK.meas
  have hgn : Measurable fun y => ‖g y‖ := hg.norm.measurable
  have hmeas : Measurable (Function.uncurry fun (x z : Euc d) =>
      ENNReal.ofReal (wt P x) * (ENNReal.ofReal |ultKN κ z| * ENNReal.ofReal ‖g (x - z)‖ ^ 2)) := by
    refine ((ENNReal.measurable_ofReal.comp (who_wt_meas P)).comp measurable_fst).mul ?_
    refine ((ENNReal.measurable_ofReal.comp hKN.abs).comp measurable_snd).mul ?_
    exact (((ENNReal.measurable_ofReal.comp hgn).comp
      (measurable_fst.sub measurable_snd))).pow_const 2
  calc ∫⁻ x, ENNReal.ofReal (wt P x) *
        (∫⁻ z, ENNReal.ofReal |ultKN κ z| * ENNReal.ofReal ‖g (x - z)‖) ^ 2
      ≤ ∫⁻ x, ENNReal.ofReal (wt P x) * (nearMass κ *
          ∫⁻ z, ENNReal.ofReal |ultKN κ z| * ENNReal.ofReal ‖g (x - z)‖ ^ 2) := by
        refine lintegral_mono fun x => ?_
        refine mul_le_mul' le_rfl ?_
        exact who_cs_density (μ := volume) (a := fun z => ENNReal.ofReal |ultKN κ z|)
          (b := fun z => ENNReal.ofReal ‖g (x - z)‖) hKN.abs.ennreal_ofReal
          ((hgn.comp (measurable_const.sub measurable_id)).ennreal_ofReal)
    _ = nearMass κ * ∫⁻ z, ENNReal.ofReal |ultKN κ z| *
          ∫⁻ x, ENNReal.ofReal (wt P x) * ENNReal.ofReal ‖g (x - z)‖ ^ 2 := by
        have h1 : ∀ x : Euc d, ENNReal.ofReal (wt P x) * (nearMass κ *
            ∫⁻ z, ENNReal.ofReal |ultKN κ z| * ENNReal.ofReal ‖g (x - z)‖ ^ 2) =
            nearMass κ * ∫⁻ z, ENNReal.ofReal (wt P x) *
              (ENNReal.ofReal |ultKN κ z| * ENNReal.ofReal ‖g (x - z)‖ ^ 2) := fun x => by
          rw [mul_left_comm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        simp_rw [h1]
        have hm2 : Measurable fun x : Euc d => ∫⁻ z, ENNReal.ofReal (wt P x) *
            (ENNReal.ofReal |ultKN κ z| * ENNReal.ofReal ‖g (x - z)‖ ^ 2) := hmeas.lintegral_prod_right'
        rw [lintegral_const_mul _ hm2]
        congr 1
        rw [lintegral_lintegral_swap hmeas.aemeasurable]
        refine lintegral_congr fun z => ?_
        simp_rw [mul_left_comm (ENNReal.ofReal (wt P _))]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ nearMass κ * ∫⁻ z, ENNReal.ofReal |ultKN κ z| * (ENNReal.ofReal (4 ^ P) * wSq P (fun x => ‖g x‖)) := by
        refine mul_le_mul' le_rfl (lintegral_mono fun z => ?_)
        by_cases hz : ‖z‖ ≤ 1 / 4
        · refine mul_le_mul' le_rfl ?_
          have h1 := who_wSq_shift hP (fun x => ‖g x‖) z
          have h2 : wSq P (fun x => ‖g (x - z)‖) = ∫⁻ x, ENNReal.ofReal (wt P x) *
              ENNReal.ofReal ‖g (x - z)‖ ^ 2 := who_wSq_eq_sq P _ (fun x => norm_nonneg _)
          rw [← h2]
          refine h1.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
          have hjb : jbracket z ^ (2 * P) = (1 + ‖z‖ ^ 2) ^ P := by
            rw [show 2 * P = (2 : ℕ) * P by push_cast; ring, Real.rpow_mul (who_jb_pos _).le,
              Real.rpow_natCast, who_jb_sq]
          rw [hjb]
          have h3 : (1 + ‖z‖ ^ 2) ^ P ≤ 2 ^ P :=
            Real.rpow_le_rpow (by positivity) (by nlinarith [norm_nonneg z]) hP
          calc 2 ^ P * (1 + ‖z‖ ^ 2) ^ P ≤ 2 ^ P * 2 ^ P := by gcongr
            _ = 4 ^ P := by
              rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
        · have h0 : ultKN κ z = 0 := by unfold ultKN; exact if_neg hz
          rw [h0]; simp
    _ = _ := by
        rw [lintegral_mul_const _ hKN.abs.ennreal_ofReal]
        show nearMass κ * (nearMass κ * (ENNReal.ofReal (4 ^ P) * wSq P (fun x => ‖g x‖))) = _
        ring


/-- **weighted bound for the cancellation convolution** -/
theorem who_ultK_wSq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (hd : 1 ≤ d) {P : ℝ} (hP : 0 ≤ P) (hPd : (d : ℝ) / 2 < P) {κ : Euc d → ℝ} {s : ℝ}
    (hK : UlKer κ s) (hs1 : s + 1 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : Euc d → F}, Continuous g →
      wSq P (fun x => ‖ultK κ g x‖) ≤ ENNReal.ofReal C *
        (wSq P (fun x => ‖g x‖) + (∫⁻ y, ENNReal.ofReal ‖g y‖) ^ 2 * wtMass (d := d) P) := by
  obtain ⟨BF, hBF0, hpt⟩ := who_ultK_pt (F := F) hK
  have hnm := who_nearMass_lt_top hd hK hs1
  set a : ℝ := (nearMass κ).toReal with ha
  have hna : nearMass κ = ENNReal.ofReal a := (ENNReal.ofReal_toReal hnm.ne).symm
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  refine ⟨4 * (a ^ 2 * 4 ^ P + a ^ 2 + BF ^ 2), by positivity, fun {g} hg => ?_⟩
  have hKN := ultKN_meas hK.meas
  have hgn : Measurable fun y => ‖g y‖ := hg.norm.measurable
  have hT1m : Measurable fun x : Euc d => ∫⁻ z, ENNReal.ofReal |ultKN κ z| * ENNReal.ofReal ‖g (x - z)‖ := by
    have : Measurable (Function.uncurry fun (x z : Euc d) =>
        ENNReal.ofReal |ultKN κ z| * ENNReal.ofReal ‖g (x - z)‖) :=
      (((ENNReal.measurable_ofReal.comp hKN.abs).comp measurable_snd).mul
        ((ENNReal.measurable_ofReal.comp hgn).comp (measurable_fst.sub measurable_snd)))
    exact this.lintegral_prod_right'
  set L : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal ‖g y‖ with hL
  set T1 : Euc d → ℝ≥0∞ := fun x => ∫⁻ z, ENNReal.ofReal |ultKN κ z| * ENNReal.ofReal ‖g (x - z)‖ with hT1
  rw [who_wSq_eq_sq P _ (fun x => norm_nonneg _)]
  calc ∫⁻ x, ENNReal.ofReal (wt P x) * ENNReal.ofReal ‖ultK κ g x‖ ^ 2
      ≤ ∫⁻ x, ENNReal.ofReal (wt P x) * (4 * (T1 x ^ 2 + (nearMass κ * ENNReal.ofReal ‖g x‖) ^ 2 +
          (ENNReal.ofReal BF * L) ^ 2)) := by
        refine lintegral_mono fun x => ?_
        refine mul_le_mul' le_rfl ((pow_le_pow_left' (hpt hg x) 2).trans (who_sq_add3_le _ _ _))
    _ = 4 * ((∫⁻ x, ENNReal.ofReal (wt P x) * T1 x ^ 2) +
          (∫⁻ x, ENNReal.ofReal (wt P x) * (nearMass κ * ENNReal.ofReal ‖g x‖) ^ 2) +
          ∫⁻ x, ENNReal.ofReal (wt P x) * (ENNReal.ofReal BF * L) ^ 2) := by
        have hwm : Measurable fun x : Euc d => ENNReal.ofReal (wt P x) :=
          ENNReal.measurable_ofReal.comp (who_wt_meas P)
        have hf1 : Measurable fun x : Euc d => ENNReal.ofReal (wt P x) * T1 x ^ 2 :=
          hwm.mul (hT1m.pow_const 2)
        have hf2 : Measurable fun x : Euc d => ENNReal.ofReal (wt P x) *
            (nearMass κ * ENNReal.ofReal ‖g x‖) ^ 2 :=
          hwm.mul ((measurable_const.mul (ENNReal.measurable_ofReal.comp hgn)).pow_const 2)
        calc ∫⁻ x, ENNReal.ofReal (wt P x) * (4 * (T1 x ^ 2 + (nearMass κ * ENNReal.ofReal ‖g x‖) ^ 2 +
              (ENNReal.ofReal BF * L) ^ 2))
            = ∫⁻ x, 4 * (ENNReal.ofReal (wt P x) * T1 x ^ 2 +
                ENNReal.ofReal (wt P x) * (nearMass κ * ENNReal.ofReal ‖g x‖) ^ 2 +
                ENNReal.ofReal (wt P x) * (ENNReal.ofReal BF * L) ^ 2) :=
              lintegral_congr fun x => by ring
          _ = 4 * ∫⁻ x, (ENNReal.ofReal (wt P x) * T1 x ^ 2 +
                ENNReal.ofReal (wt P x) * (nearMass κ * ENNReal.ofReal ‖g x‖) ^ 2 +
                ENNReal.ofReal (wt P x) * (ENNReal.ofReal BF * L) ^ 2) :=
              lintegral_const_mul' _ _ (by norm_num)
          _ = _ := by
              congr 1
              rw [lintegral_add_left (f := fun x => ENNReal.ofReal (wt P x) * T1 x ^ 2 +
                ENNReal.ofReal (wt P x) * (nearMass κ * ENNReal.ofReal ‖g x‖) ^ 2) (hf1.add hf2),
                lintegral_add_left hf1]
    _ ≤ 4 * (nearMass κ ^ 2 * ENNReal.ofReal (4 ^ P) * wSq P (fun x => ‖g x‖) + nearMass κ ^ 2 * wSq P (fun x => ‖g x‖) +
          ENNReal.ofReal BF ^ 2 * L ^ 2 * wtMass P) := by
        gcongr
        · exact who_near_wSq hd hP hK hg
        · rw [who_wSq_eq_sq P _ (fun x => norm_nonneg _), ← lintegral_const_mul' _ _ (ENNReal.pow_ne_top hnm.ne)]
          refine le_of_eq (lintegral_congr fun x => ?_)
          rw [mul_pow]; ring
        · have hwm : Measurable fun x : Euc d => ENNReal.ofReal (wt P x) :=
            ENNReal.measurable_ofReal.comp (who_wt_meas P)
          rw [lintegral_mul_const _ hwm]
          exact le_of_eq (by unfold wtMass; rw [mul_pow]; ring)
    _ ≤ _ := by
        have eC : ENNReal.ofReal (4 * (a ^ 2 * 4 ^ P + a ^ 2 + BF ^ 2)) =
            4 * (nearMass κ ^ 2 * ENNReal.ofReal (4 ^ P) + nearMass κ ^ 2 + ENNReal.ofReal BF ^ 2) := by
          rw [hna, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_pow ha0, ENNReal.ofReal_pow hBF0]
          norm_num
        rw [eC]
        set W := wSq P (fun x => ‖g x‖)
        set Q := L ^ 2 * wtMass (d := d) P
        set X := nearMass κ ^ 2 * ENNReal.ofReal (4 ^ P)
        set Y := nearMass κ ^ 2
        set Z := ENNReal.ofReal BF ^ 2
        have e1 : Z * L ^ 2 * wtMass (d := d) P = Z * Q := by simp only [Q]; ring
        calc 4 * (X * W + Y * W + Z * L ^ 2 * wtMass P) = 4 * (X * W + Y * W + Z * Q) := by rw [e1]
          _ ≤ 4 * (X * W + Y * W + Z * Q + (Z * W + X * Q + Y * Q)) := by
              exact mul_le_mul' le_rfl le_self_add
          _ = 4 * (X + Y + Z) * (W + Q) := by ring

end HRS.MS.Who
