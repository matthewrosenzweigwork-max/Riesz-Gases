import HRS.Whole.Q34Aux3

/-!
# Packet Q34, helper file 4: sup bound for `g * f` with `|f| ≤ B`, `‖f‖₁ ≤ ε`
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace HRS.Whole.Q34

variable {d : ℕ}

theorem abs_integral_le_of_lintegral_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : α → ℝ} (hF : AEStronglyMeasurable F μ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∫⁻ a, ENNReal.ofReal |F a| ∂μ ≤ ENNReal.ofReal c) :
    Integrable F μ ∧ |∫ a, F a ∂μ| ≤ c := by
  have hlt : ∫⁻ a, ENNReal.ofReal |F a| ∂μ < ∞ := h.trans_lt ENNReal.ofReal_lt_top
  have hI : Integrable F μ := by
    refine ⟨hF, ?_⟩
    simp only [HasFiniteIntegral, Real.enorm_eq_ofReal_abs]
    exact hlt
  refine ⟨hI, ?_⟩
  have h1 : |∫ a, F a ∂μ| ≤ ∫ a, |F a| ∂μ := by
    have := norm_integral_le_integral_norm (μ := μ) F
    simpa [Real.norm_eq_abs] using this
  refine h1.trans ?_
  have hFa : AEStronglyMeasurable (fun a => |F a|) μ := by simpa [Real.norm_eq_abs] using hF.norm
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun a => abs_nonneg (F a))
    hFa]
  exact ENNReal.toReal_le_of_le_ofReal hc h


theorem lintegral_near_far (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) {f : Euc d → ℝ}
    (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) {r : ℝ} (hr : 0 < r) (x : Euc d) :
    ∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-s)) * ENNReal.ofReal |f y| ≤
      ENNReal.ofReal B * ENNReal.ofReal (sphereArea d * (r ^ ((d : ℝ) - s) / ((d : ℝ) - s))) +
        ENNReal.ofReal (r ^ (-s)) * ∫⁻ y, ENNReal.ofReal |f y| := by
  set Φ : Euc d → ℝ≥0∞ := fun y => ENNReal.ofReal (‖x - y‖ ^ (-s)) * ENNReal.ofReal |f y| with hΦ
  have h1 : ∫⁻ y, Φ y = ∫⁻ w, Φ (x - w) := (lintegral_sub_left_eq_self Φ x).symm
  have hΦw : ∀ w, Φ (x - w) = ENNReal.ofReal (‖w‖ ^ (-s)) * ENNReal.ofReal |f (x - w)| := by
    intro w; simp only [hΦ, sub_sub_cancel]
  set H1 : Euc d → ℝ≥0∞ := (ball (0 : Euc d) r).indicator
    (fun w => ENNReal.ofReal B * ENNReal.ofReal (‖w‖ ^ (-s))) with hH1
  have hH1m : Measurable H1 :=
    (measurable_const.mul (Measurable.ennreal_ofReal (measurable_norm.pow_const _))).indicator
      measurableSet_ball
  have hpt : ∀ w : Euc d, Φ (x - w) ≤ H1 w +
      ENNReal.ofReal (r ^ (-s)) * ENNReal.ofReal |f (x - w)| := by
    intro w
    rw [hΦw]
    by_cases hw : ‖w‖ < r
    · have hwb : w ∈ ball (0 : Euc d) r := by simpa using hw
      calc ENNReal.ofReal (‖w‖ ^ (-s)) * ENNReal.ofReal |f (x - w)|
          ≤ ENNReal.ofReal (‖w‖ ^ (-s)) * ENNReal.ofReal B := by
            gcongr
            exact hB _
        _ = H1 w := by simp [hH1, hwb, mul_comm]
        _ ≤ _ := le_self_add
    · have hw' : r ≤ ‖w‖ := not_lt.1 hw
      have : ‖w‖ ^ (-s) ≤ r ^ (-s) := Real.rpow_le_rpow_of_nonpos hr hw' (by linarith)
      calc ENNReal.ofReal (‖w‖ ^ (-s)) * ENNReal.ofReal |f (x - w)|
          ≤ ENNReal.ofReal (r ^ (-s)) * ENNReal.ofReal |f (x - w)| := by
            gcongr
        _ ≤ _ := le_add_self
  have hfm : Measurable (fun w : Euc d => ENNReal.ofReal |f (x - w)|) :=
    (hf.comp (measurable_const.sub measurable_id)).abs.ennreal_ofReal
  calc ∫⁻ y, Φ y = ∫⁻ w, Φ (x - w) := h1
    _ ≤ ∫⁻ w, (H1 w + ENNReal.ofReal (r ^ (-s)) * ENNReal.ofReal |f (x - w)|) :=
        lintegral_mono hpt
    _ = (∫⁻ w, H1 w) + ENNReal.ofReal (r ^ (-s)) * ∫⁻ w, ENNReal.ofReal |f (x - w)| := by
        rw [lintegral_add_left hH1m, lintegral_const_mul _ hfm]
    _ = _ := by
        have e1 : ∫⁻ w, H1 w = ENNReal.ofReal B * ENNReal.ofReal (sphereArea d *
            (r ^ ((d : ℝ) - s) / ((d : ℝ) - s))) := by
          rw [hH1, lintegral_indicator measurableSet_ball,
            lintegral_const_mul _ (Measurable.ennreal_ofReal (measurable_norm.pow_const _)),
            lintegral_ball_rpow hd hr hsd]
        have e2 : ∫⁻ w, ENNReal.ofReal |f (x - w)| = ∫⁻ y, ENNReal.ofReal |f y| :=
          lintegral_sub_left_eq_self (fun y => ENNReal.ofReal |f y|) x
        rw [e1, e2]


theorem sup_core (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) {f : Euc d → ℝ}
    (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) (hfi : Integrable f) {ε : ℝ}
    (hε : ∫ x, |f x| ≤ ε) {r : ℝ} (hr : 0 < r) (x : Euc d) :
    ∫⁻ y, ENNReal.ofReal |‖x - y‖ ^ (-s) * f y| ≤
      ENNReal.ofReal (B * (sphereArea d * (r ^ ((d : ℝ) - s) / ((d : ℝ) - s))) + r ^ (-s) * ε) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hsA := sphereArea_nonneg hd
  have hdm : 0 < (d : ℝ) - s := by linarith
  have hnf := lintegral_near_far hd hs0 hsd hf hB hr x
  have hfa : ∫⁻ y, ENNReal.ofReal |f y| = ENNReal.ofReal (∫ y, |f y|) := by
    rw [ofReal_integral_eq_lintegral_ofReal hfi.abs (Filter.Eventually.of_forall fun y => abs_nonneg _)]
  have hint0 : 0 ≤ ∫ y, |f y| := integral_nonneg fun y => abs_nonneg _
  have hε0 : 0 ≤ ε := hint0.trans hε
  have h1 : ∀ y : Euc d, ENNReal.ofReal |‖x - y‖ ^ (-s) * f y| =
      ENNReal.ofReal (‖x - y‖ ^ (-s)) * ENNReal.ofReal |f y| := by
    intro y
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
      ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)]
  simp_rw [h1]
  refine hnf.trans ?_
  rw [hfa]
  have hrs : 0 ≤ r ^ (-s) := Real.rpow_nonneg hr.le _
  rw [← ENNReal.ofReal_mul hB0, ← ENNReal.ofReal_mul hrs,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have : r ^ (-s) * ∫ y, |f y| ≤ r ^ (-s) * ε := mul_le_mul_of_nonneg_left hε hrs
  linarith


theorem sup_bound (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) (B : ℝ) :
    ∃ CB : ℝ, ∀ f : Euc d → ℝ, Measurable f → (∀ x, |f x| ≤ B) → Integrable f →
      ∀ ε : ℝ, ε ≤ 1 → ∫ x, |f x| ≤ ε →
        (∀ x, Integrable (fun y => ‖x - y‖ ^ (-s) * f y)) ∧
        ∀ x, |∫ y, ‖x - y‖ ^ (-s) * f y| ≤ CB * ε ^ (1 - s / d) := by
  have hsA := sphereArea_nonneg hd
  have hdm : 0 < (d : ℝ) - s := by linarith
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨|B| * sphereArea d / ((d : ℝ) - s) + 1, ?_⟩
  intro f hf hB hfi ε hε1 hε
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hint0 : 0 ≤ ∫ y, |f y| := integral_nonneg fun y => abs_nonneg _
  have hε0 : 0 ≤ ε := hint0.trans hε
  have hmeas : ∀ x : Euc d, Measurable (fun y => ‖x - y‖ ^ (-s) * f y) := fun x =>
    ((measurable_norm.comp (measurable_const.sub measurable_id)).pow_const _).mul hf
  have hcore1 := fun x => sup_core hd hs0 hsd hf hB hfi hε one_pos x
  refine ⟨fun x => ?_, fun x => ?_⟩
  · have := abs_integral_le_of_lintegral_le (hmeas x).aestronglyMeasurable
      (c := B * (sphereArea d * (1 ^ ((d : ℝ) - s) / ((d : ℝ) - s))) + 1 ^ (-s) * ε)
      (by positivity) (hcore1 x)
    exact this.1
  · by_cases hε' : ε = 0
    · subst hε'
      have hz : ∫ y, |f y| = 0 := le_antisymm hε hint0
      have hae : (fun y => |f y|) =ᵐ[volume] 0 :=
        (integral_eq_zero_iff_of_nonneg (fun y => abs_nonneg _) hfi.abs).1 hz
      have hae2 : (fun y => ‖x - y‖ ^ (-s) * f y) =ᵐ[volume] 0 := by
        filter_upwards [hae] with y hy
        have : f y = 0 := abs_eq_zero.1 hy
        simp [this]
      rw [integral_congr_ae hae2]
      have : (1 - s / d) ≠ 0 := by
        have : s / d < 1 := by rw [div_lt_one hdpos]; exact hsd
        linarith
      simp [Real.zero_rpow this]
    · have hεpos : 0 < ε := lt_of_le_of_ne hε0 (Ne.symm hε')
      set r : ℝ := ε ^ (1 / (d : ℝ)) with hr
      have hr0 : 0 < r := Real.rpow_pos_of_pos hεpos _
      have hcore := sup_core hd hs0 hsd hf hB hfi hε hr0 x
      have hc0 : 0 ≤ B * (sphereArea d * (r ^ ((d : ℝ) - s) / ((d : ℝ) - s))) + r ^ (-s) * ε := by
        have := Real.rpow_nonneg hr0.le ((d : ℝ) - s)
        have := Real.rpow_nonneg hr0.le (-s)
        positivity
      refine (abs_integral_le_of_lintegral_le (hmeas x).aestronglyMeasurable hc0 hcore).2.trans ?_
      have e1 : r ^ ((d : ℝ) - s) = ε ^ (1 - s / d) := by
        rw [hr, ← Real.rpow_mul hεpos.le]
        congr 1; field_simp
      have e2 : r ^ (-s) * ε = ε ^ (1 - s / d) := by
        rw [hr, ← Real.rpow_mul hεpos.le]
        have : 1 - s / (d : ℝ) = -s * (1 / (d : ℝ)) + 1 := by ring
        rw [this, Real.rpow_add hεpos, Real.rpow_one, mul_comm (1 / (d : ℝ)) (-s)]
      rw [e1, e2]
      have hE : 0 ≤ ε ^ (1 - s / d) := Real.rpow_nonneg hεpos.le _
      have : B * (sphereArea d * (ε ^ (1 - s / d) / ((d : ℝ) - s))) + ε ^ (1 - s / d) =
          (B * sphereArea d / ((d : ℝ) - s) + 1) * ε ^ (1 - s / d) := by ring
      rw [this]
      refine mul_le_mul_of_nonneg_right ?_ hE
      have : B * sphereArea d / ((d : ℝ) - s) ≤ |B| * sphereArea d / ((d : ℝ) - s) := by
        gcongr
        exact le_abs_self B
      linarith

end HRS.Whole.Q34
