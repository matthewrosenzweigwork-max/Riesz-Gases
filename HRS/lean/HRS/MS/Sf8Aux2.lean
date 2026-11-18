import HRS.MS.SameFunction

/-!
# MS-SF8II, analytic helpers (route: `Sf8Plan.md`)

* conversions between `lintegral` of `ofReal f` and `Integrable`/`∫`;
* `conv_bound`: the tail kernel `I2 = 1_{|z|≥1}|z|^{-s-1}` acting on a locally `L¹`-uniform `g`
  (averaging over unit balls and Tonelli);
* `far_int`: `∬ I2(x-y) h(x) g(y)` is integrable with an explicit bound;
* `l1_of_l2`: local `L²` bound ⇒ local `L¹` bound.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MS.Sf8

open HRS.Whole HRS.MS.SameFunction

variable {d : ℕ}

theorem integrable_of_lintegral_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x) (hb : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ⊤) :
    Integrable f μ := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  have e : ∀ x, ‖f x‖ₑ = ENNReal.ofReal (f x) := fun x => Real.enorm_eq_ofReal (h0 x)
  show ∫⁻ x, ‖f x‖ₑ ∂μ < ⊤
  simp_rw [e]
  exact lt_top_iff_ne_top.2 hb

theorem integral_le_of_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : Integrable f μ) (h0 : ∀ x, 0 ≤ f x) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ENNReal.ofReal M) : ∫ x, f x ∂μ ≤ M := by
  have h := ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall h0)
  rw [← h] at hM
  exact (ENNReal.ofReal_le_ofReal_iff hM0).1 hM

theorem measurable_msf_I2 (s : ℝ) : Measurable (fun z : Euc d => msf_I2 s z) :=
  (measurable_norm.pow_const _).indicator measurableSet_ball.compl

theorem measurable_msf_I1 (s : ℝ) : Measurable (fun z : Euc d => msf_I1 s z) :=
  (measurable_norm.pow_const _).indicator measurableSet_ball

/-- `I2(x-y) ≤ 4^{s+1} (1+|x-y'|)^{-(s+1)}` whenever `|y-y'| < 1`. -/
theorem I2_le_J {s : ℝ} (hs : 0 ≤ s + 1) (x y y' : Euc d) (h : dist y' y < 1) :
    msf_I2 s (x - y) ≤ 4 ^ (s + 1) * (1 + ‖x - y'‖) ^ (-(s + 1)) := by
  rcases lt_or_ge ‖x - y‖ 1 with h1 | h1
  · rw [msf_I2_lt h1]; positivity
  · rw [msf_I2_ge h1]
    have e : -s - 1 = -(s + 1) := by ring
    rw [e]
    have h2 := msf_rpow_tail h1 hs
    have hyy : ‖y - y'‖ < 1 := by rw [norm_sub_rev, ← dist_eq_norm]; exact h
    have hxy : ‖x - y'‖ ≤ ‖x - y‖ + 1 := by
      have : x - y' = (x - y) + (y - y') := by abel
      rw [this]
      exact (norm_add_le _ _).trans (by linarith)
    have hpos : 0 < (1 + ‖x - y'‖) / 2 := by positivity
    have h3 : (1 + ‖x - y‖) ^ (-(s + 1)) ≤ 2 ^ (s + 1) * (1 + ‖x - y'‖) ^ (-(s + 1)) := by
      have hle : (1 + ‖x - y'‖) / 2 ≤ 1 + ‖x - y‖ := by
        have := norm_nonneg (x - y); linarith
      have h4 := Real.rpow_le_rpow_of_nonpos hpos hle (by linarith : -(s + 1) ≤ 0)
      refine h4.trans (le_of_eq ?_)
      rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
        div_inv_eq_mul, mul_comm]
    have h5 : (4 : ℝ) ^ (s + 1) = 2 ^ (s + 1) * 2 ^ (s + 1) := by
      rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
    calc ‖x - y‖ ^ (-(s + 1)) ≤ 2 ^ (s + 1) * (1 + ‖x - y‖) ^ (-(s + 1)) := h2
      _ ≤ 2 ^ (s + 1) * (2 ^ (s + 1) * (1 + ‖x - y'‖) ^ (-(s + 1))) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 4 ^ (s + 1) * (1 + ‖x - y'‖) ^ (-(s + 1)) := by rw [h5]; ring

/-- The tail kernel applied to a locally uniformly integrable `g`. -/
theorem conv_bound {s : ℝ} (hs : 0 ≤ s + 1) {g : Euc d → ℝ≥0∞} (hg : Measurable g) {A : ℝ≥0∞}
    (hA : ∀ u : Euc d, ∫⁻ y in Metric.ball u 1, g y ≤ A) (x : Euc d) :
    volume (Metric.ball (0 : Euc d) 1) * ∫⁻ y, ENNReal.ofReal (msf_I2 s (x - y)) * g y ≤
      ENNReal.ofReal (4 ^ (s + 1)) * (∫⁻ z : Euc d, ENNReal.ofReal ((1 + ‖z‖) ^ (-(s + 1)))) * A := by
  set 𝒮 : Set (Euc d × Euc d) := {p | dist p.2 p.1 < 1} with h𝒮
  have h𝒮m : MeasurableSet 𝒮 :=
    measurableSet_lt (measurable_snd.dist measurable_fst) measurable_const
  set ind : Euc d × Euc d → ℝ≥0∞ := 𝒮.indicator (fun _ => (1 : ℝ≥0∞)) with hind
  have hindm : Measurable ind := measurable_const.indicator h𝒮m
  have hV : ∀ y : Euc d, ∫⁻ y', ind (y, y') = volume (Metric.ball (0 : Euc d) 1) := by
    intro y
    have e : (fun y' => ind (y, y')) = (Metric.ball y 1).indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext y'
      simp only [hind, h𝒮, Set.indicator, Set.mem_setOf_eq, Metric.mem_ball]
    rw [e, lintegral_indicator_const measurableSet_ball, one_mul, Measure.addHaar_ball_center]
  have hgm : Measurable fun y : Euc d => ENNReal.ofReal (msf_I2 s (x - y)) * g y :=
    (ENNReal.measurable_ofReal.comp ((measurable_msf_I2 s).comp (measurable_const.sub measurable_id))).mul hg
  have hJm : Measurable fun y' : Euc d => ENNReal.ofReal (4 ^ (s + 1) * (1 + ‖x - y'‖) ^ (-(s + 1))) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have hind' : ∀ y : Euc d, Measurable fun y' => ind (y, y') := fun y =>
    hindm.comp measurable_prodMk_left
  calc volume (Metric.ball (0 : Euc d) 1) * ∫⁻ y, ENNReal.ofReal (msf_I2 s (x - y)) * g y
      = ∫⁻ y, ∫⁻ y', (ENNReal.ofReal (msf_I2 s (x - y)) * g y) * ind (y, y') := by
        rw [← lintegral_const_mul' _ _ (measure_ball_lt_top).ne]
        refine lintegral_congr fun y => ?_
        rw [lintegral_const_mul _ (hind' y), hV y, mul_comm]
    _ ≤ ∫⁻ y, ∫⁻ y', (ENNReal.ofReal (4 ^ (s + 1) * (1 + ‖x - y'‖) ^ (-(s + 1))) * g y) *
          ind (y, y') := by
        refine lintegral_mono fun y => lintegral_mono fun y' => ?_
        by_cases hm : (y, y') ∈ 𝒮
        · have : ind (y, y') = 1 := by simp only [hind, Set.indicator_of_mem hm]
          rw [this, mul_one, mul_one]
          exact mul_le_mul' (ENNReal.ofReal_le_ofReal (I2_le_J hs x y y' hm)) le_rfl
        · have : ind (y, y') = 0 := by simp only [hind, Set.indicator_of_notMem hm]
          rw [this]; simp
    _ = ∫⁻ y', ∫⁻ y, (ENNReal.ofReal (4 ^ (s + 1) * (1 + ‖x - y'‖) ^ (-(s + 1))) * g y) *
          ind (y, y') := by
        refine lintegral_lintegral_swap ?_
        exact (((hJm.comp measurable_snd).mul (hg.comp measurable_fst)).mul hindm).aemeasurable
    _ ≤ ∫⁻ y', ENNReal.ofReal (4 ^ (s + 1) * (1 + ‖x - y'‖) ^ (-(s + 1))) * A := by
        refine lintegral_mono fun y' => ?_
        have e : ∀ y : Euc d, (ENNReal.ofReal (4 ^ (s + 1) * (1 + ‖x - y'‖) ^ (-(s + 1))) * g y) *
            ind (y, y') = ENNReal.ofReal (4 ^ (s + 1) * (1 + ‖x - y'‖) ^ (-(s + 1))) *
            (Metric.ball y' 1).indicator g y := by
          intro y
          by_cases hm : y ∈ Metric.ball y' 1
          · have h' : (y, y') ∈ 𝒮 := by simpa [h𝒮, Metric.mem_ball, dist_comm] using hm
            simp only [hind, Set.indicator_of_mem h', Set.indicator_of_mem hm, mul_one]
          · have h' : (y, y') ∉ 𝒮 := by simpa [h𝒮, Metric.mem_ball, dist_comm] using hm
            simp only [hind, Set.indicator_of_notMem h', Set.indicator_of_notMem hm, mul_zero]
        simp_rw [e]
        rw [lintegral_const_mul _ (hg.indicator measurableSet_ball),
          lintegral_indicator measurableSet_ball]
        exact mul_le_mul' le_rfl (hA y')
    _ = ENNReal.ofReal (4 ^ (s + 1)) * (∫⁻ z : Euc d, ENNReal.ofReal ((1 + ‖z‖) ^ (-(s + 1)))) * A := by
        have hc : (0 : ℝ) ≤ 4 ^ (s + 1) := by positivity
        have e1 : ∀ y' : Euc d, ENNReal.ofReal (4 ^ (s + 1) * (1 + ‖x - y'‖) ^ (-(s + 1))) =
            ENNReal.ofReal (4 ^ (s + 1)) * ENNReal.ofReal ((1 + ‖x - y'‖) ^ (-(s + 1))) :=
          fun y' => ENNReal.ofReal_mul hc
        have hJm' : Measurable fun y' : Euc d => ENNReal.ofReal ((1 + ‖x - y'‖) ^ (-(s + 1))) :=
          ENNReal.measurable_ofReal.comp (by fun_prop)
        have hfm : Measurable fun y' : Euc d => ENNReal.ofReal (4 ^ (s + 1)) *
            ENNReal.ofReal ((1 + ‖x - y'‖) ^ (-(s + 1))) := measurable_const.mul hJm'
        simp_rw [e1]
        rw [lintegral_mul_const _ hfm, lintegral_const_mul _ hJm',
          lintegral_sub_left_eq_self (fun z : Euc d => ENNReal.ofReal ((1 + ‖z‖) ^ (-(s + 1)))) x]

/-- The constant of `far_int`. -/
def farConst (d : ℕ) (s : ℝ) : ℝ :=
  4 ^ (s + 1) * (∫ z : Euc d, (1 + ‖z‖) ^ (-(s + 1))) /
    (volume (Metric.ball (0 : Euc d) 1)).toReal

theorem integrable_J (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s + 1) :
    Integrable (fun z : Euc d => (1 + ‖z‖) ^ (-(s + 1))) := by
  have hfr : Module.finrank ℝ (Euc d) = d := finrank_euclideanSpace_fin
  exact integrable_one_add_norm (by rw [hfr]; exact hs)

theorem farConst_nonneg (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s + 1) : 0 ≤ farConst d s := by
  unfold farConst
  have : 0 ≤ ∫ z : Euc d, (1 + ‖z‖) ^ (-(s + 1)) :=
    integral_nonneg fun z => Real.rpow_nonneg (by positivity) _
  positivity

/-- `∬ I2(x-y) h(x) g(y)` for `h ∈ L¹`, `g` locally uniformly `L¹`. -/
theorem far_int (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s + 1) {h g : Euc d → ℝ}
    (hh : Measurable h) (hg : Measurable g) (hh0 : ∀ x, 0 ≤ h x) (hg0 : ∀ x, 0 ≤ g x)
    {M1 M3 : ℝ} (hM1 : 0 ≤ M1) (hM3 : 0 ≤ M3)
    (h1 : ∫⁻ x, ENNReal.ofReal (h x) ≤ ENNReal.ofReal M1)
    (h3 : ∀ u : Euc d, ∫⁻ y in Metric.ball u 1, ENNReal.ofReal (g y) ≤ ENNReal.ofReal M3) :
    Integrable (fun p : Euc d × Euc d => msf_I2 s (p.1 - p.2) * h p.1 * g p.2) ∧
      ∫ p : Euc d × Euc d, msf_I2 s (p.1 - p.2) * h p.1 * g p.2 ≤ farConst d s * M1 * M3 := by
  have hs0 : 0 ≤ s + 1 := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hJi := integrable_J hd hs
  have hJn : ∀ z : Euc d, 0 ≤ (1 + ‖z‖) ^ (-(s + 1)) := fun z => Real.rpow_nonneg (by positivity) _
  have hJr0 : 0 ≤ ∫ z : Euc d, (1 + ‖z‖) ^ (-(s + 1)) := integral_nonneg hJn
  have hV1pos : 0 < volume (Metric.ball (0 : Euc d) 1) := Metric.measure_ball_pos _ _ one_pos
  have hV1top : volume (Metric.ball (0 : Euc d) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hV1r : 0 < (volume (Metric.ball (0 : Euc d) 1)).toReal :=
    ENNReal.toReal_pos hV1pos.ne' hV1top
  have hJl : ∫⁻ z : Euc d, ENNReal.ofReal ((1 + ‖z‖) ^ (-(s + 1))) =
      ENNReal.ofReal (∫ z : Euc d, (1 + ‖z‖) ^ (-(s + 1))) :=
    (ofReal_integral_eq_lintegral_ofReal hJi (Eventually.of_forall hJn)).symm
  have hc : (0 : ℝ) ≤ 4 ^ (s + 1) := by positivity
  -- bound on the inner convolution
  have hBnn : 0 ≤ farConst d s * M3 := mul_nonneg (farConst_nonneg hd hs) hM3
  have hconv : ∀ x : Euc d, ∫⁻ y, ENNReal.ofReal (msf_I2 s (x - y)) * ENNReal.ofReal (g y) ≤
      ENNReal.ofReal (farConst d s * M3) := by
    intro x
    have h0 := conv_bound hs0 (g := fun y => ENNReal.ofReal (g y))
      (ENNReal.measurable_ofReal.comp hg) h3 x
    rw [hJl] at h0
    have hR : ENNReal.ofReal (4 ^ (s + 1)) *
        ENNReal.ofReal (∫ z : Euc d, (1 + ‖z‖) ^ (-(s + 1))) * ENNReal.ofReal M3 =
        ENNReal.ofReal (4 ^ (s + 1) * (∫ z : Euc d, (1 + ‖z‖) ^ (-(s + 1))) * M3) := by
      rw [ENNReal.ofReal_mul (mul_nonneg hc hJr0), ENNReal.ofReal_mul hc]
    rw [hR] at h0
    rw [mul_comm] at h0
    have h2 := (ENNReal.le_div_iff_mul_le (Or.inl hV1pos.ne') (Or.inl hV1top)).2 h0
    refine h2.trans (le_of_eq ?_)
    conv_lhs => rw [← ENNReal.ofReal_toReal hV1top]
    rw [← ENNReal.ofReal_div_of_pos hV1r]
    congr 1
    unfold farConst
    ring
  have hmI : Measurable fun p : Euc d × Euc d => msf_I2 s (p.1 - p.2) :=
    (measurable_msf_I2 (d := d) s).comp (measurable_fst.sub measurable_snd)
  have hmeasI : Measurable fun p : Euc d × Euc d => msf_I2 s (p.1 - p.2) * h p.1 * g p.2 :=
    (hmI.mul (hh.comp measurable_fst)).mul (hg.comp measurable_snd)
  have hmE : Measurable fun p : Euc d × Euc d => ENNReal.ofReal (msf_I2 s (p.1 - p.2)) *
      ENNReal.ofReal (h p.1) * ENNReal.ofReal (g p.2) :=
    ((ENNReal.measurable_ofReal.comp hmI).mul
      (ENNReal.measurable_ofReal.comp (hh.comp measurable_fst))).mul
      (ENNReal.measurable_ofReal.comp (hg.comp measurable_snd))
  have hlint : ∫⁻ p : Euc d × Euc d, ENNReal.ofReal (msf_I2 s (p.1 - p.2) * h p.1 * g p.2) ≤
      ENNReal.ofReal (M1 * (farConst d s * M3)) := by
    have e : ∀ p : Euc d × Euc d, ENNReal.ofReal (msf_I2 s (p.1 - p.2) * h p.1 * g p.2) =
        ENNReal.ofReal (msf_I2 s (p.1 - p.2)) * ENNReal.ofReal (h p.1) *
          ENNReal.ofReal (g p.2) := by
      intro p
      rw [ENNReal.ofReal_mul (mul_nonneg (msf_I2_nonneg _ _) (hh0 _)),
        ENNReal.ofReal_mul (msf_I2_nonneg _ _)]
    simp_rw [e]
    rw [Measure.volume_eq_prod, lintegral_prod _ hmE.aemeasurable]
    have hmy : ∀ x : Euc d, Measurable fun y : Euc d =>
        ENNReal.ofReal (msf_I2 s (x - y)) * ENNReal.ofReal (g y) := fun x =>
      (ENNReal.measurable_ofReal.comp ((measurable_msf_I2 (d := d) s).comp
        (measurable_const.sub measurable_id))).mul (ENNReal.measurable_ofReal.comp hg)
    calc ∫⁻ x : Euc d, ∫⁻ y : Euc d, ENNReal.ofReal (msf_I2 s (x - y)) * ENNReal.ofReal (h x) *
            ENNReal.ofReal (g y)
        = ∫⁻ x : Euc d, ENNReal.ofReal (h x) *
            ∫⁻ y : Euc d, ENNReal.ofReal (msf_I2 s (x - y)) * ENNReal.ofReal (g y) := by
          refine lintegral_congr fun x => ?_
          rw [← lintegral_const_mul _ (hmy x)]
          refine lintegral_congr fun y => ?_
          ring
      _ ≤ ∫⁻ x : Euc d, ENNReal.ofReal (h x) * ENNReal.ofReal (farConst d s * M3) :=
          lintegral_mono fun x => mul_le_mul' le_rfl (hconv x)
      _ = (∫⁻ x : Euc d, ENNReal.ofReal (h x)) * ENNReal.ofReal (farConst d s * M3) :=
          lintegral_mul_const _ (ENNReal.measurable_ofReal.comp hh)
      _ ≤ ENNReal.ofReal M1 * ENNReal.ofReal (farConst d s * M3) := mul_le_mul' h1 le_rfl
      _ = ENNReal.ofReal (M1 * (farConst d s * M3)) := (ENNReal.ofReal_mul hM1).symm
  have hnn : ∀ p : Euc d × Euc d, 0 ≤ msf_I2 s (p.1 - p.2) * h p.1 * g p.2 := fun p =>
    mul_nonneg (mul_nonneg (msf_I2_nonneg _ _) (hh0 _)) (hg0 _)
  have hint : Integrable (fun p : Euc d × Euc d => msf_I2 s (p.1 - p.2) * h p.1 * g p.2) :=
    integrable_of_lintegral_ofReal hmeasI hnn (hlint.trans_lt ENNReal.ofReal_lt_top).ne
  refine ⟨hint, ?_⟩
  have := integral_le_of_lintegral hint hnn (mul_nonneg hM1 hBnn) hlint
  calc _ ≤ M1 * (farConst d s * M3) := this
    _ = farConst d s * M1 * M3 := by ring

/-- Local `L²` bound ⇒ local `L¹` bound. -/
theorem l1_of_l2 {B : Set (Euc d)} (hB : MeasurableSet B) (hBfin : volume B ≠ ⊤)
    {w : Euc d → ℝ} (hw : Measurable w) {P S : ℝ} (hP : 0 ≤ P) (hS : 0 ≤ S)
    (h : ∫⁻ x in B, ENNReal.ofReal (w x ^ 2) ≤ ENNReal.ofReal (P * S ^ 2)) :
    ∫⁻ x in B, ENNReal.ofReal |w x| ≤ ENNReal.ofReal (S * (P + (volume B).toReal)) := by
  have hwm2 : Measurable fun x => ENNReal.ofReal (w x ^ 2) :=
    ENNReal.measurable_ofReal.comp (hw.pow_const 2)
  rcases hS.eq_or_lt with hS0 | hSpos
  · subst hS0
    have h0 : ENNReal.ofReal (P * (0 : ℝ) ^ 2) = 0 := by simp
    rw [h0] at h
    have h' : ∫⁻ x in B, ENNReal.ofReal (w x ^ 2) = 0 := le_antisymm h zero_le
    have hae := (lintegral_eq_zero_iff hwm2).1 h'
    have : ∫⁻ x in B, ENNReal.ofReal |w x| = 0 := by
      have hm : Measurable fun x => ENNReal.ofReal |w x| := ENNReal.measurable_ofReal.comp hw.abs
      rw [lintegral_eq_zero_iff hm]
      filter_upwards [hae] with x hx
      have hx' : ENNReal.ofReal (w x ^ 2) = 0 := hx
      have h1 : w x ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.1 hx'
      have h2 : w x = 0 := by nlinarith [sq_nonneg (w x)]
      simp [h2]
    rw [this]; exact zero_le
  · set V := (volume B).toReal with hV
    have hVe : volume B = ENNReal.ofReal V := (ENNReal.ofReal_toReal hBfin).symm
    have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
    calc ∫⁻ x in B, ENNReal.ofReal |w x|
        ≤ ∫⁻ x in B, (ENNReal.ofReal (1 / (2 * S)) * ENNReal.ofReal (w x ^ 2) +
            ENNReal.ofReal (S / 2)) := by
          refine lintegral_mono fun x => ?_
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : 0 < 2 * S := by positivity
          have h2 : 1 / (2 * S) * w x ^ 2 + S / 2 - |w x| = (|w x| - S) ^ 2 / (2 * S) := by
            rw [← sq_abs (w x)]; field_simp; ring
          have h3 : 0 ≤ (|w x| - S) ^ 2 / (2 * S) := by positivity
          linarith
      _ = ENNReal.ofReal (1 / (2 * S)) * (∫⁻ x in B, ENNReal.ofReal (w x ^ 2)) +
            ENNReal.ofReal (S / 2) * volume B := by
          rw [lintegral_add_right (fun x => ENNReal.ofReal (1 / (2 * S)) *
              ENNReal.ofReal (w x ^ 2))
              (measurable_const : Measurable fun _ : Euc d => ENNReal.ofReal (S / 2)),
            lintegral_const_mul _ hwm2, setLIntegral_const]
      _ ≤ ENNReal.ofReal (1 / (2 * S)) * ENNReal.ofReal (P * S ^ 2) +
            ENNReal.ofReal (S / 2) * ENNReal.ofReal V := by
          rw [hVe]
          gcongr
      _ = ENNReal.ofReal (P * S / 2 + S / 2 * V) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          field_simp
      _ ≤ ENNReal.ofReal (S * (P + V)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          nlinarith [mul_nonneg hP hS, mul_nonneg hS hV0]

end HRS.MS.Sf8
