import HRS.Equilibrium.Parametrix.PX3aAuxB

/-!
# Packet PX3a auxiliaries C: logarithmic weights and one-dimensional radial integrals
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

/-- The logarithmic weight `1 + |log t|`. -/
def lw (t : ℝ) : ℝ := 1 + |Real.log t|

lemma one_le_lw (t : ℝ) : 1 ≤ lw t := by unfold lw; linarith [abs_nonneg (Real.log t)]

lemma lw_pos (t : ℝ) : 0 < lw t := lt_of_lt_of_le one_pos (one_le_lw t)

lemma lw_anti {t s : ℝ} (ht : 0 < t) (hts : t ≤ s) (hs : s ≤ 1) : lw s ≤ lw t := by
  unfold lw
  have h1 : Real.log t ≤ Real.log s := Real.log_le_log ht hts
  have h2 : Real.log s ≤ 0 := Real.log_nonpos (ht.le.trans hts) hs
  rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]
  linarith

lemma lw_mul_le {t s : ℝ} (ht : 0 < t) (hs : 0 < s) : lw (t * s) ≤ lw t * lw s := by
  unfold lw
  rw [Real.log_mul ht.ne' hs.ne']
  nlinarith [abs_add_le (Real.log t) (Real.log s), abs_nonneg (Real.log t), abs_nonneg (Real.log s)]

lemma lw_le_two_mul {r t : ℝ} (hr : 0 < r) (h1 : r / 2 ≤ t) (h2 : t ≤ 2 * r) : lw t ≤ 2 * lw r := by
  have ht : 0 < t := lt_of_lt_of_le (by positivity) h1
  have : t = r * (t / r) := by field_simp
  have hq : lw (t / r) ≤ 2 := by
    unfold lw
    have h3 : (1 / 2 : ℝ) ≤ t / r := by rw [le_div_iff₀ hr]; linarith
    have h4 : t / r ≤ 2 := by rw [div_le_iff₀ hr]; linarith
    have h5 : |Real.log (t / r)| ≤ Real.log 2 := by
      rw [abs_le]
      constructor
      · have := Real.log_le_log (by norm_num : (0:ℝ) < 1 / 2) h3
        rw [one_div, Real.log_inv] at this
        linarith
      · exact Real.log_le_log (by positivity) h4
    have := Real.log_two_lt_d9
    linarith
  calc lw t = lw (r * (t / r)) := by rw [← this]
    _ ≤ lw r * lw (t / r) := lw_mul_le hr (by positivity)
    _ ≤ lw r * 2 := by gcongr; exact (lw_pos r).le
    _ = 2 * lw r := by ring

/-- Integrability of `s^(e-1) (1+|log s|)^b` near zero. -/
lemma intervalIntegrable_rpow_lw {e : ℝ} (he : 0 < e) (b : ℕ) :
    IntervalIntegrable (fun s : ℝ => s ^ (e - 1) * lw s ^ b) volume 0 1 := by
  obtain ⟨C, hC, hCb⟩ := one_add_abs_log_pow_le b (δ := e / 2) (by positivity)
  have hint : IntervalIntegrable (fun s : ℝ => C * s ^ (e / 2 - 1)) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul C
  refine hint.mono_fun ?_ ?_
  · have : ContinuousOn (fun s : ℝ => s ^ (e - 1) * lw s ^ b) (Set.uIoc 0 1) := by
      intro s hs
      rw [Set.uIoc_of_le zero_le_one] at hs
      have hs0 : s ≠ 0 := hs.1.ne'
      refine ContinuousAt.continuousWithinAt ?_
      unfold lw
      have h1 : ContinuousAt (fun s : ℝ => s ^ (e - 1)) s := Real.continuousAt_rpow_const _ _ (Or.inl hs0)
      have h2 : ContinuousAt Real.log s := Real.continuousAt_log hs0
      fun_prop (disch := assumption)
    exact this.aestronglyMeasurable measurableSet_uIoc
  · refine (ae_restrict_iff' measurableSet_uIoc).mpr (Eventually.of_forall fun s hs => ?_)
    rw [Set.uIoc_of_le zero_le_one] at hs
    have h1 := hCb s hs.1 hs.2
    have hs0 := hs.1
    show ‖s ^ (e - 1) * lw s ^ b‖ ≤ ‖C * s ^ (e / 2 - 1)‖
    rw [Real.norm_of_nonneg (by have := one_le_lw s; positivity),
      Real.norm_of_nonneg (by positivity)]
    have : s ^ (e - 1) * lw s ^ b ≤ s ^ (e - 1) * (C * s ^ (-(e / 2))) := by
      unfold lw; gcongr
    refine this.trans (le_of_eq ?_)
    rw [show e - 1 = (e / 2 - 1) + e / 2 by ring, Real.rpow_add hs0]
    have : s ^ (e / 2) * s ^ (-(e / 2)) = 1 := by
      rw [← Real.rpow_add hs0]; simp
    calc s ^ (e / 2 - 1) * s ^ (e / 2) * (C * s ^ (-(e / 2)))
        = C * s ^ (e / 2 - 1) * (s ^ (e / 2) * s ^ (-(e / 2))) := by ring
      _ = _ := by rw [this]; ring

lemma intervalIntegrable_rpow_lw_le {e : ℝ} (he : 0 < e) (b : ℕ) {R : ℝ} (hR0 : 0 < R) (hR : R ≤ 1) :
    IntervalIntegrable (fun s : ℝ => s ^ (e - 1) * lw s ^ b) volume 0 R :=
  (intervalIntegrable_rpow_lw he b).mono_set (by
    rw [Set.uIcc_of_le hR0.le, Set.uIcc_of_le zero_le_one]
    exact Set.Icc_subset_Icc le_rfl hR)

/-- Scaling bound: `∫_0^R t^(e-1) lw(t)^b dt ≤ I R^e lw(R)^b`. -/
lemma int_scale_le {e : ℝ} (he : 0 < e) (b : ℕ) :
    ∃ I : ℝ, 0 ≤ I ∧ ∀ R : ℝ, 0 < R → R ≤ 1 →
      ∫ t in (0 : ℝ)..R, t ^ (e - 1) * lw t ^ b ≤ I * R ^ e * lw R ^ b := by
  refine ⟨∫ s in (0 : ℝ)..1, s ^ (e - 1) * lw s ^ b, ?_, fun R hR0 hR1 => ?_⟩
  · refine intervalIntegral.integral_nonneg zero_le_one fun s hs => ?_
    have := one_le_lw s
    have hs0 : 0 ≤ s := hs.1
    positivity
  · have h1 := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
      (fun t : ℝ => t ^ (e - 1) * lw t ^ b) hR0.ne'
    simp only [mul_zero, mul_one, smul_eq_mul] at h1
    have h2 : ∫ t in (0 : ℝ)..R, t ^ (e - 1) * lw t ^ b =
        R * ∫ s in (0 : ℝ)..1, (R * s) ^ (e - 1) * lw (R * s) ^ b := by
      rw [h1]; field_simp
    rw [h2]
    have hint1 : IntervalIntegrable (fun s : ℝ => (R * s) ^ (e - 1) * lw (R * s) ^ b) volume 0 1 := by
      have := (intervalIntegrable_rpow_lw_le he b hR0 hR1).comp_mul_left (c := R)
      simpa [hR0.ne'] using this
    have hint2 : IntervalIntegrable (fun s : ℝ => (R ^ (e - 1) * lw R ^ b) * (s ^ (e - 1) * lw s ^ b))
        volume 0 1 := (intervalIntegrable_rpow_lw he b).const_mul _
    have h3 : ∫ s in (0 : ℝ)..1, (R * s) ^ (e - 1) * lw (R * s) ^ b ≤
        ∫ s in (0 : ℝ)..1, (R ^ (e - 1) * lw R ^ b) * (s ^ (e - 1) * lw s ^ b) := by
      refine intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one hint1 hint2 fun s hs => ?_
      have hs0 : 0 < s := hs.1
      rw [Real.mul_rpow hR0.le hs0.le]
      have := pow_le_pow_left₀ (lw_pos _).le (lw_mul_le hR0 hs0) b
      rw [mul_pow] at this
      have hA : 0 ≤ R ^ (e - 1) * s ^ (e - 1) := by positivity
      calc R ^ (e - 1) * s ^ (e - 1) * lw (R * s) ^ b
          ≤ R ^ (e - 1) * s ^ (e - 1) * (lw R ^ b * lw s ^ b) := by gcongr
        _ = _ := by ring
    rw [intervalIntegral.integral_const_mul] at h3
    have hR' : R * R ^ (e - 1) = R ^ e := by
      rw [← Real.rpow_one_add' hR0.le (by linarith)]; ring_nf
    calc R * ∫ s in (0 : ℝ)..1, (R * s) ^ (e - 1) * lw (R * s) ^ b
        ≤ R * ((R ^ (e - 1) * lw R ^ b) * ∫ s in (0 : ℝ)..1, s ^ (e - 1) * lw s ^ b) := by gcongr
      _ = (∫ s in (0 : ℝ)..1, s ^ (e - 1) * lw s ^ b) * R ^ e * lw R ^ b := by
          rw [← hR']; ring

/-! ### Radial integrals -/

section Radial

variable {d : ℕ}

/-- Polar coordinates: a radial majorant bounds the norm of the integral. -/
lemma norm_integral_le_radial (hd : 1 ≤ d) {φ : Euc d → ℝ} {f : ℝ → ℝ}
    (hf : IntegrableOn (fun y : ℝ => y ^ (d - 1) • f y) (Ioi 0))
    (hle : ∀ᵐ x : Euc d ∂volume, ‖φ x‖ ≤ f ‖x‖) :
    ‖∫ x, φ x‖ ≤ (d * (volume (Metric.ball (0 : Euc d) 1)).toReal) *
      ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * f y := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hint : Integrable (fun x : Euc d => f ‖x‖) (volume : Measure (Euc d)) := by
    refine (integrable_fun_norm_addHaar (volume : Measure (Euc d))).mpr ?_
    rw [finrank_euclideanSpace_fin]
    exact hf
  refine (norm_integral_le_of_norm_le hint hle).trans (le_of_eq ?_)
  rw [integral_fun_norm_addHaar (volume : Measure (Euc d)) f, finrank_euclideanSpace_fin]
  simp only [smul_eq_mul, nsmul_eq_mul, Measure.real]
  ring

lemma integrableOn_rpow_lw_cut {d : ℕ} (hd : 1 ≤ d) {q : ℝ} (hq : q < d) (b : ℕ) {R : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) :
    IntegrableOn (fun y : ℝ => y ^ (d - 1) •
      (if y < R then y ^ (-q) * lw y ^ b else 0)) (Ioi 0) := by
  have h1 : IntervalIntegrable (fun s : ℝ => s ^ (((d : ℝ) - q) - 1) * lw s ^ b) volume 0 R :=
    intervalIntegrable_rpow_lw_le (by linarith) b hR hR1
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hR.le] at h1
  have h2 : IntegrableOn (fun y : ℝ => y ^ (d - 1) •
      (if y < R then y ^ (-q) * lw y ^ b else 0)) (Ioo 0 R) := by
    refine h1.congr_fun (fun y hy => ?_) measurableSet_Ioo
    have hy0 : 0 < y := hy.1
    simp only [smul_eq_mul, if_pos hy.2]
    rw [show ((d : ℝ) - q) - 1 = ((d : ℝ) - 1) + (-q) by ring, Real.rpow_add hy0]
    have : y ^ (d - 1) = y ^ ((d : ℝ) - 1) := by
      rw [← Real.rpow_natCast]; congr 1; rw [Nat.cast_sub hd]; simp
    rw [this]; ring
  have h3 : IntegrableOn (fun y : ℝ => y ^ (d - 1) •
      (if y < R then y ^ (-q) * lw y ^ b else 0)) (Ioi 0 \ Ioo 0 R) := by
    refine (integrableOn_zero (μ := volume)).congr_fun (fun y hy => ?_) (measurableSet_Ioi.diff measurableSet_Ioo)
    have : ¬ y < R := by
      intro h; exact hy.2 ⟨hy.1, h⟩
    simp [this]
  have := h2.union h3
  rwa [Set.union_diff_cancel (fun y hy => hy.1)] at this

lemma radial_ball_le {d : ℕ} (hd : 1 ≤ d) {q : ℝ} (hq : q < d) (b : ℕ) :
    ∃ I : ℝ, 0 ≤ I ∧ ∀ R : ℝ, 0 < R → R ≤ 1 →
      ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * (if y < R then y ^ (-q) * lw y ^ b else 0) ≤
        I * R ^ ((d : ℝ) - q) * lw R ^ b := by
  obtain ⟨I, hI0, hI⟩ := int_scale_le (e := (d : ℝ) - q) (by linarith) b
  refine ⟨I, hI0, fun R hR hR1 => ?_⟩
  have h1 : ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * (if y < R then y ^ (-q) * lw y ^ b else 0) =
      ∫ y in (0 : ℝ)..R, y ^ (((d : ℝ) - q) - 1) * lw y ^ b := by
    rw [intervalIntegral.integral_of_le hR.le, integral_Ioc_eq_integral_Ioo]
    have h0 : ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * (if y < R then y ^ (-q) * lw y ^ b else 0) =
        ∫ y in Ioo (0 : ℝ) R, y ^ (d - 1) * (if y < R then y ^ (-q) * lw y ^ b else 0) := by
      refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s := Set.Ioo (0 : ℝ) R)
        (t := Set.Ioi (0 : ℝ)) measurableSet_Ioi (Set.Ioo_subset_Ioi_self) (fun y hy => ?_)
      have : ¬ y < R := fun h => hy.2 ⟨hy.1, h⟩
      simp [this]
    rw [h0]
    refine setIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
    have hy0 : 0 < y := hy.1
    simp only [hy.2, if_true]
    rw [show ((d : ℝ) - q) - 1 = ((d : ℝ) - 1) + (-q) by ring, Real.rpow_add hy0]
    have : y ^ (d - 1) = y ^ ((d : ℝ) - 1) := by
      rw [← Real.rpow_natCast]; congr 1; rw [Nat.cast_sub hd]; simp
    rw [this]; ring
  rw [h1]
  exact hI R hR hR1

end Radial

lemma lw_two_le : lw 2 ≤ 2 := by
  unfold lw
  have := Real.log_two_lt_d9
  rw [abs_of_nonneg (Real.log_nonneg (by norm_num))]
  linarith

lemma lw_mono_int {r y : ℝ} (hr : 0 < r) (hry : 2 * r ≤ y) (hy : y ≤ 1) : lw y ≤ 2 * lw r := by
  calc lw y ≤ lw (2 * r) := lw_anti (by positivity) hry hy
    _ ≤ lw 2 * lw r := lw_mul_le (by norm_num) hr
    _ ≤ 2 * lw r := by have := lw_pos r; nlinarith [lw_two_le]

lemma continuousOn_rpow_lw {e : ℝ} (b : ℕ) {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ContinuousOn (fun y : ℝ => y ^ (e - 1) * lw y ^ b) (Set.uIcc a c) := by
  intro y hy
  have hy0 : y ≠ 0 := (lt_of_lt_of_le (lt_min ha hc) hy.1).ne'
  refine ContinuousAt.continuousWithinAt ?_
  unfold lw
  have h1 : ContinuousAt (fun s : ℝ => s ^ (e - 1)) y := Real.continuousAt_rpow_const _ _ (Or.inl hy0)
  have h2 : ContinuousAt Real.log y := Real.continuousAt_log hy0
  fun_prop (disch := assumption)

/-- The outer annulus integral. -/
lemma outer_int_le (e : ℝ) (b : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 / 32 →
      ∫ y in (2 * r)..(1 / 16 : ℝ), y ^ (e - 1) * lw y ^ b ≤
        C * (1 + r ^ e * lw r ^ (b + if e = 0 then 1 else 0)) := by
  rcases lt_trichotomy e 0 with he | he | he
  · refine ⟨2 ^ b / (-e), by have : 0 < -e := by linarith
                             positivity, fun r hr hr1 => ?_⟩
    have hab : 2 * r ≤ 1 / 16 := by linarith
    have hr2 : 0 < 2 * r := by positivity
    have hf : IntervalIntegrable (fun y : ℝ => y ^ (e - 1) * lw y ^ b) volume (2 * r) (1 / 16) :=
      (continuousOn_rpow_lw b hr2 (by norm_num)).intervalIntegrable
    have hcont : ContinuousOn (fun y : ℝ => y ^ (e - 1)) (Set.uIcc (2 * r) (1 / 16)) := by
      refine ContinuousOn.rpow_const continuousOn_id (fun y hy => Or.inl ?_)
      exact (lt_of_lt_of_le (lt_min hr2 (by norm_num)) hy.1).ne'
    have hg : IntervalIntegrable (fun y : ℝ => (2 * lw r) ^ b * y ^ (e - 1)) volume (2 * r) (1 / 16) :=
      (continuousOn_const.mul hcont).intervalIntegrable
    have h1 : ∫ y in (2 * r)..(1 / 16 : ℝ), y ^ (e - 1) * lw y ^ b ≤
        ∫ y in (2 * r)..(1 / 16 : ℝ), (2 * lw r) ^ b * y ^ (e - 1) := by
      refine intervalIntegral.integral_mono_on hab hf hg fun y hy => ?_
      have hy0 : 0 < y := lt_of_lt_of_le hr2 hy.1
      have := pow_le_pow_left₀ (lw_pos y).le (lw_mono_int hr hy.1 (by linarith [hy.2])) b
      have hp : 0 ≤ y ^ (e - 1) := by positivity
      calc y ^ (e - 1) * lw y ^ b ≤ y ^ (e - 1) * (2 * lw r) ^ b := by gcongr
        _ = _ := by ring
    have h2 : ∫ y in (2 * r)..(1 / 16 : ℝ), (2 * lw r) ^ b * y ^ (e - 1) =
        (2 * lw r) ^ b * (((1 / 16 : ℝ) ^ e - (2 * r) ^ e) / e) := by
      rw [intervalIntegral.integral_const_mul, integral_rpow]
      · congr 3 <;> ring_nf
      · right
        refine ⟨by intro h; apply he.ne; linarith, ?_⟩
        rw [Set.uIcc_of_le hab]
        intro h; exact absurd h.1 (by linarith)
    rw [h2] at h1
    refine h1.trans ?_
    have hA : 0 ≤ (2 * lw r) ^ b := by have := lw_pos r; positivity
    have hne : (0 : ℝ) < -e := by linarith
    have h3 : ((1 / 16 : ℝ) ^ e - (2 * r) ^ e) / e ≤ (2 * r) ^ e / (-e) := by
      have h4 : 0 ≤ (1 / 16 : ℝ) ^ e := by positivity
      have h5 : ((1 / 16 : ℝ) ^ e - (2 * r) ^ e) / e = ((2 * r) ^ e - (1 / 16 : ℝ) ^ e) / (-e) := by
        field_simp
        ring
      rw [h5]
      exact div_le_div_of_nonneg_right (by linarith) hne.le
    have h6 : (2 * r) ^ e ≤ r ^ e := by
      rw [Real.mul_rpow (by norm_num) hr.le]
      have : (2 : ℝ) ^ e ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) he.le
      have : 0 ≤ r ^ e := by positivity
      nlinarith
    have hex : (if e = 0 then 1 else 0) = 0 := by simp [he.ne]
    rw [hex, add_zero]
    calc (2 * lw r) ^ b * (((1 / 16 : ℝ) ^ e - (2 * r) ^ e) / e)
        ≤ (2 * lw r) ^ b * ((2 * r) ^ e / (-e)) := by gcongr
      _ ≤ (2 * lw r) ^ b * (r ^ e / (-e)) := by gcongr
      _ = 2 ^ b / (-e) * (r ^ e * lw r ^ b) := by rw [mul_pow]; ring
      _ ≤ 2 ^ b / (-e) * (1 + r ^ e * lw r ^ b) := by
          gcongr
          linarith
  · subst he
    refine ⟨2 ^ b, by positivity, fun r hr hr1 => ?_⟩
    have hab : 2 * r ≤ 1 / 16 := by linarith
    have hr2 : 0 < 2 * r := by positivity
    have hf : IntervalIntegrable (fun y : ℝ => y ^ ((0 : ℝ) - 1) * lw y ^ b) volume (2 * r) (1 / 16) :=
      (continuousOn_rpow_lw b hr2 (by norm_num)).intervalIntegrable
    have hcont : ContinuousOn (fun y : ℝ => y⁻¹) (Set.uIcc (2 * r) (1 / 16)) := by
      refine ContinuousOn.inv₀ continuousOn_id (fun y hy => ?_)
      exact (lt_of_lt_of_le (lt_min hr2 (by norm_num)) hy.1).ne'
    have hg : IntervalIntegrable (fun y : ℝ => (2 * lw r) ^ b * y⁻¹) volume (2 * r) (1 / 16) :=
      (continuousOn_const.mul hcont).intervalIntegrable
    have h1 : ∫ y in (2 * r)..(1 / 16 : ℝ), y ^ ((0 : ℝ) - 1) * lw y ^ b ≤
        ∫ y in (2 * r)..(1 / 16 : ℝ), (2 * lw r) ^ b * y⁻¹ := by
      refine intervalIntegral.integral_mono_on hab hf hg fun y hy => ?_
      have hy0 : 0 < y := lt_of_lt_of_le hr2 hy.1
      have := pow_le_pow_left₀ (lw_pos y).le (lw_mono_int hr hy.1 (by linarith [hy.2])) b
      have hp : 0 ≤ y⁻¹ := by positivity
      rw [zero_sub, Real.rpow_neg_one]
      calc y⁻¹ * lw y ^ b ≤ y⁻¹ * (2 * lw r) ^ b := by gcongr
        _ = _ := by ring
    refine h1.trans ?_
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hr2 (by norm_num)]
    have hlog : Real.log ((1 / 16 : ℝ) / (2 * r)) ≤ lw r := by
      unfold lw
      have : Real.log ((1 / 16 : ℝ) / (2 * r)) = -Real.log 32 - Real.log r := by
        rw [Real.log_div (by norm_num) (by positivity), Real.log_mul (by norm_num) hr.ne']
        have : Real.log 32 = Real.log 16 + Real.log 2 := by
          rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
        rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
        linarith
      rw [this]
      have h0 : 0 ≤ Real.log 32 := Real.log_nonneg (by norm_num)
      have := neg_le_abs (Real.log r)
      linarith
    have hA : 0 ≤ (2 * lw r) ^ b := by have := lw_pos r; positivity
    calc (2 * lw r) ^ b * Real.log ((1 / 16 : ℝ) / (2 * r)) ≤ (2 * lw r) ^ b * lw r := by gcongr
      _ = 2 ^ b * (1 * lw r ^ (b + 1)) := by rw [mul_pow, pow_succ]; ring
      _ ≤ 2 ^ b * (1 + r ^ (0 : ℝ) * lw r ^ (b + if (0 : ℝ) = 0 then 1 else 0)) := by
          simp
  · obtain ⟨I, hI0, hI⟩ := int_scale_le he b
    refine ⟨I * (1 / 16 : ℝ) ^ e * lw (1 / 16) ^ b, by have := lw_pos (1 / 16 : ℝ); positivity,
      fun r hr hr1 => ?_⟩
    have hab : 2 * r ≤ 1 / 16 := by linarith
    have hr2 : 0 < 2 * r := by positivity
    have h1 : ∫ y in (2 * r)..(1 / 16 : ℝ), y ^ (e - 1) * lw y ^ b ≤
        ∫ y in (0 : ℝ)..(1 / 16 : ℝ), y ^ (e - 1) * lw y ^ b := by
      refine intervalIntegral.integral_mono_interval hr2.le hab le_rfl ?_ ?_
      · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun y hy => ?_)
        have := lw_pos y
        have hy0 : 0 < y := hy.1
        show 0 ≤ y ^ (e - 1) * lw y ^ b
        positivity
      · exact intervalIntegrable_rpow_lw_le he b (by norm_num) (by norm_num)
    refine h1.trans ?_
    have := hI (1 / 16) (by norm_num) (by norm_num)
    have hex : (if e = 0 then 1 else 0) = 0 := by simp [he.ne']
    rw [hex, add_zero]
    refine this.trans ?_
    have : 0 ≤ r ^ e * lw r ^ b := by have := lw_pos r; positivity
    nlinarith [mul_nonneg (mul_nonneg hI0 (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 1/16) e)) (pow_nonneg (lw_pos (1/16:ℝ)).le b)]

end HRS.Parx
