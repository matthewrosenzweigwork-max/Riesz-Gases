import HRS.Equilibrium.Parametrix.PX3aAuxH

/-!
# Packet PX3a auxiliaries I: radial estimates of integrals
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

/-- The polar-coordinates constant. -/
def cpol (d : ℕ) : ℝ := d * (volume (Metric.ball (0 : Euc d) 1)).toReal

lemma cpol_nonneg (d : ℕ) : 0 ≤ cpol d := by
  unfold cpol; positivity

/-- Integral over a small ball of a radially dominated function. -/
lemma norm_integral_ball_le (hd : 1 ≤ d) {q : ℝ} (hq : q < d) (b : ℕ) :
    ∃ I : ℝ, 0 ≤ I ∧ ∀ (R Mt : ℝ), 0 < R → R ≤ 1 → 0 ≤ Mt → ∀ ψ : Euc d → ℝ,
      (∀ᵐ x : Euc d ∂volume, ‖ψ x‖ ≤ Mt * (if ‖x‖ < R then ‖x‖ ^ (-q) * lw ‖x‖ ^ b else 0)) →
      ‖∫ x, ψ x‖ ≤ cpol d * Mt * (I * R ^ ((d : ℝ) - q) * lw R ^ b) := by
  obtain ⟨I, hI0, hI⟩ := radial_ball_le hd hq b
  refine ⟨I, hI0, fun R Mt hR hR1 hMt ψ hψ => ?_⟩
  have hint := integrableOn_rpow_lw_cut hd hq b hR hR1
  have hint' : IntegrableOn (fun y : ℝ => y ^ (d - 1) •
      (Mt * (if y < R then y ^ (-q) * lw y ^ b else 0))) (Ioi 0) := by
    have : IntegrableOn (Mt • fun y : ℝ => y ^ (d - 1) •
      (if y < R then y ^ (-q) * lw y ^ b else 0)) (Ioi 0) := hint.smul Mt
    refine IntegrableOn.congr_fun this (fun y _ => ?_) measurableSet_Ioi
    simp [smul_eq_mul]; ring
  have h1 := norm_integral_le_radial hd (φ := ψ) (f := fun y => Mt * (if y < R then y ^ (-q) * lw y ^ b else 0))
    hint' hψ
  refine h1.trans ?_
  have h2 : ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * (Mt * (if y < R then y ^ (-q) * lw y ^ b else 0)) =
      Mt * ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * (if y < R then y ^ (-q) * lw y ^ b else 0) := by
    rw [← integral_const_mul]; congr 1; ext y; ring
  rw [h2]
  have := hI R hR hR1
  have hc := cpol_nonneg d
  unfold cpol at *
  calc (↑d * (volume (Metric.ball (0 : Euc d) 1)).toReal) *
      (Mt * ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * (if y < R then y ^ (-q) * lw y ^ b else 0))
      ≤ (↑d * (volume (Metric.ball (0 : Euc d) 1)).toReal) * (Mt * (I * R ^ ((d : ℝ) - q) * lw R ^ b)) := by
        gcongr
    _ = _ := by ring

/-- Integral over an annulus `2r ≤ ‖x‖ < 1/16` of a radially dominated function. -/
lemma norm_integral_annulus_le (hd : 1 ≤ d) (q : ℝ) (b : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r Mt : ℝ), 0 < r → r ≤ 1 / 32 → 0 ≤ Mt → ∀ ψ : Euc d → ℝ,
      (∀ᵐ x : Euc d ∂volume, ‖ψ x‖ ≤ Mt * (if 2 * r ≤ ‖x‖ ∧ ‖x‖ < 1 / 16 then ‖x‖ ^ (-q) * lw ‖x‖ ^ b else 0)) →
      ‖∫ x, ψ x‖ ≤ cpol d * Mt * (C * (1 + r ^ ((d : ℝ) - q) *
        lw r ^ (b + if (d : ℝ) - q = 0 then 1 else 0))) := by
  obtain ⟨C, hC0, hC⟩ := outer_int_le ((d : ℝ) - q) b
  refine ⟨C, hC0, fun r Mt hr hr1 hMt ψ hψ => ?_⟩
  have hr2 : 0 < 2 * r := by positivity
  set G : ℝ → ℝ := fun y => y ^ (((d : ℝ) - q) - 1) * lw y ^ b with hG
  have hcont : ContinuousOn G (Icc (2 * r) (1 / 16)) := by
    have := continuousOn_rpow_lw (e := (d : ℝ) - q) b hr2 (by norm_num : (0 : ℝ) < 1 / 16)
    rwa [Set.uIcc_of_le (by linarith : 2 * r ≤ 1 / 16)] at this
  have hGint : IntegrableOn G (Icc (2 * r) (1 / 16)) := hcont.integrableOn_Icc
  set f : ℝ → ℝ := fun y => Mt * (if 2 * r ≤ y ∧ y < 1 / 16 then y ^ (-q) * lw y ^ b else 0) with hf
  have hrel : ∀ y ∈ Ioi (0 : ℝ), y ^ (d - 1) • f y = Mt • (Ico (2 * r) (1 / 16)).indicator G y := by
    intro y hy
    have hy0 : 0 < y := hy
    by_cases h : 2 * r ≤ y ∧ y < 1 / 16
    · rw [Set.indicator_of_mem (by exact ⟨h.1, h.2⟩)]
      simp only [hf, if_pos h, hG, smul_eq_mul]
      rw [show ((d : ℝ) - q) - 1 = ((d : ℝ) - 1) + (-q) by ring, Real.rpow_add hy0]
      have : y ^ (d - 1) = y ^ ((d : ℝ) - 1) := by
        rw [← Real.rpow_natCast]; congr 1; rw [Nat.cast_sub hd]; simp
      rw [this]; ring
    · rw [Set.indicator_of_notMem (by intro hh; exact h ⟨hh.1, hh.2⟩)]
      simp only [hf]
      rw [if_neg h]
      simp
  have hint : IntegrableOn (fun y : ℝ => y ^ (d - 1) • f y) (Ioi 0) := by
    have h1 : Integrable ((Ico (2 * r) (1 / 16)).indicator G) :=
      (integrable_indicator_iff measurableSet_Ico).mpr (hGint.mono_set Ico_subset_Icc_self)
    exact IntegrableOn.congr_fun (h1.smul Mt).integrableOn (fun y hy => (hrel y hy).symm) measurableSet_Ioi
  have h1 := norm_integral_le_radial hd (φ := ψ) (f := f) hint hψ
  refine h1.trans ?_
  have h2 : ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * f y = Mt * ∫ y in (2 * r)..(1 / 16 : ℝ), G y := by
    have : ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * f y =
        ∫ y in Ioi (0 : ℝ), Mt * (Ico (2 * r) (1 / 16)).indicator G y := by
      refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
      have := hrel y hy
      simpa [smul_eq_mul] using this
    rw [this, integral_const_mul]
    congr 1
    have hset : Ioi (0 : ℝ) ∩ Ico (2 * r) (1 / 16) = Ico (2 * r) (1 / 16) :=
      Set.inter_eq_right.mpr (fun y hy => lt_of_lt_of_le hr2 hy.1)
    rw [setIntegral_indicator measurableSet_Ico, hset]
    rw [intervalIntegral.integral_of_le (by linarith : 2 * r ≤ 1 / 16), integral_Ioc_eq_integral_Ioo,
      integral_Ico_eq_integral_Ioo]
  rw [h2]
  have := hC r hr hr1
  have hc := cpol_nonneg d
  calc cpol d * (Mt * ∫ y in (2 * r)..(1 / 16 : ℝ), G y)
      ≤ cpol d * (Mt * (C * (1 + r ^ ((d : ℝ) - q) * lw r ^ (b + if (d : ℝ) - q = 0 then 1 else 0)))) := by
        gcongr
    _ = _ := by ring

lemma Efund_abs_le (hd : 2 ≤ d) : ∃ c : ℝ, 0 ≤ c ∧ ∀ u : Euc d, u ≠ 0 →
    |Efund d u| ≤ c * (‖u‖ ^ (-((d : ℝ) - 2)) * lw ‖u‖ ^ (if d = 2 then 1 else 0)) := by
  by_cases h2 : d = 2
  · subst h2
    refine ⟨1 / (2 * Real.pi), by positivity, fun u hu => ?_⟩
    have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
    simp only [Efund, e0, if_true, Nat.cast_ofNat, sub_self, neg_zero, Real.rpow_zero, one_mul, pow_one, if_true]
    rw [Real.log_pow, abs_mul]
    push_cast
    have : |(-(1 / (4 * Real.pi)))| = 1 / (4 * Real.pi) := by
      rw [abs_neg, abs_of_pos (by positivity)]
    rw [this, abs_mul, abs_two]
    unfold lw
    have hp : 0 < Real.pi := Real.pi_pos
    have : 1 / (4 * Real.pi) * (2 * |Real.log ‖u‖|) = 1 / (2 * Real.pi) * |Real.log ‖u‖| := by
      field_simp; ring
    rw [this]
    have : 0 < 1 / (2 * Real.pi) := by positivity
    nlinarith
  · have hd3 : 3 ≤ d := by omega
    have hc : 0 ≤ newtonC d / ((d : ℝ) - 2) := by
      have : (0 : ℝ) < (d : ℝ) - 2 := by
        have : (3 : ℝ) ≤ d := by exact_mod_cast hd3
        linarith
      have := newtonC_pos (d := d) (by omega)
      positivity
    refine ⟨newtonC d / ((d : ℝ) - 2), hc, fun u hu => ?_⟩
    have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
    simp only [Efund, e0, h2, if_false, if_neg h2, pow_zero, mul_one]
    have : (‖u‖ ^ 2) ^ (((2 : ℝ) - d) / 2) = ‖u‖ ^ (-((d : ℝ) - 2)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
      congr 1; push_cast; ring
    rw [this, abs_of_nonneg (by positivity)]

lemma ae_ne_zero_euc (hd : 1 ≤ d) : ∀ᵐ x : Euc d ∂(volume : Measure (Euc d)), x ≠ 0 := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have := (Set.countable_singleton (0 : Euc d)).ae_notMem (volume : Measure (Euc d))
  filter_upwards [this] with w hw using by simpa using hw

/-- Near integral with `κ = 0`. -/
lemma near_integral_zero (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ Mt : ℝ), 0 < ρ → ρ ≤ 1 → 0 ≤ Mt → ∀ ψ : Euc d → ℝ,
      (∀ x, ‖ψ x‖ ≤ Mt * ‖Ln d 0 ρ x‖) →
      ‖∫ x, ψ x‖ ≤ C * Mt * (ρ ^ (2 : ℝ) * lw ρ ^ (if d = 2 then 1 else 0)) := by
  obtain ⟨c, hc0, hc⟩ := Efund_abs_le hd
  obtain ⟨I, hI0, hI⟩ := norm_integral_ball_le (d := d) (by omega) (q := (d : ℝ) - 2)
    (by linarith) (if d = 2 then 1 else 0)
  refine ⟨cpol d * c * I, by have := cpol_nonneg d; positivity, fun ρ Mt hρ hρ1 hMt ψ hψ => ?_⟩
  have key := hI ρ (Mt * c) hρ hρ1 (by positivity) ψ ?_
  · refine key.trans (le_of_eq ?_)
    have : (d : ℝ) - ((d : ℝ) - 2) = 2 := by ring
    rw [this]; ring
  · filter_upwards [ae_ne_zero_euc (by omega : 1 ≤ d)] with x hx
    refine (hψ x).trans ?_
    by_cases hxρ : ‖x‖ < ρ
    · simp only [if_pos hxρ]
      have h1 : ‖Ln d 0 ρ x‖ ≤ |Efund d x| := by
        simp only [Ln, sub_zero, norm_mul, Real.norm_eq_abs]
        rw [abs_of_nonneg (px3a_zeta_nonneg ρ x)]
        calc px3a_zeta d ρ x * |Efund d x| ≤ 1 * |Efund d x| := by
              gcongr; exact px3a_zeta_le_one ρ x
          _ = _ := one_mul _
      calc Mt * ‖Ln d 0 ρ x‖ ≤ Mt * (c * (‖x‖ ^ (-((d : ℝ) - 2)) * lw ‖x‖ ^ (if d = 2 then 1 else 0))) := by
            gcongr; exact h1.trans (hc x hx)
        _ = _ := by ring
    · simp only [if_neg hxρ, mul_zero]
      have : Ln d 0 ρ x = 0 := by simp [Ln, px3a_zeta_eq_zero hρ (not_lt.mp hxρ)]
      simp [this]

lemma Efund_sub_Ekap_two {r : ℝ} (hr : 0 < r) {x : Euc 2} (hx : x ≠ 0) (hxr : ‖x‖ < r) :
    |Efund 2 x - Ekap 2 r| ≤ (1 / Real.pi) * (r ^ ((1 : ℝ) / 2) * ‖x‖ ^ (-((1 : ℝ) / 2))) := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hp : 0 < Real.pi := Real.pi_pos
  have e1 : Efund 2 x - Ekap 2 r = (1 / (2 * Real.pi)) * Real.log (r / ‖x‖) := by
    simp only [Efund, e0, Ekap, if_true]
    rw [Real.log_pow, Real.log_pow, Real.log_div hr.ne' hn.ne']
    push_cast
    field_simp
    ring
  have hlog : Real.log (r / ‖x‖) ≤ 2 * (r / ‖x‖) ^ ((1 : ℝ) / 2) := by
    have := Real.log_le_rpow_div (div_nonneg hr.le hn.le) (by norm_num : (0 : ℝ) < 1 / 2)
    linarith [show (r / ‖x‖) ^ ((1 : ℝ) / 2) / (1 / 2) = 2 * (r / ‖x‖) ^ ((1 : ℝ) / 2) by ring]
  have hpos : 0 ≤ Real.log (r / ‖x‖) := Real.log_nonneg (by rw [le_div_iff₀ hn]; linarith)
  rw [e1, abs_of_nonneg (by positivity)]
  have e2 : (r / ‖x‖) ^ ((1 : ℝ) / 2) = r ^ ((1 : ℝ) / 2) * ‖x‖ ^ (-((1 : ℝ) / 2)) := by
    rw [Real.div_rpow hr.le hn.le, Real.rpow_neg hn.le]; ring
  rw [e2] at hlog
  calc 1 / (2 * Real.pi) * Real.log (r / ‖x‖)
      ≤ 1 / (2 * Real.pi) * (2 * (r ^ ((1 : ℝ) / 2) * ‖x‖ ^ (-((1 : ℝ) / 2)))) := by gcongr
    _ = _ := by field_simp

/-- Near integral for `d = 2` with the subtraction `κ = Ekap`. -/
lemma near_integral_two :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r Mt : ℝ), 0 < r → r ≤ 1 → 0 ≤ Mt → ∀ ψ : Euc 2 → ℝ,
      (∀ x, ‖ψ x‖ ≤ Mt * ‖Ln 2 (Ekap 2 r) (r / 8) x‖) →
      ‖∫ x, ψ x‖ ≤ C * Mt * r ^ (2 : ℝ) := by
  obtain ⟨I, hI0, hI⟩ := norm_integral_ball_le (d := 2) (by norm_num) (q := (1 : ℝ) / 2)
    (by norm_num) 0
  refine ⟨cpol 2 * (1 / Real.pi) * I, by have := cpol_nonneg 2; positivity, fun r Mt hr hr1 hMt ψ hψ => ?_⟩
  have hρ : 0 < r / 8 := by positivity
  have key := hI (r / 8) (Mt * ((1 / Real.pi) * r ^ ((1 : ℝ) / 2))) hρ (by linarith) (by positivity) ψ ?_
  · refine key.trans ?_
    have h1 : (r / 8) ^ (((2 : ℕ) : ℝ) - 1 / 2) = r ^ (3 / 2 : ℝ) / 8 ^ (3 / 2 : ℝ) := by
      rw [Real.div_rpow hr.le (by norm_num)]; norm_num
    have h2 : r ^ ((1 : ℝ) / 2) * r ^ (3 / 2 : ℝ) = r ^ (2 : ℝ) := by
      rw [← Real.rpow_add hr]; norm_num
    simp only [pow_zero, mul_one]
    rw [h1]
    have h8 : (1 : ℝ) ≤ 8 ^ (3 / 2 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
    have hc := cpol_nonneg 2
    calc cpol 2 * (Mt * (1 / Real.pi * r ^ ((1 : ℝ) / 2))) * (I * (r ^ (3 / 2 : ℝ) / 8 ^ (3 / 2 : ℝ)))
        = (cpol 2 * (1 / Real.pi) * I * Mt) * ((r ^ ((1 : ℝ) / 2) * r ^ (3 / 2 : ℝ)) / 8 ^ (3 / 2 : ℝ)) := by ring
      _ = (cpol 2 * (1 / Real.pi) * I * Mt) * (r ^ (2 : ℝ) / 8 ^ (3 / 2 : ℝ)) := by rw [h2]
      _ ≤ (cpol 2 * (1 / Real.pi) * I * Mt) * r ^ (2 : ℝ) := by
          gcongr
          exact div_le_self (by positivity) h8
  · filter_upwards [ae_ne_zero_euc (by norm_num : 1 ≤ 2)] with x hx
    refine (hψ x).trans ?_
    by_cases hxρ : ‖x‖ < r / 8
    · simp only [if_pos hxρ]
      have h1 : ‖Ln 2 (Ekap 2 r) (r / 8) x‖ ≤ |Efund 2 x - Ekap 2 r| := by
        simp only [Ln, norm_mul, Real.norm_eq_abs]
        rw [abs_of_nonneg (px3a_zeta_nonneg (r / 8) x)]
        calc px3a_zeta 2 (r / 8) x * |Efund 2 x - Ekap 2 r| ≤ 1 * |Efund 2 x - Ekap 2 r| := by
              gcongr; exact px3a_zeta_le_one _ x
          _ = _ := one_mul _
      have h2 := Efund_sub_Ekap_two hr hx (by linarith)
      simp only [pow_zero, mul_one]
      calc Mt * ‖Ln 2 (Ekap 2 r) (r / 8) x‖ ≤ Mt * ((1 / Real.pi) * (r ^ ((1 : ℝ) / 2) * ‖x‖ ^ (-((1 : ℝ) / 2)))) := by
            gcongr; exact h1.trans h2
        _ = _ := by ring
    · simp only [if_neg hxρ, mul_zero]
      have : Ln 2 (Ekap 2 r) (r / 8) x = 0 := by simp [Ln, px3a_zeta_eq_zero hρ (not_lt.mp hxρ)]
      simp [this]

/-- Two-region estimate for the far integral. -/
lemma far_estimate (hd : 2 ≤ d) {σ : ℝ} (hσ : σ < d) (q : ℝ) (b : ℕ) :
    ∃ C1 C2 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧ ∀ (r M1 M2 : ℝ), 0 < r → r < 1 / 8 → 0 ≤ M1 → 0 ≤ M2 →
      ∀ ψ : Euc d → ℝ, Integrable ψ →
      (∀ᵐ w : Euc d ∂volume, ‖w‖ < 2 * r → ‖ψ w‖ ≤ M1 * (‖w‖ ^ (-σ) * lw ‖w‖ ^ b)) →
      (∀ᵐ w : Euc d ∂volume, 2 * r ≤ ‖w‖ → ‖w‖ < 1 / 16 → ‖ψ w‖ ≤ M2 * (‖w‖ ^ (-q) * lw ‖w‖ ^ b)) →
      (∀ᵐ w : Euc d ∂volume, 1 / 16 ≤ ‖w‖ → ψ w = 0) →
      ‖∫ w, ψ w‖ ≤ C1 * M1 * (r ^ ((d : ℝ) - σ) * lw r ^ b) +
        C2 * M2 * (1 + r ^ ((d : ℝ) - q) * lw r ^ (b + if (d : ℝ) - q = 0 then 1 else 0)) := by
  obtain ⟨I, hI0, hI⟩ := norm_integral_ball_le (d := d) (by omega) hσ b
  obtain ⟨C, hC0, hC⟩ := norm_integral_annulus_le (d := d) (by omega) q b
  refine ⟨cpol d * I * 2 ^ ((d : ℝ) - σ) * 2 ^ b, cpol d * C, by have := cpol_nonneg d; positivity,
    by have := cpol_nonneg d; positivity, fun r M1 M2 hr hr1 hM1 hM2 ψ hψi h1 h2 h3 => ?_⟩
  set ψ1 : Euc d → ℝ := fun w => if ‖w‖ < 2 * r then ψ w else 0 with hψ1
  set ψ2 : Euc d → ℝ := fun w => if 2 * r ≤ ‖w‖ then ψ w else 0 with hψ2
  have hm1 : MeasurableSet {w : Euc d | ‖w‖ < 2 * r} := measurableSet_lt measurable_norm measurable_const
  have hm2 : MeasurableSet {w : Euc d | 2 * r ≤ ‖w‖} := measurableSet_le measurable_const measurable_norm
  have hi1 : Integrable ψ1 := hψi.indicator hm1 |>.congr (Eventually.of_forall fun w => by
    simp [hψ1, Set.indicator])
  have hi2 : Integrable ψ2 := hψi.indicator hm2 |>.congr (Eventually.of_forall fun w => by
    simp [hψ2, Set.indicator])
  have hsum : ∫ w, ψ w = (∫ w, ψ1 w) + ∫ w, ψ2 w := by
    rw [← integral_add hi1 hi2]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    by_cases h : ‖w‖ < 2 * r
    · simp [hψ1, hψ2, h, not_le.mpr h]
    · simp [hψ1, hψ2, h, not_lt.mp h]
  rw [hsum]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · have key := hI (2 * r) M1 (by positivity) (by linarith) hM1 ψ1 ?_
    · refine key.trans ?_
      have h2r : lw (2 * r) ≤ 2 * lw r := by
        calc lw (2 * r) ≤ lw 2 * lw r := lw_mul_le (by norm_num) hr
          _ ≤ 2 * lw r := by have := lw_pos r; nlinarith [lw_two_le]
      have hpow : lw (2 * r) ^ b ≤ 2 ^ b * lw r ^ b := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (lw_pos _).le h2r b
      rw [Real.mul_rpow (by norm_num) hr.le]
      have := cpol_nonneg d
      have : 0 ≤ r ^ ((d : ℝ) - σ) := by positivity
      calc cpol d * M1 * (I * (2 ^ ((d : ℝ) - σ) * r ^ ((d : ℝ) - σ)) * lw (2 * r) ^ b)
          ≤ cpol d * M1 * (I * (2 ^ ((d : ℝ) - σ) * r ^ ((d : ℝ) - σ)) * (2 ^ b * lw r ^ b)) := by gcongr
        _ = _ := by ring
    · filter_upwards [h1] with w hw
      by_cases h : ‖w‖ < 2 * r
      · simp only [hψ1, if_pos h, if_pos h]; exact hw h
      · simp [hψ1, h]
  · by_cases hr32 : r ≤ 1 / 32
    · have key := hC r M2 hr hr32 hM2 ψ2 ?_
      · refine key.trans (le_of_eq ?_); ring
      · filter_upwards [h2, h3] with w hw hw3
        by_cases h : 2 * r ≤ ‖w‖
        · by_cases h' : ‖w‖ < 1 / 16
          · simp only [hψ2, if_pos h, if_pos (And.intro h h')]; exact hw h h'
          · have hn : ¬(2 * r ≤ ‖w‖ ∧ ‖w‖ < 1 / 16) := fun hh => h' hh.2
            simp only [hψ2, if_pos h, hw3 (not_lt.mp h'), norm_zero]
            rw [if_neg hn]; simp
        · have hn : ¬(2 * r ≤ ‖w‖ ∧ ‖w‖ < 1 / 16) := fun hh => h hh.1
          simp only [hψ2, if_neg h, norm_zero]
          rw [if_neg hn]; simp
    · have : ∫ w, ψ2 w = 0 := by
        refine integral_eq_zero_of_ae ?_
        filter_upwards [h3] with w hw3
        by_cases h : 2 * r ≤ ‖w‖
        · simp [hψ2, h, hw3 (by linarith [not_le.mp hr32])]
        · simp [hψ2, h]
      rw [this, norm_zero]
      have := cpol_nonneg d
      have : 0 ≤ r ^ ((d : ℝ) - q) * lw r ^ (b + if (d : ℝ) - q = 0 then 1 else 0) := by
        have := lw_pos r; positivity
      positivity

end HRS.Parx

end
