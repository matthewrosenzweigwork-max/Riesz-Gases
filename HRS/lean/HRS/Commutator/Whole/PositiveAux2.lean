import HRS.Commutator.Whole.PositiveAux

/-!
# Helpers for `Positive.lean` (packet `CMX-POS`), part B

The spatial formulas for `f_1` and `g_1`, the integrals `∫ r^{s-1} φ(r) dr`, positivity of `c_φ`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

/-- Change of variables `r = ρ / t`. -/
lemma cov_inv (F : ℝ → ℝ) {ρ : ℝ} (hρ : 0 < ρ) (s : ℝ) :
    ∫ t in Set.Ioc (0:ℝ) 1, t ^ (-s - 1) * F (ρ / t) =
      ρ ^ (-s) * ∫ r in Set.Ioi ρ, r ^ (s - 1) * F r := by
  have himg : (fun t : ℝ => ρ / t) '' Set.Ioo 0 1 = Set.Ioi ρ := by
    ext r; constructor
    · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
      simp only [Set.mem_Ioi]
      rw [lt_div_iff₀ ht0]; nlinarith
    · intro hr
      have hr : ρ < r := hr
      have hr0 : 0 < r := hρ.trans hr
      refine ⟨ρ / r, ⟨by positivity, ?_⟩, ?_⟩
      · rw [div_lt_one hr0]; exact hr
      · field_simp
  have h := integral_image_eq_integral_abs_deriv_smul (s := Set.Ioo (0:ℝ) 1)
    (f := fun t : ℝ => ρ / t) (f' := fun t : ℝ => -(ρ / t ^ 2)) measurableSet_Ioo
    (fun t ht => by
      have := (hasDerivAt_inv ht.1.ne').const_mul ρ
      have h2 : HasDerivAt (fun t : ℝ => ρ / t) (-(ρ / t ^ 2)) t := by
        simpa [div_eq_mul_inv, neg_div] using (hasDerivAt_inv ht.1.ne').const_mul ρ
      exact h2.hasDerivWithinAt)
    (by
      intro a ha b hb hab
      have := ha.1; have := hb.1
      field_simp at hab
      nlinarith [hab]) (fun r => r ^ (s - 1) * F r)
  rw [himg] at h
  rw [h, ← integral_Ioc_eq_integral_Ioo, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
  have ht0 : 0 < t := ht.1
  simp only [smul_eq_mul]
  rw [abs_neg, abs_of_pos (by positivity), Real.div_rpow hρ.le ht0.le]
  have : t ^ (-s - 1) * F (ρ / t) =
      ρ ^ (-s) * (ρ / t ^ 2 * (ρ ^ (s - 1) / t ^ (s - 1) * F (ρ / t))) := by
    have h1 : ρ ^ (s - 1) = ρ ^ s / ρ := by
      rw [Real.rpow_sub hρ, Real.rpow_one]
    have h2 : t ^ (s - 1) = t ^ s / t := by
      rw [Real.rpow_sub ht0, Real.rpow_one]
    have h3 : t ^ (-s - 1) = (t ^ s)⁻¹ / t := by
      rw [Real.rpow_sub ht0, Real.rpow_one, Real.rpow_neg ht0.le]
    have h4 : ρ ^ (-s) = (ρ ^ s)⁻¹ := Real.rpow_neg hρ.le s
    have hp1 : 0 < ρ ^ s := Real.rpow_pos_of_pos hρ s
    have hp2 : 0 < t ^ s := Real.rpow_pos_of_pos ht0 s
    rw [h1, h2, h3, h4]
    field_simp
  exact this


lemma phiT_eq {t : ℝ} (ht : 0 < t) (x : Euc d) :
    phiT t x = t ^ (-(d : ℝ)) * phiR d (‖x‖ / t) := by
  unfold phiT
  rw [phi_eq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht, inv_mul_eq_div]

lemma integrand_eq {t : ℝ} (ht : 0 < t) (x : Euc d) :
    t ^ ((d : ℝ) - s) * phiT t x / t = t ^ (-s - 1) * phiR d (‖x‖ / t) := by
  rw [phiT_eq ht]
  have : t ^ ((d : ℝ) - s) * (t ^ (-(d : ℝ)) * phiR d (‖x‖ / t)) =
      t ^ (-s) * phiR d (‖x‖ / t) := by
    rw [← mul_assoc, ← Real.rpow_add ht]; congr 2; ring
  rw [this, Real.rpow_sub ht, Real.rpow_one, Real.rpow_neg ht.le]
  field_simp

lemma fTrunc_eq (x : Euc d) :
    fTrunc s 1 x = cPhi d s * ∫ t in Set.Ioc (0:ℝ) 1, t ^ (-s - 1) * phiR d (‖x‖ / t) := by
  unfold fTrunc
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
  exact integrand_eq ht.1 x

/-- the tail integral `∫_ρ^∞ r^{s-1} φ(r) dr`. -/
lemma integrableOn_tail (d : ℕ) {s a : ℝ} (ha : 0 < a) (hs : s < 2 * (d : ℝ) + 4) :
    IntegrableOn (fun r : ℝ => r ^ (s - 1) * phiR d r) (Set.Ioi a) := by
  have h1 : IntegrableOn (fun r : ℝ => r ^ (s - 1 + (-(2 * (d : ℝ) + 4)))) (Set.Ioi a) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) ha
  refine Integrable.mono' h1 ?_ ?_
  · have : Measurable (fun r : ℝ => r ^ (s - 1) * phiR d r) := by
      have := continuous_phiR (d := d)
      fun_prop
    exact this.aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := a))] with r hr
    have hr0 : 0 < r := ha.trans hr
    rw [Real.norm_of_nonneg (by have := phiR_pos (d := d) r; positivity), Real.rpow_add hr0]
    exact mul_le_mul_of_nonneg_left (phiR_le_pow hr0) (by positivity)

lemma integrableOn_near (d : ℕ) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun r : ℝ => r ^ (s - 1) * phiR d r) (Set.Ioc 0 1) := by
  have h1 : IntegrableOn (fun r : ℝ => r ^ (s - 1)) (Set.Ioc 0 1) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := s - 1) (by linarith))
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 this
  refine Integrable.mono' h1 ?_ ?_
  · have : Measurable (fun r : ℝ => r ^ (s - 1) * phiR d r) := by
      have := continuous_phiR (d := d)
      fun_prop
    exact this.aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict (measurableSet_Ioc (a := (0:ℝ)) (b := 1))] with r hr
    have hr0 : 0 < r := hr.1
    rw [Real.norm_of_nonneg (by have := phiR_pos (d := d) r; positivity)]
    calc r ^ (s - 1) * phiR d r ≤ r ^ (s - 1) * 1 :=
          mul_le_mul_of_nonneg_left (phiR_le_one r) (by positivity)
      _ = r ^ (s - 1) := mul_one _

lemma integrableOn_all (d : ℕ) {s : ℝ} (hs : 0 < s) (hs2 : s < 2 * (d : ℝ) + 4) :
    IntegrableOn (fun r : ℝ => r ^ (s - 1) * phiR d r) (Set.Ioi 0) := by
  have h1 := integrableOn_near d hs
  have h2 := integrableOn_tail d (s := s) one_pos hs2
  have : Set.Ioi (0:ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 := (Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [this]
  exact h1.union h2

lemma tail_pos (d : ℕ) {s ρ : ℝ} (hρ : 0 < ρ) (hs : s < 2 * (d : ℝ) + 4) :
    0 < ∫ r in Set.Ioi ρ, r ^ (s - 1) * phiR d r := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · have : Function.support (fun r : ℝ => r ^ (s - 1) * phiR d r) ∩ Set.Ioi ρ = Set.Ioi ρ := by
      ext r; constructor
      · exact fun h => h.2
      · intro hr
        have hr0 : 0 < r := hρ.trans hr
        exact ⟨(mul_pos (Real.rpow_pos_of_pos hr0 _) (phiR_pos r)).ne', hr⟩
    rw [this]; simp
  · filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := ρ))] with r hr
    have hr0 : 0 < r := hρ.trans hr
    have := phiR_pos (d := d) r
    positivity
  · exact integrableOn_tail d hρ hs

lemma all_pos (d : ℕ) {s : ℝ} (hs : 0 < s) (hs2 : s < 2 * (d : ℝ) + 4) :
    0 < ∫ r in Set.Ioi (0:ℝ), r ^ (s - 1) * phiR d r := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · have : Function.support (fun r : ℝ => r ^ (s - 1) * phiR d r) ∩ Set.Ioi 0 = Set.Ioi 0 := by
      ext r; constructor
      · exact fun h => h.2
      · intro hr
        have hr0 : 0 < r := hr
        exact ⟨(mul_pos (Real.rpow_pos_of_pos hr0 _) (phiR_pos r)).ne', hr⟩
    rw [this]; simp
  · filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0:ℝ)))] with r hr
    have hr0 : 0 < r := hr
    have := phiR_pos (d := d) r
    positivity
  · exact integrableOn_all d hs hs2

lemma cPhi_pos (d : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs2 : s < 2 * (d : ℝ) + 4) : 0 < cPhi d s := by
  unfold cPhi
  by_cases h : s = 0
  · simp [h]
  · have hs : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h)
    simp only [h, ite_false]
    exact inv_pos.2 (mul_pos hs (all_pos d hs hs2))

lemma cPhi_mul (d : ℕ) {s : ℝ} (hs : 0 < s) (hs2 : s < 2 * (d : ℝ) + 4) :
    s * cPhi d s * ∫ r in Set.Ioi (0:ℝ), r ^ (s - 1) * phiR d r = 1 := by
  unfold cPhi
  simp only [hs.ne', ↓reduceIte]
  have := all_pos d hs hs2
  field_simp

theorem fTrunc_spatial_aux (x : Euc d) (hx : x ≠ 0) :
    fTrunc s 1 x =
      if s = 0 then ∫ r in Set.Ioi ‖x‖, phiR d r / r
      else cPhi d s * ‖x‖ ^ (-s) * ∫ r in Set.Ioi ‖x‖, r ^ (s - 1) * phiR d r := by
  have hρ : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [fTrunc_eq, cov_inv (phiR d) hρ s]
  split_ifs with h
  · subst h
    simp only [cPhi, ite_true, neg_zero, Real.rpow_zero, one_mul, zero_sub]
    refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
    rw [Real.rpow_neg_one]; ring
  · ring


lemma fTrunc_eq_tail (hs0 : 0 ≤ s) (x : Euc d) (hx : x ≠ 0) :
    fTrunc s 1 x = cPhi d s * ‖x‖ ^ (-s) * ∫ r in Set.Ioi ‖x‖, r ^ (s - 1) * phiR d r := by
  rw [fTrunc_spatial_aux x hx]
  split_ifs with h
  · subst h
    simp only [cPhi, ite_true, neg_zero, Real.rpow_zero, mul_one, one_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
    rw [zero_sub, Real.rpow_neg_one]; ring
  · rfl

theorem fTrunc_pos_aux (hs0 : 0 ≤ s) (hs2 : s < 2 * (d : ℝ) + 4) (x : Euc d) (hx : x ≠ 0) :
    0 < fTrunc s 1 x := by
  have hρ : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [fTrunc_eq_tail hs0 x hx]
  exact mul_pos (mul_pos (cPhi_pos d hs0 hs2) (Real.rpow_pos_of_pos hρ _)) (tail_pos d hρ hs2)

/-- far field bounds. -/
lemma cmp_far (hs0 : 0 ≤ s) (hs2 : s < 2 * (d : ℝ) + 4) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : Euc d, 1 ≤ ‖x‖ →
      c * ‖x‖ ^ (-(2 * (d : ℝ) + 4)) ≤ fTrunc s 1 x ∧ fTrunc s 1 x ≤ C * ‖x‖ ^ (-(2 * (d : ℝ) + 4)) := by
  have hcp := cPhi_pos d hs0 hs2
  have hk : 0 < 2 * (d : ℝ) + 4 - s := by linarith
  refine ⟨cPhi d s * (2:ℝ) ^ (-((d:ℝ) + 2)) / (2 * (d : ℝ) + 4 - s), cPhi d s / (2 * (d : ℝ) + 4 - s),
    by positivity, by positivity, fun x hx => ?_⟩
  have hx0 : x ≠ 0 := by
    intro h; rw [h, norm_zero] at hx; linarith
  have hρ : 0 < ‖x‖ := by linarith
  rw [fTrunc_eq_tail hs0 x hx0]
  set ρ := ‖x‖ with hρdef
  have hI : ∫ r in Set.Ioi ρ, r ^ (s - 1 + (-(2 * (d : ℝ) + 4))) =
      ρ ^ (s - (2 * (d : ℝ) + 4)) / (2 * (d : ℝ) + 4 - s) := by
    rw [integral_Ioi_rpow_of_lt (by linarith) hρ]
    have : s - 1 + -(2 * (d : ℝ) + 4) + 1 = s - (2 * (d : ℝ) + 4) := by ring
    have e2 : 2 * (d : ℝ) + 4 - s = -(s - (2 * (d : ℝ) + 4)) := by ring
    rw [this, e2, div_neg, neg_div]
  have hint1 : IntegrableOn (fun r : ℝ => r ^ (s - 1 + (-(2 * (d : ℝ) + 4)))) (Set.Ioi ρ) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hρ
  have hint2 := integrableOn_tail d (s := s) hρ hs2
  have key : ρ ^ (-s) * ρ ^ (s - (2 * (d : ℝ) + 4)) = ρ ^ (-(2 * (d : ℝ) + 4)) := by
    rw [← Real.rpow_add hρ]; congr 1; ring
  constructor
  · -- lower
    have h1 : ∫ r in Set.Ioi ρ, (2:ℝ) ^ (-((d:ℝ) + 2)) * r ^ (s - 1 + (-(2 * (d : ℝ) + 4))) ≤
        ∫ r in Set.Ioi ρ, r ^ (s - 1) * phiR d r := by
      refine setIntegral_mono_on (hint1.const_mul _) hint2 measurableSet_Ioi (fun r hr => ?_)
      have hr1 : 1 ≤ r := le_trans hx (le_of_lt hr)
      have hr0 : 0 < r := by linarith
      have := phiR_ge_pow (d := d) hr1
      rw [Real.rpow_add hr0]
      calc (2:ℝ) ^ (-((d:ℝ) + 2)) * (r ^ (s - 1) * r ^ (-(2 * (d : ℝ) + 4)))
          = r ^ (s - 1) * ((2:ℝ) ^ (-((d:ℝ) + 2)) * r ^ (-(2 * (d : ℝ) + 4))) := by ring
        _ ≤ r ^ (s - 1) * phiR d r := mul_le_mul_of_nonneg_left this (by positivity)
    rw [integral_const_mul, hI] at h1
    calc cPhi d s * (2:ℝ) ^ (-((d:ℝ) + 2)) / (2 * (d : ℝ) + 4 - s) * ρ ^ (-(2 * (d : ℝ) + 4))
        = cPhi d s * ρ ^ (-s) * ((2:ℝ) ^ (-((d:ℝ) + 2)) * (ρ ^ (s - (2 * (d : ℝ) + 4)) / (2 * (d : ℝ) + 4 - s))) := by
          rw [← key]; ring
      _ ≤ cPhi d s * ρ ^ (-s) * ∫ r in Set.Ioi ρ, r ^ (s - 1) * phiR d r := by
          gcongr
  · -- upper
    have h1 : ∫ r in Set.Ioi ρ, r ^ (s - 1) * phiR d r ≤
        ∫ r in Set.Ioi ρ, r ^ (s - 1 + (-(2 * (d : ℝ) + 4))) := by
      refine setIntegral_mono_on hint2 hint1 measurableSet_Ioi (fun r hr => ?_)
      have hr0 : 0 < r := hρ.trans hr
      rw [Real.rpow_add hr0]
      exact mul_le_mul_of_nonneg_left (phiR_le_pow hr0) (by positivity)
    rw [hI] at h1
    calc cPhi d s * ρ ^ (-s) * ∫ r in Set.Ioi ρ, r ^ (s - 1) * phiR d r
        ≤ cPhi d s * ρ ^ (-s) * (ρ ^ (s - (2 * (d : ℝ) + 4)) / (2 * (d : ℝ) + 4 - s)) := by
          gcongr
      _ = cPhi d s / (2 * (d : ℝ) + 4 - s) * ρ ^ (-(2 * (d : ℝ) + 4)) := by
          rw [← key]; ring


lemma cmp_near_pos (hs : 0 < s) (hs2 : s < 2 * (d : ℝ) + 4) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : Euc d, x ≠ 0 → ‖x‖ ≤ 1 →
      c * ‖x‖ ^ (-s) ≤ fTrunc s 1 x ∧ fTrunc s 1 x ≤ C * ‖x‖ ^ (-s) := by
  have hcp := cPhi_pos d hs.le hs2
  have hm := tail_pos d (s := s) one_pos hs2
  have hJ := cPhi_mul d hs hs2
  refine ⟨cPhi d s * ∫ r in Set.Ioi (1:ℝ), r ^ (s - 1) * phiR d r, 1 / s, by positivity, by positivity,
    fun x hx0 hx1 => ?_⟩
  have hρ : 0 < ‖x‖ := norm_pos_iff.2 hx0
  rw [fTrunc_eq_tail hs.le x hx0]
  set ρ := ‖x‖ with hρdef
  have hpos : 0 < ρ ^ (-s) := Real.rpow_pos_of_pos hρ _
  constructor
  · have : ∫ r in Set.Ioi (1:ℝ), r ^ (s - 1) * phiR d r ≤ ∫ r in Set.Ioi ρ, r ^ (s - 1) * phiR d r := by
      refine setIntegral_mono_set (integrableOn_tail d hρ hs2) ?_ ?_
      · filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := ρ))] with r hr
        have hr0 : 0 < r := hρ.trans hr
        have := phiR_pos (d := d) r
        simp only [Pi.zero_apply]
        positivity
      · exact Filter.Eventually.of_forall (Set.Ioi_subset_Ioi hx1)
    calc cPhi d s * (∫ r in Set.Ioi (1:ℝ), r ^ (s - 1) * phiR d r) * ρ ^ (-s)
        = cPhi d s * ρ ^ (-s) * ∫ r in Set.Ioi (1:ℝ), r ^ (s - 1) * phiR d r := by ring
      _ ≤ _ := by gcongr
  · have : ∫ r in Set.Ioi ρ, r ^ (s - 1) * phiR d r ≤ ∫ r in Set.Ioi (0:ℝ), r ^ (s - 1) * phiR d r := by
      refine setIntegral_mono_set (integrableOn_all d hs hs2) ?_ ?_
      · filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0:ℝ)))] with r hr
        have hr0 : 0 < r := hr
        have := phiR_pos (d := d) r
        simp only [Pi.zero_apply]
        positivity
      · exact Filter.Eventually.of_forall (Set.Ioi_subset_Ioi hρ.le)
    calc cPhi d s * ρ ^ (-s) * ∫ r in Set.Ioi ρ, r ^ (s - 1) * phiR d r
        ≤ cPhi d s * ρ ^ (-s) * ∫ r in Set.Ioi (0:ℝ), r ^ (s - 1) * phiR d r := by gcongr
      _ = 1 / s * ρ ^ (-s) := by
          have : cPhi d s * ∫ r in Set.Ioi (0:ℝ), r ^ (s - 1) * phiR d r = 1 / s := by
            field_simp; linarith
          rw [← this]; ring

lemma cmp_near_zero (hs : s = 0) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : Euc d, x ≠ 0 → ‖x‖ ≤ 1 →
      c * (1 + |Real.log ‖x‖|) ≤ fTrunc s 1 x ∧ fTrunc s 1 x ≤ C * (1 + |Real.log ‖x‖|) := by
  subst hs
  have hs2 : (0:ℝ) < 2 * (d : ℝ) + 4 := by positivity
  have hm := tail_pos d (s := 0) one_pos hs2
  set m := ∫ r in Set.Ioi (1:ℝ), r ^ ((0:ℝ) - 1) * phiR d r with hmdef
  refine ⟨min ((2:ℝ) ^ (-((d:ℝ) + 2))) m, max 1 m, lt_min (by positivity) hm, lt_max_of_lt_left one_pos,
    fun x hx0 hx1 => ?_⟩
  have hρ : 0 < ‖x‖ := norm_pos_iff.2 hx0
  rw [fTrunc_eq_tail le_rfl x hx0]
  set ρ := ‖x‖ with hρdef
  have hcp : cPhi d 0 = 1 := by simp [cPhi]
  rw [hcp, neg_zero, Real.rpow_zero, one_mul, one_mul]
  have hI1 : IntegrableOn (fun r : ℝ => r ^ ((0:ℝ) - 1) * phiR d r) (Set.Ioc ρ 1) :=
    (integrableOn_tail d hρ hs2).mono_set Set.Ioc_subset_Ioi_self
  have hsplit : ∫ r in Set.Ioi ρ, r ^ ((0:ℝ) - 1) * phiR d r =
      (∫ r in Set.Ioc ρ 1, r ^ ((0:ℝ) - 1) * phiR d r) + m := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hx1, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi hI1 (integrableOn_tail d one_pos hs2)]
  have hint0 : IntegrableOn (fun r : ℝ => r ^ ((0:ℝ) - 1)) (Set.Ioc ρ 1) := by
    have : ContinuousOn (fun r : ℝ => r ^ ((0:ℝ) - 1)) (Set.Icc ρ 1) :=
      continuousOn_id.rpow_const (fun x hx => Or.inl (hρ.trans_le hx.1).ne')
    exact this.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hL : ∫ r in Set.Ioc ρ 1, r ^ ((0:ℝ) - 1) = |Real.log ρ| := by
    have e : ∀ r : ℝ, r ^ ((0:ℝ) - 1) = r⁻¹ := fun r => by rw [zero_sub, Real.rpow_neg_one]
    simp_rw [e]
    rw [← intervalIntegral.integral_of_le hx1, integral_inv_of_pos hρ one_pos, one_div,
      Real.log_inv, abs_of_nonpos (Real.log_nonpos hρ.le hx1)]
  have hA1 : ∫ r in Set.Ioc ρ 1, r ^ ((0:ℝ) - 1) * phiR d r ≤ |Real.log ρ| := by
    rw [← hL]
    refine setIntegral_mono_on hI1 hint0 measurableSet_Ioc (fun r hr => ?_)
    have hr0 : 0 < r := hρ.trans hr.1
    calc r ^ ((0:ℝ) - 1) * phiR d r ≤ r ^ ((0:ℝ) - 1) * 1 :=
          mul_le_mul_of_nonneg_left (phiR_le_one r) (by positivity)
      _ = _ := mul_one _
  have hA2 : (2:ℝ) ^ (-((d:ℝ) + 2)) * |Real.log ρ| ≤ ∫ r in Set.Ioc ρ 1, r ^ ((0:ℝ) - 1) * phiR d r := by
    rw [← hL, ← integral_const_mul]
    refine setIntegral_mono_on (hint0.const_mul _) hI1 measurableSet_Ioc (fun r hr => ?_)
    have hr0 : 0 < r := hρ.trans hr.1
    calc (2:ℝ) ^ (-((d:ℝ) + 2)) * r ^ ((0:ℝ) - 1) = r ^ ((0:ℝ) - 1) * (2:ℝ) ^ (-((d:ℝ) + 2)) := mul_comm _ _
      _ ≤ r ^ ((0:ℝ) - 1) * phiR d r :=
          mul_le_mul_of_nonneg_left (phiR_ge_near hr0.le hr.2) (by positivity)
  rw [hsplit]
  have hL0 : 0 ≤ |Real.log ρ| := abs_nonneg _
  have hmin1 : min ((2:ℝ) ^ (-((d:ℝ) + 2))) m ≤ (2:ℝ) ^ (-((d:ℝ) + 2)) := min_le_left _ _
  have hmin2 : min ((2:ℝ) ^ (-((d:ℝ) + 2))) m ≤ m := min_le_right _ _
  have hmax1 : (1:ℝ) ≤ max 1 m := le_max_left _ _
  have hmax2 : m ≤ max 1 m := le_max_right _ _
  constructor
  · nlinarith
  · nlinarith

end HRS.Commutator.Whole
