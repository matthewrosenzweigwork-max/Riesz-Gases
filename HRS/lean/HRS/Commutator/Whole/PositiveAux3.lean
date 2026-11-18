import HRS.Commutator.Whole.PositiveAux2

/-!
# Helpers for `Positive.lean` (packet `CMX-POS`), part C

Measurability, integrability and `L^q` bounds for `f_1`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

/-- The integrand of `f_1`. -/
def fInt (s : ℝ) (p : Euc d × ℝ) : ℝ := p.2 ^ ((d : ℝ) - s) * phiT p.2 p.1 / p.2

lemma measurable_fInt : Measurable (fInt s : Euc d × ℝ → ℝ) := by
  have := continuous_phi (d := d)
  unfold fInt phiT
  fun_prop

lemma measurable_fTrunc : Measurable (fTrunc s 1 : Euc d → ℝ) := by
  unfold fTrunc
  refine Measurable.const_mul ?_ _
  have h : StronglyMeasurable (fun x : Euc d => ∫ t in Set.Ioc (0:ℝ) 1, fInt s (x, t)) := by
    refine StronglyMeasurable.integral_prod_right (f := fun x t => fInt s (x, t)) ?_
    exact measurable_fInt.stronglyMeasurable
  exact h.measurable

lemma fInt_nonneg {t : ℝ} (ht : 0 < t) (x : Euc d) : 0 ≤ fInt s (x, t) := by
  unfold fInt
  rw [integrand_eq ht x]
  have := phiR_pos (d := d) (‖x‖ / t)
  positivity

lemma integral_phiT {t : ℝ} (ht : 0 < t) :
    ∫ x : Euc d, phiT t x = ∫ x : Euc d, phi x := by
  unfold phiT
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume (fun x : Euc d => phi x) ht.le]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  rw [← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add ht]
  simp

lemma integrable_phiT {t : ℝ} (ht : 0 < t) : Integrable (phiT t : Euc d → ℝ) := by
  unfold phiT
  exact (integrable_phi.comp_smul (inv_ne_zero ht.ne')).const_mul _

lemma integrable_fInt_slice {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : Euc d => fInt s (x, t)) := by
  unfold fInt
  exact ((integrable_phiT ht).const_mul (t ^ ((d : ℝ) - s))).div_const t

lemma integral_fInt_slice {t : ℝ} (ht : 0 < t) :
    ∫ x : Euc d, fInt s (x, t) = t ^ ((d : ℝ) - s - 1) * ∫ x : Euc d, phi x := by
  unfold fInt
  dsimp only
  rw [integral_div, integral_const_mul, integral_phiT ht, Real.rpow_sub_one ht.ne']
  ring

lemma integrable_fInt (hs : s < d) :
    Integrable (fun p : Euc d × ℝ => fInt s p) (volume.prod (volume.restrict (Set.Ioc (0:ℝ) 1))) := by
  rw [integrable_prod_iff' measurable_fInt.aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · filter_upwards [self_mem_ae_restrict (measurableSet_Ioc (a := (0:ℝ)) (b := 1))] with t ht
    exact integrable_fInt_slice ht.1
  · have h1 : IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - s - 1)) (Set.Ioc 0 1) := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := (d : ℝ) - s - 1)
        (by linarith))
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 this
    have h2 : Integrable (fun t : ℝ => t ^ ((d : ℝ) - s - 1) * ∫ x : Euc d, phi x)
        (volume.restrict (Set.Ioc (0:ℝ) 1)) := h1.mul_const _
    refine h2.congr ?_
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioc (a := (0:ℝ)) (b := 1))] with t ht
    have : ∫ x : Euc d, ‖fInt s (x, t)‖ = ∫ x : Euc d, fInt s (x, t) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => Real.norm_of_nonneg (fInt_nonneg ht.1 x))
    rw [this, integral_fInt_slice ht.1]

theorem fTrunc_integrable_aux (hs : s < d) :
    Integrable (fTrunc s 1 : Euc d → ℝ) ∧
      ∫ x : Euc d, fTrunc s 1 x = cPhi d s * (∫ x : Euc d, phi x) / ((d : ℝ) - s) := by
  have hI := integrable_fInt (d := d) (s := s) hs
  have h1 := hI.integral_prod_left
  refine ⟨?_, ?_⟩
  · unfold fTrunc
    exact h1.const_mul _
  · unfold fTrunc
    rw [integral_const_mul]
    have hswap := integral_integral_swap (f := fun (x : Euc d) (t : ℝ) => fInt s (x, t)) hI
    have e1 : (∫ x : Euc d, ∫ t in Set.Ioc (0:ℝ) 1, t ^ ((d : ℝ) - s) * phiT t x / t) =
        ∫ x : Euc d, ∫ t in Set.Ioc (0:ℝ) 1, fInt s (x, t) := rfl
    rw [e1, hswap]
    have e2 : ∀ t ∈ Set.Ioc (0:ℝ) 1, ∫ x : Euc d, fInt s (x, t) =
        t ^ ((d : ℝ) - s - 1) * ∫ x : Euc d, phi x := fun t ht => integral_fInt_slice ht.1
    rw [setIntegral_congr_fun measurableSet_Ioc e2, integral_mul_const]
    have e3 : ∫ t in Set.Ioc (0:ℝ) 1, t ^ ((d : ℝ) - s - 1) = 1 / ((d : ℝ) - s) := by
      rw [← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl (by linarith))]
      have : (d : ℝ) - s - 1 + 1 = (d : ℝ) - s := by ring
      rw [this, Real.zero_rpow (by linarith), Real.one_rpow]
      simp
    rw [e3]
    ring


lemma ae_ne_zero (hd : 0 < d) : ∀ᵐ x : Euc d ∂volume, x ≠ 0 := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have : Set.Countable ({0} : Set (Euc d)) := Set.countable_singleton _
  filter_upwards [this.ae_notMem volume] with x hx
  simpa using hx

lemma log_bound {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) (hr1 : r ≤ 1) :
    1 + |Real.log r| ≤ (1 + 1 / δ) * r ^ (-δ) := by
  have h1 : 1 ≤ r ^ (-δ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (by linarith)
  have h2 : Real.log (r ^ (-δ)) = -δ * Real.log r := Real.log_rpow hr _
  have h3 : Real.log (r ^ (-δ)) ≤ r ^ (-δ) - 1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hr _)
  have h4 : |Real.log r| = -Real.log r := abs_of_nonpos (Real.log_nonpos hr.le hr1)
  rw [h4]
  have : -Real.log r ≤ (r ^ (-δ) - 1) / δ := by
    rw [le_div_iff₀ hδ]; nlinarith
  calc 1 + -Real.log r ≤ 1 + (r ^ (-δ) - 1) / δ := by linarith
    _ ≤ (1 + 1 / δ) * r ^ (-δ) := by
      have : (r ^ (-δ) - 1) / δ ≤ 1 / δ * r ^ (-δ) := by
        rw [div_mul_eq_mul_div, one_mul]
        exact div_le_div_of_nonneg_right (by linarith) hδ.le
      nlinarith

lemma near_bound (hs0 : 0 ≤ s) (hs2 : s < 2 * (d : ℝ) + 4) {Q : ℝ} (hQ1 : 1 ≤ Q)
    (hQ : Q * s < d) (hd : 0 < d) :
    ∃ δ K : ℝ, 0 ≤ δ ∧ δ * Q < d ∧ 0 < K ∧ ∀ x : Euc d, x ≠ 0 → ‖x‖ ≤ 1 →
      fTrunc s 1 x ≤ K * ‖x‖ ^ (-δ) := by
  by_cases hs : s = 0
  · obtain ⟨c, C, hc, hC, h⟩ := cmp_near_zero (d := d) hs
    have hd0 : (0:ℝ) < d := by exact_mod_cast hd
    have hQ0 : 0 < Q := by linarith
    refine ⟨d / (2 * Q), C * (1 + 1 / (d / (2 * Q))), by positivity, ?_, by positivity, fun x hx hx1 => ?_⟩
    · have : (d : ℝ) / (2 * Q) * Q = d / 2 := by field_simp
      rw [this]; linarith
    · have hρ : 0 < ‖x‖ := norm_pos_iff.2 hx
      calc fTrunc s 1 x ≤ C * (1 + |Real.log ‖x‖|) := (h x hx hx1).2
        _ ≤ C * ((1 + 1 / ((d:ℝ) / (2 * Q))) * ‖x‖ ^ (-((d:ℝ) / (2 * Q)))) :=
            mul_le_mul_of_nonneg_left (log_bound (by positivity) hρ hx1) hC.le
        _ = _ := by ring
  · have hs' : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    obtain ⟨c, C, hc, hC, h⟩ := cmp_near_pos (d := d) hs' hs2
    refine ⟨s, C, hs'.le, by linarith, hC, fun x hx hx1 => (h x hx hx1).2⟩

lemma memLp_fTrunc_real (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {Q : ℝ} (hQ1 : 1 ≤ Q)
    (hQ : Q * s < d) (hd : 0 < d) :
    MemLp (fTrunc s 1 : Euc d → ℝ) (ENNReal.ofReal Q) volume := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hs2 : s < 2 * (d : ℝ) + 4 := by linarith
  have hQ0 : 0 < Q := by linarith
  obtain ⟨δ, K, hδ, hδQ, hK, hnear⟩ := near_bound hs0 hs2 hQ1 hQ hd
  obtain ⟨c, C, hc, hC, hfar⟩ := cmp_far (d := d) hs0 hs2
  have hmeas : AEStronglyMeasurable (fTrunc s 1 : Euc d → ℝ) volume :=
    measurable_fTrunc.aestronglyMeasurable
  have hne : ENNReal.ofReal Q ≠ 0 := by simpa using hQ0
  rw [← integrable_norm_rpow_iff hmeas hne ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hQ0.le]
  -- dominating function
  set r := (2 * (d : ℝ) + 4) * Q with hr
  have hrd : (d : ℝ) < r := by nlinarith
  have hI1 : Integrable (fun x : Euc d => (1 + ‖x‖) ^ (-r)) := integrable_one_add_norm (by simpa using hrd)
  have hI2 : IntegrableOn (fun x : Euc d => ‖x‖ ^ (-(δ * Q))) (Metric.ball (0 : Euc d) 1) := by
    have : Nontrivial (Euc d) := by
      have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
      infer_instance
    rw [integrableOn_fun_norm_addHaar volume (f := fun y : ℝ => y ^ (-(δ * Q)))]
    have h1 : IntegrableOn (fun y : ℝ => y ^ ((d : ℝ) - 1 + (-(δ * Q)))) (Set.Ioc 0 1) := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := (d : ℝ) - 1 + (-(δ * Q)))
        (by linarith))
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 this
    refine (h1.mono_set Set.Ioo_subset_Ioc_self).congr_fun ?_ measurableSet_Ioo
    intro y hy
    simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
    have hy0 : 0 < y := hy.1
    have e : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub hd]; simp
    rw [Real.rpow_add hy0, ← Real.rpow_natCast, e]
  have hB : Integrable (fun x : Euc d => (Metric.ball (0 : Euc d) 1).indicator
        (fun x => K ^ Q * ‖x‖ ^ (-(δ * Q))) x + C ^ Q * 2 ^ r * (1 + ‖x‖) ^ (-r)) := by
    refine Integrable.add ?_ (hI1.const_mul _)
    rw [integrable_indicator_iff Metric.isOpen_ball.measurableSet]
    exact hI2.const_mul _
  refine hB.mono' (measurable_fTrunc.norm.pow_const Q).aestronglyMeasurable ?_
  filter_upwards [ae_ne_zero hd] with x hx
  have hρ : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hpos := fTrunc_pos_aux (d := d) hs0 hs2 x hx
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), Real.norm_of_nonneg hpos.le]
  have hnn1 : 0 ≤ C ^ Q * 2 ^ r * (1 + ‖x‖) ^ (-r) := by positivity
  by_cases hx1 : ‖x‖ < 1
  · have hb := hnear x hx hx1.le
    have : fTrunc s 1 x ^ Q ≤ K ^ Q * ‖x‖ ^ (-(δ * Q)) := by
      calc fTrunc s 1 x ^ Q ≤ (K * ‖x‖ ^ (-δ)) ^ Q := Real.rpow_le_rpow hpos.le hb hQ0.le
        _ = K ^ Q * ‖x‖ ^ (-(δ * Q)) := by
          rw [Real.mul_rpow hK.le (by positivity), ← Real.rpow_mul hρ.le]; congr 2; ring
    rw [Set.indicator_of_mem (by simpa using hx1)]
    linarith
  · have hx1' : 1 ≤ ‖x‖ := not_lt.1 hx1
    have hb := (hfar x hx1').2
    have h1 : fTrunc s 1 x ^ Q ≤ C ^ Q * ‖x‖ ^ (-r) := by
      calc fTrunc s 1 x ^ Q ≤ (C * ‖x‖ ^ (-(2 * (d : ℝ) + 4))) ^ Q := Real.rpow_le_rpow hpos.le hb hQ0.le
        _ = C ^ Q * ‖x‖ ^ (-r) := by
          rw [Real.mul_rpow hC.le (by positivity), ← Real.rpow_mul hρ.le]; congr 2; rw [hr]; ring
    have h2 : ‖x‖ ^ (-r) ≤ 2 ^ r * (1 + ‖x‖) ^ (-r) := by
      have h3 : (1 + ‖x‖) / 2 ≤ ‖x‖ := by linarith
      have hr0 : 0 < r := by linarith
      calc ‖x‖ ^ (-r) ≤ ((1 + ‖x‖) / 2) ^ (-r) := Real.rpow_le_rpow_of_nonpos (by positivity) h3 (by linarith)
        _ = 2 ^ r * (1 + ‖x‖) ^ (-r) := by
          rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by positivity),
            Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
          field_simp
    rw [Set.indicator_of_notMem (by simpa using hx1)]
    calc fTrunc s 1 x ^ Q ≤ C ^ Q * ‖x‖ ^ (-r) := h1
      _ ≤ C ^ Q * (2 ^ r * (1 + ‖x‖) ^ (-r)) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 0 + C ^ Q * 2 ^ r * (1 + ‖x‖) ^ (-r) := by ring


theorem fTrunc_Lq_aux (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (p q : ℝ≥0∞)
    (hp : ENNReal.ofReal ((d : ℝ) / (d - s)) < p) (hpq : p⁻¹ + q⁻¹ = 1) :
    MemLp (fTrunc s 1 : Euc d → ℝ) q volume := by
  have hd3 : (3:ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : 0 < d := by omega
  have hds : 0 < (d : ℝ) - s := by linarith
  have hρ1 : 1 ≤ (d : ℝ) / (d - s) := by
    rw [le_div_iff₀ hds]; linarith
  by_cases hptop : p = ⊤
  · subst hptop
    have : q = 1 := by
      simpa using hpq
    subst this
    exact memLp_one_iff_integrable.2 (fTrunc_integrable_aux (d := d) (s := s) (by linarith)).1
  · have hPgt : (d : ℝ) / (d - s) < p.toReal :=
      (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hptop).1 hp
    set P := p.toReal with hP
    have hP1 : 1 < P := lt_of_le_of_lt hρ1 hPgt
    have hP0 : 0 < P := by linarith
    have hqtop : q ≠ ⊤ := by
      intro h
      rw [h, ENNReal.inv_top, add_zero, ENNReal.inv_eq_one] at hpq
      have : P = 1 := by rw [hP, hpq]; simp
      linarith
    have hq0 : q ≠ 0 := by
      intro h
      rw [h, ENNReal.inv_zero, add_top] at hpq
      exact ENNReal.top_ne_one hpq
    set Q := q.toReal with hQ
    have hQ0 : 0 < Q := ENNReal.toReal_pos hq0 hqtop
    have hqQ : q = ENNReal.ofReal Q := (ENNReal.ofReal_toReal hqtop).symm
    have hrel : P⁻¹ + Q⁻¹ = 1 := by
      have := congrArg ENNReal.toReal hpq
      rw [ENNReal.toReal_add (ENNReal.inv_ne_top.2 (by
        intro h; rw [h] at hP; simp at hP; linarith)) (ENNReal.inv_ne_top.2 hq0),
        ENNReal.toReal_inv, ENNReal.toReal_inv] at this
      simpa using this
    have hQ1 : 1 ≤ Q := by
      have : Q⁻¹ ≤ 1 := by have := inv_pos.2 hP0; linarith
      exact (inv_le_one₀ hQ0).1 this
    have hPd : (d : ℝ) < P * ((d : ℝ) - s) := (div_lt_iff₀ hds).1 hPgt
    have hQeq : Q = P / (P - 1) := by
      have h1 : Q⁻¹ = (P - 1) / P := by
        have : Q⁻¹ = 1 - P⁻¹ := by linarith
        rw [this]; field_simp
      rw [← inv_inv Q, h1, inv_div]
    have hQs : Q * s < d := by
      rw [hQeq, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    rw [hqQ]
    exact memLp_fTrunc_real hs0 hsd hQ1 hQs hd0

end HRS.Commutator.Whole
