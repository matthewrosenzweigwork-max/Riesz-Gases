import HRS.Commutator.Whole.PositiveAux5

/-!
# Helpers for `Positive.lean` (packet `CMX-POS`), part F

Representation of `g_1` as a scale integral of `φ`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

/-- Change of variables `r = ρ / t` on `(1,∞)`. -/
lemma cov_inv2 (F : ℝ → ℝ) {ρ : ℝ} (hρ : 0 < ρ) (s : ℝ) :
    ∫ t in Set.Ioi (1:ℝ), t ^ (-s - 1) * F (ρ / t) =
      ρ ^ (-s) * ∫ r in Set.Ioc 0 ρ, r ^ (s - 1) * F r := by
  have himg : (fun t : ℝ => ρ / t) '' Set.Ioi 1 = Set.Ioo 0 ρ := by
    ext r; constructor
    · rintro ⟨t, ht, rfl⟩
      have ht : 1 < t := ht
      have ht0 : 0 < t := by linarith
      refine ⟨by positivity, ?_⟩
      rw [div_lt_iff₀ ht0]; nlinarith
    · intro hr
      have hr0 : 0 < r := hr.1
      refine ⟨ρ / r, ?_, ?_⟩
      · show 1 < ρ / r
        rw [lt_div_iff₀ hr0]; linarith [hr.2]
      · field_simp
  have h := integral_image_eq_integral_abs_deriv_smul (s := Set.Ioi (1:ℝ))
    (f := fun t : ℝ => ρ / t) (f' := fun t : ℝ => -(ρ / t ^ 2)) measurableSet_Ioi
    (fun t ht => by
      have ht0 : (t:ℝ) ≠ 0 := by have : 1 < t := ht; linarith
      have h2 : HasDerivAt (fun t : ℝ => ρ / t) (-(ρ / t ^ 2)) t := by
        simpa [div_eq_mul_inv, neg_div] using (hasDerivAt_inv ht0).const_mul ρ
      exact h2.hasDerivWithinAt)
    (by
      intro a ha b hb hab
      have := (show 1 < a from ha); have := (show 1 < b from hb)
      field_simp at hab
      nlinarith [hab]) (fun r => r ^ (s - 1) * F r)
  rw [himg] at h
  rw [integral_Ioc_eq_integral_Ioo, h, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have ht0 : 0 < t := lt_trans one_pos ht
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

lemma one_sub_phiR_le (r : ℝ) : 1 - phiR d r ≤ ((d : ℝ) + 2) * r ^ 2 := by
  unfold phiR
  have h1 : (0:ℝ) < 1 + r ^ 2 := by positivity
  have h2 : (1 + r ^ 2) ^ (-((d : ℝ) + 2)) = Real.exp (-((d : ℝ) + 2) * Real.log (1 + r ^ 2)) := by
    rw [Real.rpow_def_of_pos h1]; ring_nf
  have h3 := Real.add_one_le_exp (-((d : ℝ) + 2) * Real.log (1 + r ^ 2))
  have h4 : Real.log (1 + r ^ 2) ≤ r ^ 2 := by
    have := Real.log_le_sub_one_of_pos h1; linarith
  have h5 : (0:ℝ) ≤ (d : ℝ) + 2 := by positivity
  rw [h2]
  nlinarith [mul_le_mul_of_nonneg_left h4 h5]

lemma integrableOn_phiR_sub_one_div {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun r : ℝ => (phiR d r - 1) / r) (Set.Ioc 0 b) := by
  have h1 : IntegrableOn (fun r : ℝ => ((d : ℝ) + 2) * r) (Set.Ioc 0 b) := by
    have : ContinuousOn (fun r : ℝ => ((d : ℝ) + 2) * r) (Set.Icc 0 b) := by fun_prop
    exact this.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  refine Integrable.mono' h1 ?_ ?_
  · have := continuous_phiR (d := d)
    exact (by fun_prop : Measurable (fun r : ℝ => (phiR d r - 1) / r)).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict (measurableSet_Ioc (a := (0:ℝ)) (b := b))] with r hr
    have hr0 : 0 < r := hr.1
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hr0, div_le_iff₀ hr0]
    have h2 := one_sub_phiR_le (d := d) r
    have h3 := phiR_le_one (d := d) r
    rw [abs_of_nonpos (by linarith)]
    nlinarith


lemma phiR_zero : phiR d 0 = 1 := by simp [phiR]

theorem g1_repr_pos (hs : 0 < s) (hs2 : s < 2 * (d : ℝ) + 4) (x : Euc d) :
    g1 s x = cPhi d s * ∫ t in Set.Ioi (1:ℝ), t ^ (-s - 1) * phiR d (‖x‖ / t) := by
  by_cases hx : x = 0
  · subst hx
    simp only [g1, ite_true, g1Zero, hs.ne', ite_false, norm_zero, zero_div, phiR_zero, mul_one]
    rw [integral_Ioi_rpow_of_lt (by linarith) one_pos]
    have : -s - 1 + 1 = -s := by ring
    rw [this, Real.one_rpow]
    field_simp
  · have hρ : 0 < ‖x‖ := norm_pos_iff.2 hx
    simp only [g1, hx, ite_false]
    rw [cov_inv2 (phiR d) hρ s, fTrunc_eq_tail hs.le x hx]
    simp only [kern, hs.ne', ite_false]
    set ρ := ‖x‖ with hρdef
    have hJ := cPhi_mul d hs hs2
    have hsplit : ∫ r in Set.Ioi (0:ℝ), r ^ (s - 1) * phiR d r =
        (∫ r in Set.Ioc 0 ρ, r ^ (s - 1) * phiR d r) + ∫ r in Set.Ioi ρ, r ^ (s - 1) * phiR d r := by
      rw [← Set.Ioc_union_Ioi_eq_Ioi hρ.le, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        ((integrableOn_all d hs hs2).mono_set (fun r hr => hr.1)) (integrableOn_tail d hρ hs2)]
    have h1 : s⁻¹ = cPhi d s * ∫ r in Set.Ioi (0:ℝ), r ^ (s - 1) * phiR d r := by
      field_simp; linarith [hJ]
    rw [h1, hsplit]
    ring


lemma integrableOn_phiR_div {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun r : ℝ => phiR d r / r) (Set.Ioi a) := by
  have := integrableOn_tail d (s := 0) ha (by positivity)
  refine this.congr_fun (fun r hr => ?_) measurableSet_Ioi
  simp only
  rw [zero_sub, Real.rpow_neg_one]; ring

theorem g1_repr_zero (hs : s = 0) (x : Euc d) :
    g1 s x = g1Zero d s + ∫ t in Set.Ioi (1:ℝ), (phiR d (‖x‖ / t) - 1) / t := by
  subst hs
  by_cases hx : x = 0
  · subst hx
    simp [g1, phiR_zero]
  · have hρ : 0 < ‖x‖ := norm_pos_iff.2 hx
    simp only [g1, hx, ite_false]
    rw [fTrunc_spatial_aux x hx]
    simp only [kern, ite_true]
    set ρ := ‖x‖ with hρdef
    have hc := cov_inv2 (fun r => phiR d r - 1) hρ 0
    have e1 : ∀ t ∈ Set.Ioi (1:ℝ), (phiR d (ρ / t) - 1) / t = t ^ (-(0:ℝ) - 1) * (phiR d (ρ / t) - 1) := by
      intro t ht
      have ht0 : 0 < t := lt_trans one_pos ht
      rw [neg_zero, zero_sub, Real.rpow_neg_one]; ring
    rw [setIntegral_congr_fun measurableSet_Ioi e1, hc]
    simp only [neg_zero, Real.rpow_zero, one_mul]
    have e2 : ∀ r ∈ Set.Ioc (0:ℝ) ρ, r ^ ((0:ℝ) - 1) * (phiR d r - 1) = (phiR d r - 1) / r := by
      intro r hr
      rw [zero_sub, Real.rpow_neg_one]; ring
    rw [setIntegral_congr_fun measurableSet_Ioc e2]
    unfold g1Zero
    simp only [ite_true]
    -- interval integral bookkeeping
    have hI1 : IntegrableOn (fun r : ℝ => phiR d r / r) (Set.Ioi 1) := integrableOn_phiR_div one_pos
    have hIρ : IntegrableOn (fun r : ℝ => phiR d r / r) (Set.Ioi ρ) := integrableOn_phiR_div hρ
    have h1 := intervalIntegral.integral_Ioi_sub_Ioi' hI1 hIρ
    have hcont : ∀ a b : ℝ, 0 < a → 0 < b → IntervalIntegrable (fun r : ℝ => phiR d r / r) volume a b := by
      intro a b ha hb
      refine ContinuousOn.intervalIntegrable ?_
      have := continuous_phiR (d := d)
      refine ContinuousOn.div (by fun_prop) continuousOn_id (fun r hr => ?_)
      have : 0 < min a b := lt_min ha hb
      have h2 : min a b ≤ r := hr.1
      exact (by linarith : (0:ℝ) < r).ne'
    have hcont1 : ∀ a b : ℝ, 0 < a → 0 < b → IntervalIntegrable (fun r : ℝ => r⁻¹) volume a b := by
      intro a b ha hb
      refine ContinuousOn.intervalIntegrable ?_
      refine ContinuousOn.inv₀ continuousOn_id (fun r hr => ?_)
      have : 0 < min a b := lt_min ha hb
      have h2 : min a b ≤ r := hr.1
      exact (by linarith : (0:ℝ) < r).ne'
    have hL : ∀ b : ℝ, 0 < b → ∫ r in Set.Ioc 0 b, (phiR d r - 1) / r = ∫ r in (0:ℝ)..b, (phiR d r - 1) / r := by
      intro b hb
      rw [intervalIntegral.integral_of_le hb.le]
    have hLint : ∀ b : ℝ, 0 < b → IntervalIntegrable (fun r : ℝ => (phiR d r - 1) / r) volume 0 b := by
      intro b hb
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).2 (integrableOn_phiR_sub_one_div hb)
    rw [hL ρ hρ, hL 1 one_pos]
    have h2 := intervalIntegral.integral_interval_sub_left (hLint ρ hρ) (hLint 1 one_pos)
    have h3 : ∫ r in (1:ℝ)..ρ, (phiR d r - 1) / r = (∫ r in (1:ℝ)..ρ, phiR d r / r) - Real.log ρ := by
      have : ∀ r : ℝ, (phiR d r - 1) / r = phiR d r / r - r⁻¹ := fun r => by ring
      simp_rw [this]
      rw [intervalIntegral.integral_sub (hcont 1 ρ one_pos hρ) (hcont1 1 ρ one_pos hρ),
        integral_inv_of_pos one_pos hρ, div_one]
    have h4 : ∫ r in Set.Ioi ρ, phiR d r / r = (∫ r in Set.Ioi 1, phiR d r / r) - ∫ r in (1:ℝ)..ρ, phiR d r / r := by
      linarith [h1]
    rw [h4]
    have := h2
    rw [h3] at this
    linarith

end HRS.Commutator.Whole
