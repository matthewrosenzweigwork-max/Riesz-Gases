import HRS.PDE.MeanFieldAdjointFrozenB
import HRS.PDE.MeanFieldAprioriVolterraToolsB
import HRS.PDE.MeanFieldLocalB
import HRS.PDE.Uniqueness

/-!
# Frozen smoothing and `H^j` decay (package MF-01, packet P11b)

See `HRS/PDE/MeanFieldAdjointPlan.md`, packet P11b.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.MFAdjoint

variable {d : ℕ}

/-! ### Singular Gronwall with data exponent `γ₀` -/

theorem kernel_pointwise_gen (a γ₀ : ℝ) (ha0 : 0 ≤ a) (hγ₀ : 0 ≤ γ₀) {t : ℝ} (ht0 : 0 < t) :
    ∀ r ∈ Set.Ioo 0 t, (t - r) ^ (-a) * r ^ (-γ₀) ≤
      (t / 2) ^ (-γ₀) * (t - r) ^ (-a) + (t / 2) ^ (-a) * r ^ (-γ₀) := by
  have hu : 0 < t / 2 := by positivity
  intro r hr
  have h1 : 0 ≤ (t - r) ^ (-a) := Real.rpow_nonneg (by linarith [hr.2]) _
  have h2 : 0 ≤ r ^ (-γ₀) := Real.rpow_nonneg hr.1.le _
  have h3 : 0 ≤ (t / 2) ^ (-γ₀) := Real.rpow_nonneg hu.le _
  have h4 : 0 ≤ (t / 2) ^ (-a) := Real.rpow_nonneg hu.le _
  rcases le_or_gt (t / 2) r with h | h
  · have : r ^ (-γ₀) ≤ (t / 2) ^ (-γ₀) :=
      Real.rpow_le_rpow_of_nonpos hu h (by linarith)
    nlinarith [mul_nonneg h4 h2]
  · have : (t - r) ^ (-a) ≤ (t / 2) ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos hu (by linarith) (by linarith)
    nlinarith [mul_nonneg h3 h1]

theorem kernel_integrableOn_gen (a γ₀ : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (hγ₀ : 0 ≤ γ₀)
    (hγ₀1 : γ₀ < 1) {t : ℝ} (ht0 : 0 < t) :
    IntegrableOn (fun r : ℝ => (t - r) ^ (-a) * r ^ (-γ₀)) (Set.Ioo 0 t) := by
  have hpt := kernel_pointwise_gen a γ₀ ha0 hγ₀ ht0
  have hg1 := (MFApriori.intervalIntegrable_sub_rpow_neg a ha1 t).const_mul ((t / 2) ^ (-γ₀))
  have hg2 := (MFApriori.intervalIntegrable_rpow_neg γ₀ hγ₀1 t).const_mul ((t / 2) ^ (-a))
  have hg := hg1.add hg2
  have hgI : IntegrableOn (fun r : ℝ => (t / 2) ^ (-γ₀) * (t - r) ^ (-a) +
      (t / 2) ^ (-a) * r ^ (-γ₀)) (Set.Ioo 0 t) := by
    have := (intervalIntegrable_iff_integrableOn_Ioc_of_le ht0.le).mp hg
    exact this.mono_set Set.Ioo_subset_Ioc_self
  have hfm : Measurable (fun r : ℝ => (t - r) ^ (-a) * r ^ (-γ₀)) :=
    ((measurable_const.sub measurable_id).pow_const _).mul (measurable_id.pow_const _)
  refine Integrable.mono' hgI hfm.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall fun r hr => ?_)
  have h1 : 0 ≤ (t - r) ^ (-a) := Real.rpow_nonneg (by linarith [hr.2]) _
  have h2 : 0 ≤ r ^ (-γ₀) := Real.rpow_nonneg hr.1.le _
  rw [Real.norm_of_nonneg (mul_nonneg h1 h2)]
  exact hpt r hr

theorem kernel_bound_gen (a γ₀ : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hγ₀ : 0 < γ₀) (hγ₀1 : γ₀ < 1)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    t ^ γ₀ * ∫ r in (0 : ℝ)..t, (t - r) ^ (-a) * r ^ (-γ₀) ≤ 2 / (1 - a) + 2 / (1 - γ₀) := by
  have hu : 0 < t / 2 := by positivity
  have hpt := kernel_pointwise_gen a γ₀ ha0.le hγ₀.le ht0
  have hI1 := MFApriori.integral_sub_rpow_neg a ha0 ha1 ht0.le
  have hI2 := MFApriori.integral_rpow_neg_zero γ₀ hγ₀ hγ₀1 ht0.le
  have hg1 := (MFApriori.intervalIntegrable_sub_rpow_neg a ha1 t).const_mul ((t / 2) ^ (-γ₀))
  have hg2 := (MFApriori.intervalIntegrable_rpow_neg γ₀ hγ₀1 t).const_mul ((t / 2) ^ (-a))
  have hg := hg1.add hg2
  have hgI : IntegrableOn (fun r : ℝ => (t / 2) ^ (-γ₀) * (t - r) ^ (-a) +
      (t / 2) ^ (-a) * r ^ (-γ₀)) (Set.Ioo 0 t) := by
    have := (intervalIntegrable_iff_integrableOn_Ioc_of_le ht0.le).mp hg
    exact this.mono_set Set.Ioo_subset_Ioc_self
  have hfI := kernel_integrableOn_gen a γ₀ ha0.le ha1 hγ₀.le hγ₀1 ht0
  have hmono : ∫ r in (0 : ℝ)..t, (t - r) ^ (-a) * r ^ (-γ₀) ≤
      ∫ r in (0 : ℝ)..t, ((t / 2) ^ (-γ₀) * (t - r) ^ (-a) + (t / 2) ^ (-a) * r ^ (-γ₀)) := by
    rw [intervalIntegral.integral_of_le ht0.le, intervalIntegral.integral_of_le ht0.le,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    exact setIntegral_mono_on hfI hgI measurableSet_Ioo hpt
  rw [intervalIntegral.integral_add hg1 hg2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hI1, hI2] at hmono
  refine (mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg ht0.le _)).trans ?_
  have e1 : t ^ γ₀ * (t / 2) ^ (-γ₀) ≤ 2 := by
    have ht2 : t ^ γ₀ = 2 ^ γ₀ * (t / 2) ^ γ₀ := by
      rw [← Real.mul_rpow (by norm_num) hu.le]; congr 1; ring
    rw [ht2, mul_assoc, ← Real.rpow_add hu]
    simp only [add_neg_cancel, Real.rpow_zero, mul_one]
    calc (2 : ℝ) ^ γ₀ ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hγ₀1.le
      _ = 2 := Real.rpow_one 2
  have e2 : t ^ (1 - a) ≤ 1 := Real.rpow_le_one ht0.le ht1 (by linarith)
  have e3 : t ^ γ₀ * ((t / 2) ^ (-a) * (t ^ (1 - γ₀) / (1 - γ₀))) ≤ 2 / (1 - γ₀) := by
    have hsq : t ^ γ₀ * t ^ (1 - γ₀) = t := by
      rw [← Real.rpow_add ht0]; simp
    have h3 : t * (t / 2) ^ (-a) = 2 * (t / 2) ^ (1 - a) := by
      have e : t * (t / 2) ^ (-a) = 2 * ((t / 2) * (t / 2) ^ (-a)) := by ring
      rw [e, show (1 - a) = 1 + (-a) by ring, Real.rpow_add hu, Real.rpow_one]
    have h4 : (t / 2) ^ (1 - a) ≤ 1 := Real.rpow_le_one hu.le (by linarith) (by linarith)
    have h1g : 0 < 1 - γ₀ := by linarith
    calc t ^ γ₀ * ((t / 2) ^ (-a) * (t ^ (1 - γ₀) / (1 - γ₀)))
        = (t ^ γ₀ * t ^ (1 - γ₀) * (t / 2) ^ (-a)) / (1 - γ₀) := by ring
      _ = 2 * (t / 2) ^ (1 - a) / (1 - γ₀) := by rw [hsq, h3]
      _ ≤ 2 / (1 - γ₀) := by
        apply div_le_div_of_nonneg_right _ h1g.le
        linarith
  have h1a : 0 < 1 - a := by linarith
  calc t ^ γ₀ * ((t / 2) ^ (-γ₀) * (t ^ (1 - a) / (1 - a)) +
        (t / 2) ^ (-a) * (t ^ (1 - γ₀) / (1 - γ₀)))
      = (t ^ γ₀ * (t / 2) ^ (-γ₀)) * (t ^ (1 - a) / (1 - a)) +
        t ^ γ₀ * ((t / 2) ^ (-a) * (t ^ (1 - γ₀) / (1 - γ₀))) := by ring
    _ ≤ 2 * (1 / (1 - a)) + 2 / (1 - γ₀) := by
        have h5 : t ^ (1 - a) / (1 - a) ≤ 1 / (1 - a) := by gcongr
        have := mul_le_mul e1 h5 (by positivity) (by norm_num)
        linarith
    _ = 2 / (1 - a) + 2 / (1 - γ₀) := by ring


/-- Singular Gronwall with data exponent `γ₀ ∈ (0,1)`, for a bounded measurable `ψ`. -/
theorem singular_gronwall_meas (γ γ₀ C : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hγ₀ : 0 < γ₀)
    (hγ₀1 : γ₀ < 1) (hC : 0 ≤ C) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (ψ : ℝ → ℝ) (A B : ℝ), 0 ≤ A →
      AEStronglyMeasurable ψ (volume.restrict (Set.Ioc (0 : ℝ) 1)) →
      (∀ t ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ ψ t ∧ ψ t ≤ B) →
      (∀ t ∈ Set.Ioc (0 : ℝ) 1, ψ t ≤ A * t ^ (-γ₀) +
        C * ∫ r in (0 : ℝ)..t, (t - r) ^ (-γ) * ψ r) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ψ t ≤ C' * A * t ^ (-γ₀) := by
  set ε : ℝ := (1 - γ) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hε1 : ε ≤ 1 := by rw [hε]; linarith
  set a : ℝ := γ + ε with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have ha1 : a < 1 := by rw [ha, hε]; linarith
  set K : ℝ := 2 / (1 - a) + 2 / (1 - γ₀) with hK
  have hK0 : 0 ≤ K := by
    have : 0 < 1 - a := by linarith
    have : 0 < 1 - γ₀ := by linarith
    rw [hK]; positivity
  set l : ℝ := max 1 ((2 * C * K) ^ (1 / ε)) with hl
  have hl1 : 1 ≤ l := le_max_left _ _
  have hl0 : 0 < l := by linarith
  have hlε : 2 * C * K ≤ l ^ ε := by
    have h1 : (2 * C * K) ^ (1 / ε) ≤ l := le_max_right _ _
    have h2 : ((2 * C * K) ^ (1 / ε)) ^ ε ≤ l ^ ε :=
      Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) h1 hε0.le
    rwa [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hε0.ne', Real.rpow_one] at h2
  refine ⟨2 * Real.exp l, by positivity, ?_⟩
  intro ψ A B hA hmeas hbd hineq
  set φ : ℝ → ℝ := fun t => t ^ γ₀ * Real.exp (-(l * t)) * ψ t with hφ
  have hB0 : 0 ≤ B := by
    have := hbd 1 ⟨by norm_num, le_rfl⟩
    exact this.1.trans this.2
  have hφle0 : ∀ t ∈ Set.Ioc (0 : ℝ) 1, φ t ≤ B := by
    intro t ht
    have h1 : t ^ γ₀ ≤ 1 := Real.rpow_le_one ht.1.le ht.2 hγ₀.le
    have h2 : Real.exp (-(l * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
    have h3 := hbd t ht
    have h4 : 0 ≤ t ^ γ₀ := Real.rpow_nonneg ht.1.le _
    have h5 := Real.exp_pos (-(l * t))
    calc φ t = (t ^ γ₀ * Real.exp (-(l * t))) * ψ t := rfl
      _ ≤ 1 * B := by
        apply mul_le_mul _ h3.2 h3.1 zero_le_one
        calc t ^ γ₀ * Real.exp (-(l * t)) ≤ 1 * 1 :=
              mul_le_mul h1 h2 h5.le zero_le_one
          _ = 1 := one_mul 1
      _ = B := one_mul B
  have : Nonempty (Set.Ioc (0 : ℝ) 1) := ⟨⟨1, by norm_num, le_rfl⟩⟩
  set Ψ : ℝ := ⨆ t : Set.Ioc (0 : ℝ) 1, φ t with hΨ
  have hbdd : BddAbove (Set.range fun t : Set.Ioc (0 : ℝ) 1 => φ t) :=
    ⟨B, by rintro _ ⟨t, rfl⟩; exact hφle0 t.1 t.2⟩
  have hφΨ : ∀ t ∈ Set.Ioc (0 : ℝ) 1, φ t ≤ Ψ := fun t ht =>
    le_ciSup hbdd (⟨t, ht⟩ : Set.Ioc (0 : ℝ) 1)
  have hφ_nonneg : ∀ t ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ φ t := by
    intro t ht
    have := (hbd t ht).1
    have h4 : 0 ≤ t ^ γ₀ := Real.rpow_nonneg ht.1.le _
    have h5 := Real.exp_pos (-(l * t))
    exact mul_nonneg (mul_nonneg h4 h5.le) this
  have hΨ0 : 0 ≤ Ψ := (hφ_nonneg 1 ⟨by norm_num, le_rfl⟩).trans (hφΨ 1 ⟨by norm_num, le_rfl⟩)
  -- the key estimate
  have key : ∀ t ∈ Set.Ioc (0 : ℝ) 1, φ t ≤ A + (C * K * l ^ (-ε)) * Ψ := by
    intro t ht
    have ht0 := ht.1
    have ht1 := ht.2
    have hψt := hineq t ht
    -- integrability of the singular integrand
    have hmeas' : AEStronglyMeasurable ψ (volume.restrict (Set.Ioc (0 : ℝ) t)) :=
      hmeas.mono_measure (Measure.restrict_mono (Set.Ioc_subset_Ioc_right ht1) le_rfl)
    have hI : IntervalIntegrable (fun r : ℝ => (t - r) ^ (-γ) * ψ r) volume 0 t := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht0.le]
      have h1 := (intervalIntegrable_iff_integrableOn_Ioc_of_le ht0.le).mp
        (MFApriori.intervalIntegrable_sub_rpow_neg γ hγ1 t)
      refine Integrable.mul_bdd h1 hmeas' (c := B) ?_
      rw [ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall fun r hr => ?_
      have := hbd r ⟨hr.1, hr.2.trans ht1⟩
      rw [Real.norm_of_nonneg this.1]
      exact this.2
    set J : ℝ := ∫ r in (0 : ℝ)..t, (t - r) ^ (-γ) * (Real.exp (-(l * t)) * ψ r) with hJ
    have hJ' : Real.exp (-(l * t)) * ∫ r in (0 : ℝ)..t, (t - r) ^ (-γ) * ψ r = J := by
      rw [hJ, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun r _ => ?_
      ring
    -- pointwise bound
    have hpt : ∀ r ∈ Set.Ioo 0 t, (t - r) ^ (-γ) * (Real.exp (-(l * t)) * ψ r) ≤
        (Ψ * l ^ (-ε)) * ((t - r) ^ (-a) * r ^ (-γ₀)) := by
      intro r hr
      have hr0 := hr.1
      have hr1 : r ≤ 1 := hr.2.le.trans ht1
      have hu : 0 < t - r := by linarith [hr.2]
      have h1 : φ r ≤ Ψ := hφΨ r ⟨hr0, hr1⟩
      have h2 : Real.exp (-(l * r)) * ψ r ≤ Ψ * r ^ (-γ₀) := by
        have hrp : 0 < r ^ γ₀ := Real.rpow_pos_of_pos hr0 _
        have : r ^ (-γ₀) * r ^ γ₀ = 1 := by
          rw [← Real.rpow_add hr0]; simp
        calc Real.exp (-(l * r)) * ψ r
            = r ^ (-γ₀) * (r ^ γ₀ * Real.exp (-(l * r)) * ψ r) := by
              rw [← mul_assoc, ← mul_assoc]
              nlinarith [this, mul_nonneg (Real.exp_pos (-(l * r))).le (hbd r ⟨hr0, hr1⟩).1]
          _ ≤ r ^ (-γ₀) * Ψ := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hr0.le _)
          _ = Ψ * r ^ (-γ₀) := mul_comm _ _
      have h3 : Real.exp (-(l * t)) * ψ r ≤ Real.exp (-(l * (t - r))) * (Ψ * r ^ (-γ₀)) := by
        have : Real.exp (-(l * t)) = Real.exp (-(l * (t - r))) * Real.exp (-(l * r)) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [this, mul_assoc]
        exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      have h4 := MFApriori.exp_rpow_bound (γ := γ) hl0 hε0 hε1 hu
      have h5 : 0 ≤ (t - r) ^ (-γ) := Real.rpow_nonneg hu.le _
      calc (t - r) ^ (-γ) * (Real.exp (-(l * t)) * ψ r)
          ≤ (t - r) ^ (-γ) * (Real.exp (-(l * (t - r))) * (Ψ * r ^ (-γ₀))) :=
            mul_le_mul_of_nonneg_left h3 h5
        _ = ((t - r) ^ (-γ) * Real.exp (-(l * (t - r)))) * (Ψ * r ^ (-γ₀)) := by ring
        _ ≤ (l ^ (-ε) * (t - r) ^ (-a)) * (Ψ * r ^ (-γ₀)) :=
            mul_le_mul_of_nonneg_right h4 (mul_nonneg hΨ0 (Real.rpow_nonneg hr0.le _))
        _ = (Ψ * l ^ (-ε)) * ((t - r) ^ (-a) * r ^ (-γ₀)) := by ring
    have hkI := kernel_integrableOn_gen a γ₀ ha0.le ha1 hγ₀.le hγ₀1 ht0
    have hJmono : J ≤ ∫ r in (0 : ℝ)..t, (Ψ * l ^ (-ε)) * ((t - r) ^ (-a) * r ^ (-γ₀)) := by
      rw [hJ, intervalIntegral.integral_of_le ht0.le, intervalIntegral.integral_of_le ht0.le,
        integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
      refine setIntegral_mono_on ?_ (hkI.const_mul _) measurableSet_Ioo hpt
      have := (hI.const_mul (Real.exp (-(l * t)))).1.mono_set Set.Ioo_subset_Ioc_self
      refine this.congr_fun (fun r _ => ?_) measurableSet_Ioo
      ring
    rw [intervalIntegral.integral_const_mul] at hJmono
    have hkb := kernel_bound_gen a γ₀ ha0 ha1 hγ₀ hγ₀1 ht0 ht1
    have hst : 0 ≤ t ^ γ₀ := Real.rpow_nonneg ht0.le _
    have hex := Real.exp_pos (-(l * t))
    have hex1 : Real.exp (-(l * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have htt : t ^ γ₀ * t ^ (-γ₀) = 1 := by
      rw [← Real.rpow_add ht0]; simp
    -- assemble
    have hφt : φ t ≤ t ^ γ₀ * Real.exp (-(l * t)) *
        (A * t ^ (-γ₀) + C * ∫ r in (0 : ℝ)..t, (t - r) ^ (-γ) * ψ r) :=
      mul_le_mul_of_nonneg_left hψt (mul_nonneg hst hex.le)
    have e1 : t ^ γ₀ * Real.exp (-(l * t)) *
        (A * t ^ (-γ₀) + C * ∫ r in (0 : ℝ)..t, (t - r) ^ (-γ) * ψ r)
        = A * Real.exp (-(l * t)) * (t ^ γ₀ * t ^ (-γ₀)) +
          C * t ^ γ₀ * (Real.exp (-(l * t)) * ∫ r in (0 : ℝ)..t, (t - r) ^ (-γ) * ψ r) := by
      ring
    rw [e1, htt, hJ'] at hφt
    have e2 : C * t ^ γ₀ * J ≤ C * (Ψ * l ^ (-ε)) * K := by
      have h6 : t ^ γ₀ * J ≤ t ^ γ₀ *
          ((Ψ * l ^ (-ε)) * ∫ r in (0 : ℝ)..t, (t - r) ^ (-a) * r ^ (-γ₀)) :=
        mul_le_mul_of_nonneg_left hJmono hst
      have h7 : t ^ γ₀ *
          ((Ψ * l ^ (-ε)) * ∫ r in (0 : ℝ)..t, (t - r) ^ (-a) * r ^ (-γ₀)) ≤
          (Ψ * l ^ (-ε)) * K := by
        have hc : 0 ≤ Ψ * l ^ (-ε) := mul_nonneg hΨ0 (Real.rpow_nonneg hl0.le _)
        calc t ^ γ₀ *
            ((Ψ * l ^ (-ε)) * ∫ r in (0 : ℝ)..t, (t - r) ^ (-a) * r ^ (-γ₀))
            = (Ψ * l ^ (-ε)) * (t ^ γ₀ *
              ∫ r in (0 : ℝ)..t, (t - r) ^ (-a) * r ^ (-γ₀)) := by ring
          _ ≤ (Ψ * l ^ (-ε)) * K := mul_le_mul_of_nonneg_left hkb hc
      calc C * t ^ γ₀ * J = C * (t ^ γ₀ * J) := by ring
        _ ≤ C * ((Ψ * l ^ (-ε)) * K) := mul_le_mul_of_nonneg_left (h6.trans h7) hC
        _ = C * (Ψ * l ^ (-ε)) * K := by ring
    have e3 : A * Real.exp (-(l * t)) * 1 ≤ A := by
      calc A * Real.exp (-(l * t)) * 1 = A * Real.exp (-(l * t)) := mul_one _
        _ ≤ A * 1 := mul_le_mul_of_nonneg_left hex1 hA
        _ = A := mul_one A
    calc φ t ≤ A * Real.exp (-(l * t)) * 1 + C * t ^ γ₀ * J := hφt
      _ ≤ A + C * (Ψ * l ^ (-ε)) * K := add_le_add e3 e2
      _ = A + (C * K * l ^ (-ε)) * Ψ := by ring
  -- contraction
  have hcoef : C * K * l ^ (-ε) ≤ 1 / 2 := by
    have hlε0 : 0 < l ^ ε := Real.rpow_pos_of_pos hl0 _
    rw [Real.rpow_neg hl0.le, ← div_eq_mul_inv, div_le_iff₀ hlε0]
    linarith
  have hΨle : Ψ ≤ A + (1 / 2) * Ψ := by
    refine ciSup_le fun t => (key t.1 t.2).trans ?_
    have := mul_le_mul_of_nonneg_right hcoef hΨ0
    linarith
  have hΨ2 : Ψ ≤ 2 * A := by linarith
  intro t ht
  have h1 := hφΨ t ht
  have hφt : φ t = t ^ γ₀ * (Real.exp (-(l * t)) * ψ t) := by simp only [hφ]; ring
  have hexl : Real.exp (l * t) * Real.exp (-(l * t)) = 1 := by rw [← Real.exp_add]; simp
  have hexle : Real.exp (l * t) ≤ Real.exp l :=
    Real.exp_le_exp.2 (by nlinarith [ht.1, ht.2])
  have htt : t ^ (-γ₀) * t ^ γ₀ = 1 := by rw [← Real.rpow_add ht.1]; simp
  have hpos : 0 ≤ t ^ (-γ₀) := Real.rpow_nonneg ht.1.le _
  have hψ : ψ t = Real.exp (l * t) * (t ^ (-γ₀) * φ t) := by
    rw [hφt]
    calc ψ t = (Real.exp (l * t) * Real.exp (-(l * t))) * ((t ^ (-γ₀) * t ^ γ₀) * ψ t) := by
          rw [hexl, htt]; ring
      _ = _ := by ring
  rw [hψ]
  have hA2 : 0 ≤ A := hA
  calc Real.exp (l * t) * (t ^ (-γ₀) * φ t)
      ≤ Real.exp l * (t ^ (-γ₀) * (2 * A)) := by
        apply mul_le_mul hexle _ (mul_nonneg hpos (hφ_nonneg t ht)) (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left (h1.trans hΨ2) hpos
    _ = 2 * Real.exp l * A * t ^ (-γ₀) := by ring

theorem singular_gronwall_gen (γ γ₀ C : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hγ₀ : 1 / 2 ≤ γ₀)
    (hγ₀1 : γ₀ < 1) (hC : 0 ≤ C) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (ψ : ℝ → ℝ) (A B : ℝ), 0 ≤ A → ContinuousOn ψ (Set.Ioc 0 1) →
      (∀ t ∈ Set.Ioc 0 1, 0 ≤ ψ t ∧ ψ t ≤ B) →
      (∀ t ∈ Set.Ioc 0 1, ψ t ≤ A * t ^ (-γ₀) + C * ∫ r in (0 : ℝ)..t, (t - r) ^ (-γ) * ψ r) →
      ∀ t ∈ Set.Ioc 0 1, ψ t ≤ C' * A * t ^ (-γ₀) := by
  obtain ⟨C', hC'0, hC'⟩ := singular_gronwall_meas γ γ₀ C hγ0 hγ1 (by linarith) hγ₀1 hC
  exact ⟨C', hC'0, fun ψ A B hA hψc hbd hineq t ht =>
    hC' ψ A B hA (hψc.aestronglyMeasurable measurableSet_Ioc) hbd hineq t ht⟩


/-! ### The frozen path: uniqueness, time-homogeneity, linearity -/

section FrozenPath

variable {s : ℝ} {m : ℕ} {R : Regime} {MB Λ VB : ℝ} {D : DynData d} {ν₀ T : ℝ} {ρ : Torus d → ℝ}

theorem isForwardSolution_restrict {t t' : ℝ} {φc : Coeff d} {F : ℝ → Coeff d}
    (h : IsForwardSolution D (fun _ => ρ) t φc F) (ht' : t' ≤ t) :
    IsForwardSolution D (fun _ => ρ) t' φc F :=
  ⟨fun τ hτ => h.h1 τ ⟨hτ.1, hτ.2.trans ht'⟩,
    fun k => (h.integrable k).mono_set (Set.Icc_subset_Icc_right ht'),
    fun k τ hτ => h.eq k τ ⟨hτ.1, hτ.2.trans ht'⟩⟩

theorem weakContinuousInHs_restrict {m' : ℝ} {t t' : ℝ} {F : ℝ → Coeff d}
    (h : WeakContinuousInHs m' F t) (ht' : t' ≤ t) : WeakContinuousInHs m' F t' :=
  ⟨fun τ hτ => h.1 τ ⟨hτ.1, hτ.2.trans ht'⟩,
    fun G hG => (h.2 G hG).mono (Set.Icc_subset_Icc_right ht')⟩

theorem weakContinuousInHs_sub {m' : ℝ} {t : ℝ} {F₁ F₂ : ℝ → Coeff d}
    (h₁ : WeakContinuousInHs m' F₁ t) (h₂ : WeakContinuousInHs m' F₂ t) :
    WeakContinuousInHs m' (fun σ => F₁ σ - F₂ σ) t := by
  refine ⟨fun τ hτ => memHs_sub (h₁.1 τ hτ) (h₂.1 τ hτ), fun G hG => ?_⟩
  refine ((h₁.2 G hG).sub (h₂.2 G hG)).congr fun τ hτ => ?_
  exact ET.hsInner_sub_left (h₁.1 τ hτ) (h₂.1 τ hτ) hG


theorem isForwardSolution_sub (hd : 1 ≤ d) {μ : ℝ → Torus d → ℝ}
    (hA : AdjointData s m R MB Λ VB D ν₀ T μ) {t : ℝ} (ht : t ∈ Set.Ioc 0 T)
    {φc φc' : Coeff d} {F₁ F₂ : ℝ → Coeff d} (h₁ : IsForwardSolution D μ t φc F₁)
    (h₂ : IsForwardSolution D μ t φc' F₂) :
    IsForwardSolution D μ t (φc - φc') (fun σ => F₁ σ - F₂ σ) := by
  obtain ⟨K, hK0, hKm⟩ := uniform_multBound hd hA
  have hrT : ∀ σ ∈ Set.Icc (0:ℝ) t, t - σ ∈ Set.Icc (0:ℝ) T := fun σ hσ =>
    ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩
  have hsub : ∀ σ ∈ Set.Icc (0:ℝ) t, forwardGen D (μ (t - σ)) (F₁ σ - F₂ σ) =
      forwardGen D (μ (t - σ)) (F₁ σ) - forwardGen D (μ (t - σ)) (F₂ σ) := fun σ hσ =>
    forwardGen_sub_H1 D _ (hKm _ (hrT σ hσ)).1.memHs0
      (fun j => ((hKm _ (hrT σ hσ)).2 j).memHs0) (h₁.h1 σ hσ) (h₂.h1 σ hσ)
  refine ⟨fun σ hσ => memHs_sub (h₁.h1 σ hσ) (h₂.h1 σ hσ), fun k => ?_, fun k τ hτ => ?_⟩
  · refine ((h₁.integrable k).sub (h₂.integrable k)).congr_fun (fun σ hσ => ?_) measurableSet_Icc
    simp only [hsub σ hσ, Pi.sub_apply]
  · have hi : ∀ (F : ℝ → Coeff d), (∀ k, IntegrableOn (fun σ => forwardGen D (μ (t - σ)) (F σ) k)
        (Set.Icc 0 t)) → IntervalIntegrable (fun σ => forwardGen D (μ (t - σ)) (F σ) k)
          volume 0 τ := fun F hF => by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hτ.1]
      exact (hF k).mono_set (Set.Icc_subset_Icc_right hτ.2)
    show F₁ τ k - F₂ τ k = (φc - φc') k + ∫ σ in (0:ℝ)..τ,
      forwardGen D (μ (t - σ)) (F₁ σ - F₂ σ) k
    have hc : ∫ σ in (0:ℝ)..τ, forwardGen D (μ (t - σ)) (F₁ σ - F₂ σ) k =
        ∫ σ in (0:ℝ)..τ, (forwardGen D (μ (t - σ)) (F₁ σ) k -
          forwardGen D (μ (t - σ)) (F₂ σ) k) := by
      refine intervalIntegral.integral_congr fun σ hσ => ?_
      rw [Set.uIcc_of_le hτ.1] at hσ
      simp only [hsub σ ⟨hσ.1, hσ.2.trans hτ.2⟩, Pi.sub_apply]
    rw [hc, intervalIntegral.integral_sub (hi F₁ h₁.integrable) (hi F₂ h₂.integrable),
      h₁.eq k τ hτ, h₂.eq k τ hτ]
    simp only [Pi.sub_apply]
    ring

/-- Uniqueness: any weakly continuous forward solution is the propagator path. -/
theorem propagatorCoeff_eq_of_solution (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hm : 1 ≤ m)
    {μ : ℝ → Torus d → ℝ} (hA : AdjointData s m R MB Λ VB D ν₀ T μ) {t : ℝ}
    (ht : t ∈ Set.Ioc 0 T) {φc : Coeff d} (hφ : MemHs m φc) {F : ℝ → Coeff d}
    (hF : IsForwardSolution D μ t φc F) (hw : WeakContinuousInHs 1 F t) :
    ∀ τ ∈ Set.Icc 0 t, propagatorCoeff D μ m t φc τ = F τ := by
  obtain ⟨C, -, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd m hm R MB Λ VB
  obtain ⟨h1, w, -⟩ := hspec D ν₀ T μ hA t ht φc hφ
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  exact forward_unique_H1 hd s hs0 hsd m hm R MB Λ VB D ν₀ T μ hA t ht φc _ _ h1
    (weakContinuousInHs_mono hm1 w) hF hw

theorem frozenCoeff_zero (hm : 1 ≤ m) {ψc : Coeff d} (hψ : MemHs m ψc) :
    frozenCoeff D ρ m ψc 0 = ψc := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hsol : IsForwardSolution D (fun _ => ρ) 0 ψc (fun _ => ψc) := by
    refine ⟨fun τ _ => hψ.mono hm1, fun k => ?_, fun k τ hτ => ?_⟩
    · exact integrableOn_const (by simp) (by simp)
    · have : τ = 0 := le_antisymm hτ.2 hτ.1
      subst this
      simp
  have hw : WeakContinuousInHs (m : ℝ) (fun _ => ψc) 0 :=
    ⟨fun τ _ => hψ, fun G _ => continuousOn_const⟩
  have hex : ∃ F, IsForwardSolution D (fun _ => ρ) 0 ψc F ∧ WeakContinuousInHs (m : ℝ) F 0 :=
    ⟨_, hsol, hw⟩
  unfold frozenCoeff propagatorCoeff
  simp only [hex, dite_true]
  funext k
  have := hex.choose_spec.1.eq k 0 ⟨le_rfl, le_rfl⟩
  simpa using this

/-- Time-homogeneity (statement of the packet). -/
theorem frozenCoeff_eq_propagatorCoeff_aux (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hm : 1 ≤ m)
    (hA : AdjointData s m R MB Λ VB D ν₀ T (fun _ => ρ)) {ψc : Coeff d} (hψ : MemHs m ψc)
    {t τ : ℝ} (ht : t ∈ Set.Ioc 0 T) (hτ : τ ∈ Set.Icc 0 t) :
    propagatorCoeff D (fun _ => ρ) m t ψc τ = frozenCoeff D ρ m ψc τ := by
  obtain ⟨C, -, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd m hm R MB Λ VB
  obtain ⟨h1, w, -⟩ := hspec D ν₀ T (fun _ => ρ) hA t ht ψc hψ
  rcases hτ.1.eq_or_lt with h0 | hpos
  · subst h0
    rw [frozenCoeff_zero hm hψ]
    funext k
    have := h1.eq k 0 ⟨le_rfl, ht.1.le⟩
    simpa using this
  · have hmem : τ ∈ Set.Ioc 0 T := ⟨hpos, hτ.2.trans ht.2⟩
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have := propagatorCoeff_eq_of_solution hd hs0 hsd hm hA hmem hψ
      (isForwardSolution_restrict h1 hτ.2)
      (weakContinuousInHs_restrict (weakContinuousInHs_mono hm1 w) hτ.2) τ ⟨hτ.1, le_rfl⟩
    exact this.symm

theorem frozenCoeff_sub_aux (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hm : 1 ≤ m)
    (hA : AdjointData s m R MB Λ VB D ν₀ T (fun _ => ρ)) {ψc ψc' : Coeff d}
    (hψ : MemHs m ψc) (hψ' : MemHs m ψc') {τ : ℝ} (hτ : τ ∈ Set.Icc 0 T) :
    frozenCoeff D ρ m (ψc - ψc') τ = frozenCoeff D ρ m ψc τ - frozenCoeff D ρ m ψc' τ := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rcases hτ.1.eq_or_lt with h0 | hpos
  · subst h0
    rw [frozenCoeff_zero hm hψ, frozenCoeff_zero hm hψ', frozenCoeff_zero hm (memHs_sub hψ hψ')]
  · have ht : τ ∈ Set.Ioc 0 T := ⟨hpos, hτ.2⟩
    obtain ⟨C, -, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd m hm R MB Λ VB
    obtain ⟨h1, w1, -⟩ := hspec D ν₀ T (fun _ => ρ) hA τ ht ψc hψ
    obtain ⟨h2, w2, -⟩ := hspec D ν₀ T (fun _ => ρ) hA τ ht ψc' hψ'
    have hsol := isForwardSolution_sub hd hA ht h1 h2
    have hw := weakContinuousInHs_sub (weakContinuousInHs_mono hm1 w1)
      (weakContinuousInHs_mono hm1 w2)
    exact propagatorCoeff_eq_of_solution hd hs0 hsd hm hA ht (memHs_sub hψ hψ') hsol hw τ
      ⟨hτ.1, le_rfl⟩


theorem memHs_smul_delta (m : ℝ) (c : ℂ) : MemHs m (c • deltaCoeff (0 : Lattice d)) := by
  refine summable_of_ne_finset_zero (s := {0}) fun k hk => ?_
  have : k ≠ 0 := by simpa using hk
  simp [deltaCoeff, this]

/-- Constants (multiples of `δ₀`) are stationary. -/
theorem forwardGen_smul_delta (D : DynData d) (ρ : Torus d → ℝ) (c : ℂ) :
    forwardGen D ρ (c • deltaCoeff (0 : Lattice d)) = 0 := by
  have hder : ∀ j : Fin d, derivCoeff j (c • deltaCoeff (0 : Lattice d)) = 0 := by
    intro j; funext k
    by_cases hk : k = 0
    · subst hk; simp [derivCoeff]
    · simp [derivCoeff, deltaCoeff, hk]
  have hmul0 : ∀ a : Coeff d, mulCoeff a (0 : Coeff d) = 0 := by
    intro a; funext k; simp [mulCoeff]
  funext k
  have hlap : laplaceCoeff (c • deltaCoeff (0 : Lattice d)) k = 0 := by
    by_cases hk : k = 0
    · subst hk
      have : Lattice.enorm (0 : Lattice d) = 0 := by
        unfold Lattice.enorm Lattice.toEuc
        have : (WithLp.toLp 2 fun i : Fin d => (((0 : Lattice d) i : ℤ) : ℝ)) = (0 : Euc d) := by
          ext i; simp
        rw [this, norm_zero]
      simp [laplaceCoeff, this]
    · simp [laplaceCoeff, deltaCoeff, hk]
  have htr : transportCoeff D ρ (c • deltaCoeff (0 : Lattice d)) k = 0 := by
    simp [transportCoeff, hder, hmul0]
  have hnl : nonlocalCoeff D ρ (c • deltaCoeff (0 : Lattice d)) k = 0 := by
    simp [nonlocalCoeff, hder, hmul0, gradRieszCoeff, derivCoeff, rieszMult]
  simp [forwardGen, hlap, htr, hnl]

theorem isForwardSolution_const_delta {μ : ℝ → Torus d → ℝ} (t : ℝ) (c : ℂ) :
    IsForwardSolution D μ t (c • deltaCoeff (0 : Lattice d)) (fun _ => c • deltaCoeff 0) := by
  have h0 := forwardGen_smul_delta D
  refine ⟨fun τ _ => memHs_smul_delta 1 c, fun k => ?_, fun k τ hτ => ?_⟩
  · simp only [h0]
    exact integrableOn_const (by simp) (by simp)
  · simp only [h0]
    simp

theorem frozenCoeff_const_delta (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hm : 1 ≤ m)
    (hA : AdjointData s m R MB Λ VB D ν₀ T (fun _ => ρ)) (c : ℂ) {τ : ℝ}
    (hτ : τ ∈ Set.Icc 0 T) :
    frozenCoeff D ρ m (c • deltaCoeff (0 : Lattice d)) τ = c • deltaCoeff 0 := by
  have hmem : MemHs (m : ℝ) (c • deltaCoeff (0 : Lattice d)) := memHs_smul_delta _ c
  rcases hτ.1.eq_or_lt with h0 | hpos
  · subst h0; exact frozenCoeff_zero hm hmem
  · have ht : τ ∈ Set.Ioc 0 T := ⟨hpos, hτ.2⟩
    have hw : WeakContinuousInHs 1 (fun _ => c • deltaCoeff (0 : Lattice d)) τ :=
      ⟨fun _ _ => memHs_smul_delta 1 c, fun G _ => continuousOn_const⟩
    exact propagatorCoeff_eq_of_solution hd hs0 hsd hm hA ht hmem
      (isForwardSolution_const_delta τ c) hw τ ⟨hτ.1, le_rfl⟩

/-- Membership and growth bound of the frozen path. -/
theorem exists_frozenCoeff_bound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hm : 1 ≤ m)
    (R : Regime) (MB Λ VB : ℝ) :
    ∃ L : ℝ, 0 < L ∧ ∀ (D : DynData d) (ν₀ T : ℝ) (ρ : Torus d → ℝ)
      (_ : AdjointData s m R MB Λ VB D ν₀ T (fun _ => ρ)) (ψc : Coeff d) (_ : MemHs m ψc)
      (τ : ℝ) (_ : τ ∈ Set.Icc 0 T), MemHs m (frozenCoeff D ρ m ψc τ) ∧
        hsNorm m (frozenCoeff D ρ m ψc τ) ≤
          Real.exp (R.lambdaM L ν₀ (thetaOrder d s) * τ) * hsNorm m ψc := by
  obtain ⟨C, hC, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd m hm R MB Λ VB
  refine ⟨C, hC, fun D ν₀ T ρ hA ψc hψ τ hτ => ?_⟩
  rcases hτ.1.eq_or_lt with h0 | hpos
  · subst h0
    rw [frozenCoeff_zero hm hψ]
    refine ⟨hψ, ?_⟩
    simp
  · obtain ⟨-, w, hb⟩ := hspec D ν₀ T (fun _ => ρ) hA τ ⟨hpos, hτ.2⟩ ψc hψ
    exact ⟨w.1 τ ⟨hpos.le, le_rfl⟩, hb τ ⟨hpos.le, le_rfl⟩⟩

/-- Semigroup property of the frozen path at the coefficient level. -/
theorem frozenCoeff_shift (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hm : 1 ≤ m)
    (hA : AdjointData s m R MB Λ VB D ν₀ T (fun _ => ρ)) {ψc : Coeff d} (hψ : MemHs m ψc)
    {τ v : ℝ} (hτ : 0 ≤ τ) (hv : 0 ≤ v) (hτv : τ + v ≤ T) :
    MemHs m (frozenCoeff D ρ m ψc τ) ∧
      frozenCoeff D ρ m (frozenCoeff D ρ m ψc τ) v = frozenCoeff D ρ m ψc (τ + v) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨L, hL, hbd⟩ := exists_frozenCoeff_bound (d := d) (s := s) (m := m) hd hs0 hsd hm R MB Λ VB
  have hmemτ : MemHs m (frozenCoeff D ρ m ψc τ) :=
    (hbd D ν₀ T ρ hA ψc hψ τ ⟨hτ, by linarith⟩).1
  refine ⟨hmemτ, ?_⟩
  rcases hv.eq_or_lt with h0 | hvpos
  · subst h0
    rw [frozenCoeff_zero hm hmemτ, add_zero]
  rcases hτ.eq_or_lt with h0 | hτpos
  · subst h0
    rw [frozenCoeff_zero hm hψ, zero_add]
  -- main case
  have ht : τ + v ∈ Set.Ioc 0 T := ⟨by linarith, hτv⟩
  have hv' : v ∈ Set.Ioc 0 T := ⟨hvpos, by linarith⟩
  obtain ⟨C, -, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd m hm R MB Λ VB
  obtain ⟨hF, hw, -⟩ := hspec D ν₀ T (fun _ => ρ) hA (τ + v) ht ψc hψ
  set F := propagatorCoeff D (fun _ => ρ) m (τ + v) ψc with hFdef
  have hFτ : F τ = frozenCoeff D ρ m ψc τ :=
    frozenCoeff_eq_propagatorCoeff_aux hd hs0 hsd hm hA hψ ht ⟨hτ, by linarith⟩
  have hFt : F (τ + v) = frozenCoeff D ρ m ψc (τ + v) := rfl
  have hsol : IsForwardSolution D (fun _ => ρ) v (F τ) (fun σ => F (τ + σ)) := by
    refine ⟨fun σ hσ => hF.h1 (τ + σ) ⟨by linarith [hσ.1], by linarith [hσ.2]⟩, fun k => ?_,
      fun k σ hσ => ?_⟩
    · have h1 : IntervalIntegrable (fun x => forwardGen D ρ (F x) k) volume τ (τ + v) := by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
        exact (hF.integrable k).mono_set (Set.Icc_subset_Icc hτ le_rfl)
      have h2 := h1.comp_add_left τ
      simp only [sub_self, add_sub_cancel_left] at h2
      rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hvpos.le]
      exact h2
    · have hi : ∀ b, 0 ≤ b → b ≤ τ + v →
          IntervalIntegrable (fun x => forwardGen D ρ (F x) k) volume 0 b := by
        intro b hb0 hb1
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le hb0]
        exact (hF.integrable k).mono_set (Set.Icc_subset_Icc_right hb1)
      have e1 := hF.eq k (τ + σ) ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
      have e2 := hF.eq k τ ⟨hτ, by linarith⟩
      have hI1 := hi τ hτ (by linarith)
      have hI2 : IntervalIntegrable (fun x => forwardGen D ρ (F x) k) volume τ (τ + σ) := by
        refine (hi (τ + σ) (by linarith [hσ.1]) (by linarith [hσ.2])).mono_set ?_
        rw [Set.uIcc_of_le (by linarith [hσ.1]), Set.uIcc_of_le (by linarith [hσ.1])]
        exact Set.Icc_subset_Icc hτ le_rfl
      have e3 := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
      have e4 := intervalIntegral.integral_comp_add_left
        (fun x => forwardGen D ρ (F x) k) (a := 0) (b := σ) τ
      simp only [add_zero] at e4
      show F (τ + σ) k = F τ k + ∫ x in (0:ℝ)..σ, forwardGen D ρ (F (τ + x)) k
      rw [e4, e1, e2, ← e3]
      ring
  have hw1 : WeakContinuousInHs 1 (fun σ => F (τ + σ)) v := by
    have hw' := weakContinuousInHs_mono hm1 hw
    refine ⟨fun σ hσ => hw'.1 (τ + σ) ⟨by linarith [hσ.1], by linarith [hσ.2]⟩, fun G hG => ?_⟩
    refine (hw'.2 G hG).comp (continuous_const.add continuous_id).continuousOn fun σ hσ =>
      ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have hFτm : MemHs m (F τ) := by rw [hFτ]; exact hmemτ
  have := propagatorCoeff_eq_of_solution hd hs0 hsd hm hA hv' hFτm hsol hw1 v ⟨hvpos.le, le_rfl⟩
  rw [← hFt]
  change propagatorCoeff D (fun _ => ρ) m v (frozenCoeff D ρ m ψc τ) v = F (τ + v)
  rw [← hFτ]
  exact this


/-! ### The mild (variation of constants) formula -/

/-- Scalar variation of constants: `y' = r`, `r = -c y + b`. -/
theorem mild_scalar (c : ℝ) (y r : ℝ → ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hy : ContinuousOn y (Set.Icc 0 t)) (hr : ContinuousOn r (Set.Icc 0 t))
    (heq : ∀ σ ∈ Set.Icc (0 : ℝ) t, y σ = y 0 + ∫ x in (0 : ℝ)..σ, r x) :
    y t = ((Real.exp (-(c * t)) : ℝ) : ℂ) * y 0 +
      ∫ σ in (0 : ℝ)..t, ((Real.exp (-(c * (t - σ))) : ℝ) : ℂ) * (r σ + (c : ℂ) * y σ) := by
  have hderiv : ∀ τ ∈ Set.Ioo (0 : ℝ) t, HasDerivAt y (r τ) τ := by
    intro τ hτ
    have hco : ContinuousOn r (Set.Ioo 0 t) := hr.mono Set.Ioo_subset_Icc_self
    have hat : Set.Ioo (0 : ℝ) t ∈ 𝓝 τ := Ioo_mem_nhds hτ.1 hτ.2
    have hint : IntervalIntegrable r volume 0 τ := by
      refine (hr.mono ?_).intervalIntegrable
      rw [Set.uIcc_of_le hτ.1.le]
      exact Set.Icc_subset_Icc le_rfl hτ.2.le
    have h1 := intervalIntegral.integral_hasDerivAt_right hint
      (hco.stronglyMeasurableAtFilter isOpen_Ioo τ hτ) (hco.continuousAt hat)
    have h2 := h1.const_add (y 0)
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [hat] with τ' hτ'
    exact heq τ' ⟨hτ'.1.le, hτ'.2.le⟩
  set F : ℝ → ℂ := fun σ => r σ + (c : ℂ) * y σ with hF
  have hFc : ContinuousOn F (Set.Icc 0 t) := hr.add (continuousOn_const.mul hy)
  set z : ℝ → ℂ := fun τ => ((Real.exp (c * τ) : ℝ) : ℂ) * y τ with hz
  have hexpc : Continuous (fun τ : ℝ => ((Real.exp (c * τ) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hzc : ContinuousOn z (Set.Icc 0 t) := hexpc.continuousOn.mul hy
  have hzd : ∀ τ ∈ Set.Ioo 0 t, HasDerivAt z (((Real.exp (c * τ) : ℝ) : ℂ) * F τ) τ := by
    intro τ hτ
    have h2 : HasDerivAt (fun τ' : ℝ => ((Real.exp (c * τ') : ℝ) : ℂ))
        (((c * Real.exp (c * τ) : ℝ) : ℂ)) τ := by
      have h3 : HasDerivAt (fun y : ℝ => c * y) c τ := by
        simpa using (hasDerivAt_id τ).const_mul c
      exact (h3.exp.congr_deriv (by ring)).ofReal_comp
    refine (h2.mul (hderiv τ hτ)).congr_deriv ?_
    simp only [hF]; push_cast; ring
  have hFI : IntervalIntegrable (fun σ => ((Real.exp (c * σ) : ℝ) : ℂ) * F σ) volume 0 t := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le ht]
    exact hexpc.continuousOn.mul hFc
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hzc hzd hFI
  have hz0 : z 0 = y 0 := by simp [hz]
  have hzt : z t = ((Real.exp (c * t) : ℝ) : ℂ) * y t := rfl
  rw [hz0, hzt] at hftc
  have hint : ∫ σ in (0 : ℝ)..t, ((Real.exp (-(c * (t - σ))) : ℝ) : ℂ) * F σ =
      ((Real.exp (-(c * t)) : ℝ) : ℂ) *
        ∫ σ in (0 : ℝ)..t, ((Real.exp (c * σ) : ℝ) : ℂ) * F σ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun σ _ => ?_
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 3; ring
  show y t = _ + ∫ σ in (0 : ℝ)..t, ((Real.exp (-(c * (t - σ))) : ℝ) : ℂ) * F σ
  rw [hint, hftc]
  have h1 : ((Real.exp (-(c * t)) : ℝ) : ℂ) * ((Real.exp (c * t) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]; simp
  calc y t = (((Real.exp (-(c * t)) : ℝ) : ℂ) * ((Real.exp (c * t) : ℝ) : ℂ)) * y t := by
        rw [h1, one_mul]
    _ = _ := by ring

end FrozenPath

/-! ### Frozen data as `AdjointData` at every level -/

open Classical in
/-- The regime used for the frozen coefficient (depends only on `d, s, c₀`). -/
def frozenRegime (d : ℕ) (s c₀ : ℝ) : Regime := if s ≤ (d : ℝ) - 2 then .R1 else .R2b c₀

theorem frozenRegime_lambdaM (d : ℕ) (s c₀ C ν₀ θ : ℝ) :
    (frozenRegime d s c₀).lambdaM C ν₀ θ = C := by
  unfold frozenRegime
  split_ifs <;> rfl

theorem adjointData_frozen_level {s νm νp c₀ Λ₀ β : ℝ} {V ρβ : Torus d → ℝ} (m : ℕ)
    (H : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρβ) (ν₀ T : ℝ) (hT : 0 < T) :
    AdjointData s m (frozenRegime d s c₀) 1 Λ₀ Λ₀ (mfData d s H.hs0 H.hsd V β H.hβ) ν₀ T
      (fun _ => ρβ) := by
  have hM : MatBound 1 (-1 : Matrix (Fin d) (Fin d) ℝ) := by
    intro i j
    by_cases h : i = j <;> simp [h]
  have hsym : Torus.SymNonpos (-1 : Matrix (Fin d) (Fin d) ℝ) := by
    unfold Torus.SymNonpos Torus.symPart
    simp only [Matrix.transpose_neg, Matrix.transpose_one]
    have : (-((1 / 2 : ℝ) • ((-1 : Matrix (Fin d) (Fin d) ℝ) + -1))) = 1 := by
      rw [← two_smul ℝ (-1 : Matrix (Fin d) (Fin d) ℝ), smul_smul]
      norm_num
    rw [this]
    exact Matrix.PosSemidef.one
  have common : ∀ (R : Regime),
      R.Holds d s (-1 : Matrix (Fin d) (Fin d) ℝ) β⁻¹ ν₀ T (fun _ => ρβ) →
      AdjointData s m R 1 Λ₀ Λ₀ (mfData d s H.hs0 H.hsd V β H.hβ) ν₀ T (fun _ => ρβ) :=
    fun R hR =>
    ⟨rfl, hM, ⟨H.hV, H.hVb⟩, ⟨fun r _ => H.thermal.1, fun r _ => H.hρC, fun r _ => H.hρb,
      fun ψ _ => continuousOn_const⟩, hT, hR⟩
  unfold frozenRegime
  split_ifs with hs
  · exact common _ hs
  · exact common _ ⟨by linarith, hsym, H.hc₀, fun r _ x => H.hlow x⟩


/-! ### Path-level facts for forward solutions with constant coefficient -/

section PathFacts

variable {s : ℝ} {m : ℕ} {R : Regime} {MB Λ VB : ℝ} {D : DynData d} {ν₀ T : ℝ} {ρ : Torus d → ℝ}

theorem mode_continuousOn {μ : ℝ → Torus d → ℝ} {t : ℝ} {φc : Coeff d} {F : ℝ → Coeff d}
    (h : IsForwardSolution D μ t φc F) (ht : 0 ≤ t) (k : Lattice d) :
    ContinuousOn (fun σ => F σ k) (Set.Icc 0 t) := by
  have hint : IntegrableOn (fun σ => forwardGen D (μ (t - σ)) (F σ) k) (Set.uIcc 0 t) := by
    rw [Set.uIcc_of_le ht]; exact h.integrable k
  have := (intervalIntegral.continuousOn_primitive_interval hint).const_add (φc k)
  rw [Set.uIcc_of_le ht] at this
  exact this.congr fun σ hσ => h.eq k σ hσ

/-- Re-anchoring of the integral equation at time `v`. -/
theorem forward_eq_shift {t : ℝ} {φc : Coeff d} {F : ℝ → Coeff d}
    (hF : IsForwardSolution D (fun _ => ρ) t φc F) (k : Lattice d) {v σ : ℝ} (hv : 0 ≤ v)
    (hσ : 0 ≤ σ) (hvσ : v + σ ≤ t) :
    F (v + σ) k = F v k + ∫ x in (0 : ℝ)..σ, forwardGen D ρ (F (v + x)) k := by
  have hi : ∀ b, 0 ≤ b → b ≤ t →
      IntervalIntegrable (fun x => forwardGen D ρ (F x) k) volume 0 b := by
    intro b hb0 hb1
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hb0]
    exact (hF.integrable k).mono_set (Set.Icc_subset_Icc_right hb1)
  have e1 := hF.eq k (v + σ) ⟨by linarith, hvσ⟩
  have e2 := hF.eq k v ⟨hv, by linarith⟩
  have hI1 := hi v hv (by linarith)
  have hI2 : IntervalIntegrable (fun x => forwardGen D ρ (F x) k) volume v (v + σ) := by
    refine (hi (v + σ) (by linarith) hvσ).mono_set ?_
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
    exact Set.Icc_subset_Icc hv le_rfl
  have e3 := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
  have e4 := intervalIntegral.integral_comp_add_left
    (fun x => forwardGen D ρ (F x) k) (a := 0) (b := σ) v
  simp only [add_zero] at e4
  rw [e4, e1, e2, ← e3]
  ring

/-- The modes of the generator along the propagator path are continuous. -/
theorem gen_continuousOn (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hm : 1 ≤ m)
    (hA : AdjointData s m R MB Λ VB D ν₀ T (fun _ => ρ)) {t : ℝ} (ht : t ∈ Set.Ioc 0 T)
    {φc : Coeff d} (hφ : MemHs m φc) (k : Lattice d) :
    ContinuousOn (fun σ => forwardGen D ρ (propagatorCoeff D (fun _ => ρ) m t φc σ) k)
      (Set.Icc 0 t) :=
  MFApriori.Aux.continuousOn_mode
    (adjoint_torus_time_regularity hd s hs0 hsd m hm R MB Λ VB D ν₀ T (fun _ => ρ) hA t ht φc hφ).1 k

/-- The mild formula for a forward solution, started at time `v`. -/
theorem mild_path {t : ℝ} {φc : Coeff d} {F : ℝ → Coeff d}
    (hF : IsForwardSolution D (fun _ => ρ) t φc F)
    (hgen : ∀ k, ContinuousOn (fun σ => forwardGen D ρ (F σ) k) (Set.Icc 0 t)) (k : Lattice d)
    {v t' : ℝ} (hv : 0 ≤ v) (ht' : 0 ≤ t') (hvt : v + t' ≤ t) :
    F (v + t') k = (MFApriori.heatMult (D.invβ * t') k : ℂ) * F v k +
      ∫ σ in (0 : ℝ)..t', (MFApriori.heatMult (D.invβ * (t' - σ)) k : ℂ) *
        (forwardGen D ρ (F (v + σ)) k - ((D.invβ : ℝ) : ℂ) * laplaceCoeff (F (v + σ)) k) := by
  have ht0 : 0 ≤ t := by linarith
  have hshift : ∀ σ ∈ Set.Icc (0 : ℝ) t', v + σ ∈ Set.Icc (0 : ℝ) t := fun σ hσ =>
    ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have hy : ContinuousOn (fun σ => F (v + σ) k) (Set.Icc 0 t') :=
    (mode_continuousOn hF ht0 k).comp (continuous_const.add continuous_id).continuousOn hshift
  have hr : ContinuousOn (fun σ => forwardGen D ρ (F (v + σ)) k) (Set.Icc 0 t') :=
    (hgen k).comp (continuous_const.add continuous_id).continuousOn hshift
  set c : ℝ := D.invβ * (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) with hc
  have key := mild_scalar c (fun σ => F (v + σ) k) (fun σ => forwardGen D ρ (F (v + σ)) k) t'
    ht' hy hr (fun σ hσ => by
      have := forward_eq_shift hF k hv hσ.1 (by linarith [hσ.2])
      simpa using this)
  have hheat : ∀ τ : ℝ, (MFApriori.heatMult (D.invβ * τ) k : ℂ) =
      ((Real.exp (-(c * τ)) : ℝ) : ℂ) := by
    intro τ
    simp only [MFApriori.heatMult, hc]
    congr 2; ring
  have hlap : ∀ G : Coeff d, ((D.invβ : ℝ) : ℂ) * laplaceCoeff G k = -((c : ℝ) : ℂ) * G k := by
    intro G
    simp only [laplaceCoeff, hc]
    push_cast; ring
  simp only [add_zero] at key
  rw [hheat]
  simp only [hheat, hlap]
  convert key using 3
  funext σ
  ring


theorem frozen_mild_eq_aux (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hm : 1 ≤ m)
    (hA : AdjointData s m R MB Λ VB D ν₀ T (fun _ => ρ)) {ψc : Coeff d} (hψ : MemHs m ψc)
    (k : Lattice d) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 T) :
    frozenCoeff D ρ m ψc τ k = (MFApriori.heatMult (D.invβ * τ) k : ℂ) * ψc k +
      ∫ σ in (0 : ℝ)..τ, (MFApriori.heatMult (D.invβ * (τ - σ)) k : ℂ) *
        (forwardGen D ρ (frozenCoeff D ρ m ψc σ) k -
          ((D.invβ : ℝ) : ℂ) * laplaceCoeff (frozenCoeff D ρ m ψc σ) k) := by
  rcases hτ.1.eq_or_lt with h0 | hpos
  · subst h0
    rw [frozenCoeff_zero hm hψ]
    simp [MFApriori.heatMult]
  · have ht : τ ∈ Set.Ioc 0 T := ⟨hpos, hτ.2⟩
    obtain ⟨C, -, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd m hm R MB Λ VB
    obtain ⟨hF, -, -⟩ := hspec D ν₀ T (fun _ => ρ) hA τ ht ψc hψ
    have hgen := gen_continuousOn hd hs0 hsd hm hA ht hψ
    have key := mild_path hF hgen k (le_refl 0) hpos.le (by linarith)
    simp only [zero_add] at key
    have h0 : propagatorCoeff D (fun _ => ρ) m τ ψc 0 = ψc := by
      funext k'
      have := hF.eq k' 0 ⟨le_rfl, hpos.le⟩
      simpa using this
    rw [h0] at key
    have hh : ∀ σ ∈ Set.Icc (0 : ℝ) τ, propagatorCoeff D (fun _ => ρ) m τ ψc σ =
        frozenCoeff D ρ m ψc σ := fun σ hσ =>
      frozenCoeff_eq_propagatorCoeff_aux hd hs0 hsd hm hA hψ ht hσ
    change propagatorCoeff D (fun _ => ρ) m τ ψc τ k = _ at key
    rw [hh τ ⟨hpos.le, le_rfl⟩] at key
    rw [key]
    congr 1
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    rw [Set.uIcc_of_le hpos.le] at hσ
    simp only [hh σ hσ]

end PathFacts

/-! ### One smoothing step -/

theorem kappa_bound {p νm ν u : ℝ} (hp : 0 ≤ p) (hνm : 0 < νm) (hν : νm ≤ ν) (hu : 0 < u)
    (hu1 : u ≤ 1) :
    1 + (ν * u) ^ (-p) ≤ (1 + νm ^ (-p)) * u ^ (-p) := by
  have hν0 : 0 < ν := lt_of_lt_of_le hνm hν
  rw [Real.mul_rpow hν0.le hu.le]
  have h1 : 1 ≤ u ^ (-p) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu hu1 (by linarith)
  have h2 : ν ^ (-p) ≤ νm ^ (-p) := Real.rpow_le_rpow_of_nonpos hνm hν (by linarith)
  have h3 : 0 ≤ u ^ (-p) := Real.rpow_nonneg hu.le _
  nlinarith [mul_le_mul_of_nonneg_right h2 h3]

theorem ae_mem_Ioo_restrict (a b : ℝ) :
    ∀ᵐ σ ∂(volume.restrict (Set.Ioc a b)), σ ∈ Set.Ioo a b := by
  have h1 : ∀ᵐ σ ∂(volume : Measure ℝ), σ ∉ ({b} : Set ℝ) :=
    (Set.countable_singleton b).ae_notMem volume
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [h1] with σ hσ hσ'
  exact ⟨hσ'.1, lt_of_le_of_ne hσ'.2 (by simpa using hσ)⟩

theorem smoothing_step (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (i r : ℝ) (hi : 1 ≤ i)
    (hr : (d : ℝ) / 2 + i < r) (νm N : ℝ) (hνm : 0 < νm) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : DynData d), D.s = s → D.M = -1 → νm ≤ D.invβ →
      ∀ ρ : Torus d → ℝ, Continuous ρ → MemHs r (coeffOf ρ) → MemHs r (coeffOf D.V) →
      hsNorm r (coeffOf ρ) + hsNorm r (coeffOf D.V) ≤ N →
      ∀ (G : ℝ → Coeff d) (B : ℝ),
        (∀ σ ∈ Set.Icc (0 : ℝ) 1, MemHs i (G σ) ∧ hsNorm i (G σ) ≤ B) →
        (∀ k, ContinuousOn (fun σ => G σ k) (Set.Icc 0 1)) →
        (∀ k, ContinuousOn (fun σ => forwardGen D ρ (G σ) k) (Set.Icc 0 1)) →
        MemHs (i - aExp d s) (G 0) →
        (∀ k, ∀ σ ∈ Set.Icc (0 : ℝ) 1, G σ k =
          (MFApriori.heatMult (D.invβ * σ) k : ℂ) * G 0 k +
          ∫ x in (0 : ℝ)..σ, (MFApriori.heatMult (D.invβ * (σ - x)) k : ℂ) *
            (forwardGen D ρ (G x) k - ((D.invβ : ℝ) : ℂ) * laplaceCoeff (G x) k)) →
        ∀ σ ∈ Set.Ioc (0 : ℝ) 1,
          hsNorm i (G σ) ≤ C * σ ^ (-(aExp d s / 2)) * hsNorm (i - aExp d s) (G 0) := by
  obtain ⟨ha1, ha2, -⟩ := aExp_spec (d := d) s hsd
  set a : ℝ := aExp d s with ha
  obtain ⟨CL, hCL0, hCL⟩ := exists_forwardGen_loss hd s hs0 hsd i r hi hr
  obtain ⟨Ch, hCh0, hCh⟩ := MFApriori.exists_heat_smoothing (d := d) (i - a) a (by linarith)
    (by linarith)
  set κ : ℝ := 1 + νm ^ (-(a / 2)) with hκ
  have hκ0 : 0 ≤ κ := by
    have := Real.rpow_nonneg hνm.le (-(a / 2)); rw [hκ]; linarith
  set Kh : ℝ := Ch * κ with hKh
  have hKh0 : 0 ≤ Kh := mul_nonneg hCh0 hκ0
  set N' : ℝ := max N 0 with hN'
  set C₁ : ℝ := Kh * (CL * N') with hC₁
  have hC₁0 : 0 ≤ C₁ := mul_nonneg hKh0 (mul_nonneg hCL0 (le_max_right _ _))
  obtain ⟨C', hC'0, hGr⟩ := singular_gronwall_meas (a / 2) (a / 2) C₁ (by linarith) (by linarith)
    (by linarith) (by linarith) hC₁0
  refine ⟨C' * Kh, mul_nonneg hC'0 hKh0, ?_⟩
  intro D hDs hDM hνD ρ hρc hρr hVr hN G B hG hGc hGgen hG0 hmild σ₀ hσ₀
  have hν : 0 < D.invβ := lt_of_lt_of_le hνm hνD
  set ν : ℝ := D.invβ with hνdef
  -- the generator remainder
  set b : ℝ → Coeff d := fun x => forwardGen D ρ (G x) - fun k => ((D.invβ : ℝ) : ℂ) *
    laplaceCoeff (G x) k with hb
  have hbm : ∀ x ∈ Set.Icc (0 : ℝ) 1, MemHs (i - a) (b x) ∧
      hsNorm (i - a) (b x) ≤ CL * N' * hsNorm i (G x) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hCL D hDs hDM ρ hρc hρr hVr (G x) (hG x hx).1
    refine ⟨h1, h2.trans ?_⟩
    have : hsNorm r (coeffOf ρ) + hsNorm r (coeffOf D.V) ≤ N' := hN.trans (le_max_left _ _)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hCL0)
      (MFApriori.hsNorm_nonneg' _ _)
  -- the function ψ
  set ψ : ℝ → ℝ := fun x => hsNorm i (G x) with hψ
  have hψnn : ∀ x, 0 ≤ ψ x := fun x => MFApriori.hsNorm_nonneg' _ _
  have hψmeas : AEStronglyMeasurable ψ (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    refine MFApriori.aestronglyMeasurable_hsNorm i G (fun k => ?_)
    exact ((hGc k).mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hinq : ∀ σ ∈ Set.Ioc (0 : ℝ) 1, ψ σ ≤ (Kh * hsNorm (i - a) (G 0)) * σ ^ (-(a / 2)) +
      C₁ * ∫ x in (0 : ℝ)..σ, (σ - x) ^ (-(a / 2)) * ψ x := by
    intro σ hσ
    have hσ0 := hσ.1
    have hσ1 := hσ.2
    set E : Coeff d := fun k => (MFApriori.heatMult (ν * σ) k : ℂ) * G 0 k with hE
    set H : ℝ → Coeff d := fun x k => (MFApriori.heatMult (ν * (σ - x)) k : ℂ) * b x k with hH
    set I : Coeff d := fun k => ∫ x in (0 : ℝ)..σ, H x k with hI
    have hGσ : G σ = fun k => E k + I k := by
      funext k
      exact hmild k σ ⟨hσ0.le, hσ1⟩
    -- the data term
    obtain ⟨hEm, hEn⟩ := hCh ν σ hν hσ0 (G 0) hG0
    rw [sub_add_cancel] at hEm hEn
    have hEn' : hsNorm i E ≤ Ch * κ * σ ^ (-(a / 2)) * hsNorm (i - a) (G 0) := by
      refine hEn.trans ?_
      have := kappa_bound (p := a / 2) (by linarith) hνm hνD hσ0 hσ1
      have h2 : Ch * (1 + (ν * σ) ^ (-(a / 2))) ≤ Ch * (κ * σ ^ (-(a / 2))) :=
        mul_le_mul_of_nonneg_left this hCh0
      calc Ch * (1 + (ν * σ) ^ (-(a / 2))) * hsNorm (i - a) (G 0)
          ≤ Ch * (κ * σ ^ (-(a / 2))) * hsNorm (i - a) (G 0) :=
            mul_le_mul_of_nonneg_right h2 (MFApriori.hsNorm_nonneg' _ _)
        _ = _ := by ring
    -- the integral term
    have hHm : ∀ x ∈ Set.Ioo (0 : ℝ) σ, MemHs i (H x) ∧
        hsNorm i (H x) ≤ Kh * (σ - x) ^ (-(a / 2)) * (CL * N' * ψ x) := by
      intro x hx
      have hx1 : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le.trans hσ1⟩
      have hux : 0 < σ - x := by linarith [hx.2]
      obtain ⟨hbm1, hbm2⟩ := hbm x hx1
      obtain ⟨h1, h2⟩ := hCh ν (σ - x) hν hux (b x) hbm1
      rw [sub_add_cancel] at h1 h2
      refine ⟨h1, h2.trans ?_⟩
      have hk := kappa_bound (p := a / 2) (by linarith) hνm hνD hux (by linarith [hx.1])
      have h3 : Ch * (1 + (ν * (σ - x)) ^ (-(a / 2))) ≤ Kh * (σ - x) ^ (-(a / 2)) := by
        rw [hKh]
        calc Ch * (1 + (ν * (σ - x)) ^ (-(a / 2))) ≤ Ch * (κ * (σ - x) ^ (-(a / 2))) :=
              mul_le_mul_of_nonneg_left hk hCh0
          _ = _ := by ring
      exact mul_le_mul h3 hbm2 (MFApriori.hsNorm_nonneg' _ _)
        (mul_nonneg hKh0 (Real.rpow_nonneg hux.le _))
    have hHmeas : ∀ k, AEStronglyMeasurable (fun x => H x k)
        (volume.restrict (Set.Ioc (0 : ℝ) σ)) := by
      intro k
      have hc : ContinuousOn (fun x => (MFApriori.heatMult (ν * (σ - x)) k : ℂ) *
          (forwardGen D ρ (G x) k - ((D.invβ : ℝ) : ℂ) * laplaceCoeff (G x) k))
          (Set.Icc 0 1) := by
        refine ContinuousOn.mul ?_ ((hGgen k).sub (continuousOn_const.mul ?_))
        · exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
            (continuous_const.mul (continuous_const.mul
              (continuous_const.sub continuous_id))))).continuousOn
        · simp only [laplaceCoeff]
          exact continuousOn_const.mul (hGc k)
      exact (hc.mono (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl hσ1))).aestronglyMeasurable
        measurableSet_Ioc
    have hker : IntegrableOn (fun x : ℝ => (σ - x) ^ (-(a / 2))) (Set.Ioc 0 σ) := by
      have := (intervalIntegrable_iff_integrableOn_Ioc_of_le hσ0.le).mp
        (MFApriori.intervalIntegrable_sub_rpow_neg (a / 2) (by linarith) σ)
      exact this
    have hψbd : ∀ x ∈ Set.Ioc (0 : ℝ) σ, ‖ψ x‖ ≤ B := by
      intro x hx
      have := hG x ⟨hx.1.le, hx.2.trans hσ1⟩
      rw [Real.norm_of_nonneg (hψnn x)]
      exact this.2
    have hψmeasσ : AEStronglyMeasurable ψ (volume.restrict (Set.Ioc (0 : ℝ) σ)) :=
      hψmeas.mono_measure (Measure.restrict_mono (Set.Ioc_subset_Ioc_right hσ1) le_rfl)
    have hψbdae : ∀ᵐ x ∂(volume.restrict (Set.Ioc (0 : ℝ) σ)), ‖ψ x‖ ≤ B := by
      rw [ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall hψbd
    have hrhs : Integrable (fun x : ℝ => Kh * (σ - x) ^ (-(a / 2)) * (CL * N' * ψ x))
        (volume.restrict (Set.Ioc (0 : ℝ) σ)) := by
      have h1 := (hker.const_mul (Kh * (CL * N'))).mul_bdd hψmeasσ hψbdae
      refine h1.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only
      ring
    have hHnorm_meas : AEStronglyMeasurable (fun x => hsNorm i (H x))
        (volume.restrict (Set.Ioc (0 : ℝ) σ)) :=
      MFApriori.aestronglyMeasurable_hsNorm i H hHmeas
    have hHint : IntegrableOn (fun x => hsNorm i (H x)) (Set.Ioc 0 σ) := by
      refine Integrable.mono' hrhs hHnorm_meas ?_
      filter_upwards [ae_mem_Ioo_restrict 0 σ] with x hx
      rw [Real.norm_of_nonneg (MFApriori.hsNorm_nonneg' _ _)]
      exact (hHm x hx).2
    obtain ⟨hIm, hIn⟩ := MFApriori.hsNorm_intervalIntegral_le i H 0 σ hσ0.le hHmeas
      (fun x hx => (hHm x hx).1) hHint
    have hIn' : hsNorm i I ≤ C₁ * ∫ x in (0 : ℝ)..σ, (σ - x) ^ (-(a / 2)) * ψ x := by
      refine hIn.trans ?_
      have hle : ∫ x in (0 : ℝ)..σ, hsNorm i (H x) ≤
          ∫ x in (0 : ℝ)..σ, Kh * (σ - x) ^ (-(a / 2)) * (CL * N' * ψ x) := by
        rw [intervalIntegral.integral_of_le hσ0.le, intervalIntegral.integral_of_le hσ0.le]
        refine integral_mono_ae hHint hrhs ?_
        filter_upwards [ae_mem_Ioo_restrict 0 σ] with x hx
        exact (hHm x hx).2
      refine hle.trans (le_of_eq ?_)
      rw [hC₁, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun x _ => ?_
      ring
    -- assemble
    obtain ⟨hsm, hsn⟩ := hs_add_le i hEm hIm
    have hGn : hsNorm i (G σ) ≤ hsNorm i E + hsNorm i I := by
      rw [hGσ]; exact hsn
    show hsNorm i (G σ) ≤ _
    refine hGn.trans ((add_le_add hEn' hIn').trans_eq ?_)
    rw [hKh]; ring
  have hA0 : 0 ≤ Kh * hsNorm (i - a) (G 0) := mul_nonneg hKh0 (MFApriori.hsNorm_nonneg' _ _)
  have := hGr ψ (Kh * hsNorm (i - a) (G 0)) B hA0 hψmeas
    (fun x hx => ⟨hψnn x, (hG x ⟨hx.1.le, hx.2⟩).2⟩) hinq σ₀ hσ₀
  show ψ σ₀ ≤ _
  refine this.trans_eq ?_
  ring

/-! ### Smoothing of the frozen path -/

section FrozenSmoothing

theorem frozen_coeff_norm_le {s νm νp c₀ Λ₀ β : ℝ} {n : ℕ} {V ρβ : Torus d → ℝ}
    (H : FrozenHyp d s n νm νp c₀ Λ₀ β V ρβ) :
    MemHs (n : ℝ) (coeffOf ρβ) ∧ MemHs (n : ℝ) (coeffOf V) ∧
      hsNorm n (coeffOf ρβ) + hsNorm n (coeffOf V) ≤ 2 * Real.sqrt ((1 + d) ^ n) * |Λ₀| := by
  obtain ⟨h1, h2⟩ := ClassicalPart.memHs_coeffOf_cbNorm n ρβ H.hρC
  obtain ⟨h3, h4⟩ := ClassicalPart.memHs_coeffOf_cbNorm n V H.hV
  refine ⟨h1, h3, ?_⟩
  have hb : ∀ (f : Torus d → ℝ), hsNormSq (n : ℝ) (coeffOf f) ≤ (1 + d) ^ n * Torus.cbNorm n f ^ 2 →
      Torus.cbNorm n f ≤ Λ₀ → hsNorm n (coeffOf f) ≤ Real.sqrt ((1 + d) ^ n) * |Λ₀| := by
    intro f hf hΛ
    unfold hsNorm
    calc Real.sqrt (hsNormSq (n : ℝ) (coeffOf f))
        ≤ Real.sqrt ((1 + d) ^ n * Torus.cbNorm n f ^ 2) := Real.sqrt_le_sqrt hf
      _ = Real.sqrt ((1 + d) ^ n) * Torus.cbNorm n f := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (ClassicalPart.cbNorm_nonneg'' n f)]
      _ ≤ Real.sqrt ((1 + d) ^ n) * |Λ₀| :=
          mul_le_mul_of_nonneg_left (hΛ.trans (le_abs_self _)) (Real.sqrt_nonneg _)
  have := hb ρβ h2 H.hρb
  have := hb V h4 H.hVb
  linarith

theorem frozen_aux_data {s νm νp c₀ Λ₀ β : ℝ} {n : ℕ} {V ρβ : Torus d → ℝ}
    (H : FrozenHyp d s n νm νp c₀ Λ₀ β V ρβ) (hn : 1 ≤ n) :
    Continuous ρβ ∧ 0 < (mfData d s H.hs0 H.hsd V β H.hβ).invβ ∧
      νm ≤ (mfData d s H.hs0 H.hsd V β H.hβ).invβ := by
  have hρ1 : Torus.IsCk 1 ρβ := ET.isCk_mono' (a := 1) (b := n) hn H.hρC
  exact ⟨MFAux.continuous_of_isCk hρ1, lt_of_lt_of_le H.hνm H.hν.1, H.hν.1⟩

/-- Smoothing step along the frozen path: gain `a` derivatives in unit time. -/
theorem frozen_step (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (j : ℕ) (hj : 1 ≤ j)
    (νm νp c₀ Λ₀ : ℝ) (i : ℝ) (hi : 1 ≤ i) (hij : i ≤ j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρβ : Torus d → ℝ)
      (H : FrozenHyp d s (j + mStar d) νm νp c₀ Λ₀ β V ρβ) (ψc : Coeff d), MemHs j ψc →
      ∀ v : ℝ, 0 ≤ v → ∀ σ ∈ Set.Ioc (0 : ℝ) 1,
        hsNorm i (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc (v + σ)) ≤
          C * σ ^ (-(aExp d s / 2)) *
            hsNorm (i - aExp d s) (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc v) := by
  by_cases hνm : 0 < νm
  swap
  · refine ⟨0, le_rfl, fun β V ρβ H => ?_⟩
    exact absurd H.hνm hνm
  set r : ℝ := ((j + mStar d : ℕ) : ℝ) with hr
  have hr' : (d : ℝ) / 2 + i < r := by
    have h1 : (i : ℝ) ≤ j := hij
    have := mStar_gt d
    rw [hr]; push_cast; linarith
  obtain ⟨C, hC0, hC⟩ := smoothing_step hd s hs0 hsd i r hi hr' νm
    (2 * Real.sqrt ((1 + d) ^ (j + mStar d)) * |Λ₀|) hνm
  obtain ⟨L, hL, hLb⟩ := exists_frozenCoeff_bound (d := d) (s := s) (m := j) hd hs0 hsd hj
    (frozenRegime d s c₀) 1 Λ₀ Λ₀
  refine ⟨C, hC0, fun β V ρβ H ψc hψ v hv σ hσ => ?_⟩
  set D := mfData d s H.hs0 H.hsd V β H.hβ with hD
  obtain ⟨hρc, hν, hνD⟩ := frozen_aux_data H (by have := ClassicalPart.three_le_mStar d; omega)
  obtain ⟨hρm, hVm, hN⟩ := frozen_coeff_norm_le H
  have H3 : FrozenHyp d s (j + 3) νm νp c₀ Λ₀ β V ρβ :=
    H.mono (by have := ClassicalPart.three_le_mStar d; omega)
  set T' : ℝ := v + 1 with hT'
  have hT'0 : 0 < T' := by linarith
  have hA := adjointData_frozen_level j H3 0 T' hT'0
  have hT'mem : T' ∈ Set.Ioc 0 T' := ⟨hT'0, le_rfl⟩
  obtain ⟨C₀, -, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd j hj (frozenRegime d s c₀) 1 Λ₀ Λ₀
  obtain ⟨hF, hw, -⟩ := hspec D 0 T' (fun _ => ρβ) hA T' hT'mem ψc hψ
  set F := propagatorCoeff D (fun _ => ρβ) j T' ψc with hFdef
  have hgen := gen_continuousOn hd hs0 hsd hj hA hT'mem hψ
  have hhom : ∀ x ∈ Set.Icc (0 : ℝ) T', F x = frozenCoeff D ρβ j ψc x := fun x hx =>
    frozenCoeff_eq_propagatorCoeff_aux hd hs0 hsd hj hA hψ hT'mem hx
  have hbnd : ∀ x ∈ Set.Icc (0 : ℝ) T', MemHs j (F x) ∧
      hsNorm j (F x) ≤ Real.exp (L * T') * hsNorm j ψc := by
    intro x hx
    rw [hhom x hx]
    obtain ⟨h1, h2⟩ := hLb D 0 T' ρβ hA ψc hψ x hx
    rw [frozenRegime_lambdaM] at h2
    refine ⟨h1, h2.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by nlinarith [hx.2, hL]))
      (MFApriori.hsNorm_nonneg' _ _)
  have hshift : ∀ x ∈ Set.Icc (0 : ℝ) 1, v + x ∈ Set.Icc (0 : ℝ) T' := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hij' : (i : ℝ) ≤ (j : ℝ) := hij
  have hjmem : ∀ x ∈ Set.Icc (0 : ℝ) T', MemHs i (F x) ∧ hsNorm i (F x) ≤ hsNorm j (F x) := by
    intro x hx
    have := (hbnd x hx).1
    exact ⟨this.mono hij', MFApriori.hsNorm_mono_idx hij' this⟩
  have hres := hC D rfl rfl hνD ρβ hρc (by simpa [hr] using hρm) (by simpa [hr, hD, mfData] using hVm)
    (by simpa [hr, hD, mfData] using hN) (fun x => F (v + x))
    (Real.exp (L * T') * hsNorm j ψc)
    (fun x hx => ⟨(hjmem _ (hshift x hx)).1,
      (hjmem _ (hshift x hx)).2.trans (hbnd _ (hshift x hx)).2⟩)
    (fun k => (mode_continuousOn hF hT'0.le k).comp (continuous_const.add continuous_id).continuousOn
      hshift)
    (fun k => (hgen k).comp (continuous_const.add continuous_id).continuousOn hshift)
    (by
      have := (hbnd v ⟨hv, by linarith⟩).1
      have h0 : F (v + 0) = F v := by rw [add_zero]
      show MemHs (i - aExp d s) (F (v + 0))
      rw [h0]
      obtain ⟨-, ha2, -⟩ := aExp_spec (d := d) s hsd
      have : (i - aExp d s) ≤ (j : ℝ) := by
        have := (aExp_spec (d := d) s hsd).1
        linarith
      exact (hbnd v ⟨hv, by linarith⟩).1.mono this)
    (fun k x hx => by
      have := mild_path hF hgen k hv hx.1 (by linarith [hx.2] : v + x ≤ T')
      simpa using this) σ hσ
  have h1 : F (v + σ) = frozenCoeff D ρβ j ψc (v + σ) := hhom _ (hshift σ ⟨hσ.1.le, hσ.2⟩)
  have h2 : F (v + 0) = frozenCoeff D ρβ j ψc v := by
    rw [add_zero]; exact hhom v ⟨hv, by linarith⟩
  simp only [h1] at hres
  rw [h2] at hres
  exact hres

end FrozenSmoothing

/-! ### Packet statements 2, 3, 4 (verbatim) -/

/-- Linearity of the frozen propagator in the datum (uniqueness), and time-homogeneity. -/
theorem frozenCoeff_sub (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ) (ρβ : Torus d → ℝ)
    (hA : AdjointData s m R MB Λ VB D ν₀ T (fun _ => ρβ)) (ψc ψc' : Coeff d) (hψ : MemHs m ψc)
    (hψ' : MemHs m ψc') {τ : ℝ} (hτ : τ ∈ Set.Icc 0 T) :
    frozenCoeff D ρβ m (ψc - ψc') τ = frozenCoeff D ρβ m ψc τ - frozenCoeff D ρβ m ψc' τ :=
  frozenCoeff_sub_aux hd hs0 hsd hm hA hψ hψ' hτ

theorem frozenCoeff_eq_propagatorCoeff (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (hm : 1 ≤ m) (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ) (ρβ : Torus d → ℝ)
    (hA : AdjointData s m R MB Λ VB D ν₀ T (fun _ => ρβ)) (ψc : Coeff d) (hψ : MemHs m ψc)
    {t τ : ℝ} (ht : t ∈ Set.Ioc 0 T) (hτ : τ ∈ Set.Icc 0 t) :
    propagatorCoeff D (fun _ => ρβ) m t ψc τ = frozenCoeff D ρβ m ψc τ :=
  frozenCoeff_eq_propagatorCoeff_aux hd hs0 hsd hm hA hψ ht hτ

set_option linter.unusedVariables false in
/-- Frozen mild formula (variation of constants against the heat semigroup), modewise. -/
theorem frozen_mild_eq (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ) (ρβ : Torus d → ℝ)
    (hA : AdjointData s m R MB Λ VB D ν₀ T (fun _ => ρβ)) (hν : 0 < D.invβ) (ψc : Coeff d)
    (hψ : MemHs m ψc) (k : Lattice d) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 T) :
    frozenCoeff D ρβ m ψc τ k = (MFApriori.heatMult (D.invβ * τ) k : ℂ) * ψc k +
      ∫ σ in (0 : ℝ)..τ, (MFApriori.heatMult (D.invβ * (τ - σ)) k : ℂ) *
        (forwardGen D ρβ (frozenCoeff D ρβ m ψc σ) k -
          ((D.invβ : ℝ) : ℂ) * laplaceCoeff (frozenCoeff D ρβ m ψc σ) k) :=
  frozen_mild_eq_aux hd hs0 hsd hm hA hψ k hτ

/-! ### Centering and the Parseval link -/

theorem summable_meanTerm {a c : Coeff d} (ha : MemHs 0 a) (hc : MemHs 0 c) :
    Summable fun k => ((sobWeight 0 k : ℝ) : ℂ) * (a k * conj (c k)) := by
  have ha2 : Summable fun k => (‖a k‖) ^ 2 := (memHs_zero_iff _).mp ha
  have hc2 : Summable fun k => (‖c k‖) ^ 2 := (memHs_zero_iff _).mp hc
  obtain ⟨hs, -⟩ := Torus.cs_tsum (fun k => ‖a k‖) (fun k => ‖c k‖)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) ha2 hc2
  refine Summable.of_norm (hs.congr fun k => ?_)
  rw [sobWeight_zero]; simp

theorem meanCoeff_coeffOf {ρ f : Torus d → ℝ} (hρ : IsProbDensity ρ) (hρc : Continuous ρ)
    (hf : Continuous f) : meanCoeff ρ (coeffOf f) = pair (withDensityReal ρ) f := by
  have hm1 : MemLp (fun x => (ρ x : ℂ)) 2 volume :=
    MFThermal.memLp_two_of_continuous (Complex.continuous_ofReal.comp hρc)
  have hm2 : MemLp (fun x => (f x : ℂ)) 2 volume :=
    MFThermal.memLp_two_of_continuous (Complex.continuous_ofReal.comp hf)
  have h := hasSum_parseval _ _ hm1 hm2
  have hint : ∫ t, conj ((ρ t : ℂ)) * (f t : ℂ) = ((∫ t, ρ t * f t : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp
  have h2 : hsInner 0 (coeffOf ρ) (coeffOf f) = conj (∫ t, conj ((ρ t : ℂ)) * (f t : ℂ)) := by
    rw [← h.tsum_eq, Complex.conj_tsum]
    unfold hsInner
    refine tsum_congr fun k => ?_
    rw [sobWeight_zero]
    simp [coeffOf]
  unfold meanCoeff
  rw [h2, hint, Complex.conj_ofReal, Complex.ofReal_re, MFAdjoint.pair_mu hρ]

theorem meanCoeff_sub_delta {ρ : Torus d → ℝ} {c : Coeff d} (hρ : MemHs 0 (coeffOf ρ))
    (hc : MemHs 0 c) (r : ℝ) :
    meanCoeff ρ (c - (r : ℂ) • deltaCoeff (0 : Lattice d)) =
      meanCoeff ρ c - r * (coeffOf ρ 0).re := by
  have hδ : MemHs 0 ((r : ℂ) • deltaCoeff (0 : Lattice d)) := memHs_smul_delta 0 r
  have hs1 := summable_meanTerm hρ hc
  have hs2 := summable_meanTerm hρ hδ
  unfold meanCoeff hsInner
  have : (∑' k, ((sobWeight 0 k : ℝ) : ℂ) * (coeffOf ρ k * conj ((c - (r : ℂ) • deltaCoeff (0 : Lattice d)) k))) =
      (∑' k, ((sobWeight 0 k : ℝ) : ℂ) * (coeffOf ρ k * conj (c k))) -
        ∑' k, ((sobWeight 0 k : ℝ) : ℂ) * (coeffOf ρ k * conj (((r : ℂ) • deltaCoeff (0 : Lattice d)) k)) := by
    rw [← Summable.tsum_sub hs1 hs2]
    refine tsum_congr fun k => ?_
    simp only [Pi.sub_apply, map_sub]
    ring
  rw [this, Complex.sub_re]
  congr 1
  rw [tsum_eq_single (0 : Lattice d)]
  · simp [sobWeight_zero, deltaCoeff]
    ring
  · intro k hk
    simp [deltaCoeff, hk]


theorem coeffOf_zero_prob {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) : (coeffOf ρ 0).re = 1 := by
  rw [MFApriori.coeffOf_zero_eq_integral', Complex.ofReal_re, hρ.integral_one]

theorem centerCoeff_eq_of_sub_delta {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ)
    (hρ0 : MemHs 0 (coeffOf ρ)) {c c' : Coeff d} (hc : MemHs 0 c) (r : ℝ)
    (h : c' = c - (r : ℂ) • deltaCoeff (0 : Lattice d)) :
    centerCoeff ρ c' = centerCoeff ρ c := by
  have hm : meanCoeff ρ c' = meanCoeff ρ c - r := by
    rw [h, meanCoeff_sub_delta hρ0 hc, coeffOf_zero_prob hρ, mul_one]
  funext k
  have e1 : ∀ (e : Coeff d), centerCoeff ρ e k = e k - (meanCoeff ρ e : ℂ) * deltaCoeff 0 k :=
    fun e => by simp [centerCoeff]
  rw [e1, e1, hm, h]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem meanCoeff_centerCoeff {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ)
    (hρ0 : MemHs 0 (coeffOf ρ)) {c : Coeff d} (hc : MemHs 0 c) :
    meanCoeff ρ (centerCoeff ρ c) = 0 := by
  have := meanCoeff_sub_delta hρ0 hc (meanCoeff ρ c)
  rw [coeffOf_zero_prob hρ, mul_one, sub_self] at this
  exact this

theorem centerCoeff_idem {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ)
    (hρ0 : MemHs 0 (coeffOf ρ)) {c : Coeff d} (hc : MemHs 0 c) :
    centerCoeff ρ (centerCoeff ρ c) = centerCoeff ρ c :=
  centerCoeff_eq_of_sub_delta hρ hρ0 hc (meanCoeff ρ c) rfl


theorem centerCoeff_isReal {ρ : Torus d → ℝ} {c : Coeff d} (hc : IsRealCoeff c) :
    IsRealCoeff (centerCoeff ρ c) := by
  intro k
  by_cases hk : k = 0
  · subst hk
    have := hc 0
    simp only [neg_zero] at this
    rw [neg_zero]
    simp only [centerCoeff, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, deltaCoeff, ite_true,
      mul_one, map_sub, Complex.conj_ofReal]
    rw [← this]
  · have hk' : -k ≠ 0 := by simpa using hk
    simp [centerCoeff, deltaCoeff, hk, hk', hc k]

theorem summable_center {ρ : Torus d → ℝ} {c : Coeff d} (hs : Summable fun k => ‖c k‖) :
    Summable fun k => ‖centerCoeff ρ c k‖ := by
  have hδ : Summable fun k : Lattice d => ‖((meanCoeff ρ c : ℂ) • deltaCoeff (0 : Lattice d)) k‖ :=
    summable_of_ne_finset_zero (s := {0}) fun k hk => by
      have : k ≠ 0 := by simpa using hk
      simp [deltaCoeff, this]
  exact Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => norm_sub_le _ _) (hs.add hδ)

theorem toFun_centerCoeff {ρ : Torus d → ℝ} {c : Coeff d} (hs : Summable fun k => ‖c k‖)
    (x : Torus d) : toFun (centerCoeff ρ c) x = toFun c x - meanCoeff ρ c := by
  have hδ : ClassicalPart.WS 0 ((meanCoeff ρ c : ℂ) • deltaCoeff (0 : Lattice d)) := by
    rw [ClassicalPart.WS_zero_iff]
    exact summable_of_ne_finset_zero (s := {0}) fun k hk => by
      have : k ≠ 0 := by simpa using hk
      simp [deltaCoeff, this]
  have h1 : centerCoeff ρ c = c - (meanCoeff ρ c : ℂ) • deltaCoeff (0 : Lattice d) := rfl
  rw [h1, ClassicalPart.toFun_sub ((ClassicalPart.WS_zero_iff c).2 hs) hδ]
  congr 1
  unfold toFun series
  rw [tsum_eq_single (0 : Lattice d)]
  · simp [deltaCoeff, Torus.mode_zero]
  · intro k hk
    simp [deltaCoeff, hk]

theorem projMean_toFun {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (hρc : Continuous ρ)
    {c : Coeff d} {m : ℝ} (hs : Summable fun k => ‖c k‖) (hc : MemHs m c)
    (hreal : IsRealCoeff c) :
    projMean (withDensityReal ρ) (toFun c) = toFun (centerCoeff ρ c) ∧
    MemSobolev m (toFun (centerCoeff ρ c)) ∧
    sobolevNorm m (toFun (centerCoeff ρ c)) = hsNorm m (centerCoeff ρ c) := by
  have hpair : pair (withDensityReal ρ) (toFun c) = meanCoeff ρ c := by
    rw [← meanCoeff_coeffOf hρ hρc (continuous_toFun c hs), coeffOf_toFun c hreal hs]
  refine ⟨?_, ?_⟩
  · funext x
    rw [toFun_centerCoeff hs, projMean, hpair]
  · exact ClassicalPart.memSobolev_toFun (summable_center hs)
      (memHs_sub hc (memHs_smul_delta m _)) (centerCoeff_isReal hreal)

/-- Centering is bounded on every `H^i`, `i ≥ 0`, with an explicit constant. -/
theorem centerCoeff_bound' {ρβ : Torus d → ℝ} (hρ : IsProbDensity ρβ) (hc : Continuous ρβ)
    {Λ₀ : ℝ} (hΛ : ∀ x, ρβ x ≤ Λ₀) {i : ℝ} (hi : 0 ≤ i) {c : Coeff d} (hci : MemHs i c) :
    MemHs i (centerCoeff ρβ c) ∧ hsNorm i (centerCoeff ρβ c) ≤ 2 * (1 + Λ₀) * hsNorm i c := by
  have hΛ0 : 0 ≤ Λ₀ := (hρ.nonneg 0).trans (hΛ 0)
  obtain ⟨hρ0, hρΛ⟩ := memHs_zero_coeffOf_le hρ hc hΛ
  have hc0 : MemHs 0 c := by
    have := (hs_lower hi hci).1
    simpa using this
  have hc0n : hsNorm 0 c ≤ hsNorm i c := by
    have := (hs_lower hi hci).2
    simpa using this
  have hm := abs_meanCoeff_le ρβ hρ0 hc0
  have hρn : hsNorm 0 (coeffOf ρβ) ≤ Real.sqrt Λ₀ := by
    unfold hsNorm
    exact Real.sqrt_le_sqrt hρΛ
  have hmabs : |meanCoeff ρβ c| ≤ Real.sqrt Λ₀ * hsNorm i c :=
    hm.trans (mul_le_mul hρn hc0n (hsNorm_nonneg' _ _) (Real.sqrt_nonneg _))
  set m : ℝ := meanCoeff ρβ c with hmdef
  have hy := hs_mult (m := i) (γ := 0) (C := |m|) (abs_nonneg _) (memHs_deltaCoeff (d := d) i)
    (e := fun k => -((m : ℂ) * deltaCoeff (0 : Lattice d) k)) (fun k => by
      rw [Real.rpow_zero, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]; simp)
  have hcen : centerCoeff ρβ c = fun k => c k + -((m : ℂ) * deltaCoeff (0 : Lattice d) k) := by
    funext k
    simp [centerCoeff, sub_eq_add_neg, hmdef]
  rw [hcen]
  obtain ⟨hA, hA'⟩ := hs_add_le i hci (by simpa using hy.1)
  refine ⟨hA, hA'.trans ?_⟩
  have hy2 : hsNorm i (fun k => -((m : ℂ) * deltaCoeff (0 : Lattice d) k)) ≤ |m| := by
    have := hy.2
    rw [hsNorm_deltaCoeff_zero] at this
    simpa using this
  have ht : Real.sqrt Λ₀ ≤ 1 + 2 * Λ₀ := by
    have h1 := Real.sq_sqrt hΛ0
    nlinarith [Real.sqrt_nonneg Λ₀, sq_nonneg (Real.sqrt Λ₀ - 1)]
  have hN0 := hsNorm_nonneg' i c
  nlinarith [mul_le_mul_of_nonneg_right ht hN0]


/-! ### The frozen path: reality, centering, levels -/

section FrozenCenter

variable {s : ℝ} {m : ℕ} {R : Regime} {MB Λ VB : ℝ} {D : DynData d} {ν₀ T : ℝ} {ρ : Torus d → ℝ}

theorem frozenCoeff_real (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hm : 1 ≤ m)
    (hA : AdjointData s m R MB Λ VB D ν₀ T (fun _ => ρ)) {ψc : Coeff d} (hψ : MemHs m ψc)
    (hre : IsRealCoeff ψc) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 T) :
    IsRealCoeff (frozenCoeff D ρ m ψc τ) := by
  rcases hτ.1.eq_or_lt with h0 | hpos
  · subst h0
    rw [frozenCoeff_zero hm hψ]; exact hre
  · exact ClassicalPart.propagatorCoeff_real hd s hs0 hsd m hm R MB Λ VB D ν₀ T (fun _ => ρ) hA τ
      ⟨hpos, hτ.2⟩ ψc hψ hre τ ⟨hτ.1, le_rfl⟩

theorem center_frozen_center (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hm : 1 ≤ m)
    (hA : AdjointData s m R MB Λ VB D ν₀ T (fun _ => ρ)) (hρ : IsProbDensity ρ)
    (hρc : Continuous ρ) {ψc : Coeff d} (hψ : MemHs m ψc) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 T) :
    centerCoeff ρ (frozenCoeff D ρ m ψc τ) =
      centerCoeff ρ (frozenCoeff D ρ m (centerCoeff ρ ψc) τ) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hδ : MemHs (m : ℝ) ((meanCoeff ρ ψc : ℂ) • deltaCoeff (0 : Lattice d)) :=
    memHs_smul_delta _ _
  have hsub : frozenCoeff D ρ m (centerCoeff ρ ψc) τ =
      frozenCoeff D ρ m ψc τ - (meanCoeff ρ ψc : ℂ) • deltaCoeff (0 : Lattice d) := by
    have h1 : centerCoeff ρ ψc = ψc - (meanCoeff ρ ψc : ℂ) • deltaCoeff (0 : Lattice d) := rfl
    rw [h1, frozenCoeff_sub_aux hd hs0 hsd hm hA hψ hδ hτ,
      frozenCoeff_const_delta hd hs0 hsd hm hA _ hτ]
  have hmem := (exists_frozenCoeff_bound (d := d) (s := s) (m := m) hd hs0 hsd hm R MB Λ VB).choose_spec.2
    D ν₀ T ρ hA ψc hψ τ hτ
  have hc0 : MemHs 0 (frozenCoeff D ρ m ψc τ) := hmem.1.mono (by linarith)
  exact (centerCoeff_eq_of_sub_delta hρ (MFApriori.memHs_zero_coeffOf_continuous hρc) hc0 _ hsub).symm

theorem center_frozen_shift (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hm : 1 ≤ m)
    (hA : AdjointData s m R MB Λ VB D ν₀ T (fun _ => ρ)) (hρ : IsProbDensity ρ)
    (hρc : Continuous ρ) {ψc : Coeff d} (hψ : MemHs m ψc) {τ v : ℝ} (hτ : 0 ≤ τ) (hv : 0 ≤ v)
    (hτv : τ + v ≤ T) :
    centerCoeff ρ (frozenCoeff D ρ m ψc (τ + v)) =
      centerCoeff ρ (frozenCoeff D ρ m (centerCoeff ρ (frozenCoeff D ρ m ψc τ)) v) := by
  obtain ⟨hmem, hsh⟩ := frozenCoeff_shift hd hs0 hsd hm hA hψ hτ hv hτv
  rw [← hsh]
  exact center_frozen_center hd hs0 hsd hm hA hρ hρc hmem ⟨hv, by linarith⟩

/-- The frozen path does not depend on the (admissible) level of the datum. -/
theorem frozenCoeff_level (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {m m' : ℕ} (hm : 1 ≤ m)
    (hmm' : m ≤ m') (hA : AdjointData s m R MB Λ VB D ν₀ T (fun _ => ρ))
    (hA' : AdjointData s m' R MB Λ VB D ν₀ T (fun _ => ρ)) {ψc : Coeff d} (hψ' : MemHs m' ψc)
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 T) :
    frozenCoeff D ρ m ψc τ = frozenCoeff D ρ m' ψc τ := by
  have hmm'R : (m : ℝ) ≤ m' := by exact_mod_cast hmm'
  have hψ : MemHs m ψc := hψ'.mono hmm'R
  have hm1' : 1 ≤ m' := hm.trans hmm'
  rcases hτ.1.eq_or_lt with h0 | hpos
  · subst h0
    rw [frozenCoeff_zero hm hψ, frozenCoeff_zero hm1' hψ']
  · have ht : τ ∈ Set.Ioc 0 T := ⟨hpos, hτ.2⟩
    obtain ⟨C, -, hspec⟩ := propagatorCoeff_spec hd s hs0 hsd m' hm1' R MB Λ VB
    obtain ⟨hF, hw, -⟩ := hspec D ν₀ T (fun _ => ρ) hA' τ ht ψc hψ'
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    exact propagatorCoeff_eq_of_solution hd hs0 hsd hm hA ht hψ hF
      (weakContinuousInHs_mono (by exact_mod_cast hm1' : (1 : ℝ) ≤ m') hw) τ ⟨hτ.1, le_rfl⟩

end FrozenCenter

/-! ### Function-level bridge -/

theorem memSobolev_mono_idx {m m' : ℝ} {ψ : Torus d → ℝ} (hψ : MemSobolev m ψ) (h : m' ≤ m) :
    MemSobolev m' ψ := by
  have := (hsNormSq_coeffOf m ψ hψ).1
  exact memSobolev_of_memHs m' ψ hψ.1 (this.mono h)

theorem equilibriumSemigroup_eq (hd : 1 ≤ d) {s νm νp c₀ Λ₀ β : ℝ} {V ρβ : Torus d → ℝ} (m : ℕ)
    (hm : mStar d + 2 ≤ m) (H : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρβ) {ψ : Torus d → ℝ}
    (hψc : Continuous ψ) (hψ : MemSobolev m ψ) {τ : ℝ} (hτ : 0 ≤ τ) :
    equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ =
      projMean (withDensityReal ρβ)
        (toFun (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ m (coeffOf ψ) τ)) := by
  set D := mfData d s H.hs0 H.hsd V β H.hβ with hD
  have hmst : mStar d ≤ m := by omega
  have hm1 : 1 ≤ m := by have := ClassicalPart.three_le_mStar d; omega
  have hmR : ((mStar d : ℝ) + 2) ≤ (m : ℝ) := by exact_mod_cast hm
  have hψ2' : MemSobolev ((mStar d : ℝ) + 2) ψ := memSobolev_mono_idx hψ hmR
  have hcm : MemHs (m : ℝ) (coeffOf ψ) := (hsNormSq_coeffOf _ ψ hψ).1
  unfold equilibriumSemigroup
  congr 1
  rcases hτ.eq_or_lt with h0 | hpos
  · subst h0
    have hψ2 : Torus.IsCk 2 ψ := isCk_two_of_memSobolev hψc hψ2'
    have hKf := ClassicalAux.convKernelFacts hd D
    have hV1 : Torus.IsCk 1 D.V := ET.isCk_mono' (a := 1) (b := m + 3) (by omega) H.hV
    have hρ1 : Torus.IsCk 1 ρβ := ET.isCk_mono' (a := 1) (b := m + 3) (by omega) H.hρC
    rw [MFSemigroup.propagator_zero D hKf hV1 _ hρ1 hψ2, frozenCoeff_zero hm1 hcm]
    have hdm : (d : ℝ) / 2 < m := by linarith [mStar_gt d]
    exact (MFThermalReg.toFun_coeffOf hψc (summable_norm_of_memHs _ hdm _ hcm)).symm
  · have hA := adjointData_frozen_level m H 0 τ hpos
    rw [ClassicalPart.propagator_eq_toFun hd s H.hs0 H.hsd m hmst _ 1 Λ₀ Λ₀ D 0 τ (fun _ => ρβ) hA τ
      ⟨hpos, le_rfl⟩ ψ hψc hψ 0 ⟨le_rfl, hτ⟩]
    funext x
    simp [frozenCoeff]


section FrozenFun

variable {s νm νp c₀ Λ₀ β : ℝ} {V ρβ : Torus d → ℝ} {n : ℕ}

theorem FrozenHyp.cont (H : FrozenHyp d s n νm νp c₀ Λ₀ β V ρβ) (hn : 1 ≤ n) : Continuous ρβ :=
  MFAux.continuous_of_isCk (ET.isCk_mono' (a := 1) (b := n) hn H.hρC)

theorem FrozenHyp.le_Lam (H : FrozenHyp d s n νm νp c₀ Λ₀ β V ρβ) (x : Torus d) : ρβ x ≤ Λ₀ :=
  (le_abs_self _).trans ((abs_le_cbNorm n ρβ H.hρC x).trans H.hρb)

/-- Data of the frozen path at a function datum. -/
theorem frozenData (hd : 1 ≤ d) (m : ℕ) (hm : mStar d + 2 ≤ m)
    (H : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρβ) {ψ : Torus d → ℝ} (hψc : Continuous ψ)
    (hψ : MemSobolev m ψ) {τ : ℝ} (hτ : 0 ≤ τ) :
    MemHs m (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ m (coeffOf ψ) τ) ∧
    IsRealCoeff (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ m (coeffOf ψ) τ) ∧
    Summable (fun k => ‖frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ m (coeffOf ψ) τ k‖) := by
  have hm1 : 1 ≤ m := by have := ClassicalPart.three_le_mStar d; omega
  have hcm : MemHs (m : ℝ) (coeffOf ψ) := (hsNormSq_coeffOf _ ψ hψ).1
  have hre : IsRealCoeff (coeffOf ψ) := isRealCoeff_coeffOf ψ (integrable_of_cont hψc)
  have hA := adjointData_frozen_level m H 0 (τ + 1) (by linarith)
  have hτT : τ ∈ Set.Icc (0 : ℝ) (τ + 1) := ⟨hτ, by linarith⟩
  have hmem := ((exists_frozenCoeff_bound (d := d) (s := s) (m := m) hd H.hs0 H.hsd hm1
    (frozenRegime d s c₀) 1 Λ₀ Λ₀).choose_spec.2 _ 0 (τ + 1) ρβ hA _ hcm τ hτT).1
  have hdm : (d : ℝ) / 2 < m := by
    have := mStar_gt d
    have h2 : (mStar d : ℝ) + 2 ≤ m := by exact_mod_cast hm
    linarith
  exact ⟨hmem, frozenCoeff_real hd H.hs0 H.hsd hm1 hA hcm hre hτT,
    summable_norm_of_memHs _ hdm _ hmem⟩

theorem S_eq (hd : 1 ≤ d) (m : ℕ) (hm : mStar d + 2 ≤ m)
    (H : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρβ) {ψ : Torus d → ℝ} (hψc : Continuous ψ)
    (hψ : MemSobolev m ψ) {τ : ℝ} (hτ : 0 ≤ τ) :
    equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ =
      toFun (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ m (coeffOf ψ) τ)) ∧
    ∀ m' : ℝ, 0 ≤ m' → m' ≤ m →
      MemSobolev m' (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) ∧
      sobolevNorm m' (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) =
        hsNorm m' (centerCoeff ρβ
          (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ m (coeffOf ψ) τ)) := by
  obtain ⟨hmem, hre, hsum⟩ := frozenData hd m hm H hψc hψ hτ
  have hm3 : 1 ≤ m + 3 := by omega
  have hprob := H.thermal.1
  have hρc := H.cont hm3
  have h1 := equilibriumSemigroup_eq hd m hm H hψc hψ hτ
  have h2 := (projMean_toFun hprob hρc hsum hmem hre).1
  refine ⟨h1.trans h2, fun m' hm'0 hm'm => ?_⟩
  have hmem' : MemHs m' (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ m (coeffOf ψ) τ) :=
    hmem.mono hm'm
  have h3 := (projMean_toFun hprob hρc hsum hmem' hre)
  rw [h1, h3.1]
  exact h3.2

theorem proj_data (m : ℕ) (hm : mStar d + 2 ≤ m)
    (H : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρβ) {ψ : Torus d → ℝ} (hψc : Continuous ψ)
    (hψ : MemSobolev m ψ) :
    projMean (withDensityReal ρβ) ψ = toFun (centerCoeff ρβ (coeffOf ψ)) ∧
    ∀ m' : ℝ, 0 ≤ m' → m' ≤ m →
      MemSobolev m' (projMean (withDensityReal ρβ) ψ) ∧
      sobolevNorm m' (projMean (withDensityReal ρβ) ψ) = hsNorm m' (centerCoeff ρβ (coeffOf ψ)) := by
  have hm3 : 1 ≤ m + 3 := by have := ClassicalPart.three_le_mStar d; omega
  have hcm : MemHs (m : ℝ) (coeffOf ψ) := (hsNormSq_coeffOf _ ψ hψ).1
  have hre : IsRealCoeff (coeffOf ψ) := isRealCoeff_coeffOf ψ (integrable_of_cont hψc)
  have hdm : (d : ℝ) / 2 < m := by
    have := mStar_gt d
    have h2 : (mStar d : ℝ) + 2 ≤ m := by exact_mod_cast hm
    linarith
  have hsum := summable_norm_of_memHs _ hdm _ hcm
  have hprob := H.thermal.1
  have hρc := H.cont hm3
  have htf : toFun (coeffOf ψ) = ψ := MFThermalReg.toFun_coeffOf hψc hsum
  refine ⟨?_, fun m' hm'0 hm'm => ?_⟩
  · have := (projMean_toFun hprob hρc hsum hcm hre).1
    rwa [htf] at this
  · have h3 := projMean_toFun hprob hρc hsum (hcm.mono hm'm) hre
    rw [htf] at h3
    rw [h3.1]
    exact h3.2

end FrozenFun


theorem coeff_data (m : ℕ) (hm : mStar d + 2 ≤ m) {ψ : Torus d → ℝ} (hψc : Continuous ψ)
    (hψ : MemSobolev m ψ) :
    MemHs (m : ℝ) (coeffOf ψ) ∧ IsRealCoeff (coeffOf ψ) ∧
      Summable fun k => ‖coeffOf ψ k‖ := by
  have hcm : MemHs (m : ℝ) (coeffOf ψ) := (hsNormSq_coeffOf _ ψ hψ).1
  have hre : IsRealCoeff (coeffOf ψ) := isRealCoeff_coeffOf ψ (integrable_of_cont hψc)
  have hdm : (d : ℝ) / 2 < m := by
    have := mStar_gt d
    have h2 : (mStar d : ℝ) + 2 ≤ m := by exact_mod_cast hm
    linarith
  exact ⟨hcm, hre, summable_norm_of_memHs _ hdm _ hcm⟩

/-- P11b: `S_β(τ)` kills the centering of the datum (`U^{0,τ}1 = 1` by uniqueness) and is a
semigroup (`propagator_semigroup` + time-homogeneity). -/
theorem equilibriumSemigroup_projMean (hd : 1 ≤ d) (s : ℝ) (νm νp c₀ Λ₀ : ℝ) (β : ℝ)
    (V ρβ : Torus d → ℝ) (H : FrozenHyp d s (2 * mStar d + 4) νm νp c₀ Λ₀ β V ρβ)
    (ψ : Torus d → ℝ) (hψ : Continuous ψ) (hψm : MemSobolev (mStar d + 4) ψ) (τ : ℝ)
    (hτ : 0 ≤ τ) :
    equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ
        (projMean (withDensityReal ρβ) ψ) =
      equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ := by
  have h3 := ClassicalPart.three_le_mStar d
  set m : ℕ := mStar d + 4 with hmdef
  have hm : mStar d + 2 ≤ m := by omega
  have hH : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρβ := H.mono (by omega)
  have hψm' : MemSobolev (m : ℝ) ψ := by rw [hmdef]; push_cast; exact hψm
  obtain ⟨hcm, hre, hsum⟩ := coeff_data m hm hψ hψm'
  have hm3 : 1 ≤ m + 3 := by omega
  have hprob := hH.thermal.1
  have hρc := hH.cont hm3
  obtain ⟨e1, -⟩ := S_eq hd m hm hH hψ hψm' hτ
  obtain ⟨hpd1, hpd2⟩ := proj_data m hm hH hψ hψm'
  have hψ'c : Continuous (projMean (withDensityReal ρβ) ψ) := by
    rw [hpd1]; exact continuous_toFun _ (summable_center hsum)
  have hψ'm : MemSobolev (m : ℝ) (projMean (withDensityReal ρβ) ψ) :=
    (hpd2 m (by positivity) le_rfl).1
  obtain ⟨e2, -⟩ := S_eq hd m hm hH hψ'c hψ'm hτ
  have hco : coeffOf (projMean (withDensityReal ρβ) ψ) = centerCoeff ρβ (coeffOf ψ) := by
    rw [hpd1]; exact coeffOf_toFun _ (centerCoeff_isReal hre) (summable_center hsum)
  rw [e1, e2, hco]
  congr 1
  have hA := adjointData_frozen_level m hH 0 (τ + 1) (by linarith)
  exact (center_frozen_center hd hH.hs0 hH.hsd (by omega) hA hprob hρc hcm
    ⟨hτ, by linarith⟩).symm

theorem equilibriumSemigroup_add (hd : 1 ≤ d) (s : ℝ) (νm νp c₀ Λ₀ : ℝ) (β : ℝ)
    (V ρβ : Torus d → ℝ) (H : FrozenHyp d s (2 * mStar d + 4) νm νp c₀ Λ₀ β V ρβ)
    (ψ : Torus d → ℝ) (hψ : Continuous ψ) (hψm : MemSobolev (mStar d + 4) ψ) (v τ : ℝ)
    (hv : 0 ≤ v) (hτ : 0 ≤ τ) :
    equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ v
        (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) =
      equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (v + τ) ψ := by
  have h3 := ClassicalPart.three_le_mStar d
  set m : ℕ := mStar d + 4 with hmdef
  have hm : mStar d + 2 ≤ m := by omega
  have hH : FrozenHyp d s (m + 3) νm νp c₀ Λ₀ β V ρβ := H.mono (by omega)
  have hψm' : MemSobolev (m : ℝ) ψ := by rw [hmdef]; push_cast; exact hψm
  obtain ⟨hcm, hre, hsum⟩ := coeff_data m hm hψ hψm'
  have hm3 : 1 ≤ m + 3 := by omega
  have hprob := hH.thermal.1
  have hρc := hH.cont hm3
  obtain ⟨e1, hS1⟩ := S_eq hd m hm hH hψ hψm' hτ
  obtain ⟨hmemE, hrealE, hsumE⟩ := frozenData hd m hm hH hψ hψm' hτ
  set E := frozenCoeff (mfData d s hH.hs0 hH.hsd V β hH.hβ) ρβ m (coeffOf ψ) τ with hE
  have hψ'c : Continuous (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) := by
    rw [e1]; exact continuous_toFun _ (summable_center hsumE)
  have hψ'm : MemSobolev (m : ℝ) (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) :=
    (hS1 m (by positivity) le_rfl).1
  have hco : coeffOf (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) =
      centerCoeff ρβ E := by
    rw [e1]; exact coeffOf_toFun _ (centerCoeff_isReal hrealE) (summable_center hsumE)
  obtain ⟨e2, -⟩ := S_eq hd m hm hH hψ'c hψ'm hv
  obtain ⟨e3, -⟩ := S_eq hd m hm hH hψ hψm' (add_nonneg hv hτ)
  rw [e2, e3, hco, add_comm v τ]
  congr 1
  have hA := adjointData_frozen_level m hH 0 (τ + v + 1) (by linarith)
  exact (center_frozen_shift hd hH.hs0 hH.hsd (by omega) hA hprob hρc hcm hτ hv
    (by linarith)).symm


/-! ### Part 2 of P11b: centered unit-time smoothing and the two decay statements -/

section Part2

theorem adjointData_frozen' {s νm νp c₀ Λ₀ β : ℝ} {V ρβ : Torus d → ℝ} {n : ℕ} (m : ℕ)
    (hn : m + 3 ≤ n) (H : FrozenHyp d s n νm νp c₀ Λ₀ β V ρβ) (ν₀ T : ℝ) (hT : 0 < T) :
    AdjointData s m (frozenRegime d s c₀) 1 Λ₀ Λ₀ (mfData d s H.hs0 H.hsd V β H.hβ) ν₀ T
      (fun _ => ρβ) :=
  adjointData_frozen_level m (H.mono hn) ν₀ T hT

/-- The frozen path of an `H^j` datum stays in `H^j` (qualitative, every time). -/
theorem frozen_memHs (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (j : ℕ) (hj : 1 ≤ j)
    {νm νp c₀ Λ₀ β : ℝ} {V ρβ : Torus d → ℝ} (H : FrozenHyp d s (j + mStar d) νm νp c₀ Λ₀ β V ρβ)
    {ψc : Coeff d} (hψ : MemHs (j : ℝ) ψc) {τ : ℝ} (hτ : 0 ≤ τ) :
    MemHs (j : ℝ) (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc τ) := by
  have h3 := ClassicalPart.three_le_mStar d
  obtain ⟨L, -, hLb⟩ := exists_frozenCoeff_bound (d := d) (s := s) (m := j) hd hs0 hsd hj
    (frozenRegime d s c₀) 1 Λ₀ Λ₀
  have hA := adjointData_frozen' j (by omega) H 0 (τ + 1) (by linarith)
  exact (hLb _ 0 (τ + 1) ρβ hA ψc hψ τ ⟨hτ, by linarith⟩).1

/-- Finite-time `H^j` bound of the frozen path on `[0,1]`. -/
theorem frozen_fin_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (j : ℕ) (hj : 1 ≤ j)
    (c₀ Λ₀ : ℝ) :
    ∃ L : ℝ, 0 < L ∧ ∀ (νm νp β : ℝ) (V ρβ : Torus d → ℝ)
      (H : FrozenHyp d s (j + mStar d) νm νp c₀ Λ₀ β V ρβ) (ψc : Coeff d), MemHs (j : ℝ) ψc →
      ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 →
        hsNorm (j : ℝ) (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc τ) ≤
          Real.exp L * hsNorm (j : ℝ) ψc := by
  have h3 := ClassicalPart.three_le_mStar d
  obtain ⟨L, hL, hLb⟩ := exists_frozenCoeff_bound (d := d) (s := s) (m := j) hd hs0 hsd hj
    (frozenRegime d s c₀) 1 Λ₀ Λ₀
  refine ⟨L, hL, fun νm νp β V ρβ H ψc hψ τ hτ0 hτ1 => ?_⟩
  have hA := adjointData_frozen' j (by omega) H 0 2 (by norm_num)
  have key := hLb _ 0 2 ρβ hA ψc hψ τ ⟨hτ0, by linarith⟩
  rw [frozenRegime_lambdaM] at key
  refine key.2.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_)
    (MFApriori.hsNorm_nonneg' _ _))
  nlinarith [mul_nonneg hL.le (sub_nonneg.2 hτ1)]

/-- One centered unit-time smoothing step at any level `i ∈ [1, j]`: re-center at time `v`
(`center_frozen_shift`), then apply the uncentered step `frozen_step` to the centered datum. -/
theorem center_step (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (j : ℕ) (hj : 1 ≤ j)
    (νm νp c₀ Λ₀ : ℝ) (i : ℝ) (hi : 1 ≤ i) (hij : i ≤ j) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (β : ℝ) (V ρβ : Torus d → ℝ)
      (H : FrozenHyp d s (j + mStar d) νm νp c₀ Λ₀ β V ρβ) (ψc : Coeff d), MemHs (j : ℝ) ψc →
      ∀ v : ℝ, 0 ≤ v → ∀ σ ∈ Set.Ioc (0 : ℝ) 1,
        hsNorm i (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc (v + σ))) ≤
          K * σ ^ (-(aExp d s / 2)) *
            hsNorm (i - aExp d s)
              (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc v)) := by
  obtain ⟨C, hC0, hC⟩ := frozen_step hd s hs0 hsd j hj νm νp c₀ Λ₀ i hi hij
  refine ⟨2 * (1 + |Λ₀|) * C, mul_nonneg (by positivity) hC0, ?_⟩
  intro β V ρβ H ψc hψ v hv σ hσ
  have h3 := ClassicalPart.three_le_mStar d
  have hρ : IsProbDensity ρβ := H.thermal.1
  have hρc : Continuous ρβ := H.cont (by omega)
  have hΛ : ∀ x, ρβ x ≤ Λ₀ := H.le_Lam
  have hΛ0 : 0 ≤ Λ₀ := (H.hc₀.le.trans (H.hlow 0)).trans (H.le_Lam 0)
  have hσ0 : 0 < σ := hσ.1
  have hσ1 : σ ≤ 1 := hσ.2
  have hi0 : (0 : ℝ) ≤ i := by linarith
  have hFv := frozen_memHs hd s hs0 hsd j hj H hψ hv
  have hcv := (centerCoeff_bound' hρ hρc hΛ (by positivity : (0 : ℝ) ≤ (j : ℝ)) hFv).1
  have hA := adjointData_frozen' j (by omega) H 0 (v + 1) (by linarith)
  have hshift := center_frozen_shift hd hs0 hsd hj hA hρ hρc hψ hv hσ0.le (by linarith)
  have hstep := hC β V ρβ H _ hcv 0 le_rfl σ ⟨hσ0, hσ1⟩
  rw [zero_add, frozenCoeff_zero hj hcv] at hstep
  have hFs := frozen_memHs hd s hs0 hsd j hj H hcv hσ0.le
  have hcs := centerCoeff_bound' hρ hρc hΛ hi0 (hFs.mono hij)
  rw [hshift]
  have hΛ2 : 2 * (1 + Λ₀) ≤ 2 * (1 + |Λ₀|) := by linarith [le_abs_self Λ₀]
  have hZ0 : 0 ≤ C * σ ^ (-(aExp d s / 2)) *
      hsNorm (i - aExp d s) (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc v)) :=
    mul_nonneg (mul_nonneg hC0 (Real.rpow_nonneg hσ0.le _)) (MFApriori.hsNorm_nonneg' _ _)
  calc _ ≤ 2 * (1 + Λ₀) * hsNorm i (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j
            (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc v)) σ) := hcs.2
    _ ≤ 2 * (1 + Λ₀) * (C * σ ^ (-(aExp d s / 2)) *
            hsNorm (i - aExp d s) (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc v))) :=
          mul_le_mul_of_nonneg_left hstep (by linarith)
    _ ≤ 2 * (1 + |Λ₀|) * (C * σ ^ (-(aExp d s / 2)) *
            hsNorm (i - aExp d s) (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc v))) :=
          mul_le_mul_of_nonneg_right hΛ2 hZ0
    _ = _ := by ring

end Part2

section Part2b

/-- The chain of `⌈j/a⌉` unit-time centered smoothing steps (each of length `1/N`) from the
`L²` level to the `H^j` level over unit time, with constant `P` uniform in `β, V, ρβ, ψ`. -/
theorem center_chain (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (j : ℕ)
    (hj : mStar d + 4 ≤ j) (νm νp c₀ Λ₀ : ℝ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ (β : ℝ) (V ρβ : Torus d → ℝ)
      (H : FrozenHyp d s (j + mStar d) νm νp c₀ Λ₀ β V ρβ) (ψc : Coeff d), MemHs (j : ℝ) ψc →
      ∀ v₀ : ℝ, 0 ≤ v₀ →
        hsNorm (j : ℝ) (centerCoeff ρβ
            (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc (v₀ + 1))) ≤
          P * hsNorm 0 (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc v₀)) := by
  have h3 := ClassicalPart.three_le_mStar d
  have hj1 : 1 ≤ j := by omega
  have ha := aExp_spec (d := d) s hsd
  have ha0 : 0 < aExp d s := by linarith [ha.1]
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
  obtain ⟨N, hN1, hNa⟩ : ∃ N : ℕ, 1 ≤ N ∧ (j : ℝ) ≤ (N : ℝ) * aExp d s := by
    refine ⟨⌈(j : ℝ) / aExp d s⌉₊, Nat.ceil_pos.2 (div_pos hjpos ha0), ?_⟩
    have h := Nat.le_ceil ((j : ℝ) / aExp d s)
    rwa [div_le_iff₀ ha0] at h
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = 1 / (N : ℝ) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδdef]; exact div_pos one_pos hNpos
  have hδ1 : δ ≤ 1 := by rw [hδdef, div_le_one hNpos]; exact hN1'
  have hNδ : (N : ℝ) * δ = 1 := by rw [hδdef]; field_simp
  have hstep : ∀ k : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (β : ℝ) (V ρβ : Torus d → ℝ)
      (H : FrozenHyp d s (j + mStar d) νm νp c₀ Λ₀ β V ρβ) (ψc : Coeff d), MemHs (j : ℝ) ψc →
      ∀ v : ℝ, 0 ≤ v → ∀ σ ∈ Set.Ioc (0 : ℝ) 1,
        hsNorm (min (((k : ℝ) + 1) * aExp d s) (j : ℝ))
            (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc (v + σ))) ≤
          K * σ ^ (-(aExp d s / 2)) *
            hsNorm (min (((k : ℝ) + 1) * aExp d s) (j : ℝ) - aExp d s)
              (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc v)) := by
    intro k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have ha1' : (1 : ℝ) ≤ ((k : ℝ) + 1) * aExp d s := by nlinarith [ha.1]
    have hi1 : (1 : ℝ) ≤ min (((k : ℝ) + 1) * aExp d s) (j : ℝ) :=
      le_min ha1' (by exact_mod_cast hj1)
    obtain ⟨K, hK0, hK⟩ := center_step hd s hs0 hsd j hj1 νm νp c₀ Λ₀ _ hi1 (min_le_right _ _)
    exact ⟨K, hK0, hK⟩
  choose K hK0 hKb using hstep
  refine ⟨∏ l ∈ Finset.range N, (K l * δ ^ (-(aExp d s / 2))),
    Finset.prod_nonneg fun l _ => mul_nonneg (hK0 l) (Real.rpow_nonneg hδpos.le _), ?_⟩
  intro β V ρβ H ψc hψ v₀ hv₀
  have hρc : Continuous ρβ := H.cont (by omega)
  have hmem : ∀ v : ℝ, 0 ≤ v → MemHs (j : ℝ)
      (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc v)) := fun v hv =>
    (centerCoeff_bound' H.thermal.1 hρc H.le_Lam (by positivity)
      (frozen_memHs hd s hs0 hsd j hj1 H hψ hv)).1
  have claim : ∀ k : ℕ, k ≤ N → hsNorm (min ((k : ℝ) * aExp d s) (j : ℝ))
      (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc (v₀ + (k : ℝ) * δ))) ≤
      (∏ l ∈ Finset.range k, (K l * δ ^ (-(aExp d s / 2)))) *
        hsNorm 0 (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc v₀)) := by
    intro k
    induction k with
    | zero =>
      intro _
      have e : min (((0 : ℕ) : ℝ) * aExp d s) (j : ℝ) = 0 := by
        rw [Nat.cast_zero, zero_mul]; exact min_eq_left (by positivity)
      rw [e, Nat.cast_zero, zero_mul, add_zero, Finset.prod_range_zero, one_mul]
    | succ k ih =>
      intro hk
      have ihk := ih (by omega)
      have hv : 0 ≤ v₀ + (k : ℝ) * δ := by
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith
      have hs := hKb k β V ρβ H ψc hψ (v₀ + (k : ℝ) * δ) hv δ ⟨hδpos, hδ1⟩
      have hmono : hsNorm (min (((k : ℝ) + 1) * aExp d s) (j : ℝ) - aExp d s)
          (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc (v₀ + (k : ℝ) * δ))) ≤
          hsNorm (min ((k : ℝ) * aExp d s) (j : ℝ))
          (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc (v₀ + (k : ℝ) * δ))) := by
        apply MFApriori.hsNorm_mono_idx
        · apply le_min
          · linarith [min_le_left (((k : ℝ) + 1) * aExp d s) (j : ℝ)]
          · linarith [min_le_right (((k : ℝ) + 1) * aExp d s) (j : ℝ), ha.1]
        · exact (hmem _ hv).mono (min_le_right _ _)
      have e1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      have e2 : v₀ + ((k + 1 : ℕ) : ℝ) * δ = (v₀ + (k : ℝ) * δ) + δ := by push_cast; ring
      rw [e2, e1, Finset.prod_range_succ]
      have hK := hK0 k
      have hpow : 0 ≤ K k * δ ^ (-(aExp d s / 2)) := mul_nonneg hK (Real.rpow_nonneg hδpos.le _)
      calc _ ≤ K k * δ ^ (-(aExp d s / 2)) *
            hsNorm (min (((k : ℝ) + 1) * aExp d s) (j : ℝ) - aExp d s)
              (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc (v₀ + (k : ℝ) * δ))) := hs
        _ ≤ K k * δ ^ (-(aExp d s / 2)) *
            hsNorm (min ((k : ℝ) * aExp d s) (j : ℝ))
              (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc (v₀ + (k : ℝ) * δ))) :=
          mul_le_mul_of_nonneg_left hmono hpow
        _ ≤ K k * δ ^ (-(aExp d s / 2)) * ((∏ l ∈ Finset.range k, (K l * δ ^ (-(aExp d s / 2)))) *
            hsNorm 0 (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j ψc v₀))) :=
          mul_le_mul_of_nonneg_left ihk hpow
        _ = _ := by ring
  have hfin := claim N le_rfl
  have hmin : min ((N : ℝ) * aExp d s) (j : ℝ) = (j : ℝ) := min_eq_right hNa
  have hv1 : v₀ + (N : ℝ) * δ = v₀ + 1 := by rw [hNδ]
  rw [hmin, hv1] at hfin
  exact hfin

/-- The equilibrium semigroup at level `j` (wrapper of `S_eq` for the `H^j` frozen level). -/
theorem S_facts (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (j : ℕ) (hj : mStar d + 4 ≤ j)
    {νm νp c₀ Λ₀ β : ℝ} {V ρβ : Torus d → ℝ} (H : FrozenHyp d s (j + mStar d) νm νp c₀ Λ₀ β V ρβ)
    {ψ : Torus d → ℝ} (hψc : Continuous ψ) (hψ : MemSobolev (j : ℝ) ψ) {t : ℝ} (ht : 0 ≤ t) :
    ∀ m' : ℝ, 0 ≤ m' → m' ≤ j →
      MemSobolev m' (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ t ψ) ∧
      sobolevNorm m' (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ t ψ) =
        hsNorm m' (centerCoeff ρβ
          (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j (coeffOf ψ) t)) := by
  have h3 := ClassicalPart.three_le_mStar d
  exact (S_eq hd j (by omega) (H.mono (by omega)) hψc hψ ht).2

/-- The centered datum `projMean ψ` at level `j` (wrapper of `proj_data`). -/
theorem P_facts (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (j : ℕ) (hj : mStar d + 4 ≤ j)
    {νm νp c₀ Λ₀ β : ℝ} {V ρβ : Torus d → ℝ} (H : FrozenHyp d s (j + mStar d) νm νp c₀ Λ₀ β V ρβ)
    {ψ : Torus d → ℝ} (hψc : Continuous ψ) (hψ : MemSobolev (j : ℝ) ψ) :
    ∀ m' : ℝ, 0 ≤ m' → m' ≤ j →
      MemSobolev m' (projMean (withDensityReal ρβ) ψ) ∧
      sobolevNorm m' (projMean (withDensityReal ρβ) ψ) =
        hsNorm m' (centerCoeff ρβ (coeffOf ψ)) := by
  have h3 := ClassicalPart.three_le_mStar d
  exact (proj_data j (by omega) (H.mono (by omega)) hψc hψ).2

/-- P11b, `H^j` decay of the frozen equilibrium semigroup, at fixed frozen data. -/
theorem exists_frozen_hj_decay (hd : 1 ≤ d) (s : ℝ) (j : ℕ) (hj : mStar d + 4 ≤ j) (νm νp c₀ Λ₀ : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (β : ℝ) (V ρβ : Torus d → ℝ) (H : FrozenHyp d s (j + mStar d) νm νp c₀ Λ₀ β V ρβ),
      ∀ ψ : Torus d → ℝ, Continuous ψ → MemSobolev j ψ → ∀ τ, 0 ≤ τ →
        MemSobolev j (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) ∧
        sobolevNorm j (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) ≤
          C * Real.exp (-c * τ) * sobolevNorm j (projMean (withDensityReal ρβ) ψ) := by
  by_cases hsc : 0 ≤ s ∧ s < d
  swap
  · exact ⟨1, 1, one_pos, one_pos, fun β V ρβ H => (hsc ⟨H.hs0, H.hsd⟩).elim⟩
  obtain ⟨hs0, hsd⟩ := hsc
  have h3 := ClassicalPart.three_le_mStar d
  obtain ⟨P, hP0, hP⟩ := center_chain hd s hs0 hsd j hj νm νp c₀ Λ₀
  obtain ⟨L, hL, hLb⟩ := frozen_fin_bound hd s hs0 hsd j (by omega) c₀ Λ₀
  obtain ⟨CL, cL, hCL, hcL, hL2⟩ := exists_frozen_l2_decay hd s νm νp c₀ Λ₀
  have hK1 : 0 ≤ 2 * (1 + |Λ₀|) * Real.exp L := by positivity
  have hPC : 0 ≤ P * CL := mul_nonneg hP0 hCL.le
  refine ⟨(2 * (1 + |Λ₀|) * Real.exp L + P * CL + 1) * Real.exp cL, cL,
    mul_pos (by linarith) (Real.exp_pos cL), hcL, ?_⟩
  intro β V ρβ H ψ hψc hψ τ hτ
  have hjm : mStar d + 2 ≤ j := by omega
  have hprob : IsProbDensity ρβ := H.thermal.1
  have hρc : Continuous ρβ := H.cont (by omega)
  have hΛ : ∀ x, ρβ x ≤ Λ₀ := H.le_Lam
  have hΛ0 : 0 ≤ Λ₀ := (H.hc₀.le.trans (H.hlow 0)).trans (H.le_Lam 0)
  have hcdat : MemHs (j : ℝ) (coeffOf ψ) := (coeff_data j hjm hψc hψ).1
  have hcc : MemHs (j : ℝ) (centerCoeff ρβ (coeffOf ψ)) :=
    (centerCoeff_bound' hprob hρc hΛ (by positivity) hcdat).1
  have hS := S_facts hd s hs0 hsd j hj H hψc hψ hτ
  have hPf := P_facts hd s hs0 hsd j hj H hψc hψ
  have hR : sobolevNorm (j : ℝ) (projMean (withDensityReal ρβ) ψ) =
      hsNorm (j : ℝ) (centerCoeff ρβ (coeffOf ψ)) := (hPf j (by positivity) le_rfl).2
  have hRnn : 0 ≤ hsNorm (j : ℝ) (centerCoeff ρβ (coeffOf ψ)) := MFApriori.hsNorm_nonneg' _ _
  have hψ2 : MemSobolev ((mStar d : ℝ) + 2) ψ :=
    memSobolev_mono_idx hψ (by exact_mod_cast hjm)
  have hE0 : 0 ≤ Real.exp cL * Real.exp (-cL * τ) := by positivity
  rcases le_total τ 1 with hτ1 | hτ1
  · -- regime `τ ≤ 1`: finite-time bound on the centered datum
    have hA := adjointData_frozen' j (by omega) H 0 (τ + 1) (by linarith)
    have hcenter := center_frozen_center hd hs0 hsd (by omega) hA hprob hρc hcdat
      ⟨hτ, by linarith⟩
    have hFcc := frozen_memHs hd s hs0 hsd j (by omega) H hcc hτ
    have hBd := hLb νm νp β V ρβ H _ hcc τ hτ hτ1
    have hYc := (centerCoeff_bound' hprob hρc hΛ (by positivity) hFcc).2
    have h1 : 2 * (1 + Λ₀) ≤ 2 * (1 + |Λ₀|) := by linarith [le_abs_self Λ₀]
    have hYb : hsNorm (j : ℝ) (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j
        (coeffOf ψ) τ)) ≤ 2 * (1 + |Λ₀|) * Real.exp L * hsNorm (j : ℝ) (centerCoeff ρβ (coeffOf ψ)) := by
      rw [hcenter]
      calc _ ≤ 2 * (1 + Λ₀) * hsNorm (j : ℝ) (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j
            (centerCoeff ρβ (coeffOf ψ)) τ) := hYc
        _ ≤ 2 * (1 + |Λ₀|) * hsNorm (j : ℝ) (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j
            (centerCoeff ρβ (coeffOf ψ)) τ) := mul_le_mul_of_nonneg_right h1 (MFApriori.hsNorm_nonneg' _ _)
        _ ≤ 2 * (1 + |Λ₀|) * (Real.exp L * hsNorm (j : ℝ) (centerCoeff ρβ (coeffOf ψ))) :=
          mul_le_mul_of_nonneg_left hBd (by positivity)
        _ = _ := by ring
    have hEe : 1 ≤ Real.exp cL * Real.exp (-cL * τ) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith [mul_nonneg hcL.le (sub_nonneg.2 hτ1)])
    have hSτ := hS (j : ℝ) (by positivity) le_rfl
    refine ⟨hSτ.1, ?_⟩
    rw [hSτ.2, hR]
    calc _ ≤ 2 * (1 + |Λ₀|) * Real.exp L * hsNorm (j : ℝ) (centerCoeff ρβ (coeffOf ψ)) := hYb
      _ ≤ (2 * (1 + |Λ₀|) * Real.exp L + P * CL + 1) * (Real.exp cL * Real.exp (-cL * τ)) *
            hsNorm (j : ℝ) (centerCoeff ρβ (coeffOf ψ)) := by
          apply mul_le_mul_of_nonneg_right _ hRnn
          have := le_mul_of_one_le_right (by linarith : 0 ≤ 2 * (1 + |Λ₀|) * Real.exp L + P * CL + 1) hEe
          linarith
      _ = _ := by ring
  · -- regime `τ ≥ 1`: one unit-time chain step from the `L²` level at time `τ - 1`
    have hτ0 : 0 ≤ τ - 1 := by linarith
    have hch := hP β V ρβ H (coeffOf ψ) hcdat (τ - 1) hτ0
    rw [sub_add_cancel] at hch
    have hS1 := S_facts hd s hs0 hsd j hj H hψc hψ hτ0
    have hL2' : sobolevNorm 0 (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (τ - 1) ψ) ≤
        CL * Real.exp (-cL * (τ - 1)) * sobolevNorm 2 (projMean (withDensityReal ρβ) ψ) :=
      hL2 β V ρβ (H.mono (by omega)) ψ hψc hψ2 (τ - 1) hτ0
    have hR2 : sobolevNorm 2 (projMean (withDensityReal ρβ) ψ) ≤
        hsNorm (j : ℝ) (centerCoeff ρβ (coeffOf ψ)) := by
      rw [(hPf 2 (by norm_num) (by exact_mod_cast (by omega : 2 ≤ j))).2]
      exact MFApriori.hsNorm_mono_idx (by exact_mod_cast (by omega : 2 ≤ j)) hcc
    have hSτ := hS (j : ℝ) (by positivity) le_rfl
    refine ⟨hSτ.1, ?_⟩
    rw [hSτ.2, hR]
    have hS10 := (hS1 0 le_rfl (by positivity)).2
    calc _ ≤ P * hsNorm 0 (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j
            (coeffOf ψ) (τ - 1))) := hch
      _ = P * sobolevNorm 0 (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (τ - 1) ψ) := by
          rw [hS10]
      _ ≤ P * (CL * Real.exp (-cL * (τ - 1)) * sobolevNorm 2 (projMean (withDensityReal ρβ) ψ)) :=
          mul_le_mul_of_nonneg_left hL2' hP0
      _ ≤ P * (CL * Real.exp (-cL * (τ - 1)) * hsNorm (j : ℝ) (centerCoeff ρβ (coeffOf ψ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hR2 (by positivity)) hP0
      _ = P * CL * (Real.exp cL * Real.exp (-cL * τ)) *
            hsNorm (j : ℝ) (centerCoeff ρβ (coeffOf ψ)) := by
          rw [show -cL * (τ - 1) = cL + (-cL * τ) by ring, Real.exp_add]; ring
      _ ≤ (2 * (1 + |Λ₀|) * Real.exp L + P * CL + 1) * (Real.exp cL * Real.exp (-cL * τ)) *
            hsNorm (j : ℝ) (centerCoeff ρβ (coeffOf ψ)) := by
          apply mul_le_mul_of_nonneg_right _ hRnn
          exact mul_le_mul_of_nonneg_right (by linarith) hE0
      _ = _ := by ring

/-- Frozen paths of `H^m` data stay in `H^m` (general level). -/
theorem frozen_memHs' (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m n : ℕ) (hm : 1 ≤ m)
    (hn : m + 3 ≤ n) {νm νp c₀ Λ₀ β : ℝ} {V ρβ : Torus d → ℝ}
    (H : FrozenHyp d s n νm νp c₀ Λ₀ β V ρβ) {ψc : Coeff d} (hψ : MemHs (m : ℝ) ψc) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    MemHs (m : ℝ) (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ m ψc τ) := by
  obtain ⟨L, -, hLb⟩ := exists_frozenCoeff_bound (d := d) (s := s) (m := m) hd hs0 hsd hm
    (frozenRegime d s c₀) 1 Λ₀ Λ₀
  have hA := adjointData_frozen' m hn H 0 (τ + 1) (by linarith)
  exact (hLb _ 0 (τ + 1) ρβ hA ψc hψ τ ⟨hτ, by linarith⟩).1

theorem meanCoeff_sub' {ρ : Torus d → ℝ} {x y : Coeff d} (hρ : MemHs 0 (coeffOf ρ))
    (hx : MemHs 0 x) (hy : MemHs 0 y) :
    meanCoeff ρ (x - y) = meanCoeff ρ x - meanCoeff ρ y := by
  unfold meanCoeff hsInner
  have hs1 := summable_meanTerm hρ hx
  have hs2 := summable_meanTerm hρ hy
  have h : (∑' k, ((sobWeight 0 k : ℝ) : ℂ) * (coeffOf ρ k * conj ((x - y) k))) =
      (∑' k, ((sobWeight 0 k : ℝ) : ℂ) * (coeffOf ρ k * conj (x k))) -
        ∑' k, ((sobWeight 0 k : ℝ) : ℂ) * (coeffOf ρ k * conj (y k)) := by
    rw [← Summable.tsum_sub hs1 hs2]
    refine tsum_congr fun k => ?_
    simp only [Pi.sub_apply, map_sub]
    ring
  rw [h, Complex.sub_re]

theorem centerCoeff_sub' {ρ : Torus d → ℝ} {x y : Coeff d} (hρ : MemHs 0 (coeffOf ρ))
    (hx : MemHs 0 x) (hy : MemHs 0 y) :
    centerCoeff ρ (x - y) = centerCoeff ρ x - centerCoeff ρ y := by
  have hm := meanCoeff_sub' hρ hx hy
  funext k
  simp only [centerCoeff, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hm]
  push_cast
  ring

theorem norm_coeff_le_hsNorm0 {x : Coeff d} (hx : MemHs 0 x) (k : Lattice d) :
    ‖x k‖ ≤ hsNorm 0 x := by
  have hs : Summable (fun j => sobWeight 0 j * ‖x j‖ ^ 2) := hx
  have h1 : sobWeight 0 k * ‖x k‖ ^ 2 ≤ ∑' j, sobWeight 0 j * ‖x j‖ ^ 2 :=
    hs.le_tsum k (fun j _ => mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))
  rw [sobWeight_zero, one_mul] at h1
  calc ‖x k‖ = Real.sqrt (‖x k‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (∑' j, sobWeight 0 j * ‖x j‖ ^ 2) := Real.sqrt_le_sqrt h1
    _ = hsNorm 0 x := rfl

theorem hsNorm_le_sub_add {m : ℝ} {f g : Coeff d} (hf : MemHs m f) (hg : MemHs m g) :
    hsNorm m f ≤ hsNorm m (f - g) + hsNorm m g := by
  calc hsNorm m f = hsNorm m ((f - g) + g) := by rw [sub_add_cancel]
    _ ≤ hsNorm m (f - g) + hsNorm m g := (hs_add_le m (memHs_sub hf hg) hg).2

theorem isRealCoeff_truncCoeff' {u : Coeff d} (hu : IsRealCoeff u) (n : ℕ) :
    IsRealCoeff (truncCoeff n u) := by
  intro k
  unfold truncCoeff
  by_cases hk : InBox n k
  · have hk' : InBox n (-k) := InBox.neg hk
    rw [if_pos hk', if_pos hk, hu k]
  · have hk' : ¬ InBox n (-k) := fun h => hk (by have := InBox.neg h; rwa [neg_neg] at this)
    rw [if_neg hk', if_neg hk, map_zero]

/-- Smoothing of the equilibrium semigroup for `H^j` data (unit-time steps; constants uniform). -/
theorem frozen_smooth_H (hd : 1 ≤ d) (s : ℝ) (j : ℕ) (hj : mStar d + 4 ≤ j) (νm νp c₀ Λ₀ : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (β : ℝ) (V ρβ : Torus d → ℝ)
      (H : FrozenHyp d s (j + mStar d) νm νp c₀ Λ₀ β V ρβ),
      ∀ ψ : Torus d → ℝ, Continuous ψ → MemSobolev j ψ → ∀ τ : ℝ, 0 < τ →
        MemSobolev j (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) ∧
        sobolevNorm j (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) ≤
          C * (1 + τ ^ (-(aExp d s / 2))) * Real.exp (-c * τ) *
            sobolevNorm ((j : ℝ) - aExp d s) (projMean (withDensityReal ρβ) ψ) := by
  by_cases hsc : 0 ≤ s ∧ s < d
  swap
  · exact ⟨1, 1, one_pos, one_pos, fun β V ρβ H => (hsc ⟨H.hs0, H.hsd⟩).elim⟩
  obtain ⟨hs0, hsd⟩ := hsc
  have h3 := ClassicalPart.three_le_mStar d
  have hjpos : 1 ≤ j := by omega
  obtain ⟨P, hP0, hP⟩ := center_chain hd s hs0 hsd j hj νm νp c₀ Λ₀
  obtain ⟨K, hK0, hK⟩ := center_step hd s hs0 hsd j hjpos νm νp c₀ Λ₀ (j : ℝ)
    (by exact_mod_cast hjpos) le_rfl
  obtain ⟨CL, cL, hCL, hcL, hL2⟩ := exists_frozen_l2_decay hd s νm νp c₀ Λ₀
  have hPC : 0 ≤ P * CL := mul_nonneg hP0 hCL.le
  refine ⟨(K + P * CL + 1) * Real.exp cL, cL, mul_pos (by linarith) (Real.exp_pos cL), hcL, ?_⟩
  intro β V ρβ H ψ hψc hψ τ hτ
  have hjm : mStar d + 2 ≤ j := by omega
  have hprob : IsProbDensity ρβ := H.thermal.1
  have hρc : Continuous ρβ := H.cont (by omega)
  have hΛ : ∀ x, ρβ x ≤ Λ₀ := H.le_Lam
  have hΛ0 : 0 ≤ Λ₀ := (H.hc₀.le.trans (H.hlow 0)).trans (H.le_Lam 0)
  have hcdat : MemHs (j : ℝ) (coeffOf ψ) := (coeff_data j hjm hψc hψ).1
  have hcc : MemHs (j : ℝ) (centerCoeff ρβ (coeffOf ψ)) :=
    (centerCoeff_bound' hprob hρc hΛ (by positivity) hcdat).1
  have hS := S_facts hd s hs0 hsd j hj H hψc hψ hτ.le
  have hPf := P_facts hd s hs0 hsd j hj H hψc hψ
  have hA1 : (2 : ℝ) ≤ (j : ℝ) - aExp d s := by
    have ha := aExp_spec (d := d) s hsd
    have : (mStar d : ℝ) + 4 ≤ j := by exact_mod_cast hj
    have : (3 : ℝ) ≤ mStar d := by exact_mod_cast h3
    linarith [ha.2.1]
  have hA0 : 0 ≤ (j : ℝ) - aExp d s := by linarith
  have hAle : (j : ℝ) - aExp d s ≤ j := by linarith [(aExp_spec (d := d) s hsd).1]
  have hRj : sobolevNorm ((j : ℝ) - aExp d s) (projMean (withDensityReal ρβ) ψ) =
      hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ)) := (hPf _ hA0 hAle).2
  have hcJA : MemHs ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ)) :=
    (centerCoeff_bound' hprob hρc hΛ hA0 (hcdat.mono hAle)).1
  have hR0 : 0 ≤ hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ)) :=
    MFApriori.hsNorm_nonneg' _ _
  have hτ0 : 0 < τ := hτ
  rcases le_total τ 1 with hτ1 | hτ1
  · -- regime `τ ≤ 1`: one centered step from time `0`
    have hstep := hK β V ρβ H (coeffOf ψ) hcdat 0 le_rfl τ ⟨hτ0, hτ1⟩
    rw [zero_add, frozenCoeff_zero hjpos hcdat] at hstep
    have hSτ := hS (j : ℝ) (by positivity) le_rfl
    refine ⟨hSτ.1, ?_⟩
    rw [hSτ.2, hRj]
    have hX : 0 ≤ τ ^ (-(aExp d s / 2)) := Real.rpow_nonneg hτ0.le _
    have hEe : 1 ≤ Real.exp cL * Real.exp (-cL * τ) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith [mul_nonneg hcL.le (sub_nonneg.2 hτ1)])
    calc _ ≤ K * τ ^ (-(aExp d s / 2)) *
          hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ)) := hstep
      _ ≤ (K + P * CL + 1) * (1 + τ ^ (-(aExp d s / 2))) *
            (Real.exp cL * Real.exp (-cL * τ)) *
            hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ)) := by
          apply mul_le_mul_of_nonneg_right _ hR0
          have h1 : K * τ ^ (-(aExp d s / 2)) ≤ (K + P * CL + 1) * (1 + τ ^ (-(aExp d s / 2))) := by
            nlinarith [mul_nonneg hPC (by linarith : (0 : ℝ) ≤ 1 + τ ^ (-(aExp d s / 2))),
              mul_nonneg hK0 hX]
          have h2 : (K + P * CL + 1) * (1 + τ ^ (-(aExp d s / 2))) ≤
              (K + P * CL + 1) * (1 + τ ^ (-(aExp d s / 2))) * (Real.exp cL * Real.exp (-cL * τ)) :=
            le_mul_of_one_le_right (mul_nonneg (by linarith) (by linarith)) hEe
          linarith
      _ = _ := by ring
  · -- regime `τ ≥ 1`: chain from the `L²` level at time `τ - 1`
    have hτ0' : 0 ≤ τ - 1 := by linarith
    have hch := hP β V ρβ H (coeffOf ψ) hcdat (τ - 1) hτ0'
    rw [sub_add_cancel] at hch
    have hS1 := (S_facts hd s hs0 hsd j hj H hψc hψ hτ0' 0 le_rfl (by positivity)).2
    have hψ2 : MemSobolev ((mStar d : ℝ) + 2) ψ :=
      memSobolev_mono_idx hψ (by exact_mod_cast hjm)
    have hL2' : sobolevNorm 0 (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (τ - 1) ψ) ≤
        CL * Real.exp (-cL * (τ - 1)) * sobolevNorm 2 (projMean (withDensityReal ρβ) ψ) :=
      hL2 β V ρβ (H.mono (by omega)) ψ hψc hψ2 (τ - 1) hτ0'
    have hR2 : sobolevNorm 2 (projMean (withDensityReal ρβ) ψ) ≤
        hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ)) := by
      rw [(hPf 2 (by norm_num) (by exact_mod_cast (by omega : 2 ≤ j))).2]
      exact MFApriori.hsNorm_mono_idx hA1 hcJA
    have hSτ := hS (j : ℝ) (by positivity) le_rfl
    have hX : 0 ≤ τ ^ (-(aExp d s / 2)) := Real.rpow_nonneg (by linarith) _
    have hE0 : 0 ≤ Real.exp cL * Real.exp (-cL * τ) := by positivity
    refine ⟨hSτ.1, ?_⟩
    rw [hSτ.2, hRj]
    calc _ ≤ P * hsNorm 0 (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j
            (coeffOf ψ) (τ - 1))) := hch
      _ = P * sobolevNorm 0 (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (τ - 1) ψ) := by
          rw [hS1]
      _ ≤ P * (CL * Real.exp (-cL * (τ - 1)) * sobolevNorm 2 (projMean (withDensityReal ρβ) ψ)) :=
          mul_le_mul_of_nonneg_left hL2' hP0
      _ ≤ P * (CL * Real.exp (-cL * (τ - 1)) *
            hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hR2 (by positivity)) hP0
      _ = P * CL * (Real.exp cL * Real.exp (-cL * τ)) *
            hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ)) := by
          rw [show -cL * (τ - 1) = cL + (-cL * τ) by ring, Real.exp_add]; ring
      _ ≤ (K + P * CL + 1) * (1 + τ ^ (-(aExp d s / 2))) * (Real.exp cL * Real.exp (-cL * τ)) *
            hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ)) := by
          apply mul_le_mul_of_nonneg_right _ hR0
          have h1 : P * CL ≤ (K + P * CL + 1) * (1 + τ ^ (-(aExp d s / 2))) := by
            have h1' : P * CL ≤ K + P * CL + 1 := by linarith
            have h2' : (K + P * CL + 1) ≤ (K + P * CL + 1) * (1 + τ ^ (-(aExp d s / 2))) :=
              le_mul_of_one_le_right (by linarith) (by linarith)
            exact h1'.trans h2'
          exact mul_le_mul_of_nonneg_right h1 hE0
      _ = _ := by ring

theorem isRealCoeff_sub' {u v : Coeff d} (hu : IsRealCoeff u) (hv : IsRealCoeff v) :
    IsRealCoeff (u - v) := fun k => by simp only [Pi.sub_apply, hu k, hv k, map_sub]

theorem hsNormSq_eq_sq' (m : ℝ) (c : Coeff d) : hsNormSq m c = hsNorm m c ^ 2 := by
  have hnn : 0 ≤ hsNormSq m c := tsum_nonneg fun k =>
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _)
  unfold hsNorm
  rw [Real.sq_sqrt hnn]

/-- The centered norm is Lipschitz with respect to the uncentered difference. -/
theorem abs_hsNorm_center_sub_le {ρ : Torus d → ℝ} (hprob : IsProbDensity ρ) (hρc : Continuous ρ)
    {Λ₀ : ℝ} (hΛ : ∀ x, ρ x ≤ Λ₀) {m : ℝ} (hm : 0 ≤ m) {x y : Coeff d} (hx : MemHs m x)
    (hy : MemHs m y) :
    |hsNorm m (centerCoeff ρ x) - hsNorm m (centerCoeff ρ y)| ≤ 2 * (1 + Λ₀) * hsNorm m (x - y) := by
  have hρ0 : MemHs 0 (coeffOf ρ) := MFApriori.memHs_zero_coeffOf_continuous hρc
  have hx0 : MemHs 0 x := hx.mono hm
  have hy0 : MemHs 0 y := hy.mono hm
  have hcx := centerCoeff_bound' hprob hρc hΛ hm hx
  have hcy := centerCoeff_bound' hprob hρc hΛ hm hy
  have hc : centerCoeff ρ x - centerCoeff ρ y = centerCoeff ρ (x - y) :=
    (centerCoeff_sub' hρ0 hx0 hy0).symm
  have e1 := hsNorm_le_sub_add hcx.1 hcy.1
  have e2 := hsNorm_le_sub_add hcy.1 hcx.1
  have e3 := MFApriori.Aux.hsNorm_sub_comm m (centerCoeff ρ y) (centerCoeff ρ x)
  have e5 := (centerCoeff_bound' hprob hρc hΛ hm (memHs_sub hx hy)).2
  have key : |hsNorm m (centerCoeff ρ x) - hsNorm m (centerCoeff ρ y)| ≤
      hsNorm m (centerCoeff ρ x - centerCoeff ρ y) := by
    rw [abs_sub_le_iff]
    constructor <;> linarith
  rw [hc] at key
  linarith

/-- Density: the smoothing estimate for `H^{j-a}` data, from the `H^j` case by truncation,
the `L²` decay of the differences, and Fatou on the finite partial sums of `hsNormSq`. -/
theorem frozen_density (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (j : ℕ)
    (hj : mStar d + 4 ≤ j) (νm νp c₀ Λ₀ C c : ℝ) (hC : 0 ≤ C) {β : ℝ} {V ρβ : Torus d → ℝ}
    (H : FrozenHyp d s (j + mStar d) νm νp c₀ Λ₀ β V ρβ)
    (hsm : ∀ ψ : Torus d → ℝ, Continuous ψ → MemSobolev j ψ → ∀ τ : ℝ, 0 < τ →
        MemSobolev j (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) ∧
        sobolevNorm j (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) ≤
          C * (1 + τ ^ (-(aExp d s / 2))) * Real.exp (-c * τ) *
            sobolevNorm ((j : ℝ) - aExp d s) (projMean (withDensityReal ρβ) ψ))
    (ψ : Torus d → ℝ) (hψc : Continuous ψ) (hψa : MemSobolev ((j : ℝ) - aExp d s) ψ) {τ : ℝ}
    (hτ : 0 < τ) :
    MemSobolev j (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) ∧
    sobolevNorm j (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) ≤
      C * (1 + τ ^ (-(aExp d s / 2))) * Real.exp (-c * τ) *
        sobolevNorm ((j : ℝ) - aExp d s) (projMean (withDensityReal ρβ) ψ) := by
  have h3 := ClassicalPart.three_le_mStar d
  have ha := aExp_spec (d := d) s hsd
  obtain ⟨CL, cL, hCL, hcL, hL2⟩ := exists_frozen_l2_decay hd s νm νp c₀ Λ₀
  have hjR : (mStar d : ℝ) + 4 ≤ (j : ℝ) := by exact_mod_cast hj
  have h3R : (3 : ℝ) ≤ mStar d := by exact_mod_cast h3
  have hmst := mStar_gt d
  have hA2 : aExp d s < 2 := ha.2.1
  have hA1 : 1 ≤ aExp d s := ha.1
  have hm0A : (mStar d : ℝ) + 2 ≤ (j : ℝ) - aExp d s := by linarith
  have hjA0 : (0 : ℝ) ≤ (j : ℝ) - aExp d s := by linarith
  have hjAle : (j : ℝ) - aExp d s ≤ j := by linarith
  have hdjA : (d : ℝ) / 2 < (j : ℝ) - aExp d s := by linarith
  have hdj : (d : ℝ) / 2 < (j : ℝ) := by linarith
  have hdm0 : (d : ℝ) / 2 < (mStar d : ℝ) + 2 := by linarith
  have hprob : IsProbDensity ρβ := H.thermal.1
  have hρc : Continuous ρβ := H.cont (by omega)
  have hΛ : ∀ x, ρβ x ≤ Λ₀ := H.le_Lam
  have hΛ0 : 0 ≤ Λ₀ := (H.hc₀.le.trans (H.hlow 0)).trans (H.le_Lam 0)
  have hρ0 : MemHs 0 (coeffOf ρβ) := MFApriori.memHs_zero_coeffOf_continuous hρc
  have hcA : MemHs ((j : ℝ) - aExp d s) (coeffOf ψ) := (hsNormSq_coeffOf _ ψ hψa).1
  have hsumA : Summable (fun k => ‖coeffOf ψ k‖) := summable_norm_of_memHs _ hdjA _ hcA
  have hreal : IsRealCoeff (coeffOf ψ) := isRealCoeff_coeffOf ψ (integrable_of_cont hψc)
  have hψeq : toFun (coeffOf ψ) = ψ := toFun_coeffOf ψ hψc hsumA
  have hm0ψ : MemSobolev ((mStar d : ℝ) + 2) ψ := memSobolev_mono_idx hψa hm0A
  have hcm0 : MemHs ((mStar d : ℝ) + 2) (coeffOf ψ) := hcA.mono hm0A
  have hS0 : equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ =
      toFun (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (mStar d + 2)
        (coeffOf ψ) τ)) :=
    (S_eq hd (mStar d + 2) (by omega) (H.mono (by omega)) hψc (by push_cast; exact hm0ψ) hτ.le).1
  -- truncations of the coefficients
  have hcn_mem : ∀ n : ℕ, MemHs (j : ℝ) (truncCoeff n (coeffOf ψ)) := fun n =>
    MFLocal.memHs_truncCoeff _ n _
  have hcn_real : ∀ n : ℕ, IsRealCoeff (truncCoeff n (coeffOf ψ)) := fun n =>
    isRealCoeff_truncCoeff' hreal n
  have hcn_sum : ∀ n : ℕ, Summable (fun k => ‖truncCoeff n (coeffOf ψ) k‖) := fun n =>
    summable_norm_of_memHs _ hdj _ (hcn_mem n)
  have hψn_cont : ∀ n : ℕ, Continuous (toFun (truncCoeff n (coeffOf ψ))) := fun n =>
    continuous_toFun _ (hcn_sum n)
  have hψn_mem : ∀ n : ℕ, MemSobolev (j : ℝ) (toFun (truncCoeff n (coeffOf ψ))) := fun n =>
    (ClassicalPart.memSobolev_toFun (hcn_sum n) (hcn_mem n) (hcn_real n)).1
  have hψn_coeff : ∀ n : ℕ, coeffOf (toFun (truncCoeff n (coeffOf ψ))) =
      truncCoeff n (coeffOf ψ) := fun n => coeffOf_toFun _ (hcn_real n) (hcn_sum n)
  have hcn0 : ∀ n : ℕ, MemHs ((mStar d + 2 : ℕ) : ℝ) (truncCoeff n (coeffOf ψ)) := fun n =>
    (hcn_mem n).mono (by push_cast; linarith)
  have hcm0' : MemHs ((mStar d + 2 : ℕ) : ℝ) (coeffOf ψ) := by push_cast; exact hcm0
  -- adjoint data at the two levels
  have hA0 := adjointData_frozen' (mStar d + 2) (by omega) H 0 (τ + 1) (by linarith)
  have hAj := adjointData_frozen' j (by omega) H 0 (τ + 1) (by linarith)
  have hτT : τ ∈ Set.Icc (0 : ℝ) (τ + 1) := ⟨hτ.le, by linarith⟩
  have hlev : ∀ n : ℕ, frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (mStar d + 2)
      (truncCoeff n (coeffOf ψ)) τ =
      frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j (truncCoeff n (coeffOf ψ)) τ :=
    fun n => frozenCoeff_level hd hs0 hsd (by omega) (by omega) hA0 hAj (hcn_mem n) hτT
  have hWmem : ∀ n : ℕ, MemHs 0 (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ)
      ρβ (mStar d + 2) (truncCoeff n (coeffOf ψ) - coeffOf ψ) τ)) := by
    intro n
    have hm := frozen_memHs' hd s hs0 hsd (mStar d + 2) (j + mStar d) (by omega) (by omega) H
      (memHs_sub (hcn0 n) hcm0') hτ.le
    exact (centerCoeff_bound' hprob hρc hΛ (by positivity) (hm.mono (by positivity))).1
  have hdm0' : (d : ℝ) / 2 < ((mStar d + 2 : ℕ) : ℝ) := by push_cast; linarith
  have hWid : ∀ n : ℕ, centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (mStar d + 2)
      (truncCoeff n (coeffOf ψ)) τ) - centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ)
      ρβ (mStar d + 2) (coeffOf ψ) τ) = centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ)
      ρβ (mStar d + 2) (truncCoeff n (coeffOf ψ) - coeffOf ψ) τ) := by
    intro n
    have hsub := frozenCoeff_sub hd s hs0 hsd (mStar d + 2) (by omega) (frozenRegime d s c₀) 1 Λ₀ Λ₀
      (mfData d s H.hs0 H.hsd V β H.hβ) 0 (τ + 1) ρβ hA0 (truncCoeff n (coeffOf ψ)) (coeffOf ψ)
      (hcn0 n) hcm0' hτT
    have hF0t : MemHs 0 (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (mStar d + 2)
        (truncCoeff n (coeffOf ψ)) τ) :=
      (frozen_memHs' hd s hs0 hsd (mStar d + 2) (j + mStar d) (by omega) (by omega) H (hcn0 n)
        hτ.le).mono (by positivity)
    have hF0c : MemHs 0 (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (mStar d + 2)
        (coeffOf ψ) τ) :=
      (frozen_memHs' hd s hs0 hsd (mStar d + 2) (j + mStar d) (by omega) (by omega) H hcm0'
        hτ.le).mono (by positivity)
    rw [hsub, centerCoeff_sub' hρ0 hF0t hF0c]
  have hWbd : ∀ n : ℕ, hsNorm 0 (centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ
      (mStar d + 2) (truncCoeff n (coeffOf ψ) - coeffOf ψ) τ)) ≤
      CL * Real.exp (-cL * τ) * (2 * (1 + Λ₀) * hsNorm ((j : ℝ) - aExp d s)
        (coeffOf ψ - truncCoeff n (coeffOf ψ))) := by
    intro n
    obtain ⟨x, hx⟩ : ∃ x : Coeff d, x = truncCoeff n (coeffOf ψ) - coeffOf ψ := ⟨_, rfl⟩
    rw [← hx]
    have hxm0 : MemHs ((mStar d + 2 : ℕ) : ℝ) x := by
      rw [hx]; exact memHs_sub (hcn0 n) hcm0'
    have hxreal : IsRealCoeff x := by rw [hx]; exact isRealCoeff_sub' (hcn_real n) hreal
    have hxsum : Summable (fun k => ‖x k‖) := summable_norm_of_memHs _ hdm0' _ hxm0
    have hgc : Continuous (toFun x) := continuous_toFun x hxsum
    have hgm : MemSobolev ((mStar d + 2 : ℕ) : ℝ) (toFun x) :=
      (ClassicalPart.memSobolev_toFun hxsum hxm0 hxreal).1
    have hgcoeff : coeffOf (toFun x) = x := coeffOf_toFun x hxreal hxsum
    have hSg := (S_eq hd (mStar d + 2) (by omega) (H.mono (by omega)) hgc hgm hτ.le).2 0 le_rfl
      (by positivity)
    rw [hgcoeff] at hSg
    have hgm' : MemSobolev ((mStar d : ℝ) + 2) (toFun x) := by push_cast at hgm; exact hgm
    have hL := hL2 β V ρβ (H.mono (by omega)) (toFun x) hgc hgm' τ hτ.le
    have hx2 : MemHs 2 x := hxm0.mono (by push_cast; linarith)
    obtain ⟨hpj, -, hpn⟩ := projMean_toFun hprob hρc hxsum hx2 hxreal
    rw [hpj, hpn, hSg.2] at hL
    have hcc2 := (centerCoeff_bound' hprob hρc hΛ (by norm_num : (0 : ℝ) ≤ 2) hx2).2
    have hxA : MemHs ((j : ℝ) - aExp d s) x := by
      rw [hx]; exact memHs_sub (MFLocal.memHs_truncCoeff _ n _) hcA
    have hmono2 : hsNorm 2 x ≤ hsNorm ((j : ℝ) - aExp d s) x :=
      MFApriori.hsNorm_mono_idx (by linarith) hxA
    have hsw : hsNorm ((j : ℝ) - aExp d s) x =
        hsNorm ((j : ℝ) - aExp d s) (coeffOf ψ - truncCoeff n (coeffOf ψ)) := by
      rw [hx]; exact MFApriori.Aux.hsNorm_sub_comm _ _ _
    calc _ ≤ CL * Real.exp (-cL * τ) * hsNorm 2 (centerCoeff ρβ x) := hL
      _ ≤ CL * Real.exp (-cL * τ) * (2 * (1 + Λ₀) * hsNorm 2 x) :=
          mul_le_mul_of_nonneg_left hcc2 (by positivity)
      _ ≤ CL * Real.exp (-cL * τ) * (2 * (1 + Λ₀) * hsNorm ((j : ℝ) - aExp d s) x) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono2 (by linarith)) (by positivity)
      _ = _ := by rw [hsw]
  have hδn : Tendsto (fun n : ℕ => CL * Real.exp (-cL * τ) * (2 * (1 + Λ₀) *
      hsNorm ((j : ℝ) - aExp d s) (coeffOf ψ - truncCoeff n (coeffOf ψ)))) atTop (𝓝 0) := by
    have h := (truncCoeff_tendsto ((j : ℝ) - aExp d s) (coeffOf ψ) hcA).2
    simpa using (h.const_mul (2 * (1 + Λ₀))).const_mul (CL * Real.exp (-cL * τ))
  have hPn : ∀ n : ℕ, sobolevNorm ((j : ℝ) - aExp d s)
      (projMean (withDensityReal ρβ) (toFun (truncCoeff n (coeffOf ψ)))) =
      hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (truncCoeff n (coeffOf ψ))) := by
    intro n
    have h := (P_facts hd s hs0 hsd j hj H (hψn_cont n) (hψn_mem n) ((j : ℝ) - aExp d s) hjA0
      hjAle).2
    rw [hψn_coeff n] at h
    exact h
  have hsmooth : ∀ n : ℕ, sobolevNorm (j : ℝ)
      (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ (toFun (truncCoeff n (coeffOf ψ)))) ≤
      C * (1 + τ ^ (-(aExp d s / 2))) * Real.exp (-c * τ) *
        hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (truncCoeff n (coeffOf ψ))) := by
    intro n
    have h := (hsm _ (hψn_cont n) (hψn_mem n) τ hτ).2
    rw [hPn n] at h
    exact h
  obtain ⟨un, hun_def⟩ : ∃ un : ℕ → Coeff d, un = fun n =>
      centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ j (truncCoeff n (coeffOf ψ)) τ) :=
    ⟨_, rfl⟩
  obtain ⟨u, hu_def⟩ : ∃ u : Coeff d, u = centerCoeff ρβ
      (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ (mStar d + 2) (coeffOf ψ) τ) := ⟨_, rfl⟩
  have hunb : ∀ n : ℕ, hsNorm (j : ℝ) (un n) ≤ C * (1 + τ ^ (-(aExp d s / 2))) * Real.exp (-c * τ) *
      hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (truncCoeff n (coeffOf ψ))) := by
    intro n
    have h1 := (S_facts hd s hs0 hsd j hj H (hψn_cont n) (hψn_mem n) hτ.le (j : ℝ)
      (by positivity) le_rfl).2
    rw [hψn_coeff n] at h1
    rw [hun_def, ← h1]
    exact hsmooth n
  have hunmem : ∀ n : ℕ, MemHs (j : ℝ) (un n) := by
    intro n
    have hm := frozen_memHs' hd s hs0 hsd j (j + mStar d) (by omega) (by omega) H (hcn_mem n) hτ.le
    rw [hun_def]
    exact (centerCoeff_bound' hprob hρc hΛ (by positivity) hm).1
  have hu_eq : ∀ n : ℕ, un n - u = centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ
      (mStar d + 2) (truncCoeff n (coeffOf ψ) - coeffOf ψ) τ) := by
    intro n
    simp only [hun_def, hu_def]
    rw [← hlev n]
    exact hWid n
  have hcoordTend : ∀ k : Lattice d, Tendsto (fun n => un n k) atTop (𝓝 (u k)) := by
    intro k
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hδn
    have hk : un n k - u k = centerCoeff ρβ (frozenCoeff (mfData d s H.hs0 H.hsd V β H.hβ) ρβ
        (mStar d + 2) (truncCoeff n (coeffOf ψ) - coeffOf ψ) τ) k := by
      rw [← hu_eq n]; rfl
    rw [hk]
    exact (norm_coeff_le_hsNorm0 (hWmem n) k).trans (hWbd n)
  have hsumF : ∀ F : Finset (Lattice d), Tendsto (fun n => ∑ k ∈ F, sobWeight (j : ℝ) k * ‖un n k‖ ^ 2)
      atTop (𝓝 (∑ k ∈ F, sobWeight (j : ℝ) k * ‖u k‖ ^ 2)) := by
    intro F
    apply tendsto_finset_sum
    intro k _
    exact ((hcoordTend k).norm.pow 2).const_mul (sobWeight (j : ℝ) k)
  have hRtend : Tendsto (fun n => hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (truncCoeff n (coeffOf ψ))))
      atTop (𝓝 (hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ)))) := by
    have hb2 := (truncCoeff_tendsto ((j : ℝ) - aExp d s) (coeffOf ψ) hcA).2
    have hg : Tendsto (fun n : ℕ => 2 * (1 + Λ₀) * hsNorm ((j : ℝ) - aExp d s)
        (coeffOf ψ - truncCoeff n (coeffOf ψ))) atTop (𝓝 0) := by
      simpa using hb2.const_mul (2 * (1 + Λ₀))
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hg
    rw [Real.norm_eq_abs]
    have h := abs_hsNorm_center_sub_le hprob hρc hΛ hjA0
      (MFLocal.memHs_truncCoeff ((j : ℝ) - aExp d s) n (coeffOf ψ)) hcA
    rw [MFApriori.Aux.hsNorm_sub_comm] at h
    exact h
  have hRpow : Tendsto (fun n => (C * (1 + τ ^ (-(aExp d s / 2))) * Real.exp (-c * τ) *
      hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (truncCoeff n (coeffOf ψ)))) ^ 2) atTop
      (𝓝 ((C * (1 + τ ^ (-(aExp d s / 2))) * Real.exp (-c * τ) *
        hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ))) ^ 2)) :=
    (hRtend.const_mul (C * (1 + τ ^ (-(aExp d s / 2))) * Real.exp (-c * τ))).pow 2
  have hfin : ∀ F : Finset (Lattice d), ∑ k ∈ F, sobWeight (j : ℝ) k * ‖u k‖ ^ 2 ≤
      (C * (1 + τ ^ (-(aExp d s / 2))) * Real.exp (-c * τ) *
        hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ))) ^ 2 := by
    intro F
    refine le_of_tendsto_of_tendsto (hsumF F) hRpow (Filter.Eventually.of_forall fun n => ?_)
    have hsn : ∑ k ∈ F, sobWeight (j : ℝ) k * ‖un n k‖ ^ 2 ≤ hsNorm (j : ℝ) (un n) ^ 2 := by
      calc _ ≤ ∑' k, sobWeight (j : ℝ) k * ‖un n k‖ ^ 2 :=
            (hunmem n).sum_le_tsum F (fun k _ => mul_nonneg (Real.rpow_nonneg (by positivity) _)
              (sq_nonneg _))
        _ = hsNorm (j : ℝ) (un n) ^ 2 := hsNormSq_eq_sq' _ _
    exact hsn.trans (pow_le_pow_left₀ (MFApriori.hsNorm_nonneg' _ _) (hunb n) 2)
  have hnn_all : (0 : Lattice d → ℝ) ≤ fun k => sobWeight (j : ℝ) k * ‖u k‖ ^ 2 :=
    fun k => mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _)
  have hsumAll : Summable (fun k => sobWeight (j : ℝ) k * ‖u k‖ ^ 2) :=
    summable_of_sum_le hnn_all hfin
  have htsum : ∑' k, sobWeight (j : ℝ) k * ‖u k‖ ^ 2 ≤
      (C * (1 + τ ^ (-(aExp d s / 2))) * Real.exp (-c * τ) *
        hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ))) ^ 2 :=
    Real.tsum_le_of_sum_le hnn_all hfin
  have hu_mem : MemHs (j : ℝ) u := hsumAll
  have hX0 : 0 ≤ 1 + τ ^ (-(aExp d s / 2)) := by
    have := Real.rpow_nonneg hτ.le (-(aExp d s / 2)); linarith
  have hMR0 : 0 ≤ C * (1 + τ ^ (-(aExp d s / 2))) * Real.exp (-c * τ) *
      hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC hX0) (Real.exp_pos _).le) (MFApriori.hsNorm_nonneg' _ _)
  have hnorm_u : hsNorm (j : ℝ) u ≤ C * (1 + τ ^ (-(aExp d s / 2))) * Real.exp (-c * τ) *
      hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ)) := by
    have h1 : hsNorm (j : ℝ) u = Real.sqrt (∑' k, sobWeight (j : ℝ) k * ‖u k‖ ^ 2) := rfl
    rw [h1]
    calc _ ≤ Real.sqrt ((C * (1 + τ ^ (-(aExp d s / 2))) * Real.exp (-c * τ) *
          hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ))) ^ 2) := Real.sqrt_le_sqrt htsum
      _ = _ := Real.sqrt_sq hMR0
  have hSu : equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ = toFun u := by
    rw [hS0, hu_def]
  have hreal_u : IsRealCoeff u := by
    rw [hu_def]
    exact centerCoeff_isReal (frozenCoeff_real hd hs0 hsd (by omega) hA0 hcm0' hreal hτT)
  have hsum_u : Summable (fun k => ‖u k‖) := summable_norm_of_memHs _ hdj _ hu_mem
  have hMemTo := ClassicalPart.memSobolev_toFun hsum_u hu_mem hreal_u
  have hPR : sobolevNorm ((j : ℝ) - aExp d s) (projMean (withDensityReal ρβ) ψ) =
      hsNorm ((j : ℝ) - aExp d s) (centerCoeff ρβ (coeffOf ψ)) := by
    have hpm : projMean (withDensityReal ρβ) ψ = toFun (centerCoeff ρβ (coeffOf ψ)) := by
      conv_lhs => rw [← hψeq]
      exact (projMean_toFun hprob hρc hsumA hcA hreal).1
    rw [hpm]
    exact (projMean_toFun hprob hρc hsumA hcA hreal).2.2
  rw [hSu]
  refine ⟨hMemTo.1, ?_⟩
  rw [hMemTo.2, hPR]
  exact hnorm_u

/-- P11b, smoothing of the frozen semigroup from `H^{j-a}` data (`C:eq:S-smoothing` at the
endpoint `a = aExp d s`). -/
theorem exists_frozen_smoothing (hd : 1 ≤ d) (s : ℝ) (j : ℕ) (hj : mStar d + 4 ≤ j) (νm νp c₀ Λ₀ : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (β : ℝ) (V ρβ : Torus d → ℝ) (H : FrozenHyp d s (j + mStar d) νm νp c₀ Λ₀ β V ρβ),
      ∀ ψ : Torus d → ℝ, Continuous ψ → MemSobolev ((j : ℝ) - aExp d s) ψ → ∀ τ, 0 < τ →
        MemSobolev j (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) ∧
        sobolevNorm j (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) ≤
          C * (1 + τ ^ (-(aExp d s / 2))) * Real.exp (-c * τ) * sobolevNorm ((j : ℝ) - aExp d s) (projMean (withDensityReal ρβ) ψ) := by
  by_cases hsc : 0 ≤ s ∧ s < d
  swap
  · exact ⟨1, 1, one_pos, one_pos, fun β V ρβ H => (hsc ⟨H.hs0, H.hsd⟩).elim⟩
  obtain ⟨hs0, hsd⟩ := hsc
  obtain ⟨C, c, hC, hc, hsm⟩ := frozen_smooth_H hd s j hj νm νp c₀ Λ₀
  refine ⟨C, c, hC, hc, fun β V ρβ H ψ hψc hψa τ hτ => frozen_density hd s hs0 hsd j hj νm νp c₀ Λ₀
    C c hC.le H (hsm β V ρβ H) ψ hψc hψa hτ⟩

end Part2b

end HRS.PDE.MFAdjoint
