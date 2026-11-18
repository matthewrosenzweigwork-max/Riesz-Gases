import HRS.Commutator.Whole.PositiveAux3

/-!
# Helpers for `Positive.lean` (packet `CMX-POS`), part D

The Fourier-side functions `f1Hat`, `g1Hat` and the coercivity bounds.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

lemma re_phiHat (η : Euc d) : (𝓕 (fun x : Euc d => ((phi x : ℝ) : ℂ)) η).re = phiHatR d ‖η‖ := by
  rw [fourier_phi]; simp

lemma alphaE_two_mul (d : ℕ) (s : ℝ) : 2 * alphaE d s = (d : ℝ) - s := by
  unfold alphaE; ring

lemma g1Hat_eq (ξ : Euc d) : g1Hat s ξ =
    cPhi d s * ∫ t in Set.Ioi (1:ℝ), t ^ ((d : ℝ) - s - 1) * phiHatR d (t * ‖ξ‖) := by
  unfold g1Hat
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have ht0 : 0 < t := lt_trans one_pos ht
  rw [re_phiHat, norm_smul, Real.norm_eq_abs, abs_of_pos ht0, alphaE_two_mul, Real.rpow_sub_one ht0.ne']
  ring

lemma f1Hat_eq (ξ : Euc d) : f1Hat s ξ =
    cPhi d s * ∫ t in Set.Ioc (0:ℝ) 1, t ^ ((d : ℝ) - s - 1) * phiHatR d (t * ‖ξ‖) := by
  unfold f1Hat
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
  have ht0 : 0 < t := ht.1
  rw [re_phiHat, norm_smul, Real.norm_eq_abs, abs_of_pos ht0, alphaE_two_mul, Real.rpow_sub_one ht0.ne']
  ring

lemma phiHatR_le_zero (r : ℝ) : phiHatR d |r| ≤ phiHatR d 0 :=
  phiHatR_anti le_rfl (abs_nonneg r)

lemma phiHatR_even (r : ℝ) : phiHatR d (-r) = phiHatR d r := by
  unfold phiHatR gmixHat
  simp only [neg_sq]

/-- radial integrability of `φ̂`. -/
lemma integrableOn_phiHat_pow (hd : 0 < d) :
    IntegrableOn (fun y : ℝ => y ^ (d - 1) * phiHatR d y) (Set.Ioi 0) := by
  have : Nontrivial (Euc d) := by
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  have h := (integrable_fun_norm_addHaar (volume : Measure (Euc d)) (f := fun y : ℝ => phiHatR d y)).1
    integrable_phiHat
  simpa [smul_eq_mul] using h

lemma integrableOn_phiHat_scaled (hd : 0 < d) {a m : ℝ} (ha : 0 < a) (hm : m ≤ (d : ℝ) - 1) :
    IntegrableOn (fun t : ℝ => t ^ m * phiHatR d (t * a)) (Set.Ioi 1) := by
  have h1 := integrableOn_phiHat_pow (d := d) hd
  have h2 : IntegrableOn (fun y : ℝ => y ^ ((d : ℝ) - 1) * phiHatR d y) (Set.Ioi 0) := by
    refine h1.congr_fun (fun y hy => ?_) measurableSet_Ioi
    dsimp only
    rw [← Real.rpow_natCast, Nat.cast_sub hd]; simp
  have h3 : IntegrableOn (fun t : ℝ => (a * t) ^ ((d : ℝ) - 1) * phiHatR d (a * t)) (Set.Ioi 0) := by
    have h2' : IntegrableOn (fun y : ℝ => y ^ ((d : ℝ) - 1) * phiHatR d y) (Set.Ioi (a * 0)) := by
      rwa [mul_zero]
    have := (integrableOn_Ioi_comp_mul_left_iff (fun y : ℝ => y ^ ((d : ℝ) - 1) * phiHatR d y) 0 ha).2 h2'
    simpa using this
  have h4 : IntegrableOn (fun t : ℝ => (a ^ ((d : ℝ) - 1))⁻¹ * ((a * t) ^ ((d : ℝ) - 1) * phiHatR d (a * t)))
      (Set.Ioi 1) := (h3.mono_set (Set.Ioi_subset_Ioi zero_le_one)).const_mul _
  refine Integrable.mono' h4 ?_ ?_
  · have : Measurable (fun t : ℝ => t ^ m * phiHatR d (t * a)) := by
      have := continuous_phiHatR (d := d)
      fun_prop
    exact this.aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (1:ℝ)))] with t ht
    have ht1 : 1 < t := ht
    have ht0 : 0 < t := lt_trans one_pos ht1
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _) (phiHatR_pos _).le)]
    rw [Real.mul_rpow ha.le ht0.le, mul_comm t a]
    have hpa : 0 < a ^ ((d : ℝ) - 1) := Real.rpow_pos_of_pos ha _
    have : t ^ m ≤ t ^ ((d : ℝ) - 1) := Real.rpow_le_rpow_of_exponent_le ht1.le hm
    have hP := phiHatR_pos (d := d) (a * t)
    calc t ^ m * phiHatR d (a * t) ≤ t ^ ((d : ℝ) - 1) * phiHatR d (a * t) :=
          mul_le_mul_of_nonneg_right this hP.le
      _ = (a ^ ((d : ℝ) - 1))⁻¹ * (a ^ ((d : ℝ) - 1) * t ^ ((d : ℝ) - 1) * phiHatR d (a * t)) := by
          field_simp


lemma g1Hat_nonneg (hs0 : 0 ≤ s) (hs2 : s < 2 * (d : ℝ) + 4) (ξ : Euc d) : 0 ≤ g1Hat s ξ := by
  rw [g1Hat_eq]
  refine mul_nonneg (cPhi_pos d hs0 hs2).le (setIntegral_nonneg measurableSet_Ioi (fun t ht => ?_))
  have : 0 < t := lt_trans one_pos ht
  exact mul_nonneg (Real.rpow_nonneg this.le _) (phiHatR_pos _).le

lemma f1Hat_nonneg (hs0 : 0 ≤ s) (hs2 : s < 2 * (d : ℝ) + 4) (ξ : Euc d) : 0 ≤ f1Hat s ξ := by
  rw [f1Hat_eq]
  refine mul_nonneg (cPhi_pos d hs0 hs2).le (setIntegral_nonneg measurableSet_Ioc (fun t ht => ?_))
  exact mul_nonneg (Real.rpow_nonneg ht.1.le _) (phiHatR_pos _).le

theorem lowcoercive_aux (hd : 0 < d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {R : ℝ} (hR : 0 < R) :
    ∃ cR : ℝ, 0 < cR ∧ ∀ ξ : Euc d, ξ ≠ 0 → ‖ξ‖ ≤ R →
      cR * ‖ξ‖ ^ (-(2 * alphaE d s)) ≤ g1Hat s ξ := by
  have hs2 : s < 2 * (d : ℝ) + 4 := by linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  have hcp := cPhi_pos d hs0 hs2
  set m : ℝ := (d : ℝ) - s - 1 with hm
  have hm0 : 0 < m := by linarith
  refine ⟨cPhi d s * R ^ m * phiHatR d (R + 1), by have := phiHatR_pos (d := d) (R + 1); positivity,
    fun ξ hξ hξR => ?_⟩
  have ha : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  set a := ‖ξ‖ with hadef
  rw [g1Hat_eq]
  have h1 : 1 ≤ R / a := by rw [le_div_iff₀ ha]; linarith
  have hJ : Set.Ioc (R / a) ((R + 1) / a) ⊆ Set.Ioi 1 :=
    fun t ht => lt_of_le_of_lt h1 ht.1
  have hint := integrableOn_phiHat_scaled (d := d) hd ha (m := m) (by linarith)
  have hint' : IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - s - 1) * phiHatR d (t * a)) (Set.Ioi 1) := hint
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (1:ℝ))] (fun t : ℝ => t ^ ((d : ℝ) - s - 1) * phiHatR d (t * a)) := by
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (1:ℝ)))] with t ht
    have : 0 < t := lt_trans one_pos ht
    exact mul_nonneg (Real.rpow_nonneg this.le _) (phiHatR_pos _).le
  have h2 : ∫ t in Set.Ioc (R / a) ((R + 1) / a), t ^ ((d : ℝ) - s - 1) * phiHatR d (t * a) ≤
      ∫ t in Set.Ioi (1:ℝ), t ^ ((d : ℝ) - s - 1) * phiHatR d (t * a) :=
    setIntegral_mono_set hint' hnn (Filter.Eventually.of_forall hJ)
  have hlen : (R + 1) / a - R / a = 1 / a := by field_simp; ring
  have h3 : (R / a) ^ m * phiHatR d (R + 1) * (1 / a) ≤
      ∫ t in Set.Ioc (R / a) ((R + 1) / a), t ^ ((d : ℝ) - s - 1) * phiHatR d (t * a) := by
    have hcint : IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - s - 1) * phiHatR d (t * a))
        (Set.Ioc (R / a) ((R + 1) / a)) := hint'.mono_set hJ
    have : ∫ t in Set.Ioc (R / a) ((R + 1) / a), (R / a) ^ m * phiHatR d (R + 1) =
        (R / a) ^ m * phiHatR d (R + 1) * (1 / a) := by
      rw [setIntegral_const, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by
        rw [hlen]; positivity), hlen, smul_eq_mul]
      ring
    rw [← this]
    refine setIntegral_mono_on (integrableOn_const (by simp)) hcint measurableSet_Ioc (fun t ht => ?_)
    have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht.1.le
    have hta : t * a ≤ R + 1 := by
      have := ht.2
      rw [le_div_iff₀ ha] at this; exact this
    have e1 : (R / a) ^ m ≤ t ^ m := Real.rpow_le_rpow (by positivity) ht.1.le hm0.le
    have e2 : phiHatR d (R + 1) ≤ phiHatR d (t * a) :=
      phiHatR_anti (by positivity) hta
    exact mul_le_mul e1 e2 (phiHatR_pos _).le (Real.rpow_nonneg ht0.le _)
  have h4 : cPhi d s * R ^ m * phiHatR d (R + 1) * a ^ (-(2 * alphaE d s)) =
      cPhi d s * ((R / a) ^ m * phiHatR d (R + 1) * (1 / a)) := by
    rw [alphaE_two_mul, Real.div_rpow hR.le ha.le]
    have : a ^ (-((d : ℝ) - s)) = (a ^ m)⁻¹ * a⁻¹ := by
      have e : -((d : ℝ) - s) = -m + -1 := by rw [hm]; ring
      rw [e, Real.rpow_add ha, Real.rpow_neg_one, Real.rpow_neg ha.le]
    rw [this]
    field_simp
  rw [h4]
  exact mul_le_mul_of_nonneg_left (h3.trans h2) hcp.le


theorem shortcoercive_aux (hd : 0 < d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ ξ : Euc d,
      c * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-(alphaE d s)) ≤ f1Hat s ξ := by
  have hs2 : s < 2 * (d : ℝ) + 4 := by linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  have hcp := cPhi_pos d hs0 hs2
  set m : ℝ := (d : ℝ) - s - 1 with hm
  have hm0 : 0 < m := by linarith
  have hα : 0 < alphaE d s := by unfold alphaE; linarith
  refine ⟨cPhi d s * phiHatR d 1 * (2:ℝ) ^ (-(alphaE d s)) / ((d : ℝ) - s),
    by have := phiHatR_pos (d := d) 1; have : 0 < (d : ℝ) - s := by linarith
       positivity, fun ξ => ?_⟩
  set a := ‖ξ‖ with hadef
  have ha : 0 ≤ a := norm_nonneg _
  rw [f1Hat_eq]
  set τ := 1 / (1 + a) with hτ
  have hτ0 : 0 < τ := by positivity
  have hτ1 : τ ≤ 1 := by rw [hτ, div_le_one (by positivity)]; linarith
  have hint0 : IntegrableOn (fun t : ℝ => t ^ m) (Set.Ioc 0 1) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := m) (by linarith))
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 this
  have hint : IntegrableOn (fun t : ℝ => t ^ m * phiHatR d (t * a)) (Set.Ioc 0 1) := by
    refine Integrable.mono' (hint0.mul_const (phiHatR d 0)) ?_ ?_
    · have : Measurable (fun t : ℝ => t ^ m * phiHatR d (t * a)) := by
        have := continuous_phiHatR (d := d)
        fun_prop
      exact this.aestronglyMeasurable
    · filter_upwards [self_mem_ae_restrict (measurableSet_Ioc (a := (0:ℝ)) (b := 1))] with t ht
      rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _) (phiHatR_pos _).le)]
      exact mul_le_mul_of_nonneg_left (phiHatR_anti le_rfl (by have := ht.1; positivity)) (Real.rpow_nonneg ht.1.le _)
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0:ℝ) 1)] (fun t : ℝ => t ^ m * phiHatR d (t * a)) := by
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioc (a := (0:ℝ)) (b := 1))] with t ht
    exact mul_nonneg (Real.rpow_nonneg ht.1.le _) (phiHatR_pos _).le
  have h2 : ∫ t in Set.Ioc (0:ℝ) τ, t ^ m * phiHatR d (t * a) ≤
      ∫ t in Set.Ioc (0:ℝ) 1, t ^ m * phiHatR d (t * a) :=
    setIntegral_mono_set hint hnn (Filter.Eventually.of_forall (Set.Ioc_subset_Ioc_right hτ1))
  have h3 : phiHatR d 1 * (τ ^ (m + 1) / (m + 1)) ≤
      ∫ t in Set.Ioc (0:ℝ) τ, t ^ m * phiHatR d (t * a) := by
    have hcint : IntegrableOn (fun t : ℝ => t ^ m * phiHatR d (t * a)) (Set.Ioc 0 τ) :=
      hint.mono_set (Set.Ioc_subset_Ioc_right hτ1)
    have hc2 : IntegrableOn (fun t : ℝ => t ^ m) (Set.Ioc 0 τ) := hint0.mono_set (Set.Ioc_subset_Ioc_right hτ1)
    have hI : ∫ t in Set.Ioc (0:ℝ) τ, t ^ m = τ ^ (m + 1) / (m + 1) := by
      rw [← intervalIntegral.integral_of_le hτ0.le, integral_rpow (Or.inl (by linarith))]
      rw [Real.zero_rpow (by linarith)]; ring
    have : ∫ t in Set.Ioc (0:ℝ) τ, phiHatR d 1 * t ^ m = phiHatR d 1 * (τ ^ (m + 1) / (m + 1)) := by
      rw [integral_const_mul, hI]
    rw [← this]
    refine setIntegral_mono_on (hc2.const_mul _) hcint measurableSet_Ioc (fun t ht => ?_)
    have hta : t * a ≤ 1 := by
      have h1 : t ≤ 1 / (1 + a) := ht.2
      rw [le_div_iff₀ (by positivity)] at h1
      nlinarith [ht.1]
    have e2 : phiHatR d 1 ≤ phiHatR d (t * a) := phiHatR_anti (by have := ht.1; positivity) hta
    calc phiHatR d 1 * t ^ m = t ^ m * phiHatR d 1 := mul_comm _ _
      _ ≤ t ^ m * phiHatR d (t * a) := mul_le_mul_of_nonneg_left e2 (Real.rpow_nonneg ht.1.le _)
  have h4 : τ ^ (m + 1) = ((1 + a) ^ 2) ^ (-(alphaE d s)) := by
    have e : m + 1 = (d : ℝ) - s := by rw [hm]; ring
    rw [e, hτ, one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity),
      ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    unfold alphaE; push_cast; ring
  have h5 : (2:ℝ) ^ (-(alphaE d s)) * (1 + 4 * Real.pi ^ 2 * a ^ 2) ^ (-(alphaE d s)) ≤
      ((1 + a) ^ 2) ^ (-(alphaE d s)) := by
    rw [← Real.mul_rpow (by norm_num) (by positivity)]
    apply Real.rpow_le_rpow_of_nonpos (by positivity)
    · have : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
      nlinarith [sq_nonneg (1 - a), sq_nonneg a]
    · linarith
  have hm1 : m + 1 = (d : ℝ) - s := by rw [hm]; ring
  calc cPhi d s * phiHatR d 1 * (2:ℝ) ^ (-(alphaE d s)) / ((d : ℝ) - s) * (1 + 4 * Real.pi ^ 2 * a ^ 2) ^ (-(alphaE d s))
      = cPhi d s * (phiHatR d 1 * ((2:ℝ) ^ (-(alphaE d s)) * (1 + 4 * Real.pi ^ 2 * a ^ 2) ^ (-(alphaE d s)) / (m + 1))) := by
        rw [hm1]; ring
    _ ≤ cPhi d s * (phiHatR d 1 * (τ ^ (m + 1) / (m + 1))) := by
        rw [h4]
        gcongr
        all_goals first | exact (phiHatR_pos _).le | linarith
    _ ≤ cPhi d s * ∫ t in Set.Ioc (0:ℝ) 1, t ^ m * phiHatR d (t * a) :=
        mul_le_mul_of_nonneg_left (h3.trans h2) hcp.le

end HRS.Commutator.Whole
