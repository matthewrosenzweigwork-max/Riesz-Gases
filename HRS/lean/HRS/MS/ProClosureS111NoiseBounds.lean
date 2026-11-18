import HRS.MS.ProClosureS111NoiseFeatures
import HRS.MS.ProClosureS111OrbitSummable

/-!
Square-summable bounds and time increments for the actual common-noise
feature. The part of a noise increment before the earlier observation is
controlled by the physical terminal derivative of the gradient. The new
time slab has length |t-v|. No regularity or summability of a proposed
Gaussian feature map is assumed in the physical theorem.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R2WinOrb

variable {d : ℕ}

theorem noise_L2_norm_sq {X : Type*} [MeasurableSpace X] (nu : Measure X)
    (F : Lp (Euc d) 2 nu) : ‖F‖ ^ 2 = ∫ x, ‖F x‖ ^ 2 ∂nu := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem noiseClass_norm_sq_integral {C : WholeCoeff d} {mu : Measure (Euc d)}
    {t : ℝ} {phi : Euc d → ℝ}
    (hm : MemLp (noiseVector C t phi) 2 ((volume : Measure ℝ).prod mu)) :
    ‖noiseClass C mu t phi‖ ^ 2 =
      ∫ p, ‖noiseVector C t phi p‖ ^ 2 ∂((volume : Measure ℝ).prod mu) := by
  rw [noise_L2_norm_sq]
  exact integral_congr_ae ((noiseClass_ae hm).fun_comp (fun z => ‖z‖ ^ 2))

theorem noiseClass_sub_norm_sq_integral {C : WholeCoeff d} {mu : Measure (Euc d)}
    {t v : ℝ} {phi : Euc d → ℝ}
    (hm1 : MemLp (noiseVector C t phi) 2 ((volume : Measure ℝ).prod mu))
    (hm2 : MemLp (noiseVector C v phi) 2 ((volume : Measure ℝ).prod mu)) :
    ‖noiseClass C mu t phi - noiseClass C mu v phi‖ ^ 2 =
      ∫ p, ‖noiseVector C t phi p - noiseVector C v phi p‖ ^ 2
        ∂((volume : Measure ℝ).prod mu) := by
  rw [noise_L2_norm_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (noiseClass C mu t phi) (noiseClass C mu v phi),
    noiseClass_ae hm1, noiseClass_ae hm2] with p hp h1 h2
  rw [hp, Pi.sub_apply, h1, h2]

theorem noise_slab_Icc_integrable {mu : Measure (Euc d)} [IsProbabilityMeasure mu]
    (a b c : ℝ) : Integrable
      ((Icc a b ×ˢ (univ : Set (Euc d))).indicator (fun _ => c))
      ((volume : Measure ℝ).prod mu) := by
  refine (integrable_indicator_iff (measurableSet_Icc.prod MeasurableSet.univ)).2
    (integrableOn_const ?_)
  simp [Measure.prod_prod, Real.volume_Icc]

theorem noise_slab_Ioc_integrable {mu : Measure (Euc d)} [IsProbabilityMeasure mu]
    (a b c : ℝ) : Integrable
      ((Ioc a b ×ˢ (univ : Set (Euc d))).indicator (fun _ => c))
      ((volume : Measure ℝ).prod mu) := by
  refine (integrable_indicator_iff (measurableSet_Ioc.prod MeasurableSet.univ)).2
    (integrableOn_const ?_)
  simp [Measure.prod_prod, Real.volume_Ioc]

theorem noise_slab_Icc_integral {mu : Measure (Euc d)} [IsProbabilityMeasure mu]
    {a b : ℝ} (hab : a ≤ b) (c : ℝ) :
    ∫ p, (Icc a b ×ˢ (univ : Set (Euc d))).indicator (fun _ => c) p
      ∂((volume : Measure ℝ).prod mu) = (b - a) * c := by
  rw [integral_indicator (measurableSet_Icc.prod MeasurableSet.univ), integral_const]
  simp [Measure.real, Measure.prod_prod, Real.volume_Icc, sub_nonneg.2 hab, smul_eq_mul]

theorem noise_slab_Ioc_integral {mu : Measure (Euc d)} [IsProbabilityMeasure mu]
    {a b : ℝ} (hab : a ≤ b) (c : ℝ) :
    ∫ p, (Ioc a b ×ˢ (univ : Set (Euc d))).indicator (fun _ => c) p
      ∂((volume : Measure ℝ).prod mu) = (b - a) * c := by
  rw [integral_indicator (measurableSet_Ioc.prod MeasurableSet.univ), integral_const]
  simp [Measure.real, Measure.prod_prod, Real.volume_Ioc, sub_nonneg.2 hab, smul_eq_mul]

theorem noiseClass_norm_sq_le {C : WholeCoeff d} {mu : Measure (Euc d)}
    [IsProbabilityMeasure mu] {t A : ℝ} (ht : 0 ≤ t) (hA : 0 ≤ A)
    {phi : Euc d → ℝ}
    (hf : IsClassicalAdjointW C t phi (fun r => propagatorW C r t phi))
    (hgrad : ∀ r ∈ Icc (0 : ℝ) t, ∀ x,
      ‖gradient (propagatorW C r t phi) x‖ ≤ A) :
    ‖noiseClass C mu t phi‖ ^ 2 ≤ A ^ 2 * t := by
  have hm := noiseVector_memLp ht hf (mu := mu)
  have hi : Integrable (fun p => ‖noiseVector C t phi p‖ ^ 2)
      ((volume : Measure ℝ).prod mu) := hm.integrable_norm_pow (by norm_num)
  rw [noiseClass_norm_sq_integral hm]
  calc
    _ ≤ ∫ p, (Icc (0 : ℝ) t ×ˢ (univ : Set (Euc d))).indicator
        (fun _ => A ^ 2) p ∂((volume : Measure ℝ).prod mu) := by
      apply integral_mono hi (noise_slab_Icc_integrable 0 t (A ^ 2))
      intro p
      by_cases hp : p.1 ∈ Icc (0 : ℝ) t
      · simp only [noiseVector, if_pos hp,
          Set.indicator_of_mem (show p ∈ Icc (0 : ℝ) t ×ˢ (univ : Set (Euc d)) from ⟨hp, mem_univ _⟩)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hgrad p.1 hp p.2) 2
      · simp [noiseVector, hp]
    _ = A ^ 2 * t := by rw [noise_slab_Icc_integral ht]; ring

theorem noiseClass_sub_norm_sq_le_ordered {C : WholeCoeff d} {mu : Measure (Euc d)}
    [IsProbabilityMeasure mu] {v t A : ℝ} (hv : 0 ≤ v) (hvt : v ≤ t) (hA : 0 ≤ A)
    {phi : Euc d → ℝ}
    (hf : IsClassicalAdjointW C t phi (fun r => propagatorW C r t phi))
    (hg : IsClassicalAdjointW C v phi (fun r => propagatorW C r v phi))
    (hgrad : ∀ r ∈ Ioc v t, ∀ x, ‖gradient (propagatorW C r t phi) x‖ ≤ A)
    (hinc : ∀ r ∈ Icc (0 : ℝ) v, ∀ x,
      ‖gradient (propagatorW C r t phi) x - gradient (propagatorW C r v phi) x‖ ≤
        A * (t - v)) :
    ‖noiseClass C mu t phi - noiseClass C mu v phi‖ ^ 2 ≤
      A ^ 2 * (v * (t - v) ^ 2 + (t - v)) := by
  have ht : 0 ≤ t := hv.trans hvt
  have hm1 := noiseVector_memLp ht hf (mu := mu)
  have hm2 := noiseVector_memLp hv hg (mu := mu)
  have hi : Integrable
      (fun p => ‖noiseVector C t phi p - noiseVector C v phi p‖ ^ 2)
      ((volume : Measure ℝ).prod mu) := (hm1.sub hm2).integrable_norm_pow (by norm_num)
  let A1 := (Icc (0 : ℝ) v ×ˢ (univ : Set (Euc d))).indicator
    (fun _ => (A * (t - v)) ^ 2)
  let A2 := (Ioc v t ×ˢ (univ : Set (Euc d))).indicator (fun _ => A ^ 2)
  have hi1 : Integrable A1 ((volume : Measure ℝ).prod mu) :=
    noise_slab_Icc_integrable 0 v _
  have hi2 : Integrable A2 ((volume : Measure ℝ).prod mu) :=
    noise_slab_Ioc_integrable v t _
  have hbound : ∀ p : ℝ × Euc d,
      ‖noiseVector C t phi p - noiseVector C v phi p‖ ^ 2 ≤ A1 p + A2 p := by
    intro p
    by_cases hcommon : p.1 ∈ Icc (0 : ℝ) v
    · have hrt : p.1 ∈ Icc (0 : ℝ) t := ⟨hcommon.1, hcommon.2.trans hvt⟩
      have hshort : p.1 ∉ Ioc v t := fun h => not_lt_of_ge hcommon.2 h.1
      simp only [noiseVector, if_pos hrt, if_pos hcommon]
      have hsq := pow_le_pow_left₀ (norm_nonneg _) (hinc p.1 hcommon p.2) 2
      simpa [A1, A2, hcommon, hshort] using hsq
    · by_cases hshort : p.1 ∈ Ioc v t
      · have hrt : p.1 ∈ Icc (0 : ℝ) t := ⟨hv.trans hshort.1.le, hshort.2⟩
        have hsq := pow_le_pow_left₀ (norm_nonneg _) (hgrad p.1 hshort p.2) 2
        simpa [noiseVector, hrt, hcommon, A1, A2, hshort] using hsq
      · have hrt : p.1 ∉ Icc (0 : ℝ) t := by
          intro h
          have hpv : v < p.1 := lt_of_not_ge (fun hp => hcommon ⟨h.1, hp⟩)
          exact hshort ⟨hpv, h.2⟩
        simp [noiseVector, hrt, hcommon, A1, A2, hshort]
  rw [noiseClass_sub_norm_sq_integral hm1 hm2]
  calc
    _ ≤ ∫ p, (A1 p + A2 p) ∂((volume : Measure ℝ).prod mu) :=
      integral_mono hi (hi1.add hi2) hbound
    _ = A ^ 2 * (v * (t - v) ^ 2 + (t - v)) := by
      rw [integral_add hi1 hi2]
      change (∫ p, (Icc (0 : ℝ) v ×ˢ (univ : Set (Euc d))).indicator
        (fun _ => (A * (t - v)) ^ 2) p ∂((volume : Measure ℝ).prod mu)) +
        (∫ p, (Ioc v t ×ˢ (univ : Set (Euc d))).indicator
          (fun _ => A ^ 2) p ∂((volume : Measure ℝ).prod mu)) = _
      rw [noise_slab_Icc_integral hv, noise_slab_Ioc_integral hvt]
      ring

theorem noise_ordered_interval_bound {v t H : ℝ}
    (hv : 0 ≤ v) (hvt : v ≤ t) (htH : t ≤ H) :
    v * (t - v) ^ 2 + (t - v) ≤ (H ^ 2 + 1) * (t - v) := by
  have hH : 0 ≤ H := (hv.trans hvt).trans htH
  have hdelta : 0 ≤ t - v := sub_nonneg.2 hvt
  have hvH : v ≤ H := hvt.trans htH
  have hdH : t - v ≤ H := by linarith
  have hp : v * (t - v) ≤ H * H := mul_le_mul hvH hdH hdelta hH
  have hh := mul_le_mul_of_nonneg_right hp hdelta
  nlinarith

/-- The common noise has the square-summable feature and square-root time
modulus required by the accepted Gaussian path constructor. The feature
is the concrete cutoff gradient, not an existential unspecified map. -/
theorem physical_noise_features_summable (hd : 2 ≤ d)
    {s a beta : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ))
    (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d s a beta rho) (H : ℝ) (hH : 0 ≤ H) :
    let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
    let N := fun t (alpha : MultiIndex d) =>
      scaledNoiseClass C (HRS.Whole.withDensityReal rho) beta⁻¹ t
        (oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha)
    (∀ t ∈ Icc (0 : ℝ) H, Summable (fun alpha => ‖N t alpha‖ ^ 2)) ∧
      ∃ L : ℝ, 0 ≤ L ∧ ∀ t v, t ∈ Icc (0 : ℝ) H → v ∈ Icc (0 : ℝ) H →
        Summable (fun alpha => ‖N t alpha - N v alpha‖ ^ 2) ∧
          (∑' alpha, ‖N t alpha - N v alpha‖ ^ 2) ≤ L * |t - v| := by
  let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
  let mu := HRS.Whole.withDensityReal rho
  let phi := fun alpha : MultiIndex d => oscTestFun ((24 * d + 240 : ℕ) : ℝ) alpha
  let N := fun t (alpha : MultiIndex d) => scaledNoiseClass C mu beta⁻¹ t (phi alpha)
  letI : IsProbabilityMeasure mu := HRS.Whole.Q34.isProbabilityMeasure_nu hrho.2.1
  obtain ⟨B, hB, hmag, hinc⟩ := physical_gradient_time_bound hd hs0 hsd ha hbeta hrho
  have hq : 0 ≤ 2 * beta⁻¹ := by positivity
  have hphi : ∀ alpha t, 0 ≤ t → IsClassicalAdjointW C t (phi alpha)
      (fun r => propagatorW C r t (phi alpha)) := by
    intro alpha t ht
    exact HRS.MS.Fcau.propagatorW_isClassical
      (physical_classical_orbits hd hs0 hsd ha hbeta hrho alpha ht).1
  have hsquare := stationary_weight_square_summable (d := d) (by omega)
  have hNnorm : ∀ alpha t, 0 ≤ t → ‖N t alpha‖ ^ 2 ≤
      (2 * beta⁻¹) * (B * s103_b d alpha) ^ 2 * t := by
    intro alpha t ht
    have hbase := noiseClass_norm_sq_le (mu := mu) ht
      (mul_nonneg hB (s103_b_nonneg alpha)) (hphi alpha t ht)
      (fun r hr x => hmag alpha r t hr.1 hr.2 x)
    change ‖Real.sqrt (2 * beta⁻¹) • noiseClass C mu t (phi alpha)‖ ^ 2 ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt hq]
    exact (mul_le_mul_of_nonneg_left hbase hq).trans_eq (by ring)
  have hNinc_ordered : ∀ alpha t v, 0 ≤ v → v ≤ t → t ≤ H →
      ‖N t alpha - N v alpha‖ ^ 2 ≤
        (2 * beta⁻¹) * (B * s103_b d alpha) ^ 2 * (H ^ 2 + 1) * (t - v) := by
    intro alpha t v hv hvt htH
    have ht := hv.trans hvt
    have hbase := noiseClass_sub_norm_sq_le_ordered (mu := mu) hv hvt
      (mul_nonneg hB (s103_b_nonneg alpha)) (hphi alpha t ht) (hphi alpha v hv)
      (fun r hr x => hmag alpha r t (hv.trans hr.1.le) hr.2 x)
      (fun r hr x => by
        simpa only [abs_of_nonneg (sub_nonneg.2 hvt)] using
          hinc alpha r t v hr.1 (hr.2.trans hvt) hr.2 x)
    have htime := noise_ordered_interval_bound hv hvt htH
    change ‖Real.sqrt (2 * beta⁻¹) • noiseClass C mu t (phi alpha) -
      Real.sqrt (2 * beta⁻¹) • noiseClass C mu v (phi alpha)‖ ^ 2 ≤ _
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, Real.sq_sqrt hq]
    calc
      _ ≤ (2 * beta⁻¹) * ((B * s103_b d alpha) ^ 2 *
          (v * (t - v) ^ 2 + (t - v))) := mul_le_mul_of_nonneg_left hbase hq
      _ ≤ (2 * beta⁻¹) * ((B * s103_b d alpha) ^ 2 *
          ((H ^ 2 + 1) * (t - v))) := by gcongr
      _ = _ := by ring
  let K : ℝ := (2 * beta⁻¹) * B ^ 2 * (H ^ 2 + 1)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hNinc : ∀ alpha t v, t ∈ Icc (0 : ℝ) H → v ∈ Icc (0 : ℝ) H →
      ‖N t alpha - N v alpha‖ ^ 2 ≤ K * s103_b d alpha ^ 2 * |t - v| := by
    intro alpha t v ht hv
    rcases le_total v t with hvt | htv
    · have hb := hNinc_ordered alpha t v hv.1 hvt ht.2
      rw [abs_of_nonneg (sub_nonneg.2 hvt)]
      exact hb.trans_eq (by dsimp [K]; ring)
    · have hb := hNinc_ordered alpha v t ht.1 htv hv.2
      rw [norm_sub_rev, abs_of_nonpos (sub_nonpos.2 htv)]
      exact hb.trans_eq (by dsimp [K]; ring)
  refine ⟨?_, K * (∑' alpha : MultiIndex d, s103_b d alpha ^ 2),
    mul_nonneg hK (tsum_nonneg fun _ => sq_nonneg _), ?_⟩
  · intro t ht
    have hmajor : Summable (fun alpha : MultiIndex d =>
        ((2 * beta⁻¹) * B ^ 2 * t) * s103_b d alpha ^ 2) := hsquare.mul_left _
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ hmajor
    intro alpha
    exact (hNnorm alpha t ht.1).trans_eq (by ring)
  · intro t v ht hv
    have hmajor : Summable (fun alpha : MultiIndex d =>
        K * s103_b d alpha ^ 2 * |t - v|) := (hsquare.mul_left K).mul_right _
    have hsum : Summable (fun alpha => ‖N t alpha - N v alpha‖ ^ 2) :=
      Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun alpha => hNinc alpha t v ht hv) hmajor
    refine ⟨hsum, ?_⟩
    calc
      _ ≤ ∑' alpha : MultiIndex d, K * s103_b d alpha ^ 2 * |t - v| :=
        hsum.tsum_le_tsum (fun alpha => hNinc alpha t v ht hv) hmajor
      _ = _ := by rw [tsum_mul_right, tsum_mul_left]

#print axioms physical_noise_features_summable

end HRS.MS.ProClosureS111
