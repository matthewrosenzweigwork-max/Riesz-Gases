import HRS.MC.D3T1Aux1

/-!
# Packet D3T1, auxiliary facts: the mean of `P φ_t` and the Tonelli computation for `∫ w_λ`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.MC.D3T1

open HRS HRS.MC.FDLE HRS.MC.Per

variable {d : ℕ}

lemma d3t_measurable_rep (d : ℕ) : Measurable (Torus.rep : Torus d → Euc d) := by
  have h : Measurable (fun (x : Torus d) (i : Fin d) =>
      ((AddCircle.equivIco (1 : ℝ) 0 (x i) : Set.Ico (0 : ℝ) (0 + 1)) : ℝ)) :=
    measurable_pi_iff.2 fun i => measurable_subtype_coe.comp
      ((AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.comp (measurable_pi_apply i))
  exact (WithLp.measurable_toLp 2 _).comp h

/-- The mean of `P φ_t` over the torus is `∫ φ`. -/
lemma d3t_per_integral {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {t : ℝ} (ht : 0 < t) :
    ∫ x : Torus d, fdlPer (fdlPhiScale ψ t) x = ∫ y, fdlPhi ψ y := by
  have h := per_fcoef_unfold (per_phiScale_contDiff hψ t) (R := t)
    (fun x hx => per_phiScale_zero hψ ht hx.le) (0 : Lattice d)
  unfold Torus.fcoef at h
  simp only [neg_zero, Torus.mode_zero, one_mul] at h
  rw [← fdle_phiScale_integral hψ ht]
  have : ((∫ x : Torus d, fdlPer (fdlPhiScale ψ t) x : ℝ) : ℂ)
      = ((∫ y, fdlPhiScale ψ t y : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, ← integral_complex_ofReal]; exact h
  exact_mod_cast this

lemma d3t_per_integrable {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {t : ℝ} (ht : 0 < t) :
    Integrable (fdlPer (fdlPhiScale ψ t)) (volume : Measure (Torus d)) :=
  (per_fdlPer_continuous hψ ht).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma d3t_ofReal_per {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {t : ℝ} (ht : 0 < t) (x : Torus d) :
    ENNReal.ofReal (fdlPer (fdlPhiScale ψ t) x)
      = ∑' n : Lattice d, ENNReal.ofReal (fdlPhiScale ψ t (Torus.rep x + Lattice.toEuc n)) := by
  unfold fdlPer
  exact ENNReal.ofReal_tsum_of_nonneg (fun n => fdle_phiScale_nonneg hψ ht _)
    (d3t_summable hψ ht _)

lemma d3t_ofReal_integral_le {S : Set ℝ} (hS : MeasurableSet S) {f : ℝ → ℝ}
    (hnn : ∀ t ∈ S, 0 ≤ f t) :
    ENNReal.ofReal (∫ t in S, f t) ≤ ∫⁻ t in S, ENNReal.ofReal (f t) := by
  by_cases hf : IntegrableOn f S
  · rw [ofReal_integral_eq_lintegral_ofReal hf
      ((ae_restrict_iff' hS).mpr (Eventually.of_forall hnn))]
  · rw [integral_undef hf]; simp

lemma d3t_lintegral_W {ψ : Euc d → ℝ} (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) {lam : ℝ} (hlam : 0 < lam) :
    ∫⁻ x : Torus d, ENNReal.ofReal (fdlWT ψ s b lam x)
      ≤ ENNReal.ofReal (b * (∫ x, fdlPhi ψ x) * (lam ^ ((d : ℝ) - s) / ((d : ℝ) - s))) := by
  have hI0 : 0 ≤ ∫ x, fdlPhi ψ x := integral_nonneg (fdle_phi_nonneg hψ)
  have hb0 : 0 < b := hb.1
  have hds : 0 < (d : ℝ) - s := by linarith
  set κ : ℝ → ℝ := fun t => b * (t ^ ((d : ℝ) - s) / t) with hκdef
  set G : Torus d × ℝ → ℝ≥0∞ := fun p =>
    ∑' n : Lattice d, ENNReal.ofReal (fdlPhiScale ψ p.2 (Torus.rep p.1 + Lattice.toEuc n)) with hG
  -- Step 1: pointwise bound by a `t`-lintegral.
  have step1 : ∀ x : Torus d, ENNReal.ofReal (fdlWT ψ s b lam x)
      ≤ ∫⁻ t in Ioc 0 lam, ENNReal.ofReal (κ t) * G (x, t) := by
    intro x
    unfold fdlWT
    rw [← integral_const_mul]
    refine (d3t_ofReal_integral_le measurableSet_Ioc (fun t ht =>
      mul_nonneg hb0.le (div_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _)
        (d3t_per_nonneg hψ ht.1 x)) ht.1.le))).trans (le_of_eq ?_)
    refine setLIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    have hκ : 0 ≤ κ t := mul_nonneg hb0.le (div_nonneg (Real.rpow_nonneg ht.1.le _) ht.1.le)
    have : b * (t ^ ((d : ℝ) - s) * fdlPer (fdlPhiScale ψ t) x / t)
        = κ t * fdlPer (fdlPhiScale ψ t) x := by
      simp only [hκdef]; ring
    rw [this, ENNReal.ofReal_mul hκ, d3t_ofReal_per hψ ht.1]
  -- Step 2: Tonelli.
  have hφm : Measurable (fdlPhi ψ) := (fdle_phi_cont hψ).measurable
  have hrep := d3t_measurable_rep d
  have hmG : Measurable G := by
    refine Measurable.ennreal_tsum fun n => ?_
    refine Measurable.ennreal_ofReal ?_
    unfold fdlPhiScale
    exact ((measurable_snd.pow_const d).inv).mul
      (hφm.comp (measurable_snd.inv.smul ((hrep.comp measurable_fst).add_const _)))
  have hmκ : Measurable (fun p : Torus d × ℝ => ENNReal.ofReal (κ p.2) * G p) := by
    have : Measurable κ := by
      simp only [hκdef]
      exact (((measurable_id.pow_const _).div measurable_id).const_mul b)
    exact (this.comp measurable_snd).ennreal_ofReal.mul hmG
  have step2 : ∫⁻ x : Torus d, ∫⁻ t in Ioc 0 lam, ENNReal.ofReal (κ t) * G (x, t)
      = ∫⁻ t in Ioc 0 lam, ∫⁻ x : Torus d, ENNReal.ofReal (κ t) * G (x, t) :=
    lintegral_lintegral_swap hmκ.aemeasurable
  -- Step 3: the inner integral.
  have step3 : ∀ t : ℝ, 0 < t → ∫⁻ x : Torus d, ENNReal.ofReal (κ t) * G (x, t)
      = ENNReal.ofReal (κ t) * ENNReal.ofReal (∫ x, fdlPhi ψ x) := by
    intro t ht
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    have hGe : ∀ x : Torus d, G (x, t) = ENNReal.ofReal (fdlPer (fdlPhiScale ψ t) x) := by
      intro x; rw [d3t_ofReal_per hψ ht x]
    simp_rw [hGe]
    rw [← ofReal_integral_eq_lintegral_ofReal (d3t_per_integrable hψ ht)
      (Eventually.of_forall fun x => d3t_per_nonneg hψ ht x), d3t_per_integral hψ ht]
  have step4 : ∫⁻ t in Ioc 0 lam, ∫⁻ x : Torus d, ENNReal.ofReal (κ t) * G (x, t)
      = ∫⁻ t in Ioc 0 lam, ENNReal.ofReal (κ t) * ENNReal.ofReal (∫ x, fdlPhi ψ x) :=
    setLIntegral_congr_fun measurableSet_Ioc (fun t ht => step3 t ht.1)
  have hκint : IntegrableOn κ (Ioc 0 lam) := by
    have hiv : IntervalIntegrable (fun t : ℝ => t ^ ((d : ℝ) - s - 1)) volume 0 lam :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hlam.le] at hiv
    refine IntegrableOn.congr_fun (Integrable.const_mul hiv b) ?_ measurableSet_Ioc
    intro t ht
    simp only [hκdef]
    rw [Real.rpow_sub_one ht.1.ne']
  have hκnn : 0 ≤ᵐ[volume.restrict (Ioc 0 lam)] κ :=
    (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht =>
      mul_nonneg hb0.le (div_nonneg (Real.rpow_nonneg ht.1.le _) ht.1.le))
  have hκval : ∫ t in Ioc 0 lam, κ t = b * (lam ^ ((d : ℝ) - s) / ((d : ℝ) - s)) := by
    have hr1 : (d : ℝ) - s - 1 + 1 = (d : ℝ) - s := by ring
    have hcongr : ∫ t in Ioc 0 lam, κ t = ∫ t in Ioc 0 lam, b * t ^ ((d : ℝ) - s - 1) := by
      refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
      simp only [hκdef]
      rw [Real.rpow_sub_one ht.1.ne']
    rw [hcongr, ← intervalIntegral.integral_of_le hlam.le, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by linarith)), hr1,
      Real.zero_rpow (by linarith), sub_zero]
  calc ∫⁻ x : Torus d, ENNReal.ofReal (fdlWT ψ s b lam x)
      ≤ ∫⁻ x : Torus d, ∫⁻ t in Ioc 0 lam, ENNReal.ofReal (κ t) * G (x, t) :=
        lintegral_mono step1
    _ = ∫⁻ t in Ioc 0 lam, ENNReal.ofReal (κ t) * ENNReal.ofReal (∫ x, fdlPhi ψ x) := by
        rw [step2, step4]
    _ = ENNReal.ofReal (b * (∫ x, fdlPhi ψ x) * (lam ^ ((d : ℝ) - s) / ((d : ℝ) - s))) := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
          ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hκint hκnn, hκval,
          ← ENNReal.ofReal_mul (mul_nonneg hb0.le (div_nonneg (Real.rpow_nonneg hlam.le _) hds.le))]
        congr 1
        ring

end HRS.MC.D3T1
