import HRS.MC.FDLEAux2

/-!
# Packet FDLE, the lower-level Tonelli computation `∫⁻ w_λ = b (∫φ) λ^{d-s}/(d-s)` (Lemma D.3(i)).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.MC.FDLE

open HRS

variable {d : ℕ}

/-- `{0}` is Lebesgue-null, so `z ≠ 0` holds almost everywhere (`d ≥ 1`). -/
lemma fdle_ae_ne_zero (hd : 1 ≤ d) : ∀ᵐ z : Euc d ∂(volume : Measure (Euc d)), z ≠ 0 := by
  obtain ⟨x0, hx0⟩ : ∃ x0 : Euc d, x0 ≠ 0 :=
    Module.finrank_pos_iff_exists_ne_zero.mp (by rw [finrank_euclideanSpace_fin]; omega)
  haveI : Nontrivial (Euc d) := ⟨⟨x0, 0, hx0⟩⟩
  refine ae_iff.mpr ?_
  simpa using measure_singleton (0 : Euc d)

lemma fdle_lintegral_W {ψ : Euc d → ℝ} (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) {lam : ℝ} (hlam : 0 < lam) :
    ∫⁻ z : Euc d, ENNReal.ofReal (fdlWE ψ s b lam z)
      = ENNReal.ofReal (b * (∫ x, fdlPhi ψ x) * (lam ^ ((d : ℝ) - s) / ((d : ℝ) - s))) := by
  have hI0 : 0 ≤ ∫ x, fdlPhi ψ x := integral_nonneg (fdle_phi_nonneg hψ)
  have hb0 : 0 < b := hb.1
  have hds : 0 < (d : ℝ) - s := by linarith
  -- Step 1: for `z ≠ 0`, the value is a lintegral over `t`.
  have step1 : ∀ z : Euc d, z ≠ 0 → ENNReal.ofReal (fdlWE ψ s b lam z)
      = ∫⁻ t in Ioc 0 lam, ENNReal.ofReal (b * (t ^ ((d : ℝ) - s) * fdlPhiScale ψ t z / t)) := by
    intro z hz
    unfold fdlWE
    rw [← integral_const_mul]
    have hint : IntegrableOn (fun t : ℝ => b * (t ^ ((d : ℝ) - s) * fdlPhiScale ψ t z / t))
        (Ioc 0 lam) :=
      (fdle_F_integrable hs0 hb hz hlam).const_mul b
    have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 lam)]
        (fun t : ℝ => b * (t ^ ((d : ℝ) - s) * fdlPhiScale ψ t z / t)) :=
      (ae_restrict_iff' measurableSet_Ioc).mpr
        (Eventually.of_forall fun t ht => mul_nonneg hb0.le (fdle_F_nonneg hψ s ht.1 z))
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn
  have step2 : ∫⁻ z : Euc d, ENNReal.ofReal (fdlWE ψ s b lam z)
      = ∫⁻ z : Euc d, ∫⁻ t in Ioc 0 lam,
          ENNReal.ofReal (b * (t ^ ((d : ℝ) - s) * fdlPhiScale ψ t z / t)) :=
    lintegral_congr_ae ((fdle_ae_ne_zero hd).mono fun z hz => step1 z hz)
  -- Step 3: Tonelli.
  have hφm : Measurable (fdlPhi ψ) := (fdle_phi_cont hψ).measurable
  have hm1 : Measurable (fun p : Euc d × ℝ => p.2 ^ ((d : ℝ) - s)) := measurable_snd.pow_const _
  have hm2 : Measurable (fun p : Euc d × ℝ => fdlPhiScale ψ p.2 p.1) := by
    unfold fdlPhiScale
    exact ((measurable_snd.pow_const d).inv).mul
      (hφm.comp (measurable_snd.inv.smul measurable_fst))
  have hmeas : Measurable (fun p : Euc d × ℝ =>
      ENNReal.ofReal (b * (p.2 ^ ((d : ℝ) - s) * fdlPhiScale ψ p.2 p.1 / p.2))) :=
    (((hm1.mul hm2).div measurable_snd).const_mul b).ennreal_ofReal
  have step3 : ∫⁻ z : Euc d, ∫⁻ t in Ioc 0 lam,
          ENNReal.ofReal (b * (t ^ ((d : ℝ) - s) * fdlPhiScale ψ t z / t))
      = ∫⁻ t in Ioc 0 lam, ∫⁻ z : Euc d,
          ENNReal.ofReal (b * (t ^ ((d : ℝ) - s) * fdlPhiScale ψ t z / t)) :=
    lintegral_lintegral_swap hmeas.aemeasurable
  -- Step 4: for `t > 0` the `z`-integral is a product.
  have step4 : ∀ t : ℝ, 0 < t → ∫⁻ z : Euc d,
      ENNReal.ofReal (b * (t ^ ((d : ℝ) - s) * fdlPhiScale ψ t z / t))
      = ENNReal.ofReal (b * (t ^ ((d : ℝ) - s) / t)) * ENNReal.ofReal (∫ x, fdlPhi ψ x) := by
    intro t ht
    have hκ : 0 ≤ b * (t ^ ((d : ℝ) - s) / t) :=
      mul_nonneg hb0.le (div_nonneg (Real.rpow_nonneg ht.le _) ht.le)
    have hrw : ∀ z : Euc d, ENNReal.ofReal (b * (t ^ ((d : ℝ) - s) * fdlPhiScale ψ t z / t))
        = ENNReal.ofReal (b * (t ^ ((d : ℝ) - s) / t)) * ENNReal.ofReal (fdlPhiScale ψ t z) := by
      intro z
      rw [← ENNReal.ofReal_mul hκ]
      congr 1
      ring
    simp_rw [hrw]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (fdle_phiScale_integrable hψ ht)
      (Eventually.of_forall fun z => fdle_phiScale_nonneg hψ ht z),
      fdle_phiScale_integral hψ ht]
  -- Step 5: the `t`-integral.
  have step5 : ∫⁻ t in Ioc 0 lam, ∫⁻ z : Euc d,
      ENNReal.ofReal (b * (t ^ ((d : ℝ) - s) * fdlPhiScale ψ t z / t))
      = ∫⁻ t in Ioc 0 lam, ENNReal.ofReal (b * (t ^ ((d : ℝ) - s) / t))
          * ENNReal.ofReal (∫ x, fdlPhi ψ x) :=
    setLIntegral_congr_fun measurableSet_Ioc (fun t ht => step4 t ht.1)
  have hκint : IntegrableOn (fun t : ℝ => b * (t ^ ((d : ℝ) - s) / t)) (Ioc 0 lam) := by
    have hiv : IntervalIntegrable (fun t : ℝ => t ^ ((d : ℝ) - s - 1)) volume 0 lam :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hlam.le] at hiv
    refine IntegrableOn.congr_fun (Integrable.const_mul hiv b) ?_ measurableSet_Ioc
    intro t ht
    simp only
    rw [Real.rpow_sub_one ht.1.ne']
  have hκnn : 0 ≤ᵐ[volume.restrict (Ioc 0 lam)] (fun t : ℝ => b * (t ^ ((d : ℝ) - s) / t)) :=
    (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht =>
      mul_nonneg hb0.le (div_nonneg (Real.rpow_nonneg ht.1.le _) ht.1.le))
  have hκval : ∫ t in Ioc 0 lam, b * (t ^ ((d : ℝ) - s) / t) = b * (lam ^ ((d : ℝ) - s) / ((d : ℝ) - s)) := by
    have hr1 : (d : ℝ) - s - 1 + 1 = (d : ℝ) - s := by ring
    have hcongr : ∫ t in Ioc 0 lam, b * (t ^ ((d : ℝ) - s) / t)
        = ∫ t in Ioc 0 lam, b * t ^ ((d : ℝ) - s - 1) := by
      refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
      rw [Real.rpow_sub_one ht.1.ne']
    rw [hcongr, ← intervalIntegral.integral_of_le hlam.le, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by linarith)), hr1,
      Real.zero_rpow (by linarith), sub_zero]
  rw [step2, step3, step5, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
    ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hκint hκnn, hκval,
    ← ENNReal.ofReal_mul (mul_nonneg hb0.le (div_nonneg (Real.rpow_nonneg hlam.le _) hds.le))]
  congr 1
  ring

end HRS.MC.FDLE
