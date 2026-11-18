import HRS.Appendix.B15CAux2

/-!
# Packet B15-CQ: proofs of `b15c_gibbsEntropyGen_le` and `b15c_regularised_eq_strong`

Section A (`b15c_gibbsEntropyGen_le_proof`): the entropy comparison `𝓗_{G_ε}(P) ≤ 𝓗_G(P)` from
`G ≤ G_ε`.  Generic density comparison for `klDiv` against `volume.withDensity` (`b15c_klDiv_withDensity_le`),
proved via `klDiv_eq_lintegral_klFun_of_ac` and the pointwise inequality `b15c_real_klFun_ineq`.
-/

noncomputable section

open MeasureTheory InformationTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS

variable {d N : ℕ}

/-! ## Section A: `𝓗_{G_ε}(P) ≤ 𝓗_G(P)` -/

/-- Pointwise real inequality behind the entropy comparison: for `c a ≤ b`,
`b · klFun(q/b) ≤ a · klFun(q/a) + (b - a) - log c · q` for `q ≥ 0`. -/
theorem b15c_real_klFun_ineq {a b c q : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hcab : c * a ≤ b) (hq : 0 ≤ q) :
    b * klFun (q / b) ≤ a * klFun (q / a) + (b - a) - Real.log c * q := by
  rcases hq.eq_or_lt with h0 | hpos
  · subst h0
    simp [klFun_apply]
  · have hlog : Real.log (q / b) ≤ Real.log (q / a) - Real.log c := by
      rw [← Real.log_div (div_pos hpos ha).ne' hc.ne']
      apply Real.log_le_log (div_pos hpos hb)
      rw [div_div]
      exact div_le_div_of_nonneg_left hpos.le (by positivity) (by linarith [mul_comm a c])
    have hb0 := hb.ne'
    have ha0 := ha.ne'
    have e1 : b * klFun (q / b) = q * Real.log (q / b) + b - q := by
      rw [klFun_apply]; field_simp
    have e2 : a * klFun (q / a) = q * Real.log (q / a) + a - q := by
      rw [klFun_apply]; field_simp
    rw [e1, e2]
    linarith [mul_le_mul_of_nonneg_left hlog hq]

/-- The relative entropy of `P` against `volume.withDensity d` (for `d > 0` a.e.) as a `lintegral`
of the `klFun` of the density `dP/dV` (reference `volume`). -/
theorem b15c_klDiv_withDensity_eq {Ω : Type*} [MeasurableSpace Ω] (V P : Measure Ω) [SigmaFinite V]
    [IsProbabilityMeasure P] (d : Ω → ℝ) (hd : Measurable d) (hd0 : ∀ᵐ x ∂V, 0 < d x)
    (hQ : IsProbabilityMeasure (V.withDensity fun x => ENNReal.ofReal (d x)))
    (hPd : P ≪ V.withDensity fun x => ENNReal.ofReal (d x)) :
    klDiv P (V.withDensity fun x => ENNReal.ofReal (d x)) =
      ∫⁻ x, ENNReal.ofReal (d x * klFun ((P.rnDeriv V x).toReal / d x)) ∂V := by
  classical
  set Q := V.withDensity fun x => ENNReal.ofReal (d x) with hQdef
  have hPV : P ≪ V := hPd.trans (withDensity_absolutelyContinuous _ _)
  have hpm : Measurable (P.rnDeriv V) := Measure.measurable_rnDeriv P V
  have hpfin : ∀ᵐ x ∂V, P.rnDeriv V x < ⊤ := Measure.rnDeriv_lt_top P V
  have hPeq : V.withDensity (P.rnDeriv V) = P := Measure.withDensity_rnDeriv_eq P V hPV
  have hdE : Measurable fun x => ENNReal.ofReal (d x) := ENNReal.measurable_ofReal.comp hd
  have hinv : Measurable fun x => (ENNReal.ofReal (d x))⁻¹ := hdE.inv
  set r : Ω → ℝ≥0∞ := fun x => P.rnDeriv V x * (ENNReal.ofReal (d x))⁻¹ with hrdef
  have hrm : Measurable r := hpm.mul hinv
  have hPr : Q.withDensity r = P := by
    rw [hQdef, ← withDensity_mul V hdE hrm, ← hPeq]
    apply withDensity_congr_ae
    filter_upwards [hd0, hpfin] with x hx0 hxf
    have h0 : ENNReal.ofReal (d x) ≠ 0 := (ENNReal.ofReal_pos.mpr hx0).ne'
    have ht : ENNReal.ofReal (d x) ≠ ⊤ := ENNReal.ofReal_ne_top
    simp only [Pi.mul_apply, hrdef]
    rw [show ENNReal.ofReal (d x) * (P.rnDeriv V x * (ENNReal.ofReal (d x))⁻¹) =
        P.rnDeriv V x * (ENNReal.ofReal (d x) * (ENNReal.ofReal (d x))⁻¹) by ring,
      ENNReal.mul_inv_cancel h0 ht, mul_one]
  have hr : P.rnDeriv Q =ᵐ[Q] r := by
    have := Measure.rnDeriv_withDensity₀ Q hrm.aemeasurable
    rwa [hPr] at this
  rw [klDiv_eq_lintegral_klFun_of_ac hPd]
  have hg : Measurable fun x => ENNReal.ofReal (klFun ((r x).toReal)) :=
    ENNReal.measurable_ofReal.comp (measurable_klFun.comp (ENNReal.measurable_toReal.comp hrm))
  have hcongr : (fun x => ENNReal.ofReal (klFun ((P.rnDeriv Q x).toReal))) =ᵐ[Q]
      (fun x => ENNReal.ofReal (klFun ((r x).toReal))) :=
    hr.mono fun x hx => by simp only [hx]
  rw [lintegral_congr_ae hcongr, lintegral_withDensity_eq_lintegral_mul V hdE hg]
  apply lintegral_congr_ae
  filter_upwards [hd0] with x hx0
  simp only [Pi.mul_apply, hrdef]
  rw [← ENNReal.ofReal_mul hx0.le]
  congr 1
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hx0.le, div_eq_mul_inv]

/-- Generic density comparison: if `Q_a = V.withDensity a` and `Q_b = V.withDensity b` are probability
measures with `c · a ≤ b` a.e. (`c > 0`), then `H(P|Q_b) ≤ H(P|Q_a) - log c`, in real form. -/
theorem b15c_klDiv_withDensity_le {Ω : Type*} [MeasurableSpace Ω] (V P : Measure Ω) [SigmaFinite V]
    [IsProbabilityMeasure P] (a b : Ω → ℝ) (ha : Measurable a) (hb : Measurable b)
    (ha0 : ∀ᵐ x ∂V, 0 < a x) (hb0 : ∀ᵐ x ∂V, 0 < b x)
    (hna : ∫⁻ x, ENNReal.ofReal (a x) ∂V = 1) (hnb : ∫⁻ x, ENNReal.ofReal (b x) ∂V = 1)
    {c : ℝ} (hc : 0 < c) (hcab : ∀ᵐ x ∂V, c * a x ≤ b x)
    (hfin : klDiv P (V.withDensity fun x => ENNReal.ofReal (a x)) ≠ ⊤) :
    klDiv P (V.withDensity fun x => ENNReal.ofReal (b x)) ≠ ⊤ ∧
      (klDiv P (V.withDensity fun x => ENNReal.ofReal (b x))).toReal ≤
        (klDiv P (V.withDensity fun x => ENNReal.ofReal (a x))).toReal - Real.log c := by
  classical
  have hQprob : IsProbabilityMeasure (V.withDensity fun x => ENNReal.ofReal (a x)) := by
    constructor; rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hna]
  have hQeprob : IsProbabilityMeasure (V.withDensity fun x => ENNReal.ofReal (b x)) := by
    constructor; rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hnb]
  have hPQ : P ≪ V.withDensity fun x => ENNReal.ofReal (a x) := (klDiv_ne_top_iff.mp hfin).1
  have hPV : P ≪ V := hPQ.trans (withDensity_absolutelyContinuous _ _)
  have hPQe : P ≪ V.withDensity fun x => ENNReal.ofReal (b x) :=
    hPV.trans (withDensity_absolutelyContinuous'
      (ENNReal.measurable_ofReal.comp hb).aemeasurable
      (hb0.mono fun x hx => (ENNReal.ofReal_pos.mpr hx).ne'))
  rw [b15c_klDiv_withDensity_eq V P a ha ha0 hQprob hPQ] at hfin ⊢
  rw [b15c_klDiv_withDensity_eq V P b hb hb0 hQeprob hPQe]
  have hpm : Measurable (P.rnDeriv V) := Measure.measurable_rnDeriv P V
  have hPint : Integrable (fun x => (P.rnDeriv V x).toReal) V :=
    integrable_toReal_of_lintegral_ne_top hpm.aemeasurable (by
      rw [Measure.lintegral_rnDeriv hPV]; exact measure_ne_top P _)
  have hFm : Measurable (fun x => a x * klFun ((P.rnDeriv V x).toReal / a x)) :=
    ha.mul (measurable_klFun.comp (hpm.ennreal_toReal.div ha))
  have hGm : Measurable (fun x => b x * klFun ((P.rnDeriv V x).toReal / b x)) :=
    hb.mul (measurable_klFun.comp (hpm.ennreal_toReal.div hb))
  have hFnn : 0 ≤ᵐ[V] (fun x => a x * klFun ((P.rnDeriv V x).toReal / a x)) :=
    ha0.mono fun x hx => mul_nonneg hx.le
      (klFun_nonneg (div_nonneg ENNReal.toReal_nonneg hx.le))
  have hGnn : 0 ≤ᵐ[V] (fun x => b x * klFun ((P.rnDeriv V x).toReal / b x)) :=
    hb0.mono fun x hx => mul_nonneg hx.le
      (klFun_nonneg (div_nonneg ENNReal.toReal_nonneg hx.le))
  have hFint : Integrable (fun x => a x * klFun ((P.rnDeriv V x).toReal / a x)) V :=
    (lintegral_ofReal_ne_top_iff_integrable hFm.aestronglyMeasurable hFnn).mp hfin
  have hann : 0 ≤ᵐ[V] a := ha0.mono fun x hx => hx.le
  have hbnn : 0 ≤ᵐ[V] b := hb0.mono fun x hx => hx.le
  have haint : Integrable a V :=
    (lintegral_ofReal_ne_top_iff_integrable ha.aestronglyMeasurable hann).mp
      (by rw [hna]; exact ENNReal.one_ne_top)
  have hbint : Integrable b V :=
    (lintegral_ofReal_ne_top_iff_integrable hb.aestronglyMeasurable hbnn).mp
      (by rw [hnb]; exact ENNReal.one_ne_top)
  have hπint : ∫ x, (P.rnDeriv V x).toReal ∂V = 1 := by
    rw [Measure.integral_toReal_rnDeriv hPV]; simp
  have hintA : ∫ x, a x ∂V = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae hann ha.aestronglyMeasurable, hna]; simp
  have hintB : ∫ x, b x ∂V = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae hbnn hb.aestronglyMeasurable, hnb]; simp
  have hGH : ∀ᵐ x ∂V, b x * klFun ((P.rnDeriv V x).toReal / b x) ≤
      a x * klFun ((P.rnDeriv V x).toReal / a x) + (b x - a x) - Real.log c * (P.rnDeriv V x).toReal := by
    filter_upwards [ha0, hb0, hcab] with x h1 h2 h3
    exact b15c_real_klFun_ineq h1 h2 hc h3 ENNReal.toReal_nonneg
  have hFBA : Integrable (fun x => a x * klFun ((P.rnDeriv V x).toReal / a x) + (b x - a x)) V :=
    hFint.add (hbint.sub haint)
  have hBA : Integrable (fun x => b x - a x) V := hbint.sub haint
  have hHint : Integrable (fun x => a x * klFun ((P.rnDeriv V x).toReal / a x) + (b x - a x)
      - Real.log c * (P.rnDeriv V x).toReal) V :=
    hFBA.sub (hPint.const_mul (Real.log c))
  have hGint : Integrable (fun x => b x * klFun ((P.rnDeriv V x).toReal / b x)) V :=
    Integrable.mono' hHint hGm.aestronglyMeasurable (by
      filter_upwards [hGnn, hGH] with x h1 h2
      rw [Real.norm_of_nonneg h1]; exact h2)
  have hmono := integral_mono_of_nonneg hGnn hHint hGH
  have hHval : ∫ x, (a x * klFun ((P.rnDeriv V x).toReal / a x) + (b x - a x)
      - Real.log c * (P.rnDeriv V x).toReal) ∂V =
      ∫ x, a x * klFun ((P.rnDeriv V x).toReal / a x) ∂V - Real.log c := by
    have hPc : Integrable (fun x => Real.log c * (P.rnDeriv V x).toReal) V := hPint.const_mul _
    rw [integral_sub hFBA hPc, integral_add hFint hBA, integral_sub hbint haint,
      integral_const_mul, hintA, hintB, hπint]
    ring
  rw [← ofReal_integral_eq_lintegral_ofReal hGint hGnn,
    ← ofReal_integral_eq_lintegral_ofReal hFint hFnn]
  refine ⟨ENNReal.ofReal_ne_top, ?_⟩
  rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae hGnn),
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hFnn)]
  linarith [hmono, hHval]

/-- `b15c_gibbsRefGen` is a probability measure when its partition function is finite and nonzero. -/
theorem b15c_gibbsRefGen_isProb (invβ : ℝ) (U : Config d N → ℝ)
    (hZ : b15c_gibbsPartitionGen invβ U ≠ ⊤) (hZ0 : b15c_gibbsPartitionGen invβ U ≠ 0) :
    IsProbabilityMeasure (b15c_gibbsRefGen invβ U) := by
  constructor
  unfold b15c_gibbsRefGen
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hZ0 hZ

theorem b15c_measurable_totalPotential (D : DynData d) (hV : Continuous D.V) :
    Measurable (totalPotential (N := N) D) := by
  have hd := b15_one_le_d D
  have hg := CoercAux.measurable_periodicRiesz_one (d := d) (s := D.s) hd D.hs0 D.hsd
  unfold totalPotential
  refine Measurable.add (measurable_const.mul (Finset.measurable_sum _ fun i _ =>
    Finset.measurable_sum _ fun j _ => ?_)) (Finset.measurable_sum _ fun i _ =>
      hV.measurable.comp (measurable_pi_apply i))
  exact hg.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))

theorem b15c_measurable_gibbsWeightGen (invβ : ℝ) {U : Config d N → ℝ} (hU : Measurable U) :
    Measurable (b15c_gibbsWeightGen invβ U) := by
  unfold b15c_gibbsWeightGen
  exact Real.measurable_exp.comp (measurable_const.mul hU)

theorem b15c_gibbsWeightGen_pos (invβ : ℝ) (U : Config d N → ℝ) (X : Config d N) :
    0 < b15c_gibbsWeightGen invβ U X := Real.exp_pos _

/-- **Step 2, last inequality (B15-C target A)**: `𝓗_{G_{N,ε}}(P) ≤ 𝓗_G(P)` for every probability
measure `P`, from `G_{N,ε} ≥ G` and the partition bounds. -/
theorem b15c_gibbsEntropyGen_le_proof (D : DynData d) (hβ : 0 < D.invβ) (hV : Torus.IsCk 2 D.V) {M : ℝ}
    (hM : 0 ≤ M) (P : Measure (Config d N)) [IsProbabilityMeasure P] :
    b15c_gibbsEntropyGen D.invβ (b15c_potentialReg D M) P ≤ gibbsEntropy D P := by
  classical
  have hd := b15_one_le_d D
  have hVc := b15_continuous_of_isCk hV
  rw [b15c_gibbsEntropy_eq_gen D P]
  obtain ⟨hZpos, hZt⟩ := b15_gibbsPartition_pos_lt_top (N := N) D hV hβ
  obtain ⟨-, C, hC⟩ := b15c_partition_bounds (N := N) D hβ hV
  obtain ⟨hZle, -⟩ := hC M hM
  have hZeq : b15c_gibbsPartitionGen D.invβ (totalPotential (N := N) D) = gibbsPartition D N :=
    (b15c_gibbsPartition_eq_gen D).symm
  have hGt_ne_top : b15c_gibbsPartitionGen D.invβ (totalPotential (N := N) D) ≠ ⊤ := by
    rw [hZeq]; exact hZt.ne
  have hGt_ne_zero : b15c_gibbsPartitionGen D.invβ (totalPotential (N := N) D) ≠ 0 := by
    rw [hZeq]; exact hZpos.ne'
  have hGr_ne_top : b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D M) ≠ ⊤ := by
    intro h; rw [h, ENNReal.toReal_top] at hZle; linarith [ENNReal.toReal_pos hZpos.ne' hZt.ne]
  have hGr_ne_zero : b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D M) ≠ 0 := by
    intro h; rw [h, ENNReal.toReal_zero] at hZle; linarith [ENNReal.toReal_pos hZpos.ne' hZt.ne]
  have hAeq : (b15c_gibbsPartitionGen D.invβ (totalPotential (N := N) D)).toReal =
      (gibbsPartition D N).toReal := by rw [hZeq]
  have hApos : 0 < (b15c_gibbsPartitionGen D.invβ (totalPotential (N := N) D)).toReal := by
    rw [hAeq]; exact ENNReal.toReal_pos hZpos.ne' hZt.ne
  have hBpos : 0 < (b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D M)).toReal :=
    lt_of_lt_of_le hApos (by rw [hAeq]; exact hZle)
  have hAB : (b15c_gibbsPartitionGen D.invβ (totalPotential (N := N) D)).toReal ≤
      (b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D M)).toReal := by
    rw [hAeq]; exact hZle
  have hQ := b15c_gibbsRefGen_eq_withDensity D.invβ (totalPotential (N := N) D) hGt_ne_top hGt_ne_zero
  have hQe := b15c_gibbsRefGen_eq_withDensity D.invβ (b15c_potentialReg (N := N) D M) hGr_ne_top hGr_ne_zero
  have : IsProbabilityMeasure (b15c_gibbsRefGen D.invβ (totalPotential (N := N) D)) :=
    b15c_gibbsRefGen_isProb _ _ hGt_ne_top hGt_ne_zero
  have : IsProbabilityMeasure (b15c_gibbsRefGen D.invβ (b15c_potentialReg (N := N) D M)) :=
    b15c_gibbsRefGen_isProb _ _ hGr_ne_top hGr_ne_zero
  have hna : ∫⁻ X, ENNReal.ofReal
      ((b15c_gibbsPartitionGen D.invβ (totalPotential (N := N) D)).toReal⁻¹ *
        b15c_gibbsWeightGen D.invβ (totalPotential (N := N) D) X) ∂volume = 1 := by
    have h := measure_univ (μ := b15c_gibbsRefGen D.invβ (totalPotential (N := N) D))
    rw [hQ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
    exact h
  have hnb : ∫⁻ X, ENNReal.ofReal
      ((b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D M)).toReal⁻¹ *
        b15c_gibbsWeightGen D.invβ (b15c_potentialReg (N := N) D M) X) ∂volume = 1 := by
    have h := measure_univ (μ := b15c_gibbsRefGen D.invβ (b15c_potentialReg (N := N) D M))
    rw [hQe, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
    exact h
  have hmeasA : Measurable (fun X => (b15c_gibbsPartitionGen D.invβ (totalPotential (N := N) D)).toReal⁻¹ *
      b15c_gibbsWeightGen D.invβ (totalPotential (N := N) D) X) :=
    measurable_const.mul (b15c_measurable_gibbsWeightGen _ (b15c_measurable_totalPotential D hVc))
  have hmeasB : Measurable (fun X => (b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D M)).toReal⁻¹ *
      b15c_gibbsWeightGen D.invβ (b15c_potentialReg (N := N) D M) X) :=
    measurable_const.mul (b15c_measurable_gibbsWeightGen _
      (b15c_potentialReg_continuous (N := N) D hVc M).measurable)
  have hcab : ∀ᵐ X ∂(volume : Measure (Config d N)),
      ((b15c_gibbsPartitionGen D.invβ (totalPotential (N := N) D)).toReal /
          (b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D M)).toReal) *
        ((b15c_gibbsPartitionGen D.invβ (totalPotential (N := N) D)).toReal⁻¹ *
          b15c_gibbsWeightGen D.invβ (totalPotential (N := N) D) X) ≤
      (b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D M)).toReal⁻¹ *
        b15c_gibbsWeightGen D.invβ (b15c_potentialReg (N := N) D M) X := by
    filter_upwards [b15_ae_not_collision (N := N) hd] with X hX
    have hG : b15c_gibbsWeightGen D.invβ (totalPotential (N := N) D) X ≤
        b15c_gibbsWeightGen D.invβ (b15c_potentialReg (N := N) D M) X := by
      unfold b15c_gibbsWeightGen
      refine Real.exp_le_exp.mpr ?_
      have := b15c_potentialReg_le D M hX
      have hβ' : 0 < D.invβ⁻¹ := inv_pos.mpr hβ
      nlinarith
    have hA0 := hApos.ne'
    have hB0 := hBpos.ne'
    calc _ = b15c_gibbsWeightGen D.invβ (totalPotential (N := N) D) X /
          (b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D M)).toReal := by
          field_simp
      _ ≤ b15c_gibbsWeightGen D.invβ (b15c_potentialReg (N := N) D M) X /
          (b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D M)).toReal :=
          div_le_div_of_nonneg_right hG hBpos.le
      _ = _ := by rw [div_eq_inv_mul]
  have hc : 0 < (b15c_gibbsPartitionGen D.invβ (totalPotential (N := N) D)).toReal /
      (b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D M)).toReal :=
    div_pos hApos hBpos
  unfold b15c_gibbsEntropyGen relEntropy
  rw [hQ, hQe]
  have ha0 : ∀ᵐ X ∂(volume : Measure (Config d N)),
      0 < (b15c_gibbsPartitionGen D.invβ (totalPotential (N := N) D)).toReal⁻¹ *
        b15c_gibbsWeightGen D.invβ (totalPotential (N := N) D) X :=
    Filter.Eventually.of_forall fun X => mul_pos (inv_pos.mpr hApos) (b15c_gibbsWeightGen_pos _ _ _)
  have hb0 : ∀ᵐ X ∂(volume : Measure (Config d N)),
      0 < (b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D M)).toReal⁻¹ *
        b15c_gibbsWeightGen D.invβ (b15c_potentialReg (N := N) D M) X :=
    Filter.Eventually.of_forall fun X => mul_pos (inv_pos.mpr hBpos) (b15c_gibbsWeightGen_pos _ _ _)
  by_cases hfin : klDiv P (volume.withDensity fun X => ENNReal.ofReal
      ((b15c_gibbsPartitionGen D.invβ (totalPotential (N := N) D)).toReal⁻¹ *
        b15c_gibbsWeightGen D.invβ (totalPotential (N := N) D) X)) = ⊤
  · rw [hfin]; simp
  · obtain ⟨hne, hle⟩ := b15c_klDiv_withDensity_le volume P _ _ hmeasA hmeasB ha0 hb0 hna hnb hc hcab hfin
    rw [← EReal.coe_ennreal_toReal hne, ← EReal.coe_ennreal_toReal hfin, ← EReal.coe_sub,
      ← EReal.coe_sub, EReal.coe_le_coe_iff]
    rw [Real.log_div hApos.ne' hBpos.ne'] at hle
    linarith

example := (@b15c_gibbsEntropyGen_le_proof : type_of% @b15c_gibbsEntropyGen_le)

/-! ## Section F: `X^ε = X` on `[0,T]` eventually (target B) -/

/-- Pathwise uniqueness for the globally Lipschitz regularised lifted equation on `[0,T]`. -/
theorem b15c_regPath_unique (D : DynData d) (hV : Torus.IsCk 2 D.V) (M T : ℝ)
    (w : ℝ≥0 → (Fin N × Fin d) → ℝ) (hw : Continuous w) (y₀ : Fin N → Euc d)
    {y y' : ℝ → Fin N → Euc d}
    (hy : IsPathSolution (fun _ => b15c_liftedDriftReg D M) (liftedNoise (N := N) D) w y₀ ⊤ y)
    (hy' : IsPathSolution (fun _ => b15c_liftedDriftReg D M) (liftedNoise (N := N) D) w y₀
      (T : WithTop ℝ) y') :
    ∀ t : ℝ, 0 ≤ t → t < T → y t = y' t := by
  intro t ht htT
  exact ode_additive_unique Set.univ isOpen_univ _
    (b15c_liftedDriftReg_isLipschitz_proof D hV M).toLoc (liftedNoise (N := N) D) w hw y₀ hy hy'
    (fun _ _ _ => Set.mem_univ _) (fun _ _ _ => Set.mem_univ _) t ht
    (lt_min (WithTop.coe_lt_top t) (WithTop.coe_lt_coe.mpr htT))

/-- A lifted singular path solution on `[0,T]`, shifted by a lattice vector `c`, solves the
regularised equation as soon as the drifts agree along the shifted path. -/
theorem b15c_shift_isPathSolution {M T : ℝ} (D : DynData d) (w : ℝ≥0 → (Fin N × Fin d) → ℝ)
    (y : ℝ → Fin N → Euc d) (y₀ c : Fin N → Euc d) (hc : ∀ i, Torus.mk (c i) = 0)
    (hy : IsPathSolution (fun _ Z => liftedDrift D Z) (liftedNoise (N := N) D) w y₀ (T : WithTop ℝ) y)
    (hagree : ∀ s : ℝ, 0 ≤ s → s ≤ T → b15c_liftedDriftReg D M (y s - c) = liftedDrift D (y s - c)) :
    IsPathSolution (fun _ => b15c_liftedDriftReg D M) (liftedNoise (N := N) D) w (y₀ - c)
      (T : WithTop ℝ) (fun s => y s - c) := by
  obtain ⟨h0, hpath⟩ := hy
  refine ⟨by show y 0 - c = y₀ - c; rw [h0], fun t ht htT => ?_⟩
  have htT' : t ≤ T := (WithTop.coe_lt_coe.mp htT).le
  obtain ⟨hc1, hi1, heq1⟩ := hpath t ht htT
  have hsub : ∀ s ∈ Set.Icc (0 : ℝ) t,
      b15c_liftedDriftReg D M (y s - c) = liftedDrift D (y s) := fun s hs => by
    rw [hagree s hs.1 (hs.2.trans htT'), liftedDrift_sub_of_mk_eq_zero D (y s) c hc]
  refine ⟨hc1.sub continuousOn_const, hi1.congr_fun (fun s hs => (hsub s hs).symm) measurableSet_Icc, ?_⟩
  show y t - c = (y₀ - c) + (∫ s in Set.Icc (0 : ℝ) t, b15c_liftedDriftReg D M (y s - c)) +
    ∑ k, w (Real.toNNReal t) k • liftedNoise (N := N) D k
  have hI : ∫ s in Set.Icc (0 : ℝ) t, b15c_liftedDriftReg D M (y s - c) =
      ∫ s in Set.Icc (0 : ℝ) t, liftedDrift D (y s) :=
    setIntegral_congr_fun measurableSet_Icc (fun s hs => hsub s hs)
  have heq1' : y t = y₀ + (∫ s in Set.Icc (0 : ℝ) t, liftedDrift D (y s)) +
      ∑ k, w (Real.toNNReal t) k • liftedNoise (N := N) D k := heq1
  rw [hI, heq1']
  abel

theorem b15c_regularised_eq_strong_proof
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (D : DynData d) (hV : Torus.IsCk 2 D.V) {T : ℝ}
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} (hW : IsVectorBrownian P W)
    {X : ℝ≥0 → Ω → Config d N} (hS : IsStrongSolution P D T X₀ W X)
    (hWW' : ∀ᵐ ω ∂P, ∀ t i j, W' t ω (i, j) = W t ω i j)
    {Y₀ : Ω → Fin N → Euc d} (hY₀ : ∀ᵐ ω ∂P, (fun i => Torus.mk (Y₀ ω i)) = X₀ ω)
    {M : ℕ → ℝ} (hM : Tendsto M atTop atTop)
    {Y : ℕ → ℝ → Ω → (Fin N → Euc d)}
    (hY : ∀ n, IsAdditiveSDESolution P ℱ W' (fun _ => b15c_liftedDriftReg D (M n)) (liftedNoise D)
      Y₀ (fun _ => ⊤) (Y n)) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ t : ℝ≥0, (t : ℝ) ≤ T → b15c_regProcess (Y n) t ω = X t ω := by
  obtain ⟨Yx, hXeq, hYx⟩ := IsStrongSolution.exists_lift_isPathSolution P D T X₀ W hW X hS
  have hsep := particle_uniform_separation P D T X₀ W X hS
  have hYeq := ae_all_iff.2 fun n => (hY n).eq
  subst hXeq
  filter_upwards [hYx, hsep, hYeq, hWW', hS.init, hY₀, hS.cont, hW.ae_cont] with ω hpath' hsepω hYω hWω hinitX hY0ω hcontX hwc
  obtain ⟨hpath, -⟩ := hpath'
  obtain ⟨c₀, hc₀, hsepc⟩ := hsepω
  obtain ⟨M₀, hM₀⟩ := b15c_liftedDriftReg_eq_of_sep D hc₀
  -- the constant lattice shift `c` matching the initial lifts
  set c : Fin N → Euc d := Yx 0 ω - Y₀ ω with hcdef
  have hcmk : ∀ i, Torus.mk (c i) = 0 := by
    intro i
    have h1 : Torus.mk (Yx 0 ω i) = X₀ ω i := by
      have := congrFun hinitX i
      exact this
    have h2 : Torus.mk (Y₀ ω i) = X₀ ω i := congrFun hY0ω i
    simp only [hcdef, Pi.sub_apply, mk_sub', h1, h2, sub_self]
  have hcinit : Yx 0 ω - c = Y₀ ω := sub_sub_cancel _ _
  refine (hM.eventually (eventually_ge_atTop M₀)).mono fun n hn => ?_
  -- drift agreement along the shifted lift
  have hagree : ∀ s : ℝ, 0 ≤ s → s ≤ T →
      b15c_liftedDriftReg D (M n) (Yx (Real.toNNReal s) ω - c) =
        liftedDrift D (Yx (Real.toNNReal s) ω - c) := by
    intro s hs0 hsT
    refine hM₀ (M n) hn _ fun i j hij => ?_
    have h := hsepc (Real.toNNReal s) (by rw [Real.coe_toNNReal _ hs0]; exact hsT) i j hij
    have e : ∀ k, Torus.mk ((Yx (Real.toNNReal s) ω - c) k) = Torus.mk (Yx (Real.toNNReal s) ω k) := by
      intro k; rw [Pi.sub_apply, mk_sub', hcmk k, sub_zero]
    rw [e i, e j]
    exact h
  have hshift := b15c_shift_isPathSolution (M := M n) (T := T) D (fun t => toCoords W t ω)
    (fun s => Yx (Real.toNNReal s) ω) (Yx 0 ω) c hcmk hpath hagree
  rw [hcinit] at hshift
  -- the regularised solution `Y n` at level `M n`, as a path solution with the Brownian path `W`
  have hpathY : IsPathSolution (fun _ => b15c_liftedDriftReg D (M n)) (liftedNoise (N := N) D)
      (fun t => toCoords W t ω) (Y₀ ω) ⊤ (fun t => Y n t ω) := by
    refine ⟨(hY n).init ω, fun t ht _ => ?_⟩
    obtain ⟨hint, heq⟩ := hYω n t ht (WithTop.coe_lt_top t)
    refine ⟨(hY n).cont ω t ht (WithTop.coe_lt_top t), hint, ?_⟩
    have hn : ∑ k, ofNNRealTime W' t ω k • liftedNoise (N := N) D k =
        ∑ k, toCoords W (Real.toNNReal t) ω k • liftedNoise (N := N) D k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      exact hWω (Real.toNNReal t) k.1 k.2
    show Y n t ω = Y₀ ω + (∫ s in Set.Icc (0 : ℝ) t, b15c_liftedDriftReg D (M n) (Y n s ω)) +
      ∑ k, toCoords W (Real.toNNReal t) ω k • liftedNoise (N := N) D k
    rw [heq, hn]
  have hunq := b15c_regPath_unique D hV (M n) T (fun t => toCoords W t ω) hwc (Y₀ ω) hpathY hshift
  have hpt : ∀ s : ℝ, 0 ≤ s → s < T →
      (fun i => Torus.mk (Y n s ω i)) = (fun i => Torus.mk (Yx (Real.toNNReal s) ω i)) := by
    intro s hs0 hsT
    funext i
    rw [hunq s hs0 hsT]
    show Torus.mk ((Yx (Real.toNNReal s) ω - c) i) = Torus.mk (Yx (Real.toNNReal s) ω i)
    rw [Pi.sub_apply, mk_sub', hcmk i, sub_zero]
  have hfun : ∀ s : ℝ, 0 ≤ s → s ≤ T →
      (fun i => Torus.mk (Y n s ω i)) = (fun i => Torus.mk (Yx (Real.toNNReal s) ω i)) := by
    intro s hs0 hsT
    by_cases hT0 : T = 0
    · have hs : s = 0 := by linarith
      subst hs
      rw [Real.toNNReal_zero, (hY n).init ω, hY0ω]
      exact hinitX.symm
    · have hTnn : 0 ≤ T := hs0.trans hsT
      have hTpos : 0 < T := lt_of_le_of_ne hTnn (Ne.symm hT0)
      have hYc : ContinuousOn (fun u : ℝ => Y n u ω) (Set.Icc 0 T) :=
        (hY n).cont ω T hTnn (WithTop.coe_lt_top T)
      have hcont1 : ContinuousOn (fun u : ℝ => fun i => Torus.mk (Y n u ω i)) (Set.Icc 0 T) := by
        refine continuousOn_pi.2 fun i => ?_
        exact Torus.continuous_mk.comp_continuousOn ((continuous_apply i).comp_continuousOn hYc)
      have hcont2 : ContinuousOn (fun u : ℝ => fun i => Torus.mk (Yx (Real.toNNReal u) ω i))
          (Set.Icc 0 T) := by
        refine continuousOn_pi.2 fun i => ?_
        exact ((hcontX i).comp continuous_real_toNNReal).continuousOn
      have hEq : Set.EqOn (fun u : ℝ => fun i => Torus.mk (Y n u ω i))
          (fun u : ℝ => fun i => Torus.mk (Yx (Real.toNNReal u) ω i)) (Set.Ico 0 T) :=
        fun u hu => hpt u hu.1 hu.2
      have hEq' := Set.EqOn.of_subset_closure hEq hcont1 hcont2 Set.Ico_subset_Icc_self
        (by rw [closure_Ico hTpos.ne])
      exact hEq' ⟨hs0, hsT⟩
  intro t ht
  have hfun' := hfun t (NNReal.coe_nonneg t) ht
  rw [Real.toNNReal_coe] at hfun'
  exact hfun'

example := (@b15c_regularised_eq_strong_proof : type_of% @b15c_regularised_eq_strong)

end HRS
