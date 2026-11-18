import HRS.Commutator.Torus.NRSTAux13

/-!
# NRS-T, part 14: `L^p` contraction of Fejér mollification and its Fourier coefficients
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators ComplexConjugate ENNReal

namespace HRS.Commutator.TorusNote.NRST

open HRS HRS.Commutator

variable {d : ℕ}

lemma lintegral_conv_rpow_le {F A : Torus d → ℝ≥0∞} (hF : Measurable F) (hA : Measurable A)
    (hF1 : ∫⁻ z, F z = 1) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ z, F z * A z) ^ p ≤ ∫⁻ z, F z * A z ^ p := by
  rcases hp.eq_or_lt with rfl | hp1
  · simp
  · have hpq : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp1
    set q := p.conjExponent with hqdef
    have hq : q.HolderConjugate p := hpq.symm
    have hp0 : 0 < p := by linarith
    have hq0 : 0 < q := hq.pos
    have hsum : 1 / q + 1 / p = 1 := by
      have := hpq.inv_add_inv_eq_one
      rw [add_comm] at this
      simpa [one_div] using this
    have hpt : ∀ z, F z ^ (1 / q) * (F z ^ (1 / p) * A z) = F z * A z := by
      intro z
      rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity), hsum,
        ENNReal.rpow_one]
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure (Torus d)) hq
      (f := fun z => F z ^ (1 / q)) (g := fun z => F z ^ (1 / p) * A z)
      (hF.pow_const _).aemeasurable ((hF.pow_const _).mul hA).aemeasurable
    have e1 : ∫⁻ z, (F z ^ (1 / q)) ^ q = 1 := by
      simp_rw [← ENNReal.rpow_mul]
      have : ∀ z, F z ^ (1 / q * q) = F z := fun z => by
        rw [one_div, inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one]
      simp_rw [this]; exact hF1
    have e2 : ∫⁻ z, (F z ^ (1 / p) * A z) ^ p = ∫⁻ z, F z * A z ^ p := by
      refine lintegral_congr fun z => ?_
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul]
      rw [one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
    have e3 : ∫⁻ z, (fun z => F z ^ (1 / q) * (F z ^ (1 / p) * A z)) z = ∫⁻ z, F z * A z := by
      refine lintegral_congr fun z => ?_
      exact hpt z
    have h' : ∫⁻ z, F z * A z ≤ (∫⁻ z, F z * A z ^ p) ^ (1 / p) := by
      calc ∫⁻ z, F z * A z = ∫⁻ z, ((fun z => F z ^ (1 / q)) * (fun z => F z ^ (1 / p) * A z)) z := by
            refine lintegral_congr fun z => ?_
            simp only [Pi.mul_apply]; exact (hpt z).symm
        _ ≤ _ := h
        _ = (∫⁻ z, F z * A z ^ p) ^ (1 / p) := by rw [e1, e2, ENNReal.one_rpow, one_mul]
    calc (∫⁻ z, F z * A z) ^ p ≤ ((∫⁻ z, F z * A z ^ p) ^ (1 / p)) ^ p :=
          ENNReal.rpow_le_rpow h' hp0.le
      _ = ∫⁻ z, F z * A z ^ p := by
          rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]

lemma fjF_lintegral (n : ℕ) : ∫⁻ z : Torus d, ENNReal.ofReal (fj d n z) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (fj_integrable n) (Filter.Eventually.of_forall (fj_nonneg n)),
    fj_integral, ENNReal.ofReal_one]

lemma integrable_moll_of_integrable {w : Torus d → Euc d} (hw : Integrable w) (n : ℕ) (x : Torus d) :
    Integrable (fun z => fj d n z • w (x - z)) := by
  have h1 : Integrable (fun z => w (x - z)) := by
    have := hw.comp_sub_left x
    exact this
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn (fj_cont n (d := d)).continuousOn
  exact h1.bdd_smul B (fj_cont n).aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
    simpa using hB z (Set.mem_univ z))

lemma eLpNorm_mollV_le {w : Torus d → Euc d} (hw : AEStronglyMeasurable w volume) {p : ℝ}
    (hp : 1 ≤ p) (n : ℕ) :
    eLpNorm (mollV n w) (ENNReal.ofReal p) volume ≤ eLpNorm w (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := by linarith
  have hpne : ENNReal.ofReal p ≠ 0 := by simp [hp0]
  have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  set w' := hw.mk w with hw'
  have hw'm : StronglyMeasurable w' := hw.stronglyMeasurable_mk
  have hae : w =ᵐ[volume] w' := hw.ae_eq_mk
  have hmoll : mollV n w = mollV n w' := by
    funext x
    unfold mollV
    refine integral_congr_ae ?_
    have hmp : MeasurePreserving (fun z : Torus d => x - z) volume volume :=
      (volume : Measure (Torus d)).measurePreserving_sub_left x
    have := hae.comp_tendsto hmp.quasiMeasurePreserving.tendsto_ae
    filter_upwards [this] with z hz
    simp only [Function.comp] at hz
    rw [hz]
  rw [hmoll, eLpNorm_congr_ae hae]
  have hmoll_meas : AEStronglyMeasurable (mollV n w') volume := by
    have hG : StronglyMeasurable (Function.uncurry fun (x z : Torus d) => fj d n z • w' (x - z)) :=
      (((fj_cont n).measurable.comp measurable_snd).stronglyMeasurable).smul
        (hw'm.comp_measurable (measurable_fst.sub measurable_snd))
    exact (hG.integral_prod_right' (ν := (volume : Measure (Torus d)))).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne hpt hmoll_meas,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hpne hpt hw'm.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le]
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  set F : Torus d → ℝ≥0∞ := fun z => ENNReal.ofReal (fj d n z) with hF
  have hFm : Measurable F := (fj_cont n).measurable.ennreal_ofReal
  have hw'meas : Measurable w' := hw'm.measurable
  have hpoint : ∀ x : Torus d, ‖mollV n w' x‖ₑ ^ p ≤ ∫⁻ z, F z * ‖w' (x - z)‖ₑ ^ p := by
    intro x
    have h1 : ‖mollV n w' x‖ₑ ≤ ∫⁻ z, F z * ‖w' (x - z)‖ₑ := by
      unfold mollV
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      refine lintegral_congr fun z => ?_
      rw [enorm_smul, hF]
      simp only [Real.enorm_eq_ofReal_abs, abs_of_nonneg (fj_nonneg n z)]
    refine (ENNReal.rpow_le_rpow h1 hp0.le).trans ?_
    exact lintegral_conv_rpow_le hFm (hw'meas.enorm.comp (measurable_const.sub measurable_id))
      (fjF_lintegral n) hp
  calc ∫⁻ x, ‖mollV n w' x‖ₑ ^ p ≤ ∫⁻ x, ∫⁻ z, F z * ‖w' (x - z)‖ₑ ^ p := lintegral_mono hpoint
    _ = ∫⁻ z, ∫⁻ x, F z * ‖w' (x - z)‖ₑ ^ p := by
        refine lintegral_lintegral_swap ?_
        exact (hFm.comp measurable_snd).mul
          (((hw'meas.enorm.comp (measurable_fst.sub measurable_snd)).pow_const p)) |>.aemeasurable
    _ = ∫⁻ z, F z * ∫⁻ x, ‖w' x‖ₑ ^ p := by
        refine lintegral_congr fun z => ?_
        have hmz : Measurable fun x : Torus d => ‖w' (x - z)‖ₑ ^ p :=
          (hw'meas.enorm.comp (measurable_id.sub measurable_const)).pow_const p
        rw [lintegral_const_mul _ hmz]
        congr 1
        exact lintegral_sub_right_eq_self (fun x => ‖w' x‖ₑ ^ p) z
    _ = ∫⁻ x, ‖w' x‖ₑ ^ p := by
        rw [lintegral_mul_const _ hFm, fjF_lintegral, one_mul]

end HRS.Commutator.TorusNote.NRST
