import HRS.PDE.MovSpec3
import HRS.PDE.MovAAux8

/-!
# MOVF Aux1: the entropy split `H(ν|Q_N) = H(ν|μ^{⊗N}) + βN∫F_N dν + log K_N`

* `movf_kl_tilted`: general statement about `klDiv ν (P.tilted f)` for `f` measurable and bounded above.
* `movf_energy_facts`: `F_N` is measurable and bounded below (all `X`) for a continuous probability density.
* `movf_modGibbs_eq_tilted`: `modulatedGibbs = P.tilted (-βN F_N)`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movf_integrable_min_llr {α : Type*} [MeasurableSpace α] (P ν : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure ν] (hνP : ν ≪ P) :
    Integrable (fun x => min (llr ν P x) 0) ν := by
  have hm : Measurable fun x => min (llr ν P x) 0 := (measurable_llr ν P).min measurable_const
  rw [← integrable_rnDeriv_smul_iff hνP]
  refine Integrable.of_bound (C := 1) ((((Measure.measurable_rnDeriv ν P).ennreal_toReal).smul hm).aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, llr_def, Real.norm_eq_abs]
  set g := (ν.rnDeriv P x).toReal with hg
  have hg0 : 0 ≤ g := ENNReal.toReal_nonneg
  have hk := klFun_nonneg hg0
  rw [klFun_apply] at hk
  by_cases h : 0 ≤ Real.log g
  · rw [min_eq_right h, mul_zero]; simp
  · push Not at h
    rw [min_eq_left h.le]
    have h1 : g * Real.log g ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hg0 h.le
    rw [abs_of_nonpos h1]
    have : g ≤ 1 := by
      by_contra hc
      push Not at hc
      exact absurd (Real.log_pos hc) (not_lt.2 h.le)
    linarith

theorem movf_kl_tilted {α : Type*} [MeasurableSpace α] (P ν : Measure α) [IsProbabilityMeasure P]
    [IsProbabilityMeasure ν] {f : α → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, f x ≤ C) :
    (klDiv ν (P.tilted f) ≠ ⊤ ↔ klDiv ν P ≠ ⊤ ∧ Integrable f ν) ∧
    (klDiv ν P ≠ ⊤ ∧ Integrable f ν →
      (klDiv ν (P.tilted f)).toReal =
        (klDiv ν P).toReal - ∫ x, f x ∂ν + Real.log (∫ x, Real.exp (f x) ∂P)) := by
  have hexp : Integrable (fun x => Real.exp (f x)) P :=
    Integrable.of_bound (C := Real.exp C) (Real.measurable_exp.comp hf).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 (hC x))
  haveI : IsProbabilityMeasure (P.tilted f) := isProbabilityMeasure_tilted hexp
  have hPQ : P ≪ P.tilted f := absolutelyContinuous_tilted hexp
  have hQP : P.tilted f ≪ P := tilted_absolutelyContinuous P f
  refine ⟨⟨fun h => ?_, fun ⟨h1, h2⟩ => ?_⟩, fun ⟨h1, h2⟩ => ?_⟩
  · obtain ⟨hνQ, hint⟩ := klDiv_ne_top_iff.1 h
    have hνP : ν ≪ P := hνQ.trans hQP
    have e := llr_tilted_right hνP hexp
    set c := Real.log (∫ z, Real.exp (f z) ∂P) with hc
    have hu : Integrable (fun x => llr ν (P.tilted f) x + C - c) ν :=
      (hint.add (integrable_const _)).sub (integrable_const _)
    have hmin := movf_integrable_min_llr P ν hνP
    have hllr : Integrable (llr ν P) ν := by
      refine Integrable.mono' (hu.abs.add hmin.abs) (measurable_llr ν P).aestronglyMeasurable ?_
      filter_upwards [e] with x hx
      simp only [Pi.add_apply, Real.norm_eq_abs]
      have h1 : llr ν P x ≤ llr ν (P.tilted f) x + C - c := by
        have := hC x
        linarith
      have h2 : min (llr ν P x) 0 ≤ llr ν P x := min_le_left _ _
      by_cases h0 : 0 ≤ llr ν P x
      · rw [abs_of_nonneg h0]
        have := le_abs_self (llr ν (P.tilted f) x + C - c)
        have := abs_nonneg (min (llr ν P x) 0)
        linarith
      · push Not at h0
        rw [abs_of_neg h0, min_eq_left h0.le, abs_of_neg h0]
        have := abs_nonneg (llr ν (P.tilted f) x + C - c)
        linarith
    refine ⟨klDiv_ne_top hνP hllr, ?_⟩
    have : Integrable (fun x => llr ν P x + c - llr ν (P.tilted f) x) ν :=
      (hllr.add (integrable_const _)).sub hint
    refine this.congr ?_
    filter_upwards [e] with x hx
    rw [hx]; ring
  · obtain ⟨hνP, hint⟩ := klDiv_ne_top_iff.1 h1
    exact klDiv_ne_top (hνP.trans hPQ) (integrable_llr_tilted_right hνP h2 hint hexp)
  · obtain ⟨hνP, hint⟩ := klDiv_ne_top_iff.1 h1
    rw [toReal_klDiv (hνP.trans hPQ) (integrable_llr_tilted_right hνP h2 hint hexp),
      toReal_klDiv hνP hint, integral_llr_tilted_right hνP h2 hexp hint]
    simp [probReal_univ]

theorem movf_measurable_pair {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    Measurable (Function.uncurry fun x y : Torus d => periodicRiesz d s (x - y)) :=
  (CoercAux.measurable_periodicRiesz_one hd hs0 hsd).comp (measurable_fst.sub measurable_snd)

theorem movf_energy_facts (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρ : IsProbDensity ρ) (hc : Continuous ρ) (hN : 0 < N) :
    Measurable (fun X : Config d N => modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ)) ∧
    ∃ C : ℝ, ∀ X : Config d N, -C ≤ modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ) := by
  haveI := isProb_withDensityReal hρ
  obtain ⟨Λ, hΛ⟩ := isCompact_univ.exists_bound_of_continuousOn (f := ρ) hc.continuousOn
  have hΛ0 : 0 ≤ max Λ 0 := le_max_right _ _
  have hρΛ : ∀ x, ρ x ≤ max Λ 0 := fun x =>
    (le_abs_self _).trans (((hΛ x trivial).trans (le_max_left _ _)))
  have hW : Integrable (fun z => |periodicRiesz d s z|) :=
    (mova_integrable_periodicRiesz hd hs0 hsd).abs
  obtain ⟨hrow, hbound⟩ := rowOK_of_dom (ρ := ρ) hΛ0 hρΛ hW
    (k := fun x y : Torus d => periodicRiesz d s (x - y)) (movf_measurable_pair hd hs0 hsd)
    (fun x y => le_rfl)
  refine ⟨measurable_modulatedEnergy hrow, ?_⟩
  obtain ⟨B0, hB0⟩ := periodicRiesz_ge_of_one_le (d := d) hd hs0 hsd
  set B := |B0| with hB
  have hBg : ∀ z, -B ≤ periodicRiesz d s z := fun z => by
    have := hB0 z; have := le_abs_self B0; linarith
  have hB0' : 0 ≤ B := abs_nonneg _
  set Rb := max Λ 0 * ∫ z, |periodicRiesz d s z| with hRb
  have hRb0 : 0 ≤ Rb := mul_nonneg hΛ0 (integral_nonneg fun z => abs_nonneg _)
  have hrw : ∀ x : Torus d, |∫ y, periodicRiesz d s (x - y) ∂(withDensityReal ρ)| ≤ Rb := fun x =>
    abs_integral_le_integral_abs.trans (hbound x)
  refine ⟨B / 2 + Rb + Rb / 2, fun X => ?_⟩
  unfold modulatedEnergyKernel modulatedEnergy
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : -(B * (N : ℝ) ^ 2) ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, periodicRiesz d s (X i - X j) := by
    have : ∀ i : Fin N, -(B * N) ≤ ∑ j ∈ Finset.univ.erase i, periodicRiesz d s (X i - X j) := by
      intro i
      have h2 : ∑ j ∈ Finset.univ.erase i, (-B) ≤ ∑ j ∈ Finset.univ.erase i, periodicRiesz d s (X i - X j) :=
        Finset.sum_le_sum fun j _ => hBg _
      refine le_trans ?_ h2
      rw [Finset.sum_const, nsmul_eq_mul]
      have hc : ((Finset.univ.erase i).card : ℝ) ≤ N := by
        have := Finset.card_erase_le (s := (Finset.univ : Finset (Fin N))) (a := i)
        simp only [Finset.card_univ, Fintype.card_fin] at this
        exact_mod_cast this
      nlinarith
    have h3 := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => this i
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
    nlinarith
  have hT1 : -(B / 2) ≤ (1 / (2 * (N : ℝ) ^ 2)) *
      ∑ i, ∑ j ∈ Finset.univ.erase i, periodicRiesz d s (X i - X j) := by
    have hpos : 0 < 1 / (2 * (N : ℝ) ^ 2) := by positivity
    have := mul_le_mul_of_nonneg_left h1 hpos.le
    have e : 1 / (2 * (N : ℝ) ^ 2) * -(B * (N : ℝ) ^ 2) = -(B / 2) := by field_simp
    linarith
  have hT2 : (1 / (N : ℝ)) * ∑ i, ∫ y, periodicRiesz d s (X i - y) ∂(withDensityReal ρ) ≤ Rb := by
    have : ∑ i, ∫ y, periodicRiesz d s (X i - y) ∂(withDensityReal ρ) ≤ N * Rb := by
      have := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
        (le_abs_self _).trans (hrw (X i))
      simpa using this
    have hpos : 0 < 1 / (N : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left this hpos.le
    have e : 1 / (N : ℝ) * (N * Rb) = Rb := by field_simp
    linarith
  have hT3 : -Rb ≤ ∫ x, ∫ y, periodicRiesz d s (x - y) ∂(withDensityReal ρ) ∂(withDensityReal ρ) := by
    have := norm_integral_le_of_norm_le_const (μ := withDensityReal ρ)
      (f := fun x => ∫ y, periodicRiesz d s (x - y) ∂(withDensityReal ρ)) (C := Rb)
      (Eventually.of_forall fun x => by simpa using hrw x)
    simp only [probReal_univ, mul_one] at this
    have := (abs_le.1 (by simpa using this)).1
    linarith
  linarith

theorem movf_modGibbs_eq_tilted (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρ : IsProbDensity ρ) (hc : Continuous ρ) (hN : 0 < N) {β : ℝ} (hβ : 0 ≤ β) :
    modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ) =
      (Measure.pi fun _ : Fin N => withDensityReal ρ).tilted
        (fun X => -β * N * modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ)) := by
  haveI := isProb_withDensityReal hρ
  obtain ⟨hm, C, hC⟩ := movf_energy_facts hd hs0 hsd hρ hc hN (N := N)
  set P := Measure.pi fun _ : Fin N => withDensityReal ρ with hP
  set f : Config d N → ℝ := fun X => -β * N * modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ)
    with hf
  have hfm : Measurable f := measurable_const.mul hm
  have hfC : ∀ X, f X ≤ β * N * C := fun X => by
    have := hC X
    have h0 : 0 ≤ β * N := by positivity
    simp only [hf]
    nlinarith
  have hexp : Integrable (fun x => Real.exp (f x)) P :=
    Integrable.of_bound (C := Real.exp (β * N * C)) (Real.measurable_exp.comp hfm).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 (hfC x))
  have hK : 0 < ∫ x, Real.exp (f x) ∂P := integral_exp_pos hexp
  unfold modulatedGibbs Measure.tilted
  have hKdef : gibbsNormalizer (periodicRiesz d s) N β (withDensityReal ρ) = ∫ x, Real.exp (f x) ∂P := rfl
  rw [hKdef]
  have e : (fun x => ENNReal.ofReal (Real.exp (f x) / ∫ x, Real.exp (f x) ∂P)) =
      (ENNReal.ofReal (∫ x, Real.exp (f x) ∂P))⁻¹ • fun x => ENNReal.ofReal (Real.exp (f x)) := by
    funext x
    rw [ENNReal.ofReal_div_of_pos hK]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [ENNReal.div_eq_inv_mul]
  rw [e, withDensity_smul' _ _ (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hK).ne')]

end HRS

end
