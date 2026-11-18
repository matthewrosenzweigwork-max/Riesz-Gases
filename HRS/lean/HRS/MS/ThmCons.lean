import HRS.MS.ThmConsAux2
import HRS.Whole.Static

/-!
# C-B: proof of `HRS.Whole.euc_thermal_moments` (`0 < s < d`, `d ≥ 2`)

Both clauses follow from `thermalDensity ≤ C γ` and Gaussian integrability (`ThmConsAux2`).

Also `cb_euc_thermal_gaussian_bounds_of_poincare`: the conclusion of `euc_thermal_gaussian_bounds` (two-sided Gaussian
comparison and the Poincare inequality for `μ_β`) from the Gaussian Poincare inequality `CbGaussPoincare d a β κ` for the
reference measure `γ dx` (the separate Maurey-Pisier packet C-POI; it is not in Mathlib or the repo).  The transfer from
`γ` to `μ_β` is done here (`cb_poincare_transfer`) with `c = e^{-β M B}` and `C' = C (1 + κ)`; enlarging the upper constant
is harmless since the upper bound only gets weaker.

Also `cb_admissible_of_smooth`: `isAdmissiblePerturbation_thermal` follows from `ContDiff ℝ ∞ thermalDensity`
(the first conjunct of the frozen, sorried `euc_thermal_regularity`) together with the lower Gaussian bound of
`ThmConsAux1`; the smoothness itself is NOT proved here (C-REG packets).
-/

open MeasureTheory
open scoped ContDiff ENNReal

noncomputable section

namespace HRS.MS.Thm

open HRS.Whole

variable {d : ℕ}

/-- **C-B (moments).** Proof of `HRS.Whole.euc_thermal_moments`. -/
theorem euc_thermal_moments_proof : type_of% @HRS.Whole.euc_thermal_moments := by
  intro d s hd hs0 hsd a β ha hβ
  have hd1 : 1 ≤ d := by omega
  exact ⟨fun b hb => cb_thermal_exp_moment hd1 hs0 hsd ha hβ hb,
    fun p hp => cb_thermal_poly_moment hd1 hs0 hsd ha hβ hp⟩

/-- `isAdmissiblePerturbation_thermal` from the smoothness of `thermalDensity` (supplied by C-REG):
`√ρ ψ` is a smooth compactly supported (`ρ ≥ c γ > 0`), hence Schwartz, hence in every `Σ^m`. -/
theorem cb_admissible_of_smooth (hd : 1 ≤ d) {s a β : ℝ} (hs0 : 0 < s) (hsd : s < d) (ha : 0 < a)
    (hβ : 0 < β) (hsm : ContDiff ℝ ∞ (thermalDensity d s a β)) (εstar : ℝ) (hε : 0 < εstar)
    (ψ : Euc d → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (h0 : ψ ≠ 0)
    (hmean : ∫ x, ψ x * thermalDensity d s a β x = 0) :
    ∃ ε₀ > 0, ∀ ε : ℝ, |ε| ≤ ε₀ →
      IsAdmissiblePerturbation (thermalDensity d s a β) εstar ε ψ := by
  obtain ⟨-, c, C, hc0, -, hcC⟩ := cb_thermal_two_sided hd hs0 hsd ha hβ
  have hγ : ∀ x : Euc d, 0 < gaussianComparison d a β x := fun x => by
    unfold gaussianComparison
    have : 0 < β * a / (2 * Real.pi) := by positivity
    positivity
  have hpos : ∀ x, thermalDensity d s a β x ≠ 0 := fun x =>
    (lt_of_lt_of_le (mul_pos hc0 (hγ x)) (hcC x).1).ne'
  have hsq : ContDiff ℝ ∞ fun x => Real.sqrt (thermalDensity d s a β x) := hsm.sqrt hpos
  have hg : ContDiff ℝ ∞ fun x => Real.sqrt (thermalDensity d s a β x) * ψ x := hsq.mul hψ
  have hgc : HasCompactSupport fun x => Real.sqrt (thermalDensity d s a β x) * ψ x :=
    hc.mul_left
  refine isAdmissiblePerturbation_of_small _ εstar hε ψ hψ hc h0 hmean ?_
  exact memOsc_schwartz _ (hgc.toSchwartzMap hg)

/-! ### Transfer of a Gaussian Poincare inequality to `μ_β` -/

/-- The Gaussian Poincare inequality for `γ_{βa} dx` with constant `κ / (β a)` (hypothesis of the conditional result). -/
def CbGaussPoincare (d : ℕ) (a β κ : ℝ) : Prop :=
  ∀ f : Euc d → ℝ, ContDiff ℝ 1 f → MemLp f 2 (HRS.Whole.withDensityReal (gaussianComparison d a β)) →
    Integrable (fun x => ‖gradient f x‖ ^ 2) (HRS.Whole.withDensityReal (gaussianComparison d a β)) →
      ProbabilityTheory.variance f (HRS.Whole.withDensityReal (gaussianComparison d a β)) ≤
        κ / (β * a) * ∫ x, ‖gradient f x‖ ^ 2 ∂(HRS.Whole.withDensityReal (gaussianComparison d a β))

lemma cb_withDensityReal_isProb {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) :
    IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := by
  constructor
  unfold HRS.Whole.withDensityReal
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hi : Integrable ρ := Integrable.of_integral_ne_zero (by rw [hρ.integral_one]; norm_num)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hρ.nonneg), hρ.integral_one]
  simp

lemma cb_withDensityReal_le_smul {ρ ρ' : Euc d → ℝ} {C : ℝ} (hρ' : Measurable ρ') (hC : 0 ≤ C)
    (h : ∀ x, ρ x ≤ C * ρ' x) :
    HRS.Whole.withDensityReal ρ ≤ ENNReal.ofReal C • HRS.Whole.withDensityReal ρ' := by
  unfold HRS.Whole.withDensityReal
  have hm : Measurable fun x => ENNReal.ofReal (ρ' x) := hρ'.ennreal_ofReal
  rw [← withDensity_smul _ hm]
  refine withDensity_mono (ae_of_all _ fun x => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul hC]
  exact ENNReal.ofReal_le_ofReal (h x)

/-- Transfer of a Poincare inequality: if `c γ ≤ ρ ≤ C γ` and `γ dx` satisfies `Var ≤ κ/(βa) ∫|∇f|²`, then
`ρ dx` satisfies `Var ≤ C (1+κ) / (c β a) ∫|∇f|²`. -/
theorem cb_poincare_transfer {a β κ c C : ℝ} (ha : 0 < a) (hβ : 0 < β) (hκ : 0 ≤ κ) (hc : 0 < c)
    (hC : 0 < C) (hP : CbGaussPoincare d a β κ) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    (hb : ∀ x, c * gaussianComparison d a β x ≤ ρ x ∧ ρ x ≤ C * gaussianComparison d a β x)
    {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) (hf2 : MemLp f 2 (HRS.Whole.withDensityReal ρ))
    (hg : Integrable (fun x => ‖gradient f x‖ ^ 2) (HRS.Whole.withDensityReal ρ)) :
    ProbabilityTheory.variance f (HRS.Whole.withDensityReal ρ) ≤
      C * (1 + κ) / (c * β * a) * ∫ x, ‖gradient f x‖ ^ 2 ∂(HRS.Whole.withDensityReal ρ) := by
  set G := HRS.Whole.withDensityReal (gaussianComparison d a β) with hG
  set μ := HRS.Whole.withDensityReal ρ with hμ
  haveI : IsProbabilityMeasure μ := cb_withDensityReal_isProb hρ
  haveI : IsProbabilityMeasure G := cb_withDensityReal_isProb (gaussianComparison_isProbDensity ha hβ)
  have hγm := gaussianComparison_measurable (d := d) a β
  have hGμ : G ≤ ENNReal.ofReal c⁻¹ • μ := by
    refine cb_withDensityReal_le_smul hρ.measurable (inv_nonneg.2 hc.le) fun x => ?_
    have := (hb x).1
    rw [← mul_le_mul_iff_of_pos_left hc, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    exact this
  have hμG : μ ≤ ENNReal.ofReal C • G :=
    cb_withDensityReal_le_smul hγm hC.le fun x => (hb x).2
  have hf2G : MemLp f 2 G := (hf2.smul_measure ENNReal.ofReal_ne_top).mono_measure hGμ
  have hgG : Integrable (fun x => ‖gradient f x‖ ^ 2) G :=
    (hg.smul_measure ENNReal.ofReal_ne_top).mono_measure hGμ
  have hfm : AEMeasurable f μ := hf.continuous.measurable.aemeasurable
  have hfmG : AEMeasurable f G := hf.continuous.measurable.aemeasurable
  set m := ∫ x, f x ∂G with hm
  have h1 : ProbabilityTheory.variance f μ ≤ ∫ x, (f x - m) ^ 2 ∂μ := by
    have e := ProbabilityTheory.variance_sub_const (μ := μ) (X := f) hfm.aestronglyMeasurable m
    have := ProbabilityTheory.variance_le_expectation_sq (μ := μ) (X := fun x => f x - m)
      (hfm.sub_const m).aestronglyMeasurable
    rw [e] at this
    simpa using this
  have hsqG : Integrable (fun x => (f x - m) ^ 2) G :=
    (hf2G.sub (memLp_const m)).integrable_sq
  have h2 : ∫ x, (f x - m) ^ 2 ∂μ ≤ C * ∫ x, (f x - m) ^ 2 ∂G := by
    have hsq' : Integrable (fun x => (f x - m) ^ 2) (ENNReal.ofReal C • G) :=
      hsqG.smul_measure ENNReal.ofReal_ne_top
    calc ∫ x, (f x - m) ^ 2 ∂μ ≤ ∫ x, (f x - m) ^ 2 ∂(ENNReal.ofReal C • G) :=
          integral_mono_measure hμG (ae_of_all _ fun x => sq_nonneg _) hsq'
      _ = C * ∫ x, (f x - m) ^ 2 ∂G := by
          rw [integral_smul_measure, ENNReal.toReal_ofReal hC.le, smul_eq_mul]
  have h3 : ∫ x, (f x - m) ^ 2 ∂G = ProbabilityTheory.variance f G :=
    (ProbabilityTheory.variance_eq_integral hfmG).symm
  have h4 := hP f hf hf2G hgG
  have h5 : ∫ x, ‖gradient f x‖ ^ 2 ∂G ≤ c⁻¹ * ∫ x, ‖gradient f x‖ ^ 2 ∂μ := by
    have hg' : Integrable (fun x => ‖gradient f x‖ ^ 2) (ENNReal.ofReal c⁻¹ • μ) :=
      hg.smul_measure ENNReal.ofReal_ne_top
    calc ∫ x, ‖gradient f x‖ ^ 2 ∂G ≤ ∫ x, ‖gradient f x‖ ^ 2 ∂(ENNReal.ofReal c⁻¹ • μ) :=
          integral_mono_measure hGμ (ae_of_all _ fun x => sq_nonneg _) hg'
      _ = c⁻¹ * ∫ x, ‖gradient f x‖ ^ 2 ∂μ := by
          rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.2 hc.le), smul_eq_mul]
  have hI : 0 ≤ ∫ x, ‖gradient f x‖ ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hκβ : 0 ≤ κ / (β * a) := by positivity
  calc ProbabilityTheory.variance f μ ≤ C * ProbabilityTheory.variance f G := by
        rw [← h3]; exact h1.trans h2
    _ ≤ C * (κ / (β * a) * (c⁻¹ * ∫ x, ‖gradient f x‖ ^ 2 ∂μ)) :=
        mul_le_mul_of_nonneg_left (h4.trans (mul_le_mul_of_nonneg_left h5 hκβ)) hC.le
    _ = (C * κ) / (c * β * a) * ∫ x, ‖gradient f x‖ ^ 2 ∂μ := by field_simp
    _ ≤ C * (1 + κ) / (c * β * a) * ∫ x, ‖gradient f x‖ ^ 2 ∂μ := by
        apply mul_le_mul_of_nonneg_right _ hI
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith

/-- **Conditional form of `euc_thermal_gaussian_bounds`**: the two-sided comparison and the Poincare inequality for
`μ_β`, given the Gaussian Poincare inequality for `γ` (not proved here). -/
theorem cb_euc_thermal_gaussian_bounds_of_poincare (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d)
    (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) {κ : ℝ} (hκ : 0 ≤ κ) (hP : CbGaussPoincare d a β κ) :
    ∃ c > 0, ∃ C : ℝ,
      (∀ x, c * gaussianComparison d a β x ≤ thermalDensity d s a β x ∧
        thermalDensity d s a β x ≤ C * gaussianComparison d a β x) ∧
      ∀ f : Euc d → ℝ, ContDiff ℝ 1 f → MemLp f 2 (thermalMeasure d s a β) →
        Integrable (fun x => ‖gradient f x‖ ^ 2) (thermalMeasure d s a β) →
        ProbabilityTheory.variance f (thermalMeasure d s a β) ≤
          C / (c * β * a) * ∫ x, ‖gradient f x‖ ^ 2 ∂(thermalMeasure d s a β) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hρ, c, C, hc, hC, hb⟩ := cb_thermal_two_sided hd1 hs0 hsd ha hβ
  refine ⟨c, hc, C * (1 + κ), ?_, fun f hf hf2 hg => ?_⟩
  · intro x
    refine ⟨(hb x).1, (hb x).2.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (by nlinarith) (gaussianComparison_pos ha hβ x).le
  · exact cb_poincare_transfer ha hβ hκ hc hC hP hρ hb hf hf2 hg


end HRS.MS.Thm

end
