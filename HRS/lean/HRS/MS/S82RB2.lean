import HRS.MS.S82RB1

/-!
# S8.2 R01B (S82R), part 2: probability and the conditional domination of the pinned laws
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82R
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ} {a beta C0 : ℝ} {rho q : Euc d → ℝ} {h : ℕ → Euc d → ℝ}

/-- Abstract Jensen/tilt domination: tilting by `u - r` with `u ≤ M`, `∫ u ≥ -M1`, `0 ≤ r`, `∫ r ≤ R`
is dominated by `e^(M+M1+R)` times the measure with density `exp(-r)`. -/
lemma s82r_tilt_le {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    (u r : E → ℝ) (hum : Measurable u) (hrm : Measurable r) (hui : Integrable u μ)
    (hri : Integrable r μ) (hr0 : ∀ x, 0 ≤ r x) {M M1 R : ℝ} (hM : ∀ x, u x ≤ M)
    (h1 : -M1 ≤ ∫ x, u x ∂μ) (hR : ∫ x, r x ∂μ ≤ R) :
    exponentialTilt μ (fun y => u y - r y) ≤
      ENNReal.ofReal (Real.exp (M + M1 + R)) • μ.withDensity (fun y => ENNReal.ofReal (Real.exp (-r y))) := by
  have hvm : Measurable (fun y => u y - r y) := hum.sub hrm
  have hvi : Integrable (fun y => u y - r y) μ := hui.sub hri
  have hexpi : Integrable (fun y => Real.exp (u y - r y)) μ := by
    refine Integrable.of_bound (Real.measurable_exp.comp hvm).aestronglyMeasurable (Real.exp M)
      (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by linarith [hM y, hr0 y])
  have hjen : Real.exp (∫ y, (u y - r y) ∂μ) ≤ ∫ y, Real.exp (u y - r y) ∂μ :=
    convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
      (ae_of_all _ fun _ => Set.mem_univ _) hvi hexpi
  have hI : -(M1 + R) ≤ ∫ y, (u y - r y) ∂μ := by
    rw [integral_sub hui hri]; linarith
  have hZ : Real.exp (-(M1 + R)) ≤ ∫ y, Real.exp (u y - r y) ∂μ :=
    (Real.exp_le_exp.2 hI).trans hjen
  have hZpos : 0 < ∫ y, Real.exp (u y - r y) ∂μ := (Real.exp_pos _).trans_le hZ
  refine Measure.le_iff.2 fun A hA => ?_
  unfold exponentialTilt
  rw [Measure.smul_apply, withDensity_apply _ hA, Measure.smul_apply, withDensity_apply _ hA,
    smul_eq_mul, smul_eq_mul]
  have hinv : (ENNReal.ofReal (∫ y, Real.exp (u y - r y) ∂μ))⁻¹ ≤
      ENNReal.ofReal (Real.exp (M1 + R)) := by
    rw [← ENNReal.ofReal_inv_of_pos hZpos]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [inv_le_comm₀ hZpos (Real.exp_pos _), ← Real.exp_neg]
    exact hZ
  calc (ENNReal.ofReal (∫ y, Real.exp (u y - r y) ∂μ))⁻¹ *
        ∫⁻ y in A, ENNReal.ofReal (Real.exp (u y - r y)) ∂μ
      ≤ ENNReal.ofReal (Real.exp (M1 + R)) *
        ∫⁻ y in A, ENNReal.ofReal (Real.exp M) * ENNReal.ofReal (Real.exp (-r y)) ∂μ := by
        refine mul_le_mul' hinv (lintegral_mono fun y => ?_)
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Real.exp_add]
        exact Real.exp_le_exp.2 (by linarith [hM y])
    _ = ENNReal.ofReal (Real.exp (M + M1 + R)) *
        ∫⁻ y in A, ENNReal.ofReal (Real.exp (-r y)) ∂μ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 3
        ring


lemma s82r_col_int (hd : 2 ≤ d) (hq : ShortRangePole d q) {G c : ℝ} (hG : 0 < G)
    (hρ : HRS.Whole.IsProbDensity rho) (hρG : HRS.Whole.HasR2GaussianUpper G c rho) (x : Euc d) :
    Integrable (fun y => q (y - x)) (HRS.Whole.withDensityReal rho) :=
  HRS.MS.S82P2.s82p2_q_integrable hd hq G c hG hρG.1 rho hρ hρG x

lemma s82r_col_le (hbeta : 0 < beta) (hD : CalibratedReferenceData d a beta rho q h C0) (x : Euc d) :
    ∫ y, q (y - x) ∂(HRS.Whole.withDensityReal rho) ≤ 1 / (1000 * beta) := by
  have e : ∫ y, q (y - x) ∂(HRS.Whole.withDensityReal rho) =
      HRS.Whole.convMeasure q (HRS.Whole.withDensityReal rho) x := by
    unfold HRS.Whole.convMeasure
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    show q (y - x) = q (x - y)
    rw [← hD.short.even (x - y), neg_sub]
  rw [e]
  exact s82r_row_le hbeta hD x

/-- The conditional density bound with the explicit constant `e^(2.002)`. -/
lemma s82r_conditional_core (hd : 2 ≤ d) (hbeta : 0 < beta)
    (hD : CalibratedReferenceData d a beta rho q h C0)
    {G c : ℝ} (hG : 0 < G) (hρ : HRS.Whole.IsProbDensity rho)
    (hρG : HRS.Whole.HasR2GaussianUpper G c rho) {N : ℕ} (hN : 2 ≤ N) {p n : ℕ}
    (hnp : n + p ≤ N) (pins : Fin p → Euc d) (i : Fin n) (X : EucConfig d n) :
    resampleLaw q h (HRS.Whole.withDensityReal rho) beta N pins i X ≤
      ENNReal.ofReal (Real.exp (1 + 1 / 1000 + 1 + 1 / 1000)) •
        (HRS.Whole.withDensityReal rho).withDensity (fun y =>
          ENNReal.ofReal (Real.exp (-(beta / N) *
            ((∑ j ∈ Finset.univ.erase i, q (y - X j)) + ∑ j, q (y - pins j))))) := by
  haveI := s82r_isProb hρ
  set μ := HRS.Whole.withDensityReal rho with hμ
  have hq := hD.short
  have hfield := s82r_isField hd hbeta hD hG hρ hρG hN
  set r : Euc d → ℝ := fun y => (beta / N) * ((∑ j ∈ Finset.univ.erase i, q (y - X j)) +
    ∑ j, q (y - pins j)) with hr
  have hqm : ∀ x : Euc d, Measurable (fun y => q (y - x)) := fun x =>
    hq.measurable.comp (measurable_id.sub_const x)
  have hrm : Measurable r :=
    ((Finset.measurable_sum _ fun j _ => hqm (X j)).add
      (Finset.measurable_sum _ fun j _ => hqm (pins j))).const_mul _
  have hri : Integrable r μ :=
    ((integrable_finset_sum _ fun j _ => s82r_col_int hd hq hG hρ hρG (X j)).add
      (integrable_finset_sum _ fun j _ => s82r_col_int hd hq hG hρ hρG (pins j))).const_mul _
  have hr0 : ∀ y, 0 ≤ r y := fun y =>
    mul_nonneg (div_nonneg hbeta.le (Nat.cast_nonneg N))
      (add_nonneg (Finset.sum_nonneg fun j _ => hq.nonneg _) (Finset.sum_nonneg fun j _ => hq.nonneg _))
  have hrint : ∫ y, r y ∂μ ≤ 1 / 1000 := by
    have e : ∫ y, r y ∂μ = (beta / N) * ((∑ j ∈ Finset.univ.erase i, ∫ y, q (y - X j) ∂μ) +
        ∑ j, ∫ y, q (y - pins j) ∂μ) := by
      rw [hr]
      simp only
      rw [integral_const_mul, integral_add
        (integrable_finset_sum _ fun j _ => s82r_col_int hd hq hG hρ hρG (X j))
        (integrable_finset_sum _ fun j _ => s82r_col_int hd hq hG hρ hρG (pins j)),
        integral_finset_sum _ fun j _ => s82r_col_int hd hq hG hρ hρG (X j),
        integral_finset_sum _ fun j _ => s82r_col_int hd hq hG hρ hρG (pins j)]
    rw [e]
    have hA := s82r_col_le hbeta hD
    have h1 : ∑ j ∈ Finset.univ.erase i, ∫ y, q (y - X j) ∂μ ≤
        ∑ _j ∈ Finset.univ.erase i, 1 / (1000 * beta) := Finset.sum_le_sum fun j _ => hA _
    have h2 : ∑ j, ∫ y, q (y - pins j) ∂μ ≤ ∑ _j : Fin p, 1 / (1000 * beta) :=
      Finset.sum_le_sum fun j _ => hA _
    have hc1 : ((Finset.univ.erase i).card : ℝ) ≤ n := by
      have := Finset.card_erase_le (s := (Finset.univ : Finset (Fin n))) (a := i)
      simp only [Finset.card_univ, Fintype.card_fin] at this
      exact_mod_cast this
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1 h2
    have hnpR : (n : ℝ) + p ≤ N := by exact_mod_cast hnp
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hAn : 0 ≤ 1 / (1000 * beta) := by positivity
    calc (beta / N) * ((∑ j ∈ Finset.univ.erase i, ∫ y, q (y - X j) ∂μ) +
          ∑ j, ∫ y, q (y - pins j) ∂μ)
        ≤ (beta / N) * (((Finset.univ.erase i).card : ℝ) * (1 / (1000 * beta)) +
            (p : ℝ) * (1 / (1000 * beta))) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)
      _ ≤ (beta / N) * ((n : ℝ) * (1 / (1000 * beta)) + (p : ℝ) * (1 / (1000 * beta))) := by
          gcongr
      _ = (beta / N) * (((n : ℝ) + p) * (1 / (1000 * beta))) := by ring
      _ ≤ (beta / N) * ((N : ℝ) * (1 / (1000 * beta))) := by gcongr
      _ = 1 / 1000 := by field_simp
  have := s82r_tilt_le μ (s82r_phi q h μ beta N) r hfield.measurable hrm hfield.integrable hri hr0
    hfield.le hfield.ge hrint
  have e : (fun y => s82r_phi q h μ beta N y - r y) = fun y => beta * HRS.Whole.convMeasure q μ y +
      h N y - (beta / N) * ((∑ j ∈ Finset.univ.erase i, q (y - X j)) + ∑ j, q (y - pins j)) := rfl
  unfold resampleLaw
  rw [← e]
  refine this.trans (le_of_eq ?_)
  congr 3
  funext y
  simp only [hr, neg_mul]

end HRS.MS.S82R

end
