import HRS.MS.R26T8AC01b

/-!
# S8.2 observed-time layer, packet T8A.C01c: one-site partition function of the fractional law
For fixed others `X'`, the one-site exponent `psi = beta conv + h - (beta/N) sum q(. - X') - sum w q(. - pins)` is
measurable, at most `1 + 1/1000`, and its exponential has mean at least `exp (-1 - 1/1000)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.R26T8A
open HRS.MS.Phase2S82

theorem r26t8a_c01_site {d p m : ℕ} (hd : 2 ≤ d) {a beta C0 : ℝ} (ha : 0 < a) (hbeta : 0 < beta)
    {rho q : Euc d → ℝ} {h : ℕ → Euc d → ℝ}
    (hrho : HRS.Whole.IsThermalEquilibrium d (criticalS d) a beta rho)
    (hW : WeakReferenceSetup d a beta rho q h C0) (N : ℕ) (hN : 2 ≤ N)
    (hh1 : ∀ x, |h N x| ≤ 1) (hnp : m + p ≤ N) (pins : Fin p → Euc d) (weights : Fin p → ℝ)
    (hw : ∀ j, 0 ≤ weights j ∧ weights j ≤ beta / N) (X' : Fin m → Euc d) :
    Measurable (fun y => beta * HRS.Whole.convMeasure q (HRS.Whole.withDensityReal rho) y + h N y -
        ((beta / N) * ∑ l, q (y - X' l) + ∑ j, weights j * q (y - pins j))) ∧
    (∀ y, beta * HRS.Whole.convMeasure q (HRS.Whole.withDensityReal rho) y + h N y -
        ((beta / N) * ∑ l, q (y - X' l) + ∑ j, weights j * q (y - pins j)) ≤ 1 + 1 / 1000) ∧
    Real.exp (-1 - 1 / 1000) ≤ ∫ y, Real.exp (beta * HRS.Whole.convMeasure q
        (HRS.Whole.withDensityReal rho) y + h N y -
        ((beta / N) * ∑ l, q (y - X' l) + ∑ j, weights j * q (y - pins j)))
        ∂HRS.Whole.withDensityReal rho ∧
    ∫⁻ y, ENNReal.ofReal (Real.exp (beta * HRS.Whole.convMeasure q
        (HRS.Whole.withDensityReal rho) y + h N y -
        ((beta / N) * ∑ l, q (y - X' l) + ∑ j, weights j * q (y - pins j))))
        ∂HRS.Whole.withDensityReal rho =
      ENNReal.ofReal (∫ y, Real.exp (beta * HRS.Whole.convMeasure q
        (HRS.Whole.withDensityReal rho) y + h N y -
        ((beta / N) * ∑ l, q (y - X' l) + ∑ j, weights j * q (y - pins j)))
        ∂HRS.Whole.withDensityReal rho) := by
  haveI hμ : IsProbabilityMeasure (HRS.Whole.withDensityReal rho) :=
    HRS.Whole.Q09A.measure_isProb hrho.2.1
  set μ : Measure (Euc d) := HRS.Whole.withDensityReal rho with hμdef
  have hq := hW.short
  have hqm : Measurable q := hq.measurable
  have hhm : Measurable (h N) := hW.hmeas N
  have hconv := HRS.MS.S82P2.s82p2_conv_measurable hqm μ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hint := r26t8a_c01_qint hd ha hbeta hrho hq
  have hmass := r26t8a_c01_qmass hW hbeta
  set f : Euc d → ℝ := fun y => beta * HRS.Whole.convMeasure q μ y + h N y with hf
  set S : Euc d → ℝ := fun y => (beta / N) * ∑ l, q (y - X' l) + ∑ j, weights j * q (y - pins j) with hS
  have hfm : Measurable f := (measurable_const.mul hconv).add hhm
  have hSnn : ∀ y, 0 ≤ S y := fun y => add_nonneg
    (mul_nonneg (div_nonneg hbeta.le hNpos.le) (Finset.sum_nonneg fun l _ => hq.nonneg _))
    (Finset.sum_nonneg fun j _ => mul_nonneg (hw j).1 (hq.nonneg _))
  have hSm : Measurable S := by
    simp only [hS]
    exact (measurable_const.mul (Finset.measurable_sum _ fun l _ => hqm.comp (measurable_id.sub_const _))).add
      (Finset.measurable_sum _ fun j _ => measurable_const.mul (hqm.comp (measurable_id.sub_const _)))
  have hi1 : ∀ l ∈ (Finset.univ : Finset (Fin m)), Integrable (fun y => q (y - X' l)) μ :=
    fun l _ => hint (X' l)
  have hi2 : ∀ j ∈ (Finset.univ : Finset (Fin p)), Integrable (fun y => weights j * q (y - pins j)) μ :=
    fun j _ => (hint (pins j)).const_mul _
  have hSint : Integrable S μ :=
    ((integrable_finset_sum _ hi1).const_mul (beta / N)).add (integrable_finset_sum _ hi2)
  have hSmass : ∫ y, S y ∂μ ≤ 1 / 1000 := by
    simp only [hS]
    rw [integral_add ((integrable_finset_sum _ hi1).const_mul (beta / N)) (integrable_finset_sum _ hi2),
      integral_const_mul, integral_finset_sum _ hi1, integral_finset_sum _ hi2]
    have hB : (0 : ℝ) ≤ 1 / (1000 * beta) := by positivity
    have e1 : ∑ l, ∫ y, q (y - X' l) ∂μ ≤ (m : ℝ) * (1 / (1000 * beta)) := by
      have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin m)) (fun l => ∫ y, q (y - X' l) ∂μ)
        (1 / (1000 * beta)) fun l _ => hmass (X' l)
      simpa using this
    have e2 : ∑ j, ∫ y, weights j * q (y - pins j) ∂μ ≤ (p : ℝ) * ((beta / N) * (1 / (1000 * beta))) := by
      have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin p))
        (fun j => ∫ y, weights j * q (y - pins j) ∂μ) ((beta / N) * (1 / (1000 * beta))) fun j _ => by
          rw [integral_const_mul]
          exact mul_le_mul (hw j).2 (hmass (pins j)) (integral_nonneg fun z => hq.nonneg _) (by positivity)
      simpa using this
    have hmp : (m : ℝ) + p ≤ N := by exact_mod_cast hnp
    have h3 : (beta / N) * ((m : ℝ) * (1 / (1000 * beta))) + (p : ℝ) * ((beta / N) * (1 / (1000 * beta))) =
        (beta / N) * (((m : ℝ) + p) * (1 / (1000 * beta))) := by ring
    have h4 : (beta / N) * (((m : ℝ) + p) * (1 / (1000 * beta))) ≤ (beta / N) * ((N : ℝ) * (1 / (1000 * beta))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmp hB) (by positivity)
    have h5 : (beta / N) * ((N : ℝ) * (1 / (1000 * beta))) = 1 / 1000 := by field_simp
    have h6 : (beta / N) * ∑ l, ∫ y, q (y - X' l) ∂μ ≤ (beta / N) * ((m : ℝ) * (1 / (1000 * beta))) :=
      mul_le_mul_of_nonneg_left e1 (by positivity)
    linarith
  have hf1 : ∀ y, f y ≤ 1 + 1 / 1000 := fun y => by
    have h1 := hW.small_row y
    have h2 := (abs_le.1 (hh1 y)).2
    simp only [hf]; linarith
  have hf2 : ∀ y, -1 ≤ f y := fun y => by
    have h1 : 0 ≤ beta * HRS.Whole.convMeasure q μ y :=
      mul_nonneg hbeta.le (integral_nonneg fun z => hq.nonneg _)
    have h2 := (abs_le.1 (hh1 y)).1
    simp only [hf]; linarith
  obtain ⟨-, hlow, hl⟩ := r26t8a_c01_Zlow μ f S hfm hSm hSnn hSint hf1 hf2 hSmass
  refine ⟨hfm.sub hSm, fun y => ?_, hlow, hl⟩
  have := hSnn y
  have := hf1 y
  simp only [hf, hS] at *
  linarith

end HRS.MS.R26T8A
