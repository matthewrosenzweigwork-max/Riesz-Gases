import HRS.MS.S82P2Mar2

/-!
# S8.2 (S82P2): means of centered functions under pinned one-site marginals
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

instance s82p2_ref_sfinite {d p n : ℕ} (q : Euc d → ℝ) (h : ℕ → Euc d → ℝ)
    (mu : Measure (Euc d)) [SigmaFinite mu] (beta : ℝ) (N : ℕ) (pins : Fin p → Euc d) :
    SFinite (referenceLaw q h mu beta N n pins) := by
  unfold referenceLaw exponentialTilt
  infer_instance

lemma s82p2_marg_le_smul {d : ℕ} {beta C1 : ℝ} {rho : Euc d → ℝ} {q : Euc d → ℝ}
    {h : ℕ → Euc d → ℝ} [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)]
    (hP : PinComparison beta rho q h C1) {N : ℕ} (hN : 2 ≤ N) {p n : ℕ} (hp : p ≤ 2)
    (hnp : n + p ≤ N) (hNn : N - (n + p) ≤ 2) (pins : Fin p → Euc d) (i : Fin n)
    (hprob : IsProbabilityMeasure
      (referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins)) :
    (referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins).map (fun X => X i) ≤
      ENNReal.ofReal (1 + 2 * C1) • HRS.Whole.withDensityReal rho := by
  refine Measure.le_iff.2 fun s hs => ?_
  have := s82p2_marg_lintegral_le hP hN hp hnp hNn pins i hprob (s.indicator 1)
    (measurable_one.indicator hs)
  simpa [lintegral_indicator_one hs] using this

lemma s82p2_marg_mean_abs_le {d : ℕ} {beta C1 : ℝ} {rho : Euc d → ℝ} {q : Euc d → ℝ}
    {h : ℕ → Euc d → ℝ} [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)]
    (hP : PinComparison beta rho q h C1) {N : ℕ} (hN : 2 ≤ N) {p n : ℕ} (hp : p ≤ 2)
    (hnp : n + p ≤ N) (hNn : N - (n + p) ≤ 2) (pins : Fin p → Euc d) (i : Fin n)
    (hprob : IsProbabilityMeasure
      (referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins))
    (ψ : Euc d → ℝ) (hψm : Measurable ψ) (hψi : Integrable ψ (HRS.Whole.withDensityReal rho))
    (hψ0 : ∫ z, ψ z ∂HRS.Whole.withDensityReal rho = 0)
    (hint : Integrable (fun z => |ψ z| * (C1 * Phase2S82.deltaN N +
      C1 * min 1 ((1 + ∑ j, q (z - pins j)) / N))) (HRS.Whole.withDensityReal rho)) :
    |∫ z, ψ z ∂((referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins).map
        (fun X => X i))| ≤
      ∫ z, |ψ z| * (C1 * Phase2S82.deltaN N +
        C1 * min 1 ((1 + ∑ j, q (z - pins j)) / N)) ∂HRS.Whole.withDensityReal rho := by
  set mu := HRS.Whole.withDensityReal rho with hmu
  haveI : IsProbabilityMeasure mu := by rw [hmu]; infer_instance
  set ν := (referenceLaw q h mu beta N n pins).map (fun X => X i) with hν
  set r : Euc d → ℝ := fun z => (ν.rnDeriv mu z).toReal with hr
  have hrm : Measurable r := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hac : ν ≪ mu := s82p2_marg_ac q h mu beta N pins i
  haveI : IsProbabilityMeasure ν :=
    ⟨by rw [hν, Measure.map_apply (measurable_pi_apply i) MeasurableSet.univ]; simp⟩
  haveI : Measure.HaveLebesgueDecomposition ν mu := Measure.haveLebesgueDecomposition_of_sigmaFinite ν mu
  have e1 : ∫ z, ψ z ∂ν = ∫ z, r z * ψ z ∂mu := (integral_toReal_rnDeriv_mul hac).symm
  have hdev := s82p2_rn_dev hP hN hp hnp hNn pins i
  have hI : Integrable (fun z => (r z - 1) * ψ z) mu := by
    refine hint.mono' ((hrm.sub measurable_const).mul hψm).aestronglyMeasurable ?_
    filter_upwards [hdev] with z hz
    rw [Real.norm_eq_abs, abs_mul, mul_comm (|ψ z|)]
    exact mul_le_mul_of_nonneg_right hz (abs_nonneg _)
  have e2 : ∫ z, r z * ψ z ∂mu = ∫ z, (r z - 1) * ψ z ∂mu := by
    have : (fun z => r z * ψ z) = fun z => (r z - 1) * ψ z + ψ z := by
      funext z; ring
    rw [this, integral_add hI hψi, hψ0, add_zero]
  rw [e1, e2]
  refine (abs_integral_le_integral_abs).trans (integral_mono_ae hI.abs hint ?_)
  filter_upwards [hdev] with z hz
  rw [abs_mul, mul_comm (|ψ z|)]
  exact mul_le_mul_of_nonneg_right hz (abs_nonneg _)

end HRS.MS.S82P2
