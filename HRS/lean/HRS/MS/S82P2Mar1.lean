import HRS.MS.S82P2Dis4

/-!
# S8.2 (S82P2): one-site marginals of the pinned weak reference laws
Absolute continuity, the ae density bound `|rn - 1| <= C1 (delta_N + min 1 ((1 + sum q)/N))`
from `PinComparison`, and the corresponding transfer of lintegrals.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

lemma s82p2_ref_ac {d p n : ℕ} (q : Euc d → ℝ) (h : ℕ → Euc d → ℝ)
    (mu : Measure (Euc d)) [SigmaFinite mu] (beta : ℝ) (N : ℕ) (pins : Fin p → Euc d) :
    referenceLaw q h mu beta N n pins ≪ Measure.pi fun _ : Fin n => mu := by
  unfold referenceLaw exponentialTilt
  exact (Measure.smul_absolutelyContinuous).trans (withDensity_absolutelyContinuous _ _)

lemma s82p2_marg_ac {d p n : ℕ} (q : Euc d → ℝ) (h : ℕ → Euc d → ℝ)
    (mu : Measure (Euc d)) [SigmaFinite mu] (beta : ℝ) (N : ℕ) (pins : Fin p → Euc d)
    (i : Fin n) :
    (referenceLaw q h mu beta N n pins).map (fun X => X i) ≪ mu := by
  have h1 := (s82p2_ref_ac (n := n) q h mu beta N pins).map (measurable_pi_apply i)
  exact h1.trans ((Measure.quasiMeasurePreserving_eval (fun _ : Fin n => mu) i).absolutelyContinuous)

lemma s82p2_deltaN_le_one {N : ℕ} (hN : 1 ≤ N) : Phase2S82.deltaN N ≤ 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  unfold Phase2S82.deltaN Phase2S82.logN
  rw [div_le_one hNpos, Real.log_mul (Real.exp_pos 1).ne' hNpos.ne', Real.log_exp]
  have := Real.log_le_sub_one_of_pos hNpos
  linarith

lemma s82p2_deltaN_nonneg {N : ℕ} (hN : 1 ≤ N) : 0 ≤ Phase2S82.deltaN N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  unfold Phase2S82.deltaN Phase2S82.logN
  apply div_nonneg _ hNpos.le
  rw [Real.log_mul (Real.exp_pos 1).ne' hNpos.ne', Real.log_exp]
  have : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  linarith

/-- `PinComparison` forces `0 ≤ C1` (on a probability space). -/
lemma s82p2_pinCmp_nonneg {d : ℕ} {beta C1 : ℝ} {rho : Euc d → ℝ} {q : Euc d → ℝ}
    {h : ℕ → Euc d → ℝ} [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)]
    (hP : PinComparison beta rho q h C1) : 0 ≤ C1 := by
  have := (hP.2 2 le_rfl 0 2 (by norm_num) (by norm_num) (by norm_num) (fun i => i.elim0)
    ⟨0, by norm_num⟩).exists
  obtain ⟨z, hz⟩ := this
  have hz' := (abs_nonneg _).trans hz
  simp at hz'
  exact hz'


/-- The refMarginal density is uniformly close to one. -/
lemma s82p2_refMarg_dev {d : ℕ} {beta C1 : ℝ} {rho : Euc d → ℝ} {q : Euc d → ℝ}
    {h : ℕ → Euc d → ℝ} [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)]
    (hP : PinComparison beta rho q h C1) {N : ℕ} (hN : 2 ≤ N) :
    ∀ᵐ z ∂HRS.Whole.withDensityReal rho,
      |((refMarginal q h (HRS.Whole.withDensityReal rho) beta N).rnDeriv
        (HRS.Whole.withDensityReal rho) z).toReal - 1| ≤ C1 * Phase2S82.deltaN N := by
  have hC1 := s82p2_pinCmp_nonneg hP
  have hδ := s82p2_deltaN_nonneg (N := N) (by omega)
  have h1 := hP.1 N hN
  have h2 := enorm_ae_le_eLpNormEssSup (fun x => ((refMarginal q h (HRS.Whole.withDensityReal rho)
    beta N).rnDeriv (HRS.Whole.withDensityReal rho) x).toReal - 1) (HRS.Whole.withDensityReal rho)
  filter_upwards [h2] with z hz
  have h3 := hz.trans ((eLpNormEssSup_le_eLpNorm_top).trans h1)
  rw [Real.enorm_eq_ofReal_abs] at h3
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC1 hδ)).1 h3

/-- Density of a pinned one-site marginal against `mu`: ae bound on `|rn - 1|`. -/
lemma s82p2_rn_dev {d : ℕ} {beta C1 : ℝ} {rho : Euc d → ℝ} {q : Euc d → ℝ}
    {h : ℕ → Euc d → ℝ} [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)]
    (hP : PinComparison beta rho q h C1) {N : ℕ} (hN : 2 ≤ N) {p n : ℕ} (hp : p ≤ 2)
    (hnp : n + p ≤ N) (hNn : N - (n + p) ≤ 2) (pins : Fin p → Euc d) (i : Fin n) :
    ∀ᵐ z ∂HRS.Whole.withDensityReal rho,
      |(((referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins).map
          (fun X => X i)).rnDeriv (HRS.Whole.withDensityReal rho) z).toReal - 1| ≤
        C1 * Phase2S82.deltaN N + C1 * min 1 ((1 + ∑ j, q (z - pins j)) / N) := by
  filter_upwards [s82p2_refMarg_dev hP hN, hP.2 N hN p n hp hnp hNn pins i] with z h1 h2
  have : |(((referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins).map
          (fun X => X i)).rnDeriv (HRS.Whole.withDensityReal rho) z).toReal - 1| ≤
      |(((referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins).map
          (fun X => X i)).rnDeriv (HRS.Whole.withDensityReal rho) z).toReal -
        ((refMarginal q h (HRS.Whole.withDensityReal rho) beta N).rnDeriv
            (HRS.Whole.withDensityReal rho) z).toReal| +
      |((refMarginal q h (HRS.Whole.withDensityReal rho) beta N).rnDeriv
        (HRS.Whole.withDensityReal rho) z).toReal - 1| := by
    exact abs_sub_le _ _ _
  linarith

/-- Transfer of lintegrals through the density `rn`. -/
lemma s82p2_marg_lintegral {d p n : ℕ} (q : Euc d → ℝ) (h : ℕ → Euc d → ℝ)
    (mu : Measure (Euc d)) [SigmaFinite mu] (beta : ℝ) (N : ℕ) (pins : Fin p → Euc d)
    (i : Fin n) (H : Euc d → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ z, H z ∂((referenceLaw q h mu beta N n pins).map (fun X => X i)) =
      ∫⁻ z, ((referenceLaw q h mu beta N n pins).map (fun X => X i)).rnDeriv mu z * H z ∂mu := by
  haveI : SFinite (referenceLaw q h mu beta N n pins) := by
    unfold referenceLaw exponentialTilt
    infer_instance
  haveI : Measure.HaveLebesgueDecomposition
      ((referenceLaw q h mu beta N n pins).map (fun X => X i)) mu := inferInstance
  exact (lintegral_rnDeriv_mul (s82p2_marg_ac q h mu beta N pins i) hH.aemeasurable).symm

end HRS.MS.S82P2
