import HRS.MS.S82QInv

/-!
# S8.2 (S82Q): pin-weighted domination of resampling kernels and one-site marginals
`nu_w = mu.withDensity (exp (-(beta/N) * sum_b q (. - a_b)))`.  The resampling law of every site is at most
`C0 * nu_w` (all other particles' repulsion factors are at most one), the resampling law is a
probability measure, and, by reversibility (`s82q_invariance`), every one-site marginal of the
pinned reference law is at most `C0 * nu_w`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82Q
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2

/-- The pin-repulsion weighted copy of the base measure. -/
def s82q_nu {d p : ℕ} (q : Euc d → ℝ) (mu : Measure (Euc d)) (beta : ℝ) (N : ℕ)
    (pins : Fin p → Euc d) : Measure (Euc d) :=
  mu.withDensity (fun y => ENNReal.ofReal (Real.exp (-(beta / N) * ∑ j, q (y - pins j))))

lemma s82q_nu_le {d p : ℕ} (q : Euc d → ℝ) (hq0 : ∀ z, 0 ≤ q z) (mu : Measure (Euc d)) (beta : ℝ)
    (hbeta : 0 < beta) (N : ℕ) (pins : Fin p → Euc d) : s82q_nu q mu beta N pins ≤ mu := by
  refine Measure.le_iff.2 fun s hs => ?_
  unfold s82q_nu
  rw [withDensity_apply _ hs]
  calc ∫⁻ y in s, ENNReal.ofReal (Real.exp (-(beta / N) * ∑ j, q (y - pins j))) ∂mu
      ≤ ∫⁻ y in s, 1 ∂mu := by
        refine lintegral_mono fun y => ?_
        refine ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 ?_)
        have : 0 ≤ (beta / N) * ∑ j, q (y - pins j) :=
          mul_nonneg (div_nonneg hbeta.le (Nat.cast_nonneg _))
            (Finset.sum_nonneg fun j _ => hq0 _)
        linarith
    _ = mu s := by simp

lemma s82q_res_le_nu {d : ℕ} {a beta C0 : ℝ} {rho : Euc d → ℝ} {q : Euc d → ℝ}
    {h : ℕ → Euc d → ℝ} (hW : WeakReferenceSetup d a beta rho q h C0) (hbeta : 0 < beta)
    {N : ℕ} (hN : 2 ≤ N) {p n : ℕ} (hp : p ≤ 2) (hnp : n + p ≤ N) (pins : Fin p → Euc d)
    (i : Fin n) (X : EucConfig d n) :
    resampleLaw q h (HRS.Whole.withDensityReal rho) beta N pins i X ≤
      ENNReal.ofReal C0 • s82q_nu q (HRS.Whole.withDensityReal rho) beta N pins := by
  refine (hW.conditional N hN p n (by omega) hnp pins i X).trans ?_
  refine Measure.le_iff.2 fun s hs => ?_
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul, withDensity_apply _ hs]
  unfold s82q_nu
  rw [withDensity_apply _ hs]
  refine mul_le_mul_of_nonneg_left (lintegral_mono fun y => ?_) bot_le
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have hq := hW.short.nonneg
  have h1 : 0 ≤ (beta / N) * ∑ j ∈ Finset.univ.erase i, q (y - X j) :=
    mul_nonneg (div_nonneg hbeta.le (Nat.cast_nonneg _)) (Finset.sum_nonneg fun j _ => hq _)
  nlinarith

/-- Bounds feeding `s82q_invariance`. -/
lemma s82q_hup {d : ℕ} {a beta C0 : ℝ} {rho : Euc d → ℝ} {q : Euc d → ℝ}
    {h : ℕ → Euc d → ℝ} (hW : WeakReferenceSetup d a beta rho q h C0) {N : ℕ} (hN : 2 ≤ N)
    (y : Euc d) :
    beta * HRS.Whole.convMeasure q (HRS.Whole.withDensityReal rho) y + h N y ≤ 1 / 1000 + C0 := by
  have h1 := hW.small_row y
  have h2 := hW.hbound N hN y
  have h3 := s82p2_deltaN_le_one (N := N) (by omega)
  have h4 := s82p2_deltaN_nonneg (N := N) (by omega)
  have hC := hW.positive
  have : C0 * Phase2S82.deltaN N ≤ C0 := by nlinarith
  linarith [le_abs_self (h N y)]

theorem s82q_inv_hw {d : ℕ} {a beta C0 : ℝ} {rho : Euc d → ℝ} {q : Euc d → ℝ}
    {h : ℕ → Euc d → ℝ} [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)]
    (hW : WeakReferenceSetup d a beta rho q h C0) (hbeta : 0 < beta)
    {N : ℕ} (hN : 2 ≤ N) {p m : ℕ} (hp : p ≤ 2) (hnp : m + 1 + p ≤ N) (pins : Fin p → Euc d)
    (i : Fin (m + 1)) (g : EucConfig d (m + 1) → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ X, ∫⁻ y, g (Function.update X i y)
        ∂resampleLaw q h (HRS.Whole.withDensityReal rho) beta N pins i X
        ∂referenceLaw q h (HRS.Whole.withDensityReal rho) beta N (m + 1) pins =
      ∫⁻ X, g X ∂referenceLaw q h (HRS.Whole.withDensityReal rho) beta N (m + 1) pins :=
  s82q_invariance hW.short.measurable hW.short.even hW.short.nonneg beta N
    (div_nonneg hbeta.le (Nat.cast_nonneg _)) (hW.hmeas N) _ (s82q_hup hW hN) pins i
    (hW.probability N hN p (m + 1) (by omega) hnp pins) g hg

/-- Each resampling law is a probability measure. -/
theorem s82q_res_prob {d : ℕ} {a beta C0 : ℝ} {rho : Euc d → ℝ} {q : Euc d → ℝ}
    {h : ℕ → Euc d → ℝ} [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)]
    (hW : WeakReferenceSetup d a beta rho q h C0) (hbeta : 0 < beta)
    {N : ℕ} (hN : 2 ≤ N) {p m : ℕ} (pins : Fin p → Euc d)
    (i : Fin (m + 1)) (X : EucConfig d (m + 1)) :
    IsProbabilityMeasure (resampleLaw q h (HRS.Whole.withDensityReal rho) beta N pins i X) := by
  rw [← s82q_insertNth_removeNth i X, s82q_res_insertNth hW.short.even]
  set X' : Fin m → Euc d := fun j => X (i.succAbove j)
  set mu := HRS.Whole.withDensityReal rho
  have hq0 := hW.short.nonneg
  have hVm := (s82q_V_measurable (m := m) (mu := mu) hW.short.measurable beta N (hW.hmeas N) pins)
  have hVy : Measurable (s82q_V q h mu beta N pins X') := hVm.comp measurable_prodMk_left
  have hVb : ∀ y, s82q_V q h mu beta N pins X' y ≤ 1 / 1000 + C0 := by
    intro y
    unfold s82q_V s82p2_site
    have hβN : 0 ≤ beta / N := div_nonneg hbeta.le (Nat.cast_nonneg _)
    have h2 : 0 ≤ (beta / N) * ∑ j, q (y - pins j) :=
      mul_nonneg hβN (Finset.sum_nonneg fun j _ => hq0 _)
    have h3 : 0 ≤ (beta / N) * ∑ j, q (X' j - y) :=
      mul_nonneg hβN (Finset.sum_nonneg fun j _ => hq0 _)
    linarith [s82q_hup hW hN y]
  obtain ⟨a1, a2, a3⟩ := s82q_zeta mu _ hVy _ hVb
  refine ⟨?_⟩
  have := s82q_tilt_lintegral mu _ hVy (fun _ => (1 : ℝ≥0∞)) measurable_const
  rw [lintegral_one] at this
  simp only [mul_one] at this
  rw [this, ← a1]
  exact ENNReal.inv_mul_cancel a2 a3

/-- Every one-site marginal of the pinned reference law is dominated by `C0 * nu_w`. -/
theorem s82q_marg_le_nu {d : ℕ} {a beta C0 : ℝ} {rho : Euc d → ℝ} {q : Euc d → ℝ}
    {h : ℕ → Euc d → ℝ} [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)]
    (hW : WeakReferenceSetup d a beta rho q h C0) (hbeta : 0 < beta)
    {N : ℕ} (hN : 2 ≤ N) {p m : ℕ} (hp : p ≤ 2) (hnp : m + 1 + p ≤ N) (pins : Fin p → Euc d)
    (i : Fin (m + 1)) :
    (referenceLaw q h (HRS.Whole.withDensityReal rho) beta N (m + 1) pins).map (fun X => X i) ≤
      ENNReal.ofReal C0 • s82q_nu q (HRS.Whole.withDensityReal rho) beta N pins := by
  set mu := HRS.Whole.withDensityReal rho
  set ref := referenceLaw q h mu beta N (m + 1) pins with href
  have : IsProbabilityMeasure ref := hW.probability N hN p (m + 1) (by omega) hnp pins
  refine Measure.le_iff.2 fun s hs => ?_
  rw [Measure.map_apply (measurable_pi_apply i) hs, Measure.smul_apply, smul_eq_mul]
  have hS : MeasurableSet ((fun X : EucConfig d (m + 1) => X i) ⁻¹' s) :=
    measurable_pi_apply i hs
  have hg : Measurable (fun X : EucConfig d (m + 1) => s.indicator (1 : Euc d → ℝ≥0∞) (X i)) :=
    (measurable_one.indicator hs).comp (measurable_pi_apply i)
  have e1 : ref ((fun X : EucConfig d (m + 1) => X i) ⁻¹' s) =
      ∫⁻ X, s.indicator (1 : Euc d → ℝ≥0∞) (X i) ∂ref := by
    rw [← lintegral_indicator_one hS]
    refine lintegral_congr fun X => ?_
    by_cases hX : X i ∈ s <;> simp [Set.indicator, hX]
  rw [e1, ← s82q_inv_hw hW hbeta hN hp hnp pins i _ hg]
  simp only [Function.update_self]
  calc ∫⁻ X, ∫⁻ y, s.indicator (1 : Euc d → ℝ≥0∞) y
          ∂resampleLaw q h mu beta N pins i X ∂ref
      = ∫⁻ X, resampleLaw q h mu beta N pins i X s ∂ref := by
        refine lintegral_congr fun X => ?_
        have := lintegral_indicator_one (μ := resampleLaw q h mu beta N pins i X) hs
        simpa using this
    _ ≤ ∫⁻ X, ENNReal.ofReal C0 * s82q_nu q mu beta N pins s ∂ref := by
        refine lintegral_mono fun X => ?_
        have := s82q_res_le_nu hW hbeta hN hp (by omega) pins i X s
        simpa [Measure.smul_apply] using this
    _ = ENNReal.ofReal C0 * s82q_nu q mu beta N pins s := by
        rw [lintegral_const, measure_univ, mul_one]

end HRS.MS.S82Q
