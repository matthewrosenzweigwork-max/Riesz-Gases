import HRS.MS.R26T8AC01c

/-!
# S8.2 observed-time layer, packet T8A.C01d: the fractional law is a probability measure with marginals dominated by `8 mu`
For `N` with `|h N| ≤ 1`, `n = m + 1`, `n + p ≤ N` and weights in `[0, beta/N]`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.R26T8A
open HRS.MS.Phase2S82

theorem r26t8a_c01_fixedN {d p m : ℕ} (hd : 2 ≤ d) {a beta C0 : ℝ} (ha : 0 < a) (hbeta : 0 < beta)
    {rho q : Euc d → ℝ} {h : ℕ → Euc d → ℝ}
    (hrho : HRS.Whole.IsThermalEquilibrium d (criticalS d) a beta rho)
    (hW : WeakReferenceSetup d a beta rho q h C0) (N : ℕ) (hN : 2 ≤ N)
    (hh1 : ∀ x, |h N x| ≤ 1) (hnp : m + 1 + p ≤ N) (pins : Fin p → Euc d) (weights : Fin p → ℝ)
    (hw : ∀ j, 0 ≤ weights j ∧ weights j ≤ beta / N) (i : Fin (m + 1)) :
    IsProbabilityMeasure (r26t8a_fractionalLaw q h (HRS.Whole.withDensityReal rho) beta N (m + 1) pins weights) ∧
    (r26t8a_fractionalLaw q h (HRS.Whole.withDensityReal rho) beta N (m + 1) pins weights).map
        (fun X => X i) ≤ ENNReal.ofReal 8 • HRS.Whole.withDensityReal rho := by
  haveI hμ : IsProbabilityMeasure (HRS.Whole.withDensityReal rho) :=
    HRS.Whole.Q09A.measure_isProb hrho.2.1
  set μ : Measure (Euc d) := HRS.Whole.withDensityReal rho with hμdef
  have hq := hW.short
  have hqm : Measurable q := hq.measurable
  have hhm : Measurable (h N) := hW.hmeas N
  have hqe := hq.even
  have hw0 : ∀ j, 0 ≤ weights j := fun j => (hw j).1
  set E : HRS.Whole.EucConfig d (m + 1) → ℝ := r26t8a_c01_E q h μ beta N (m + 1) pins weights with hE
  have hEm : Measurable E := r26t8a_c01_E_meas hqm beta N (m + 1) hhm pins weights
  obtain ⟨-, hpos, hlint⟩ := r26t8a_r09_tilt_bdd (Measure.pi fun _ : Fin (m + 1) => μ) E hEm _
    (r26t8a_c01_E_le hbeta hW N (m + 1) hN hh1 pins weights hw0)
  set π : Measure (HRS.Whole.EucConfig d (m + 1)) := Measure.pi fun _ : Fin (m + 1) => μ with hπ
  set Zc : ℝ := ∫ X, Real.exp (E X) ∂π with hZc
  set F : HRS.Whole.EucConfig d (m + 1) → ℝ≥0∞ := fun X => ENNReal.ofReal (Real.exp (E X)) with hF
  have hFm : Measurable F := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hEm)
  have hlaw : r26t8a_fractionalLaw q h μ beta N (m + 1) pins weights =
      (ENNReal.ofReal Zc)⁻¹ • π.withDensity F := rfl
  have hZ0 : ENNReal.ofReal Zc ≠ 0 := (ENNReal.ofReal_pos.2 hpos).ne'
  have hZt : ENNReal.ofReal Zc ≠ ⊤ := ENNReal.ofReal_ne_top
  have hFint : ∫⁻ X, F X ∂π = ENNReal.ofReal Zc := hlint
  have hprob : IsProbabilityMeasure (r26t8a_fractionalLaw q h μ beta N (m + 1) pins weights) := by
    refine ⟨?_⟩
    rw [hlaw, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, smul_eq_mul,
      hFint]
    exact ENNReal.inv_mul_cancel hZ0 hZt
  refine ⟨hprob, ?_⟩
  -- the one-site data
  set ψ : (Fin m → Euc d) → Euc d → ℝ := fun X' y => beta * HRS.Whole.convMeasure q μ y + h N y -
    ((beta / N) * ∑ l, q (y - X' l) + ∑ j, weights j * q (y - pins j)) with hψ
  have hsite := fun X' => r26t8a_c01_site hd ha hbeta hrho hW N hN hh1 (m := m) (p := p)
    (by omega) pins weights hw X'
  set A : (Fin m → Euc d) → Euc d → ℝ≥0∞ := fun X' y => ENNReal.ofReal (Real.exp (ψ X' y)) with hA
  have hAm : ∀ X', Measurable (A X') := fun X' =>
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hsite X').1)
  set Zl : (Fin m → Euc d) → ℝ≥0∞ := fun X' => ∫⁻ y, A X' y ∂μ with hZl
  have hFins : ∀ y X', F (i.insertNth y X' : HRS.Whole.EucConfig d (m + 1)) =
      ENNReal.ofReal (Real.exp (r26t8a_c01_E q h μ beta N m pins weights X')) * A X' y := by
    intro y X'
    simp only [hF, hE, r26t8a_c01_E_insert hqe, hA, hψ]
    rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]
  have hFsplit : ∫⁻ X, F X ∂π = ∫⁻ X', ENNReal.ofReal (Real.exp (r26t8a_c01_E q h μ beta N m pins weights X')) *
      Zl X' ∂(Measure.pi fun _ : Fin m => μ) := by
    rw [hπ, r26t8a_c01_split μ i F hFm]
    refine lintegral_congr fun X' => ?_
    simp only [hFins]
    rw [lintegral_const_mul _ (hAm X')]
  refine Measure.le_iff.2 fun s hs => ?_
  have hev : Measurable (fun X : HRS.Whole.EucConfig d (m + 1) => X i) := measurable_pi_apply i
  rw [Measure.map_apply hev hs, hlaw, Measure.smul_apply, withDensity_apply _ (hev hs), smul_eq_mul,
    Measure.smul_apply, smul_eq_mul, ← lintegral_indicator (hev hs)]
  have hΨm : Measurable (((fun X : HRS.Whole.EucConfig d (m + 1) => X i) ⁻¹' s).indicator F) :=
    hFm.indicator (hev hs)
  have hbound : ∫⁻ X, ((fun X : HRS.Whole.EucConfig d (m + 1) => X i) ⁻¹' s).indicator F X ∂π ≤
      ENNReal.ofReal (Real.exp (2 + 2 / 1000)) * μ s * ∫⁻ X, F X ∂π := by
    rw [hπ, r26t8a_c01_split μ i _ hΨm, hFsplit, ← lintegral_const_mul' _ _
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ s))]
    refine lintegral_mono fun X' => ?_
    have hind : ∀ y, ((fun X : HRS.Whole.EucConfig d (m + 1) => X i) ⁻¹' s).indicator F
        (i.insertNth y X' : HRS.Whole.EucConfig d (m + 1)) =
        s.indicator (fun y => ENNReal.ofReal (Real.exp (r26t8a_c01_E q h μ beta N m pins weights X')) *
          A X' y) y := fun y => by
      by_cases hy : y ∈ s
      · simp [Set.indicator, hy, hFins]
      · simp [Set.indicator, hy]
    simp only [hind]
    rw [lintegral_indicator hs, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    obtain ⟨-, hup, hlow, hl⟩ := hsite X'
    have hAle : ∀ y, A X' y ≤ ENNReal.ofReal (Real.exp (1 + 1 / 1000)) := fun y =>
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hup y))
    have h1 : ∫⁻ y in s, A X' y ∂μ ≤ ENNReal.ofReal (Real.exp (1 + 1 / 1000)) * μ s := by
      calc _ ≤ ∫⁻ y in s, ENNReal.ofReal (Real.exp (1 + 1 / 1000)) ∂μ := lintegral_mono hAle
        _ = _ := by rw [setLIntegral_const]
    have h2 : ENNReal.ofReal (Real.exp (1 + 1 / 1000)) ≤
        ENNReal.ofReal (Real.exp (2 + 2 / 1000)) * Zl X' := by
      have hZ : Zl X' = ENNReal.ofReal (∫ y, Real.exp (ψ X' y) ∂μ) := hl
      rw [hZ, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      refine ENNReal.ofReal_le_ofReal ?_
      calc Real.exp (1 + 1 / 1000) = Real.exp (2 + 2 / 1000) * Real.exp (-1 - 1 / 1000) := by
            rw [← Real.exp_add]; congr 1; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hlow (Real.exp_pos _).le
    calc ENNReal.ofReal (Real.exp (r26t8a_c01_E q h μ beta N m pins weights X')) * ∫⁻ y in s, A X' y ∂μ
        ≤ ENNReal.ofReal (Real.exp (r26t8a_c01_E q h μ beta N m pins weights X')) *
            (ENNReal.ofReal (Real.exp (1 + 1 / 1000)) * μ s) := by gcongr
      _ ≤ ENNReal.ofReal (Real.exp (r26t8a_c01_E q h μ beta N m pins weights X')) *
            ((ENNReal.ofReal (Real.exp (2 + 2 / 1000)) * Zl X') * μ s) := by gcongr
      _ = _ := by ring
  have h8 : ENNReal.ofReal (Real.exp (2 + 2 / 1000)) ≤ ENNReal.ofReal 8 := by
    refine ENNReal.ofReal_le_ofReal ?_
    have hl8 : (2 + 2 / 1000 : ℝ) ≤ Real.log 8 := by
      have e : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
      have := Real.log_two_gt_d9
      rw [e]; linarith
    calc Real.exp (2 + 2 / 1000) ≤ Real.exp (Real.log 8) := Real.exp_le_exp.2 hl8
      _ = 8 := Real.exp_log (by norm_num)
  calc (ENNReal.ofReal Zc)⁻¹ * ∫⁻ X, ((fun X : HRS.Whole.EucConfig d (m + 1) => X i) ⁻¹' s).indicator F X ∂π
      ≤ (ENNReal.ofReal Zc)⁻¹ * (ENNReal.ofReal (Real.exp (2 + 2 / 1000)) * μ s * ENNReal.ofReal Zc) := by
        rw [← hFint]; gcongr
    _ = ENNReal.ofReal (Real.exp (2 + 2 / 1000)) * μ s := by
        rw [mul_comm (ENNReal.ofReal (Real.exp (2 + 2 / 1000)) * μ s), ← mul_assoc,
          ENNReal.inv_mul_cancel hZ0 hZt, one_mul]
    _ ≤ ENNReal.ofReal 8 * μ s := by gcongr

end HRS.MS.R26T8A
