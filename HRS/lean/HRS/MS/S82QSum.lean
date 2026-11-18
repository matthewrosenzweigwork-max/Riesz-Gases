import HRS.MS.S82QDom

/-!
# S8.2 (S82Q): second moment of a sum `sum_j psi (X_j)` under the pinned weak reference law, weighted form
Same resampling argument as `s82p2_centered_sum_sq`, but with the pin-repulsion weighted base measure
`nu = s82q_nu` in place of `mu` (needed when `psi` has a non-square-integrable pole at a pin):
`E S^2 <= 4 C0^2 n int psi^2 dnu + (n M1)^2`, where `M1` bounds the mean of `psi` under every one-site marginal.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82Q
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2

theorem s82q_sum_sq {d : ℕ} {a beta C0 : ℝ} {rho : Euc d → ℝ} {q : Euc d → ℝ}
    {h : ℕ → Euc d → ℝ} [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)]
    (hW : WeakReferenceSetup d a beta rho q h C0) (hbeta : 0 < beta)
    {N : ℕ} (hN : 2 ≤ N) {p m : ℕ} (hp : p ≤ 2) (hnp : m + 1 + p ≤ N) (hNn : N - (m + 1 + p) ≤ 2)
    (pins : Fin p → Euc d) (ψ : Euc d → ℝ) (hψm : Measurable ψ)
    (hψ2 : Integrable (fun z => ψ z ^ 2) (s82q_nu q (HRS.Whole.withDensityReal rho) beta N pins))
    (M1 : ℝ) (hmean : ∀ i : Fin (m + 1),
      |∫ z, ψ z ∂((referenceLaw q h (HRS.Whole.withDensityReal rho) beta N (m + 1) pins).map
        (fun X => X i))| ≤ M1) :
    MemLp (fun X : EucConfig d (m + 1) => ∑ j, ψ (X j)) 2
        (referenceLaw q h (HRS.Whole.withDensityReal rho) beta N (m + 1) pins) ∧
      ∫⁻ X, ENNReal.ofReal ((∑ j, ψ (X j)) ^ 2)
          ∂referenceLaw q h (HRS.Whole.withDensityReal rho) beta N (m + 1) pins ≤
        ENNReal.ofReal (4 * C0 ^ 2 * (m + 1 : ℕ) *
            ∫ z, ψ z ^ 2 ∂s82q_nu q (HRS.Whole.withDensityReal rho) beta N pins +
          ((m + 1 : ℕ) * M1) ^ 2) := by
  classical
  set mu := HRS.Whole.withDensityReal rho with hmu
  set nu := s82q_nu q mu beta N pins with hnu
  set ref := referenceLaw q h mu beta N (m + 1) pins with href
  have hprob : IsProbabilityMeasure ref := hW.probability N hN p (m + 1) (by omega) hnp pins
  have hC0 := hW.positive
  have hψL2 : MemLp ψ 2 nu := (memLp_two_iff_integrable_sq hψm.aestronglyMeasurable).2 hψ2
  have hdom : ∀ i : Fin (m + 1), ref.map (fun X => X i) ≤ ENNReal.ofReal C0 • nu :=
    fun i => s82q_marg_le_nu hW hbeta hN hp hnp pins i
  have hcoord : ∀ i : Fin (m + 1), MemLp (fun X : EucConfig d (m + 1) => ψ (X i)) 2 ref := by
    intro i
    have h1 : MemLp ψ 2 (ref.map (fun X => X i)) :=
      (hψL2.smul_measure ENNReal.ofReal_ne_top).mono_measure (hdom i)
    exact (memLp_map_measure_iff hψm.aestronglyMeasurable
      (measurable_pi_apply i).aemeasurable).1 h1
  have hSmem : MemLp (fun X : EucConfig d (m + 1) => ∑ j, ψ (X j)) 2 ref :=
    memLp_finsetSum _ (fun j _ => hcoord j)
  refine ⟨hSmem, ?_⟩
  have hmeanS : |∫ X, ∑ j, ψ (X j) ∂ref| ≤ (m + 1 : ℕ) * M1 := by
    rw [integral_finset_sum _ (fun j _ => (hcoord j).integrable one_le_two)]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hj : ∀ j : Fin (m + 1), |∫ X, ψ (X j) ∂ref| ≤ M1 := by
      intro j
      rw [← integral_map (measurable_pi_apply j).aemeasurable hψm.aestronglyMeasurable]
      exact hmean j
    calc ∑ j : Fin (m + 1), |∫ X, ψ (X j) ∂ref| ≤ ∑ j : Fin (m + 1), M1 :=
          Finset.sum_le_sum fun j _ => hj j
      _ = (m + 1 : ℕ) * M1 := by simp
  have hvar := hW.resampling N hN p (m + 1) hp hnp hNn pins (fun X => ∑ j, ψ (X j)) hSmem
  set A : ℝ≥0∞ := ∫⁻ z, ENNReal.ofReal (ψ z ^ 2) ∂nu with hA
  have hAeq : A = ENNReal.ofReal (∫ z, ψ z ^ 2 ∂nu) := by
    rw [hA]
    exact (ofReal_integral_eq_lintegral_ofReal hψ2 (ae_of_all _ fun z => sq_nonneg _)).symm
  have hψ2m : Measurable (fun z => ψ z ^ 2) := hψm.pow_const 2
  have inner : ∀ (i : Fin (m + 1)) (X : EucConfig d (m + 1)),
      ∫⁻ y, ENNReal.ofReal ((∑ j, ψ (Function.update X i y j) - ∑ j, ψ (X j)) ^ 2)
          ∂resampleLaw q h mu beta N pins i X ≤
        ENNReal.ofReal C0 * (ENNReal.ofReal 2 * A) + ENNReal.ofReal (2 * ψ (X i) ^ 2) := by
    intro i X
    have e : ∀ y, (∑ j, ψ (Function.update X i y j) - ∑ j, ψ (X j)) = ψ y - ψ (X i) := by
      intro y; rw [s82p2_sum_update]; ring
    simp only [e]
    haveI := s82q_res_prob hW hbeta hN pins i X
    calc ∫⁻ y, ENNReal.ofReal ((ψ y - ψ (X i)) ^ 2) ∂resampleLaw q h mu beta N pins i X
        ≤ ∫⁻ y, (ENNReal.ofReal 2 * ENNReal.ofReal (ψ y ^ 2) +
            ENNReal.ofReal (2 * ψ (X i) ^ 2)) ∂resampleLaw q h mu beta N pins i X := by
          refine lintegral_mono fun y => ?_
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          nlinarith [sq_nonneg (ψ y + ψ (X i))]
      _ = ENNReal.ofReal 2 * ∫⁻ y, ENNReal.ofReal (ψ y ^ 2)
            ∂resampleLaw q h mu beta N pins i X + ENNReal.ofReal (2 * ψ (X i) ^ 2) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          simp
      _ ≤ ENNReal.ofReal 2 * ∫⁻ y, ENNReal.ofReal (ψ y ^ 2)
            ∂(ENNReal.ofReal C0 • nu) + ENNReal.ofReal (2 * ψ (X i) ^ 2) := by
          gcongr
          exact s82q_res_le_nu hW hbeta hN hp (by omega) pins i X
      _ = ENNReal.ofReal C0 * (ENNReal.ofReal 2 * A) + ENNReal.ofReal (2 * ψ (X i) ^ 2) := by
          rw [lintegral_smul_measure, smul_eq_mul, ← hA]
          ring
  have hB : ∀ i : Fin (m + 1), ∫⁻ X, (∫⁻ y, ENNReal.ofReal
        ((∑ j, ψ (Function.update X i y j) - ∑ j, ψ (X j)) ^ 2)
          ∂resampleLaw q h mu beta N pins i X) ∂ref ≤
        ENNReal.ofReal C0 * (ENNReal.ofReal 2 * A) +
          ENNReal.ofReal C0 * (ENNReal.ofReal 2 * A) := by
    intro i
    calc ∫⁻ X, (∫⁻ y, ENNReal.ofReal ((∑ j, ψ (Function.update X i y j) - ∑ j, ψ (X j)) ^ 2)
          ∂resampleLaw q h mu beta N pins i X) ∂ref
        ≤ ∫⁻ X, (ENNReal.ofReal C0 * (ENNReal.ofReal 2 * A) +
            ENNReal.ofReal (2 * ψ (X i) ^ 2)) ∂ref :=
          lintegral_mono fun X => inner i X
      _ = ENNReal.ofReal C0 * (ENNReal.ofReal 2 * A) +
            ∫⁻ X, ENNReal.ofReal (2 * ψ (X i) ^ 2) ∂ref := by
          rw [lintegral_add_left measurable_const]
          simp
      _ ≤ _ := by
          gcongr
          have hm : Measurable (fun z : Euc d => ENNReal.ofReal (2 * ψ z ^ 2)) :=
            ENNReal.measurable_ofReal.comp (measurable_const.mul hψ2m)
          have e1 : ∫⁻ X, ENNReal.ofReal (2 * ψ (X i) ^ 2) ∂ref =
              ∫⁻ z, ENNReal.ofReal (2 * ψ z ^ 2) ∂(ref.map (fun X => X i)) :=
            (lintegral_map hm (measurable_pi_apply i)).symm
          rw [e1]
          calc ∫⁻ z, ENNReal.ofReal (2 * ψ z ^ 2) ∂(ref.map (fun X => X i))
              ≤ ∫⁻ z, ENNReal.ofReal (2 * ψ z ^ 2) ∂(ENNReal.ofReal C0 • nu) :=
                lintegral_mono' (hdom i) le_rfl
            _ = ENNReal.ofReal C0 * (ENNReal.ofReal 2 * A) := by
                rw [lintegral_smul_measure, smul_eq_mul]
                congr 1
                have : ∀ z : Euc d, ENNReal.ofReal (2 * ψ z ^ 2) =
                    ENNReal.ofReal 2 * ENNReal.ofReal (ψ z ^ 2) := fun z =>
                  ENNReal.ofReal_mul (by norm_num)
                simp only [this]
                rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have ha2 : 0 ≤ ∫ z, ψ z ^ 2 ∂nu := integral_nonneg fun z => sq_nonneg _
  have hvar2 : evariance (fun X : EucConfig d (m + 1) => ∑ j, ψ (X j)) ref ≤
      ENNReal.ofReal (4 * C0 ^ 2 * (m + 1 : ℕ) * ∫ z, ψ z ^ 2 ∂nu) := by
    calc evariance (fun X : EucConfig d (m + 1) => ∑ j, ψ (X j)) ref
        ≤ ENNReal.ofReal C0 * ∑ i : Fin (m + 1), ∫⁻ X, (∫⁻ y, ENNReal.ofReal
            ((∑ j, ψ (Function.update X i y j) - ∑ j, ψ (X j)) ^ 2)
              ∂resampleLaw q h mu beta N pins i X) ∂ref := hvar
      _ ≤ ENNReal.ofReal C0 * ∑ i : Fin (m + 1), (ENNReal.ofReal C0 * (ENNReal.ofReal 2 * A) +
            ENNReal.ofReal C0 * (ENNReal.ofReal 2 * A)) := by
          gcongr with i _
          exact hB i
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hAeq,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_mul hC0.le, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul hC0.le]
        congr 1
        ring
  have hev := evariance_def' (μ := ref) hSmem.aestronglyMeasurable
  have hL : ∫⁻ X, ENNReal.ofReal ((∑ j, ψ (X j)) ^ 2) ∂ref =
      ∫⁻ X, ‖∑ j, ψ (X j)‖ₑ ^ 2 ∂ref := by simp_rw [s82p2_enorm_sq]
  rw [hL]
  have h1 : ∫⁻ X, ‖∑ j, ψ (X j)‖ₑ ^ 2 ∂ref ≤ evariance (fun X : EucConfig d (m + 1) => ∑ j, ψ (X j)) ref +
      ENNReal.ofReal ((∫ X, ∑ j, ψ (X j) ∂ref) ^ 2) := by
    rw [hev]
    exact le_tsub_add
  have hsq : (∫ X, ∑ j, ψ (X j) ∂ref) ^ 2 ≤ ((m + 1 : ℕ) * M1) ^ 2 :=
    sq_le_sq.2 (hmeanS.trans (le_abs_self _))
  calc ∫⁻ X, ‖∑ j, ψ (X j)‖ₑ ^ 2 ∂ref
      ≤ _ := h1
    _ ≤ ENNReal.ofReal (4 * C0 ^ 2 * (m + 1 : ℕ) * ∫ z, ψ z ^ 2 ∂nu) +
          ENNReal.ofReal (((m + 1 : ℕ) * M1) ^ 2) :=
        add_le_add hvar2 (ENNReal.ofReal_le_ofReal hsq)
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (sq_nonneg _)]

end HRS.MS.S82Q
