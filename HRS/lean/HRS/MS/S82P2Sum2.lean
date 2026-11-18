import HRS.MS.S82P2Sum1

/-!
# S8.2 (S82P2): second moment of a centered sum under the pinned weak reference law
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

lemma s82p2_enorm_sq (x : ℝ) : ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]

theorem s82p2_centered_sum_sq {d : ℕ} {a beta C0 C1 : ℝ} {rho : Euc d → ℝ} {q : Euc d → ℝ}
    {h : ℕ → Euc d → ℝ} [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)]
    (hW : WeakReferenceSetup d a beta rho q h C0) (hbeta : 0 < beta)
    (hP : PinComparison beta rho q h C1) {N : ℕ} (hN : 2 ≤ N) {p n : ℕ} (hp : p ≤ 2)
    (hnp : n + p ≤ N) (hNn : N - (n + p) ≤ 2) (pins : Fin p → Euc d)
    (ψ : Euc d → ℝ) (hψm : Measurable ψ)
    (hψ2 : Integrable (fun z => ψ z ^ 2) (HRS.Whole.withDensityReal rho))
    (hψ0 : ∫ z, ψ z ∂HRS.Whole.withDensityReal rho = 0)
    (hint : Integrable (fun z => |ψ z| * (C1 * Phase2S82.deltaN N +
      C1 * min 1 ((1 + ∑ j, q (z - pins j)) / N))) (HRS.Whole.withDensityReal rho)) :
    MemLp (fun X : EucConfig d n => ∑ j, ψ (X j)) 2
        (referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins) ∧
      ∫⁻ X, ENNReal.ofReal ((∑ j, ψ (X j)) ^ 2)
          ∂referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins ≤
        ENNReal.ofReal (C0 ^ 2 * (2 + 2 * (1 + 2 * C1)) * n *
            ∫ z, ψ z ^ 2 ∂HRS.Whole.withDensityReal rho +
          (n * ∫ z, |ψ z| * (C1 * Phase2S82.deltaN N +
            C1 * min 1 ((1 + ∑ j, q (z - pins j)) / N)) ∂HRS.Whole.withDensityReal rho) ^ 2) := by
  classical
  set mu := HRS.Whole.withDensityReal rho with hmu
  set ref := referenceLaw q h mu beta N n pins with href
  have hprob : IsProbabilityMeasure ref := hW.probability N hN p n (by omega) hnp pins
  have hC0 := hW.positive
  have hC1 := s82p2_pinCmp_nonneg hP
  set K : ℝ := 1 + 2 * C1 with hKdef
  have hK : 0 ≤ K := by rw [hKdef]; linarith
  have hψL2 : MemLp ψ 2 mu := (memLp_two_iff_integrable_sq hψm.aestronglyMeasurable).2 hψ2
  have hψi : Integrable ψ mu := hψL2.integrable one_le_two
  have hdom : ∀ i : Fin n, ref.map (fun X => X i) ≤ ENNReal.ofReal K • mu :=
    fun i => s82p2_marg_le_smul hP hN hp hnp hNn pins i hprob
  have hcoord : ∀ i : Fin n, MemLp (fun X : EucConfig d n => ψ (X i)) 2 ref := by
    intro i
    have h1 : MemLp ψ 2 (ref.map (fun X => X i)) :=
      (hψL2.smul_measure ENNReal.ofReal_ne_top).mono_measure (hdom i)
    exact (memLp_map_measure_iff hψm.aestronglyMeasurable
      (measurable_pi_apply i).aemeasurable).1 h1
  have hSmem : MemLp (fun X : EucConfig d n => ∑ j, ψ (X j)) 2 ref :=
    memLp_finsetSum _ (fun j _ => hcoord j)
  refine ⟨hSmem, ?_⟩
  set E1 : ℝ := ∫ z, |ψ z| * (C1 * Phase2S82.deltaN N +
            C1 * min 1 ((1 + ∑ j, q (z - pins j)) / N)) ∂mu with hE1
  have hmean : |∫ X, ∑ j, ψ (X j) ∂ref| ≤ n * E1 := by
    rw [integral_finset_sum _ (fun j _ => (hcoord j).integrable one_le_two)]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hj : ∀ j : Fin n, |∫ X, ψ (X j) ∂ref| ≤ E1 := by
      intro j
      rw [← integral_map (measurable_pi_apply j).aemeasurable hψm.aestronglyMeasurable]
      exact s82p2_marg_mean_abs_le hP hN hp hnp hNn pins j hprob ψ hψm hψi hψ0 hint
    calc ∑ j : Fin n, |∫ X, ψ (X j) ∂ref| ≤ ∑ j : Fin n, E1 :=
          Finset.sum_le_sum fun j _ => hj j
      _ = n * E1 := by simp
  have hvar := hW.resampling N hN p n hp hnp hNn pins (fun X => ∑ j, ψ (X j)) hSmem
  set A : ℝ≥0∞ := ∫⁻ z, ENNReal.ofReal (ψ z ^ 2) ∂mu with hA
  have hAeq : A = ENNReal.ofReal (∫ z, ψ z ^ 2 ∂mu) := by
    rw [hA]
    exact (ofReal_integral_eq_lintegral_ofReal hψ2 (ae_of_all _ fun z => sq_nonneg _)).symm
  have hψ2m : Measurable (fun z => ψ z ^ 2) := hψm.pow_const 2
  have inner : ∀ (i : Fin n) (X : EucConfig d n),
      ∫⁻ y, ENNReal.ofReal ((∑ j, ψ (Function.update X i y j) - ∑ j, ψ (X j)) ^ 2)
          ∂resampleLaw q h mu beta N pins i X ≤
        ENNReal.ofReal C0 * (ENNReal.ofReal 2 * A + ENNReal.ofReal (2 * ψ (X i) ^ 2)) := by
    intro i X
    have e : ∀ y, (∑ j, ψ (Function.update X i y j) - ∑ j, ψ (X j)) = ψ y - ψ (X i) := by
      intro y; rw [s82p2_sum_update]; ring
    simp only [e]
    calc ∫⁻ y, ENNReal.ofReal ((ψ y - ψ (X i)) ^ 2) ∂resampleLaw q h mu beta N pins i X
        ≤ ∫⁻ y, ENNReal.ofReal ((ψ y - ψ (X i)) ^ 2) ∂(ENNReal.ofReal C0 • mu) :=
          lintegral_mono' (s82p2_resample_le hW hbeta hN hp hnp pins i X) le_rfl
      _ = ENNReal.ofReal C0 * ∫⁻ y, ENNReal.ofReal ((ψ y - ψ (X i)) ^ 2) ∂mu := by
          rw [lintegral_smul_measure, smul_eq_mul]
      _ ≤ ENNReal.ofReal C0 * ∫⁻ y, (ENNReal.ofReal 2 * ENNReal.ofReal (ψ y ^ 2) +
            ENNReal.ofReal (2 * ψ (X i) ^ 2)) ∂mu := by
          gcongr with y
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          nlinarith [sq_nonneg (ψ y + ψ (X i))]
      _ = ENNReal.ofReal C0 * (ENNReal.ofReal 2 * A + ENNReal.ofReal (2 * ψ (X i) ^ 2)) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          simp [hA]
  beta_reduce at hvar
  have hB : ∀ i : Fin n, ∫⁻ X, (∫⁻ y, ENNReal.ofReal ((∑ j, ψ (Function.update X i y j) - ∑ j, ψ (X j)) ^ 2)
          ∂resampleLaw q h mu beta N pins i X) ∂ref ≤
        ENNReal.ofReal C0 * (ENNReal.ofReal 2 * A + ENNReal.ofReal K * (ENNReal.ofReal 2 * A)) := by
    intro i
    calc ∫⁻ X, (∫⁻ y, ENNReal.ofReal ((∑ j, ψ (Function.update X i y j) - ∑ j, ψ (X j)) ^ 2)
          ∂resampleLaw q h mu beta N pins i X) ∂ref
        ≤ ∫⁻ X, ENNReal.ofReal C0 * (ENNReal.ofReal 2 * A + ENNReal.ofReal (2 * ψ (X i) ^ 2)) ∂ref :=
          lintegral_mono fun X => inner i X
      _ = ENNReal.ofReal C0 * (ENNReal.ofReal 2 * A +
            ∫⁻ X, ENNReal.ofReal (2 * ψ (X i) ^ 2) ∂ref) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left measurable_const]
          simp
      _ ≤ ENNReal.ofReal C0 * (ENNReal.ofReal 2 * A +
            ENNReal.ofReal K * (ENNReal.ofReal 2 * A)) := by
          gcongr
          have hm : Measurable (fun z : Euc d => ENNReal.ofReal (2 * ψ z ^ 2)) :=
            ENNReal.measurable_ofReal.comp (measurable_const.mul hψ2m)
          have e1 : ∫⁻ X, ENNReal.ofReal (2 * ψ (X i) ^ 2) ∂ref =
              ∫⁻ z, ENNReal.ofReal (2 * ψ z ^ 2) ∂(ref.map (fun X => X i)) :=
            (lintegral_map hm (measurable_pi_apply i)).symm
          rw [e1]
          calc ∫⁻ z, ENNReal.ofReal (2 * ψ z ^ 2) ∂(ref.map (fun X => X i))
              ≤ ∫⁻ z, ENNReal.ofReal (2 * ψ z ^ 2) ∂(ENNReal.ofReal K • mu) :=
                lintegral_mono' (hdom i) le_rfl
            _ = ENNReal.ofReal K * (ENNReal.ofReal 2 * A) := by
                rw [lintegral_smul_measure, smul_eq_mul]
                congr 1
                have : ∀ z : Euc d, ENNReal.ofReal (2 * ψ z ^ 2) =
                    ENNReal.ofReal 2 * ENNReal.ofReal (ψ z ^ 2) := fun z =>
                  ENNReal.ofReal_mul (by norm_num)
                simp only [this]
                rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hvar2 : evariance (fun X : EucConfig d n => ∑ j, ψ (X j)) ref ≤
      ENNReal.ofReal (C0 * (n * (C0 * (2 * (∫ z, ψ z ^ 2 ∂mu) +
        K * (2 * (∫ z, ψ z ^ 2 ∂mu)))))) := by
    have ha2 : 0 ≤ ∫ z, ψ z ^ 2 ∂mu := integral_nonneg fun z => sq_nonneg _
    calc evariance (fun X : EucConfig d n => ∑ j, ψ (X j)) ref
        ≤ ENNReal.ofReal C0 * ∑ i : Fin n, ∫⁻ X, (∫⁻ y, ENNReal.ofReal ((∑ j, ψ (Function.update X i y j) - ∑ j, ψ (X j)) ^ 2)
          ∂resampleLaw q h mu beta N pins i X) ∂ref := hvar
      _ ≤ ENNReal.ofReal C0 * ∑ i : Fin n, ENNReal.ofReal C0 * (ENNReal.ofReal 2 * A +
            ENNReal.ofReal K * (ENNReal.ofReal 2 * A)) := by
          gcongr with i _
          exact hB i
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hAeq,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul hC0.le, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ← ENNReal.ofReal_mul hC0.le]
  have hev := evariance_def' (μ := ref) hSmem.aestronglyMeasurable
  have hL : ∫⁻ X, ENNReal.ofReal ((∑ j, ψ (X j)) ^ 2) ∂ref =
      ∫⁻ X, ‖∑ j, ψ (X j)‖ₑ ^ 2 ∂ref := by simp_rw [s82p2_enorm_sq]
  rw [hL]
  have h1 : ∫⁻ X, ‖∑ j, ψ (X j)‖ₑ ^ 2 ∂ref ≤ evariance (fun X : EucConfig d n => ∑ j, ψ (X j)) ref +
      ENNReal.ofReal ((∫ X, ∑ j, ψ (X j) ∂ref) ^ 2) := by
    rw [hev]
    exact le_tsub_add
  have hsq : (∫ X, ∑ j, ψ (X j) ∂ref) ^ 2 ≤ (n * E1) ^ 2 :=
    sq_le_sq.2 (hmean.trans (le_abs_self _))
  have ha2 : 0 ≤ ∫ z, ψ z ^ 2 ∂mu := integral_nonneg fun z => sq_nonneg _
  have hV0 : 0 ≤ C0 * (n * (C0 * (2 * (∫ z, ψ z ^ 2 ∂mu) + K * (2 * (∫ z, ψ z ^ 2 ∂mu))))) := by
    positivity
  calc ∫⁻ X, ‖∑ j, ψ (X j)‖ₑ ^ 2 ∂ref
      ≤ _ := h1
    _ ≤ ENNReal.ofReal (C0 * (n * (C0 * (2 * (∫ z, ψ z ^ 2 ∂mu) +
          K * (2 * (∫ z, ψ z ^ 2 ∂mu)))))) + ENNReal.ofReal ((n * E1) ^ 2) :=
        add_le_add hvar2 (ENNReal.ofReal_le_ofReal hsq)
    _ = _ := by
        rw [← ENNReal.ofReal_add hV0 (sq_nonneg _)]
        congr 1
        rw [hKdef]
        ring

end HRS.MS.S82P2
